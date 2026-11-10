/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.Stack
public import ProofLib.Hoare.Hooks

/-!
# Rust Global Allocator Contracts

Separation-logic contracts for Rust's `#[global_allocator]` ABI (`__rustc::__rust_alloc`,
`__rustc::__rust_alloc_zeroed`, `__rustc::__rust_dealloc`, `__rustc::__rust_realloc`, and
`__rustc::__rust_no_alloc_shim_is_unstable_v2`). Defines the alignment-indexed `RustAlloc` model,
`ByteAlloc` projections, the `allocFailedIn` trace predicate, and the `AllocHooksIdeal` and
`AllocHooksSimple` hook bundles.
-/

@[expose] public section

namespace ProofLib.RustHeap

open Arm64 ProofLib

/-! ## Abstract Allocator Models -/

/-- An abstract Rust global allocator:
    - `pool`: the allocator's private state,
    - `live p n al`: ownership token for a live allocation of `n` bytes at `p` made with alignment
      `al` (without its byte contents),
    - `noWrap`: every live block fits in the 64-bit address space without wrapping. -/
structure RustAlloc where
  pool : SepProp
  live : BitVec 64 → Nat → Nat → SepProp
  noWrap : ∀ (p : BitVec 64) (n al : Nat), live p n al ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ live p n al

theorem RustAlloc.live_noWrap (A : RustAlloc) (p : BitVec 64) (n al : Nat) :
    A.live p n al ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ A.live p n al :=
  A.noWrap p n al

/-- Single-alignment allocator model where `live p n` tracks only pointer `p` and byte size `n`
    (alias for `Arm64.Allocator`). -/
abbrev ByteAlloc := Arm64.Allocator

/-- Project a `RustAlloc` to a fixed alignment `align` (`live p n := A.live p n align`). -/
def RustAlloc.atAlign (A : RustAlloc) (align : Nat) : ByteAlloc where
  pool := A.pool
  live p n := A.live p n align
  noWrap p n := A.noWrap p n align

/-- Lift a `ByteAlloc` to a `RustAlloc` by ignoring the alignment parameter in `live`. -/
def ByteAlloc.toRustAlloc (A : ByteAlloc) : RustAlloc where
  pool := A.pool
  live p n _ := A.live p n
  noWrap p n _ := A.noWrap p n


@[simp] theorem RustAlloc.atAlign_toRustAlloc (A : ByteAlloc) (align : Nat) :
    (A.toRustAlloc).atAlign align = A := rfl

/-! ## Stack Budget and Layout Validity -/

/-- Stack bytes below `sp` that an allocator hook may use. -/
abbrev allocHookStack : Nat := 4096

/-- The allocator hook's stack scratch region (`allocHookStack` bytes below `sp`). -/
abbrev allocHookFrame (sp : BitVec 64) : SepProp :=
  stackAt sp allocHookStack

/-- A byte length `n` fits in a non-negative 64-bit signed `isize` (`n < 2 ^ 63`). -/
abbrev SmallLen (n : Nat) : Prop := n < 2 ^ 63

/-- Valid non-zero-size `core::alloc::Layout`: positive size, power-of-two alignment, and
    `size + align <= 2 ^ 63` (so rounding up to `align` cannot overflow `isize::MAX`). -/
def LayoutOk (size align : Nat) : Prop :=
  0 < size ∧ (∃ k, align = 2 ^ k) ∧ size + align ≤ 2 ^ 63


theorem LayoutOk.align_pos {size align : Nat} (h : LayoutOk size align) : 0 < align := by
  rcases h.2.1 with ⟨k, rfl⟩
  exact Nat.two_pow_pos k

theorem LayoutOk.size_small {size align : Nat} (h : LayoutOk size align) : SmallLen size := by
  have hal : 0 < align := h.align_pos
  have hle : size + align ≤ 2 ^ 63 := h.2.2
  unfold SmallLen
  omega



theorem LayoutOk.align_8 {size : Nat} (hpos : 0 < size) (hle : size + 8 ≤ 2 ^ 63) :
    LayoutOk size 8 :=
  ⟨hpos, ⟨3, rfl⟩, hle⟩

/-! ## Observable Allocation Failure -/

/-- The trace event a failing allocation hook appends (tag `"rust_alloc_failed"`, empty payload). -/
def allocFailedEvent : TraceEvent := .userDefined "rust_alloc_failed" []

/-- The allocator reported a failure in the part of `sf`'s trace after `s0`'s. -/
def allocFailedIn (s0 sf : State) : Prop :=
  allocFailedEvent ∈ sf.trace.drop s0.trace.length

theorem allocFailedIn_append_singleton {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) : allocFailedIn s0 sf := by
  unfold allocFailedIn
  rw [h, List.drop_left]
  exact List.Mem.head []

theorem not_allocFailedIn_of_trace_eq {s0 sf : State} (h : sf.trace = s0.trace) :
    ¬ allocFailedIn s0 sf := by
  unfold allocFailedIn
  rw [h, List.drop_length]
  intro hmem
  cases hmem

/-! ## Ideal and Simple Global-Allocator Contracts -/

/-- Maximum request byte size `0x7fffffffffffefd0` (`2^63 - 4144`) for which page-rounded C
    allocation with chunk header and alignment overhead (`OVERHEAD = 16`, `SIZE_ALIGN = 32`,
    `PAGE_SIZE = 4096`) stays below `PTRDIFF_MAX` (`2^63 - 1`). -/
abbrev MaxAllocSize : Nat := 0x7fffffffffffefd0

/-- `align` is a non-zero power of two (`align != 0` and `align &&& (align - 1) = 0`), as required
    by `core::alloc::Layout`. -/
def IsPow2Align (align : BitVec 64) : Prop :=
  align ≠ 0#64 ∧ align &&& (align - 1#64) = 0#64

instance (align : BitVec 64) : Decidable (IsPow2Align align) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Effective request byte size after accounting for over-aligned prefix splitting (`align > 32`),
    bounded by `MaxAllocSize` (`0x7fffffffffffefd0`). For `align.toNat <= 32`, this reduces to
    `size.toNat <= MaxAllocSize`. -/
def IdealLayoutFit (size align : BitVec 64) : Prop :=
  (if align.toNat ≤ 32 then size.toNat else size.toNat + align.toNat - 1) ≤ MaxAllocSize

instance (size align : BitVec 64) : Decidable (IdealLayoutFit size align) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Ideal contract for `__rustc::__rust_alloc(size, align)` (`zeroed = false`) and
    `__rustc::__rust_alloc_zeroed(size, align)` (`zeroed = true`) over `A : RustAlloc`:
    returns a fresh `align`-aligned block `A.live ret size.toNat align.toNat` on normal `.Running`
    termination whenever `IdealLayoutFit size align` holds, with hardware exhaustion terminating in
    `ExecStatus.OutOfMemory`. -/
rust_spec rustAllocIdealSpec (ctx A : RustAlloc) (ctx zeroed : Bool)
    (size : u64) (align : u64) (sp : sp) : (ret : u64)
  requires_cond size ≠ 0#64 ∧ IsPow2Align align ∧ SmallLen size.toNat
  preserves     A.pool ∗ allocHookFrame sp
  ensures       if ret = 0#64 then ⌜¬ IdealLayoutFit size align⌝
                else ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64⌝ ∗
                  A.live ret size.toNat align.toNat ∗
                  (if zeroed then (ret ↦ₛ List.replicate size.toNat 0#8)
                   else memRegion ret size.toNat)
  oom_when      True

/-- Alignment-polymorphic contract for `__rustc::__rust_dealloc(p, size, align)` over
    `A : RustAlloc`. -/
rust_spec rustDeallocIdealSpec (ctx A : RustAlloc)
    (p : ptr) (size : u64) (align : u64) (sp : sp)
  requires_cond IsPow2Align align
  preserves     A.pool
  requires      A.live p size.toNat align.toNat ∗ memRegion p size.toNat
  preserves     allocHookFrame sp

/-- Ideal contract for `__rustc::__rust_realloc(p, old, align, new)` over `A : RustAlloc`:
    returns a fresh `align`-aligned block `A.live ret new.toNat align.toNat` containing `bs`
    whenever `IdealLayoutFit new align` holds, and leaves `p` unchanged on null return. -/
rust_spec rustReallocIdealSpec (ctx A : RustAlloc)
    (p : ptr) (old : u64) (align : u64) (new : u64)
    (ghost bs : List (BitVec 8)) (sp : sp) : (ret : u64)
  requires_cond new ≠ 0#64 ∧ IsPow2Align align ∧ SmallLen new.toNat ∧
                bs.length ≤ old.toNat ∧ bs.length ≤ new.toNat
  preserves     A.pool
  requires      A.live p old.toNat align.toNat ∗ (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old.toNat - bs.length)
  preserves     allocHookFrame sp
  ensures       if ret = 0#64 then
                  ⌜¬ IdealLayoutFit new align⌝ ∗
                  A.live p old.toNat align.toNat ∗ (p ↦ₛ bs) ∗
                    memRegion (p + BitVec.ofNat 64 bs.length) (old.toNat - bs.length)
                else
                  ⌜ret.toNat % align.toNat = 0 ∧ ret.toNat + new.toNat < 2 ^ 64⌝ ∗
                  A.live ret new.toNat align.toNat ∗ (ret ↦ₛ bs) ∗
                    memRegion (ret + BitVec.ofNat 64 bs.length) (new.toNat - bs.length)
  oom_when      True

/-- Contract for `__rust_no_alloc_shim_is_unstable_v2()`. -/
rust_spec rustShimIdealSpec (sp : sp)
  preserves allocHookFrame sp

/-- Ideal Rust `#[global_allocator]` hook bundle over `A : RustAlloc`. -/
structure AllocHooksIdeal (A : RustAlloc) (hooks : String → Option (State → State)) : Prop where
  alloc       : HookSat hooks "__rustc::__rust_alloc"        (rustAllocIdealSpec A false)
  allocZeroed : HookSat hooks "__rustc::__rust_alloc_zeroed" (rustAllocIdealSpec A true)
  realloc     : HookSat hooks "__rustc::__rust_realloc"      (rustReallocIdealSpec A)
  dealloc     : HookSat hooks "__rustc::__rust_dealloc"      (rustDeallocIdealSpec A)
  shim        : HookSat hooks "__rustc::__rust_no_alloc_shim_is_unstable_v2" rustShimIdealSpec

/-- Caller-facing contract for `__rustc::__rust_alloc` and `__rustc::__rust_alloc_zeroed` under
    `align.toNat <= 32` and `size.toNat <= MaxAllocSize`, returning non-null on `.Running`
    termination. -/
rust_spec rustAllocSimpleSpec (ctx A : RustAlloc) (ctx zeroed : Bool)
    (size : u64) (align : u64) (sp : sp) : (ret : u64)
  requires_cond size ≠ 0#64 ∧ IsPow2Align align ∧ align.toNat ≤ 32 ∧ size.toNat ≤ MaxAllocSize
  preserves     A.pool ∗ allocHookFrame sp
  ensures_pure  ret ≠ 0#64 ∧ ret.toNat % align.toNat = 0 ∧ ret.toNat + size.toNat < 2 ^ 64
  ensures       A.live ret size.toNat align.toNat ∗
                (if zeroed then (ret ↦ₛ List.replicate size.toNat 0#8)
                 else memRegion ret size.toNat)
  oom_when      True

/-- Caller-facing contract for `__rustc::__rust_realloc` under `align.toNat <= 32` and
    `new.toNat <= MaxAllocSize`, returning non-null on `.Running` termination. -/
rust_spec rustReallocSimpleSpec (ctx A : RustAlloc)
    (p : ptr) (old : u64) (align : u64) (new : u64)
    (ghost bs : List (BitVec 8)) (sp : sp) : (ret : u64)
  requires_cond new ≠ 0#64 ∧ IsPow2Align align ∧ align.toNat ≤ 32 ∧ new.toNat ≤ MaxAllocSize ∧
                bs.length ≤ old.toNat ∧ bs.length ≤ new.toNat
  preserves     A.pool
  requires      A.live p old.toNat align.toNat ∗ (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old.toNat - bs.length)
  preserves     allocHookFrame sp
  ensures_pure  ret ≠ 0#64 ∧ ret.toNat % align.toNat = 0 ∧ ret.toNat + new.toNat < 2 ^ 64
  ensures       A.live ret new.toNat align.toNat ∗ (ret ↦ₛ bs) ∗
                memRegion (ret + BitVec.ofNat 64 bs.length) (new.toNat - bs.length)
  oom_when      True

/-- Simple Rust `#[global_allocator]` hook bundle over `A : RustAlloc`. -/
structure AllocHooksSimple (A : RustAlloc) (hooks : String → Option (State → State)) : Prop where
  alloc       : HookSat hooks "__rustc::__rust_alloc"        (rustAllocSimpleSpec A false)
  allocZeroed : HookSat hooks "__rustc::__rust_alloc_zeroed" (rustAllocSimpleSpec A true)
  realloc     : HookSat hooks "__rustc::__rust_realloc"      (rustReallocSimpleSpec A)
  dealloc     : HookSat hooks "__rustc::__rust_dealloc"      (rustDeallocIdealSpec A)
  shim        : HookSat hooks "__rustc::__rust_no_alloc_shim_is_unstable_v2" rustShimIdealSpec

private theorem smallLen_of_le_maxAllocSize {n : Nat} (h : n ≤ MaxAllocSize) : SmallLen n := by
  unfold SmallLen MaxAllocSize at *
  omega

private theorem idealLayoutFit_of_simple {n align : BitVec 64}
    (ha : align.toNat ≤ 32) (hn : n.toNat ≤ MaxAllocSize) :
    IdealLayoutFit n align := by
  unfold IdealLayoutFit
  simp [ha, hn]

private theorem hookSat_conseq_ideal {α β : Type} {H : String → Option (State → State)}
    {name : String} {spec : Spec α} {spec' : Spec β} (f : β → α)
    (h : HookSat H name spec)
    (h_pre : ∀ y R s0, (s0.mem ⊨ spec'.pre y s0 ∗ R) → (s0.mem ⊨ spec.pre (f y) s0 ∗ R))
    (h_post : ∀ y R s0 sf, (sf.mem ⊨ spec.post (f y) s0 sf ∗ R) → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (h_no_panic : ∀ x R' s0 sf, ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf, ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ y R s0 sf, (sf.mem ⊨ spec.onOom (f y) s0 sf ∗ R) → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R) := by
      intro _ _ _ _ ho; first | exact ho | exact False.elim (not_satisfies_false_sepConj ho)) :
    HookSat H name spec' := by
  obtain ⟨fn, hfn, hok⟩ := h
  refine ⟨fn, hfn, ?_⟩
  intro y R s0 hrun hp hsp
  have hm := h_pre y R s0 hp
  obtain ⟨hkeep, hsym, hout⟩ := hok (f y) R s0 hrun hm hsp
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨hoom, hq⟩
  · exact Or.inl ⟨hret, hcc, h_post y R s0 (fn s0) hq⟩
  · exact False.elim (h_no_panic (f y) R s0 _ hq)
  · exact False.elim (h_no_exit (f y) code R s0 _ hq)
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, h_oom y R s0 (fn s0) hq⟩))

theorem rustAllocIdealSpec_refines_rustAllocSimpleSpec (A : RustAlloc) (zeroed : Bool)
    {hooks : String → Option (State → State)} {name : String}
    (hIdeal : HookSat hooks name (rustAllocIdealSpec A zeroed)) :
    HookSat hooks name (rustAllocSimpleSpec A zeroed) := by
  have hRef : HookSat hooks name
      ({ pre := fun (size, align, sp) s0 =>
           ⌜IdealLayoutFit size align⌝ ∗ (rustAllocIdealSpec A zeroed).pre (size, align, sp) s0
         post := fun (size, align, sp) s0 sf =>
           ⌜IdealLayoutFit size align⌝ ∗ (rustAllocIdealSpec A zeroed).post (size, align, sp) s0 sf
         onOom := fun (size, align, sp) s0 sf =>
           (rustAllocIdealSpec A zeroed).onOom (size, align, sp) s0 sf }) := by
    obtain ⟨fn, hfn, hok⟩ := hIdeal
    refine ⟨fn, hfn, ?_⟩
    intro y R s0 hrun hp hsp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    obtain ⟨hFit, hp'⟩ := hp
    obtain ⟨hkeep, hsym, hout⟩ := hok y R s0 hrun hp' hsp
    refine ⟨hkeep, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hq⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hFit, hq⟩
    · exact Or.inr hrest
  refine hookSat_conseq_ideal id hRef ?_ ?_
  · rintro ⟨size, align, sp⟩ R s0 hp
    dsimp only [rustAllocSimpleSpec, rustAllocIdealSpec, Spec.split, id_eq] at hp ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨hx0, hx1, hsp, hsz, hpow, ha, hmax⟩, hrest⟩
    exact ⟨idealLayoutFit_of_simple ha hmax,
      ⟨hx0, hx1, hsp, hsz, hpow, smallLen_of_le_maxAllocSize hmax⟩, hrest⟩
  · rintro ⟨size, align, sp⟩ R s0 sf hp
    dsimp only [rustAllocSimpleSpec, rustAllocIdealSpec, Spec.split, id_eq] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨hFit, hp⟩
    by_cases hZero : sf.readReg64 .x0 = 0#64
    · simp only [hZero, ↓reduceIte] at hp
      have hp' : sf.mem ⊨ ⌜¬IdealLayoutFit size align⌝ ∗ (A.pool ∗ allocHookFrame sp ∗ R) :=
        Satisfies.of_eq hp (by ac_rfl)
      rw [satisfies_pure_sepConj] at hp'
      exact False.elim (hp'.1 hFit)
    · simp only [hZero, ↓reduceIte] at hp
      have hp' : sf.mem ⊨ ⌜(sf.readReg64 .x0).toNat % align.toNat = 0 ∧
            (sf.readReg64 .x0).toNat + size.toNat < 2 ^ 64⌝ ∗
          (A.pool ∗ allocHookFrame sp ∗ A.live (sf.readReg64 .x0) size.toNat align.toNat ∗
            (if zeroed then sf.readReg64 .x0 ↦ₛ List.replicate size.toNat 0#8
             else memRegion (sf.readReg64 .x0) size.toNat) ∗ R) :=
        Satisfies.of_eq hp (by ac_rfl)
      rw [satisfies_pure_sepConj] at hp'
      have hout : sf.mem ⊨ ⌜sf.readReg64 .x0 ≠ 0#64 ∧ (sf.readReg64 .x0).toNat % align.toNat = 0 ∧
            (sf.readReg64 .x0).toNat + size.toNat < 2 ^ 64⌝ ∗
          (A.pool ∗ allocHookFrame sp ∗ A.live (sf.readReg64 .x0) size.toNat align.toNat ∗
            (if zeroed then sf.readReg64 .x0 ↦ₛ List.replicate size.toNat 0#8
             else memRegion (sf.readReg64 .x0) size.toNat) ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hZero, hp'.1.1, hp'.1.2⟩, hp'.2⟩
      exact Satisfies.of_eq hout (by ac_rfl)

theorem rustReallocIdealSpec_refines_rustReallocSimpleSpec (A : RustAlloc)
    {hooks : String → Option (State → State)} {name : String}
    (hIdeal : HookSat hooks name (rustReallocIdealSpec A)) :
    HookSat hooks name (rustReallocSimpleSpec A) := by
  have hRef : HookSat hooks name
      ({ pre := fun (p, old, align, new, bs, sp) s0 =>
           ⌜IdealLayoutFit new align⌝ ∗ (rustReallocIdealSpec A).pre (p, old, align, new, bs, sp) s0
         post := fun (p, old, align, new, bs, sp) s0 sf =>
           ⌜IdealLayoutFit new align⌝ ∗ (rustReallocIdealSpec A).post (p, old, align, new, bs, sp) s0 sf
         onOom := fun (p, old, align, new, bs, sp) s0 sf =>
           (rustReallocIdealSpec A).onOom (p, old, align, new, bs, sp) s0 sf }) := by
    obtain ⟨fn, hfn, hok⟩ := hIdeal
    refine ⟨fn, hfn, ?_⟩
    intro y R s0 hrun hp hsp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    obtain ⟨hFit, hp'⟩ := hp
    obtain ⟨hkeep, hsym, hout⟩ := hok y R s0 hrun hp' hsp
    refine ⟨hkeep, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hq⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hFit, hq⟩
    · exact Or.inr hrest
  refine hookSat_conseq_ideal id hRef ?_ ?_
  · rintro ⟨p, old, align, new, bs, sp⟩ R s0 hp
    dsimp only [rustReallocSimpleSpec, rustReallocIdealSpec, Spec.split, id_eq] at hp ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨hx0, hx1, hx2, hx3, hsp, hnew, hpow, ha, hmax, hbs1, hbs2⟩, hrest⟩
    exact ⟨idealLayoutFit_of_simple ha hmax,
      ⟨hx0, hx1, hx2, hx3, hsp, hnew, hpow, smallLen_of_le_maxAllocSize hmax, hbs1, hbs2⟩, hrest⟩
  · rintro ⟨p, old, align, new, bs, sp⟩ R s0 sf hp
    dsimp only [rustReallocSimpleSpec, rustReallocIdealSpec, Spec.split, id_eq] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨hFit, hp⟩
    by_cases hZero : sf.readReg64 .x0 = 0#64
    · simp only [hZero, ↓reduceIte] at hp
      have hp' : sf.mem ⊨ ⌜¬IdealLayoutFit new align⌝ ∗
          (A.pool ∗ allocHookFrame sp ∗ A.live p old.toNat align.toNat ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old.toNat - bs.length) ∗ R) :=
        Satisfies.of_eq hp (by ac_rfl)
      rw [satisfies_pure_sepConj] at hp'
      exact False.elim (hp'.1 hFit)
    · simp only [hZero, ↓reduceIte] at hp
      have hp' : sf.mem ⊨ ⌜(sf.readReg64 .x0).toNat % align.toNat = 0 ∧
            (sf.readReg64 .x0).toNat + new.toNat < 2 ^ 64⌝ ∗
          (A.pool ∗ allocHookFrame sp ∗ A.live (sf.readReg64 .x0) new.toNat align.toNat ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗ R) :=
        Satisfies.of_eq hp (by ac_rfl)
      rw [satisfies_pure_sepConj] at hp'
      have hout : sf.mem ⊨ ⌜sf.readReg64 .x0 ≠ 0#64 ∧ (sf.readReg64 .x0).toNat % align.toNat = 0 ∧
            (sf.readReg64 .x0).toNat + new.toNat < 2 ^ 64⌝ ∗
          (A.pool ∗ allocHookFrame sp ∗ A.live (sf.readReg64 .x0) new.toNat align.toNat ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hZero, hp'.1.1, hp'.1.2⟩, hp'.2⟩
      exact Satisfies.of_eq hout (by ac_rfl)

theorem AllocHooksIdeal.toAllocHooksSimple {A : RustAlloc}
    {hooks : String → Option (State → State)} (h : AllocHooksIdeal A hooks) :
    AllocHooksSimple A hooks where
  alloc := rustAllocIdealSpec_refines_rustAllocSimpleSpec A false h.alloc
  allocZeroed := rustAllocIdealSpec_refines_rustAllocSimpleSpec A true h.allocZeroed
  realloc := rustReallocIdealSpec_refines_rustReallocSimpleSpec A h.realloc
  dealloc := h.dealloc
  shim := h.shim

end ProofLib.RustHeap

end
