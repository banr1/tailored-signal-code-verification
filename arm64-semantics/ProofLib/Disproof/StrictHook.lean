/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Disproof.Basic
public import ProofLib.Hoare.LibcHooks
import Arm64.Trusted.Spec.SepLogic

/-!
# Strict Hook Wrapper and OOM Witnesses

Wraps external hooks in `strictHook`, which preserves `HookOk` on valid AAPCS64 call states
and transitions out-of-contract calls to `.Exception "callee precondition violated"`. Also
provides the always-null `oomAllocator` model, `oomMallocRegionSpec`, and permission-based
refutation lemmas for `ValidHookCall`.
-/

@[expose] public section

namespace ProofLib.Disproof

open Arm64 ProofLib

/-! ## `ValidHookCall` and `strictHook` -/

/-- Asserts that `s` is a valid AAPCS64 call state satisfying `calleeSpec.pre y s ∗ R`
    for some ghost witness `y : β` and separation-logic frame `R : SepProp`. -/
def ValidHookCall {β : Type} (calleeSpec : Spec β) (s : State) : Prop :=
  ∃ (y : β) (R : SepProp),
    s.status = .Running ∧ s.spAligned = true ∧ (s.mem ⊨ calleeSpec.pre y s ∗ R)

/-- Wrapper around an external hook `fallback` that evaluates `fallback s` when
    `ValidHookCall calleeSpec s` holds and sets `status := .Exception "callee precondition violated"`
    otherwise, preserving `HookOk`. -/
noncomputable def strictHook {β : Type} (calleeSpec : Spec β) (fallback : State → State) (s : State) : State :=
  letI := Classical.propDecidable (ValidHookCall calleeSpec s)
  if ValidHookCall calleeSpec s then
    fallback s
  else
    { s with status := .Exception "callee precondition violated" }

theorem strictHook_eq_of_valid {β : Type} {calleeSpec : Spec β} {fallback : State → State}
    {s : State} (h : ValidHookCall calleeSpec s) :
    strictHook calleeSpec fallback s = fallback s := by
  simp [strictHook, h]

theorem strictHook_eq_of_not_valid {β : Type} {calleeSpec : Spec β} {fallback : State → State}
    {s : State} (h : ¬ ValidHookCall calleeSpec s) :
    strictHook calleeSpec fallback s = { s with status := .Exception "callee precondition violated" } := by
  simp [strictHook, h]

theorem strictHook_ok {β : Type} {calleeSpec : Spec β} {fallback : State → State}
    (hok : HookOk fallback calleeSpec) :
    HookOk (strictHook calleeSpec fallback) calleeSpec := by
  intro y R s0 hrun hpre hsp
  have hval : ValidHookCall calleeSpec s0 := ⟨y, R, hrun, hsp, hpre⟩
  rw [strictHook_eq_of_valid hval]
  exact hok y R s0 hrun hpre hsp

/-- Single-step transition when `s.pc` points to `strictHook calleeSpec fallback` and
    `ValidHookCall calleeSpec s` does not hold: execution steps in one step to
    `{ s with status := .Exception "callee precondition violated" }`. -/
theorem Step.of_strictHook_invalid {β : Type} {prog : Program}
    {calleeSpec : Spec β} {fallback : State → State} {s : State}
    (hrun : s.status = .Running)
    (hextern : prog.externAt? s.pc = some (strictHook calleeSpec fallback))
    (hinvalid : ¬ ValidHookCall calleeSpec s) :
    Step prog s { s with status := .Exception "callee precondition violated" } := by
  have heq := strictHook_eq_of_not_valid (fallback := fallback) hinvalid
  have hkeep : s.mem.KeepsFrozen (strictHook calleeSpec fallback s).mem := by
    rw [heq]; exact Memory.KeepsFrozen.refl s.mem
  have hsym : (strictHook calleeSpec fallback s).symtab = s.symtab := by
    rw [heq]
  have hstep := Step.extern hrun hextern hkeep hsym
  rwa [heq] at hstep

/-! ## Always-NULL OOM Allocator Model and Hook Witnesses -/

/-- Always-NULL symbolic `Allocator` model representing out-of-memory (OOM) at every call site. -/
def oomAllocator : ProofLib.Allocator where
  ptr := fun _ _ => 0#64

@[simp]
theorem oomAllocator_ptr (idx : Nat) (req : BitVec 64) :
    oomAllocator.ptr idx req = 0#64 := rfl

@[simp]
theorem oomAllocator_allocAt (idx : Nat) (req : BitVec 64) (len : Nat := req.toNat) :
    oomAllocator.allocAt idx req len = emp := rfl

@[simp]
theorem oomAllocator_callocAt (idx : Nat) (nmemb size : BitVec 64)
    (len : Nat := (nmemb * size).toNat) :
    oomAllocator.callocAt idx nmemb size len = emp := rfl

@[simp]
theorem oomAllocator_allocSeq (idx : Nat) (reqs : List (BitVec 64 × Nat)) :
    oomAllocator.allocSeq idx reqs = emp := by
  induction reqs generalizing idx with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨req, len⟩
    simp [ProofLib.Allocator.allocSeq, ih]

/-- Minimal OOM-capable `malloc(req)` specification without a stack-frame conjunct:
    either returns `0#64` (`emp`) or a fresh `memRegion ptr req.toNat`. -/
def oomMallocRegionSpec : Spec (BitVec 64) where
  pre := fun req s0 =>
    ⌜s0.readReg64 .x0 = req⌝
  post := fun req _ sf =>
    ∃∗ ptr : BitVec 64,
      ⌜sf.readReg64 .x0 = ptr⌝ ∗
      ProofLib.Allocator.optRegion ptr req.toNat

theorem hookAllocNull_oomMallocRegion_ok : HookOk hookAllocNull oomMallocRegionSpec := by
  refine hookReturnZero_ok fun req R s0 hpre => ?_
  simp only [oomMallocRegionSpec, satisfies_pure_sepConj] at hpre
  change s0.mem ⊨ (∃∗ ptr : BitVec 64,
    ⌜(hookReturnZero s0).readReg64 .x0 = ptr⌝ ∗
    ProofLib.Allocator.optRegion ptr req.toNat) ∗ R
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨0#64, ?_⟩
  simp only [hookReturnZero, retHook, State.readReg64_setPC,
    ProofLib.Allocator.optRegion_zero, sepConj_emp, satisfies_pure_sepConj]
  exact ⟨by simp, hpre.2⟩

/-! ## Pre-Packaged Strict Memory Hooks -/

/-- Strict `memcpy` hook wrapped with `memcpyRegionSpec` (no stack-frame conjunct). -/
noncomputable def strictMemcpyRegionHook : State → State :=
  strictHook memcpyRegionSpec hookMemcpy

theorem strictMemcpyRegionHook_ok :
    HookOk strictMemcpyRegionHook memcpyRegionSpec :=
  strictHook_ok hookMemcpy_region_ok

/-! ## Refuting `ValidHookCall` on Unmapped / Non-Writable Pointers -/

/-- Generic refutation of `ValidHookCall`: if every witness `(y, R)` satisfying
    `s.mem ⊨ calleeSpec.pre y s ∗ R` requires `s.mem.perm a = some .rw` at some address `a`,
    and `s.mem.perm a ≠ some .rw` (for example `s.mem.perm a = none`), then `¬ ValidHookCall calleeSpec s`. -/
theorem not_validHookCall_of_perm_ne_rw {β : Type} {calleeSpec : Spec β} {s : State} {a : BitVec 64}
    (hreq : ∀ y R, (s.mem ⊨ calleeSpec.pre y s ∗ R) → s.mem.perm a = some .rw)
    (hnot_rw : s.mem.perm a ≠ some .rw) :
    ¬ ValidHookCall calleeSpec s := by
  rintro ⟨y, R, _, _, hpre⟩
  exact hnot_rw (hreq y R hpre)

theorem perm_rw_base_of_memRegion {m : Memory} {ptr : BitVec 64} {len : Nat} {R : SepProp}
    (h : m ⊨ memRegion ptr len ∗ R) (hlen : 0 < len) :
    m.perm ptr = some .rw := by
  refine (IsBlock.memRegion ptr len).perm_rw h ?_
  simp only [InRegion, BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod]
  exact hlen

/-- Calling `memcpyRegionSpec` with positive length `0 < (s.readReg64 .x2).toNat` when the
    destination pointer `s.readReg64 .x0 = addr` is not read-write mapped (`m0.perm addr ≠ some .rw`,
    e.g. `NULL` or `NULL + offset` with `.perm = none`) violates `ValidHookCall memcpyRegionSpec s`. -/
theorem not_validHookCall_memcpyRegion_of_dst_not_rw {s : State} {m0 : Memory} {addr : BitVec 64}
    (hlen : 0 < (s.readReg64 .x2).toNat := by with_unfolding_all decide)
    (hnot_rw : m0.perm addr ≠ some .rw)
    (haddr : s.readReg64 .x0 = addr := by with_unfolding_all rfl)
    (hmem : s.mem.perm addr = m0.perm addr := by with_unfolding_all rfl) :
    ¬ ValidHookCall memcpyRegionSpec s := by
  have hnot_rw' : s.mem.perm (s.readReg64 .x0) ≠ some .rw := by rw [haddr, hmem]; exact hnot_rw
  refine not_validHookCall_of_perm_ne_rw (a := s.readReg64 .x0) (fun ⟨dst, src, bs⟩ R hpre => ?_) hnot_rw'
  simp only [memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, _, hx2⟩, hmem⟩
  rw [hx0]
  rw [hx2] at hlen
  exact perm_rw_base_of_memRegion hmem hlen

end ProofLib.Disproof
