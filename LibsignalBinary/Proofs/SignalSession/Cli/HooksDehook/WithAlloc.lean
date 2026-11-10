/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import

/-!
# Allocator-Pool Framing Combinator for Non-Allocating Hook Contracts (`HooksDehook.WithAlloc`)

Shared untrusted combinator for lifting non-allocating extern / ghost hook contracts (`HookOk f
(withVmPreserved spec)`) across the CLI budget-threaded allocator pool `A.pool lim st s`.

## What the `A.pool lim st s` Frame Means

In the budget-threaded CLI verification stack (`LibsignalBinary.Heap.IfaceBudget` /
`LibsignalBinary.Heap.SpecBudget`), `A : RustCliAllocBudget M` threads an abstract allocator cost
state `st : M.σ` under capacity limits `lim : BudgetLimits` via a state-indexed separation-logic
invariant `A.pool lim st : State → SepProp`:

- Under the real linked `mallocng` allocator (`MallocngBridgeBudget.mallocngRustCliAllocBudget`),
  `A.pool lim st s` owns `mallocng`'s global allocator metadata (`__malloc_context` / `ctx` globals,
  group/meta bookkeeping), `StdErrnoCell`, `StaticMappedCover` (virtual-address mapping coverage),
  and the `FitsTrace` budget invariant tying `st` to `s`'s virtual-memory and physical-memory state
  (`s.mem.perm`, `s.brk`, `s.mmapNext`, `s.physMemAvail`, `s.mlockAvail`).
- Because `A.pool lim st s` depends on those five VM/process fields of the `State` `s` (not just the
  partial byte heap passed to `SepProp`), ordinary separation-logic framing `R := A.pool lim st s0 ∗ R₀`
  leaves `A.pool lim st s0` in the postcondition evaluated at the **entry** state `s0`, whereas
  budget-threaded callers require `A.pool lim st sf` evaluated at the **post-call** state `sf` (with
  unchanged cost state `st`, matching zero allocation events `M.stepEvents [] st = st`).
- `A.pool_transport : VmPreserved s0 sf → A.pool lim st s0 = A.pool lim st sf` bridges `s0` to `sf`
  whenever the callee preserves `VmPreserved s0 sf` (`s0.mem.perm = sf.mem.perm`, `brk`,
  `mmapNext`, `physMemAvail`, `mlockAvail`).

`withAlloc (M := M) A lim spec` packages this non-allocating pool-threading discipline into a
`Spec (α × M.σ)`:
- **`.pre ⟨x, st⟩ s`**: `spec.pre x s ∗ A.pool lim st s` (disjointness from the allocator pool at
  entry `s`);
- **`.post ⟨x, st⟩ s0 sf`**: `spec.post x s0 sf ∗ A.pool lim st sf` (allocator pool re-indexed to the
  exit state `sf` at unchanged cost state `st`);
- **`.onPanic` / `.onExit` / `.onOom`**: unchanged from `spec` (dropping `A.pool lim st s0` on
  abnormal termination via affine `Satisfies.drop_mid`, so specs with non-trivial `onPanic` such as
  `timeAddSpec` and `durationSinceBoundedSpec` lift without extra side conditions).

Used uniformly by C11's `ExtraGhostSpecs.GhostRowSpecOk` and the Cutover-2 per-row `*Ghost` modules
(`BcmpGhost`, `StrlenGhost`, `MemmoveGhost`, RustStd / Curve25519-dalek ghost hooks).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc

open Arm64 ProofLib
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

/-- Thread `A.pool lim st` across a non-allocating `spec : Spec α` at unchanged cost-model state
    `st : M.σ`, pairing the ghost witness `(x, st) : α × M.σ`. Preserves `onPanic`, `onExit`, and
    `onOom` verbatim. -/
@[expose] def withAlloc {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    Spec (α × M.σ) where
  pre := fun ⟨x, st⟩ s => spec.pre x s ∗ A.pool lim st s
  post := fun ⟨x, st⟩ s0 sf => spec.post x s0 sf ∗ A.pool lim st sf
  onPanic := fun ⟨x, _⟩ s0 sf => spec.onPanic x s0 sf
  onExit := fun ⟨x, _⟩ code s0 sf => spec.onExit x code s0 sf
  onOom := fun ⟨x, _⟩ s0 sf => spec.onOom x s0 sf

/-- Lift `HookOk f (withVmPreserved spec)` to `HookOk f (withAlloc (M := M) A lim spec)` for any
    `spec : Spec α` (including specs with non-`⌜False⌝` `onPanic` / `onExit` / `onOom`), transporting
    `A.pool lim st s0` to `A.pool lim st (f s0)` via `A.pool_transport` on normal return and
    dropping the entry pool via `Satisfies.drop_mid` on abnormal termination. -/
theorem hookOk_withAlloc_of_withVmPreserved {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State} {spec : Spec α}
    (hh : HookOk f (withVmPreserved spec)) :
    HookOk f (withAlloc (M := M) A lim spec) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [withAlloc] at hpre
  have hpre' : s0.mem ⊨ (withVmPreserved spec).pre x s0 ∗ (A.pool lim st s0 ∗ R) := by
    dsimp only [withVmPreserved]
    rwa [← sepConj_assoc]
  obtain ⟨hkf, hsym, hout⟩ := hh x (A.pool lim st s0 ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, he⟩ | ⟨hoom, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, hrest⟩
    dsimp only [withAlloc]
    rw [A.pool_transport lim st s0 (f s0) hvm, sepConj_assoc]
    exact hrest
  · exact Or.inr (Or.inl ⟨hpan, Satisfies.drop_mid hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, Satisfies.drop_mid he⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, Satisfies.drop_mid ho⟩))

/-- Lift `HookOk f (withVmPreserved spec)` to
    `HookOk f (withAlloc (M := M) A lim (withVmPreserved spec))` (retaining `⌜VmPreserved s0 sf⌝`
    inside `.post` alongside `A.pool lim st sf`, matching C11 §1.4's `GhostRowSpecOk` arms). -/
theorem hookOk_withAlloc_withVmPreserved {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {f : State → State} {spec : Spec α}
    (hh : HookOk f (withVmPreserved spec)) :
    HookOk f (withAlloc (M := M) A lim (withVmPreserved spec)) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  dsimp only [withAlloc] at hpre
  have hpre' : s0.mem ⊨ (withVmPreserved spec).pre x s0 ∗ (A.pool lim st s0 ∗ R) := by
    rwa [← sepConj_assoc]
  obtain ⟨hkf, hsym, hout⟩ := hh x (A.pool lim st s0 ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, he⟩ | ⟨hoom, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    have hpost_dup := hpost
    dsimp only [withVmPreserved] at hpost_dup
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_dup
    have hvm : VmPreserved s0 (f s0) := hpost_dup.1
    dsimp only [withAlloc]
    rw [A.pool_transport lim st s0 (f s0) hvm, sepConj_assoc]
    exact hpost
  · exact Or.inr (Or.inl ⟨hpan, Satisfies.drop_mid hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, Satisfies.drop_mid he⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, Satisfies.drop_mid ho⟩))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
