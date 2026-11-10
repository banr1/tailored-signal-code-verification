/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
import Arm64.Trusted.Spec.SepLogic

/-!
# Byte-Granular Memory Regions, Frame Conditions, and Region Disjointness

Defines the `AgreesOutside` frame condition and `BytesAgree` buffer congruence predicate, proves
region-disjointness and store-preservation lemmas across byte and multi-byte writes, and provides
context-pruned `bv_omega` tactics (`bv_omega_fast`, `wp_bv_omega`, `wp_step_bv_omega`) for region
offset arithmetic.
-/

namespace ProofLib

open Arm64

@[expose] public section

/-- Frame condition: `m₂` agrees with `m₁` on byte contents and `lazyFree` state at every byte
    outside `[base, base + len)`, permissions are unchanged everywhere, no non-`lazyFree` byte
    becomes `lazyFree`, and anonymous bytes remain anonymous (stores never change permissions or
    anonymity and only clear `lazyFree` inside `[base, base + len)`). -/
def AgreesOutside (m₁ m₂ : Memory) (base : BitVec 64) (len : Nat) : Prop :=
  (∀ a : BitVec 64, OutsideRegion base len a → m₂.read8 a = m₁.read8 a) ∧
  m₂.perm = m₁.perm ∧
  (∀ a : BitVec 64, OutsideRegion base len a → m₂.isLazyFree a = m₁.isLazyFree a) ∧
  (∀ a : BitVec 64, m₁.isLazyFree a = false → m₂.isLazyFree a = false) ∧
  (∀ a : BitVec 64, m₁.isAnon a = true → m₂.isAnon a = true)

/-- Byte-for-byte equality of the `len` bytes at `a₁` in `m₁` and at `a₂` in `m₂`. -/
def BytesAgree (m₁ : Memory) (a₁ : BitVec 64) (m₂ : Memory) (a₂ : BitVec 64) (len : Nat) : Prop :=
  ∀ i : Nat, i < len → m₁.read8 (a₁ + BitVec.ofNat 64 i) = m₂.read8 (a₂ + BitVec.ofNat 64 i)

/-- Assert that memory `m` at `buf` begins with the byte list `bytes`. -/
@[simp, arm64_norm]
def MemMatchesBytes (m : Memory) (buf : BitVec 64) : List (BitVec 8) → Prop
  | [] => True
  | [b0] => m.read8 buf = b0
  | [b0, b1] => m.read8 buf = b0 ∧ m.read8 (buf + 1#64) = b1
  | b0 :: b1 :: b2 :: rest =>
    m.read8 buf = b0 ∧ m.read8 (buf + 1#64) = b1 ∧ m.read8 (buf + 2#64) = b2 ∧
    MemMatchesBytes m (buf + 3#64) rest

end

public meta section

/-- Run `tac` speculatively with `recover := false`, restoring the tactic state and message log
    if `tac` fails. -/
def tryTacticQuiet {α : Type} (tac : Lean.Elab.Tactic.TacticM α) : Lean.Elab.Tactic.TacticM Bool := do
  let savedMsgs ← Lean.Core.getMessageLog
  let ok ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.withoutRecover tac)
  if !ok then
    Lean.Core.setMessageLog savedMsgs
  return ok

/-- Constants from `Arm64` that represent pure register reads and register identifiers, which
    should be preserved as `BitVec` atoms in `wp_bv_omega` and `hasConstrainedFVar` (provided they
    do not wrap a heavy `State.writeReg*` / `State.set*` spine). -/
def isAllowedWpConst (declName : Lean.Name) : Bool :=
  declName == ``State.readReg64 ||
  declName == ``State.readReg32 ||
  declName == ``State.readReg ||
  declName == ``State.sp ||
  declName == ``Reg ||
  declName.getPrefix == `Arm64.Reg

/-- Pure arithmetic `Prop` / `Nat` / `BitVec` abbreviations and constants under `Arm64` and
    `ProofLib` (such as `Arm64.Rust.SmallLen`, `Arm64.Rust.IsPow2Align`, `Arm64.Rust.LayoutOk`,
    `Arm64.Rust.BudgetOk`, `Arm64.Rust.GlobalAlloc.budgetOk`, `Arm64.Rust.hookStack`, and their
    `ProofLib.RustHeap` counterparts) that should not be pruned as heavy machine-state terms by
    `isHeavyHypType` before `wp_bv_omega` / `wp_omega_bounded`. -/
def isAllowedArithConst (declName : Lean.Name) : Bool :=
  declName == `Arm64.Rust.SmallLen ||
  declName == `Arm64.Rust.IsPow2Align ||
  declName == `Arm64.Rust.isPow2Align ||
  declName == `Arm64.Rust.LayoutOk ||
  declName == `Arm64.Rust.layoutOk ||
  declName == `Arm64.Rust.BudgetOk ||
  declName == `Arm64.Rust.GlobalAlloc.budgetOk ||
  declName == `Arm64.Rust.GlobalAlloc.maxGuaranteedAlign ||
  declName == `Arm64.Rust.GlobalAlloc.maxLiveBytes ||
  declName == `Arm64.Rust.GlobalAlloc.maxLiveBlocks ||
  declName == `Arm64.Rust.GlobalAlloc.stackBytes ||
  declName == `Arm64.Rust.hookStack ||
  declName == `Arm64.PAGE_SIZE ||
  declName == `Arm64.pageAlignUp ||
  declName == `Arm64.MMAP_MIN_ADDR ||
  declName == `ProofLib.RustHeap.SmallLen ||
  declName == `ProofLib.RustHeap.LayoutOk ||
  declName == `ProofLib.RustHeap.IsPow2Align ||
  declName == `ProofLib.RustHeap.IdealLayoutFit ||
  declName == `ProofLib.RustHeap.MaxAllocSize ||
  declName == `ProofLib.RustHeap.allocHookStack

/-- Return `true` if `ty` mentions machine-state updates, memory, program, separation-logic, or
    protocol constants that are irrelevant to pure `BitVec`/`Nat` arithmetic and expensive for
    `bv_omega` to traverse. -/
def isHeavyHypType (ty : Lean.Expr) : Bool :=
  (ty.find? fun e =>
    if let .const declName _ := e then
      if isAllowedWpConst declName || isAllowedArithConst declName then
        false
      else
        let root := declName.getRoot
        root == `Arm64 || root == `ProofLib || root == `CryptoVerification || root == `Specifications
    else
      false).isSome

/-- A term `omega` treats as an opaque atom and that may be defined away: a local variable, or a
    pure register / `sp` read (`isAllowedWpConst` head, no heavy state argument). -/
def isPrunableOmegaAtom (e : Lean.Expr) : Bool :=
  e.isFVar || (match e.getAppFn with
    | .const n _ => isAllowedWpConst n && !e.getAppArgs.isEmpty && !isHeavyHypType e
    | _ => false)

/-- Does `atom` (see `isPrunableOmegaAtom`) possibly occur in `e`? Local variables are matched
    exactly; register reads are matched up to reducible defeq of their arguments (so `Reg.x0` and
    `Reg.gpr 0#5` are the same register), and any same-head read under a binder counts. -/
def omegaAtomMayOccur (atom e : Lean.Expr) : Lean.MetaM Bool := do
  if let .fvar atomId := atom then return e.containsFVar atomId
  let head := atom.getAppFn
  let nArgs := atom.getAppNumArgs
  let cands ← (do
    let r ← IO.mkRef (#[] : Array Lean.Expr)
    e.forEach fun t => do
      if t.getAppFn == head && t.getAppNumArgs == nArgs then r.modify (·.push t)
    r.get : Lean.MetaM (Array Lean.Expr))
  for t in cands do
    if t.hasLooseBVars || t == atom then return true
    if ← Lean.Meta.withNewMCtxDepth <| Lean.Meta.withReducible <| Lean.Meta.isDefEq t atom then
      return true
  return false

/-- Hypotheses of `g` that only define an otherwise-unused arithmetic atom: `x = e` or `e = x`
    (over `BitVec` / `Nat` / `Int`) where `x` (see `isPrunableOmegaAtom`) occurs in neither `e`,
    the goal, nor any other hypothesis. Clearing them keeps a `bv_omega` goal provable (any
    counter-model of the rest extends by choosing `x := e`) and removes their `% 2^w` case
    splits. Iterates a few rounds, since dropping one definition can free another atom. -/
def omegaDefinitionalHyps (g : Lean.MVarId) : Lean.MetaM (Array Lean.FVarId) := g.withContext do
  let lctx ← Lean.getLCtx
  let goalTy ← Lean.instantiateMVars (← g.getType)
  let mut entries : Array (Lean.FVarId × Lean.Expr) := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← Lean.instantiateMVars decl.type
    let body := match decl.value? with
      | some v => Lean.mkApp ty v
      | none => ty
    entries := entries.push (decl.fvarId, body)
  let mut dropped : Array Lean.FVarId := #[]
  for _ in [0:4] do
    let mut changed := false
    for (fv, ty) in entries do
      if dropped.contains fv then continue
      let some (α, lhs, rhs) := ty.eq? | continue
      unless α.isAppOf ``BitVec || α.isConstOf ``Nat || α.isConstOf ``Int do continue
      let mut isDef := false
      for (atom, other) in [(lhs, rhs), (rhs, lhs)] do
        if isDef || !isPrunableOmegaAtom atom then continue
        if let .fvar atomId := atom then
          if (← atomId.getDecl).isLet then continue
        if ← omegaAtomMayOccur atom other then continue
        if ← omegaAtomMayOccur atom goalTy then continue
        let mut elsewhere := false
        for (fv', ty') in entries do
          if fv' == fv || dropped.contains fv' then continue
          if let .fvar atomId := atom then
            if fv' == atomId then continue
          if ← omegaAtomMayOccur atom ty' then
            elsewhere := true
            break
        unless elsewhere do isDef := true
      if isDef then
        dropped := dropped.push fv
        changed := true
    unless changed do break
  return dropped

end

@[expose] public section

theorem bitvec_ult_eq_true_to_nat {w : Nat} (x y : BitVec w) :
    (BitVec.ult x y = true) ↔ (x.toNat < y.toNat) := by
  simp [BitVec.ult]

theorem bitvec_ule_eq_true_to_nat {w : Nat} (x y : BitVec w) :
    (BitVec.ule x y = true) ↔ (x.toNat ≤ y.toNat) := by
  simp [BitVec.ule]

theorem bitvec_ult_eq_false_to_nat {w : Nat} (x y : BitVec w) :
    (BitVec.ult x y = false) ↔ ¬(x.toNat < y.toNat) := by
  simp [BitVec.ult]

theorem bitvec_ule_eq_false_to_nat {w : Nat} (x y : BitVec w) :
    (BitVec.ule x y = false) ↔ ¬(x.toNat ≤ y.toNat) := by
  simp [BitVec.ule]

end

public meta section

/-- Fast `bv_omega` for region-offset arithmetic: clears all `Prop` hypotheses and non-numeric
    (or state/protocol-dependent) `let`-bindings from the local context before running `bv_omega`,
    preventing `simp at *` and `omega` from traversing large machine-state hypotheses (`s.mem = ...`)
    in long proofs. -/
elab "bv_omega_fast" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut toClear : Array Lean.FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        let heavyVal := match decl.value? with
          | some v => isHeavyHypType v
          | none => false
        if (← Lean.Meta.isProp ty) ||
           (decl.isLet && ((!ty.isAppOf ``BitVec && !ty.isConstOf ``Nat) || heavyVal)) then
          toClear := toClear.push decl.fvarId
    let goal' ← goal.tryClearMany toClear
    Lean.Elab.Tactic.replaceMainGoal [goal']
    Lean.Elab.Tactic.evalTactic (← `(tactic| bv_omega))

/-- Fast `bv_omega` for `SepWP` path-condition arithmetic: clears `State`/`Memory`/`SepProp`
    hypotheses and non-numeric `let`-bindings from the local context, keeps pure `BitVec`/`Nat`
    path conditions, and clears equations that only define an otherwise unused register read or
    variable (`omegaDefinitionalHyps`). -/
elab "wp_bv_omega" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut toClear : Array Lean.FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        let heavyVal := match decl.value? with
          | some v => isHeavyHypType v
          | none => false
        if ((← Lean.Meta.isProp ty) && isHeavyHypType ty) ||
           (decl.isLet && ((!ty.isAppOf ``BitVec && !ty.isConstOf ``Nat) || heavyVal)) then
          toClear := toClear.push decl.fvarId
    let goal' ← goal.tryClearMany toClear
    let goal' ← goal'.tryClearMany (← omegaDefinitionalHyps goal')
    Lean.Elab.Tactic.replaceMainGoal [goal']
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      try simp only [bitvec_ult_eq_true_to_nat, bitvec_ule_eq_true_to_nat,
                     bitvec_ult_eq_false_to_nat, bitvec_ule_eq_false_to_nat] at *
      bv_omega)))

/-- Fast `bv_omega` for `wpStepCore` PC branch resolution: clears heavy hypotheses, non-numeric
    `let`-bindings, and unused definitional equations (`omegaDefinitionalHyps`), then runs standard
    `bv_omega` without rewriting `BitVec.ult`/`BitVec.ule`, resolving equality and countdown loop
    branches without collapsing comparison branches handled by `wp_if`. -/
elab "wp_step_bv_omega" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut toClear : Array Lean.FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        let heavyVal := match decl.value? with
          | some v => isHeavyHypType v
          | none => false
        if ((← Lean.Meta.isProp ty) && isHeavyHypType ty) ||
           (decl.isLet && ((!ty.isAppOf ``BitVec && !ty.isConstOf ``Nat) || heavyVal)) then
          toClear := toClear.push decl.fvarId
    let goal' ← goal.tryClearMany toClear
    let goal' ← goal'.tryClearMany (← omegaDefinitionalHyps goal')
    Lean.Elab.Tactic.replaceMainGoal [goal']
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      try simp only [zeroExtend64_eq_zero_iff_32, zeroExtend64_eq_zero_iff_16,
                     zeroExtend64_eq_zero_iff_8, zeroExtend32_eq_zero_iff_16,
                     zeroExtend32_eq_zero_iff_8] at *
      bv_omega)))

end

@[expose] public section

/-! ## Regions -/

/-- Membership and non-membership are complementary, by definition. -/
theorem outsideRegion_iff_not_inRegion (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    OutsideRegion base len a ↔ ¬ InRegion base len a := by
  simp [OutsideRegion, InRegion]

/-- Positional characterization of `InRegion`: `a` lies in `[base, base + len)` iff `a = base + i`
    for some `i < len`. -/
theorem inRegion_iff_exists_offset (base : BitVec 64) (len : Nat) (a : BitVec 64)
    (hlen : len ≤ 2 ^ 64) :
    InRegion base len a ↔ ∃ i : Nat, i < len ∧ a = base + BitVec.ofNat 64 i := by
  constructor
  · intro h
    refine ⟨(a - base).toNat, h, ?_⟩
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  · rintro ⟨i, hi, rfl⟩
    have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi hlen
    simp only [InRegion]
    bv_omega

/-- The `len`-byte region at `base` contains `base + i` for every `i < len`. -/
theorem inRegion_base_add (base : BitVec 64) (len i : Nat) (hi : i < len) (hlen : len ≤ 2 ^ 64) :
    InRegion base len (base + BitVec.ofNat 64 i) :=
  (inRegion_iff_exists_offset base len _ hlen).mpr ⟨i, hi, rfl⟩

/-- Region disjointness is symmetric. -/
theorem _root_.Arm64.DisjointRegions.symm {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) : DisjointRegions b₂ n₂ b₁ n₁ := ⟨h.2, h.1⟩

/-- Disjoint regions share no address: every address of the second lies outside the first. -/
theorem _root_.Arm64.DisjointRegions.outside {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) {a : BitVec 64} (ha : InRegion b₂ n₂ a)
    (hlen : n₂ ≤ 2 ^ 64) : OutsideRegion b₁ n₁ a := by
  rcases (inRegion_iff_exists_offset b₂ n₂ a hlen).mp ha with ⟨i, hi, rfl⟩
  have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi hlen
  have h1 := h.1
  have h2 := h.2
  simp only [OutsideRegion]
  bv_omega

/-- Region disjointness at widths `8`, `8` is exactly `Memory.Disjoint64`. -/
theorem disjointRegions_iff_disjoint64 (a₁ a₂ : BitVec 64) :
    DisjointRegions a₁ 8 a₂ 8 ↔ Memory.Disjoint64 a₁ a₂ := Iff.rfl

/-- Region disjointness at widths `16`, `16` is exactly `Memory.Disjoint128`. -/
theorem disjointRegions_iff_disjoint128 (a₁ a₂ : BitVec 64) :
    DisjointRegions a₁ 16 a₂ 16 ↔ Memory.Disjoint128 a₁ a₂ := Iff.rfl

/-- Any sub-region `[a₁, a₁ + m₁)` of `[b₁, b₁ + n₁)` and `[a₂, a₂ + m₂)` of `[b₂, b₂ + n₂)`
    are disjoint whenever `[b₁, b₁ + n₁)` and `[b₂, b₂ + n₂)` are disjoint. -/
theorem _root_.Arm64.DisjointRegions.sub {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) (a₁ : BitVec 64 := b₁) (a₂ : BitVec 64 := b₂) {m₁ m₂ : Nat}
    (ha₁ : 0 < m₁ ∧ (a₁ - b₁).toNat + m₁ ≤ n₁ := by bv_omega_fast)
    (ha₂ : 0 < m₂ ∧ (a₂ - b₂).toNat + m₂ ≤ n₂ := by bv_omega_fast) :
    DisjointRegions a₁ m₁ a₂ m₂ := by
  rcases h with ⟨hd₁, hd₂⟩
  rcases ha₁ with ⟨hm₁, ho₁⟩
  rcases ha₂ with ⟨hm₂, ho₂⟩
  constructor <;> bv_omega

theorem _root_.Arm64.DisjointRegions.sub_left {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) (a₁ : BitVec 64 := b₁) {m₁ : Nat}
    (ha₁ : 0 < m₁ ∧ (a₁ - b₁).toNat + m₁ ≤ n₁ := by bv_omega_fast) :
    DisjointRegions a₁ m₁ b₂ n₂ := by
  rcases h with ⟨hd₁, hd₂⟩
  rcases ha₁ with ⟨hm₁, ho₁⟩
  constructor <;> bv_omega

theorem _root_.Arm64.DisjointRegions.sub_right {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (h : DisjointRegions b₁ n₁ b₂ n₂) (a₂ : BitVec 64 := b₂) {m₂ : Nat}
    (ha₂ : 0 < m₂ ∧ (a₂ - b₂).toNat + m₂ ≤ n₂ := by bv_omega_fast) :
    DisjointRegions b₁ n₁ a₂ m₂ := by
  rcases h with ⟨hd₁, hd₂⟩
  rcases ha₂ with ⟨hm₂, ho₂⟩
  constructor <;> bv_omega

export Memory (read8_write64_disjoint read8_write32_disjoint)

theorem sub_add_eq_sub (x c1 off c2 : BitVec 64)
    (h : decide (c2 = c1 - off) = true) :
    (x - c1) + off = x - c2 := by
  have h' := of_decide_eq_true h
  subst h'
  bv_omega

theorem sub_add_eq_sub_add (x c1 off c2 c3 : BitVec 64)
    (h : decide (c1 - off = c2 - c3) = true) :
    (x - c1) + off = (x - c2) + c3 := by
  have _ := of_decide_eq_true h
  bv_omega

theorem add_add_eq_add (x c1 off c2 : BitVec 64)
    (h : decide (c1 + off = c2) = true) :
    (x + c1) + off = x + c2 := by
  have h' := of_decide_eq_true h
  subst h'
  bv_omega

/-- When `[b1, b1 + n1)` and `[b2, b2 + n2)` are disjoint, a 64-bit store at `b1 + off1` inside
    the first region leaves `read64 (b2 + off2)` inside the second region unchanged. -/
theorem _root_.Arm64.DisjointRegions.read64_write64 {b1 b2 : BitVec 64} {n1 n2 : Nat}
    (h : DisjointRegions b1 n1 b2 n2)
    (m : Memory) (off1 off2 : BitVec 64) (v : BitVec 64)
    (hk : decide (off1.toNat + 8 ≤ n1 ∧ off2.toNat + 8 ≤ n2 ∧ n1 ≤ 2^64 ∧ n2 ≤ 2^64) = true) :
    (m.write64 (b1 + off1) v).read64 (b2 + off2) =
      m.read64 (b2 + off2) := by
  have ⟨hk1, hk2, hn1, hn2⟩ := of_decide_eq_true hk
  have ⟨hd1, hd2⟩ := h
  apply Memory.read64_write64_disjoint <;> bv_omega

/-- When `[b1, b1 + n1)` and `[b2, b2 + n2)` are disjoint, a 64-bit store at `a1 = b1 + off1` inside
    the first region leaves `read64 a2` (`a2 = b2 + off2`) inside the second region unchanged. -/
theorem _root_.Arm64.DisjointRegions.read64_write64_at {b1 b2 : BitVec 64} {n1 n2 : Nat}
    (h : DisjointRegions b1 n1 b2 n2)
    (m : Memory) (a1 a2 v : BitVec 64) (off1 off2 : BitVec 64)
    (ha1 : b1 + off1 = a1) (ha2 : b2 + off2 = a2)
    (hk : decide (off1.toNat + 8 ≤ n1 ∧ off2.toNat + 8 ≤ n2 ∧ n1 ≤ 2^64 ∧ n2 ≤ 2^64) = true) :
    (m.write64 a1 v).read64 a2 = m.read64 a2 := by
  subst ha1; subst ha2
  exact h.read64_write64 m off1 off2 v hk

/-- Extract `DisjointRegions a1 w1 a2 w2` for sub-accesses `a1 = b1 + off1` (width `w1`) inside
    `[b1, b1 + n1)` and `a2 = b2 + off2` (width `w2`) inside `[b2, b2 + n2)`. -/
theorem _root_.Arm64.DisjointRegions.sub_at {b1 b2 : BitVec 64} {n1 n2 : Nat}
    (h : DisjointRegions b1 n1 b2 n2)
    (w1 w2 : Nat) (a1 a2 off1 off2 : BitVec 64)
    (ha1 : b1 + off1 = a1) (ha2 : b2 + off2 = a2)
    (hk : decide (0 < w1 ∧ 0 < w2 ∧ off1.toNat + w1 ≤ n1 ∧ off2.toNat + w2 ≤ n2 ∧ n1 ≤ 2^64 ∧ n2 ≤ 2^64) = true) :
    DisjointRegions a1 w1 a2 w2 := by
  subst ha1; subst ha2
  have ⟨hw1, hw2, hk1, hk2, hn1, hn2⟩ := of_decide_eq_true hk
  have ⟨hd1, hd2⟩ := h
  constructor <;> bv_omega

/-- Symmetric variant of `DisjointRegions.sub_at` when `a1 = b2 + off2` lies in the second region
    and `a2 = b1 + off1` lies in the first region. -/
theorem _root_.Arm64.DisjointRegions.sub_at_symm {b1 b2 : BitVec 64} {n1 n2 : Nat}
    (h : DisjointRegions b1 n1 b2 n2)
    (w1 w2 : Nat) (a1 a2 off1 off2 : BitVec 64)
    (ha1 : b2 + off2 = a1) (ha2 : b1 + off1 = a2)
    (hk : decide (0 < w1 ∧ 0 < w2 ∧ off1.toNat + w2 ≤ n1 ∧ off2.toNat + w1 ≤ n2 ∧ n1 ≤ 2^64 ∧ n2 ≤ 2^64) = true) :
    DisjointRegions a1 w1 a2 w2 :=
  h.symm.sub_at w1 w2 a1 a2 off2 off1 ha1 ha2
    (by have ⟨h1, h2, h3, h4, h5, h6⟩ := of_decide_eq_true hk; exact decide_eq_true ⟨h1, h2, h4, h3, h6, h5⟩)

/-- A 1-byte store into a downward callee sub-frame `[base - sub_off, base)` at offset `slot_off < sub_off`
    leaves `read64 (base + off)` in the caller's frame unchanged. -/
@[simp, arm64_norm]
theorem read64_write8_sub_frame (m : Memory) (base sub_off slot_off off : BitVec 64) (v : BitVec 8)
    (h : decide (0 < sub_off.toNat ∧ slot_off.toNat < sub_off.toNat ∧ off.toNat + 8 + sub_off.toNat ≤ 2 ^ 64) = true) :
    (m.write8 ((base - sub_off) + slot_off) v).read64 (base + off) =
      m.read64 (base + off) := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true h
  have hne : ∀ (i : BitVec 64), i.toNat < 8 →
      base + off + i ≠ (base - sub_off) + slot_off := by
    intro i hi
    bv_omega
  have h_ite : ∀ {α : Type} {c : Prop} [Decidable c] (t e : α), ¬c → (if c then t else e) = e :=
    fun _ _ hc => ite_eq_right_iff.mpr (fun h => False.elim (hc h))
  simp only [Memory.read64, Memory.read8_write8]
  repeat' (rw [h_ite _ _ (hne _ (by decide))])

/-- Zero-offset variant of `read64_write8_sub_frame`. -/
@[simp, arm64_norm]
theorem read64_write8_sub_frame_zero (m : Memory) (base sub_off slot_off : BitVec 64) (v : BitVec 8)
    (h : decide (0 < sub_off.toNat ∧ slot_off.toNat < sub_off.toNat ∧ 8 + sub_off.toNat ≤ 2 ^ 64) = true) :
    (m.write8 ((base - sub_off) + slot_off) v).read64 base =
      m.read64 base := by
  have ⟨h1, h2, h3⟩ := of_decide_eq_true h
  have h := read64_write8_sub_frame m base sub_off slot_off 0#64 v (by simp [h1, h2, h3])
  simpa using h

theorem _root_.Arm64.Memory.readBytes_congr_region {m₁ m₂ : Memory} {p : BitVec 64} {n : Nat} (hn : n ≤ 2 ^ 64)
    (h : ∀ a, InRegion p n a → m₂.read8 a = m₁.read8 a) :
    m₂.readBytes p n = m₁.readBytes p n :=
  Memory.readBytes_congr p n fun i hi => h _ (inRegion_base_add p n i hi hn)

theorem _root_.Arm64.Memory.read64_congr {m₁ m₂ : Memory} {a : BitVec 64}
    (h : ∀ b, InRegion a 8 b → m₂.read8 b = m₁.read8 b) :
    m₂.read64 a = m₁.read64 a := by
  have hb : ∀ k : Nat, k < 8 →
      m₂.read8 (a + BitVec.ofNat 64 k) = m₁.read8 (a + BitVec.ofNat 64 k) :=
    fun k hk => h _ (inRegion_base_add a 8 k hk (by decide))
  have h0 := hb 0 (by decide)
  simp only [Memory.read64, hb 1 (by decide), hb 2 (by decide), hb 3 (by decide),
    hb 4 (by decide), hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), h0]

@[simp]
theorem not_inRegion_zero (base a : BitVec 64) : ¬ InRegion base 0 a := by
  simp [InRegion]

theorem _root_.Arm64.Memory.read8_write64_outside {m : Memory} {addr a : BitVec 64} {v : BitVec 64}
    (h : OutsideRegion addr 8 a) : (m.write64 addr v).read8 a = m.read8 a := by
  simp only [OutsideRegion] at h
  simp only [Memory.read8_write64]
  have h_ite : ∀ {α : Type} {c : Prop} [Decidable c] (t e : α), ¬c → (if c then t else e) = e :=
    fun _ _ hc => ite_eq_right_iff.mpr (fun h => False.elim (hc h))
  repeat' (rw [h_ite _ _ (by bv_omega)])

theorem _root_.Arm64.Memory.read8_write8_ne {m : Memory} {addr a : BitVec 64} {v : BitVec 8}
    (h : a ≠ addr) : (m.write8 addr v).read8 a = m.read8 a := by
  simp [Memory.read8_write8, h]

theorem _root_.Arm64.Memory.isLazyFree_write8_ne {m : Memory} {addr a : BitVec 64} {v : BitVec 8}
    (h : a ≠ addr) : (m.write8 addr v).isLazyFree a = m.isLazyFree a := by
  simp [Memory.isLazyFree_write8, h]

theorem _root_.Arm64.Memory.read8_writeBytes_outside (m : Memory) (base a : BitVec 64)
    (bs : List (BitVec 8)) (h : OutsideRegion base bs.length a) :
    (m.writeBytes base bs).read8 a = m.read8 a := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at h
    have hne : a ≠ base := by
      rintro rfl
      unfold OutsideRegion at h
      rw [BitVec.sub_self, BitVec.toNat_zero] at h
      omega
    have h_rest : OutsideRegion (base + 1#64) rest.length a := by
      unfold OutsideRegion at h ⊢
      have h_lt := (a - base).isLt
      have h_sub : (a - (base + 1#64)).toNat = (a - base).toNat - 1 := by bv_omega
      omega
    rw [Memory.writeBytes_cons, ih (m.write8 base b) (base + 1#64) h_rest]
    exact Memory.read8_write8_ne hne

theorem _root_.Arm64.Memory.isLazyFree_writeBytes_outside (m : Memory) (base a : BitVec 64)
    (bs : List (BitVec 8)) (h : OutsideRegion base bs.length a) :
    (m.writeBytes base bs).isLazyFree a = m.isLazyFree a := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at h
    have hne : a ≠ base := by
      rintro rfl
      unfold OutsideRegion at h
      rw [BitVec.sub_self, BitVec.toNat_zero] at h
      omega
    have h_rest : OutsideRegion (base + 1#64) rest.length a := by
      unfold OutsideRegion at h ⊢
      have h_lt := (a - base).isLt
      have h_sub : (a - (base + 1#64)).toNat = (a - base).toNat - 1 := by bv_omega
      omega
    rw [Memory.writeBytes_cons, ih (m.write8 base b) (base + 1#64) h_rest]
    exact Memory.isLazyFree_write8_ne hne

theorem _root_.Arm64.Memory.isAnon_writeBytes_apply (m : Memory) (base : BitVec 64)
    (bs : List (BitVec 8)) (a : BitVec 64) :
    (m.writeBytes base bs).isAnon a = m.isAnon a := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    rw [Memory.writeBytes_cons, ih (m.write8 base b) (base + 1#64), Memory.isAnon_write8_apply]

theorem _root_.Arm64.Memory.read8_writeBytes_inbounds (m : Memory) (base : BitVec 64)
    (bs : List (BitVec 8)) (i : Nat) (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    (m.writeBytes base bs).read8 (base + BitVec.ofNat 64 i) = bs[i] := by
  induction bs generalizing m base i with
  | nil => cases hi
  | cons b rest ih =>
    simp only [List.length_cons] at hi hlen
    cases i with
    | zero =>
      have h_out : OutsideRegion (base + 1#64) rest.length (base + BitVec.ofNat 64 0) := by
        unfold OutsideRegion
        have : base + BitVec.ofNat 64 0 - (base + 1#64) = BitVec.ofNat 64 (2 ^ 64 - 1) := by
          bv_omega
        rw [this, BitVec.toNat_ofNat]
        omega
      rw [Memory.writeBytes_cons, Memory.read8_writeBytes_outside _ _ _ _ h_out]
      have h0 : base + BitVec.ofNat 64 0 = base := by bv_arith
      rw [h0, Memory.read8_write8_same]
      rfl
    | succ j =>
      have h_addr : base + BitVec.ofNat 64 (j + 1) = (base + 1#64) + BitVec.ofNat 64 j := by
        bv_arith
      rw [Memory.writeBytes_cons, h_addr]
      exact ih (m.write8 base b) (base + 1#64) j (Nat.lt_of_succ_lt_succ hi) (by omega)

theorem _root_.Arm64.Memory.readBytes_writeBytes_same (m : Memory) (addr : BitVec 64)
    (bs : List (BitVec 8)) (hlen : bs.length ≤ 2 ^ 64) :
    (m.writeBytes addr bs).readBytes addr bs.length = bs := by
  induction bs generalizing m addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hlen
    simp only [List.length_cons, Memory.writeBytes_cons, Memory.readBytes_succ, List.cons.injEq]
    have h0 : (Memory.writeBytes (m.write8 addr b) (addr + 1#64) rest).read8 addr = b := by
      have hout : OutsideRegion (addr + 1#64) rest.length addr := by
        unfold OutsideRegion
        bv_omega
      rw [Memory.read8_writeBytes_outside _ _ _ _ hout, Memory.read8_write8_same]
    exact ⟨h0, ih (m.write8 addr b) (addr + 1#64) (by omega)⟩

abbrev _root_.Arm64.Memory.readBytes_writeBytes := @Memory.readBytes_writeBytes_same

theorem _root_.Arm64.Memory.readBytes_writeBytes_eq (m : Memory) (a : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat) (hn : bs.length = n := by rfl)
    (hlen : n ≤ 2 ^ 64 := by decide) :
    (m.writeBytes a bs).readBytes a n = bs := by
  subst hn; exact Memory.readBytes_writeBytes_same m a bs hlen

theorem _root_.Arm64.Memory.write8_writeBytes_comm (m : Memory) (a : BitVec 64) (v : BitVec 8)
    (base : BitVec 64) (bs : List (BitVec 8)) (h : OutsideRegion base bs.length a) :
    (m.writeBytes base bs).write8 a v = (m.write8 a v).writeBytes base bs := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    simp only [OutsideRegion, List.length_cons] at h
    have hne : base ≠ a := by
      rintro rfl
      rw [BitVec.sub_self, BitVec.toNat_zero] at h
      omega
    have h' : OutsideRegion (base + 1#64) rest.length a := by
      unfold OutsideRegion
      bv_omega
    simp only [Memory.writeBytes_cons]
    rw [ih (m.write8 base b) (base + 1#64) h', Memory.write8_write8_comm m base a b v hne]

theorem _root_.Arm64.Memory.writeBytes_writeBytes_overwrite (m : Memory) (addr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) (hwrap : bs1.length < 2 ^ 64) :
    (m.writeBytes addr bs1).writeBytes addr bs2 =
      m.writeBytes addr (bs2 ++ bs1.drop bs2.length) := by
  induction bs2 generalizing m addr bs1 with
  | nil => simp [Memory.writeBytes_nil]
  | cons b2 rest2 ih =>
    cases bs1 with
    | nil => simp [Memory.writeBytes_nil]
    | cons b1 rest1 =>
      simp only [List.length_cons] at hwrap
      simp only [Memory.writeBytes_cons, List.cons_append, List.length_cons, List.drop_succ_cons]
      have hout : OutsideRegion (addr + 1#64) rest1.length addr := by
        unfold OutsideRegion
        bv_omega
      rw [Memory.write8_writeBytes_comm (m.write8 addr b1) addr b2 (addr + 1#64) rest1 hout,
        Memory.write8_write8_same, ih (m.write8 addr b2) (addr + 1#64) rest1 (by omega)]

theorem _root_.Arm64.Memory.writeBytes_writeBytes_same (m : Memory) (addr : BitVec 64)
    (bs1 bs2 : List (BitVec 8)) (hlen : bs1.length ≤ bs2.length) (hwrap : bs1.length < 2 ^ 64) :
    (m.writeBytes addr bs1).writeBytes addr bs2 = m.writeBytes addr bs2 := by
  rw [Memory.writeBytes_writeBytes_overwrite m addr bs1 bs2 hwrap,
    List.drop_eq_nil_of_le hlen, List.append_nil]

/-! ## Frame conditions -/

namespace AgreesOutside

theorem perm_eq {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat}
    (h : AgreesOutside m₁ m₂ base len) : m₂.perm = m₁.perm := h.2.1

theorem isLazyFree_eq {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {a : BitVec 64}
    (h : AgreesOutside m₁ m₂ base len) (ha : OutsideRegion base len a) :
    m₂.isLazyFree a = m₁.isLazyFree a := h.2.2.1 a ha

theorem isLazyFree_false {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {a : BitVec 64}
    (h : AgreesOutside m₁ m₂ base len) (ha : m₁.isLazyFree a = false) :
    m₂.isLazyFree a = false := h.2.2.2.1 a ha

theorem isAnon_true {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {a : BitVec 64}
    (h : AgreesOutside m₁ m₂ base len) (ha : m₁.isAnon a = true) :
    m₂.isAnon a = true := h.2.2.2.2 a ha

/-- Not writing at all frames everything. -/
theorem rfl' (m : Memory) (base : BitVec 64) (len : Nat) : AgreesOutside m m base len :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ h => h, fun _ h => h⟩

abbrev refl := @rfl'

/-- Frame conditions compose along a sequence of stores. -/
theorem trans {m₁ m₂ m₃ : Memory} {base : BitVec 64} {len : Nat}
    (h₁ : AgreesOutside m₁ m₂ base len) (h₂ : AgreesOutside m₂ m₃ base len) :
    AgreesOutside m₁ m₃ base len :=
  ⟨fun a ha => (h₂.1 a ha).trans (h₁.1 a ha),
   h₂.2.1.trans h₁.2.1,
   fun a ha => (h₂.2.2.1 a ha).trans (h₁.2.2.1 a ha),
   fun a ha => h₂.2.2.2.1 a (h₁.2.2.2.1 a ha),
   fun a ha => h₂.2.2.2.2 a (h₁.2.2.2.2 a ha)⟩

/-- Widening the framed region weakens the frame condition. -/
theorem mono {m₁ m₂ : Memory} {base : BitVec 64} {len len' : Nat}
    (h : AgreesOutside m₁ m₂ base len) (hlen : len ≤ len') : AgreesOutside m₁ m₂ base len' :=
  ⟨fun a ha => h.1 a (Nat.le_trans hlen ha),
   h.2.1,
   fun a ha => h.2.2.1 a (Nat.le_trans hlen ha),
   h.2.2.2.1,
   h.2.2.2.2⟩

/-- A one-byte store inside the region preserves the frame condition. -/
theorem write8 {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {b : BitVec 64} {v : BitVec 8}
    (h : AgreesOutside m₁ m₂ base len) (hb : InRegion base len b) :
    AgreesOutside m₁ (m₂.write8 b v) base len := by
  have hne_of_out : ∀ a, OutsideRegion base len a → a ≠ b := by
    intro a ha hEq
    subst hEq
    simp only [OutsideRegion] at ha
    simp only [InRegion] at hb
    omega
  refine ⟨fun a ha => ?_, (Memory.perm_write8 _ _ _).trans h.2.1, fun a ha => ?_,
    fun a ha => Memory.isLazyFree_write8_of_false b v (h.2.2.2.1 a ha),
    fun a ha => by rw [Memory.isAnon_write8_apply]; exact h.2.2.2.2 a ha⟩
  · rw [Memory.read8_write8_ne (hne_of_out a ha)]
    exact h.1 a ha
  · rw [Memory.isLazyFree_write8_ne (hne_of_out a ha)]
    exact h.2.2.1 a ha

private theorem inRegion_of_sub_add {base b k : BitVec 64} {len n : Nat}
    (hb : (b - base).toNat + n ≤ len) (_hlen : len ≤ 2 ^ 64) (hk : k.toNat < n) :
    InRegion base len (b + k) := by
  simp only [InRegion]
  bv_omega

/-- A two-byte store wholly inside the region preserves the frame condition. -/
theorem write16 {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {b : BitVec 64} {v : BitVec 16}
    (h : AgreesOutside m₁ m₂ base len) (hb : (b - base).toNat + 2 ≤ len) (hlen : len ≤ 2 ^ 64) :
    AgreesOutside m₁ (m₂.write16 b v) base len := by
  have step (k : BitVec 64) (hk : k.toNat < 2) := inRegion_of_sub_add hb hlen hk
  simp only [Memory.write16]
  exact (h.write8 (step 0#64 (by decide))).write8 (step 1#64 (by decide))

/-- A four-byte store wholly inside the region preserves the frame condition. -/
theorem write32 {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {b : BitVec 64} {v : BitVec 32}
    (h : AgreesOutside m₁ m₂ base len) (hb : (b - base).toNat + 4 ≤ len) (hlen : len ≤ 2 ^ 64) :
    AgreesOutside m₁ (m₂.write32 b v) base len := by
  have step (k : BitVec 64) (hk : k.toNat < 4) := inRegion_of_sub_add hb hlen hk
  simp only [Memory.write32]
  exact (((h.write8 (step 0#64 (by decide))).write8 (step 1#64 (by decide))).write8
    (step 2#64 (by decide))).write8 (step 3#64 (by decide))

/-- An eight-byte store wholly inside the region preserves the frame condition. -/
theorem write64 {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {b : BitVec 64} {v : BitVec 64}
    (h : AgreesOutside m₁ m₂ base len) (hb : (b - base).toNat + 8 ≤ len) (hlen : len ≤ 2 ^ 64) :
    AgreesOutside m₁ (m₂.write64 b v) base len := by
  have step (k : BitVec 64) (hk : k.toNat < 8) := inRegion_of_sub_add hb hlen hk
  simp only [Memory.write64]
  exact (((((((h.write8 (step 0#64 (by decide))).write8 (step 1#64 (by decide))).write8
    (step 2#64 (by decide))).write8 (step 3#64 (by decide))).write8
    (step 4#64 (by decide))).write8 (step 5#64 (by decide))).write8
    (step 6#64 (by decide))).write8 (step 7#64 (by decide))

private theorem sub_self_le {base : BitVec 64} {n w : Nat} (hk : w ≤ n) :
    (base - base).toNat + w ≤ n := by
  simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
  exact hk

/-- Fast 64-bit stack-frame step at offset `0` inside an `n`-byte region. -/
theorem write64_zero {m₁ m₂ : Memory} {base : BitVec 64} {n : Nat} {v : BitVec 64}
    (h : AgreesOutside m₁ m₂ base n)
    (hk : decide (8 ≤ n ∧ n ≤ 2 ^ 64) = true) :
    AgreesOutside m₁ (m₂.write64 base v) base n := by
  have ⟨hk1, hn⟩ := of_decide_eq_true hk
  exact h.write64 (sub_self_le hk1) hn

/-- A sixteen-byte (`STR q` / `STUR q`) store wholly inside the region preserves the frame
    condition, including unaligned 16-byte copies. -/
theorem write128 {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {b : BitVec 64} {v : BitVec 128}
    (h : AgreesOutside m₁ m₂ base len) (hb : (b - base).toNat + 16 ≤ len) (hlen : len ≤ 2 ^ 64) :
    AgreesOutside m₁ (m₂.write128 b v) base len := by
  have hlo : (b - base).toNat + 8 ≤ len := by omega
  have hhi : ((b + 8#64) - base).toNat + 8 ≤ len := by bv_omega
  simp only [Memory.write128]
  exact (h.write64 hlo hlen).write64 hhi hlen

private theorem outside_of_disjoint {base a k : BitVec 64} {len n : Nat}
    (hd : DisjointRegions base len a n) (hk : k.toNat < n) (hn : n ≤ 2 ^ 64) :
    OutsideRegion base len (a + k) := by
  refine hd.outside ?_ hn
  simp only [InRegion]
  bv_omega

/-- A single byte read from outside the framed region sees the original byte. -/
theorem read8_eq {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {a : BitVec 64}
    (h : AgreesOutside m₁ m₂ base len) (ha : OutsideRegion base len a) :
    m₂.read8 a = m₁.read8 a := h.1 a ha

/-- A 32-bit read from a region disjoint from the framed one sees the original bytes. -/
theorem read32_eq {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {a : BitVec 64}
    (h : AgreesOutside m₁ m₂ base len) (hd : DisjointRegions base len a 4) :
    m₂.read32 a = m₁.read32 a := by
  have hout (k : BitVec 64) (hk : k.toNat < 4) := outside_of_disjoint hd hk (by decide)
  simp only [Memory.read32]
  rw [h.1 _ (hout 0#64 (by decide)), h.1 _ (hout 1#64 (by decide)),
    h.1 _ (hout 2#64 (by decide)), h.1 _ (hout 3#64 (by decide))]

/-- A 64-bit read from a region disjoint from the framed one sees the original bytes. -/
theorem read64_eq {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {a : BitVec 64}
    (h : AgreesOutside m₁ m₂ base len) (hd : DisjointRegions base len a 8) :
    m₂.read64 a = m₁.read64 a := by
  have hout (k : BitVec 64) (hk : k.toNat < 8) := outside_of_disjoint hd hk (by decide)
  simp only [Memory.read64]
  rw [h.1 _ (hout 0#64 (by decide)), h.1 _ (hout 1#64 (by decide)), h.1 _ (hout 2#64 (by decide)),
    h.1 _ (hout 3#64 (by decide)), h.1 _ (hout 4#64 (by decide)), h.1 _ (hout 5#64 (by decide)),
    h.1 _ (hout 6#64 (by decide)), h.1 _ (hout 7#64 (by decide))]

/-- A 128-bit (`LDR q`) read from a region disjoint from the framed one sees the original
    bytes. -/
theorem read128_eq {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {a : BitVec 64}
    (h : AgreesOutside m₁ m₂ base len) (hd : DisjointRegions base len a 16) :
    m₂.read128 a = m₁.read128 a := by
  have hd0 : DisjointRegions base len a 8 := ⟨hd.1, Nat.le_trans (by decide) hd.2⟩
  have hd8 : DisjointRegions base len (a + 8#64) 8 :=
    ⟨by have := hd.1; have := hd.2; bv_omega, by have := hd.2; bv_omega⟩
  simp only [Memory.read128, h.read64_eq hd0, h.read64_eq hd8]

/-- A contiguous `n`-byte read from a region disjoint from the framed one sees the original bytes. -/
theorem readBytes_eq {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat} {a : BitVec 64} {n : Nat}
    (h : AgreesOutside m₁ m₂ base len) (hd : DisjointRegions base len a n) (hn : n ≤ 2 ^ 64) :
    m₂.readBytes a n = m₁.readBytes a n :=
  Memory.readBytes_congr a n fun i hi => h.1 _ (hd.outside (inRegion_base_add a n i hi hn) hn)

/-- `writeBytes` at `a` preserves `AgreesOutside m · a bs.length`. -/
theorem writeBytes_self (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    AgreesOutside m (m.writeBytes a bs) a bs.length :=
  ⟨fun x hx => Memory.read8_writeBytes_outside m a x bs hx,
   Memory.perm_writeBytes m a bs,
   fun x hx => Memory.isLazyFree_writeBytes_outside m a x bs hx,
   fun _ hx => Memory.isLazyFree_writeBytes_of_false a bs hx,
   fun x hx => by rw [Memory.isAnon_writeBytes_apply]; exact hx⟩

/-- A byte-slice store wholly inside the region preserves the frame condition. -/
theorem writeBytes {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat}
    {a : BitVec 64} (bs : List (BitVec 8))
    (h : AgreesOutside m₁ m₂ base len)
    (ha : (a - base).toNat + bs.length ≤ len) :
    AgreesOutside m₁ (m₂.writeBytes a bs) base len := by
  have hout_sub : ∀ x, OutsideRegion base len x → OutsideRegion a bs.length x := by
    intro x hx
    simp only [OutsideRegion] at hx ⊢
    bv_omega
  refine ⟨fun x hx => ?_, (Memory.perm_writeBytes m₂ a bs).trans h.2.1, fun x hx => ?_,
    fun x hx => Memory.isLazyFree_writeBytes_of_false a bs (h.2.2.2.1 x hx),
    fun x hx => by rw [Memory.isAnon_writeBytes_apply]; exact h.2.2.2.2 x hx⟩
  · rw [Memory.read8_writeBytes_outside m₂ a x bs (hout_sub x hx), h.read8_eq hx]
  · rw [Memory.isLazyFree_writeBytes_outside m₂ a x bs (hout_sub x hx), h.isLazyFree_eq hx]

/-- `AgreesOutside` on a region disjoint from `(prog.base, prog.code.length)` preserves `CodeLoaded`. -/
theorem codeLoaded {prog : Program} {m₁ m₂ : Memory} {base : BitVec 64} {len : Nat}
    (h : AgreesOutside m₁ m₂ base len)
    (hd : DisjointRegions base len prog.base prog.code.length)
    (hL : prog.CodeLoaded m₁) : prog.CodeLoaded m₂ := by
  rw [Program.codeLoaded_iff] at hL ⊢
  refine ⟨hL.1, hL.2.1, fun i hi => ?_⟩
  have hlen : prog.code.length ≤ 2 ^ 64 := by omega
  have hin : InRegion prog.base prog.code.length (prog.base + BitVec.ofNat 64 i) :=
    inRegion_base_add prog.base prog.code.length i hi hlen
  have hout : OutsideRegion base len (prog.base + BitVec.ofNat 64 i) :=
    hd.outside hin hlen
  have hp : m₂.perm (prog.base + BitVec.ofNat 64 i) = m₁.perm (prog.base + BitVec.ofNat 64 i) :=
    congrFun h.2.1 _
  rw [h.read8_eq hout, hp, h.isLazyFree_eq hout]
  exact hL.2.2 i hi

end AgreesOutside

theorem agreesOutside_writeBytes (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8)) :
    AgreesOutside m (m.writeBytes addr bs) addr bs.length :=
  AgreesOutside.writeBytes_self m addr bs

theorem _root_.Arm64.Program.CodeLoaded.writeBytes_of_disjoint {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded m) {a : BitVec 64} (bs : List (BitVec 8))
    (hd : DisjointRegions a bs.length prog.base prog.code.length) :
    prog.CodeLoaded (m.writeBytes a bs) :=
  (AgreesOutside.writeBytes_self m a bs).codeLoaded hd hL

theorem _root_.Arm64.Memory.readBytes_writeBytes_of_disjoint (m : Memory) (a : BitVec 64)
    (bs : List (BitVec 8)) (b : BitVec 64) (n : Nat)
    (hd : DisjointRegions a bs.length b n) (hn : n ≤ 2 ^ 64) :
    (m.writeBytes a bs).readBytes b n = m.readBytes b n :=
  (agreesOutside_writeBytes m a bs).readBytes_eq hd hn

theorem _root_.Arm64.Memory.readBytes_writeBytes_disjoint (m : Memory) (a1 : BitVec 64) (n1 : Nat)
    (a2 : BitVec 64) (bs : List (BitVec 8))
    (hd : DisjointRegions a1 n1 a2 bs.length) :
    (m.writeBytes a2 bs).readBytes a1 n1 = m.readBytes a1 n1 :=
  (agreesOutside_writeBytes m a2 bs).readBytes_eq hd.symm (by have := hd.1; bv_omega)

theorem _root_.Arm64.Memory.readBytes_writeBytes_disjoint' (m : Memory) (a1 : BitVec 64) (n1 : Nat)
    (a2 : BitVec 64) (bs : List (BitVec 8))
    (hd : DisjointRegions a2 bs.length a1 n1) :
    (m.writeBytes a2 bs).readBytes a1 n1 = m.readBytes a1 n1 :=
  Memory.readBytes_writeBytes_disjoint m a1 n1 a2 bs hd.symm

theorem _root_.Arm64.Memory.read64_writeBytes_disjoint (m : Memory) (a1 a2 : BitVec 64)
    (bs : List (BitVec 8)) (hd : DisjointRegions a1 8 a2 bs.length) :
    (m.writeBytes a2 bs).read64 a1 = m.read64 a1 :=
  (agreesOutside_writeBytes m a2 bs).read64_eq hd.symm

theorem _root_.Arm64.Memory.read128_writeBytes_disjoint (m : Memory) (a1 a2 : BitVec 64)
    (bs : List (BitVec 8)) (hd : DisjointRegions a1 16 a2 bs.length) :
    (m.writeBytes a2 bs).read128 a1 = m.read128 a1 :=
  (agreesOutside_writeBytes m a2 bs).read128_eq hd.symm

abbrev read8_writeBytes_outside := @Memory.read8_writeBytes_outside
abbrev read8_writeBytes_inbounds := @Memory.read8_writeBytes_inbounds
abbrev readBytes_writeBytes_same := @Memory.readBytes_writeBytes_same
abbrev readBytes_writeBytes := @Memory.readBytes_writeBytes
abbrev readBytes_writeBytes_eq := @Memory.readBytes_writeBytes_eq
abbrev readBytes_writeBytes_of_disjoint := @Memory.readBytes_writeBytes_of_disjoint
abbrev readBytes_writeBytes_disjoint := @Memory.readBytes_writeBytes_disjoint
abbrev readBytes_writeBytes_disjoint' := @Memory.readBytes_writeBytes_disjoint'
abbrev read64_writeBytes_disjoint := @Memory.read64_writeBytes_disjoint
abbrev read128_writeBytes_disjoint := @Memory.read128_writeBytes_disjoint
abbrev write8_writeBytes_comm := @Memory.write8_writeBytes_comm
abbrev writeBytes_writeBytes_overwrite := @Memory.writeBytes_writeBytes_overwrite
abbrev writeBytes_writeBytes_same := @Memory.writeBytes_writeBytes_same

/-- Discharge an `AgreesOutside m₁ m₂ base len` goal over a chain of `write8`/`write16`/`write32`/`write64`/`write128`
    stores into `[base, base + len)` by peeling off each store using `with_reducible` (preventing
    expensive unfolding of `Memory.write64` into `Memory.write8`) and discharging the offset bounds via `bv_omega_fast`. -/
macro "agrees_outside_writes" : tactic =>
  `(tactic| (
    repeat' (first
      | (with_reducible apply AgreesOutside.rfl')
      | ((with_reducible refine AgreesOutside.write64 ?_ ?_ ?_); rotate_left; (· bv_omega_fast); (· first | decide | bv_omega_fast))
      | ((with_reducible refine AgreesOutside.write128 ?_ ?_ ?_); rotate_left; (· bv_omega_fast); (· first | decide | bv_omega_fast))
      | ((with_reducible refine AgreesOutside.write32 ?_ ?_ ?_); rotate_left; (· bv_omega_fast); (· first | decide | bv_omega_fast))
      | ((with_reducible refine AgreesOutside.write16 ?_ ?_ ?_); rotate_left; (· bv_omega_fast); (· first | decide | bv_omega_fast))
      | ((with_reducible refine AgreesOutside.write8 ?_ ?_); rotate_left; (· simp only [InRegion]; bv_omega_fast)))))

/-! ## Byte-for-byte buffer equality -/

namespace BytesAgree

private theorem concat2_bytes_inj {b1 b0 c1 c0 : BitVec 8}
    (h : b1 ++ b0 = c1 ++ c0) : b0 = c0 ∧ b1 = c1 := by
  bv_bits

private theorem concat4_bytes_inj {b3 b2 b1 b0 c3 c2 c1 c0 : BitVec 8}
    (h : b3 ++ b2 ++ b1 ++ b0 = c3 ++ c2 ++ c1 ++ c0) :
    b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3 := by
  bv_bits

private theorem concat8_bytes_inj {b7 b6 b5 b4 b3 b2 b1 b0 c7 c6 c5 c4 c3 c2 c1 c0 : BitVec 8}
    (h : b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 =
         c7 ++ c6 ++ c5 ++ c4 ++ c3 ++ c2 ++ c1 ++ c0) :
    b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3 ∧ b4 = c4 ∧ b5 = c5 ∧ b6 = c6 ∧ b7 = c7 := by
  bv_bits

private theorem concat2_u64_inj {b1 b0 c1 c0 : BitVec 64}
    (h : b1 ++ b0 = c1 ++ c0) : b0 = c0 ∧ b1 = c1 := by
  bv_bits

private theorem add_ofNat_add8 (a : BitVec 64) (k : Nat) :
    a + BitVec.ofNat 64 (8 + k) = a + 8#64 + BitVec.ofNat 64 k := by
  bv_omega

/-- Byte-for-byte equality of two 8-byte buffers follows from equality of the 64-bit values at
    the two addresses (`Memory.read64` is by definition the concatenation of the eight bytes). -/
theorem of_read64_eq (m₁ m₂ : Memory) (a₁ a₂ : BitVec 64)
    (h : m₁.read64 a₁ = m₂.read64 a₂) : BytesAgree m₁ a₁ m₂ a₂ 8 := by
  rcases concat8_bytes_inj h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  intro i hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

end BytesAgree

end

end ProofLib
