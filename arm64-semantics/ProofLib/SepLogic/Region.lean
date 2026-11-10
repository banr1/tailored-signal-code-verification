/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Exists
public import ProofLib.SepLogic.Solver
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model
public import ProofLib.CoreLemmas

/-!
# Region Algebra and Ghost-Changing Consequence

Splitting, merging, and multi-offset partitioning (`memRegion_partition`) for contiguous byte
regions (`memRegion`), read-only subregions (`memRO_subregion`), downward-growing stack frames
(`stackFrameAt`), and 64-bit word arrays (`pointsToWords64`). Also provides `subroutine_ok_of_ghost`
and `reaches_of_ghost` for lifting low-level subroutine specifications across ghost-state and frame
refinements, plus non-wrapping and interior non-null lemmas for `Allocator`.
-/

namespace ProofLib

open Arm64

@[expose] public section

/-- Reading a single byte inside `memRegion b N` (`k < N ≤ 2^64`) is permitted. -/
theorem memRegion_canRead1 {m : Memory} {b : BitVec 64} {N k : Nat} {R : SepProp}
    (h : m ⊨ memRegion b N ∗ R) (hk : k < N) (hN : N ≤ 2 ^ 64) :
    m.canRead (b + BitVec.ofNat 64 k) 1 = true := by
  rw [memRegion_split3 b N k 1 (by omega) hN, sepConj_assoc] at h
  exact (IsBlock.memRegion _ 1).canRead (by decide) h

/-- Writing a single byte inside `memRegion b N` (`k < N ≤ 2^64`) is permitted. -/
theorem memRegion_canWrite1 {m : Memory} {b : BitVec 64} {N k : Nat} {R : SepProp}
    (h : m ⊨ memRegion b N ∗ R) (hk : k < N) (hN : N ≤ 2 ^ 64) :
    m.canWrite (b + BitVec.ofNat 64 k) 1 = true := by
  rw [memRegion_split3 b N k 1 (by omega) hN, sepConj_assoc] at h
  exact (IsBlock.memRegion _ 1).canWrite (by decide) h

/-- Writing a byte inside `memRegion b N` (`k < N ≤ 2^64`) preserves `memRegion b N ∗ R`. -/
theorem memRegion_write8 {m : Memory} {b : BitVec 64} {N k : Nat} {v : BitVec 8} {R : SepProp}
    (h : m ⊨ memRegion b N ∗ R) (hk : k < N) (hN : N ≤ 2 ^ 64) :
    m.write8 (b + BitVec.ofNat 64 k) v ⊨ memRegion b N ∗ R := by
  rw [memRegion_split3 b N k 1 (by omega) hN, sepConj_assoc] at h ⊢
  exact (IsBlock.memRegion _ 1).update (IsBlock.memRegion _ 1) (Nat.le_refl _) h
    ((AgreesOutside.rfl' m (b + BitVec.ofNat 64 k) 1).write8 (by simp [InRegion])) trivial

/-- `Satisfies` is affine: any separated conjunct can be dropped. -/
theorem Satisfies.drop_left {m : Memory} {P Q : SepProp} (h : m ⊨ P ∗ Q) : m ⊨ Q :=
  Satisfies.of_sep_right h

/-- A leading 64-bit cell and the rest of a region form the region. -/
theorem memRegion_cons (a v : BitVec 64) {n : Nat} (hn : 8 ≤ n) (hlen : n ≤ 2 ^ 64) :
    ((a ↦₆₄ v) ∗ memRegion (a + 8#64) (n - 8)) ⊢ memRegion a n := by
  rw [memRegion_split' (n := 8) (k := n - 8) (by omega) rfl hlen]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a v)

/-- A region of at least 8 bytes is a leading 64-bit cell (with some value) and the rest. -/
theorem memRegion_uncons (a : BitVec 64) {n : Nat} (hn : 8 ≤ n) (hlen : n ≤ 2 ^ 64) :
    memRegion a n = ∃∗ v : BitVec 64, (a ↦₆₄ v) ∗ memRegion (a + 8#64) (n - 8) := by
  rw [memRegion_split' (n := 8) (k := n - 8) (by omega) rfl hlen, memRegion_eight,
    sepExists_sepConj_left]

/-- Split a prefix `memRegion p m` (`m ≤ n ≤ 2^64`) off `memRegion p n`. -/
theorem memRegion_split_le (p : BitVec 64) (m n : Nat) (hmn : m ≤ n) (hn : n ≤ 2 ^ 64) :
    memRegion p n = memRegion p m ∗ memRegion (p + BitVec.ofNat 64 m) (n - m) :=
  memRegion_split' (by omega) rfl hn

/-- Split `memRegion (sp - BitVec.ofNat 64 n) n` (`m + k = n ≤ 2 ^ 64`) into the bottom `m` bytes
    at `sp - BitVec.ofNat 64 n` and the top `k` bytes at `sp - BitVec.ofNat 64 k`. -/
theorem memRegion_split_sub (sp : BitVec 64) (n m k : Nat)
    (hmk : m + k = n := by decide) (hn : n ≤ 2 ^ 64 := by decide) :
    memRegion (sp - BitVec.ofNat 64 n) n =
      memRegion (sp - BitVec.ofNat 64 n) m ∗ memRegion (sp - BitVec.ofNat 64 k) k := by
  rw [memRegion_split' (n := m) (k := k) (by omega)
    (b' := sp - BitVec.ofNat 64 k)
    (by rw [show BitVec.ofNat 64 n = BitVec.ofNat 64 k + BitVec.ofNat 64 m by
          rw [← BitVec.ofNat_add]; congr 1; omega, ← BitVec.sub_sub, BitVec.sub_add_cancel]) hn]

/-- Split a region of size `a + l + o` into three adjacent regions. -/
theorem memRegion_split_three (c : BitVec 64) (a l o : Nat) (h : a + l + o ≤ 2 ^ 64) :
    memRegion c (a + l + o) =
      memRegion c a ∗ memRegion (c + BitVec.ofNat 64 a) l ∗
        memRegion (c + BitVec.ofNat 64 a + BitVec.ofNat 64 l) o := by
  rw [memRegion_split c (a + l) o h, memRegion_split c a l (by omega), sepConj_assoc,
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Rejoin three slices `[b, b + k)`, `[b + k, b + k + m)`, and `[b + k + m, b + N)` into
    `memRegion b N` (inverse of `memRegion_split3`). -/
theorem memRegion_merge3 (b : BitVec 64) (N k m : Nat) (hk : k + m ≤ N) (hN : N ≤ 2 ^ 64) :
    memRegion (b + BitVec.ofNat 64 k) m ∗
      (memRegion b k ∗ memRegion (b + BitVec.ofNat 64 (k + m)) (N - k - m)) =
      memRegion b N :=
  (memRegion_split3 b N k m hk hN).symm

/-- Split `memRegion a N` in address order into `[a, a + m)`, `[a + m, a + m + n)`, and
    `[a + m + n, a + N)` (`m + n ≤ N ≤ 2 ^ 64`). -/
theorem memRegion_split3_ord (a : BitVec 64) (N m n : Nat) (h : m + n ≤ N) (hN : N ≤ 2 ^ 64) :
    memRegion a N =
      memRegion a m ∗ memRegion (a + BitVec.ofNat 64 m) n ∗
        memRegion (a + BitVec.ofNat 64 (m + n)) (N - (m + n)) := by
  rw [memRegion_split' (n := m) (k := N - m) (by omega) rfl hN,
    memRegion_split' (b := a + BitVec.ofNat 64 m) (n := n) (k := N - m - n) (by omega) rfl (by omega)]
  congr 3
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · omega

/-- Fold a leading byte cell `a ↦₈ v` and a trailing `memRegion (a + 1#64) n` back into
    `memRegion a (n + 1)`. -/
theorem memRegion_byte_merge (a : BitVec 64) (v : BitVec 8) (n : Nat) (hn : n + 1 ≤ 2 ^ 64) :
    ((a ↦₈ v) ∗ memRegion (a + 1#64) n) ⊢ memRegion a (n + 1) := by
  rw [show n + 1 = 1 + n by omega, memRegion_split a 1 n (by omega)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion a v)

/-- Split the leading byte at `p + k` from `memRegion (p + k) (n + 1)`. -/
theorem memRegion_succ_off (p : BitVec 64) (k n : Nat) (hn : 1 + n ≤ 2 ^ 64) :
    memRegion (p + BitVec.ofNat 64 k) (n + 1) =
      ((∃∗ v : BitVec 8, (p + BitVec.ofNat 64 k) ↦₈ v) ∗
       memRegion (p + BitVec.ofNat 64 (k + 1)) n) := by
  have h1 : n + 1 = 1 + n := Nat.add_comm n 1
  have h2 : (p + BitVec.ofNat 64 k) + 1#64 = p + BitVec.ofNat 64 (k + 1) := by
    rw [BitVec.add_assoc]; congr 1
    change BitVec.ofNat 64 k + BitVec.ofNat 64 1 = BitVec.ofNat 64 (k + 1)
    rw [← BitVec.ofNat_add]
  rw [h1, memRegion_split (p + BitVec.ofNat 64 k) 1 n hn, memRegion_one, h2]

/-! ## Multi-offset region partitioning -/

/-- Auto-parameter helper that evaluates ground `Nat` expressions on the RHS of `?lhs = rhs` to a
    canonical `OfNat.ofNat` numeral literal before closing the equality by `rfl`. -/
elab "reduce_nat_eq" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goalTy ← Lean.instantiateMVars (← goal.getType)
  if let some (_, lhs, rhs) := goalTy.eq? then
    let rhsWhnf ← Lean.Meta.whnf rhs
    if let some n := rhsWhnf.rawNatLit? then
      let _ ← Lean.Meta.isDefEq lhs (Lean.mkNatLit n)
  Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

/-- Check that `offs` is a monotonically non-decreasing list of byte offsets in `[curOff, endOff]`. -/
def MemRegionPartitionValid (curOff endOff : Nat) : List Nat → Bool
  | [] => decide (curOff ≤ endOff)
  | off :: offs =>
    decide (curOff ≤ off) && decide (off ≤ endOff) && MemRegionPartitionValid off endOff offs

/-- Partition `memRegion (b + BitVec.ofNat 64 curOff) (endOff - curOff)` at ascending byte offsets
    `offs` (each relative to `b`). -/
def memRegionPartitionAt (b : BitVec 64) (curOff endOff : Nat) : List Nat → SepProp
  | [] => memRegion (b + BitVec.ofNat 64 curOff) (endOff - curOff)
  | off :: offs =>
    memRegion (b + BitVec.ofNat 64 curOff) (off - curOff) ∗
      memRegionPartitionAt b off endOff offs

/-- Partition `memRegion b total` at ascending byte offsets `offs` (each relative to `b`). -/
def memRegionPartition (b : BitVec 64) (total : Nat) : List Nat → SepProp
  | [] => memRegion b total
  | off :: offs =>
    memRegion b off ∗ memRegionPartitionAt b off total offs

/-- Core equality for `memRegionPartitionAt` before numeral normalization. -/
theorem memRegion_partition_at_eq (b : BitVec 64) :
    ∀ (offs : List Nat) (curOff endOff : Nat),
      MemRegionPartitionValid curOff endOff offs = true →
      endOff - curOff ≤ 2 ^ 64 →
      memRegion (b + BitVec.ofNat 64 curOff) (endOff - curOff) =
        memRegionPartitionAt b curOff endOff offs
  | [], curOff, endOff, _, _ => rfl
  | off :: offs, curOff, endOff, hvalid, hbound => by
    simp only [MemRegionPartitionValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
    rcases hvalid with ⟨⟨hle1, hle2⟩, hrest⟩
    simp only [memRegionPartitionAt]
    rw [memRegion_split' (n := off - curOff) (k := endOff - off) (by omega)
      (b' := b + BitVec.ofNat 64 off)
      (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega) hbound]
    rw [memRegion_partition_at_eq b offs off endOff hrest (by omega)]

/-- Core equality for `memRegionPartition` before numeral normalization. -/
theorem memRegion_partition_eq (b : BitVec 64) (total : Nat) (offs : List Nat)
    (hvalid : MemRegionPartitionValid 0 total offs = true)
    (hbound : total ≤ 2 ^ 64) :
    memRegion b total = memRegionPartition b total offs := by
  cases offs with
  | nil => rfl
  | cons off offs =>
    simp only [MemRegionPartitionValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
    rcases hvalid with ⟨⟨_, hle2⟩, hrest⟩
    simp only [memRegionPartition]
    rw [memRegion_split' (n := off) (k := total - off) (by omega) rfl hbound]
    rw [memRegion_partition_at_eq b offs off total hrest (by omega)]

end

public meta section

private partial def normMemRegionPartitionExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  Lean.Meta.transform e (pre := fun sub => do
    if sub.isAppOfArity ``memRegionPartition 3 || sub.isAppOfArity ``memRegionPartitionAt 4 then
      let offsWhnf ← Lean.Meta.whnf sub.appArg!
      if offsWhnf.isAppOf ``List.nil || offsWhnf.isAppOf ``List.cons then
        if let some unfolded ← Lean.Meta.unfoldDefinition? sub then
          return .visit (← Lean.Meta.whnfCore unfolded)
    if sub.isAppOfArity ``memRegion 2 then
      let addr := sub.appFn!.appArg!
      let len := sub.appArg!
      let lenWhnf ← Lean.Meta.whnf len
      if let some n := lenWhnf.rawNatLit? then
        return .done (Lean.mkApp2 sub.appFn!.appFn! addr (Lean.mkNatLit n))
    return .continue)

/-- Auto-parameter helper that unfolds `memRegionPartition` / `memRegionPartitionAt` on the RHS of
    `?out = rhs` and reduces each slice length `off_{i+1} - off_i` to a canonical `Nat` numeral. -/
elab "reduce_partition_eq" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goalTy ← Lean.instantiateMVars (← goal.getType)
  if let some (_, lhs, rhs) := goalTy.eq? then
    let normRhs ← normMemRegionPartitionExpr rhs
    let _ ← Lean.Meta.isDefEq lhs normRhs
  Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

end

@[expose] public section

/-- Partition `memRegion b total` across an ascending list of byte offsets `offs = [off₁, ..., offₖ]`
    in a single rewrite, computing all slice sizes `off_{i+1} - off_i` and the tail size
    `total - offₖ` as reduced numeral literals and discharging bounds automatically:
    ```
    rw [memRegion_partition base 24 [8, 10, 12, 16]]
    -- rewrites `memRegion base 24` to:
    --   memRegion base 8 ∗ (memRegion (base + 8#64) 2 ∗ (memRegion (base + 10#64) 2 ∗
    --     (memRegion (base + 12#64) 4 ∗ memRegion (base + 16#64) 8)))
    ``` -/
theorem memRegion_partition (b : BitVec 64) (total : Nat) (offs : List Nat)
    {out : SepProp}
    (hvalid : MemRegionPartitionValid 0 total offs = true := by
      first | decide | (simp [MemRegionPartitionValid]; omega))
    (hbound : total ≤ 2 ^ 64 := by first | decide | omega)
    (hout : out = memRegionPartition b total offs := by reduce_partition_eq) :
    memRegion b total = out := by
  rw [hout]
  exact memRegion_partition_eq b total offs hvalid hbound

/-- Partition a suffix `memRegion (b + BitVec.ofNat 64 off₀) rem` inside a region of total extent
    `total` (`rem = total - off₀`) across ascending byte offsets `offs = [off₁, ..., offₖ]`
    (each relative to `b`). -/
theorem memRegion_partition_at (b : BitVec 64) (off₀ total : Nat) (offs : List Nat)
    {rem : Nat} {out : SepProp}
    (hrem : rem = total - off₀ := by reduce_nat_eq)
    (hvalid : MemRegionPartitionValid off₀ total offs = true := by
      first | decide | (simp [MemRegionPartitionValid]; omega))
    (hbound : total - off₀ ≤ 2 ^ 64 := by first | decide | omega)
    (hout : out = memRegionPartitionAt b off₀ total offs := by reduce_partition_eq) :
    memRegion (b + BitVec.ofNat 64 off₀) rem = out := by
  subst hrem
  rw [hout]
  exact memRegion_partition_at_eq b offs off₀ total hvalid hbound

/-- Any sub-range `[base + off, base + off + subLen)` with `off.toNat + subLen ≤ len < 2^64`
    inside a `memRO m base len` region is also `memRO`. -/
theorem memRO_subregion {m : Memory} {base : BitVec 64} {len : Nat}
    (hRO : memRO m base len) (off : BitVec 64) (subLen : Nat)
    (hle : off.toNat + subLen ≤ len) (hlt64 : len < 2 ^ 64) :
    memRO m (base + off) subLen := by
  intro a ha
  apply hRO a
  simp only [InRegion] at ha ⊢
  have hsub : a - base = (a - (base + off)) + off := by bv_lin
  rw [hsub, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega


/-- Every byte inside a `memRO` region is `Frozen` (`Perm.ro`). -/
theorem memRO_frozen {m : Memory} {base a : BitVec 64} {len : Nat}
    (hro : memRO m base len) (ha : InRegion base len a) :
    m.Frozen a := by
  have hp := (hro a ha).1
  unfold Memory.Frozen
  rw [hp]
  rfl

/-- Split `ptr ↦₆₄* (ws1 ++ ws2)` into `(ptr ↦₆₄* ws1) ∗ ((ptr + 8 * ws1.length) ↦₆₄* ws2)`. -/
theorem pointsToWords64_append (ptr : BitVec 64) (ws1 ws2 : List (BitVec 64)) :
    (ptr ↦₆₄* (ws1 ++ ws2)) =
      (ptr ↦₆₄* ws1) ∗ ((ptr + BitVec.ofNat 64 (8 * ws1.length)) ↦₆₄* ws2) := by
  induction ws1 generalizing ptr with
  | nil =>
    simp [pointsToWords64_nil, emp_sepConj]
  | cons w ws1 ih =>
    simp only [List.cons_append, pointsToWords64_cons, List.length_cons, ih (ptr + 8#64),
      sepConj_assoc]
    congr 2
    have haddr : ptr + 8#64 + BitVec.ofNat 64 (8 * ws1.length) =
        ptr + BitVec.ofNat 64 (8 * (ws1.length + 1)) := by
      rw [BitVec.add_assoc]
      congr 1
      change BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * ws1.length) =
        BitVec.ofNat 64 (8 * (ws1.length + 1))
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    rw [haddr]

/-- A word array `a ↦₆₄* ws` entails `memRegion a (8 * ws.length)` (forgetting word values). -/
theorem pointsToWords64_entails_memRegion :
    ∀ (ws : List (BitVec 64)) (a : BitVec 64), 8 * ws.length ≤ 2 ^ 64 →
      (a ↦₆₄* ws) ⊢ memRegion a (8 * ws.length)
  | [], a, _ => by
    rw [List.length_nil, Nat.mul_zero, memRegion_zero, pointsToWords64_nil]
    exact Entails.refl _
  | w :: ws, a, h => by
    rw [pointsToWords64_cons]
    refine Entails.trans
      (sepConj_mono_right (pointsToWords64_entails_memRegion ws (a + 8#64) (by simp at h; omega)))
      ?_
    have := memRegion_cons a w (n := 8 * (ws.length + 1)) (by omega) (by simpa using h)
    simpa [Nat.mul_add] using this

/-- An `8 * n`-byte `memRegion` entails an existential `n`-element word array `a ↦₆₄* ws`. -/
theorem memRegion_entails_pointsToWords64 :
    ∀ (n : Nat) (a : BitVec 64), 8 * n ≤ 2 ^ 64 →
      memRegion a (8 * n) ⊢ ∃∗ ws, ⌜ws.length = n⌝ ∗ (a ↦₆₄* ws)
  | 0, a, _ => by
    rw [Nat.mul_zero, memRegion_zero]
    exact Entails.sepExists_right [] (by simp; exact Entails.refl _)
  | n + 1, a, h => by
    rw [memRegion_uncons a (n := 8 * (n + 1)) (by omega) h]
    refine Entails.sepExists_elim fun v => ?_
    have e : 8 * (n + 1) - 8 = 8 * n := by omega
    rw [e]
    refine Entails.trans
      (sepConj_mono_right (memRegion_entails_pointsToWords64 n (a + 8#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun ws => ?_
    refine Entails.sepExists_right (v :: ws) ?_
    rw [sepConj_left_comm]
    refine Entails.pure_left fun hl => ?_
    rw [pointsToWords64_cons]
    simp only [List.length_cons, hl, pure_true, emp_sepConj]
    exact Entails.refl _


/-! ## Ghost-changing consequence -/

/-- Default auto-parameter tactic discharging out-of-memory side conditions in
    `subroutine_ok_of_ghost` and `reaches_of_ghost`. -/
elab "close_ghost_oom_default" : tactic => do
  let _ ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic (← `(tactic| (
    dsimp only [Program.relocSubroutineOk, Program.alignedSubroutineOk,
      Obj.LinkedImage.subroutineOk, Program.subroutineOk, fn_subroutine_ok,
      ToBaseSpec.toSpec, instToBaseSpecId, instToBaseSpecFn]))))
  for _ in [:3] do
    let mvarId ← Lean.Elab.Tactic.getMainGoal
    let ref ← IO.mkRef #[]
    mvarId.withContext do
      let collectFromExpr (e : Lean.Expr) : Lean.MetaM Unit := do
        e.forEach fun sub => do
          if sub.isConst then
            let nm := sub.constName!
            if nm != ``Arm64.Spec.mk then
              let ty ← Lean.Meta.inferType sub
              if ty.getForallBody.isAppOf ``Arm64.Spec then
                let arr ← ref.get
                if !arr.any (fun i => i.getId == nm) then
                  ref.set (arr.push (Lean.mkIdent nm))
      collectFromExpr (← Lean.instantiateMVars (← mvarId.getType))
    let ids ← ref.get
    if ids.isEmpty then break
    for id in ids do
      let _ ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only [$id:ident])))
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    first | intro _ _ _ _ _ _ _ ho | intro _ _ ho
    try simp only [Spec.noPanic, Spec.allowPanicWhen, Spec.allowPanic, Spec.panicsOr, Spec.allowOom] at ho ⊢
    try dsimp only at ho ⊢
    first
      | exact ho
      | exact False.elim (not_satisfies_false_sepConj ho)
      | exact satisfies_true_sepConj ho
      | exact satisfies_true_sepConj_frame ho
      | exact Satisfies.drop_mid ho
      | exact satisfies_true_sepConj_frame (Satisfies.drop_mid ho))))

/-- Prove `subroutine_ok` for `spec'` from `subroutine_ok` for a low-level `spec` (with a possibly
    different ghost type): for every entry state satisfying `spec'.pre x' s0 ∗ R`, choose a ghost `x`
    and a frame `F` with `spec.pre x s0 ∗ F ∗ R`, such that every return state satisfying
    `spec.post x s0 sf ∗ F ∗ R` (and preserving the calling convention) satisfies `spec'.post x' s0 sf ∗ R`. -/
theorem subroutine_ok_of_ghost {α β : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry_pc spec)
    (hstep : ∀ x' R s0, (s0.mem ⊨ spec'.pre x' s0 ∗ R) →
      ∃ x F, (s0.mem ⊨ spec.pre x s0 ∗ (F ∗ R)) ∧
        ∀ sf, CallingConventionPreserved s0 sf → (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ spec'.post x' s0 sf ∗ R))
    (h_no_panic : ∀ x R s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R) := by
      intro _ _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R) := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ x x' F R s0 sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ spec'.onOom x' s0 sf ∗ R) := by
      close_ghost_oom_default) :
    subroutine_ok prog entry_pc spec' := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at h ⊢
  intro x' R s0 hpc hrun hp hsp_align hL
  obtain ⟨x, F, hpre, hpost⟩ := hstep x' R s0 hp
  rcases h x (F ∗ R) s0 hpc hrun hpre hsp_align hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret, hcc, hpost sf hcc hq⟩⟩
  · exact absurd hq (h_no_panic x (F ∗ R) s0 sf hpan)
  · exact absurd hq (h_no_exit x code (F ∗ R) s0 sf hex)
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, h_oom x x' F R s0 sf hoom hq⟩))⟩

/-- Per-state form of `subroutine_ok_of_ghost`, for proofs that case-split on the entry state and
    dispatch different paths to different low-level specs. -/
theorem reaches_of_ghost {α β : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} {spec' : Spec β} {x' : β} {R : SepProp} {s0 : State}
    {oom : State → Prop}
    (h : subroutine_ok prog entry_pc spec) (x : α) (F : SepProp)
    (hpc : s0.pc = entry_pc) (hrun : s0.status = .Running) (hsp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ (F ∗ R))
    (hpost : ∀ sf, CallingConventionPreserved s0 sf → (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R)) →
      (sf.mem ⊨ spec'.post x' s0 sf ∗ R))
    (h_no_panic : ∀ sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ (F ∗ R)) := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ (F ∗ R)) := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s0 sf ∗ (F ∗ R)) → oom sf := by
      close_ghost_oom_default) :
    reaches_pc prog (s0.readReg64 Reg.lr) s0 (SubroutinePost spec' x' R s0) oom := by
  intro hL
  simp only [subroutine_ok_iff, reaches_outcome_iff] at h
  rcases h x (F ∗ R) s0 hpc hrun hpre hsp_align hL with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hret.1, hret.2.2, hpost sf hcc hq, hcc⟩⟩
  · exact absurd hq (h_no_panic sf hpan)
  · exact absurd hq (h_no_exit code sf hex)
  · exact ⟨sf, hsteps, Or.inr ⟨hoom, h_oom sf hoom hq⟩⟩

private theorem stackFrameSlotsCont_region (sp : BitVec 64) (k : Nat) :
    ∀ (n : Nat) (X : SepProp), n * 8 ≤ 2 ^ 64 →
      stackFrameSlotsCont sp k n (fun rest => X ∗ rest) =
        X ∗ memRegion (sp - BitVec.ofNat 64 ((k + n) * 8)) (n * 8) := by
  intro n
  induction n with
  | zero => intro X _; simp [stackFrameSlotsCont, memRegion_zero, sepConj_emp]
  | succ n ih =>
    intro X hb
    cases n with
    | zero =>
      simp only [stackFrameSlotsCont, Nat.zero_add, Nat.one_mul, memRegion_eight,
        sepExists_sepConj_right]
    | succ m =>
      simp only [stackFrameSlotsCont]
      have hfun : ∀ v : BitVec 64,
          (fun rest => X ∗ (((sp - BitVec.ofNat 64 ((k + m + 2) * 8)) ↦₆₄ v) ∗ rest)) =
          (fun rest => (X ∗ ((sp - BitVec.ofNat 64 ((k + m + 2) * 8)) ↦₆₄ v)) ∗ rest) :=
        fun v => funext fun rest => (sepConj_assoc _ _ _).symm
      simp only [hfun]
      rw [funext fun v => ih (X ∗ _) (by omega)]
      simp only [sepConj_assoc, ← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← memRegion_eight]
      congr 1
      rw [memRegion_split' (b := sp - BitVec.ofNat 64 ((k + (m + 1 + 1)) * 8)) (n := 8)
        (k := (m + 1) * 8) (by omega) ?_ (by omega)]
      · congr 2 <;> omega
      · have h1 : (k + (m + 1 + 1)) * 8 = (k + (m + 1)) * 8 + 8 := by omega
        rw [h1, BitVec.ofNat_add]
        generalize BitVec.ofNat 64 ((k + (m + 1)) * 8) = x
        bv_arith

/-- Equivalence between an `n`-byte downward-growing `stackFrameAt sp n` and
    `memRegion (sp - BitVec.ofNat 64 n) n`. -/
theorem stackFrameAt_eq_memRegion (sp : BitVec 64) (n : Nat)
    (hn : n ≤ 2 ^ 64 := by first | decide | omega) :
    stackFrameAt sp n = memRegion (sp - BitVec.ofNat 64 n) n := by
  unfold stackFrameAt
  by_cases h0 : n = 0
  · subst h0; simp [memRegion_zero]
  by_cases h8 : n % 8 = 0
  · simp only [h0, h8, beq_iff_eq, ite_false, ite_true, stackFrameSlotsFrom]
    have hid : (fun P : SepProp => P) = (fun rest => SepProp.emp ∗ rest) :=
      funext fun _ => (emp_sepConj _).symm
    rw [hid, stackFrameSlotsCont_region sp 0 (n / 8) SepProp.emp (by omega), emp_sepConj,
      Nat.zero_add, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h8)]
  · simp [h0, h8]

/-- Convert an `8 * n`-byte `stackFrameAt (ptr + BitVec.ofNat 64 (8 * n)) (8 * n)` into an
    `n`-word 64-bit array `(ptr ↦₆₄* ws)`. -/
theorem stackFrameAt_eq_pointsToWords64 (ptr : BitVec 64) (n : Nat)
    (hb : 8 * n ≤ 2 ^ 64 := by first | decide | omega) :
    stackFrameAt (ptr + BitVec.ofNat 64 (8 * n)) (8 * n) =
      ∃∗ ws : List (BitVec 64), ⌜ws.length = n⌝ ∗ (ptr ↦₆₄* ws) := by
  rw [stackFrameAt_eq_memRegion (ptr + BitVec.ofNat 64 (8 * n)) (8 * n) hb]
  have hsub : ptr + BitVec.ofNat 64 (8 * n) - BitVec.ofNat 64 (8 * n) = ptr := by bv_arith
  rw [hsub]
  apply Entails.antisymm
  · exact memRegion_entails_pointsToWords64 n ptr hb
  · refine Entails.sepExists_elim fun ws => Entails.pure_left fun hl => ?_
    rw [← hl]
    exact pointsToWords64_entails_memRegion ws ptr (by rw [hl]; exact hb)

/-- Split or merge a `(m + n)`-byte downward-growing stack frame below `sp` into its top `m`
    bytes `[sp - m, sp)` and bottom `n` bytes `[sp - m - n, sp - m)`:
    `stackFrameAt sp (m + n) = stackFrameAt sp m ∗ stackFrameAt (sp - BitVec.ofNat 64 m) n`. -/
theorem stackFrameAt_split (sp : BitVec 64) (m n : Nat)
    (hmn : m + n ≤ 2 ^ 64 := by first | decide | omega) :
    stackFrameAt sp (m + n) =
      (stackFrameAt sp m ∗ stackFrameAt (sp - BitVec.ofNat 64 m) n) := by
  rw [stackFrameAt_eq_memRegion sp (m + n) hmn,
      stackFrameAt_eq_memRegion sp m (by omega),
      stackFrameAt_eq_memRegion (sp - BitVec.ofNat 64 m) n (by omega)]
  have hnm : m + n = n + m := Nat.add_comm m n
  rw [hnm, memRegion_split _ n m (by omega), sepConj_comm]
  have hbase : sp - BitVec.ofNat 64 (n + m) = sp - BitVec.ofNat 64 m - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have hmid : sp - BitVec.ofNat 64 (n + m) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 m := by
    rw [hbase, BitVec.sub_add_cancel]
  rw [hmid, hbase]

/-- Convert an `8 * n`-byte `stackFrameAt sp (8 * n)` into an existentially quantified `n`-word
    64-bit array `((sp - BitVec.ofNat 64 (8 * n)) ↦₆₄* ws)`. -/
theorem stackFrameAt_eq_exists_pointsToWords64 (sp : BitVec 64) (n : Nat)
    (hn : 8 * n ≤ 2 ^ 64 := by first | decide | omega) :
    stackFrameAt sp (8 * n) =
      ∃∗ ws : List (BitVec 64), ⌜ws.length = n⌝ ∗ ((sp - BitVec.ofNat 64 (8 * n)) ↦₆₄* ws) := by
  rw [stackFrameAt_eq_memRegion sp (8 * n) hn]
  apply Entails.antisymm
  · exact memRegion_entails_pointsToWords64 n (sp - BitVec.ofNat 64 (8 * n)) hn
  · refine Entails.sepExists_elim fun ws => Entails.pure_left fun hl => ?_
    subst hl
    exact pointsToWords64_entails_memRegion ws (sp - BitVec.ofNat 64 (8 * ws.length)) hn

/-! ## Allocator Non-Wrapping and Interior Field Non-Null Lemmas -/

/-- Every live block of an `Allocator` fits in the 64-bit address space without wrapping
    (`A.live p sz ⊢ ⌜p.toNat + sz ≤ 2 ^ 64⌝ ∗ A.live p sz`). -/
theorem _root_.Arm64.Allocator.live_noWrap (A : Arm64.Allocator) (p : BitVec 64) (sz : Nat) :
    A.live p sz ⊢ ⌜p.toNat + sz ≤ 2 ^ 64⌝ ∗ A.live p sz :=
  A.noWrap p sz

/-- Every live block of an `AllocatorOom` fits in the 64-bit address space without wrapping
    (`A.live p sz ⊢ ⌜p.toNat + sz ≤ 2 ^ 64⌝ ∗ A.live p sz`). -/
theorem _root_.Arm64.AllocatorOom.live_noWrap (A : Arm64.AllocatorOom) (p : BitVec 64) (sz : Nat) :
    A.live p sz ⊢ ⌜p.toNat + sz ≤ 2 ^ 64⌝ ∗ A.live p sz :=
  A.noWrap p sz

/-- Extract `p.toNat + sz ≤ 2 ^ 64` from memory satisfaction `m ⊨ A.live p sz ∗ R`. -/
theorem _root_.Arm64.Allocator.live_noWrap_of_satisfies {A : Arm64.Allocator} {p : BitVec 64}
    {sz : Nat} {R : SepProp} {m : Memory} (hm : m ⊨ A.live p sz ∗ R) :
    p.toNat + sz ≤ 2 ^ 64 := by
  have hm' := Satisfies.mono (sepConj_mono_left (A.noWrap p sz)) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
  exact hm'.1

/-- Extract `p.toNat + sz ≤ 2 ^ 64` from memory satisfaction `m ⊨ A.live p sz ∗ R` for `AllocatorOom`. -/
theorem _root_.Arm64.AllocatorOom.live_noWrap_of_satisfies {A : Arm64.AllocatorOom} {p : BitVec 64}
    {sz : Nat} {R : SepProp} {m : Memory} (hm : m ⊨ A.live p sz ∗ R) :
    p.toNat + sz ≤ 2 ^ 64 :=
  A.toAllocator.live_noWrap_of_satisfies hm

/-- Any interior or base byte offset `off < sz` of a non-null, non-wrapping block `[p, p + sz)`
    has a non-null 64-bit address `p + BitVec.ofNat 64 off ≠ 0#64`. -/
theorem add_ofNat_ne_zero_of_noWrap {p : BitVec 64} {off sz : Nat}
    (hp : p ≠ 0#64) (hoff : off < sz) (hnw : p.toNat + sz ≤ 2 ^ 64) :
    p + BitVec.ofNat 64 off ≠ 0#64 := by
  intro hzero
  have hp_pos : 0 < p.toNat := by
    rcases Nat.eq_zero_or_pos p.toNat with h0 | hpos
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hp
    · exact hpos
  have htoNat : (p + BitVec.ofNat 64 off).toNat = 0 := by rw [hzero]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at htoNat
  omega

/-- Separation-logic entailment extracting non-nullness of an interior field address
    `p + BitVec.ofNat 64 off` (`off < sz`) from `A.live p sz` when `p ≠ 0#64`. -/
theorem _root_.Arm64.Allocator.live_field_ne_zero (A : Arm64.Allocator) (p : BitVec 64)
    (off sz : Nat) (hp : p ≠ 0#64) (hoff : off < sz) :
    A.live p sz ⊢ ⌜p + BitVec.ofNat 64 off ≠ 0#64⌝ ∗ A.live p sz := by
  refine Entails.trans (A.noWrap p sz) ?_
  refine Entails.pure_left fun hnw => ?_
  exact Entails.pure_right (add_ofNat_ne_zero_of_noWrap hp hoff hnw) (Entails.refl _)

/-- Extract `p + BitVec.ofNat 64 off ≠ 0#64` for an interior field (`off < sz`) of a non-null
    live allocation from `m ⊨ A.live p sz ∗ R`. -/
theorem _root_.Arm64.Allocator.live_field_ne_zero_of_satisfies {A : Arm64.Allocator}
    {p : BitVec 64} {off sz : Nat} {R : SepProp} {m : Memory}
    (hp : p ≠ 0#64) (hoff : off < sz) (hm : m ⊨ A.live p sz ∗ R) :
    p + BitVec.ofNat 64 off ≠ 0#64 :=
  add_ofNat_ne_zero_of_noWrap hp hoff (A.live_noWrap_of_satisfies hm)

end

end ProofLib
