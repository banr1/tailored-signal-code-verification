/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps

/-!
# `ReductionDsl` Program-Size Lower Bounds on Lookup Trees

**Checked by Lean.** `Expr.cost` and `Comp.cost` charge each branch (`ite`, `caseOpt`, `caseSum`) by
its costlier arm (`max`), so a depth-`d` decision tree tabulating `f : ℕ → ℕ` on `d` input bits has
`O(d)` step cost despite encoding `2 ^ d` leaves. This module checks that `Expr.size`, `Comp.size`,
`CostedReduction.size`, and `TwoStageCostedReduction.size` instead sum both branch arms and
byte-literal payloads (`Ops.opSize`) while counting bounded loop bodies (`Comp.iter`, `Expr.foldrB`)
once: `(tree f d).size ≥ 2 ^ d` and `(byteTree w f d).size ≥ 2 ^ d * L`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Guards.ReductionDslSize

open ReductionDsl

section Generic

variable {S : Sig} {O : Ops S}

/-- Depth-`d` decision tree over the low `d` bits of the nat in `v0`; the leaf for bit pattern `i`
(read LSB first) is the constant `f i`. Uses `letE` to cache `x / 2`, so each level costs `O(1)`. -/
def tree (f : ℕ → ℕ) : (d : ℕ) → {Γ : List (Ty S)} → Expr O (.nat :: Γ) .nat
  | 0, _ => .nat (f 0)
  | d + 1, _ =>
      .letE (.divK 2 .v0)
        (.ite (.eqN (.modK 2 .v1) (.nat 0))
          (tree (fun i => f (2 * i)) d)
          (tree (fun i => f (2 * i + 1)) d))

theorem tree_eval (d : ℕ) : ∀ (f : ℕ → ℕ) {Γ : List (Ty S)} (x : ℕ) (ρ : Env Γ),
    (tree (O := O) f d).eval (.cons x ρ) = f (x % 2 ^ d) := by
  induction d with
  | zero => intro f Γ x ρ; simp [tree, Expr.eval, Nat.mod_one]
  | succ d ih =>
    intro f Γ x ρ
    have hsplit : x % 2 ^ (d + 1) = x % 2 + 2 * ((x / 2) % 2 ^ d) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    simp only [tree, Expr.eval, Expr.v0, Expr.v1, Env.get]
    split_ifs with h
    · rw [ih]
      have h' : x % 2 = 0 := by simpa using h
      rw [hsplit, h', Nat.zero_add]
    · rw [ih]
      have h' : x % 2 = 1 := by
        have : ¬ x % 2 = 0 := by simpa using h
        omega
      rw [hsplit, h', Nat.add_comm]

/-- Per-level `Expr.cost` overhead of `tree` (`= 10`). -/
def lvl : ℕ := 2 * bits 2 + bits 0 + 5

theorem tree_cost (d : ℕ) : ∀ (f : ℕ → ℕ) (B : ℕ) (_hf : ∀ i, bits (f i) ≤ B) {Γ : List (Ty S)},
    (tree (O := O) (Γ := Γ) f d).cost ≤ lvl * d + B := by
  induction d with
  | zero => intro f B hf Γ; simpa [tree, Expr.cost] using hf 0
  | succ d ih =>
    intro f B hf Γ
    have h0 := ih (fun i => f (2 * i)) B (fun i => hf _) (Γ := Ty.nat :: Γ)
    have h1 := ih (fun i => f (2 * i + 1)) B (fun i => hf _) (Γ := Ty.nat :: Γ)
    have hm := max_le h0 h1
    simp only [tree, Expr.cost, Expr.v0, Expr.v1]
    rw [Nat.mul_succ]
    have hl : lvl = 2 * bits 2 + bits 0 + 5 := rfl
    generalize lvl * d = L at hm ⊢
    omega

theorem bits_two : bits 2 = 2 := by
  unfold bits
  have : Nat.log 2 2 = 1 := by
    have := Nat.log_pow (b := 2) (by norm_num) 1
    simpa using this
  rw [this]

theorem bits_zero : bits 0 = 1 := by
  unfold bits; simp

theorem lvl_eq : lvl = 10 := by
  simp only [lvl, bits_two, bits_zero]

theorem bits_le_of_lt {n k : ℕ} (h : n < 2 ^ k) : bits n ≤ k + 1 := by
  unfold bits
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Nat.log_lt_of_lt_pow (b := 2) (Nat.pos_iff_ne_zero.mp hn) h
    omega

/-- Right inverse of `h` on `[0, 2 ^ 256)`, defaulting to `0` outside its image. -/
noncomputable def inv (h : ℕ → ℕ) (y : ℕ) : ℕ :=
  if hy : ∃ x, x < 2 ^ 256 ∧ h x = y then Classical.choose hy else 0

theorem inv_lt (h : ℕ → ℕ) (y : ℕ) : inv h y < 2 ^ 256 := by
  unfold inv
  split_ifs with hy
  · exact (Classical.choose_spec hy).1
  · exact Nat.two_pow_pos 256

/-- `tree (inv h) 256` inverts any `h : ℕ → ℕ` on `256`-bit inputs at `Expr.cost ≤ 2817`. -/
theorem invert_any (h : ℕ → ℕ) {Γ : List (Ty S)} :
    ∃ e : Expr O (.nat :: Γ) .nat, e.cost ≤ 10 * 256 + 257 ∧
      ∀ (x y : ℕ) (ρ : Env Γ), x < 2 ^ 256 → y < 2 ^ 256 → h x = y →
        h (e.eval (.cons y ρ)) = y := by
  refine ⟨tree (inv h) 256, ?_, ?_⟩
  · have := tree_cost (O := O) (Γ := Γ) 256 (inv h) 257 (fun i => bits_le_of_lt (inv_lt h i))
    rw [lvl_eq] at this
    exact this
  · intro x y ρ hx hy hxy
    rw [tree_eval, Nat.mod_eq_of_lt hy]
    have hex : ∃ x, x < 2 ^ 256 ∧ h x = y := ⟨x, hx, hxy⟩
    unfold inv
    split_ifs
    exact (Classical.choose_spec hex).2

theorem bits_pos (n : ℕ) : 1 ≤ bits n := by
  unfold bits; omega

theorem expr_size_pos {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) : 1 ≤ e.size := by
  cases e <;> simp [Expr.size, bits] <;> omega

theorem comp_size_pos {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) : 1 ≤ c.size := by
  cases c <;> simp [Comp.size]

theorem tree_size_ge (d : ℕ) : ∀ (f : ℕ → ℕ) {Γ : List (Ty S)},
    (tree (O := O) (Γ := Γ) f d).size ≥ 2 ^ d := by
  induction d with
  | zero =>
    intro f Γ
    have hb := bits_pos (f 0)
    simp only [tree, Expr.size, Nat.pow_zero]
    omega
  | succ d ih =>
    intro f Γ
    have h0 := ih (fun i => f (2 * i)) (Γ := Ty.nat :: Γ)
    have h1 := ih (fun i => f (2 * i + 1)) (Γ := Ty.nat :: Γ)
    simp only [tree, Expr.size, Expr.v0, Expr.v1]
    rw [Nat.pow_succ]
    omega

theorem tree_not_size_le_of_lt {d B : ℕ} (hB : B < 2 ^ d) (f : ℕ → ℕ) {Γ : List (Ty S)} :
    ¬ (tree (O := O) (Γ := Γ) f d).size ≤ B := by
  have hsize := tree_size_ge (O := O) (Γ := Γ) d f
  omega

theorem comp_tree_not_size_le_of_lt {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {d B : ℕ} (hB : B < 2 ^ d) (f : ℕ → ℕ) {Γ : List (Ty S)} :
    ¬ (Comp.ret (tree (O := O) (Γ := Γ) f d) : Comp O I (.nat :: Γ) .nat).size ≤ B := by
  have hsize := tree_size_ge (O := O) (Γ := Γ) d f
  simp only [Comp.size]
  omega

theorem costedReduction_finish_tree_not_size_le_of_lt
    {ι κ : Type} {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn : Ty S}
    (init : Comp O I [rIn] (.prod aIn .nat))
    (handle : Comp O I [.nat, C.Q] (.prod C.R .nat))
    {d B : ℕ} (hB : B < 2 ^ d) (f : ℕ → ℕ) :
    ¬ ({ σ := .nat, init := init, handle := handle,
         finish := .ret (tree (O := O) (Γ := [.nat]) f d) } :
        CostedReduction O I G C rIn aIn .nat .nat).size ≤ B := by
  have hsize := tree_size_ge (O := O) (Γ := [.nat]) d f
  simp only [CostedReduction.size, Comp.size]
  omega

theorem twoStageCostedReduction_finish_tree_not_size_le_of_lt
    {ι κ : Type} {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn ch rIn2 : Ty S}
    (init : Comp O I [rIn] (.prod aIn .nat))
    (handlePre : Comp O I [.nat, C.Q] (.sum (.prod C.R .nat) (.prod ch (.prod .nat .nat))))
    (chDone : Comp O I [.nat, .nat] ch)
    (resume : Comp O I [.nat, .nat, rIn2] (.prod C.R .nat))
    (handlePost : Comp O I [.nat, C.Q] (.prod C.R .nat))
    {d B : ℕ} (hB : B < 2 ^ d) (f : ℕ → ℕ) :
    ¬ ({ σ := .nat, π := .nat, init := init, handlePre := handlePre, chDone := chDone,
         resume := resume, handlePost := handlePost,
         finish := .ret (tree (O := O) (Γ := [.nat, rIn2]) f d) } :
        TwoStageCostedReduction O I G C rIn aIn .nat ch rIn2 .nat).size ≤ B := by
  have hsize := tree_size_ge (O := O) (Γ := [.nat, rIn2]) d f
  simp only [TwoStageCostedReduction.size, Comp.size]
  omega

theorem invert_tree_cost_small_and_rejects_budget_2_pow_24 (h : ℕ → ℕ) {Γ : List (Ty S)} :
    (tree (O := O) (Γ := Γ) (inv h) 256).cost ≤ 2817 ∧
    ¬ (tree (O := O) (Γ := Γ) (inv h) 256).size ≤ 2 ^ 24 := by
  refine ⟨?_, tree_not_size_le_of_lt (by norm_num) (inv h)⟩
  have hc := tree_cost (O := O) (Γ := Γ) 256 (inv h) 257 (fun i => bits_le_of_lt (inv_lt h i))
  rw [lvl_eq] at hc
  omega

theorem comp_iter_size_body_once {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (n : ℕ) (e : Expr O Γ t) (body : Comp O I (t :: Γ) t) :
    (Comp.iter n e body).size = e.size + body.size + bits n + 1 :=
  rfl

theorem expr_foldrB_size_body_once {Γ : List (Ty S)} {t u : Ty S}
    (K : ℕ) (l : Expr O Γ (.list t)) (z : Expr O Γ u) (f : Expr O (t :: u :: Γ) u) :
    (Expr.foldrB K l z f).size = l.size + z.size + f.size + bits K + 1 :=
  rfl

end Generic

section ByteLiteralTree

variable {ℓ : ℕ} {Pt : Type}

/-- Depth-`d` decision tree over `atomicPureOps ℓ Pt` with `AtomicPureOp.bytesLit w (f i)` leaves. -/
def byteTree (w : ℕ+) (f : ℕ → List (BitVec 8)) :
    (d : ℕ) → {Γ : List (Ty (atomicSig ℓ Pt))} →
      Expr (atomicPureOps ℓ Pt) (.nat :: Γ) (ReductionDsl.B w)
  | 0, _ => Expr.op (O := atomicPureOps ℓ Pt) (AtomicPureOp.bytesLit w (f 0)) .unit
  | d + 1, _ =>
      .letE (.divK 2 .v0)
        (.ite (.eqN (.modK 2 .v1) (.nat 0))
          (byteTree w (fun i => f (2 * i)) d)
          (byteTree w (fun i => f (2 * i + 1)) d))

theorem byteTree_eval (w : ℕ+) (d : ℕ) :
    ∀ (f : ℕ → List (BitVec 8)) {Γ : List (Ty (atomicSig ℓ Pt))} (x : ℕ) (ρ : Env Γ),
    (byteTree (ℓ := ℓ) (Pt := Pt) w f d).eval (.cons x ρ) = f (x % 2 ^ d) := by
  induction d with
  | zero => intro f Γ x ρ; simp [byteTree, Expr.eval, AtomicPureOp.eval, Nat.mod_one]
  | succ d ih =>
    intro f Γ x ρ
    have hsplit : x % 2 ^ (d + 1) = x % 2 + 2 * ((x / 2) % 2 ^ d) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    simp only [byteTree, Expr.eval, Expr.v0, Expr.v1, Env.get]
    split_ifs with h
    · rw [ih]
      have h' : x % 2 = 0 := by simpa using h
      rw [hsplit, h', Nat.zero_add]
    · rw [ih]
      have h' : x % 2 = 1 := by
        have : ¬ x % 2 = 0 := by simpa using h
        omega
      rw [hsplit, h', Nat.add_comm]

theorem byteTree_cost (w : ℕ+) (d : ℕ) :
    ∀ (f : ℕ → List (BitVec 8)) (L : ℕ) (_hf : ∀ i, (f i).length ≤ L)
      {Γ : List (Ty (atomicSig ℓ Pt))},
    (byteTree (ℓ := ℓ) (Pt := Pt) (Γ := Γ) w f d).cost ≤ lvl * d + ((w : ℕ) + L + 1) := by
  induction d with
  | zero =>
    intro f L hf Γ
    have h0 := hf 0
    simp only [byteTree, Expr.cost, atomicPureOps, AtomicPureOp.cost]
    omega
  | succ d ih =>
    intro f L hf Γ
    have h0 := ih (fun i => f (2 * i)) L (fun i => hf _) (Γ := Ty.nat :: Γ)
    have h1 := ih (fun i => f (2 * i + 1)) L (fun i => hf _) (Γ := Ty.nat :: Γ)
    have hm := max_le h0 h1
    simp only [byteTree, Expr.cost, Expr.v0, Expr.v1]
    rw [Nat.mul_succ]
    have hl : lvl = 2 * bits 2 + bits 0 + 5 := rfl
    generalize lvl * d = K at hm ⊢
    omega

theorem byteTree_size_ge (w : ℕ+) (d : ℕ) (L : ℕ) :
    ∀ (f : ℕ → List (BitVec 8)) (_hf : ∀ i, L ≤ (f i).length)
      {Γ : List (Ty (atomicSig ℓ Pt))},
    (byteTree (ℓ := ℓ) (Pt := Pt) (Γ := Γ) w f d).size ≥ 2 ^ d * L := by
  induction d with
  | zero =>
    intro f hf Γ
    have h0 := hf 0
    simp only [byteTree, Expr.size, atomicPureOps, AtomicPureOp.opSize, Nat.pow_zero, Nat.one_mul]
    omega
  | succ d ih =>
    intro f hf Γ
    have h0 := ih (fun i => f (2 * i)) (fun i => hf _) (Γ := Ty.nat :: Γ)
    have h1 := ih (fun i => f (2 * i + 1)) (fun i => hf _) (Γ := Ty.nat :: Γ)
    have hpow : 2 ^ (d + 1) * L = 2 ^ d * L + 2 ^ d * L := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.add_mul]
    simp only [byteTree, Expr.size, Expr.v0, Expr.v1, hpow]
    omega

theorem byteTree_not_size_le_of_lt {w : ℕ+} {d L M : ℕ} (hM : M < 2 ^ d * L)
    (f : ℕ → List (BitVec 8)) (hf : ∀ i, L ≤ (f i).length)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    ¬ (byteTree (ℓ := ℓ) (Pt := Pt) (Γ := Γ) w f d).size ≤ M := by
  have hsize := byteTree_size_ge (ℓ := ℓ) (Pt := Pt) (Γ := Γ) w d L f hf
  omega

theorem costedReduction_finish_byteTree_not_size_le_of_lt
    {ι κ : Type} {T : OracleSpec ι} {I : Iface (atomicSig ℓ Pt) T}
    {G : OracleSpec κ} {C : GameCodec (atomicSig ℓ Pt) G} {rIn aIn : Ty (atomicSig ℓ Pt)}
    (init : Comp (atomicPureOps ℓ Pt) I [rIn] (.prod aIn .nat))
    (handle : Comp (atomicPureOps ℓ Pt) I [.nat, C.Q] (.prod C.R .nat))
    {w : ℕ+} {d L M : ℕ} (hM : M < 2 ^ d * L)
    (f : ℕ → List (BitVec 8)) (hf : ∀ i, L ≤ (f i).length) :
    ¬ ({ σ := .nat, init := init, handle := handle,
         finish := .ret (byteTree (ℓ := ℓ) (Pt := Pt) (Γ := [.nat]) w f d) } :
        CostedReduction (atomicPureOps ℓ Pt) I G C rIn aIn .nat (ReductionDsl.B w)).size ≤ M := by
  have hsize := byteTree_size_ge (ℓ := ℓ) (Pt := Pt) (Γ := [.nat]) w d L f hf
  simp only [CostedReduction.size, Comp.size]
  omega

theorem byteTree_depth20_1MiB_cost_small_and_rejects_budget_2_pow_24
    (f : ℕ → List (BitVec 8)) (hf : ∀ i, (f i).length = 2 ^ 20)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (byteTree (ℓ := ℓ) (Pt := Pt) (Γ := Γ) 1 f 20).cost ≤ 2 ^ 20 + 202 ∧
    (byteTree (ℓ := ℓ) (Pt := Pt) (Γ := Γ) 1 f 20).size ≥ 2 ^ 40 ∧
    ¬ (byteTree (ℓ := ℓ) (Pt := Pt) (Γ := Γ) 1 f 20).size ≤ 2 ^ 24 := by
  refine ⟨?_, ?_, byteTree_not_size_le_of_lt (L := 2 ^ 20) (by norm_num) f (fun i => by rw [hf i])⟩
  · have hc := byteTree_cost (ℓ := ℓ) (Pt := Pt) (Γ := Γ) 1 20 f (2 ^ 20) (fun i => by rw [hf i])
    rw [lvl_eq] at hc
    exact hc
  · have hs := byteTree_size_ge (ℓ := ℓ) (Pt := Pt) (Γ := Γ) 1 20 (2 ^ 20) f (fun i => by rw [hf i])
    simpa using hs

/-- Depth-`d` decision tree over `atomicPureOps ℓ Pt` with `AtomicPureOp.pbytesLit w (g i)` leaves. -/
def pbyteTree (w : ℕ+) (g : ℕ → List UInt8) :
    (d : ℕ) → {Γ : List (Ty (atomicSig ℓ Pt))} →
      Expr (atomicPureOps ℓ Pt) (.nat :: Γ) (ReductionDsl.PB w)
  | 0, _ => Expr.op (O := atomicPureOps ℓ Pt) (AtomicPureOp.pbytesLit w (g 0)) .unit
  | d + 1, _ =>
      .letE (.divK 2 .v0)
        (.ite (.eqN (.modK 2 .v1) (.nat 0))
          (pbyteTree w (fun i => g (2 * i)) d)
          (pbyteTree w (fun i => g (2 * i + 1)) d))

theorem pbyteTree_size_ge (w : ℕ+) (d : ℕ) (L : ℕ) :
    ∀ (g : ℕ → List UInt8) (_hg : ∀ i, L ≤ (g i).length)
      {Γ : List (Ty (atomicSig ℓ Pt))},
    (pbyteTree (ℓ := ℓ) (Pt := Pt) (Γ := Γ) w g d).size ≥ 2 ^ d * L := by
  induction d with
  | zero =>
    intro g hg Γ
    have h0 := hg 0
    simp only [pbyteTree, Expr.size, atomicPureOps, AtomicPureOp.opSize, Nat.pow_zero, Nat.one_mul]
    omega
  | succ d ih =>
    intro g hg Γ
    have h0 := ih (fun i => g (2 * i)) (fun i => hg _) (Γ := Ty.nat :: Γ)
    have h1 := ih (fun i => g (2 * i + 1)) (fun i => hg _) (Γ := Ty.nat :: Γ)
    have hpow : 2 ^ (d + 1) * L = 2 ^ d * L + 2 ^ d * L := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.add_mul]
    simp only [pbyteTree, Expr.size, Expr.v0, Expr.v1, hpow]
    omega

theorem pbyteTree_not_size_le_of_lt {w : ℕ+} {d L M : ℕ} (hM : M < 2 ^ d * L)
    (g : ℕ → List UInt8) (hg : ∀ i, L ≤ (g i).length)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    ¬ (pbyteTree (ℓ := ℓ) (Pt := Pt) (Γ := Γ) w g d).size ≤ M := by
  have hsize := pbyteTree_size_ge (ℓ := ℓ) (Pt := Pt) (Γ := Γ) w d L g hg
  omega

end ByteLiteralTree

end CryptoVerification.E2E.Guards.ReductionDslSize
