/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs

/-!
# AVL Height Bounds, Rotations, and Upward Zipper Rebalancing

**Checked by Lean.** Establishes strict linear-order helpers, the `2 * bits cap` logarithmic AVL
height bound (`avlTree_height_lt_avlHeightCap`), soundness of single and double rotations
(`avlBalanceNodePure_spec`), DSL evaluation of `avlRebalanceStepE`, and upward zipper rebalancing
(`avlFoldRebalance_spec`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableBalance

open _root_.ReductionDsl (
  Ty Var Expr Env pqAtomicSig pqAtomicOps bits
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlShapeTy avlPathItemTy avlHeightCap
  maxNatE nodeHeightE mkShapeNodeE joinHeightE avlRebalanceStepE
  AvlTree
)

structure StrictLinOrder {K : Type} (ltK : K → K → Prop) : Prop where
  irrefl : ∀ a, ¬ ltK a a
  trans  : ∀ {a b c}, ltK a b → ltK b c → ltK a c
  trich  : ∀ a b, ltK a b ∨ a = b ∨ ltK b a

theorem StrictLinOrder.asym {K : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK) {a b : K} (hab : ltK a b) : ¬ ltK b a :=
  fun hba => H.irrefl a (H.trans hab hba)

theorem StrictLinOrder.ne_of_lt {K : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK) {a b : K} (hab : ltK a b) : a ≠ b :=
  fun h => H.irrefl a (h ▸ hab)

theorem exists_split_of_mem {α : Type} {x : α} :
    ∀ {ys : List α}, x ∈ ys → ∃ ys₁ ys₂, ys = ys₁ ++ x :: ys₂
  | [], h => nomatch h
  | y :: ys, h => by
    rcases List.mem_cons.mp h with rfl | hm
    · exact ⟨[], ys, rfl⟩
    · obtain ⟨ys₁, ys₂, rfl⟩ := exists_split_of_mem hm
      exact ⟨y :: ys₁, ys₂, rfl⟩

theorem nodup_length_le_of_sub {α : Type} :
    ∀ {xs ys : List α}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    have ⟨hnotmem, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨ys₁, ys₂, rfl⟩ := exists_split_of_mem (hsub x List.mem_cons_self)
    have hsub' : ∀ z ∈ xs, z ∈ ys₁ ++ ys₂ := by
      intro z hz
      have hmem := hsub z (List.mem_cons_of_mem x hz)
      have hzx : z ≠ x := fun h => hnotmem (h ▸ hz)
      rcases List.mem_append.mp hmem with h1 | h2
      · exact List.mem_append_left _ h1
      · rcases List.mem_cons.mp h2 with rfl | h2'
        · exact False.elim (hzx rfl)
        · exact List.mem_append_right _ h2'
    have ih := nodup_length_le_of_sub hnd' hsub'
    simp only [List.length_cons, List.length_append] at ih ⊢
    omega

theorem avlTree_shapeTbl_zero {K V : Type} {ltK : K → K → Prop}
    {kvTbl : ℕ → K × V} {shapeTbl : ℕ → ℕ × (ℕ × ℕ)} {maxId id h : ℕ} {kvs : List (K × V)}
    (ht : AvlTree ltK kvTbl shapeTbl maxId id h kvs) :
    shapeTbl 0 = (0, (0, 0)) := by
  induction ht with
  | leaf h0 => exact h0
  | node _ _ _ _ _ _ _ _ _ _ _ ihL _ => exact ihL

theorem avlTree_height_eq {K V : Type} {ltK : K → K → Prop}
    {kvTbl : ℕ → K × V} {shapeTbl : ℕ → ℕ × (ℕ × ℕ)} {maxId id h : ℕ} {kvs : List (K × V)}
    (ht : AvlTree ltK kvTbl shapeTbl maxId id h kvs) :
    (shapeTbl id).2.2 = h := by
  cases ht with
  | leaf h0 => simp [h0]
  | node _ _ _ hsh => simp [hsh]

theorem avlTree_congr {K V : Type} {ltK : K → K → Prop}
    {kvTbl kvTbl' : ℕ → K × V} {shapeTbl shapeTbl' : ℕ → ℕ × (ℕ × ℕ)}
    {maxId maxId' id h : ℕ} {kvs : List (K × V)}
    (ht : AvlTree ltK kvTbl shapeTbl maxId id h kvs)
    (hMax : maxId ≤ maxId')
    (hZero : shapeTbl' 0 = (0, (0, 0)))
    (hEq : ∀ u, 0 < u → u ≤ maxId → kvTbl u ∈ kvs →
      kvTbl' u = kvTbl u ∧ shapeTbl' u = shapeTbl u) :
    AvlTree ltK kvTbl' shapeTbl' maxId' id h kvs := by
  induction ht with
  | leaf _ => exact .leaf hZero
  | @node id l r h lh rh k v kvsL kvsR hid0 hidMax hkv hsh hh hbal1 hbal2 hL hR hltL hltR ihL ihR =>
    have hmem_self : kvTbl id ∈ kvsL ++ (k, v) :: kvsR := by
      rw [hkv]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨hkv', hsh'⟩ := hEq id hid0 hidMax hmem_self
    refine .node hid0 (Nat.le_trans hidMax hMax) (hkv'.trans hkv) (hsh'.trans hsh) hh hbal1 hbal2
      (ihL ?_) (ihR ?_) hltL hltR
    · intro u hu0 huM hmem
      exact hEq u hu0 huM (List.mem_append_left _ hmem)
    · intro u hu0 huM hmem
      exact hEq u hu0 huM (List.mem_append_right _ (List.mem_cons_of_mem _ hmem))

theorem avlTree_kvs_pairwise {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK)
    {kvTbl : ℕ → K × V} {shapeTbl : ℕ → ℕ × (ℕ × ℕ)} {maxId id h : ℕ} {kvs : List (K × V)}
    (ht : AvlTree ltK kvTbl shapeTbl maxId id h kvs) :
    kvs.Pairwise (fun a b => ltK a.1 b.1) := by
  induction ht with
  | leaf _ => exact List.Pairwise.nil
  | @node id l r h lh rh k v kvsL kvsR _ _ _ _ _ _ _ _ _ hltL hltR ihL ihR =>
    rw [List.pairwise_append]
    refine ⟨ihL, List.Pairwise.cons (fun x hx => hltR x hx) ihR, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hltL a ha
    · exact H.trans (hltL a ha) (hltR b hb')

theorem avlTree_mem_kvs_has_id {K V : Type} {ltK : K → K → Prop}
    {kvTbl : ℕ → K × V} {shapeTbl : ℕ → ℕ × (ℕ × ℕ)} {maxId id h : ℕ} {kvs : List (K × V)}
    (ht : AvlTree ltK kvTbl shapeTbl maxId id h kvs) :
    ∀ kv ∈ kvs, ∃ u, 1 ≤ u ∧ u ≤ maxId ∧ kvTbl u = kv := by
  induction ht with
  | leaf _ => intro _ h; nomatch h
  | @node id l r h lh rh k v kvsL kvsR hid0 hidMax hkv _ _ _ _ _ _ _ _ ihL ihR =>
    intro kv hmem
    rcases List.mem_append.mp hmem with hL | hR
    · exact ihL kv hL
    · rcases List.mem_cons.mp hR with rfl | hR'
      · exact ⟨id, hid0, hidMax, hkv⟩
      · exact ihR kv hR'

theorem avlTree_length_le_maxId {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK)
    {kvTbl : ℕ → K × V} {shapeTbl : ℕ → ℕ × (ℕ × ℕ)} {maxId id h : ℕ} {kvs : List (K × V)}
    (ht : AvlTree ltK kvTbl shapeTbl maxId id h kvs) :
    kvs.length ≤ maxId := by
  have hpw : (kvs.map Prod.fst).Pairwise (fun a b => a ≠ b) := by
    rw [List.pairwise_map]
    exact (avlTree_kvs_pairwise H ht).imp fun hlt => H.ne_of_lt hlt
  have hnd : (kvs.map Prod.fst).Nodup := List.Pairwise.imp (fun h => h) hpw
  let tblKeys : List K := (List.range maxId).map (fun i => (kvTbl (i + 1)).1)
  have hsub : ∀ x ∈ kvs.map Prod.fst, x ∈ tblKeys := by
    intro x hx
    obtain ⟨kv, hkvMem, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u, hu1, huM, huEq⟩ := avlTree_mem_kvs_has_id ht kv hkvMem
    refine List.mem_map.mpr ⟨u - 1, List.mem_range.mpr (by omega), ?_⟩
    have hu : u - 1 + 1 = u := by omega
    rw [hu, huEq]
  have hlen := nodup_length_le_of_sub hnd hsub
  simpa [tblKeys] using hlen

theorem avlTree_pow_le_length {K V : Type} {ltK : K → K → Prop}
    {kvTbl : ℕ → K × V} {shapeTbl : ℕ → ℕ × (ℕ × ℕ)} {maxId id h : ℕ} {kvs : List (K × V)}
    (ht : AvlTree ltK kvTbl shapeTbl maxId id h kvs) :
    h = 0 ∨ 2 ^ (h / 2) ≤ kvs.length := by
  induction ht with
  | leaf _ => exact Or.inl rfl
  | @node id l r h lh rh k v kvsL kvsR _ _ _ _ hh hbal1 hbal2 _ _ _ _ ihL ihR =>
    right
    simp only [List.length_append, List.length_cons]
    by_cases hh1 : h = 1
    · subst hh1; simp; omega
    · by_cases hh2 : h = 2
      · subst hh2
        have hmax : max lh rh = 1 := by omega
        rcases ihL with hl0 | hlPow
        · have hrh1 : rh = 1 := by omega
          rcases ihR with hr0 | hrPow
          · omega
          · rw [hrh1] at hrPow; norm_num at hrPow ⊢; omega
        · have hlPos : 1 ≤ kvsL.length := by
            have := Nat.one_le_two_pow (n := lh / 2); omega
          norm_num; omega
      · have hh3 : 3 ≤ h := by omega
        have hlhGe : h - 2 ≤ lh := by omega
        have hrhGe : h - 2 ≤ rh := by omega
        rcases ihL with hl0 | hlPow
        · omega
        · rcases ihR with hr0 | hrPow
          · omega
          · have hL' : 2 ^ ((h - 2) / 2) ≤ kvsL.length :=
              Nat.le_trans (Nat.pow_le_pow_right (by omega) (Nat.div_le_div_right hlhGe)) hlPow
            have hR' : 2 ^ ((h - 2) / 2) ≤ kvsR.length :=
              Nat.le_trans (Nat.pow_le_pow_right (by omega) (Nat.div_le_div_right hrhGe)) hrPow
            have hdiv : h / 2 = (h - 2) / 2 + 1 := by omega
            rw [hdiv, Nat.pow_succ]
            omega

theorem avlTree_height_lt_avlHeightCap {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK) {cap : ℕ}
    {kvTbl : ℕ → K × V} {shapeTbl : ℕ → ℕ × (ℕ × ℕ)} {maxId id h : ℕ} {kvs : List (K × V)}
    (ht : AvlTree ltK kvTbl shapeTbl maxId id h kvs)
    (hCap : maxId ≤ cap) :
    h < avlHeightCap cap := by
  unfold avlHeightCap bits
  rcases avlTree_pow_le_length ht with rfl | hPow
  · omega
  · have hLen : kvs.length ≤ cap := Nat.le_trans (avlTree_length_le_maxId H ht) hCap
    have hPowCap : 2 ^ (h / 2) ≤ cap := Nat.le_trans hPow hLen
    have hLog : h / 2 ≤ Nat.log 2 cap := Nat.le_log_of_pow_le (by omega) hPowCap
    omega

@[expose] def tsetPure {α : Type} (m : ℕ → α) (i : ℕ) (a : α) : ℕ → α :=
  fun j => if j = i then a else m j

theorem tsetPure_self {α : Type} (m : ℕ → α) (i : ℕ) (a : α) :
    tsetPure m i a i = a := by simp [tsetPure]

theorem tsetPure_ne {α : Type} (m : ℕ → α) {i j : ℕ} (a : α) (h : j ≠ i) :
    tsetPure m i a j = m j := by simp [tsetPure, h]

@[expose] def joinHeightPure (h1 h2 : ℕ) : ℕ :=
  (if decide (h1 < h2) then h2 else h1) + 1

theorem joinHeightPure_eq (h1 h2 : ℕ) : joinHeightPure h1 h2 = max h1 h2 + 1 := by
  by_cases h : h1 < h2 <;> simp [joinHeightPure, h] <;> omega

@[expose] def avlBalanceNodePure (p l r : ℕ) (sh : ℕ → ℕ × (ℕ × ℕ)) :
    ℕ × (ℕ → ℕ × (ℕ × ℕ)) :=
  let shl := sh l
  let shr := sh r
  let ll := shl.1
  let lr := shl.2.1
  let lh := shl.2.2
  let rl := shr.1
  let rr := shr.2.1
  let rh := shr.2.2
  if decide (rh + 1 < lh) then
    let llh := (sh ll).2.2
    let lrh := (sh lr).2.2
    if decide (llh < lrh) then
      let shlr := sh lr
      let lrl := shlr.1
      let lrr := shlr.2.1
      let hl' := joinHeightPure llh (sh lrl).2.2
      let hp' := joinHeightPure (sh lrr).2.2 rh
      let shA := tsetPure sh l (ll, (lrl, hl'))
      let shB := tsetPure shA p (lrr, (r, hp'))
      let shC := tsetPure shB lr (l, (p, joinHeightPure hl' hp'))
      (lr, shC)
    else
      let hp' := joinHeightPure lrh rh
      let shA := tsetPure sh p (lr, (r, hp'))
      let shB := tsetPure shA l (ll, (p, joinHeightPure llh hp'))
      (l, shB)
  else if decide (lh + 1 < rh) then
    let rlh := (sh rl).2.2
    let rrh := (sh rr).2.2
    if decide (rrh < rlh) then
      let shrl := sh rl
      let rll := shrl.1
      let rlr := shrl.2.1
      let hp' := joinHeightPure lh (sh rll).2.2
      let hr' := joinHeightPure (sh rlr).2.2 rrh
      let shA := tsetPure sh p (l, (rll, hp'))
      let shB := tsetPure shA r (rlr, (rr, hr'))
      let shC := tsetPure shB rl (p, (r, joinHeightPure hp' hr'))
      (rl, shC)
    else
      let hp' := joinHeightPure lh rlh
      let shA := tsetPure sh p (l, (rl, hp'))
      let shB := tsetPure shA r (p, (rr, joinHeightPure hp' rrh))
      (r, shB)
  else
    (p, tsetPure sh p (l, (r, joinHeightPure lh rh)))

@[expose] def avlRebalanceStepPure
    (item : ℕ × Bool) (acc : ℕ × (ℕ → ℕ × (ℕ × ℕ))) : ℕ × (ℕ → ℕ × (ℕ × ℕ)) :=
  let p := item.1
  let wl := item.2
  let c := acc.1
  let sh := acc.2
  let shp := sh p
  avlBalanceNodePure p (if wl then c else shp.1) (if wl then shp.2.1 else c) sh

theorem avlRebalanceStepPure_true (p c : ℕ) (sh : ℕ → ℕ × (ℕ × ℕ)) :
    avlRebalanceStepPure (p, true) (c, sh) = avlBalanceNodePure p c (sh p).2.1 sh := rfl

theorem avlRebalanceStepPure_false (p c : ℕ) (sh : ℕ → ℕ × (ℕ × ℕ)) :
    avlRebalanceStepPure (p, false) (c, sh) = avlBalanceNodePure p (sh p).1 c sh := rfl

theorem eval_letE {Γ : List (Ty pqAtomicSig)} {t u : Ty pqAtomicSig}
    (e : Expr pqAtomicOps Γ t) (b : Expr pqAtomicOps (t :: Γ) u) (ρ : Env Γ) :
    (Expr.letE e b).eval ρ = b.eval (.cons (e.eval ρ) ρ) := rfl

theorem eval_ite {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (c : Expr pqAtomicOps Γ .bool) (a b : Expr pqAtomicOps Γ t) (ρ : Env Γ) :
    (Expr.ite c a b).eval ρ = if c.eval ρ then a.eval ρ else b.eval ρ := rfl

theorem eval_tset {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (m : Expr pqAtomicOps Γ (.tbl t)) (i : Expr pqAtomicOps Γ .nat)
    (a : Expr pqAtomicOps Γ t) (ρ : Env Γ) :
    (Expr.tset m i a).eval ρ = tsetPure (m.eval ρ) (i.eval ρ) (a.eval ρ) := rfl

theorem eval_joinHeightE {Γ : List (Ty pqAtomicSig)}
    (a b : Expr pqAtomicOps Γ .nat) (ρ : Env Γ) :
    (joinHeightE a b).eval ρ = joinHeightPure (a.eval ρ) (b.eval ρ) := rfl

theorem ite_eq_ite {α : Type} {c1 c2 : Bool} {t1 t2 e1 e2 : α}
    (hc : c1 = c2) (ht : t1 = t2) (he : e1 = e2) :
    (if c1 then t1 else e1) = (if c2 then t2 else e2) := by
  subst hc ht he; rfl

theorem avlRebalanceStepE_eval {Γ : List (Ty pqAtomicSig)}
    (item : Expr pqAtomicOps Γ avlPathItemTy)
    (acc : Expr pqAtomicOps Γ (.prod .nat (.tbl avlShapeTy)))
    (ρ : Env Γ) :
    (avlRebalanceStepE item acc).eval ρ =
      avlRebalanceStepPure (item.eval ρ) (acc.eval ρ) := by
  unfold avlRebalanceStepE avlRebalanceStepPure avlBalanceNodePure tsetPure
  rw [eval_letE]
  have hPair : (Expr.pair item acc).eval ρ = (item.eval ρ, acc.eval ρ) := rfl
  rw [hPair]
  generalize item.eval ρ = iv, acc.eval ρ = av
  rcases iv with ⟨p, wl⟩
  rcases av with ⟨c, sh⟩
  cases wl <;> {
    dsimp only
    rw [eval_letE, eval_letE, eval_letE, eval_ite]
    refine ite_eq_ite rfl ?_ ?_
    · rw [eval_letE, eval_ite]
      refine ite_eq_ite rfl ?_ ?_
      · rw [eval_letE]
        simp only [eval_joinHeightE, mkShapeNodeE, nodeHeightE,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Env.get]
      · simp only [eval_joinHeightE, mkShapeNodeE, nodeHeightE,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Env.get]
    · rw [eval_ite]
      refine ite_eq_ite rfl ?_ ?_
      · rw [eval_letE, eval_ite]
        refine ite_eq_ite rfl ?_ ?_
        · rw [eval_letE]
          simp only [eval_joinHeightE, mkShapeNodeE, nodeHeightE,
            Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Env.get]
        · simp only [eval_joinHeightE, mkShapeNodeE, nodeHeightE,
            Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Env.get]
      · simp only [eval_joinHeightE, mkShapeNodeE,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get]
  }

theorem ne_id_of_lt {K V : Type} {ltK : K → K → Prop} (H : StrictLinOrder ltK)
    {kvTbl : ℕ → K × V} {i j : ℕ} {ki kj : K} {vi vj : V}
    (hi : kvTbl i = (ki, vi)) (hj : kvTbl j = (kj, vj)) (hlt : ltK ki kj) : i ≠ j :=
  fun h => H.ne_of_lt hlt (congrArg Prod.fst (hi.symm.trans (h ▸ hj)))

theorem not_mem_of_forall_lt {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK) {kvs : List (K × V)} {k : K} {v : V}
    (h : ∀ kv ∈ kvs, ltK kv.1 k) : (k, v) ∉ kvs :=
  fun hm => H.irrefl k (h (k, v) hm)

theorem not_mem_of_forall_gt {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK) {kvs : List (K × V)} {k : K} {v : V}
    (h : ∀ kv ∈ kvs, ltK k kv.1) : (k, v) ∉ kvs :=
  fun hm => H.irrefl k (h (k, v) hm)

theorem avlTree_tset_frame {K V : Type} {ltK : K → K → Prop}
    {kvTbl : ℕ → K × V} {sh : ℕ → ℕ × (ℕ × ℕ)} {maxId subId subH w : ℕ}
    {val : ℕ × (ℕ × ℕ)} {subKvs : List (K × V)}
    (ht : AvlTree ltK kvTbl sh maxId subId subH subKvs)
    (hw0 : 0 < w) (hwNotMem : kvTbl w ∉ subKvs) :
    AvlTree ltK kvTbl (tsetPure sh w val) maxId subId subH subKvs := by
  refine avlTree_congr ht (Nat.le_refl _) ?_ ?_
  · have h0 : (0 : ℕ) ≠ w := by omega
    simp [tsetPure, h0, avlTree_shapeTbl_zero ht]
  · intro u _ _ hmem
    exact ⟨rfl, by simp [tsetPure, show u ≠ w from fun h => hwNotMem (h ▸ hmem)]⟩

theorem tsetPure_preserve {K V : Type} {kvTbl : ℕ → K × V}
    {sh : ℕ → ℕ × (ℕ × ℕ)} {w : ℕ} {val : ℕ × (ℕ × ℕ)} {allKvs : List (K × V)}
    (hw0 : 0 < w) (hwMem : kvTbl w ∈ allKvs)
    {u : ℕ} (hu : u = 0 ∨ kvTbl u ∉ allKvs) :
    tsetPure sh w val u = sh u := by
  have hne : u ≠ w := by
    rcases hu with rfl | hnot
    · omega
    · exact fun h => hnot (h ▸ hwMem)
  simp [tsetPure, hne]

theorem avlBalanceNodePure_spec {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK)
    {kvTbl : ℕ → K × V} {sh : ℕ → ℕ × (ℕ × ℕ)} {maxId p l r lh rh ph : ℕ}
    {pk : K} {pv : V} {kvsL kvsR : List (K × V)}
    (hp0 : 0 < p) (hpMax : p ≤ maxId) (hkvP : kvTbl p = (pk, pv))
    (hL : AvlTree ltK kvTbl sh maxId l lh kvsL)
    (hR : AvlTree ltK kvTbl sh maxId r rh kvsR)
    (hltL : ∀ kv ∈ kvsL, ltK kv.1 pk)
    (hltR : ∀ kv ∈ kvsR, ltK pk kv.1)
    (hBnd1 : lh ≤ rh + 2) (hBnd2 : rh ≤ lh + 2)
    (hPhL : rh + 1 < lh → ph = rh + 2)
    (hPhR : lh + 1 < rh → ph = lh + 2)
    (hPhBal : lh ≤ rh + 1 → rh ≤ lh + 1 → ph ≤ max lh rh + 1 ∧ max lh rh + 1 ≤ ph + 1) :
    ∃ h',
      ph ≤ h' ∧ h' ≤ ph + 1 ∧
      AvlTree ltK kvTbl (avlBalanceNodePure p l r sh).2 maxId
        (avlBalanceNodePure p l r sh).1 h' (kvsL ++ (pk, pv) :: kvsR) ∧
      (∀ u, (u = 0 ∨ kvTbl u ∉ kvsL ++ (pk, pv) :: kvsR) →
        (avlBalanceNodePure p l r sh).2 u = sh u) := by
  have hlh_eq : (sh l).2.2 = lh := avlTree_height_eq hL
  have hrh_eq : (sh r).2.2 = rh := avlTree_height_eq hR
  have hpMem : kvTbl p ∈ kvsL ++ (pk, pv) :: kvsR := by
    rw [hkvP]; exact List.mem_append_right _ List.mem_cons_self
  unfold avlBalanceNodePure
  dsimp only
  rw [hlh_eq, hrh_eq]
  by_cases hLeftHeavy : rh + 1 < lh
  · simp only [decide_eq_true hLeftHeavy, ↓reduceIte]
    have hph : ph = rh + 2 := hPhL hLeftHeavy
    have hlh2 : lh = rh + 2 := by omega
    cases hL with
    | leaf _ => omega
    | @node _ ll lr _ llh lrh lk lv kvsLL kvsLR hl0 hlMax hkvL hshL hLh hLbal1 hLbal2
        hLL hLR hltLL hltLR =>
      have hshL1 : (sh l).1 = ll := by simp [hshL]
      have hshL21 : (sh l).2.1 = lr := by simp [hshL]
      rw [hshL1, hshL21, avlTree_height_eq hLL, avlTree_height_eq hLR]
      have hlk_lt_pk : ltK lk pk :=
        hltL (lk, lv) (List.mem_append_right _ List.mem_cons_self)
      have hl_ne_p : l ≠ p := ne_id_of_lt H hkvL hkvP hlk_lt_pk
      have hlMem : kvTbl l ∈ (kvsLL ++ (lk, lv) :: kvsLR) ++ (pk, pv) :: kvsR := by
        rw [hkvL]; exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      by_cases hLRcase : llh < lrh
      · simp only [decide_eq_true hLRcase, ↓reduceIte]
        have hlrh_eq : lrh = rh + 1 := by omega
        have hllh_eq : llh = rh := by omega
        cases hLR with
        | leaf _ => omega
        | @node _ lrl lrr _ lrlh lrrh lrk lrv kvsLRL kvsLRR hlr0 hlrMax hkvLR hshLR hLRh
            hLRbal1 hLRbal2 hLRL hLRR hltLRL hltLRR =>
          have hshLR1 : (sh lr).1 = lrl := by simp [hshLR]
          have hshLR21 : (sh lr).2.1 = lrr := by simp [hshLR]
          rw [hshLR1, hshLR21, avlTree_height_eq hLRL, avlTree_height_eq hLRR]
          have hlk_lt_lrk : ltK lk lrk :=
            hltLR (lrk, lrv) (List.mem_append_right _ List.mem_cons_self)
          have hlrk_lt_pk : ltK lrk pk :=
            hltL (lrk, lrv) (List.mem_append_right _
              (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))
          have hl_ne_lr : l ≠ lr := ne_id_of_lt H hkvL hkvLR hlk_lt_lrk
          have hp_ne_lr : p ≠ lr := (ne_id_of_lt H hkvLR hkvP hlrk_lt_pk).symm
          have hlrMem : kvTbl lr ∈
              (kvsLL ++ (lk, lv) :: (kvsLRL ++ (lrk, lrv) :: kvsLRR)) ++ (pk, pv) :: kvsR := by
            rw [hkvLR]
            exact List.mem_append_left _ (List.mem_append_right _
              (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))
          let hl' := joinHeightPure llh lrlh
          let hp' := joinHeightPure lrrh rh
          let shA := tsetPure sh l (ll, (lrl, hl'))
          let shB := tsetPure shA p (lrr, (r, hp'))
          let shC := tsetPure shB lr (l, (p, joinHeightPure hl' hp'))
          have hhl' : hl' = max llh lrlh + 1 := joinHeightPure_eq _ _
          have hhp' : hp' = max lrrh rh + 1 := joinHeightPure_eq _ _
          have htop' : joinHeightPure hl' hp' = max hl' hp' + 1 := joinHeightPure_eq _ _
          have hLL_C : AvlTree ltK kvTbl shC maxId ll llh kvsLL := by
            refine avlTree_tset_frame (avlTree_tset_frame (avlTree_tset_frame hLL hl0 ?_) hp0 ?_) hlr0 ?_
            · rw [hkvL]; exact not_mem_of_forall_lt H hltLL
            · rw [hkvP]; exact not_mem_of_forall_lt H (fun kv h => H.trans (hltLL kv h) hlk_lt_pk)
            · rw [hkvLR]; exact not_mem_of_forall_lt H (fun kv h => H.trans (hltLL kv h) hlk_lt_lrk)
          have hLRL_C : AvlTree ltK kvTbl shC maxId lrl lrlh kvsLRL := by
            refine avlTree_tset_frame (avlTree_tset_frame (avlTree_tset_frame hLRL hl0 ?_) hp0 ?_) hlr0 ?_
            · rw [hkvL]; exact not_mem_of_forall_gt H (fun kv h => hltLR kv (List.mem_append_left _ h))
            · rw [hkvP]; exact not_mem_of_forall_lt H (fun kv h => H.trans (hltLRL kv h) hlrk_lt_pk)
            · rw [hkvLR]; exact not_mem_of_forall_lt H hltLRL
          have hLRR_C : AvlTree ltK kvTbl shC maxId lrr lrrh kvsLRR := by
            refine avlTree_tset_frame (avlTree_tset_frame (avlTree_tset_frame hLRR hl0 ?_) hp0 ?_) hlr0 ?_
            · rw [hkvL]; exact not_mem_of_forall_gt H (fun kv h =>
                hltLR kv (List.mem_append_right _ (List.mem_cons_of_mem _ h)))
            · rw [hkvP]; exact not_mem_of_forall_lt H (fun kv h =>
                hltL kv (List.mem_append_right _ (List.mem_cons_of_mem _
                  (List.mem_append_right _ (List.mem_cons_of_mem _ h)))))
            · rw [hkvLR]; exact not_mem_of_forall_gt H hltLRR
          have hR_C : AvlTree ltK kvTbl shC maxId r rh kvsR := by
            refine avlTree_tset_frame (avlTree_tset_frame (avlTree_tset_frame hR hl0 ?_) hp0 ?_) hlr0 ?_
            · rw [hkvL]; exact not_mem_of_forall_gt H (fun kv h => H.trans hlk_lt_pk (hltR kv h))
            · rw [hkvP]; exact not_mem_of_forall_gt H hltR
            · rw [hkvLR]; exact not_mem_of_forall_gt H (fun kv h => H.trans hlrk_lt_pk (hltR kv h))
          have hNodeL : AvlTree ltK kvTbl shC maxId l hl' (kvsLL ++ (lk, lv) :: kvsLRL) := by
            refine .node hl0 hlMax hkvL ?_ hhl' (by omega) (by omega) hLL_C hLRL_C hltLL
              (fun kv h => hltLR kv (List.mem_append_left _ h))
            simp [shC, shB, shA, tsetPure, hl_ne_lr, hl_ne_p]
          have hNodeP : AvlTree ltK kvTbl shC maxId p hp' (kvsLRR ++ (pk, pv) :: kvsR) := by
            refine .node hp0 hpMax hkvP ?_ hhp' (by omega) (by omega) hLRR_C hR_C
              (fun kv h => hltL kv (List.mem_append_right _ (List.mem_cons_of_mem _
                (List.mem_append_right _ (List.mem_cons_of_mem _ h))))) hltR
            simp [shC, shB, tsetPure, hp_ne_lr]
          have hNodeLR : AvlTree ltK kvTbl shC maxId lr (joinHeightPure hl' hp')
              ((kvsLL ++ (lk, lv) :: kvsLRL) ++ (lrk, lrv) :: (kvsLRR ++ (pk, pv) :: kvsR)) := by
            refine .node hlr0 hlrMax hkvLR (by simp [shC, tsetPure]) htop' (by omega) (by omega)
              hNodeL hNodeP ?_ ?_
            · intro kv hmem
              rcases List.mem_append.mp hmem with h1 | h2
              · exact H.trans (hltLL kv h1) hlk_lt_lrk
              · rcases List.mem_cons.mp h2 with rfl | h2'
                · exact hlk_lt_lrk
                · exact hltLRL kv h2'
            · intro kv hmem
              rcases List.mem_append.mp hmem with h1 | h2
              · exact hltLRR kv h1
              · rcases List.mem_cons.mp h2 with rfl | h2'
                · exact hlrk_lt_pk
                · exact H.trans hlrk_lt_pk (hltR kv h2')
          have hListEq :
              (kvsLL ++ (lk, lv) :: kvsLRL) ++ (lrk, lrv) :: (kvsLRR ++ (pk, pv) :: kvsR) =
                (kvsLL ++ (lk, lv) :: (kvsLRL ++ (lrk, lrv) :: kvsLRR)) ++ (pk, pv) :: kvsR := by
            simp [List.append_assoc]
          refine ⟨joinHeightPure hl' hp', by omega, by omega, hListEq ▸ hNodeLR, ?_⟩
          intro u hu
          exact (tsetPure_preserve hlr0 hlrMem hu).trans
            ((tsetPure_preserve hp0 hpMem hu).trans (tsetPure_preserve hl0 hlMem hu))
      · simp only [decide_eq_false hLRcase, Bool.false_eq_true, ↓reduceIte]
        let hp' := joinHeightPure lrh rh
        let shA := tsetPure sh p (lr, (r, hp'))
        let shB := tsetPure shA l (ll, (p, joinHeightPure llh hp'))
        have hhp' : hp' = max lrh rh + 1 := joinHeightPure_eq _ _
        have htop' : joinHeightPure llh hp' = max llh hp' + 1 := joinHeightPure_eq _ _
        have hLL_B : AvlTree ltK kvTbl shB maxId ll llh kvsLL := by
          refine avlTree_tset_frame (avlTree_tset_frame hLL hp0 ?_) hl0 ?_
          · rw [hkvP]; exact not_mem_of_forall_lt H (fun kv h => H.trans (hltLL kv h) hlk_lt_pk)
          · rw [hkvL]; exact not_mem_of_forall_lt H hltLL
        have hLR_B : AvlTree ltK kvTbl shB maxId lr lrh kvsLR := by
          refine avlTree_tset_frame (avlTree_tset_frame hLR hp0 ?_) hl0 ?_
          · rw [hkvP]; exact not_mem_of_forall_lt H
              (fun kv h => hltL kv (List.mem_append_right _ (List.mem_cons_of_mem _ h)))
          · rw [hkvL]; exact not_mem_of_forall_gt H hltLR
        have hR_B : AvlTree ltK kvTbl shB maxId r rh kvsR := by
          refine avlTree_tset_frame (avlTree_tset_frame hR hp0 ?_) hl0 ?_
          · rw [hkvP]; exact not_mem_of_forall_gt H hltR
          · rw [hkvL]; exact not_mem_of_forall_gt H (fun kv h => H.trans hlk_lt_pk (hltR kv h))
        have hNodeP : AvlTree ltK kvTbl shB maxId p hp' (kvsLR ++ (pk, pv) :: kvsR) := by
          refine .node hp0 hpMax hkvP ?_ hhp' (by omega) (by omega) hLR_B hR_B
            (fun kv h => hltL kv (List.mem_append_right _ (List.mem_cons_of_mem _ h))) hltR
          simp [shB, shA, tsetPure, Ne.symm hl_ne_p]
        have hNodeL : AvlTree ltK kvTbl shB maxId l (joinHeightPure llh hp')
            (kvsLL ++ (lk, lv) :: (kvsLR ++ (pk, pv) :: kvsR)) := by
          refine .node hl0 hlMax hkvL (by simp [shB, tsetPure]) htop' (by omega) (by omega)
            hLL_B hNodeP hltLL ?_
          intro kv hmem
          rcases List.mem_append.mp hmem with h1 | h2
          · exact hltLR kv h1
          · rcases List.mem_cons.mp h2 with rfl | h2'
            · exact hlk_lt_pk
            · exact H.trans hlk_lt_pk (hltR kv h2')
        have hListEq :
            kvsLL ++ (lk, lv) :: (kvsLR ++ (pk, pv) :: kvsR) =
              (kvsLL ++ (lk, lv) :: kvsLR) ++ (pk, pv) :: kvsR := by
          simp [List.append_assoc]
        refine ⟨joinHeightPure llh hp', by omega, by omega, hListEq ▸ hNodeL, ?_⟩
        intro u hu
        exact (tsetPure_preserve hl0 hlMem hu).trans (tsetPure_preserve hp0 hpMem hu)
  · simp only [decide_eq_false hLeftHeavy, Bool.false_eq_true, ↓reduceIte]
    by_cases hRightHeavy : lh + 1 < rh
    · simp only [decide_eq_true hRightHeavy, ↓reduceIte]
      have hph : ph = lh + 2 := hPhR hRightHeavy
      have hrh2 : rh = lh + 2 := by omega
      cases hR with
      | leaf _ => omega
      | @node _ rl rr _ rlh rrh rk rv kvsRL kvsRR hr0 hrMax hkvR hshR hRh hRbal1 hRbal2
          hRL hRR hltRL hltRR =>
        have hshR1 : (sh r).1 = rl := by simp [hshR]
        have hshR21 : (sh r).2.1 = rr := by simp [hshR]
        rw [hshR1, hshR21, avlTree_height_eq hRL, avlTree_height_eq hRR]
        have hpk_lt_rk : ltK pk rk :=
          hltR (rk, rv) (List.mem_append_right _ List.mem_cons_self)
        have hp_ne_r : p ≠ r := ne_id_of_lt H hkvP hkvR hpk_lt_rk
        have hrMem : kvTbl r ∈ kvsL ++ (pk, pv) :: (kvsRL ++ (rk, rv) :: kvsRR) := by
          rw [hkvR]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
        by_cases hRLcase : rrh < rlh
        · simp only [decide_eq_true hRLcase, ↓reduceIte]
          have hrlh_eq : rlh = lh + 1 := by omega
          have hrrh_eq : rrh = lh := by omega
          cases hRL with
          | leaf _ => omega
          | @node _ rll rlr _ rllh rlrh rlk rlv kvsRLL kvsRLR hrl0 hrlMax hkvRL hshRL hRLh
              hRLbal1 hRLbal2 hRLL hRLR hltRLL hltRLR =>
            have hshRL1 : (sh rl).1 = rll := by simp [hshRL]
            have hshRL21 : (sh rl).2.1 = rlr := by simp [hshRL]
            rw [hshRL1, hshRL21, avlTree_height_eq hRLL, avlTree_height_eq hRLR]
            have hpk_lt_rlk : ltK pk rlk :=
              hltR (rlk, rlv) (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
            have hrlk_lt_rk : ltK rlk rk :=
              hltRL (rlk, rlv) (List.mem_append_right _ List.mem_cons_self)
            have hp_ne_rl : p ≠ rl := ne_id_of_lt H hkvP hkvRL hpk_lt_rlk
            have hr_ne_rl : r ≠ rl := (ne_id_of_lt H hkvRL hkvR hrlk_lt_rk).symm
            have hrlMem : kvTbl rl ∈
                kvsL ++ (pk, pv) :: ((kvsRLL ++ (rlk, rlv) :: kvsRLR) ++ (rk, rv) :: kvsRR) := by
              rw [hkvRL]
              exact List.mem_append_right _ (List.mem_cons_of_mem _
                (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)))
            let hp' := joinHeightPure lh rllh
            let hr' := joinHeightPure rlrh rrh
            let shA := tsetPure sh p (l, (rll, hp'))
            let shB := tsetPure shA r (rlr, (rr, hr'))
            let shC := tsetPure shB rl (p, (r, joinHeightPure hp' hr'))
            have hhp' : hp' = max lh rllh + 1 := joinHeightPure_eq _ _
            have hhr' : hr' = max rlrh rrh + 1 := joinHeightPure_eq _ _
            have htop' : joinHeightPure hp' hr' = max hp' hr' + 1 := joinHeightPure_eq _ _
            have hL_C : AvlTree ltK kvTbl shC maxId l lh kvsL := by
              refine avlTree_tset_frame (avlTree_tset_frame (avlTree_tset_frame hL hp0 ?_) hr0 ?_) hrl0 ?_
              · rw [hkvP]; exact not_mem_of_forall_lt H hltL
              · rw [hkvR]; exact not_mem_of_forall_lt H (fun kv h => H.trans (hltL kv h) hpk_lt_rk)
              · rw [hkvRL]; exact not_mem_of_forall_lt H (fun kv h => H.trans (hltL kv h) hpk_lt_rlk)
            have hRLL_C : AvlTree ltK kvTbl shC maxId rll rllh kvsRLL := by
              refine avlTree_tset_frame (avlTree_tset_frame (avlTree_tset_frame hRLL hp0 ?_) hr0 ?_) hrl0 ?_
              · rw [hkvP]; exact not_mem_of_forall_gt H
                  (fun kv h => hltR kv (List.mem_append_left _ (List.mem_append_left _ h)))
              · rw [hkvR]; exact not_mem_of_forall_lt H (fun kv h => H.trans (hltRLL kv h) hrlk_lt_rk)
              · rw [hkvRL]; exact not_mem_of_forall_lt H hltRLL
            have hRLR_C : AvlTree ltK kvTbl shC maxId rlr rlrh kvsRLR := by
              refine avlTree_tset_frame (avlTree_tset_frame (avlTree_tset_frame hRLR hp0 ?_) hr0 ?_) hrl0 ?_
              · rw [hkvP]; exact not_mem_of_forall_gt H (fun kv h =>
                  hltR kv (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ h))))
              · rw [hkvR]; exact not_mem_of_forall_lt H (fun kv h =>
                  hltRL kv (List.mem_append_right _ (List.mem_cons_of_mem _ h)))
              · rw [hkvRL]; exact not_mem_of_forall_gt H hltRLR
            have hRR_C : AvlTree ltK kvTbl shC maxId rr rrh kvsRR := by
              refine avlTree_tset_frame (avlTree_tset_frame (avlTree_tset_frame hRR hp0 ?_) hr0 ?_) hrl0 ?_
              · rw [hkvP]; exact not_mem_of_forall_gt H (fun kv h => H.trans hpk_lt_rk (hltRR kv h))
              · rw [hkvR]; exact not_mem_of_forall_gt H hltRR
              · rw [hkvRL]; exact not_mem_of_forall_gt H (fun kv h => H.trans hrlk_lt_rk (hltRR kv h))
            have hNodeP : AvlTree ltK kvTbl shC maxId p hp' (kvsL ++ (pk, pv) :: kvsRLL) := by
              refine .node hp0 hpMax hkvP ?_ hhp' (by omega) (by omega) hL_C hRLL_C hltL
                (fun kv h => hltR kv (List.mem_append_left _ (List.mem_append_left _ h)))
              simp [shC, shB, shA, tsetPure, hp_ne_rl, hp_ne_r]
            have hNodeR : AvlTree ltK kvTbl shC maxId r hr' (kvsRLR ++ (rk, rv) :: kvsRR) := by
              refine .node hr0 hrMax hkvR ?_ hhr' (by omega) (by omega) hRLR_C hRR_C
                (fun kv h => hltRL kv (List.mem_append_right _ (List.mem_cons_of_mem _ h))) hltRR
              simp [shC, shB, tsetPure, hr_ne_rl]
            have hNodeRL : AvlTree ltK kvTbl shC maxId rl (joinHeightPure hp' hr')
                ((kvsL ++ (pk, pv) :: kvsRLL) ++ (rlk, rlv) :: (kvsRLR ++ (rk, rv) :: kvsRR)) := by
              refine .node hrl0 hrlMax hkvRL (by simp [shC, tsetPure]) htop' (by omega) (by omega)
                hNodeP hNodeR ?_ ?_
              · intro kv hmem
                rcases List.mem_append.mp hmem with h1 | h2
                · exact H.trans (hltL kv h1) hpk_lt_rlk
                · rcases List.mem_cons.mp h2 with rfl | h2'
                  · exact hpk_lt_rlk
                  · exact hltRLL kv h2'
              · intro kv hmem
                rcases List.mem_append.mp hmem with h1 | h2
                · exact hltRLR kv h1
                · rcases List.mem_cons.mp h2 with rfl | h2'
                  · exact hrlk_lt_rk
                  · exact H.trans hrlk_lt_rk (hltRR kv h2')
            have hListEq :
                (kvsL ++ (pk, pv) :: kvsRLL) ++ (rlk, rlv) :: (kvsRLR ++ (rk, rv) :: kvsRR) =
                  kvsL ++ (pk, pv) :: ((kvsRLL ++ (rlk, rlv) :: kvsRLR) ++ (rk, rv) :: kvsRR) := by
              simp [List.append_assoc]
            refine ⟨joinHeightPure hp' hr', by omega, by omega, hListEq ▸ hNodeRL, ?_⟩
            intro u hu
            exact (tsetPure_preserve hrl0 hrlMem hu).trans
              ((tsetPure_preserve hr0 hrMem hu).trans (tsetPure_preserve hp0 hpMem hu))
        · simp only [decide_eq_false hRLcase, Bool.false_eq_true, ↓reduceIte]
          let hp' := joinHeightPure lh rlh
          let shA := tsetPure sh p (l, (rl, hp'))
          let shB := tsetPure shA r (p, (rr, joinHeightPure hp' rrh))
          have hhp' : hp' = max lh rlh + 1 := joinHeightPure_eq _ _
          have htop' : joinHeightPure hp' rrh = max hp' rrh + 1 := joinHeightPure_eq _ _
          have hL_B : AvlTree ltK kvTbl shB maxId l lh kvsL := by
            refine avlTree_tset_frame (avlTree_tset_frame hL hp0 ?_) hr0 ?_
            · rw [hkvP]; exact not_mem_of_forall_lt H hltL
            · rw [hkvR]; exact not_mem_of_forall_lt H (fun kv h => H.trans (hltL kv h) hpk_lt_rk)
          have hRL_B : AvlTree ltK kvTbl shB maxId rl rlh kvsRL := by
            refine avlTree_tset_frame (avlTree_tset_frame hRL hp0 ?_) hr0 ?_
            · rw [hkvP]; exact not_mem_of_forall_gt H (fun kv h => hltR kv (List.mem_append_left _ h))
            · rw [hkvR]; exact not_mem_of_forall_lt H hltRL
          have hRR_B : AvlTree ltK kvTbl shB maxId rr rrh kvsRR := by
            refine avlTree_tset_frame (avlTree_tset_frame hRR hp0 ?_) hr0 ?_
            · rw [hkvP]; exact not_mem_of_forall_gt H (fun kv h => H.trans hpk_lt_rk (hltRR kv h))
            · rw [hkvR]; exact not_mem_of_forall_gt H hltRR
          have hNodeP : AvlTree ltK kvTbl shB maxId p hp' (kvsL ++ (pk, pv) :: kvsRL) := by
            refine .node hp0 hpMax hkvP ?_ hhp' (by omega) (by omega) hL_B hRL_B
              hltL (fun kv h => hltR kv (List.mem_append_left _ h))
            simp [shB, shA, tsetPure, hp_ne_r]
          have hNodeR : AvlTree ltK kvTbl shB maxId r (joinHeightPure hp' rrh)
              ((kvsL ++ (pk, pv) :: kvsRL) ++ (rk, rv) :: kvsRR) := by
            refine .node hr0 hrMax hkvR (by simp [shB, tsetPure]) htop' (by omega) (by omega)
              hNodeP hRR_B ?_ hltRR
            intro kv hmem
            rcases List.mem_append.mp hmem with h1 | h2
            · exact H.trans (hltL kv h1) hpk_lt_rk
            · rcases List.mem_cons.mp h2 with rfl | h2'
              · exact hpk_lt_rk
              · exact hltRL kv h2'
          have hListEq :
              (kvsL ++ (pk, pv) :: kvsRL) ++ (rk, rv) :: kvsRR =
                kvsL ++ (pk, pv) :: (kvsRL ++ (rk, rv) :: kvsRR) := by
            simp [List.append_assoc]
          refine ⟨joinHeightPure hp' rrh, by omega, by omega, hListEq ▸ hNodeR, ?_⟩
          intro u hu
          exact (tsetPure_preserve hr0 hrMem hu).trans (tsetPure_preserve hp0 hpMem hu)
    · simp only [decide_eq_false hRightHeavy, Bool.false_eq_true, ↓reduceIte]
      have hbal1 : lh ≤ rh + 1 := by omega
      have hbal2 : rh ≤ lh + 1 := by omega
      obtain ⟨hPh1, hPh2⟩ := hPhBal hbal1 hbal2
      let shA := tsetPure sh p (l, (r, joinHeightPure lh rh))
      have htop' : joinHeightPure lh rh = max lh rh + 1 := joinHeightPure_eq _ _
      have hL_A : AvlTree ltK kvTbl shA maxId l lh kvsL := by
        refine avlTree_tset_frame hL hp0 ?_
        rw [hkvP]; exact not_mem_of_forall_lt H hltL
      have hR_A : AvlTree ltK kvTbl shA maxId r rh kvsR := by
        refine avlTree_tset_frame hR hp0 ?_
        rw [hkvP]; exact not_mem_of_forall_gt H hltR
      have hNodeP : AvlTree ltK kvTbl shA maxId p (joinHeightPure lh rh)
          (kvsL ++ (pk, pv) :: kvsR) :=
        .node hp0 hpMax hkvP (by simp [shA, tsetPure]) htop' hbal1 hbal2 hL_A hR_A hltL hltR
      refine ⟨joinHeightPure lh rh, by omega, by omega, hNodeP, ?_⟩
      intro u hu
      exact tsetPure_preserve hp0 hpMem hu

inductive AvlZipper {K V : Type} (ltK : K → K → Prop)
    (kvTbl : ℕ → K × V) (shapeTbl : ℕ → ℕ × (ℕ × ℕ)) (maxId : ℕ) :
    List (K × V) → List (K × V) →
    ℕ → ℕ → List (K × V) →
    List (ℕ × Bool) →
    ℕ → ℕ → List (K × V) → Prop
  | nil {id h kvs} :
      AvlZipper ltK kvTbl shapeTbl maxId [] [] id h kvs [] id h kvs
  | left {lCtx rCtx subId subH subKvs p r ph rh pk pv kvsR path topId topH topKvs} :
      0 < p → p ≤ maxId →
      kvTbl p = (pk, pv) →
      shapeTbl p = (subId, (r, ph)) →
      ph = max subH rh + 1 →
      subH ≤ rh + 1 → rh ≤ subH + 1 →
      AvlTree ltK kvTbl shapeTbl maxId r rh kvsR →
      (∀ kv ∈ subKvs, ltK kv.1 pk) →
      (∀ kv ∈ kvsR, ltK pk kv.1) →
      AvlZipper ltK kvTbl shapeTbl maxId lCtx rCtx
        p ph (subKvs ++ (pk, pv) :: kvsR) path topId topH topKvs →
      AvlZipper ltK kvTbl shapeTbl maxId lCtx (((pk, pv) :: kvsR) ++ rCtx)
        subId subH subKvs ((p, true) :: path) topId topH topKvs
  | right {lCtx rCtx subId subH subKvs p l ph lh pk pv kvsL path topId topH topKvs} :
      0 < p → p ≤ maxId →
      kvTbl p = (pk, pv) →
      shapeTbl p = (l, (subId, ph)) →
      ph = max lh subH + 1 →
      lh ≤ subH + 1 → subH ≤ lh + 1 →
      AvlTree ltK kvTbl shapeTbl maxId l lh kvsL →
      (∀ kv ∈ kvsL, ltK kv.1 pk) →
      (∀ kv ∈ subKvs, ltK pk kv.1) →
      AvlZipper ltK kvTbl shapeTbl maxId lCtx rCtx
        p ph (kvsL ++ (pk, pv) :: subKvs) path topId topH topKvs →
      AvlZipper ltK kvTbl shapeTbl maxId (lCtx ++ kvsL ++ [(pk, pv)]) rCtx
        subId subH subKvs ((p, false) :: path) topId topH topKvs

theorem avlZipper_decomp {K V : Type} {ltK : K → K → Prop}
    {kvTbl : ℕ → K × V} {shapeTbl : ℕ → ℕ × (ℕ × ℕ)} {maxId : ℕ}
    {lCtx rCtx : List (K × V)} {subId subH : ℕ} {subKvs : List (K × V)}
    {path : List (ℕ × Bool)} {topId topH : ℕ} {topKvs : List (K × V)}
    (hz : AvlZipper ltK kvTbl shapeTbl maxId lCtx rCtx subId subH subKvs path topId topH topKvs) :
    topKvs = lCtx ++ subKvs ++ rCtx := by
  induction hz with
  | nil => simp
  | left _ _ _ _ _ _ _ _ _ _ _ ih => simp [ih, List.append_assoc]
  | right _ _ _ _ _ _ _ _ _ _ _ ih => simp [ih, List.append_assoc]

theorem avlZipper_congr {K V : Type} {ltK : K → K → Prop}
    {kvTbl kvTbl' : ℕ → K × V} {shapeTbl shapeTbl' : ℕ → ℕ × (ℕ × ℕ)}
    {maxId maxId' : ℕ} {lCtx rCtx : List (K × V)}
    {subId subH : ℕ} {subKvs : List (K × V)}
    {path : List (ℕ × Bool)} {topId topH : ℕ} {topKvs : List (K × V)}
    (hz : AvlZipper ltK kvTbl shapeTbl maxId lCtx rCtx subId subH subKvs path topId topH topKvs)
    (hMax : maxId ≤ maxId')
    (hZero : shapeTbl' 0 = (0, (0, 0)))
    (hEq : ∀ u, 0 < u → u ≤ maxId → kvTbl u ∈ lCtx ++ rCtx →
      kvTbl' u = kvTbl u ∧ shapeTbl' u = shapeTbl u) :
    AvlZipper ltK kvTbl' shapeTbl' maxId' lCtx rCtx subId subH subKvs path topId topH topKvs := by
  induction hz with
  | nil => exact .nil
  | @left lCtx rCtx subId subH subKvs p r ph rh pk pv kvsR path topId topH topKvs
      hp0 hpMax hkvP hshP hph hb1 hb2 hR hltSub hltR _ ih =>
    have hpMem : kvTbl p ∈ lCtx ++ (((pk, pv) :: kvsR) ++ rCtx) := by
      rw [hkvP]; exact List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)
    obtain ⟨hkvP', hshP'⟩ := hEq p hp0 hpMax hpMem
    refine .left hp0 (Nat.le_trans hpMax hMax) (hkvP'.trans hkvP) (hshP'.trans hshP)
      hph hb1 hb2 (avlTree_congr hR hMax hZero ?_) hltSub hltR (ih ?_)
    · intro u hu0 huM hm
      exact hEq u hu0 huM
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_cons_of_mem _ hm)))
    · intro u hu0 huM hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact hEq u hu0 huM (List.mem_append_left _ h1)
      · exact hEq u hu0 huM (List.mem_append_right _ (List.mem_append_right _ h2))
  | @right lCtx rCtx subId subH subKvs p l ph lh pk pv kvsL path topId topH topKvs
      hp0 hpMax hkvP hshP hph hb1 hb2 hL hltL hltSub _ ih =>
    have hpMem : kvTbl p ∈ (lCtx ++ kvsL ++ [(pk, pv)]) ++ rCtx := by
      rw [hkvP]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    obtain ⟨hkvP', hshP'⟩ := hEq p hp0 hpMax hpMem
    refine .right hp0 (Nat.le_trans hpMax hMax) (hkvP'.trans hkvP) (hshP'.trans hshP)
      hph hb1 hb2 (avlTree_congr hL hMax hZero ?_) hltL hltSub (ih ?_)
    · intro u hu0 huM hm
      exact hEq u hu0 huM
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm)))
    · intro u hu0 huM hm
      rcases List.mem_append.mp hm with h1 | h2
      · exact hEq u hu0 huM
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h1)))
      · exact hEq u hu0 huM (List.mem_append_right _ h2)

theorem pairwise_mid_lt {K V : Type} {ltK : K → K → Prop}
    {A B C : List (K × V)}
    (hpw : (A ++ B ++ C).Pairwise (fun x y => ltK x.1 y.1)) :
    (∀ a ∈ A, ∀ b ∈ B, ltK a.1 b.1) ∧ (∀ b ∈ B, ∀ c ∈ C, ltK b.1 c.1) := by
  rw [List.pairwise_append] at hpw
  obtain ⟨hpwAB, _, hABC⟩ := hpw
  rw [List.pairwise_append] at hpwAB
  exact ⟨hpwAB.2.2, fun b hb c hc => hABC b (List.mem_append_right _ hb) c hc⟩

theorem avlFoldRebalance_spec {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK)
    {kvTbl : ℕ → K × V} {maxId topId topH : ℕ} {topKvs : List (K × V)}
    (hpw : topKvs.Pairwise (fun x y => ltK x.1 y.1)) :
    ∀ (path : List (ℕ × Bool)) {sh : ℕ → ℕ × (ℕ × ℕ)}
      {lCtx rCtx : List (K × V)} {subId subH : ℕ} {subKvs : List (K × V)}
      {cId cH : ℕ} {cKvs : List (K × V)},
      AvlZipper ltK kvTbl sh maxId lCtx rCtx subId subH subKvs path topId topH topKvs →
      AvlTree ltK kvTbl sh maxId cId cH cKvs →
      subH ≤ cH → cH ≤ subH + 1 →
      (∀ a ∈ lCtx, ∀ b ∈ cKvs, ltK a.1 b.1) →
      (∀ b ∈ cKvs, ∀ a ∈ rCtx, ltK b.1 a.1) →
      let res := path.foldl (fun acc x => avlRebalanceStepPure x acc) (cId, sh)
      ∃ h', AvlTree ltK kvTbl res.2 maxId res.1 h' (lCtx ++ cKvs ++ rCtx)
  | [], sh, lCtx, rCtx, subId, subH, subKvs, cId, cH, cKvs, hz, hSub, _, _, _, _ => by
    cases hz
    exact ⟨cH, by simpa using hSub⟩
  | (p, true) :: path, sh, lCtx, _, subId, subH, subKvs, cId, cH, cKvs,
      hz, hSub, hH1, hH2, hLtL, hLtR => by
    cases hz with
    | @left _ rCtx _ _ _ _ r ph rh pk pv kvsR _ _ _ _
        hp0 hpMax hkvP hshP hph hb1 hb2 hR hltSub hltR hzOuter =>
      dsimp only
      rw [List.foldl_cons, avlRebalanceStepPure_true, hshP]
      have hltC_pk : ∀ kv ∈ cKvs, ltK kv.1 pk :=
        fun kv hkv => hLtR kv hkv (pk, pv) (List.mem_append_left _ List.mem_cons_self)
      obtain ⟨pH', hpH1, hpH2, hNode', hFrame⟩ :=
        avlBalanceNodePure_spec H (ph := ph) hp0 hpMax hkvP hSub hR hltC_pk hltR
          (by omega) (by omega) (by omega) (by omega) (by omega)
      have hDecomp := avlZipper_decomp hzOuter
      have ⟨hA_mid, hMid_C⟩ := pairwise_mid_lt (hDecomp ▸ hpw)
      have hLtL' : ∀ a ∈ lCtx, ∀ b ∈ cKvs ++ (pk, pv) :: kvsR, ltK a.1 b.1 := by
        intro a ha b hb
        rcases List.mem_append.mp hb with hb1 | hb2
        · exact hLtL a ha b hb1
        · exact hA_mid a ha b (List.mem_append_right _ hb2)
      have hLtR' : ∀ b ∈ cKvs ++ (pk, pv) :: kvsR, ∀ a ∈ rCtx, ltK b.1 a.1 := by
        intro b hb a ha
        rcases List.mem_append.mp hb with hb1 | hb2
        · exact hLtR b hb1 a (List.mem_append_right _ ha)
        · exact hMid_C b (List.mem_append_right _ hb2) a ha
      have hzOuter' : AvlZipper ltK kvTbl (avlBalanceNodePure p cId r sh).2 maxId
          lCtx rCtx p ph (subKvs ++ (pk, pv) :: kvsR) path topId topH topKvs := by
        refine avlZipper_congr hzOuter (Nat.le_refl _) (avlTree_shapeTbl_zero hNode') ?_
        intro u _ _ hmem
        refine ⟨rfl, hFrame u (Or.inr fun hbad => ?_)⟩
        rcases List.mem_append.mp hmem with h1 | h2
        · exact H.irrefl (kvTbl u).1 (hLtL' _ h1 _ hbad)
        · exact H.irrefl (kvTbl u).1 (hLtR' _ hbad _ h2)
      obtain ⟨hFinal, hTreeFinal⟩ :=
        avlFoldRebalance_spec H hpw path hzOuter' hNode' hpH1 hpH2 hLtL' hLtR'
      exact ⟨hFinal, by simpa [List.append_assoc] using hTreeFinal⟩
  | (p, false) :: path, sh, _, rCtx, subId, subH, subKvs, cId, cH, cKvs,
      hz, hSub, hH1, hH2, hLtL, hLtR => by
    cases hz with
    | @right lCtx _ _ _ _ _ l ph lh pk pv kvsL _ _ _ _
        hp0 hpMax hkvP hshP hph hb1 hb2 hL hltL hltSub hzOuter =>
      dsimp only
      rw [List.foldl_cons, avlRebalanceStepPure_false, hshP]
      have hlt_pk_C : ∀ kv ∈ cKvs, ltK pk kv.1 :=
        fun kv hkv => hLtL (pk, pv) (List.mem_append_right _ List.mem_cons_self) kv hkv
      obtain ⟨pH', hpH1, hpH2, hNode', hFrame⟩ :=
        avlBalanceNodePure_spec H (ph := ph) hp0 hpMax hkvP hL hSub hltL hlt_pk_C
          (by omega) (by omega) (by omega) (by omega) (by omega)
      have hDecomp := avlZipper_decomp hzOuter
      have ⟨hA_mid, hMid_C⟩ := pairwise_mid_lt (hDecomp ▸ hpw)
      have hLtL' : ∀ a ∈ lCtx, ∀ b ∈ kvsL ++ (pk, pv) :: cKvs, ltK a.1 b.1 := by
        intro a ha b hb
        rcases List.mem_append.mp hb with hb1 | hb2
        · exact hA_mid a ha b (List.mem_append_left _ hb1)
        · rcases List.mem_cons.mp hb2 with rfl | hb3
          · exact hA_mid a ha (pk, pv) (List.mem_append_right _ List.mem_cons_self)
          · exact hLtL a (List.mem_append_left _ (List.mem_append_left _ ha)) b hb3
      have hLtR' : ∀ b ∈ kvsL ++ (pk, pv) :: cKvs, ∀ a ∈ rCtx, ltK b.1 a.1 := by
        intro b hb a ha
        rcases List.mem_append.mp hb with hb1 | hb2
        · exact hMid_C b (List.mem_append_left _ hb1) a ha
        · rcases List.mem_cons.mp hb2 with rfl | hb3
          · exact hMid_C (pk, pv) (List.mem_append_right _ List.mem_cons_self) a ha
          · exact hLtR b hb3 a ha
      have hzOuter' : AvlZipper ltK kvTbl (avlBalanceNodePure p l cId sh).2 maxId
          lCtx rCtx p ph (kvsL ++ (pk, pv) :: subKvs) path topId topH topKvs := by
        refine avlZipper_congr hzOuter (Nat.le_refl _) (avlTree_shapeTbl_zero hNode') ?_
        intro u _ _ hmem
        refine ⟨rfl, hFrame u (Or.inr fun hbad => ?_)⟩
        rcases List.mem_append.mp hmem with h1 | h2
        · exact H.irrefl (kvTbl u).1 (hLtL' _ h1 _ hbad)
        · exact H.irrefl (kvTbl u).1 (hLtR' _ hbad _ h2)
      obtain ⟨hFinal, hTreeFinal⟩ :=
        avlFoldRebalance_spec H hpw path hzOuter' hNode' hpH1 hpH2 hLtL' hLtR'
      exact ⟨hFinal, by simpa [List.append_assoc] using hTreeFinal⟩

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableBalance
