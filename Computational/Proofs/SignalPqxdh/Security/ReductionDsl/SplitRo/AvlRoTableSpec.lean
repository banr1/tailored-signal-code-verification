/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableBalance

/-!
# Functional Correctness of the AVL Random-Oracle Cache

**Checked by Lean.** Proves strict linear ordering of `LibsignalSpqrV1.bytesLt` and injectivity of
`E2E.ofU8` on arbitrary-length byte strings, defines the table invariants `AvlB192Valid` and
`AvlPair32Valid`, and proves search equivalence and miss-insert invariant preservation
(`avlSearchInsertB192_spec`, `avlSearchInsertPair32_spec`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec

open OracleSpec OracleComp
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface
  pqAtomicSig pqAtomicOps
  AtomicPureOp atomicPureOps
  B
  iterM foldML
)
open _root_.SignalPqxdh (Bytes)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlShapeTy avlPathItemTy avlSearchResTy avlTy avlHeightCap avlLoopAccTy
  aop avlRootE avlCountE avlKvE avlShapeE avlMkE
  avlEmptyE dfltB192E dfltPair32E mkShapeNodeE orBoolE avlRebalanceStepE
  avlSearchB192C avlSearchPair32C avlInsertAtPathC
  AvlTree
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableBalance (
  StrictLinOrder avlTree_kvs_pairwise avlTree_height_lt_avlHeightCap avlTree_shapeTbl_zero
  tsetPure tsetPure_self tsetPure_ne avlRebalanceStepPure avlRebalanceStepE_eval
  AvlZipper avlZipper_decomp avlZipper_congr pairwise_mid_lt avlFoldRebalance_spec
)

/-- Representation invariant relating a `B 192` AVL table `t` of capacity `cap` to an association
    list `entries`. -/
@[expose] def AvlB192Valid {V : Ty pqAtomicSig} (cap : ℕ)
    (t : (avlTy (B 192) V).denote)
    (entries : List (Bytes × V.denote)) : Prop :=
  entries.length ≤ cap ∧
  t.2.1 = entries.length ∧
  ∃ h kvs,
    AvlTree (fun a b => CryptoVerification.LibsignalSpqrV1.bytesLt a b = true)
      t.2.2.1 t.2.2.2 t.2.1 t.1 h kvs ∧
    ∀ sec : Bytes,
      (kvs.find? (fun p => p.1 == CryptoVerification.E2E.ofU8 sec)).map Prod.snd =
        (entries.find? (fun p => p.1 == sec)).map Prod.snd

/-- Lexicographic strict order on `(List (BitVec 8) × List (BitVec 8))` matching `avlSearchPair32C`. -/
@[expose] def pair32Lt (a b : List (BitVec 8) × List (BitVec 8)) : Prop :=
  CryptoVerification.LibsignalSpqrV1.bytesLt a.1 b.1 = true ∨
    (a.1 = b.1 ∧ CryptoVerification.LibsignalSpqrV1.bytesLt a.2 b.2 = true)

/-- Representation invariant relating a `(B 32 × B 32)` AVL table `t` of capacity `cap` to an
    association list `entries`. -/
@[expose] def AvlPair32Valid {V : Ty pqAtomicSig} (cap : ℕ)
    (t : (avlTy (.prod (B 32) (B 32)) V).denote)
    (entries : List ((Bytes × Bytes) × V.denote)) : Prop :=
  entries.length ≤ cap ∧
  t.2.1 = entries.length ∧
  ∃ h kvs,
    AvlTree pair32Lt t.2.2.1 t.2.2.2 t.2.1 t.1 h kvs ∧
    ∀ rk dh : Bytes,
      (kvs.find? (fun p =>
          p.1.1 == CryptoVerification.E2E.ofU8 rk &&
            p.1.2 == CryptoVerification.E2E.ofU8 dh)).map Prod.snd =
        (entries.find? (fun p => p.1.1 == rk && p.1.2 == dh)).map Prod.snd

theorem avlEmptyE_b192_valid {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (cap : ℕ) (dfltV : Expr pqAtomicOps Γ V) (ρ : Env Γ) :
    AvlB192Valid cap ((avlEmptyE dfltB192E dfltV).eval ρ) [] := by
  refine ⟨Nat.zero_le _, rfl, 0, [], .leaf rfl, fun _ => rfl⟩

theorem avlEmptyE_pair32_valid {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (cap : ℕ) (dfltV : Expr pqAtomicOps Γ V) (ρ : Env Γ) :
    AvlPair32Valid cap ((avlEmptyE dfltPair32E dfltV).eval ρ) [] := by
  refine ⟨Nat.zero_le _, rfl, 0, [], .leaf rfl, fun _ _ => rfl⟩

theorem bytesLt_irrefl :
    ∀ (a : List (BitVec 8)), ¬ (CryptoVerification.LibsignalSpqrV1.bytesLt a a = true)
  | [] => by simp [CryptoVerification.LibsignalSpqrV1.bytesLt]
  | x :: xs => by
    simp only [CryptoVerification.LibsignalSpqrV1.bytesLt]
    have hx : ¬ (x < x) := BitVec.lt_irrefl x
    simp [hx, bytesLt_irrefl xs]

theorem bytesLt_trans :
    ∀ {a b c : List (BitVec 8)},
      CryptoVerification.LibsignalSpqrV1.bytesLt a b = true →
      CryptoVerification.LibsignalSpqrV1.bytesLt b c = true →
      CryptoVerification.LibsignalSpqrV1.bytesLt a c = true
  | [], [], _, hab, _ => by simp [CryptoVerification.LibsignalSpqrV1.bytesLt] at hab
  | [], _ :: _, [], _, hbc => by simp [CryptoVerification.LibsignalSpqrV1.bytesLt] at hbc
  | [], _ :: _, _ :: _, _, _ => by simp [CryptoVerification.LibsignalSpqrV1.bytesLt]
  | _ :: _, [], _, hab, _ => by simp [CryptoVerification.LibsignalSpqrV1.bytesLt] at hab
  | _ :: _, _ :: _, [], _, hbc => by simp [CryptoVerification.LibsignalSpqrV1.bytesLt] at hbc
  | x :: xs, y :: ys, z :: zs, hab, hbc => by
    simp only [CryptoVerification.LibsignalSpqrV1.bytesLt] at hab hbc ⊢
    by_cases hxy : x < y
    · simp only [hxy, ↓reduceIte] at hab
      by_cases hyz : y < z
      · have hxz : x < z := BitVec.lt_trans hxy hyz
        simp [hxz]
      · by_cases hzy : z < y
        · simp [hyz, hzy] at hbc
        · have hyzeq : y = z := BitVec.le_antisymm (BitVec.not_lt.mp hzy) (BitVec.not_lt.mp hyz)
          subst hyzeq
          simp [hxy]
    · by_cases hyx : y < x
      · simp [hxy, hyx] at hab
      · have hxyeq : x = y := BitVec.le_antisymm (BitVec.not_lt.mp hyx) (BitVec.not_lt.mp hxy)
        subst hxyeq
        simp only [BitVec.lt_irrefl, ↓reduceIte] at hab ⊢
        by_cases hyz : x < z
        · simp [hyz]
        · by_cases hzy : z < x
          · simp [hyz, hzy] at hbc ⊢
          · simp only [hyz, hzy, ↓reduceIte] at hbc ⊢
            exact bytesLt_trans hab hbc

theorem bytesLt_trich :
    ∀ (a b : List (BitVec 8)),
      CryptoVerification.LibsignalSpqrV1.bytesLt a b = true ∨ a = b ∨
      CryptoVerification.LibsignalSpqrV1.bytesLt b a = true
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl (by simp [CryptoVerification.LibsignalSpqrV1.bytesLt])
  | _ :: _, [] => Or.inr (Or.inr (by simp [CryptoVerification.LibsignalSpqrV1.bytesLt]))
  | x :: xs, y :: ys => by
    simp only [CryptoVerification.LibsignalSpqrV1.bytesLt]
    by_cases hxy : x < y
    · exact Or.inl (by simp [hxy])
    · by_cases hyx : y < x
      · exact Or.inr (Or.inr (by simp [hyx]))
      · have hxyeq : x = y := BitVec.le_antisymm (BitVec.not_lt.mp hyx) (BitVec.not_lt.mp hxy)
        subst hxyeq
        simp only [BitVec.lt_irrefl, ↓reduceIte]
        rcases bytesLt_trich xs ys with hlt | rfl | hgt
        · exact Or.inl hlt
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hgt)

private theorem bytesLt_strictLinOrder :
    StrictLinOrder (fun a b => CryptoVerification.LibsignalSpqrV1.bytesLt a b = true) :=
  ⟨bytesLt_irrefl, bytesLt_trans, bytesLt_trich⟩

private theorem pair32Lt_strictLinOrder : StrictLinOrder pair32Lt where
  irrefl := fun ⟨a1, a2⟩ h => by
    rcases h with h1 | ⟨_, h2⟩
    · exact bytesLt_irrefl a1 h1
    · exact bytesLt_irrefl a2 h2
  trans := fun {a b c} hab hbc => by
    rcases hab with h1 | ⟨he1, h2⟩ <;> rcases hbc with g1 | ⟨ge1, g2⟩
    · exact Or.inl (bytesLt_trans h1 g1)
    · exact Or.inl (ge1 ▸ h1)
    · exact Or.inl (he1.symm ▸ g1)
    · exact Or.inr ⟨he1.trans ge1, bytesLt_trans h2 g2⟩
  trich := fun ⟨a1, a2⟩ ⟨b1, b2⟩ => by
    rcases bytesLt_trich a1 b1 with h1 | rfl | h1
    · exact Or.inl (Or.inl h1)
    · rcases bytesLt_trich a2 b2 with h2 | rfl | h2
      · exact Or.inl (Or.inr ⟨rfl, h2⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h2⟩))
    · exact Or.inr (Or.inr (Or.inl h1))

private theorem pair32_goL_iff (a b : List (BitVec 8) × List (BitVec 8)) :
    ((if CryptoVerification.LibsignalSpqrV1.bytesLt a.1 b.1 then true
      else ((a.1 == b.1) && CryptoVerification.LibsignalSpqrV1.bytesLt a.2 b.2)) = true) ↔
      pair32Lt a b := by
  unfold pair32Lt
  by_cases h1 : CryptoVerification.LibsignalSpqrV1.bytesLt a.1 b.1 = true
  · simp [h1]
  · have h1f : CryptoVerification.LibsignalSpqrV1.bytesLt a.1 b.1 = false :=
      Bool.eq_false_iff.mpr h1
    simp [h1f]

theorem ofU8_inj :
    ∀ {a b : Bytes},
      CryptoVerification.E2E.ofU8 a = CryptoVerification.E2E.ofU8 b ↔ a = b
  | [], [] => by simp [CryptoVerification.E2E.ofU8]
  | [], _ :: _ => by simp [CryptoVerification.E2E.ofU8]
  | _ :: _, [] => by simp [CryptoVerification.E2E.ofU8]
  | x :: xs, y :: ys => by
    simp only [CryptoVerification.E2E.ofU8, List.map_cons, List.cons.injEq, UInt8.toBitVec_inj]
    exact and_congr_right fun _ => ofU8_inj

theorem ofU8_beq_eq (a b : Bytes) :
    (CryptoVerification.E2E.ofU8 a == CryptoVerification.E2E.ofU8 b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : CryptoVerification.E2E.ofU8 a ≠ CryptoVerification.E2E.ofU8 b :=
      fun heq => h (ofU8_inj.mp heq)
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

private def iterPure {α : Type} (f : α → α) : ℕ → α → α
  | 0, a => a
  | n + 1, a => iterPure f n (f a)

private theorem iterM_pure {ι : Type} {T : OracleSpec ι} {α : Type} (f : α → α) :
    ∀ (n : ℕ) (a : α),
      ReductionDsl.iterM (m := OracleComp T) (fun x => pure (f x)) n a = pure (iterPure f n a)
  | 0, _ => rfl
  | n + 1, a => by simp [ReductionDsl.iterM, iterPure, iterM_pure f n]

private theorem foldML_pure {ι : Type} {T : OracleSpec ι} {α β : Type} (f : α → β → β) :
    ∀ (b : β) (xs : List α),
      ReductionDsl.foldML (m := OracleComp T) (fun x acc => pure (f x acc)) b xs =
        pure (xs.foldl (fun acc x => f x acc) b)
  | _, [] => rfl
  | b, x :: xs => by simp [ReductionDsl.foldML, foldML_pure f (f x b) xs]

private theorem foldML_congr_pure {ι : Type} {T : OracleSpec ι} {α β : Type}
    {g : α → β → OracleComp T β} (f : α → β → β)
    (hg : ∀ x acc, g x acc = pure (f x acc)) (b : β) (xs : List α) :
    ReductionDsl.foldML g b xs = pure (xs.foldl (fun acc x => f x acc) b) := by
  have h : g = fun x acc => pure (f x acc) := funext fun x => funext fun acc => hg x acc
  rw [h, foldML_pure]

private def avlSearchStepPure {K V : Type} (ltBool : K → K → Bool)
    (kvTbl : ℕ → K × V) (sh : ℕ → ℕ × (ℕ × ℕ)) (key : K)
    (acc : ℕ × (ℕ × List (ℕ × Bool))) : ℕ × (ℕ × List (ℕ × Bool)) :=
  let cur := acc.1
  if decide (cur = 0) then acc
  else
    let shc := sh cur
    let cand := acc.2.1
    let path := acc.2.2
    if ltBool key (kvTbl cur).1 then
      (shc.1, (cand, (cur, true) :: path))
    else
      (shc.2.1, (cur, (cur, false) :: path))

private def avlSearchPure {K V : Type} (ltBool eqBool : K → K → Bool)
    (fuel root : ℕ) (kvTbl : ℕ → K × V) (sh : ℕ → ℕ × (ℕ × ℕ)) (key : K) :
    Option V × List (ℕ × Bool) :=
  let acc := iterPure (avlSearchStepPure ltBool kvTbl sh key) fuel (root, (0, []))
  let cand := acc.2.1
  let path := acc.2.2
  if decide (cand = 0) then (none, path)
  else
    let kv := kvTbl cand
    if eqBool key kv.1 then (some kv.2, path)
    else (none, path)

private theorem avlSearchPure_snd {K V : Type} (ltBool eqBool : K → K → Bool)
    (fuel root : ℕ) (kvTbl : ℕ → K × V) (sh : ℕ → ℕ × (ℕ × ℕ)) (key : K) :
    (avlSearchPure ltBool eqBool fuel root kvTbl sh key).2 =
      (iterPure (avlSearchStepPure ltBool kvTbl sh key) fuel (root, (0, []))).2.2 := by
  unfold avlSearchPure
  dsimp only
  split
  · rfl
  · split <;> rfl

private theorem avlSearchIter_spec {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK) {ltBool : K → K → Bool}
    (hLtB : ∀ a b, ltBool a b = true ↔ ltK a b)
    {kvTbl : ℕ → K × V} {sh : ℕ → ℕ × (ℕ × ℕ)} {maxId root rootH : ℕ}
    {rootKvs : List (K × V)} (key : K)
    (hpw : rootKvs.Pairwise (fun x y => ltK x.1 y.1)) :
    ∀ (fuel : ℕ) {cur cand : ℕ} {path : List (ℕ × Bool)}
      {lCtx rCtx curKvs : List (K × V)} {curH : ℕ},
      AvlTree ltK kvTbl sh maxId cur curH curKvs →
      AvlZipper ltK kvTbl sh maxId lCtx rCtx cur curH curKvs path root rootH rootKvs →
      curH ≤ fuel →
      curH + path.length ≤ rootH →
      (∀ kv ∈ rCtx, ltK key kv.1) →
      (∀ kv ∈ lCtx, ¬ ltK key kv.1) →
      ((cand = 0 ∧ lCtx = []) ∨
        (0 < cand ∧ cand ≤ maxId ∧ kvTbl cand ∈ lCtx ∧
          ∀ kv ∈ lCtx, kv.1 = key → kvTbl cand = kv)) →
      let acc := iterPure (avlSearchStepPure ltBool kvTbl sh key) fuel (cur, (cand, path))
      ∃ lCtx' rCtx',
        acc.1 = 0 ∧
        acc.2.2.length ≤ rootH ∧
        AvlZipper ltK kvTbl sh maxId lCtx' rCtx' 0 0 [] acc.2.2 root rootH rootKvs ∧
        (∀ kv ∈ rCtx', ltK key kv.1) ∧
        (∀ kv ∈ lCtx', ¬ ltK key kv.1) ∧
        ((acc.2.1 = 0 ∧ lCtx' = []) ∨
          (0 < acc.2.1 ∧ acc.2.1 ≤ maxId ∧ kvTbl acc.2.1 ∈ lCtx' ∧
            ∀ kv ∈ lCtx', kv.1 = key → kvTbl acc.2.1 = kv))
  | 0, cur, cand, path, lCtx, rCtx, curKvs, curH, ht, hz, hFuel, hLen, hRlt, hLle, hCand => by
    cases ht with
    | leaf _ =>
      dsimp only [iterPure]
      exact ⟨lCtx, rCtx, rfl, by omega, hz, hRlt, hLle, hCand⟩
    | node => omega
  | fuel + 1, cur, cand, path, lCtx, rCtx, curKvs, curH, ht, hz, hFuel, hLen, hRlt, hLle, hCand => by
    cases ht with
    | leaf h0 =>
      have hstep : avlSearchStepPure ltBool kvTbl sh key (0, (cand, path)) = (0, (cand, path)) := by
        simp [avlSearchStepPure]
      simp only [iterPure, hstep]
      exact avlSearchIter_spec H hLtB key hpw fuel (.leaf h0) hz (by omega) hLen hRlt hLle hCand
    | @node _ l r _ lh rh pk pv kvsL kvsR hp0 hpMax hkvP hshP hph hb1 hb2 hL hR hltL hltR =>
      have hpNe0 : cur ≠ 0 := by omega
      dsimp only [iterPure, avlSearchStepPure]
      simp only [decide_eq_false hpNe0, Bool.false_eq_true, ↓reduceIte, hshP, hkvP]
      by_cases hGoL : ltBool key pk = true
      · simp only [hGoL, ↓reduceIte]
        have hlt_key_pk : ltK key pk := (hLtB key pk).mp hGoL
        refine avlSearchIter_spec H hLtB key hpw fuel hL
          (.left hp0 hpMax hkvP hshP hph hb1 hb2 hR hltL hltR hz)
          (by omega) (by simp; omega) ?_ hLle hCand
        intro kv hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · rcases List.mem_cons.mp h1 with rfl | h1'
          · exact hlt_key_pk
          · exact H.trans hlt_key_pk (hltR kv h1')
        · exact hRlt kv h2
      · have hGoLf : ltBool key pk = false := Bool.eq_false_iff.mpr hGoL
        simp only [hGoLf, Bool.false_eq_true, ↓reduceIte]
        have hnlt_key_pk : ¬ ltK key pk := fun h => hGoL ((hLtB key pk).mpr h)
        have hDecomp := avlZipper_decomp hz
        have ⟨hLctx_mid, _⟩ := pairwise_mid_lt (hDecomp ▸ hpw)
        refine avlSearchIter_spec H hLtB key hpw fuel hR
          (.right hp0 hpMax hkvP hshP hph hb1 hb2 hL hltL hltR hz)
          (by omega) (by simp; omega) hRlt ?_ (Or.inr ⟨hp0, hpMax, ?_, ?_⟩)
        · intro kv hmem
          rcases List.mem_append.mp hmem with h1 | h2
          · rcases List.mem_append.mp h1 with h1a | h1b
            · exact hLle kv h1a
            · exact fun hbad => hnlt_key_pk (H.trans hbad (hltL kv h1b))
          · rcases List.mem_singleton.mp h2 with rfl
            exact hnlt_key_pk
        · rw [hkvP]; exact List.mem_append_right _ List.mem_cons_self
        · intro kv hmem hkeq
          rcases List.mem_append.mp hmem with h1 | h2
          · rcases List.mem_append.mp h1 with h1a | h1b
            · exfalso
              have hlt1 := hLctx_mid kv h1a (pk, pv) (List.mem_append_right _ List.mem_cons_self)
              exact hnlt_key_pk (hkeq ▸ hlt1)
            · exfalso
              exact hnlt_key_pk (hkeq ▸ hltL kv h1b)
          · rw [hkvP, List.mem_singleton.mp h2]

private theorem pairwise_find?_eq {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK) {pred : K × V → Bool} {key : K}
    (hPred : ∀ p, pred p = true ↔ p.1 = key) :
    ∀ {xs : List (K × V)},
      xs.Pairwise (fun a b => ltK a.1 b.1) →
      (∀ kv ∈ xs, kv.1 = key → xs.find? pred = some kv) ∧
      ((∀ kv ∈ xs, kv.1 ≠ key) → xs.find? pred = none) := by
  intro xs hpw
  induction xs with
  | nil => exact ⟨(fun _ h => nomatch h), fun _ => rfl⟩
  | cons x xs ih =>
    obtain ⟨hx_lt, hpw'⟩ := List.pairwise_cons.mp hpw
    obtain ⟨ihSome, ihNone⟩ := ih hpw'
    constructor
    · intro kv hmem hkeq
      rcases List.mem_cons.mp hmem with rfl | hm
      · simp [List.find?, (hPred kv).mpr hkeq]
      · have hne : x.1 ≠ key := H.ne_of_lt (hkeq ▸ hx_lt kv hm)
        have hpf : pred x = false := Bool.eq_false_iff.mpr fun h => hne ((hPred x).mp h)
        simp [List.find?, hpf, ihSome kv hm hkeq]
    · intro hAll
      have hpf : pred x = false :=
        Bool.eq_false_iff.mpr fun h => hAll x List.mem_cons_self ((hPred x).mp h)
      simp [List.find?, hpf, ihNone fun kv hm => hAll kv (List.mem_cons_of_mem _ hm)]

private theorem find?_insert_sorted {K V : Type} {ltK : K → K → Prop}
    (H : StrictLinOrder ltK)
    {lCtx rCtx : List (K × V)} {key q : K} {val : V}
    {pred : K × V → Bool}
    (hPred : ∀ p, pred p = true ↔ p.1 = q)
    (hLtL : ∀ kv ∈ lCtx, ltK kv.1 key) :
    ((lCtx ++ (key, val) :: rCtx).find? pred).map Prod.snd =
      if pred (key, val) then some val else ((lCtx ++ rCtx).find? pred).map Prod.snd := by
  by_cases hpKV : pred (key, val) = true
  · have hkq : key = q := (hPred (key, val)).mp hpKV
    subst hkq
    have hLnone : lCtx.find? pred = none := by
      rw [List.find?_eq_none]
      intro x hx hpx
      exact H.ne_of_lt (hLtL x hx) ((hPred x).mp hpx)
    simp [List.find?_append, hLnone, List.find?, hpKV]
  · have hpKVf : pred (key, val) = false := Bool.eq_false_iff.mpr hpKV
    simp [List.find?_append, List.find?, hpKVf]

private theorem isNone_of_map_eq {α β γ : Type} {o1 : Option α} {o2 : Option β}
    {f : α → γ} {g : β → γ} (h : o1.map f = o2.map g) (h2 : o2.isNone) : o1.isNone := by
  cases o1 <;> cases o2 <;> simp_all

private theorem avlSearchAndInsert_generic {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {K V : Ty pqAtomicSig} {ltK : K.denote → K.denote → Prop}
    (H : StrictLinOrder ltK)
    (ltBool eqBool : K.denote → K.denote → Bool)
    (hLtB : ∀ a b, ltBool a b = true ↔ ltK a b)
    (hEqB : ∀ a b, eqBool a b = true ↔ a = b)
    (cap : ℕ) (t : (avlTy K V).denote)
    (h rootId : ℕ) (kvs : List (K.denote × V.denote))
    (hMaxCap : t.2.1 ≤ cap)
    (ht : AvlTree ltK t.2.2.1 t.2.2.2 t.2.1 rootId h kvs)
    (key : K.denote)
    (predKey : K.denote × V.denote → Bool)
    (hPredKey : ∀ p, predKey p = true ↔ p.1 = key) :
    let res := avlSearchPure ltBool eqBool (avlHeightCap cap) rootId t.2.2.1 t.2.2.2 key
    res.1 = (kvs.find? predKey).map Prod.snd ∧
    res.2.length ≤ avlHeightCap cap ∧
    ((kvs.find? predKey).isNone →
      ∀ (val : V.denote),
        ∃ t' : (avlTy K V).denote,
          (avlInsertAtPathC (I := I) cap
            (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
            (.var (.succ (.succ (.succ .zero))))).eval
            (.cons t (.cons res.2 (.cons key (.cons val .nil)))) = pure t' ∧
          t'.2.1 = t.2.1 + 1 ∧
          ∃ h' lCtx rCtx,
            kvs = lCtx ++ rCtx ∧
            (∀ kv ∈ lCtx, ltK kv.1 key) ∧
            AvlTree ltK t'.2.2.1 t'.2.2.2 t'.2.1 t'.1 h' (lCtx ++ (key, val) :: rCtx)) := by
  have hltCap : h < avlHeightCap cap := avlTree_height_lt_avlHeightCap H ht hMaxCap
  have hpw : kvs.Pairwise (fun a b => ltK a.1 b.1) := avlTree_kvs_pairwise H ht
  obtain ⟨lCtx, rCtx, hCur0, hPathLen, hz, hRlt, hLle, hCand⟩ :=
    avlSearchIter_spec H hLtB key hpw (avlHeightCap cap) ht .nil
      (Nat.le_of_lt hltCap) (by simp) (fun _ hm => nomatch hm) (fun _ hm => nomatch hm)
      (Or.inl ⟨rfl, rfl⟩)
  have hDecomp : kvs = lCtx ++ rCtx := by simpa using avlZipper_decomp hz
  obtain ⟨hFindSome, hFindNone⟩ := pairwise_find?_eq H hPredKey hpw
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [avlSearchPure]
    let cand : ℕ := (iterPure (avlSearchStepPure ltBool t.2.2.1 t.2.2.2 key)
      (avlHeightCap cap) (rootId, 0, [])).2.1
    rcases hCand with ⟨hC0, hL0⟩ | ⟨hCpos, _, hCmem, hCuniq⟩
    · rw [hC0, hFindNone]
      · rfl
      · intro kv hm
        rw [hDecomp, hL0, List.nil_append] at hm
        exact (H.ne_of_lt (hRlt kv hm)).symm
    · have hCne0 : (iterPure (avlSearchStepPure ltBool t.2.2.1 t.2.2.2 key)
          (avlHeightCap cap) (rootId, 0, [])).2.1 ≠ 0 := Nat.ne_of_gt hCpos
      simp only [decide_eq_false hCne0, Bool.false_eq_true, ↓reduceIte]
      by_cases hEq : eqBool key (t.2.2.1 cand).1 = true
      · have hEq' : eqBool key (t.2.2.1 (iterPure (avlSearchStepPure ltBool t.2.2.1 t.2.2.2 key)
            (avlHeightCap cap) (rootId, 0, [])).2.1).1 = true := hEq
        simp only [hEq', ↓reduceIte]
        have hkeq : (t.2.2.1 cand).1 = key := ((hEqB _ _).mp hEq).symm
        have hmKvs : t.2.2.1 cand ∈ kvs := hDecomp ▸ List.mem_append_left _ hCmem
        rw [hFindSome _ hmKvs hkeq]
        rfl
      · have hEqF : eqBool key (t.2.2.1 (iterPure (avlSearchStepPure ltBool t.2.2.1 t.2.2.2 key)
            (avlHeightCap cap) (rootId, 0, [])).2.1).1 = false := Bool.eq_false_iff.mpr hEq
        simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
        rw [hFindNone]
        · rfl
        · intro kv hm hkeq
          rw [hDecomp] at hm
          rcases List.mem_append.mp hm with h1 | h2
          · have hEqCand := hCuniq kv h1 hkeq
            exact hEq ((hEqB _ _).mpr (by rw [hEqCand, hkeq]))
          · exact H.ne_of_lt (hRlt kv h2) hkeq.symm
  · rw [avlSearchPure_snd]
    exact Nat.le_trans hPathLen (Nat.le_of_lt hltCap)
  · intro hIsNone val
    have hAllNe : ∀ kv ∈ kvs, kv.1 ≠ key := by
      intro kv hm hkeq
      have hs := hFindSome kv hm hkeq
      rw [hs] at hIsNone
      simp at hIsNone
    have hLtL : ∀ kv ∈ lCtx, ltK kv.1 key := by
      intro kv hm
      rcases H.trich kv.1 key with hlt | heq | hgt
      · exact hlt
      · exact False.elim (hAllNe kv (hDecomp ▸ List.mem_append_left _ hm) heq)
      · exact False.elim (hLle kv hm hgt)
    let path := (iterPure (avlSearchStepPure ltBool t.2.2.1 t.2.2.2 key)
      (avlHeightCap cap) (rootId, 0, [])).2.2
    have hRes2 : (avlSearchPure ltBool eqBool (avlHeightCap cap) rootId t.2.2.1 t.2.2.2 key).2 =
        path := avlSearchPure_snd _ _ _ _ _ _ _
    have hTake : path.take (avlHeightCap cap) = path :=
      List.take_of_length_le (Nat.le_trans hPathLen (Nat.le_of_lt hltCap))
    let cnt : ℕ := t.2.1
    let newId : ℕ := cnt + 1
    let kv1 := tsetPure t.2.2.1 newId (key, val)
    let sh1 := tsetPure t.2.2.2 newId (0, (0, 1))
    let reb := path.foldl (fun acc x => avlRebalanceStepPure x acc) (newId, sh1)
    refine ⟨(reb.1, (newId, (kv1, reb.2))), ?_, rfl, ?_⟩
    · rw [hRes2]
      simp only [avlInsertAtPathC, Comp.eval, Expr.eval, pure_bind,
        Expr.v0, Expr.v1, Env.get, avlCountE, avlKvE, avlShapeE, avlMkE, mkShapeNodeE]
      rw [hTake, foldML_congr_pure avlRebalanceStepPure
        (fun x acc => by rw [avlRebalanceStepE_eval]; rfl)]
      simp only [pure_bind]
      rfl
    · have h0ne : (0 : ℕ) ≠ newId := Nat.ne_of_lt (Nat.succ_pos cnt)
      have hsh1_zero : sh1 0 = (0, (0, 0)) :=
        (tsetPure_ne _ _ h0ne).trans (avlTree_shapeTbl_zero ht)
      have hLeaf0 : AvlTree ltK kv1 sh1 newId 0 0 [] := .leaf hsh1_zero
      have hNewNode : AvlTree ltK kv1 sh1 newId newId 1 [(key, val)] :=
        .node (Nat.succ_pos cnt) (Nat.le_refl _)
          (tsetPure_self _ _ _) (tsetPure_self _ _ _)
          rfl (Nat.zero_le 1) (Nat.zero_le 1) hLeaf0 hLeaf0
          (fun _ hm => nomatch hm) (fun _ hm => nomatch hm)
      have hz1 : AvlZipper ltK kv1 sh1 newId lCtx rCtx 0 0 [] path rootId h kvs := by
        refine avlZipper_congr hz (Nat.le_succ cnt) hsh1_zero ?_
        intro u _ huM _
        have hne : u ≠ newId := Nat.ne_of_lt (Nat.lt_succ_of_le huM)
        exact ⟨tsetPure_ne _ _ hne, tsetPure_ne _ _ hne⟩
      obtain ⟨h', hTree'⟩ := avlFoldRebalance_spec H hpw path hz1 hNewNode
        (Nat.zero_le 1) (Nat.le_refl 1)
        (fun a ha b hb => by rw [List.mem_singleton.mp hb]; exact hLtL a ha)
        (fun b hb a ha => by rw [List.mem_singleton.mp hb]; exact hRlt a ha)
      exact ⟨h', lCtx, rCtx, hDecomp, hLtL, by simpa using hTree'⟩

/-- `avlSearchB192C` is pure and agrees with `entries.find?` under `AvlB192Valid`, and on a miss
    `avlInsertAtPathC` preserves `AvlB192Valid` when `entries.length + 1 ≤ cap`. -/
theorem avlSearchInsertB192_spec {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192))
    (ρ : Env Γ) (sec : Bytes)
    (entries : List (Bytes × V.denote))
    (hKey : keyE.eval ρ = CryptoVerification.E2E.ofU8 sec)
    (hValid : AvlB192Valid cap (tblE.eval ρ) entries) :
    ∃ path : List (ℕ × Bool),
      (avlSearchB192C (I := I) cap tblE keyE).eval ρ =
        pure (((entries.find? (fun p => p.1 == sec)).map Prod.snd), path) ∧
      ((entries.find? (fun p => p.1 == sec)).isNone →
        entries.length + 1 ≤ cap →
        ∀ (val : V.denote),
          ∃ t' : (avlTy (B 192) V).denote,
            (avlInsertAtPathC (I := I) cap
              (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
              (.var (.succ (.succ (.succ .zero))))).eval
              (.cons (tblE.eval ρ) (.cons path (.cons (CryptoVerification.E2E.ofU8 sec)
                (.cons val .nil)))) = pure t' ∧
            AvlB192Valid cap t' ((sec, val) :: entries)) := by
  obtain ⟨hLenCap, hCntEq, h, kvs, ht, hLookup⟩ := hValid
  let keyB := CryptoVerification.E2E.ofU8 sec
  obtain ⟨hRes1, _, hIns⟩ := avlSearchAndInsert_generic (I := I) bytesLt_strictLinOrder
    CryptoVerification.LibsignalSpqrV1.bytesLt (· == ·)
    (fun _ _ => Iff.rfl) (fun _ _ => beq_iff_eq)
    cap (tblE.eval ρ) h (tblE.eval ρ).1 kvs (hCntEq ▸ hLenCap) ht keyB
    (fun p => p.1 == keyB) (fun _ => beq_iff_eq)
  let res := avlSearchPure CryptoVerification.LibsignalSpqrV1.bytesLt (· == ·)
    (avlHeightCap cap) (tblE.eval ρ).1 (tblE.eval ρ).2.2.1 (tblE.eval ρ).2.2.2 keyB
  refine ⟨res.2, ?_, ?_⟩
  · have hEval : (avlSearchB192C (I := I) cap tblE keyE).eval ρ = pure res := by
      simp only [avlSearchB192C, Comp.eval, Expr.eval, pure_bind, hKey,
        Expr.v0, Expr.v1, Expr.v2, Env.get, avlRootE, avlShapeE, avlKvE, aop,
        pqAtomicOps, atomicPureOps, AtomicPureOp.eval]
      have hBody :
          (fun (a : ℕ × (ℕ × List (ℕ × Bool))) =>
            (if decide (a.1 = 0) then (pure a : OracleComp T _)
             else pure (if CryptoVerification.LibsignalSpqrV1.bytesLt keyB
                 ((tblE.eval ρ).2.2.1 a.1).1 then
                 (((tblE.eval ρ).2.2.2 a.1).1, (a.2.1, (a.1, true) :: a.2.2))
               else (((tblE.eval ρ).2.2.2 a.1).2.1, (a.1, (a.1, false) :: a.2.2))))) =
            (fun a => pure (avlSearchStepPure CryptoVerification.LibsignalSpqrV1.bytesLt
              (tblE.eval ρ).2.2.1 (tblE.eval ρ).2.2.2 keyB a)) := by
        funext a
        by_cases h0 : a.1 = 0 <;> simp [avlSearchStepPure, h0]
      rw [hBody, iterM_pure]
      simp only [pure_bind]
      rfl
    exact hEval.trans (congrArg pure (Prod.ext (hRes1.trans (hLookup sec)) rfl))
  · intro hMiss hLen1 val
    have hKvsMiss : (kvs.find? (fun p => p.1 == keyB)).isNone :=
      isNone_of_map_eq (hLookup sec) hMiss
    obtain ⟨t', ht'Eval, ht'Cnt, h', lCtx, rCtx, rfl, hLtL, ht'Tree⟩ := hIns hKvsMiss val
    refine ⟨t', ht'Eval, hLen1, by simp [ht'Cnt, hCntEq], h', lCtx ++ (keyB, val) :: rCtx,
      ht'Tree, ?_⟩
    intro sec'
    rw [find?_insert_sorted bytesLt_strictLinOrder
      (q := CryptoVerification.E2E.ofU8 sec') (fun _ => beq_iff_eq) hLtL]
    dsimp only [keyB]
    rw [ofU8_beq_eq sec sec', hLookup sec']
    cases hbeq : (sec == sec') <;> simp [List.find?, hbeq]

/-- `avlSearchPair32C` is pure and agrees with `entries.find?` under `AvlPair32Valid`, and on a miss
    `avlInsertAtPathC` preserves `AvlPair32Valid` when `entries.length + 1 ≤ cap`. -/
theorem avlSearchInsertPair32_spec {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32)))
    (ρ : Env Γ) (rk dh : Bytes)
    (entries : List ((Bytes × Bytes) × V.denote))
    (hKey : keyE.eval ρ = (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh))
    (hValid : AvlPair32Valid cap (tblE.eval ρ) entries) :
    ∃ path : List (ℕ × Bool),
      (avlSearchPair32C (I := I) cap tblE keyE).eval ρ =
        pure (((entries.find? (fun p => p.1.1 == rk && p.1.2 == dh)).map Prod.snd), path) ∧
      ((entries.find? (fun p => p.1.1 == rk && p.1.2 == dh)).isNone →
        entries.length + 1 ≤ cap →
        ∀ (val : V.denote),
          ∃ t' : (avlTy (.prod (B 32) (B 32)) V).denote,
            (avlInsertAtPathC (I := I) cap
              (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
              (.var (.succ (.succ (.succ .zero))))).eval
              (.cons (tblE.eval ρ) (.cons path
                (.cons (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh)
                  (.cons val .nil)))) = pure t' ∧
            AvlPair32Valid cap t' (((rk, dh), val) :: entries)) := by
  obtain ⟨hLenCap, hCntEq, h, kvs, ht, hLookup⟩ := hValid
  let keyP : List (BitVec 8) × List (BitVec 8) :=
    (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh)
  let ltP := fun a b : List (BitVec 8) × List (BitVec 8) =>
    if CryptoVerification.LibsignalSpqrV1.bytesLt a.1 b.1 then true
    else ((a.1 == b.1) && CryptoVerification.LibsignalSpqrV1.bytesLt a.2 b.2)
  let eqP := fun a b : List (BitVec 8) × List (BitVec 8) => (a.1 == b.1) && (a.2 == b.2)
  have hEqP : ∀ a b, eqP a b = true ↔ a = b := by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩
    simp [eqP, Bool.and_eq_true]
  obtain ⟨hRes1, _, hIns⟩ := avlSearchAndInsert_generic (I := I) pair32Lt_strictLinOrder
    ltP eqP pair32_goL_iff hEqP
    cap (tblE.eval ρ) h (tblE.eval ρ).1 kvs (hCntEq ▸ hLenCap) ht keyP
    (fun p => p.1.1 == keyP.1 && p.1.2 == keyP.2)
    (fun ⟨⟨k1, k2⟩, _⟩ => by simp [keyP, Bool.and_eq_true, Prod.mk.injEq])
  let res := avlSearchPure ltP eqP
    (avlHeightCap cap) (tblE.eval ρ).1 (tblE.eval ρ).2.2.1 (tblE.eval ρ).2.2.2 keyP
  refine ⟨res.2, ?_, ?_⟩
  · have hEval : (avlSearchPair32C (I := I) cap tblE keyE).eval ρ = pure res := by
      simp only [avlSearchPair32C, Comp.eval, Expr.eval, pure_bind, hKey, orBoolE,
        Expr.v0, Expr.v1, Expr.v2, Env.get, avlRootE, avlShapeE, avlKvE, aop,
        pqAtomicOps, atomicPureOps, AtomicPureOp.eval]
      have hBody :
          (fun (a : ℕ × (ℕ × List (ℕ × Bool))) =>
            (if decide (a.1 = 0) then (pure a : OracleComp T _)
             else pure (if (if CryptoVerification.LibsignalSpqrV1.bytesLt keyP.1
                 ((tblE.eval ρ).2.2.1 a.1).1.1 then true
                 else ((keyP.1 == ((tblE.eval ρ).2.2.1 a.1).1.1) &&
                   CryptoVerification.LibsignalSpqrV1.bytesLt keyP.2
                     ((tblE.eval ρ).2.2.1 a.1).1.2)) then
                 (((tblE.eval ρ).2.2.2 a.1).1, (a.2.1, (a.1, true) :: a.2.2))
               else (((tblE.eval ρ).2.2.2 a.1).2.1, (a.1, (a.1, false) :: a.2.2))))) =
            (fun a => pure (avlSearchStepPure ltP
              (tblE.eval ρ).2.2.1 (tblE.eval ρ).2.2.2 keyP a)) := by
        funext a
        by_cases h0 : a.1 = 0 <;> simp [avlSearchStepPure, ltP, h0]
      rw [hBody, iterM_pure]
      simp only [pure_bind]
      rfl
    exact hEval.trans (congrArg pure (Prod.ext (hRes1.trans (hLookup rk dh)) rfl))
  · intro hMiss hLen1 val
    have hKvsMiss : (kvs.find? (fun p => p.1.1 == keyP.1 && p.1.2 == keyP.2)).isNone :=
      isNone_of_map_eq (hLookup rk dh) hMiss
    obtain ⟨t', ht'Eval, ht'Cnt, h', lCtx, rCtx, rfl, hLtL, ht'Tree⟩ := hIns hKvsMiss val
    refine ⟨t', ht'Eval, hLen1, by simp [ht'Cnt, hCntEq], h', lCtx ++ (keyP, val) :: rCtx,
      ht'Tree, ?_⟩
    intro rk' dh'
    rw [find?_insert_sorted pair32Lt_strictLinOrder
      (q := (CryptoVerification.E2E.ofU8 rk', CryptoVerification.E2E.ofU8 dh'))
      (fun ⟨⟨k1, k2⟩, _⟩ => by simp [Bool.and_eq_true, Prod.mk.injEq]) hLtL]
    dsimp only [keyP]
    rw [ofU8_beq_eq rk rk', ofU8_beq_eq dh dh', hLookup rk' dh']
    cases hbeq : ((rk == rk') && (dh == dh')) <;> simp [List.find?, hbeq]

/-- Evaluating `avlInsertAtPathC` on arbitrary argument expressions agrees with evaluating it on
    `.var 0 .. .var 3` in the corresponding 4-element environment. -/
theorem avlInsertAtPathC_eval_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K) (valE : Expr pqAtomicOps Γ V) (ρ : Env Γ) :
    (avlInsertAtPathC (I := I) cap tblE pathE keyE valE).eval ρ =
      (avlInsertAtPathC (I := I) cap
        (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
        (.var (.succ (.succ (.succ .zero))))).eval
        (.cons (tblE.eval ρ) (.cons (pathE.eval ρ)
          (.cons (keyE.eval ρ) (.cons (valE.eval ρ) .nil)))) := by
  simp only [avlInsertAtPathC, Comp.eval, Expr.eval, pure_bind, Env.get,
    Expr.v0, Expr.v1, avlCountE, avlKvE, avlShapeE, avlMkE, mkShapeNodeE]
  rw [foldML_congr_pure avlRebalanceStepPure (fun x acc => by rw [avlRebalanceStepE_eval]; rfl),
    foldML_congr_pure avlRebalanceStepPure (fun x acc => by rw [avlRebalanceStepE_eval]; rfl)]

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec
