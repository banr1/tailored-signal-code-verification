/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import Computational.Proofs.CryptoGames.FSAEAD.HybridProofDefs
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs
import Computational.Proofs.CryptoGames.FSAEAD.HybridLazy

/-!
# Final Hybrids for ACD19 Theorem 5

**Checked by Lean.**

Proves that for a `q`-query adversary, the final lookahead hybrid `A_N^la` (`N ≥ q + maxSkip + 1`)
accepts a lookahead forgery with probability `0` (`final_la_of_le`, `final_la_idx`), and the final
main-chain hybrid `A_N` (`N ≥ q`) outputs `true` with probability `1 / 2` (`final_main_of_le`,
`final_main_idx`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.FSAEAD.Thm5.Ends

variable {CK MK AD M C : Type}

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C
local notation "SP" => StateT (HSt CK MK AD M C) ProbComp

/-! ## Key-generation state preservation -/

theorem mem_support_sampleH {α : Type} {p : ProbComp α} {s s' : St} {a : α}
    (h : (a, s') ∈ support ((sampleH p : SP α).run s)) : s' = s := by
  simp only [sampleH_run, map_eq_bind_pure_comp, Function.comp_apply,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
  rcases h with ⟨_, _, _, hs⟩
  exact Prod.ext hs.1 hs.2

section GenSupport

variable [SampleableType MK] (G : ℕ → PRGScheme CK (CK × MK))

theorem mem_support_genStep {P : Params} {D : ℕ → ProbComp (CK × MK)} {s s' : St} {u : Unit}
    (h : (u, s') ∈ support ((genStep G P D : SP Unit).run s)) :
    ∃ ks, s'.1 = { s.1 with keys := ks } := by
  rcases s with ⟨st, sl⟩
  cases sl with
  | seed w =>
    simp only [genStep, StateT.run_mk, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    exact ⟨_, by rw [← h.2.1]⟩
  | mat pos mt =>
    by_cases hlt : st.keys.length < pos
    · simp only [genStep, StateT.run_mk, hlt, ↓reduceIte, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      rcases h with ⟨K, _, _, hst, _⟩
      exact ⟨_, by rw [← hst]⟩
    · simp only [genStep, StateT.run_mk, hlt, ↓reduceIte, support_pure, Set.mem_singleton_iff,
        Prod.ext_iff] at h
      exact ⟨_, by rw [← h.2.1]⟩
  | unknown =>
    by_cases hlt : st.keys.length < P.j
    · simp only [genStep, StateT.run_mk, hlt, ↓reduceIte, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      rcases h with ⟨K, _, _, hst, _⟩
      exact ⟨_, by rw [← hst]⟩
    · simp only [genStep, StateT.run_mk, hlt, ↓reduceIte, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      rcases h with ⟨mt, _, _, hst, _⟩
      exact ⟨_, by rw [← hst]⟩

theorem mem_support_genN {P : Params} {D : ℕ → ProbComp (CK × MK)} :
    ∀ (n : ℕ) {s s' : St} {u : Unit},
      (u, s') ∈ support ((genN G P D n : SP Unit).run s) →
      ∃ ks, s'.1 = { s.1 with keys := ks }
  | 0, s, s', u, h => by
    simp only [genN, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    exact ⟨s.1.keys, by rw [h.2.1]⟩
  | n + 1, s, s', u, h => by
    simp only [genN, StateT.run_bind, MonadAttach.mem_support_bind] at h
    rcases h with ⟨⟨_, s₁⟩, h₁, h₂⟩
    rcases mem_support_genStep G h₁ with ⟨ks₁, hks₁⟩
    rcases mem_support_genN n h₂ with ⟨ks₂, hks₂⟩
    exact ⟨ks₂, by rw [hks₂, hks₁]⟩

theorem mem_support_genUpTo {P : Params} {D : ℕ → ProbComp (CK × MK)} {i : ℕ} {s s' : St} {u : Unit}
    (h : (u, s') ∈ support ((genUpTo G P D i : SP Unit).run s)) :
    ∃ ks, s'.1 = { s.1 with keys := ks } := by
  simp only [genUpTo, StateT.run_bind, getH_run, pure_bind] at h
  exact mem_support_genN G _ h

end GenSupport

theorem mem_newSkipped_iff {iB i x : ℕ} : x ∈ newSkipped iB i ↔ iB < x ∧ x < i := by
  simp only [newSkipped, List.mem_reverse, List.mem_range']
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨x - (iB + 1), by omega, by omega⟩

theorem decIdx_none_of_ideal (ae : AEADScheme MK (ℕ × AD) M C) {N : ℕ} {la : Bool} {i : ℕ}
    {a : AD} {e : C} {s : St} (hi : i ≤ N) (hc : s.1.isCompromised i = false) :
    (decIdx ae (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) none i a e).run s =
      pure (none, s) := by
  have hk : kind (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) s.1 i = .ideal := by
    simp [kind, hp, hi, hc]
  simp [decIdx, getH, onH, hk]

theorem mem_support_decIdx (ae : AEADScheme MK (ℕ × AD) M C) {P : Params} {hint : Option M}
    {i : ℕ} {a : AD} {e : C} {s s' : St} {r : Option M}
    (h : (r, s') ∈ support ((decIdx ae P (none : Option (SpecialOps AD M C ProbComp)) hint i a e).run s)) :
    s' = s ∧ (∀ msg, hint = some msg → r = some msg) := by
  unfold decIdx at h
  cases hint with
  | some msg =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    refine ⟨Prod.ext h.2.1 h.2.2, ?_⟩
    rintro _ ⟨⟩
    exact h.1
  | none =>
    simp only [StateT.run_bind, getH_run, pure_bind, reduceCtorEq, false_implies, implies_true,
      and_true] at h ⊢
    split at h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      exact Prod.ext h.2.1 h.2.2
    · exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      exact Prod.ext h.2.1 h.2.2

theorem mem_support_encIdx (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    {P : Params} {i : ℕ} {a : AD} {msg : M} {s s' : St} {e : C}
    (h : (e, s') ∈ support ((encIdxWith ideal ae P (none : Option (SpecialOps AD M C ProbComp)) i a msg).run s)) :
    s' = s := by
  unfold encIdxWith at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · exact mem_support_sampleH h
  · exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
  · split at h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      exact Prod.ext h.2.1 h.2.2
    · exact mem_support_sampleH h

theorem mem_support_reveal [SampleableType CK] {s s' : St} {w : CK}
    (h : (w, s') ∈ support ((reveal : SP CK).run s)) :
    s'.1 = s.1 := by
  rcases s with ⟨st, sl⟩
  cases sl <;>
    simp only [reveal, StateT.run_mk, support_pure, Set.mem_singleton_iff,
      MonadAttach.mem_support_bind, Prod.ext_iff] at h
  · rcases h with ⟨_, _, _, hst, _⟩; exact hst
  · exact h.2.1
  · rcases h with ⟨_, _, _, hst, _⟩; exact hst

theorem mem_support_senderKey [SampleableType CK] (G : ℕ → PRGScheme CK (CK × MK)) {s s' : St} {w : CK}
    (h : (w, s') ∈ support ((senderKey G : SP CK).run s)) :
    s'.1 = s.1 := by
  unfold senderKey at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    exact h.2.1
  · exact mem_support_reveal h

section ReceiveSupport

variable [SampleableType MK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

theorem mem_support_receiveH_none {P : Params} {D : ℕ → ProbComp (CK × MK)} {hint : Option M}
    {a : AD} {i : ℕ} {e : C} {s s' : St}
    (h : (none, s') ∈ support
      ((receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) hint a (i, e)).run s)) :
    (∃ ks, s'.1 = { s.1 with keys := ks }) ∧
      ∀ msg, hint = some msg → i ≤ s.1.receiverIdx + maxSkip + 1 → i ≤ s.1.lastSentIdx →
        (s.1.receiverIdx < i ∨ i ∈ s.1.skipped) → False := by
  unfold receiveH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at h
    rcases h with ⟨⟨r, s₁⟩, h₁, h₂⟩
    rcases mem_support_decIdx ae h₁ with ⟨hs₁, hhint⟩
    rw [hs₁] at h₂
    cases r with
    | some msg =>
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff, reduceCtorEq, false_and] at h₂
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₂
      refine ⟨⟨s.1.keys, by rw [h₂.2.1]⟩, fun msg hmsg _ _ _ => ?_⟩
      exact nomatch hhint msg hmsg
  · rename_i hmem
    split at h
    · rename_i hwin
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      refine ⟨⟨s.1.keys, by rw [h.2.1]⟩, fun _ _ hi_win _ hpos => ?_⟩
      rcases hpos with hi_gt | hi_sk
      · omega
      · exact hmem (List.elem_eq_true_of_mem hi_sk)
    · split at h
      · rename_i hla
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hla
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
        refine ⟨⟨s.1.keys, by rw [h.2.1]⟩, fun _ _ _ hi_sent _ => ?_⟩
        have := hla.1.2
        omega
      · rw [StateT.run_bind, MonadAttach.mem_support_bind] at h
        rcases h with ⟨⟨_, s₁⟩, h₁, h₂⟩
        rw [StateT.run_bind, MonadAttach.mem_support_bind] at h₂
        rcases h₂ with ⟨⟨r, s₂⟩, h₂, h₃⟩
        rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
        rcases mem_support_decIdx ae h₂ with ⟨hs₂, hhint⟩
        rw [hs₂] at h₃
        cases r with
        | some msg =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff, reduceCtorEq, false_and] at h₃
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₃
          refine ⟨⟨ks, by rw [h₃.2.1, hks]⟩, fun msg hmsg _ _ _ => ?_⟩
          exact nomatch hhint msg hmsg

theorem mem_support_receiveH_some {P : Params} {D : ℕ → ProbComp (CK × MK)} {hint : Option M}
    {a : AD} {i i' : ℕ} {e : C} {m' : M} {s s' : St}
    (hsk : ∀ x ∈ s.1.skipped, x ≤ s.1.receiverIdx)
    (h : (some (i', m'), s') ∈ support
      ((receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) hint a (i, e)).run s)) :
    i' = i ∧ (∀ msg, hint = some msg → m' = msg) ∧
      max s.1.receiverIdx i' ≤ s.1.receiverIdx + (maxSkip + 1) ∧
      (∀ x ∈ s'.1.skipped, x ≤ max s.1.receiverIdx i') ∧
      (∀ x, x ≠ i' → (s.1.receiverIdx < x ∨ x ∈ s.1.skipped) →
        max s.1.receiverIdx i' < x ∨ x ∈ s'.1.skipped) ∧
      (∃ ks sk, s'.1 = { s.1 with keys := ks, skipped := sk }) ∧
      ((i' ≤ s.1.receiverIdx ∨
          (P.la = false → s.1.isCompromised i' = false → i' ≤ s.1.lastSentIdx)) ∧
        (∀ N, P = hp N N P.la → i' ≤ N →
          hint = none → s.1.isCompromised i' = true)) := by
  unfold receiveH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · rename_i hmem
    have hi_le : i ≤ s.1.receiverIdx := hsk i (List.mem_of_elem_eq_true hmem)
    rw [StateT.run_bind, MonadAttach.mem_support_bind] at h
    rcases h with ⟨⟨r, s₁⟩, h₁, h₂⟩
    rcases mem_support_decIdx ae h₁ with ⟨hs₁, hhint⟩
    rw [hs₁] at h₂
    cases r with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff,
        reduceCtorEq, false_and] at h₂
    | some msg =>
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff, Option.some.injEq] at h₂
      rcases h₂ with ⟨⟨rfl, rfl⟩, hst', _⟩
      refine ⟨rfl, fun m hm => Option.some.inj (hhint m hm), by omega, ?_, ?_,
        ⟨s.1.keys, _, by rw [hst']⟩, Or.inl hi_le, ?_⟩
      · intro x hx
        rw [hst'] at hx
        simp only [List.mem_filter] at hx
        have := hsk x hx.1
        omega
      · intro x hne hx
        rw [hst']
        rcases hx with hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (List.mem_filter.mpr ⟨hx, by simpa [bne_iff_ne] using hne⟩)
      · intro N hP hN hnone
        subst hnone
        rw [hP] at h₁
        by_contra hc
        simp only [Bool.not_eq_true] at hc
        rw [decIdx_none_of_ideal ae (by omega) hc] at h₁
        simp at h₁
  · rename_i hmem
    split at h
    · simp at h
    · rename_i hwin
      have hi_gt : s.1.receiverIdx < i := by omega
      have hi_le : i ≤ s.1.receiverIdx + maxSkip + 1 := by omega
      split at h
      · simp at h
      · rename_i hguard
        rw [StateT.run_bind, MonadAttach.mem_support_bind] at h
        rcases h with ⟨⟨_, s₁⟩, h₁, h₂⟩
        rw [StateT.run_bind, MonadAttach.mem_support_bind] at h₂
        rcases h₂ with ⟨⟨r, s₂⟩, h₂, h₃⟩
        rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
        rcases mem_support_decIdx ae h₂ with ⟨hs₂, hhint⟩
        rw [hs₂] at h₃
        cases r with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff,
            reduceCtorEq, false_and] at h₃
        | some msg =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.ext_iff, Option.some.injEq] at h₃
          rcases h₃ with ⟨⟨rfl, rfl⟩, hst', _⟩
          refine ⟨rfl, fun m hm => Option.some.inj (hhint m hm), by omega, ?_, ?_,
            ⟨ks, _, by rw [hst', hks]⟩, Or.inr fun hla hnc => ?_, ?_⟩
          · intro x hx
            rw [hst', hks] at hx
            simp only [List.mem_append, mem_newSkipped_iff] at hx
            rcases hx with ⟨_, _⟩ | hx
            · omega
            · have := hsk x hx; omega
          · intro x hne hx
            rw [hst', hks]
            simp only [List.mem_append, mem_newSkipped_iff]
            rcases hx with hx | hx
            · by_cases hxi : x < i'
              · exact Or.inr (Or.inl ⟨hx, hxi⟩)
              · exact Or.inl (by omega)
            · exact Or.inr (Or.inr hx)
          · by_contra hgt
            apply hguard
            simp only [hla, hnc, Bool.not_false, Bool.true_and, Bool.and_true, decide_eq_true_eq]
            omega
          · intro N hP hN hnone
            subst hnone
            rw [hP] at h₂
            by_contra hc
            simp only [Bool.not_eq_true] at hc
            have hc₁ : s₁.1.isCompromised i' = false := by
              rw [hks]; exact hc
            rw [decIdx_none_of_ideal ae (by omega) hc₁] at h₂
            simp at h₂

end ReceiveSupport

/-! ## Lookahead final hybrid -/

/-- Support invariant for the final lookahead hybrid `A_N^la`. -/
structure InvLA (maxSkip N rem : ℕ) (st : HS) : Prop where
  lf_false : st.lf = false
  corr_none : st.senderCorruptedAt = none
  sent_bound : st.lastSentIdx + rem + (maxSkip + 1) ≤ N
  rcv_le_sent : st.receiverIdx ≤ st.lastSentIdx
  skipped_le : ∀ x ∈ st.skipped, x ≤ st.receiverIdx
  inTransit_wf : ∀ r ∈ st.inTransit, r.ct.1 = r.idx ∧ r.idx ≤ st.lastSentIdx

theorem InvLA.mono {maxSkip N rem₁ rem₂ : ℕ} {st : HS} (h : InvLA maxSkip N rem₂ st)
    (hle : rem₁ ≤ rem₂) : InvLA maxSkip N rem₁ st :=
  ⟨h.lf_false, h.corr_none, by have := h.sent_bound; omega, h.rcv_le_sent,
    h.skipped_le, h.inTransit_wf⟩

section FinalLA

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem invLA_transmitH {N rem : ℕ} (hrem : 0 < rem) {s s' : St} {q : AD × M} {u : Option (ℕ × C)}
    (hinv : InvLA maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((transmitHWith ideal ae G (hp N N true) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s)) :
    InvLA maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvLA maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold transmitHWith at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rcases h with ⟨⟨_, s₁⟩, h₁, ⟨e, s₂⟩, h₂, _, hst', _⟩
    rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
    have hs₂ := mem_support_encIdx ideal ae h₂
    rw [hs₂, hks] at hst'
    rw [hst']
    refine ⟨hinv'.lf_false, hinv'.corr_none, ?_, ?_, hinv'.skipped_le, ?_⟩
    · dsimp only
      have := hinv.sent_bound
      omega
    · dsimp only
      have := hinv.rcv_le_sent
      omega
    · intro r hr
      dsimp only at hr ⊢
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨rfl, le_rfl⟩
      · rcases hinv'.inTransit_wf r hr with ⟨h1, h2⟩
        exact ⟨h1, by omega⟩

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem invLA_challengeH {N rem : ℕ} (hrem : 0 < rem) {s s' : St} {q : AD × M × M} {u : Option (ℕ × C)}
    (hinv : InvLA maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((challengeHWith ideal ae G (hp N N true) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s)) :
    InvLA maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvLA maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold challengeHWith at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rcases h with ⟨⟨_, s₁⟩, h₁, ⟨e, s₂⟩, h₂, _, hst', _⟩
    rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
    have hs₂ := mem_support_encIdx ideal ae h₂
    rw [hs₂, hks] at hst'
    rw [hst']
    refine ⟨hinv'.lf_false, hinv'.corr_none, ?_, ?_, hinv'.skipped_le, ?_⟩
    · dsimp only
      have := hinv.sent_bound
      omega
    · dsimp only
      have := hinv.rcv_le_sent
      omega
    · intro r hr
      dsimp only at hr ⊢
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨rfl, le_rfl⟩
      · rcases hinv'.inTransit_wf r hr with ⟨h1, h2⟩
        exact ⟨h1, by omega⟩

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem invLA_corruptSenderH {N rem : ℕ} {s s' : St} (q : Unit) {u : Option (RatchetSenderState CK)}
    (hinv : InvLA maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G (hp N N true) q).run s)) :
    InvLA maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvLA maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold corruptSenderH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · simp only [hp_la, ↓reduceIte, StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]
    exact ⟨hinv'.lf_false, hinv'.corr_none, hinv'.sent_bound, hinv'.rcv_le_sent,
      hinv'.skipped_le, hinv'.inTransit_wf⟩

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem invLA_corruptReceiverH {N rem : ℕ} {s s' : St} (q : Unit)
    {u : Option (RatchetSenderState CK × RatchetReceiverState CK MK)}
    (hinv : InvLA maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G (hp N N true) q).run s)) :
    InvLA maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvLA maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold corruptReceiverH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · simp only [hp_la, ↓reduceIte, StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]
    exact ⟨hinv'.lf_false, hinv'.corr_none, hinv'.sent_bound, hinv'.rcv_le_sent,
      hinv'.skipped_le, hinv'.inTransit_wf⟩

theorem invLA_deliverH {N rem : ℕ} (_hrem : 0 < rem) {s s' : St} {q : AD × (ℕ × C)}
    {u : Option (ReceiveResult M)} (hinv : InvLA maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((deliverH ae G maxSkip (hp N N true) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s)) :
    InvLA maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvLA maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold deliverH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · split at h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      rw [h.2.1]; exact hinv'
    · rename_i _ r hfind
      have hr_mem : r ∈ s.1.inTransit := List.mem_of_find?_eq_some hfind
      have hr_pred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hr_pred
      rcases q with ⟨a, i, e⟩
      rcases hinv.inTransit_wf r hr_mem with ⟨hct1, hr_sent⟩
      have hi_eq : i = r.idx := by
        have := congrArg Prod.fst hr_pred.2
        dsimp only at this
        omega
      rw [StateT.run_bind, MonadAttach.mem_support_bind] at h
      rcases h with ⟨⟨res, s₁⟩, h₁, h₂⟩
      cases res with
      | none =>
        rcases (mem_support_receiveH_none ae G maxSkip h₁).1 with ⟨ks, hks⟩
        simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff] at h₂
        rw [h₂.2.1, hks]
        exact ⟨hinv'.lf_false, hinv'.corr_none, hinv'.sent_bound, hinv'.rcv_le_sent,
          hinv'.skipped_le, hinv'.inTransit_wf⟩
      | some p =>
        rcases p with ⟨i', m'⟩
        have ⟨rfl, _, hmax, hsk₁, _, ⟨ks, sk, hks⟩, _⟩ :=
          mem_support_receiveH_some ae G maxSkip hinv.skipped_le h₁
        simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff, HState.removeFromTransit] at h₂
        have hrcv₁ : s₁.1.receiverIdx = s.1.receiverIdx := by rw [hks]
        have hsent₁ : s₁.1.lastSentIdx = s.1.lastSentIdx := by rw [hks]
        have hlf₁ : s₁.1.lf = false := by rw [hks]; exact hinv.lf_false
        rw [h₂.2.1]
        refine ⟨hlf₁, by rw [hks]; exact hinv.corr_none,
          by dsimp only; rw [hsent₁]; exact hinv'.sent_bound,
          by dsimp only; rw [hrcv₁, hsent₁]; have := hinv.rcv_le_sent; omega, ?_, ?_⟩
        · intro x hx
          dsimp only at hx ⊢
          rw [hrcv₁]
          exact hsk₁ x hx
        · intro r' hr'
          dsimp only at hr' ⊢
          rw [hks] at hr' ⊢
          exact hinv.inTransit_wf r' (List.mem_filter.mp hr').1

omit [DecidableEq M] in
theorem invLA_injectH {N rem : ℕ} (_hrem : 0 < rem) {s s' : St} {q : AD × (ℕ × C)}
    {u : Option (ReceiveResult M)} (hinv : InvLA maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((injectH ae G maxSkip (hp N N true) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s)) :
    InvLA maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvLA maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold injectH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at h
    rcases h with ⟨⟨res, s₁⟩, h₁, h₂⟩
    rcases q with ⟨a, i, e⟩
    cases res with
    | none =>
      rcases (mem_support_receiveH_none ae G maxSkip h₁).1 with ⟨ks, hks⟩
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₂
      rw [h₂.2.1, hks]
      exact ⟨hinv'.lf_false, hinv'.corr_none, hinv'.sent_bound, hinv'.rcv_le_sent,
        hinv'.skipped_le, hinv'.inTransit_wf⟩
    | some p =>
      rcases p with ⟨i', m'⟩
      have ⟨rfl, _, hmax, _, _, _, _, hcomp⟩ :=
        mem_support_receiveH_some ae G maxSkip hinv.skipped_le h₁
      have hN : i' ≤ N := by
        have := hinv.rcv_le_sent
        have := hinv.sent_bound
        omega
      have hc : s.1.isCompromised i' = true := hcomp N rfl hN rfl
      exfalso
      simp [HState.isCompromised, hinv.corr_none] at hc

theorem invLA_simulateQ {N : ℕ} {α : Type}
    {p : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)).Domain → Prop}
    [DecidablePred p] (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α) :
    ∀ {rem : ℕ} {s : St} {z : α × St},
      oa.IsQueryBoundP p rem →
      InvLA maxSkip N rem s.1 →
      z ∈ support
        ((simulateQ (implWith ideal ae G maxSkip (hp N N true) (DG G)
          (none : Option (SpecialOps AD M C ProbComp))) oa).run s) →
      z.2.1.lf = false := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro rem s z _ hinv hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hinv.lf_false
  | query_bind t mx ih =>
    intro rem s z hq hinv hz
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, s₁⟩, h₁, h₂⟩
    rcases t with t | (((((q | q) | q) | q) | q) | q)
    · have hs₁ : s₁ = s := mem_support_sampleH h₁
      subst hs₁
      exact ih u (by simpa [hp_inl t] using hq.2 u) hinv h₂
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      exact ih u (by simpa [hp_inr] using hq.2 u) (invLA_transmitH ideal ae G maxSkip hrem hinv h₁) h₂
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      exact ih u (by simpa [hp_inr] using hq.2 u) (invLA_challengeH ideal ae G maxSkip hrem hinv h₁) h₂
    · exact ih u (by simpa [hp_inr] using hq.2 u) (invLA_corruptSenderH G maxSkip q hinv h₁) h₂
    · exact ih u (by simpa [hp_inr] using hq.2 u) (invLA_corruptReceiverH G maxSkip q hinv h₁) h₂
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      exact ih u (by simpa [hp_inr] using hq.2 u) (invLA_deliverH ae G maxSkip hrem hinv h₁) h₂
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      exact ih u (by simpa [hp_inr] using hq.2 u) (invLA_injectH ae G maxSkip hrem hinv h₁) h₂

/-- For `N ≥ q + (maxSkip + 1)`, a `q`-query adversary triggers a lookahead forgery in `A_N^la` with probability `0`. -/
theorem final_la_of_le (A : RatchetAdversary CK MK AD M C) (q N : ℕ)
    (hq : MakesAtMostQueries A q) (hN : q + (maxSkip + 1) ≤ N) :
    𝒟[hybridA ideal ae G maxSkip N true A] {true} = 0 := by
  rw [MakesAtMostQueries] at hq
  have hrun : ∀ b : Bool,
      𝒟[(simulateQ (implWith ideal ae G maxSkip (hp N N true) (DG G)
          (none : Option (SpecialOps AD M C ProbComp))) A).run (hInit b .unknown) >>=
        fun z => pure (hOut true z)] =
      𝒟[(pure false : ProbComp Bool)] := by
    intro b
    have hinv₀ : InvLA maxSkip N q (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown).1 := by
      refine ⟨rfl, rfl, by simpa [hInit] using hN, by simp [hInit], by simp [hInit], by simp [hInit]⟩
    rw [evalDist_bind_congr_of_support _ _ (fun _ => pure false)]
    · exact OracleComp.evalDist_bind_const _ _
    · intro z hz
      have hlf := invLA_simulateQ ideal ae G maxSkip (fun _ => by simp) (fun _ => by simp) A hq hinv₀ hz
      simp [hOut, hlf]
  unfold hybridA hRunWith
  simp only [hp_la]
  rw [evalDist_bind_congr (liftM ($ᵗ Bool : ProbComp Bool)) _ (fun _ => pure false) hrun,
    OracleComp.evalDist_bind_const]
  simp

theorem final_la_idx (A : RatchetAdversary CK MK AD M C) (q : ℕ) (hq : MakesAtMostQueries A q) :
    𝒟[hybridA ideal ae G maxSkip (q + (maxSkip + 1)) true A] {true} = 0 :=
  final_la_of_le ideal ae G maxSkip A q (q + (maxSkip + 1)) hq le_rfl

end FinalLA

/-! ## Main final hybrid: `win = false` invariant -/

/-- Support invariant showing `st.b = b` and `st.win = false` in the final main hybrid `A_N`. -/
structure InvWin (b : Bool) (maxSkip N rem : ℕ) (st : HS) : Prop where
  b_eq : st.b = b
  win_false : st.win = false
  sent_bound : st.lastSentIdx + rem ≤ N
  skipped_le : ∀ x ∈ st.skipped, x ≤ st.receiverIdx
  corr_le : ∀ c, st.senderCorruptedAt = some c → c ≤ st.lastSentIdx
  rcv_le_sent : st.senderCorruptedAt = none → st.receiverIdx ≤ st.lastSentIdx
  inTransit_wf : ∀ r ∈ st.inTransit,
    r.ct.1 = r.idx ∧ r.idx ≤ st.lastSentIdx ∧
      (st.isCompromised r.idx = false → st.receiverIdx < r.idx ∨ r.idx ∈ st.skipped)

theorem InvWin.mono {b : Bool} {maxSkip N rem₁ rem₂ : ℕ} {st : HS}
    (h : InvWin b maxSkip N rem₂ st) (hle : rem₁ ≤ rem₂) : InvWin b maxSkip N rem₁ st :=
  ⟨h.b_eq, h.win_false,
    by have := h.sent_bound; omega,
    h.skipped_le, h.corr_le, h.rcv_le_sent, h.inTransit_wf⟩

section FinalMainWin

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem invWin_transmitH {b : Bool} {N rem : ℕ} (hrem : 0 < rem) {s s' : St} {q : AD × M} {u : Option (ℕ × C)}
    (hinv : InvWin b maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((transmitHWith ideal ae G (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s)) :
    InvWin b maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvWin b maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold transmitHWith at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rcases h with ⟨⟨_, s₁⟩, h₁, ⟨e, s₂⟩, h₂, _, hst', _⟩
    rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
    have hs₂ := mem_support_encIdx ideal ae h₂
    rw [hs₂, hks] at hst'
    rw [hst']
    refine ⟨hinv'.b_eq, hinv'.win_false, ?_, hinv'.skipped_le, ?_, ?_, ?_⟩
    · dsimp only
      have := hinv.sent_bound
      omega
    · intro c hc
      have := hinv'.corr_le c hc
      dsimp only
      omega
    · intro hnone
      have := hinv'.rcv_le_sent hnone
      dsimp only
      omega
    · intro r hr
      dsimp only [HState.isCompromised] at hr ⊢
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · refine ⟨rfl, le_rfl, fun hc => ?_⟩
        dsimp only at hc ⊢
        cases hcorr : s.1.senderCorruptedAt with
        | none =>
          have := hinv'.rcv_le_sent hcorr
          exact Or.inl (by omega)
        | some c =>
          have := hinv'.corr_le c hcorr
          simp only [hcorr, decide_eq_false_iff_not] at hc
          omega
      · rcases hinv'.inTransit_wf r hr with ⟨h1, h2, h3⟩
        exact ⟨h1, by omega, h3⟩

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem invWin_challengeH {b : Bool} {N rem : ℕ} (hrem : 0 < rem) {s s' : St} {q : AD × M × M} {u : Option (ℕ × C)}
    (hinv : InvWin b maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((challengeHWith ideal ae G (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s)) :
    InvWin b maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvWin b maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold challengeHWith at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · simp only [StateT.run_bind, MonadAttach.mem_support_bind, modifyH_run, pure_bind,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rcases h with ⟨⟨_, s₁⟩, h₁, ⟨e, s₂⟩, h₂, _, hst', _⟩
    rcases mem_support_genUpTo G h₁ with ⟨ks, hks⟩
    have hs₂ := mem_support_encIdx ideal ae h₂
    rw [hs₂, hks] at hst'
    rw [hst']
    refine ⟨hinv'.b_eq, hinv'.win_false, ?_, hinv'.skipped_le, ?_, ?_, ?_⟩
    · dsimp only
      have := hinv.sent_bound
      omega
    · intro c hc
      have := hinv'.corr_le c hc
      dsimp only
      omega
    · intro hnone
      have := hinv'.rcv_le_sent hnone
      dsimp only
      omega
    · intro r hr
      dsimp only [HState.isCompromised] at hr ⊢
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · refine ⟨rfl, le_rfl, fun hc => ?_⟩
        dsimp only at hc ⊢
        cases hcorr : s.1.senderCorruptedAt with
        | none =>
          have := hinv'.rcv_le_sent hcorr
          exact Or.inl (by omega)
        | some c =>
          have := hinv'.corr_le c hcorr
          simp only [hcorr, decide_eq_false_iff_not] at hc
          omega
      · rcases hinv'.inTransit_wf r hr with ⟨h1, h2, h3⟩
        exact ⟨h1, by omega, h3⟩

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem invWin_corruptSenderH {b : Bool} {N rem : ℕ} {s s' : St} (q : Unit)
    {u : Option (RatchetSenderState CK)} (hinv : InvWin b maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G (hp N N false) q).run s)) :
    InvWin b maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvWin b maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold corruptSenderH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · simp only [hp_la, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      MonadAttach.mem_support_bind, modifyH_run, pure_bind, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rcases h with ⟨⟨w, s₁⟩, h₁, _, hst', _⟩
    have hs₁ := mem_support_senderKey G h₁
    rw [hs₁] at hst'
    rw [hst']
    refine ⟨hinv'.b_eq, hinv'.win_false, hinv'.sent_bound, hinv'.skipped_le, ?_, ?_, ?_⟩
    · intro c hc
      dsimp only at hc ⊢
      rw [Option.some.injEq] at hc
      subst hc
      cases hcorr : s.1.senderCorruptedAt with
      | none => simp
      | some c₀ => simpa [hcorr] using hinv'.corr_le c₀ hcorr
    · intro hnone
      dsimp only at hnone
      exact nomatch hnone
    · intro r hr
      dsimp only [HState.isCompromised] at hr ⊢
      rcases hinv'.inTransit_wf r hr with ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun hc => h3 ?_⟩
      cases hcorr : s.1.senderCorruptedAt with
      | none => simp [HState.isCompromised, hcorr]
      | some c₀ => simpa [HState.isCompromised, hcorr] using hc

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem invWin_corruptReceiverH {b : Bool} {N rem : ℕ} {s s' : St} (q : Unit)
    {u : Option (RatchetSenderState CK × RatchetReceiverState CK MK)}
    (hinv : InvWin b maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G (hp N N false) q).run s)) :
    InvWin b maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvWin b maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold corruptReceiverH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · simp only [hp_la, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, getH_run, pure_bind,
      MonadAttach.mem_support_bind, modifyH_run, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.ext_iff] at h
    rcases h with ⟨⟨w, s₁⟩, h₁, _, hst', _⟩
    have hs₁ := mem_support_senderKey G h₁
    rw [hs₁] at hst'
    rw [hst']
    exact ⟨hinv'.b_eq, hinv'.win_false, hinv'.sent_bound, hinv'.skipped_le,
      hinv'.corr_le, hinv'.rcv_le_sent, hinv'.inTransit_wf⟩

theorem invWin_deliverH {b : Bool} {N rem : ℕ} (_hrem : 0 < rem) {s s' : St} {q : AD × (ℕ × C)}
    {u : Option (ReceiveResult M)} (hinv : InvWin b maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((deliverH ae G maxSkip (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s)) :
    InvWin b maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvWin b maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold deliverH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · split at h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
      rw [h.2.1]; exact hinv'
    · rename_i _ r hfind
      have hr_mem : r ∈ s.1.inTransit := List.mem_of_find?_eq_some hfind
      have hr_pred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hr_pred
      rcases q with ⟨a, i, e⟩
      rcases hinv.inTransit_wf r hr_mem with ⟨hct1, hr_sent, hr_pos⟩
      have hi_eq : i = r.idx := by
        have := congrArg Prod.fst hr_pred.2
        dsimp only at this
        omega
      rw [StateT.run_bind, MonadAttach.mem_support_bind] at h
      rcases h with ⟨⟨res, s₁⟩, h₁, h₂⟩
      cases res with
      | none =>
        rcases mem_support_receiveH_none ae G maxSkip h₁ with ⟨⟨ks, hks⟩, hnot⟩
        simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff] at h₂
        rw [h₂.2.1, hks]
        refine ⟨hinv'.b_eq, ?_, hinv'.sent_bound, hinv'.skipped_le,
          hinv'.corr_le, hinv'.rcv_le_sent, hinv'.inTransit_wf⟩
        dsimp only
        rw [hinv.win_false, Bool.false_or]
        by_contra hmust
        simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hmust
        exact hnot r.msg rfl (by omega) (by omega) (by simpa [hi_eq] using hr_pos hmust.1)
      | some p =>
        rcases p with ⟨i', m'⟩
        have ⟨rfl, hm', hmax, hsk₁, hsk_keep, ⟨ks, sk, hks⟩, _⟩ :=
          mem_support_receiveH_some ae G maxSkip hinv.skipped_le h₁
        have hm'_eq : m' = r.msg := hm' r.msg rfl
        simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.ext_iff, HState.removeFromTransit] at h₂
        have hrcv₁ : s₁.1.receiverIdx = s.1.receiverIdx := by rw [hks]
        rw [h₂.2.1]
        refine ⟨by rw [hks]; exact hinv.b_eq, ?_,
          by dsimp only; rw [hks]; exact hinv'.sent_bound, ?_, ?_, ?_, ?_⟩
        · dsimp only
          have hwin₁ : s₁.1.win = false := by rw [hks]; exact hinv.win_false
          simp [hwin₁, hi_eq, hm'_eq]
        · intro x hx
          dsimp only at hx ⊢
          rw [hrcv₁]
          exact hsk₁ x hx
        · intro c hc
          dsimp only at hc ⊢
          rw [hks] at hc ⊢
          exact hinv.corr_le c hc
        · intro hnone
          rw [hks] at hnone ⊢
          dsimp only at hnone ⊢
          have := hinv.rcv_le_sent hnone
          omega
        · intro r' hr'
          dsimp only [HState.isCompromised] at hr' ⊢
          rw [hks] at hr' ⊢
          simp only [List.mem_filter, bne_iff_ne] at hr'
          rcases hinv.inTransit_wf r' hr'.1 with ⟨h1, h2, h3⟩
          refine ⟨h1, h2, fun hc => ?_⟩
          have hne : r'.idx ≠ i' := by omega
          simpa [hks] using hsk_keep r'.idx hne (h3 hc)

omit [DecidableEq M] in
theorem invWin_injectH {b : Bool} {N rem : ℕ} (_hrem : 0 < rem) {s s' : St} {q : AD × (ℕ × C)}
    {u : Option (ReceiveResult M)} (hinv : InvWin b maxSkip N rem s.1)
    (h : (u, s') ∈ support
      ((injectH ae G maxSkip (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s)) :
    InvWin b maxSkip N (rem - 1) s'.1 := by
  have hinv' : InvWin b maxSkip N (rem - 1) s.1 := hinv.mono (by omega)
  unfold injectH at h
  simp only [StateT.run_bind, getH_run, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h
    rw [h.2.1]; exact hinv'
  · rw [StateT.run_bind, MonadAttach.mem_support_bind] at h
    rcases h with ⟨⟨res, s₁⟩, h₁, h₂⟩
    rcases q with ⟨a, i, e⟩
    cases res with
    | none =>
      rcases (mem_support_receiveH_none ae G maxSkip h₁).1 with ⟨ks, hks⟩
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₂
      rw [h₂.2.1, hks]
      exact ⟨hinv'.b_eq, hinv'.win_false, hinv'.sent_bound, hinv'.skipped_le,
        hinv'.corr_le, hinv'.rcv_le_sent, hinv'.inTransit_wf⟩
    | some p =>
      rcases p with ⟨i', m'⟩
      have ⟨rfl, _, hmax, hsk₁, hsk_keep, ⟨ks, sk, hks⟩, hi_cases, hcomp⟩ :=
        mem_support_receiveH_some ae G maxSkip hinv.skipped_le h₁
      have hc : s.1.isCompromised i' = true := by
        by_contra hnc
        simp only [Bool.not_eq_true] at hnc
        have hi_sent : i' ≤ s.1.lastSentIdx := by
          rcases hi_cases with hle | hmain
          · cases hcorr : s.1.senderCorruptedAt with
            | none =>
              have := hinv.rcv_le_sent hcorr
              omega
            | some c =>
              have := hinv.corr_le c hcorr
              simp only [HState.isCompromised, hcorr, decide_eq_false_iff_not] at hnc
              omega
          · exact hmain rfl hnc
        have hN : i' ≤ N := by
          have := hinv.sent_bound
          omega
        exact Bool.false_ne_true (hnc.symm.trans (hcomp N rfl hN rfl))
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.ext_iff, HState.removeFromTransit] at h₂
      have hrcv₁ : s₁.1.receiverIdx = s.1.receiverIdx := by rw [hks]
      rw [h₂.2.1]
      refine ⟨by rw [hks]; exact hinv.b_eq, ?_,
        by dsimp only; rw [hks]; exact hinv'.sent_bound, ?_, ?_, ?_, ?_⟩
      · dsimp only
        have hwin₁ : s₁.1.win = false := by rw [hks]; exact hinv.win_false
        simp [hwin₁, hc]
      · intro x hx
        dsimp only at hx ⊢
        rw [hrcv₁]
        exact hsk₁ x hx
      · intro c hc'
        dsimp only at hc' ⊢
        rw [hks] at hc' ⊢
        exact hinv.corr_le c hc'
      · intro hnone
        rw [hks] at hnone
        dsimp only at hnone
        simp [HState.isCompromised, hnone] at hc
      · intro r' hr'
        dsimp only [HState.isCompromised] at hr' ⊢
        rw [hks] at hr' ⊢
        simp only [List.mem_filter, bne_iff_ne] at hr'
        rcases hinv.inTransit_wf r' hr'.1 with ⟨h1, h2, h3⟩
        refine ⟨h1, h2, fun hc' => ?_⟩
        simpa [hks] using hsk_keep r'.idx hr'.2 (h3 hc')

theorem invWin_simulateQ {b : Bool} {N : ℕ} {α : Type}
    {p : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)).Domain → Prop}
    [DecidablePred p] (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α) :
    ∀ {rem : ℕ} {s : St} {z : α × St},
      oa.IsQueryBoundP p rem →
      InvWin b maxSkip N rem s.1 →
      z ∈ support
        ((simulateQ (implWith ideal ae G maxSkip (hp N N false) (DG G)
          (none : Option (SpecialOps AD M C ProbComp))) oa).run s) →
      z.2.1.b = b ∧ z.2.1.win = false := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro rem s z _ hinv hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact ⟨hinv.b_eq, hinv.win_false⟩
  | query_bind t mx ih =>
    intro rem s z hq hinv hz
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, s₁⟩, h₁, h₂⟩
    rcases t with t | (((((q | q) | q) | q) | q) | q)
    · have hs₁ : s₁ = s := mem_support_sampleH h₁
      subst hs₁
      exact ih u (by simpa [hp_inl t] using hq.2 u) hinv h₂
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      exact ih u (by simpa [hp_inr] using hq.2 u) (invWin_transmitH ideal ae G maxSkip hrem hinv h₁) h₂
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      exact ih u (by simpa [hp_inr] using hq.2 u) (invWin_challengeH ideal ae G maxSkip hrem hinv h₁) h₂
    · exact ih u (by simpa [hp_inr] using hq.2 u) (invWin_corruptSenderH G maxSkip q hinv h₁) h₂
    · exact ih u (by simpa [hp_inr] using hq.2 u) (invWin_corruptReceiverH G maxSkip q hinv h₁) h₂
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      exact ih u (by simpa [hp_inr] using hq.2 u) (invWin_deliverH ae G maxSkip hrem hinv h₁) h₂
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      exact ih u (by simpa [hp_inr] using hq.2 u) (invWin_injectH ae G maxSkip hrem hinv h₁) h₂

end FinalMainWin

/-! ## Main final hybrid: `b`-independence coupling -/

/-- Relational coupling of two `ProbComp` computations under shared random choices. -/
inductive RelComp {α₁ α₂ : Type} (R : α₁ → α₂ → Prop) : ProbComp α₁ → ProbComp α₂ → Prop
  | pure {x₁ x₂} (h : R x₁ x₂) : RelComp R (pure x₁) (pure x₂)
  | bind_self {β : Type} (m : ProbComp β) {f₁ : β → ProbComp α₁} {f₂ : β → ProbComp α₂}
      (hf : ∀ b, RelComp R (f₁ b) (f₂ b)) : RelComp R (m >>= f₁) (m >>= f₂)

theorem RelComp.mono {α₁ α₂ : Type} {R R' : α₁ → α₂ → Prop} (himp : ∀ x₁ x₂, R x₁ x₂ → R' x₁ x₂)
    {m₁ : ProbComp α₁} {m₂ : ProbComp α₂} (h : RelComp R m₁ m₂) : RelComp R' m₁ m₂ := by
  induction h with
  | pure hx => exact .pure (himp _ _ hx)
  | bind_self m _ ih => exact .bind_self m ih

theorem RelComp.bind {α₁ α₂ β₁ β₂ : Type} {R : α₁ → α₂ → Prop} {S : β₁ → β₂ → Prop}
    {m₁ : ProbComp α₁} {m₂ : ProbComp α₂} {f₁ : α₁ → ProbComp β₁} {f₂ : α₂ → ProbComp β₂}
    (hm : RelComp R m₁ m₂) (hf : ∀ x₁ x₂, R x₁ x₂ → RelComp S (f₁ x₁) (f₂ x₂)) :
    RelComp S (m₁ >>= f₁) (m₂ >>= f₂) := by
  induction hm with
  | pure hx => simp only [pure_bind]; exact hf _ _ hx
  | bind_self m _ ih => simp only [bind_assoc]; exact .bind_self m ih

theorem RelComp.eq {α : Type} {m₁ m₂ : ProbComp α} (h : RelComp Eq m₁ m₂) : m₁ = m₂ := by
  induction h with
  | pure hx => rw [hx]
  | bind_self m _ ih => congr 1; funext b; exact ih b

theorem RelComp.state_bind {σ₁ σ₂ α₁ α₂ β₁ β₂ : Type}
    {R : α₁ × σ₁ → α₂ × σ₂ → Prop} {S : β₁ × σ₁ → β₂ × σ₂ → Prop}
    {m₁ : StateT σ₁ ProbComp α₁} {m₂ : StateT σ₂ ProbComp α₂}
    {f₁ : α₁ → StateT σ₁ ProbComp β₁} {f₂ : α₂ → StateT σ₂ ProbComp β₂}
    {s₁ : σ₁} {s₂ : σ₂}
    (hm : RelComp R (m₁.run s₁) (m₂.run s₂))
    (hf : ∀ a₁ s₁' a₂ s₂', R (a₁, s₁') (a₂, s₂') →
      RelComp S ((f₁ a₁).run s₁') ((f₂ a₂).run s₂')) :
    RelComp S ((m₁ >>= f₁).run s₁) ((m₂ >>= f₂).run s₂) := by
  simp only [StateT.run_bind]
  exact hm.bind fun ⟨a₁, s₁'⟩ ⟨a₂, s₂'⟩ h => hf a₁ s₁' a₂ s₂' h

theorem relComp_sampleH {α : Type} (p : ProbComp α) {R : α × St → α × St → Prop}
    {s₁ s₂ : St} (h : ∀ a, R (a, s₁) (a, s₂)) :
    RelComp R ((sampleH p : SP α).run s₁) ((sampleH p : SP α).run s₂) := by
  simp only [sampleH_run, map_eq_bind_pure_comp]
  exact .bind_self p fun a => .pure (h a)

/-- Agreement of two hybrid states everywhere except `b` (`s₂.1.b = false`) and `inTransit`. -/
def StateSync (s₁ s₂ : St) : Prop :=
  s₂.1 = { s₁.1 with b := false, inTransit := s₂.1.inTransit } ∧ s₂.2 = s₁.2

def UpdatedKeys (s₁ s₂ s₁' s₂' : St) : Prop :=
  ∃ ks sl, s₁' = ({ s₁.1 with keys := ks }, sl) ∧ s₂' = ({ s₂.1 with keys := ks }, sl)

theorem hstate_self_keys (s : St) : ({ s.1 with keys := s.1.keys }, s.2) = s := by
  rcases s with ⟨⟨⟩, _⟩; rfl

theorem hstate_self_keys_skipped (s : St) :
    ({ s.1 with keys := s.1.keys, skipped := s.1.skipped }, s.2) = s := by
  rcases s with ⟨⟨⟩, _⟩; rfl

theorem StateSync.updatedKeys {s₁ s₂ s₁' s₂' : St} (hs : StateSync s₁ s₂)
    (hu : UpdatedKeys s₁ s₂ s₁' s₂') : StateSync s₁' s₂' := by
  rcases hu with ⟨ks, sl, rfl, rfl⟩
  rcases s₁ with ⟨⟨⟩, sl₁⟩
  rcases s₂ with ⟨⟨⟩, sl₂⟩
  rcases hs with ⟨hst, hsl⟩
  dsimp only at hst hsl ⊢
  subst hsl
  injection hst with h1 h2 h3 h4 h5 h6 _ h8 _ h10 h11 h12
  subst h1 h2 h3 h4 h5 h6 h8 h10 h11 h12
  exact ⟨rfl, rfl⟩

section RelHelpers

variable [SampleableType MK] [SampleableType CK]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

omit [SampleableType CK] in
theorem relComp_genStep {P : Params} {D : ℕ → ProbComp (CK × MK)} {s₁ s₂ : St}
    (hs : StateSync s₁ s₂) :
    RelComp (fun (_, s₁') (_, s₂') => UpdatedKeys s₁ s₂ s₁' s₂')
      ((genStep G P D : SP Unit).run s₁) ((genStep G P D : SP Unit).run s₂) := by
  rcases s₁ with ⟨st₁, sl₁⟩
  rcases s₂ with ⟨st₂, sl₂⟩
  rcases hs with ⟨hst, hsl⟩
  dsimp only at hst hsl
  subst hsl
  have hlen : st₂.keys.length = st₁.keys.length := by rw [hst]
  have hkeys : st₂.keys = st₁.keys := by rw [hst]
  cases sl₂ with
  | seed w =>
    simp only [genStep, StateT.run_mk, hkeys]
    exact .pure ⟨st₁.keys ++ [((G st₁.keys.length).gen w).2],
      .seed ((G st₁.keys.length).gen w).1, rfl, rfl⟩
  | mat pos mt =>
    simp only [genStep, StateT.run_mk, hkeys]
    split
    · exact .bind_self (liftM ($ᵗ MK : ProbComp MK)) fun K =>
        .pure ⟨st₁.keys ++ [K], .mat pos mt, rfl, rfl⟩
    · exact .pure ⟨st₁.keys ++ [mt.2], .seed mt.1, rfl, rfl⟩
  | unknown =>
    simp only [genStep, StateT.run_mk, hkeys]
    split
    · exact .bind_self (liftM ($ᵗ MK : ProbComp MK)) fun K =>
        .pure ⟨st₁.keys ++ [K], .unknown, rfl, rfl⟩
    · exact .bind_self (liftM (D st₁.keys.length)) fun mt =>
        .pure ⟨st₁.keys ++ [mt.2], .seed mt.1, rfl, rfl⟩

omit [SampleableType CK] in
theorem relComp_genN {P : Params} {D : ℕ → ProbComp (CK × MK)} :
    ∀ (n : ℕ) {s₁ s₂ : St}, StateSync s₁ s₂ →
      RelComp (fun (_, s₁') (_, s₂') => UpdatedKeys s₁ s₂ s₁' s₂')
        ((genN G P D n : SP Unit).run s₁) ((genN G P D n : SP Unit).run s₂)
  | 0, s₁, s₂, hs => by
    simp only [genN, StateT.run_pure]
    have hkeys : s₁.1.keys = s₂.1.keys := by rw [hs.1]
    have hsl : s₁.2 = s₂.2 := hs.2.symm
    exact .pure ⟨s₁.1.keys, s₁.2, (hstate_self_keys s₁).symm, by rw [hkeys, hsl]⟩
  | n + 1, s₁, s₂, hs => by
    simp only [genN]
    refine RelComp.state_bind (relComp_genStep G hs) ?_
    rintro _ s₁' _ s₂' hu
    have hs' := hs.updatedKeys hu
    rcases hu with ⟨ks₁, sl₁, rfl, rfl⟩
    refine (relComp_genN n hs').mono ?_
    rintro ⟨_, s₁''⟩ ⟨_, s₂''⟩ ⟨ks₂, sl₂, rfl, rfl⟩
    exact ⟨ks₂, sl₂, rfl, rfl⟩

omit [SampleableType CK] in
theorem relComp_genUpTo {P : Params} {D : ℕ → ProbComp (CK × MK)} {target : ℕ} {s₁ s₂ : St}
    (hs : StateSync s₁ s₂) :
    RelComp (fun (_, s₁') (_, s₂') => UpdatedKeys s₁ s₂ s₁' s₂')
      ((genUpTo G P D target : SP Unit).run s₁) ((genUpTo G P D target : SP Unit).run s₂) := by
  have hlen : s₂.1.keys.length = s₁.1.keys.length := by rw [hs.1]
  simp only [genUpTo, StateT.run_bind, getH_run, pure_bind, hlen]
  exact relComp_genN G (target - s₁.1.keys.length) hs

omit [SampleableType MK] [SampleableType CK] in
theorem relComp_encIdx_same {P : Params} {i : ℕ} {a : AD} {msg : M} {s₁ s₂ : St}
    (hs : StateSync s₁ s₂) :
    RelComp (fun (e₁, s₁') (e₂, s₂') => e₁ = e₂ ∧ s₁' = s₁ ∧ s₂' = s₂)
      ((encIdxWith ideal ae P (none : Option (SpecialOps AD M C ProbComp)) i a msg).run s₁)
      ((encIdxWith ideal ae P (none : Option (SpecialOps AD M C ProbComp)) i a msg).run s₂) := by
  have hkeys : s₂.1.keys = s₁.1.keys := by rw [hs.1]
  have hkind : kind P (none : Option (SpecialOps AD M C ProbComp)) s₂.1 i =
      kind P (none : Option (SpecialOps AD M C ProbComp)) s₁.1 i := by
    rw [hs.1]; rfl
  unfold encIdxWith
  simp only [StateT.run_bind, getH_run, pure_bind, hkind, hkeys]
  split
  · exact relComp_sampleH (ideal (i, a)) fun e => ⟨rfl, rfl, rfl⟩
  · exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
  · split
    · simp only [StateT.run_pure]
      exact .pure ⟨rfl, rfl, rfl⟩
    · exact relComp_sampleH (ideal (i, a)) fun e => ⟨rfl, rfl, rfl⟩

omit [SampleableType MK] [SampleableType CK] in
theorem relComp_encIdx_ideal {N : ℕ} {i : ℕ} {a : AD} {msg₁ msg₂ : M} {s₁ s₂ : St}
    (hs : StateSync s₁ s₂) (hi : i ≤ N) (hcorr : s₁.1.senderCorruptedAt = none) :
    RelComp (fun (e₁, s₁') (e₂, s₂') => e₁ = e₂ ∧ s₁' = s₁ ∧ s₂' = s₂)
      ((encIdxWith ideal ae (hp N N false) (none : Option (SpecialOps AD M C ProbComp)) i a msg₁).run s₁)
      ((encIdxWith ideal ae (hp N N false) (none : Option (SpecialOps AD M C ProbComp)) i a msg₂).run s₂) := by
  have hk₁ : kind (hp N N false) (none : Option (SpecialOps AD M C ProbComp)) s₁.1 i = .ideal := by
    simp [kind, hp, hi, HState.isCompromised, hcorr]
  have hk₂ : kind (hp N N false) (none : Option (SpecialOps AD M C ProbComp)) s₂.1 i = .ideal := by
    rw [hs.1]; exact hk₁
  unfold encIdxWith
  simp only [StateT.run_bind, getH_run, pure_bind, hk₁, hk₂]
  exact relComp_sampleH (ideal (i, a)) fun e => ⟨rfl, rfl, rfl⟩

omit [SampleableType MK] [SampleableType CK] in
theorem relComp_decIdx_none {P : Params} {i : ℕ} {a : AD} {e : C} {s₁ s₂ : St}
    (hs : StateSync s₁ s₂) :
    RelComp (fun (r₁, s₁') (r₂, s₂') => r₁ = r₂ ∧ s₁' = s₁ ∧ s₂' = s₂)
      ((decIdx ae P (none : Option (SpecialOps AD M C ProbComp)) none i a e).run s₁)
      ((decIdx ae P (none : Option (SpecialOps AD M C ProbComp)) none i a e).run s₂) := by
  have hkeys : s₂.1.keys = s₁.1.keys := by rw [hs.1]
  have hkind : kind P (none : Option (SpecialOps AD M C ProbComp)) s₂.1 i =
      kind P (none : Option (SpecialOps AD M C ProbComp)) s₁.1 i := by
    rw [hs.1]; rfl
  unfold decIdx
  simp only [StateT.run_bind, getH_run, pure_bind, hkind, hkeys]
  split
  · simp only [StateT.run_pure]; exact .pure ⟨rfl, rfl, rfl⟩
  · exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
  · simp only [StateT.run_pure]; exact .pure ⟨rfl, rfl, rfl⟩

omit [SampleableType MK] [SampleableType CK] in
theorem hstate_self_skipped (s : St) (sk : List ℕ) :
    ({ s.1 with skipped := sk }, s.2) =
    ({ s.1 with keys := s.1.keys, skipped := sk }, s.2) := by
  rcases s with ⟨⟨⟩, _⟩; rfl

omit [SampleableType MK] [SampleableType CK] in
theorem hstate_keys_then_skipped (s : St) (ks : List MK) (sk : List ℕ) (sl : Slot CK MK) :
    ({ { s.1 with keys := ks } with skipped := sk }, sl) =
    ({ s.1 with keys := ks, skipped := sk }, sl) := by
  rcases s with ⟨⟨⟩, _⟩; rfl

omit [SampleableType CK] in
theorem relComp_receiveH_none {P : Params} {D : ℕ → ProbComp (CK × MK)} {a : AD} {c : ℕ × C}
    {s₁ s₂ : St} (hs : StateSync s₁ s₂) :
    RelComp (fun (res₁, s₁') (res₂, s₂') =>
        res₁ = res₂ ∧ ∃ ks sk sl,
          s₁' = ({ s₁.1 with keys := ks, skipped := sk }, sl) ∧
          s₂' = ({ s₂.1 with keys := ks, skipped := sk }, sl))
      ((receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) none a c).run s₁)
      ((receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) none a c).run s₂) := by
  rcases c with ⟨i, e⟩
  set R : (Option (ℕ × M) × St) → (Option (ℕ × M) × St) → Prop :=
    fun (res₁, s₁') (res₂, s₂') =>
      res₁ = res₂ ∧ ∃ ks sk sl,
        s₁' = ({ s₁.1 with keys := ks, skipped := sk }, sl) ∧
        s₂' = ({ s₂.1 with keys := ks, skipped := sk }, sl)
  have hkeys : s₁.1.keys = s₂.1.keys := by rw [hs.1]
  have hsk : s₂.1.skipped = s₁.1.skipped := by rw [hs.1]
  have hrcv : s₂.1.receiverIdx = s₁.1.receiverIdx := by rw [hs.1]
  have hsent : s₂.1.lastSentIdx = s₁.1.lastSentIdx := by rw [hs.1]
  have hcomp : s₂.1.isCompromised i = s₁.1.isCompromised i := by rw [hs.1]; rfl
  have hsl : s₁.2 = s₂.2 := hs.2.symm
  have hself : s₁ = ({ s₁.1 with keys := s₁.1.keys, skipped := s₁.1.skipped }, s₁.2) ∧
      s₂ = ({ s₂.1 with keys := s₁.1.keys, skipped := s₁.1.skipped }, s₁.2) :=
    ⟨(hstate_self_keys_skipped s₁).symm, by rw [hkeys, ← hsk, hsl]⟩
  unfold receiveH
  simp only [StateT.run_bind, getH_run, pure_bind, hsk, hrcv, hsent, hcomp]
  split
  · refine RelComp.state_bind (relComp_decIdx_none ae hs) ?_
    rintro r₁ s₁' r₂ s₂' ⟨rfl, hs₁', hs₂'⟩
    rw [hs₁', hs₂']
    cases r₁ with
    | none =>
      simp only [StateT.run_pure]
      exact .pure ⟨rfl, s₁.1.keys, s₁.1.skipped, s₁.2, hself.1, hself.2⟩
    | some msg =>
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, hsk]
      exact .pure ⟨rfl, s₁.1.keys, s₁.1.skipped.filter (· != i), s₁.2,
        hstate_self_skipped s₁ _, by rw [hkeys, hsl]⟩
  · split
    · simp only [StateT.run_pure]
      exact .pure ⟨rfl, s₁.1.keys, s₁.1.skipped, s₁.2, hself.1, hself.2⟩
    · split
      · simp only [StateT.run_pure]
        exact .pure ⟨rfl, s₁.1.keys, s₁.1.skipped, s₁.2, hself.1, hself.2⟩
      · refine RelComp.state_bind (relComp_genUpTo G hs) ?_
        rintro _ s₁' _ s₂' hu
        have hs' := hs.updatedKeys hu
        rcases hu with ⟨ks, sl, rfl, rfl⟩
        refine RelComp.state_bind (relComp_decIdx_none ae hs') ?_
        rintro r₁ s₁'' r₂ s₂'' ⟨rfl, hs₁'', hs₂''⟩
        rw [hs₁'', hs₂'']
        cases r₁ with
        | none =>
          simp only [StateT.run_pure]
          exact .pure ⟨rfl, ks, s₁.1.skipped, sl,
            (hstate_keys_then_skipped s₁ ks s₁.1.skipped sl).symm, by rw [← hsk]⟩
        | some msg =>
          simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, hsk]
          exact .pure ⟨rfl, ks, newSkipped s₁.1.receiverIdx i ++ s₁.1.skipped, sl,
            hstate_keys_then_skipped s₁ ks _ sl,
            hstate_keys_then_skipped s₂ ks _ sl⟩

omit [SampleableType CK] in
theorem relComp_receiveH_some {P : Params} {D : ℕ → ProbComp (CK × MK)} {msg₁ msg₂ : M}
    {a : AD} {c : ℕ × C} {s₁ s₂ : St} (hs : StateSync s₁ s₂) :
    RelComp (fun (res₁, s₁') (res₂, s₂') =>
        (res₁ = none ∧ res₂ = none ∨ ∃ i', res₁ = some (i', msg₁) ∧ res₂ = some (i', msg₂)) ∧
        ∃ ks sk sl,
          s₁' = ({ s₁.1 with keys := ks, skipped := sk }, sl) ∧
          s₂' = ({ s₂.1 with keys := ks, skipped := sk }, sl))
      ((receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) (some msg₁) a c).run s₁)
      ((receiveH ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) (some msg₂) a c).run s₂) := by
  rcases c with ⟨i, e⟩
  set R : (Option (ℕ × M) × St) → (Option (ℕ × M) × St) → Prop :=
    fun (res₁, s₁') (res₂, s₂') =>
      (res₁ = none ∧ res₂ = none ∨ ∃ i', res₁ = some (i', msg₁) ∧ res₂ = some (i', msg₂)) ∧
      ∃ ks sk sl,
        s₁' = ({ s₁.1 with keys := ks, skipped := sk }, sl) ∧
        s₂' = ({ s₂.1 with keys := ks, skipped := sk }, sl)
  have hkeys : s₁.1.keys = s₂.1.keys := by rw [hs.1]
  have hsk : s₂.1.skipped = s₁.1.skipped := by rw [hs.1]
  have hrcv : s₂.1.receiverIdx = s₁.1.receiverIdx := by rw [hs.1]
  have hsent : s₂.1.lastSentIdx = s₁.1.lastSentIdx := by rw [hs.1]
  have hcomp : s₂.1.isCompromised i = s₁.1.isCompromised i := by rw [hs.1]; rfl
  have hsl : s₁.2 = s₂.2 := hs.2.symm
  have hself : s₁ = ({ s₁.1 with keys := s₁.1.keys, skipped := s₁.1.skipped }, s₁.2) ∧
      s₂ = ({ s₂.1 with keys := s₁.1.keys, skipped := s₁.1.skipped }, s₁.2) :=
    ⟨(hstate_self_keys_skipped s₁).symm, by rw [hkeys, ← hsk, hsl]⟩
  unfold receiveH decIdx
  simp only [StateT.run_bind, getH_run, pure_bind, hsk, hrcv, hsent, hcomp]
  split
  · simp only [StateT.run_pure, pure_bind, StateT.run_bind, modifyH_run, hsk]
    exact .pure ⟨Or.inr ⟨i, rfl, rfl⟩, s₁.1.keys, s₁.1.skipped.filter (· != i), s₁.2,
      hstate_self_skipped s₁ _, by rw [hkeys, hsl]⟩
  · split
    · simp only [StateT.run_pure]
      exact .pure ⟨Or.inl ⟨rfl, rfl⟩, s₁.1.keys, s₁.1.skipped, s₁.2, hself.1, hself.2⟩
    · split
      · simp only [StateT.run_pure]
        exact .pure ⟨Or.inl ⟨rfl, rfl⟩, s₁.1.keys, s₁.1.skipped, s₁.2, hself.1, hself.2⟩
      · refine RelComp.state_bind (relComp_genUpTo G hs) ?_
        rintro _ s₁' _ s₂' ⟨ks, sl, rfl, rfl⟩
        simp only [StateT.run_pure, pure_bind, StateT.run_bind, modifyH_run, hsk]
        exact .pure ⟨Or.inr ⟨i, rfl, rfl⟩, ks, newSkipped s₁.1.receiverIdx i ++ s₁.1.skipped, sl,
          hstate_keys_then_skipped s₁ ks _ sl,
          hstate_keys_then_skipped s₂ ks _ sl⟩

omit [SampleableType MK] in
theorem relComp_reveal {s₁ s₂ : St} (hs : StateSync s₁ s₂) :
    RelComp (fun (w₁, s₁') (w₂, s₂') => w₁ = w₂ ∧ ∃ sl, s₁' = (s₁.1, sl) ∧ s₂' = (s₂.1, sl))
      ((reveal : SP CK).run s₁) ((reveal : SP CK).run s₂) := by
  rcases s₁ with ⟨st₁, sl₁⟩
  rcases s₂ with ⟨st₂, sl₂⟩
  rcases hs with ⟨_, hsl⟩
  dsimp only at hsl
  subst hsl
  cases sl₂ with
  | unknown =>
    simp only [reveal, StateT.run_mk]
    refine .bind_self (liftM ($ᵗ CK : ProbComp CK)) fun w => .pure ?_
    dsimp only; exact ⟨rfl, .seed w, rfl, rfl⟩
  | seed w =>
    simp only [reveal, StateT.run_mk]
    refine .pure ?_
    dsimp only; exact ⟨rfl, .seed w, rfl, rfl⟩
  | mat pos mt =>
    simp only [reveal, StateT.run_mk]
    refine .bind_self (liftM ($ᵗ CK : ProbComp CK)) fun w => .pure ?_
    dsimp only; exact ⟨rfl, .seed w, rfl, rfl⟩

omit [SampleableType MK] in
theorem relComp_senderKey {s₁ s₂ : St} (hs : StateSync s₁ s₂) :
    RelComp (fun (w₁, s₁') (w₂, s₂') => w₁ = w₂ ∧ ∃ sl, s₁' = (s₁.1, sl) ∧ s₂' = (s₂.1, sl))
      ((senderKey G : SP CK).run s₁) ((senderKey G : SP CK).run s₂) := by
  have hcorr : s₂.1.senderCorruptedAt = s₁.1.senderCorruptedAt := by rw [hs.1]
  have hck : s₂.1.corrKey = s₁.1.corrKey := by rw [hs.1]
  have hsent : s₂.1.lastSentIdx = s₁.1.lastSentIdx := by rw [hs.1]
  have hsl : s₁.2 = s₂.2 := hs.2.symm
  unfold senderKey
  simp only [StateT.run_bind, getH_run, pure_bind, hcorr, hck, hsent]
  split
  · simp only [StateT.run_pure]
    exact .pure ⟨rfl, s₁.2, by cases s₁; rfl, by rw [hsl]⟩
  · exact relComp_reveal hs

end RelHelpers

/-- Coupling invariant relating hybrid runs from `hInit b .unknown` and `hInit false .unknown`. -/
structure RelMain (b : Bool) (N rem : ℕ) (s₁ s₂ : St) : Prop where
  sync : StateSync s₁ s₂
  sent_bound : s₁.1.lastSentIdx + rem ≤ N
  inTransit_rel : List.Forall₂
    (fun r₁ r₂ => r₁.idx = r₂.idx ∧ r₁.ad = r₂.ad ∧ r₁.ct = r₂.ct ∧
      (s₁.1.challengesInTransit.contains r₁.idx = false → r₁.msg = r₂.msg))
    s₁.1.inTransit s₂.1.inTransit

theorem RelMain.mono {b : Bool} {N rem₁ rem₂ : ℕ} {s₁ s₂ : St}
    (h : RelMain b N rem₂ s₁ s₂) (hle : rem₁ ≤ rem₂) : RelMain b N rem₁ s₁ s₂ :=
  ⟨h.sync, le_trans (by omega) h.sent_bound, h.inTransit_rel⟩

theorem forall₂_filter_idx {ch : List ℕ} {i : ℕ}
    {l₁ l₂ : List (Record AD M (ℕ × C))}
    (h : List.Forall₂
      (fun r₁ r₂ => r₁.idx = r₂.idx ∧ r₁.ad = r₂.ad ∧ r₁.ct = r₂.ct ∧
        (ch.contains r₁.idx = false → r₁.msg = r₂.msg)) l₁ l₂) :
    List.Forall₂
      (fun r₁ r₂ => r₁.idx = r₂.idx ∧ r₁.ad = r₂.ad ∧ r₁.ct = r₂.ct ∧
        ((ch.filter (· != i)).contains r₁.idx = false → r₁.msg = r₂.msg))
      (l₁.filter (·.idx != i)) (l₂.filter (·.idx != i)) := by
  induction h with
  | nil => exact .nil
  | @cons r₁ r₂ l₁ l₂ hr _ ih =>
    rcases hr with ⟨hidx, had, hct, hmsg⟩
    simp only [List.filter_cons, hidx]
    split
    · rename_i hne
      refine .cons ⟨hidx, had, hct, fun hcont => hmsg ?_⟩ ih
      rw [← hidx] at hne
      cases hmem : ch.contains r₁.idx
      · rfl
      · exfalso
        have h1 : r₁.idx ∈ ch.filter (· != i) :=
          List.mem_filter.mpr ⟨List.mem_of_elem_eq_true hmem, hne⟩
        have h2 : (ch.filter (· != i)).contains r₁.idx = true := List.elem_eq_true_of_mem h1
        rw [hcont] at h2
        contradiction
    · exact ih

theorem forall₂_find?_inTransit [DecidableEq AD] [DecidableEq C]
    {R : Record AD M (ℕ × C) → Record AD M (ℕ × C) → Prop}
    (hR : ∀ r₁ r₂, R r₁ r₂ → r₁.ad = r₂.ad ∧ r₁.ct = r₂.ct)
    {l₁ l₂ : List (Record AD M (ℕ × C))} (h : List.Forall₂ R l₁ l₂) (a : AD) (c : ℕ × C) :
    (l₁.find? (fun r => r.ad == a && r.ct == c) = none ∧
      l₂.find? (fun r => r.ad == a && r.ct == c) = none) ∨
    ∃ r₁ r₂,
      l₁.find? (fun r => r.ad == a && r.ct == c) = some r₁ ∧
      l₂.find? (fun r => r.ad == a && r.ct == c) = some r₂ ∧ R r₁ r₂ := by
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons r₁ r₂ l₁ l₂ hr _ ih =>
    rcases hR r₁ r₂ hr with ⟨had, hct⟩
    simp only [List.find?_cons]
    rw [had, hct]
    split
    · exact Or.inr ⟨r₁, r₂, rfl, rfl, hr⟩
    · exact ih

theorem forall₂_any_inTransit [DecidableEq AD] [DecidableEq C]
    {R : Record AD M (ℕ × C) → Record AD M (ℕ × C) → Prop}
    (hR : ∀ r₁ r₂, R r₁ r₂ → r₁.ad = r₂.ad ∧ r₁.ct = r₂.ct)
    {l₁ l₂ : List (Record AD M (ℕ × C))} (h : List.Forall₂ R l₁ l₂) (a : AD) (c : ℕ × C) :
    l₁.any (fun r => r.ad == a && r.ct == c) = l₂.any (fun r => r.ad == a && r.ct == c) := by
  induction h with
  | nil => rfl
  | @cons r₁ r₂ l₁ l₂ hr _ ih =>
    rcases hR r₁ r₂ hr with ⟨had, hct⟩
    simp only [List.any_cons]
    rw [had, hct, ih]

theorem forall₂_any_uncompromised {st₁ st₂ : HS} (hs : st₂.senderCorruptedAt = st₁.senderCorruptedAt)
    {R : Record AD M (ℕ × C) → Record AD M (ℕ × C) → Prop}
    (hR : ∀ r₁ r₂, R r₁ r₂ → r₁.idx = r₂.idx)
    {l₁ l₂ : List (Record AD M (ℕ × C))} (h : List.Forall₂ R l₁ l₂) :
    l₁.any (fun r => !st₁.isCompromised r.idx) = l₂.any (fun r => !st₂.isCompromised r.idx) := by
  induction h with
  | nil => rfl
  | @cons r₁ r₂ l₁ l₂ hr _ ih =>
    have hidx := hR r₁ r₂ hr
    have hcomp : st₂.isCompromised r₂.idx = st₁.isCompromised r₁.idx := by
      simp [HState.isCompromised, hs, hidx]
    simp only [List.any_cons, hcomp, ih]

section FinalMainRel

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem relMain_transmitH {b : Bool} {N rem : ℕ} (hrem : 0 < rem) {s₁ s₂ : St} {q : AD × M}
    (hrel : RelMain b N rem s₁ s₂) :
    RelComp (fun (u₁, s₁') (u₂, s₂') => u₁ = u₂ ∧ RelMain b N (rem - 1) s₁' s₂')
      ((transmitHWith ideal ae G (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s₁)
      ((transmitHWith ideal ae G (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s₂) := by
  have hend : s₂.1.ended = s₁.1.ended := by rw [hrel.sync.1]
  have hsent : s₂.1.lastSentIdx = s₁.1.lastSentIdx := by rw [hrel.sync.1]
  unfold transmitHWith
  simp only [StateT.run_bind, getH_run, pure_bind, hend, hsent]
  split
  · simp only [StateT.run_pure]
    exact .pure ⟨rfl, hrel.mono (by omega)⟩
  · refine RelComp.state_bind (relComp_genUpTo G hrel.sync) ?_
    rintro _ s₁' _ s₂' hu
    have hs' := hrel.sync.updatedKeys hu
    rcases hu with ⟨ks, sl, rfl, rfl⟩
    refine RelComp.state_bind (relComp_encIdx_same ideal ae hs') ?_
    rintro e₁ s₁'' e₂ s₂'' ⟨rfl, rfl, rfl⟩
    simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure]
    refine .pure ⟨rfl, ?_⟩
    refine ⟨⟨?_, rfl⟩, ?_, ?_⟩
    · rcases s₁ with ⟨⟨⟩, sl₁⟩; rcases s₂ with ⟨⟨⟩, sl₂⟩
      have hst := hrel.sync.1
      dsimp only at hst ⊢
      injection hst with h1 h2 h3 h4 h5 h6 _ h8 _ h10 h11 h12
      subst h1 h2 h3 h4 h5 h6 h8 h10 h11 h12
      rfl
    · dsimp only
      have := hrel.sent_bound
      omega
    · dsimp only
      exact .cons ⟨rfl, rfl, rfl, fun _ => rfl⟩ hrel.inTransit_rel

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem relMain_challengeH {b : Bool} {N rem : ℕ} (hrem : 0 < rem) {s₁ s₂ : St} {q : AD × M × M}
    (hrel : RelMain b N rem s₁ s₂) :
    RelComp (fun (u₁, s₁') (u₂, s₂') => u₁ = u₂ ∧ RelMain b N (rem - 1) s₁' s₂')
      ((challengeHWith ideal ae G (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s₁)
      ((challengeHWith ideal ae G (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s₂) := by
  have hend : s₂.1.ended = s₁.1.ended := by rw [hrel.sync.1]
  have hcorr : s₂.1.senderCorruptedAt = s₁.1.senderCorruptedAt := by rw [hrel.sync.1]
  have hsent : s₂.1.lastSentIdx = s₁.1.lastSentIdx := by rw [hrel.sync.1]
  unfold challengeHWith
  simp only [StateT.run_bind, getH_run, pure_bind, hend, hcorr, hsent]
  split
  · simp only [StateT.run_pure]
    exact .pure ⟨rfl, hrel.mono (by omega)⟩
  · rename_i hnot
    have hcorr_none : s₁.1.senderCorruptedAt = none := by
      cases hc : s₁.1.senderCorruptedAt with
      | none => rfl
      | some c => simp [hc] at hnot
    refine RelComp.state_bind (relComp_genUpTo G hrel.sync) ?_
    rintro _ s₁' _ s₂' hu
    have hs' := hrel.sync.updatedKeys hu
    rcases hu with ⟨ks, sl, rfl, rfl⟩
    have hi_le : s₁.1.lastSentIdx + 1 ≤ N := by
      have := hrel.sent_bound
      omega
    refine RelComp.state_bind (relComp_encIdx_ideal ideal ae hs' hi_le hcorr_none) ?_
    rintro e₁ s₁'' e₂ s₂'' ⟨rfl, rfl, rfl⟩
    simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure]
    refine .pure ⟨rfl, ?_⟩
    refine ⟨⟨?_, rfl⟩, ?_, ?_⟩
    · rcases s₁ with ⟨⟨⟩, sl₁⟩; rcases s₂ with ⟨⟨⟩, sl₂⟩
      have hst := hrel.sync.1
      dsimp only at hst ⊢
      injection hst with h1 h2 h3 h4 h5 h6 _ h8 _ h10 h11 h12
      subst h1 h2 h3 h4 h5 h6 h8 h10 h11 h12
      rfl
    · dsimp only
      have := hrel.sent_bound
      omega
    · dsimp only
      refine .cons ⟨rfl, rfl, rfl, ?_⟩ ?_
      · simp
      · refine hrel.inTransit_rel.imp fun r₁ r₂ hr => ⟨hr.1, hr.2.1, hr.2.2.1, fun hcont => hr.2.2.2 ?_⟩
        simp only [List.contains_cons, Bool.or_eq_false_iff] at hcont
        exact hcont.2

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem relMain_corruptSenderH {b : Bool} {N rem : ℕ} {s₁ s₂ : St} (q : Unit)
    (hrel : RelMain b N rem s₁ s₂) :
    RelComp (fun (u₁, s₁') (u₂, s₂') => u₁ = u₂ ∧ RelMain b N (rem - 1) s₁' s₂')
      ((corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G (hp N N false) q).run s₁)
      ((corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G (hp N N false) q).run s₂) := by
  have hend : s₂.1.ended = s₁.1.ended := by rw [hrel.sync.1]
  have hcorr : s₂.1.senderCorruptedAt = s₁.1.senderCorruptedAt := by rw [hrel.sync.1]
  have hck : s₂.1.corrKey = s₁.1.corrKey := by rw [hrel.sync.1]
  have hsent : s₂.1.lastSentIdx = s₁.1.lastSentIdx := by rw [hrel.sync.1]
  unfold corruptSenderH
  simp only [StateT.run_bind, getH_run, pure_bind, hend, hcorr, hck, hsent,
    hp_la, Bool.false_eq_true, ↓reduceIte]
  split
  · simp only [StateT.run_pure]
    exact .pure ⟨rfl, hrel.mono (by omega)⟩
  · refine RelComp.state_bind (relComp_senderKey G hrel.sync) ?_
    rintro w₁ s₁' w₂ s₂' ⟨rfl, sl, rfl, rfl⟩
    simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure]
    refine .pure ⟨rfl, ⟨⟨?_, rfl⟩, by dsimp only; have := hrel.sent_bound; omega, hrel.inTransit_rel⟩⟩
    rcases s₁ with ⟨⟨⟩, sl₁⟩; rcases s₂ with ⟨⟨⟩, sl₂⟩
    have hst := hrel.sync.1
    dsimp only at hst ⊢
    injection hst with h1 h2 h3 h4 h5 h6 _ h8 h9 h10 h11 h12
    subst h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12
    rfl

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem relMain_corruptReceiverH {b : Bool} {N rem : ℕ} {s₁ s₂ : St} (q : Unit)
    (hrel : RelMain b N rem s₁ s₂) :
    RelComp (fun (u₁, s₁') (u₂, s₂') => u₁ = u₂ ∧ RelMain b N (rem - 1) s₁' s₂')
      ((corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G (hp N N false) q).run s₁)
      ((corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G (hp N N false) q).run s₂) := by
  have hend : s₂.1.ended = s₁.1.ended := by rw [hrel.sync.1]
  have hch : s₂.1.challengesInTransit = s₁.1.challengesInTransit := by rw [hrel.sync.1]
  have hcorr : s₂.1.senderCorruptedAt = s₁.1.senderCorruptedAt := by rw [hrel.sync.1]
  have hck : s₂.1.corrKey = s₁.1.corrKey := by rw [hrel.sync.1]
  have hsent : s₂.1.lastSentIdx = s₁.1.lastSentIdx := by rw [hrel.sync.1]
  have hrcv : s₂.1.receiverIdx = s₁.1.receiverIdx := by rw [hrel.sync.1]
  have hsk : s₂.1.skipped = s₁.1.skipped := by rw [hrel.sync.1]
  have hkeys : s₂.1.keys = s₁.1.keys := by rw [hrel.sync.1]
  have hany := forall₂_any_uncompromised hcorr (fun _ _ h => h.1) hrel.inTransit_rel
  have hcomp_eq : s₂.1.isCompromised = s₁.1.isCompromised := by
    funext i; simp [HState.isCompromised, hcorr]
  unfold corruptReceiverH
  simp only [StateT.run_bind, getH_run, pure_bind, hend, hch, ← hany,
    hp_la, Bool.false_eq_true, ↓reduceIte]
  split
  · simp only [StateT.run_pure]
    exact .pure ⟨rfl, hrel.mono (by omega)⟩
  · refine RelComp.state_bind (relComp_senderKey G hrel.sync) ?_
    rintro w₁ s₁' w₂ s₂' ⟨rfl, sl, rfl, rfl⟩
    simp only [StateT.run_bind, getH_run, pure_bind, modifyH_run, StateT.run_pure,
      hcorr, hck, hsent, hrcv, hsk, hkeys, hcomp_eq]
    refine .pure ⟨rfl, ⟨⟨?_, rfl⟩, by dsimp only; have := hrel.sent_bound; omega, hrel.inTransit_rel⟩⟩
    rcases s₁ with ⟨⟨⟩, sl₁⟩; rcases s₂ with ⟨⟨⟩, sl₂⟩
    have hst := hrel.sync.1
    dsimp only at hst ⊢
    injection hst with h1 h2 h3 h4 h5 h6 _ h8 h9 h10 h11 h12
    subst h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12
    rfl

theorem relMain_deliverH {b : Bool} {N rem : ℕ} {s₁ s₂ : St} {q : AD × (ℕ × C)}
    (hrel : RelMain b N rem s₁ s₂) :
    RelComp (fun (u₁, s₁') (u₂, s₂') => u₁ = u₂ ∧ RelMain b N (rem - 1) s₁' s₂')
      ((deliverH ae G maxSkip (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s₁)
      ((deliverH ae G maxSkip (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s₂) := by
  have hend : s₂.1.ended = s₁.1.ended := by rw [hrel.sync.1]
  have hrcv : s₂.1.receiverIdx = s₁.1.receiverIdx := by rw [hrel.sync.1]
  have hch : s₂.1.challengesInTransit = s₁.1.challengesInTransit := by rw [hrel.sync.1]
  have hcomp : ∀ i, s₂.1.isCompromised i = s₁.1.isCompromised i := by
    intro i; rw [hrel.sync.1]; rfl
  unfold deliverH
  simp only [StateT.run_bind, getH_run, pure_bind, hend]
  split
  · simp only [StateT.run_pure]
    exact .pure ⟨rfl, hrel.mono (by omega)⟩
  · rcases forall₂_find?_inTransit (fun _ _ h => ⟨h.2.1, h.2.2.1⟩) hrel.inTransit_rel q.1 q.2 with
      ⟨hf₁, hf₂⟩ | ⟨r₁, r₂, hf₁, hf₂, hidx, had, hct, hmsg⟩
    · simp only [hf₁, hf₂, StateT.run_pure]
      exact .pure ⟨rfl, hrel.mono (by omega)⟩
    · simp only [hf₁, hf₂, ← hidx, hrcv, hcomp, hch]
      refine RelComp.state_bind (relComp_receiveH_some ae G maxSkip hrel.sync) ?_
      rintro res₁ s₁' res₂ s₂' ⟨hres, ks, sk, sl, rfl, rfl⟩
      rcases hres with ⟨rfl, rfl⟩ | ⟨i', rfl, rfl⟩
      · simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure]
        refine .pure ⟨rfl, ⟨⟨?_, rfl⟩, by dsimp only; have := hrel.sent_bound; omega, hrel.inTransit_rel⟩⟩
        rcases s₁ with ⟨⟨⟩, sl₁⟩; rcases s₂ with ⟨⟨⟩, sl₂⟩
        have hst := hrel.sync.1
        dsimp only at hst ⊢
        injection hst with h1 h2 h3 h4 h5 h6 _ h8 h9 h10 h11 h12
        subst h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12
        rfl
      · simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, bne_self_eq_false,
          Bool.or_false, HState.removeFromTransit]
        have hout : (if s₁.1.challengesInTransit.contains r₁.idx then none else some r₁.msg) =
            (if s₁.1.challengesInTransit.contains r₁.idx then none else some r₂.msg) := by
          cases hcont : s₁.1.challengesInTransit.contains r₁.idx
          · simp [hmsg hcont]
          · rfl
        rw [hout]
        refine .pure ⟨rfl, ⟨⟨?_, rfl⟩, by dsimp only; have := hrel.sent_bound; omega, ?_⟩⟩
        · rcases s₁ with ⟨⟨⟩, sl₁⟩; rcases s₂ with ⟨⟨⟩, sl₂⟩
          have hst := hrel.sync.1
          dsimp only at hst ⊢
          injection hst with h1 h2 h3 h4 h5 h6 _ h8 h9 h10 h11 h12
          subst h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12
          rfl
        · dsimp only
          exact forall₂_filter_idx hrel.inTransit_rel

omit [DecidableEq M] in
theorem relMain_injectH {b : Bool} {N rem : ℕ} {s₁ s₂ : St} {q : AD × (ℕ × C)}
    (hrel : RelMain b N rem s₁ s₂) :
    RelComp (fun (u₁, s₁') (u₂, s₂') => u₁ = u₂ ∧ RelMain b N (rem - 1) s₁' s₂')
      ((injectH ae G maxSkip (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s₁)
      ((injectH ae G maxSkip (hp N N false) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q).run s₂) := by
  have hend : s₂.1.ended = s₁.1.ended := by rw [hrel.sync.1]
  have hsent : s₂.1.lastSentIdx = s₁.1.lastSentIdx := by rw [hrel.sync.1]
  have hcomp : ∀ i, s₂.1.isCompromised i = s₁.1.isCompromised i := by
    intro i; rw [hrel.sync.1]; rfl
  have hany := forall₂_any_inTransit (fun _ _ h => ⟨h.2.1, h.2.2.1⟩) hrel.inTransit_rel q.1 q.2
  unfold injectH
  simp only [StateT.run_bind, getH_run, pure_bind, hend, ← hany]
  split
  · simp only [StateT.run_pure]
    exact .pure ⟨rfl, hrel.mono (by omega)⟩
  · refine RelComp.state_bind (relComp_receiveH_none ae G maxSkip hrel.sync) ?_
    rintro res₁ s₁' res₂ s₂' ⟨rfl, ks, sk, sl, rfl, rfl⟩
    cases res₁ with
    | none =>
      simp only [StateT.run_pure]
      refine .pure ⟨rfl, ⟨⟨?_, rfl⟩, by dsimp only; have := hrel.sent_bound; omega, hrel.inTransit_rel⟩⟩
      rcases s₁ with ⟨⟨⟩, sl₁⟩; rcases s₂ with ⟨⟨⟩, sl₂⟩
      have hst := hrel.sync.1
      dsimp only at hst ⊢
      injection hst with h1 h2 h3 h4 h5 h6 _ h8 h9 h10 h11 h12
      subst h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12
      rfl
    | some p =>
      rcases p with ⟨i', m'⟩
      simp only [StateT.run_bind, modifyH_run, pure_bind, StateT.run_pure, hcomp, hsent,
        HState.removeFromTransit]
      refine .pure ⟨rfl, ⟨⟨?_, rfl⟩, by dsimp only; have := hrel.sent_bound; omega, ?_⟩⟩
      · rcases s₁ with ⟨⟨⟩, sl₁⟩; rcases s₂ with ⟨⟨⟩, sl₂⟩
        have hst := hrel.sync.1
        dsimp only at hst ⊢
        injection hst with h1 h2 h3 h4 h5 h6 _ h8 h9 h10 h11 h12
        subst h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12
        rfl
      · dsimp only
        exact forall₂_filter_idx hrel.inTransit_rel

theorem relMain_simulateQ {b : Bool} {N : ℕ} {α : Type}
    {p : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)).Domain → Prop}
    [DecidablePred p] (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α) :
    ∀ {rem : ℕ} {s₁ s₂ : St},
      oa.IsQueryBoundP p rem →
      RelMain b N rem s₁ s₂ →
      RelComp (fun z₁ z₂ => z₁.1 = z₂.1)
        ((simulateQ (implWith ideal ae G maxSkip (hp N N false) (DG G)
          (none : Option (SpecialOps AD M C ProbComp))) oa).run s₁)
        ((simulateQ (implWith ideal ae G maxSkip (hp N N false) (DG G)
          (none : Option (SpecialOps AD M C ProbComp))) oa).run s₂) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro rem s₁ s₂ _ _
    simp only [simulateQ_pure, StateT.run_pure]
    exact .pure rfl
  | query_bind t mx ih =>
    intro rem s₁ s₂ hq hrel
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_query_bind]
    rcases t with t | (((((q | q) | q) | q) | q) | q)
    · refine RelComp.state_bind
        (relComp_sampleH (R := fun (u₁, s₁') (u₂, s₂') => u₁ = u₂ ∧ RelMain b N rem s₁' s₂')
          (liftM (query (spec := unifSpec) t)) fun a => ⟨rfl, hrel⟩) ?_
      rintro u₁ s₁' u₂ s₂' ⟨rfl, hrel'⟩
      exact ih u₁ (by simpa [hp_inl t] using hq.2 u₁) hrel'
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      refine RelComp.state_bind (relMain_transmitH ideal ae G hrem hrel) ?_
      rintro u₁ s₁' u₂ s₂' ⟨rfl, hrel'⟩
      exact ih u₁ (by simpa [hp_inr] using hq.2 u₁) hrel'
    · have hrem : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr _))
      refine RelComp.state_bind (relMain_challengeH ideal ae G hrem hrel) ?_
      rintro u₁ s₁' u₂ s₂' ⟨rfl, hrel'⟩
      exact ih u₁ (by simpa [hp_inr] using hq.2 u₁) hrel'
    · refine RelComp.state_bind (relMain_corruptSenderH G q hrel) ?_
      rintro u₁ s₁' u₂ s₂' ⟨rfl, hrel'⟩
      exact ih u₁ (by simpa [hp_inr] using hq.2 u₁) hrel'
    · refine RelComp.state_bind (relMain_corruptReceiverH G q hrel) ?_
      rintro u₁ s₁' u₂ s₂' ⟨rfl, hrel'⟩
      exact ih u₁ (by simpa [hp_inr] using hq.2 u₁) hrel'
    · refine RelComp.state_bind (relMain_deliverH ae G maxSkip hrel) ?_
      rintro u₁ s₁' u₂ s₂' ⟨rfl, hrel'⟩
      exact ih u₁ (by simpa [hp_inr] using hq.2 u₁) hrel'
    · refine RelComp.state_bind (relMain_injectH ae G maxSkip hrel) ?_
      rintro u₁ s₁' u₂ s₂' ⟨rfl, hrel'⟩
      exact ih u₁ (by simpa [hp_inr] using hq.2 u₁) hrel'

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem evalDist_uniformBool_beq (x : Bool) :
    𝒟[(liftM ($ᵗ Bool : ProbComp Bool) : ProbComp Bool) >>= fun b => pure (b == x)] =
    𝒟[(liftM ($ᵗ Bool : ProbComp Bool) : ProbComp Bool)] := by
  change 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => pure (b == x)] =
    𝒟[($ᵗ Bool : ProbComp Bool)]
  cases x
  · conv_rhs => rw [← bind_pure ($ᵗ Bool : ProbComp Bool)]
    ext s hs
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
      Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
      lintegral_fintype, lintegral_fintype, Fintype.sum_bool, Fintype.sum_bool]
    simp [add_comm]
  · simp

/-- For `N ≥ q`, the final main-chain hybrid `A_N` outputs `true` with probability `1 / 2`. -/
theorem final_main_of_le (A : RatchetAdversary CK MK AD M C) (q N : ℕ)
    (hq : MakesAtMostQueries A q) (hN : q ≤ N) :
    𝒟[hybridA ideal ae G maxSkip N false A] {true} = 1 / 2 := by
  rw [MakesAtMostQueries] at hq
  let run := fun b =>
    (simulateQ (implWith ideal ae G maxSkip (hp N N false) (DG G)
      (none : Option (SpecialOps AD M C ProbComp))) A).run (hInit b .unknown)
  have hwin : ∀ b : Bool,
      𝒟[run b >>= fun z => pure (hOut false z)] =
      𝒟[run false >>= fun z => pure (b == z.1)] := by
    intro b
    have hinv₀ : InvWin b maxSkip N q
        (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown).1 := by
      refine ⟨rfl, rfl, by simpa [hInit] using hN, by simp [hInit], by simp [hInit],
        by simp [hInit], by simp [hInit]⟩
    have hrel₀ : RelMain b N q
        (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown)
        (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) false .unknown) := by
      refine ⟨⟨rfl, rfl⟩, by simpa [hInit] using hN, .nil⟩
    have hsim := relMain_simulateQ ideal ae G maxSkip (fun _ => by simp) (fun _ => by simp) A hq hrel₀
    have heq : (run b >>= fun z => pure (b == z.1)) = (run false >>= fun z => pure (b == z.1)) :=
      RelComp.eq (RelComp.bind hsim fun z₁ z₂ hz => .pure (by rw [hz]))
    rw [← heq]
    refine evalDist_bind_congr_of_support (run b) _ _ fun z hz => ?_
    rcases invWin_simulateQ ideal ae G maxSkip (fun _ => by simp) (fun _ => by simp) A hq hinv₀ hz with
      ⟨hb, hw⟩
    simp [hOut, hb, hw]
  unfold hybridA hRunWith
  simp only [hp_la]
  rw [evalDist_bind_congr (liftM ($ᵗ Bool : ProbComp Bool)) _
      (fun b => run false >>= fun z => pure (b == z.1)) hwin,
    OracleComp.evalDist_bind_bind_swap (liftM ($ᵗ Bool : ProbComp Bool)) (run false),
    evalDist_bind_congr (run false) _ (fun _ => (liftM ($ᵗ Bool : ProbComp Bool) : ProbComp Bool))
      (fun z => evalDist_uniformBool_beq z.1),
    OracleComp.evalDist_bind_const]
  simp

theorem final_main_idx (A : RatchetAdversary CK MK AD M C) (q : ℕ) (hq : MakesAtMostQueries A q) :
    𝒟[hybridA ideal ae G maxSkip q false A] {true} = 1 / 2 :=
  final_main_of_le ideal ae G maxSkip A q q hq le_rfl

end FinalMainRel

end CryptoGames.FSAEAD.Thm5.Ends
