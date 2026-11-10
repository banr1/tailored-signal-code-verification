/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
import VCVio.OracleComp.EvalDist.Measure

/-!
# Proof of Lemma 14

**Checked by Lean.** Proves `PrivL14.lemma14_proof` (ACD19 §5.3.3, Lemma 14): in the ideal CKA
world (`b = true`), `redCKAPriv` has bias at most the real PRF-PRNG world (`b = false`) of
`redPRNGPriv` (`DEV-SM24`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.SM.Construction.PrivL14

open Engine

theorem DEq.bind_right_supp {α β : Type} (x : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ a ∈ support x, DEq (f a) (g a)) : DEq (x >>= f) (x >>= g) := fun F => by
  simp only [bind_assoc]
  exact evalDist_bind_congr_of_support x _ _ fun a ha => h a ha F

section GenericEngine

variable {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS : Type}
  {Γ T Sig SS RS M E CCoins : Type} {Γv Sv SSv RSv HS : Type}

def outerFull (oimpl : QueryImpl tspec (StateT OS ProbComp)) :
    QueryImpl (unifSpec + tspec) (StateT OS ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT OS ProbComp) + oimpl

def runHM (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type}
    (x : HM tspec HS α) (h : HS) (os : OS) : ProbComp ((α × HS) × OS) :=
  (simulateQ (outerFull oimpl) (x.run h)).run os

def runEM (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type}
    (x : EM tspec Γv T Sv SSv RSv M E HS α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    ProbComp (α × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)) :=
  (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (outerFull oimpl) (x.run s.1)).run s.2

def privOutP [DecidableEq M] {VPt C HS : Type} (Δ : ℕ) (π : Policy) (b b' : Bool)
    (es : EState VPt M C HS) : ProbComp Bool :=
  if !es.abort && lastLeakGuessAdmissible Δ π.tL π.tStar && canon π.tStar es.g == π.tL then pure (b == b')
  else ($ᵗ Bool : ProbComp Bool)

def evalEng [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) : ProbComp Bool :=
  runEM oimpl (simulateQ (implE hk Δ qep maxSkip cfg π) oa) s >>=
    fun r => privOutP Δ π b r.1 r.2.1

theorem runEM_pure (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type} (a : α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (pure a : EM tspec Γv T Sv SSv RSv M E HS α) s = pure (a, s) := by
  simp [runEM]

theorem runEM_bind (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α β : Type}
    (x : EM tspec Γv T Sv SSv RSv M E HS α)
    (f : α → EM tspec Γv T Sv SSv RSv M E HS β)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (x >>= f) s = runEM oimpl x s >>= fun r => runEM oimpl (f r.1) r.2 := by
  simp [runEM, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

theorem runEM_get (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (get : EM tspec Γv T Sv SSv RSv M E HS _) s = pure (s.1, s) := by
  simp [runEM]

theorem runEM_modify (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (f : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS →
      EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (modify f : EM tspec Γv T Sv SSv RSv M E HS Unit) s =
      pure ((), (f s.1, s.2)) := by
  simp [runEM]

theorem runEM_abortE (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (abortE : EM tspec Γv T Sv SSv RSv M E HS Unit) s =
      pure ((), ({ s.1 with abort := true }, s.2)) := by
  simp [abortE, runEM_modify]

theorem ite_bool_false {α : Type} {b : Bool} (hb : b = false) (x y : α) :
    (if b = true then x else y) = y := by
  rw [hb]; rfl

theorem ite_bool_true {α : Type} {b : Bool} (hb : b = true) (x y : α) :
    (if b = true then x else y) = x := by
  rw [hb]; rfl

theorem runEM_abort_pure (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type} (a : α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (do abortE; pure a) s = pure (a, ({ s.1 with abort := true }, s.2)) := by
  rw [runEM_bind, runEM_abortE, pure_bind, runEM_pure]

theorem runEM_modify_pure (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type}
    (f : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS →
      EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (a : α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (do modify f; pure a) s = pure (a, (f s.1, s.2)) := by
  rw [runEM_bind, runEM_modify, pure_bind, runEM_pure]

theorem runEM_liftH (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type}
    (x : HM tspec HS α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (liftH x : EM tspec Γv T Sv SSv RSv M E HS α) s =
      (fun r => (r.1.1, ({ s.1 with h := r.1.2 }, r.2))) <$> runHM oimpl x s.1.h s.2 := by
  change (fun r => (r.1.1, (r.1.2, r.2))) <$>
      (simulateQ (outerFull oimpl) (liftH x s.1)).run s.2 = _
  simp [runHM, liftH]

theorem runEM_coinsE (oimpl : QueryImpl tspec (StateT OS ProbComp)) (n : ℕ)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (coinsE n : EM tspec Γv T Sv SSv RSv M E HS _) s =
      (fun x => (x, s)) <$> (query (spec := unifSpec) n : ProbComp _) := by
  simp [runEM, coinsE, outerFull, StateT.run_lift, simulateQ_query]

theorem simulateQ_outerFull_sampleT (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (α : Type) [SampleableType α] (os : OS) :
    (simulateQ (outerFull oimpl) (sampleT (tspec := tspec) α)).run os =
      (·, os) <$> ($ᵗ α : ProbComp α) := by
  simp [sampleT, outerFull, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

theorem simulateQ_outerFull_privOut [DecidableEq M] {VPt C HS : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp)) (Δ : ℕ) (π : Policy) (b b' : Bool)
    (es : EState VPt M C HS) (os : OS) :
    Prod.fst <$> (simulateQ (outerFull oimpl) (privOut Δ π b b' es)).run os =
      privOutP Δ π b b' es := by
  unfold privOut privOutP
  split <;> simp [outerFull, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

theorem evalEng_pure [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b b' : Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    evalEng oimpl hk Δ qep maxSkip cfg π b (pure b') s = privOutP Δ π b b' s.1 := by
  simp [evalEng, runEM_pure]

theorem evalEng_query_bind [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    {α : Type} (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (q : OracleQuery (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (k : α → OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    evalEng oimpl hk Δ qep maxSkip cfg π b (liftM q >>= k) s =
      runEM oimpl (implE hk Δ qep maxSkip cfg π q.input) s >>=
        fun r => evalEng oimpl hk Δ qep maxSkip cfg π b (k (q.cont r.1)) r.2 := by
  simp [evalEng, simulateQ_bind, simulateQ_query, runEM_bind, bind_assoc]

theorem evalEng_invalid [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hinv : lastLeakGuessAdmissible Δ π.tL π.tStar = false) :
    DEq (evalEng oimpl hk Δ qep maxSkip cfg π b oa s) ($ᵗ Bool : ProbComp Bool) := by
  unfold evalEng
  refine (DEq.bind_right _ fun r => ?_).trans (DEq.bind_const _ _)
  simp [privOutP, hinv]
  exact DEq.refl _

/-! ### Doomed states -/

def MissedTL {St Msg C : Type} (tL : Option ℕ) (g : SM.GameState St Msg C) : Prop :=
  ∃ l, tL = some l ∧ l ≤ g.epoch .A ∧ l ≤ g.epoch .B ∧ l < max (g.epoch .A) (g.epoch .B) ∧
    l ∉ g.leaks

def Doom {VPt M C HS : Type} (tL : Option ℕ) (es : EState VPt M C HS) : Prop :=
  es.abort = true ∨ MissedTL tL es.g

theorem canon_ne_of_not_mem {St Msg C : Type} {tStar l : ℕ} {g : SM.GameState St Msg C}
    (h : l ∉ g.leaks) : (canon tStar g == some l) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have hmem := List.max?_mem heq
  rw [List.mem_filter] at hmem
  exact h hmem.1

theorem privOutP_of_doom [DecidableEq M] {VPt C HS : Type} (Δ : ℕ) (π : Policy) (b b' : Bool)
    (es : EState VPt M C HS) (hd : Doom π.tL es) :
    privOutP Δ π b b' es = ($ᵗ Bool : ProbComp Bool) := by
  rcases hd with hab | ⟨l, htL, -, -, -, hnl⟩
  · simp [privOutP, hab]
  · simp [privOutP, htL, canon_ne_of_not_mem hnl]

theorem MissedTL.leak {St Msg C : Type} {tL : Option ℕ} {g : SM.GameState St Msg C} {l' : ℕ}
    (hm : MissedTL tL g) (hl' : ∀ l, tL = some l → l < l') :
    MissedTL tL (g.leak l') := by
  rcases hm with ⟨l, htL, hA, hB, hmax, hnl⟩
  refine ⟨l, htL, hA, hB, hmax, ?_⟩
  simp only [SM.GameState.leak, List.mem_cons, not_or]
  refine ⟨?_, hnl⟩
  have hlt := hl' l htL
  cases g.tL <;> simp [maxOpt] <;> omega

theorem MissedTL.epMgmt {St Msg C : Type} {tL : Option ℕ} {g s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hm : MissedTL tL g) (he : g.epMgmt Δ qep P bad = some s₁) :
    MissedTL tL s₁ := by
  unfold SM.GameState.epMgmt at he
  split at he
  · split at he
    · contradiction
    · injection he with he
      subst he
      set g₁ := if bad && !g.safeCh Δ P then g.leak (g.epoch P + 1) else g
      have hm₁ : MissedTL tL g₁ := by
        change MissedTL tL (if bad && !g.safeCh Δ P then g.leak (g.epoch P + 1) else g)
        split
        · refine hm.leak fun l htL => ?_
          rcases hm with ⟨l₀, htL₀, hA, hB, -, -⟩
          rw [htL] at htL₀; injection htL₀ with htL₀; subst htL₀
          cases P <;> omega
        · exact hm
      rcases hm₁ with ⟨l, htL, hA, hB, hmax, hnl⟩
      refine ⟨l, htL, ?_, ?_, ?_, hnl⟩
      · cases P <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte] <;> omega
      · cases P <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte] <;> omega
      · cases P <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte] <;> omega
  · split at he
    · contradiction
    · injection he with he; subst he; exact hm

theorem MissedTL.record {St Msg C : Type} {tL : Option ℕ} {s₁ : SM.GameState St Msg C}
    {Δ : ℕ} {P : Party} {st' : St} {r : Record Msg C} {isChall : Bool}
    (hm : MissedTL tL s₁) : MissedTL tL (s₁.record Δ P st' r isChall) := by
  rcases hm with ⟨l, htL, hA, hB, hmax, hnl⟩
  exact ⟨l, htL, hA, hB, hmax, hnl⟩

theorem MissedTL.accept {St Msg C : Type} {tL : Option ℕ} {s : SM.GameState St Msg C}
    {P : Party} {st' : St} {pos : Pos} (hm : MissedTL tL s) :
    MissedTL tL (s.accept P st' pos) := by
  rcases hm with ⟨l, htL, hA, hB, hmax, hnl⟩
  refine ⟨l, htL, ?_, ?_, ?_, hnl⟩
  · cases P <;> simp [SM.GameState.accept, SM.GameState.delete, Function.update] <;> omega
  · cases P <;> simp [SM.GameState.accept, SM.GameState.delete, Function.update] <;> omega
  · cases P <;> simp [SM.GameState.accept, SM.GameState.delete, Function.update] <;> omega

theorem MissedTL.afterCorr {St Msg C : Type} {tL : Option ℕ} {s : SM.GameState St Msg C}
    {P : Party} (hm : MissedTL tL s) : MissedTL tL (s.afterCorr P) := by
  rcases hm with ⟨l, htL, hA, hB, hmax, hnl⟩
  unfold SM.GameState.afterCorr
  set s₁ : SM.GameState St Msg C :=
    { s with comp := (s.trans.filter (fun r : Record Msg C => r.pos.sender == P.other)).map
                       (fun r : Record Msg C => r.pos) ++ s.comp }
  have hm₁ : MissedTL tL s₁ := ⟨l, htL, hA, hB, hmax, hnl⟩
  have hm₂ : MissedTL tL (s₁.leak (max (s.epoch .A) (s.epoch .B))) := by
    refine hm₁.leak fun l₀ htL₀ => ?_
    rw [htL] at htL₀; injection htL₀ with htL₀; subst htL₀; exact hmax
  rcases hm₂ with ⟨l₀, htL₀, hA₀, hB₀, hmax₀, hnl₀⟩
  exact ⟨l₀, htL₀, hA₀, hB₀, hmax₀, hnl₀⟩

theorem runEM_liftH_abort_g (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type}
    (x : HM tspec HS α) (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    {r : α × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)}
    (hr : r ∈ support (runEM oimpl (liftH x) s)) :
    r.2.1.abort = s.1.abort ∧ r.2.1.g = s.1.g := by
  rw [runEM_liftH, support_map] at hr
  rcases hr with ⟨⟨⟨a, h'⟩, os'⟩, -, rfl⟩
  exact ⟨rfl, rfl⟩

theorem runEM_commitE_missed [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    {tL : Option ℕ} (P : Party) (old new : VP Γv T Sv SSv RSv) (pos : Pos)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hm : MissedTL tL s.1.g)
    {r : Option (Ctx Γv T Sv SSv RSv M E) ×
      (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)}
    (hr : r ∈ support (runEM oimpl (commitE hk s.1.g P old new pos) s)) :
    Doom tL r.2.1 ∧ ∀ s₁, r.1 = some s₁ → MissedTL tL s₁ := by
  unfold commitE at hr
  rw [runEM_bind, mem_support_bind_iff] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  have ⟨hab₁, hg₁⟩ := runEM_liftH_abort_g oimpl _ s hr₁
  cases hres : r₁.1 with
  | none =>
    rw [hres, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨Or.inl rfl, fun _ h => by contradiction⟩
  | some new' =>
    rw [hres, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    refine ⟨Or.inr (hg₁ ▸ hm), fun s₁ hs₁ => ?_⟩
    injection hs₁ with hs₁; subst hs₁
    rcases hm.accept (P := P) (st' := new) (pos := pos) with ⟨l, htL, hA, hB, hmax, hnl⟩
    exact ⟨l, htL, hA, hB, hmax, hnl⟩

theorem Doom.runEM_implE [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hd : Doom π.tL s.1)
    {r : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q ×
      (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)}
    (hr : r ∈ support (runEM oimpl (implE hk Δ qep maxSkip cfg π q) s)) :
    Doom π.tL r.2.1 := by
  rcases q with n | ⟨⟨⟨⟨⟨P, m, rcoins⟩ | ⟨P, m₀, m₁, rcoins⟩⟩ | ⟨P, c⟩⟩ | ⟨P, c⟩⟩ | P⟩
  ·
    change r ∈ support (runEM oimpl (coinsE n) s) at hr
    rw [runEM_coinsE, support_map] at hr
    rcases hr with ⟨_, -, rfl⟩
    exact hd
  ·
    change r ∈ support (runEM oimpl (transmitE hk Δ qep π ⟨P, m, rcoins⟩) s) at hr
    unfold transmitE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    rcases hd with hab | hm
    · simp [hab, runEM_pure] at hr; subst hr; exact Or.inl hab
    · cases hcond : s.1.abort || s.1.g.win
      · rw [ite_bool_false hcond] at hr
        cases hep : s.1.g.epMgmt Δ qep P rcoins.isSome with
        | none =>
          rw [hep, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr hm
        | some s₁ =>
          rw [hep] at hr
          dsimp only at hr
          cases hld : π.leakDoom s.1.g s₁
          · rw [ite_bool_false hld, runEM_bind, mem_support_bind_iff] at hr
            rcases hr with ⟨r₁, hr₁, hr⟩
            have ⟨_, hg₁⟩ := runEM_liftH_abort_g oimpl _ s hr₁
            cases hvs : r₁.1 with
            | none =>
              rw [hvs, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact Or.inl rfl
            | some stc =>
              rcases stc with ⟨st', ct⟩
              rw [hvs, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr
              exact Or.inr ((hm.epMgmt hep).record)
          · rw [ite_bool_true hld, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inl rfl
      · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr hm
  ·
    change r ∈ support (runEM oimpl (challE hk Δ qep cfg π ⟨P, m₀, m₁, rcoins⟩) s) at hr
    unfold challE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    rcases hd with hab | hm
    · simp [hab, runEM_pure] at hr; subst hr; exact Or.inl hab
    · cases hcond : s.1.abort || s.1.g.win
      · rw [ite_bool_false hcond] at hr
        cases hep : s.1.g.epMgmt Δ qep P rcoins.isSome with
        | none =>
          rw [hep, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr hm
        | some s₁ =>
          rw [hep] at hr
          dsimp only at hr
          cases hsc : !(s₁.safeCh Δ P) || !(cfg.challAllowedIn (s₁.epoch P))
          · rw [ite_bool_false hsc] at hr
            cases hld : π.leakDoom s.1.g s₁
            · rw [ite_bool_false hld, runEM_bind, mem_support_bind_iff] at hr
              rcases hr with ⟨r₁, hr₁, hr⟩
              cases hvs : r₁.1 with
              | none =>
                rw [hvs, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr; exact Or.inl rfl
              | some stc =>
                rcases stc with ⟨st', ct⟩
                rw [hvs, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr
                exact Or.inr ((hm.epMgmt hep).record)
            · rw [ite_bool_true hld, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact Or.inl rfl
          · rw [ite_bool_true hsc, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inr hm
      · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr hm
  ·
    change r ∈ support (runEM oimpl (deliverE hk maxSkip cfg ⟨P, c⟩) s) at hr
    unfold deliverE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    rcases hd with hab | hm
    · simp [hab, runEM_pure] at hr; subst hr; exact Or.inl hab
    · cases hcond : s.1.abort || s.1.g.win
      · rw [ite_bool_false hcond] at hr
        cases hit : s.1.g.inTransit P.other c with
        | none =>
          rw [hit, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr hm
        | some rec =>
          rw [hit] at hr
          dsimp only at hr
          rw [runEM_bind, mem_support_bind_iff] at hr
          rcases hr with ⟨r₁, hr₁, hr⟩
          have ⟨hab₁, hg₁⟩ := runEM_liftH_abort_g oimpl _ s hr₁
          cases hvr : r₁.1 with
          | none =>
            rw [hvr, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inl rfl
          | some vr =>
            cases vr with
            | none =>
              rw [hvr] at hr
              dsimp only at hr
              split at hr
              · rw [runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr
                rcases hg₁ ▸ hm with ⟨l, htL, hA, hB, hmax, hnl⟩
                exact Or.inr ⟨l, htL, hA, hB, hmax, hnl⟩
              · rw [runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr; exact Or.inr (hg₁ ▸ hm)
            | some res =>
              rcases res with ⟨st', t', i', m'⟩
              rw [hvr] at hr
              dsimp only at hr
              rw [runEM_bind, mem_support_bind_iff] at hr
              rcases hr with ⟨r₂, hr₂, hr⟩
              have ⟨hd₂, hacc₂⟩ := runEM_commitE_missed oimpl hk P (r₁.2.1.g.st P) st' rec.pos r₁.2
                (hg₁ ▸ hm) (hg₁ ▸ hr₂)
              cases hcm : r₂.1 with
              | none =>
                rw [hcm, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr; exact hd₂
              | some s₁ =>
                rw [hcm] at hr
                dsimp only at hr
                rw [runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                subst hr
                have hm₁ := hacc₂ s₁ hcm
                dsimp only
                split
                · rcases hm₁ with ⟨l, htL, hA, hB, hmax, hnl⟩
                  exact Or.inr ⟨l, htL, hA, hB, hmax, hnl⟩
                · exact Or.inr hm₁
      · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr hm
  ·
    change r ∈ support (runEM oimpl (injectE hk Δ qep cfg ⟨P, c⟩) s) at hr
    unfold injectE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    rcases hd with hab | hm
    · simp [hab, runEM_pure] at hr; subst hr; exact Or.inl hab
    · cases hcond :
          s.1.abort || s.1.g.win || (s.1.g.inTransit P.other c).isSome || !(s.1.g.safeInj Δ)
      · rw [ite_bool_false hcond, runEM_bind, mem_support_bind_iff] at hr
        rcases hr with ⟨r₁, hr₁, hr⟩
        have ⟨_, hg₁⟩ := runEM_liftH_abort_g oimpl _ s hr₁
        cases hvr : r₁.1 with
        | none =>
          rw [hvr, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inl rfl
        | some vr =>
          cases vr with
          | none =>
            rw [hvr, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inr (hg₁ ▸ hm)
          | some res =>
            rcases res with ⟨st', t', i', m'⟩
            rw [hvr] at hr
            dsimp only at hr
            by_cases hqep : qep + 1 < t'
            · simp [hqep, runEM_pure] at hr; subst hr; exact Or.inr (hg₁ ▸ hm)
            · simp only [hqep, ↓reduceIte] at hr
              cases htriv : s.1.g.trivial Δ ⟨P.other, t', i'⟩
              · rw [ite_bool_false htriv] at hr
                split at hr
                · rw [runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr
                  rcases hg₁ ▸ hm with ⟨l, htL, hA, hB, hmax, hnl⟩
                  exact Or.inr ⟨l, htL, hA, hB, hmax, hnl⟩
                · rw [runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr; exact Or.inr (hg₁ ▸ hm)
              · rw [ite_bool_true htriv, runEM_bind, mem_support_bind_iff] at hr
                rcases hr with ⟨r₂, hr₂, hr⟩
                have ⟨hd₂, hacc₂⟩ := runEM_commitE_missed oimpl hk P (r₁.2.1.g.st P) st'
                  ⟨P.other, t', i'⟩ r₁.2 (hg₁ ▸ hm) (hg₁ ▸ hr₂)
                cases hcm : r₂.1 with
                | none =>
                  rw [hcm, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr; exact hd₂
                | some s₁ =>
                  rw [hcm, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr; exact Or.inr (hacc₂ s₁ hcm)
      · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr hm
  ·
    change r ∈ support (runEM oimpl (corrE hk π P) s) at hr
    unfold corrE at hr
    rw [runEM_bind, runEM_get, pure_bind] at hr
    dsimp only at hr
    rcases hd with hab | hm
    · simp [hab, runEM_pure] at hr; subst hr; exact Or.inl hab
    · cases hcond : s.1.abort || s.1.g.win || !(s.1.g.corrAllowed P)
      · rw [ite_bool_false hcond] at hr
        cases hcd : π.leakDoom s.1.g (s.1.g.afterCorr P) || π.corrDoom s.1.g P
        · rw [ite_bool_false hcd, runEM_bind, mem_support_bind_iff] at hr
          rcases hr with ⟨r₁, hr₁, hr⟩
          cases hrev : r₁.1 with
          | none =>
            rw [hrev, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inl rfl
          | some st =>
            rw [hrev, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr
            exact Or.inr hm.afterCorr
        · rw [ite_bool_true hcd, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inl rfl
      · rw [ite_bool_true hcond, runEM_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr hm

theorem Doom.runEM_simulateQ [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    {α : Type} (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hd : Doom π.tL s.1)
    {r : α × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)}
    (hr : r ∈ support (runEM oimpl (simulateQ (implE hk Δ qep maxSkip cfg π) oa) s)) :
    Doom π.tL r.2.1 := by
  induction oa using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp [runEM_pure] at hr; subst hr; exact hd
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, runEM_bind, mem_support_bind_iff] at hr
    rcases hr with ⟨r₁, hr₁, hr⟩
    exact ih r₁.1 r₁.2 (Doom.runEM_implE oimpl hk Δ qep maxSkip cfg π q s hd hr₁) hr

theorem evalEng_doom [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hd : Doom π.tL s.1) :
    DEq (evalEng oimpl hk Δ qep maxSkip cfg π b oa s) ($ᵗ Bool : ProbComp Bool) := by
  unfold evalEng
  refine (DEq.bind_right_supp _ fun r hr => ?_).trans (DEq.bind_const _ _)
  exact privOutP_of_doom Δ π b r.1 r.2.1
    (Doom.runEM_simulateQ oimpl hk Δ qep maxSkip cfg π oa s hd hr) ▸ DEq.refl _

end GenericEngine

/-! ### Lockstep invariant `Sync` -/

section SyncInvariant

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

def eraseSt {St Msg C : Type} (g : SM.GameState St Msg C) : SM.GameState Unit Msg C :=
  { st := fun _ => ()
    epoch := g.epoch
    idx := g.idx
    tL := g.tL
    trans := g.trans
    chall := g.chall
    comp := g.comp
    maxAcc := g.maxAcc
    b := g.b
    win := g.win
    leaks := g.leaks
    corrs := g.corrs }

theorem eraseSt_epoch {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) : gL.epoch = gR.epoch :=
  congrArg SM.GameState.epoch he

theorem eraseSt_idx {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) : gL.idx = gR.idx :=
  congrArg SM.GameState.idx he

theorem eraseSt_chall {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) : gL.chall = gR.chall :=
  congrArg SM.GameState.chall he

theorem eraseSt_b {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) : gL.b = gR.b :=
  congrArg SM.GameState.b he

theorem eraseSt_win {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) : gL.win = gR.win :=
  congrArg SM.GameState.win he

theorem eraseSt_leaks {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) : gL.leaks = gR.leaks :=
  congrArg SM.GameState.leaks he

theorem eraseSt_safeCh {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (Δ : ℕ) (P : Party) :
    gL.safeCh Δ P = gR.safeCh Δ P := by
  change (eraseSt gL).safeCh Δ P = (eraseSt gR).safeCh Δ P; rw [he]

theorem eraseSt_safeInj {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (Δ : ℕ) :
    gL.safeInj Δ = gR.safeInj Δ := by
  change (eraseSt gL).safeInj Δ = (eraseSt gR).safeInj Δ; rw [he]

theorem eraseSt_inTransit {StL StR Msg C : Type} [DecidableEq C] {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (Q : Party) (c : C) :
    gL.inTransit Q c = gR.inTransit Q c := by
  change (eraseSt gL).inTransit Q c = (eraseSt gR).inTransit Q c; rw [he]

theorem eraseSt_mustBeCorrect {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (maxSkip : ℕ) (P : Party)
    (r : Record Msg C) :
    gL.mustBeCorrect maxSkip P r = gR.mustBeCorrect maxSkip P r := by
  change (eraseSt gL).mustBeCorrect maxSkip P r = (eraseSt gR).mustBeCorrect maxSkip P r; rw [he]

theorem eraseSt_trivial {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (Δ : ℕ) (pos : Pos) :
    gL.trivial Δ pos = gR.trivial Δ pos := by
  change (eraseSt gL).trivial Δ pos = (eraseSt gR).trivial Δ pos; rw [he]

theorem eraseSt_corrAllowed {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (P : Party) :
    gL.corrAllowed P = gR.corrAllowed P := by
  change (eraseSt gL).corrAllowed P = (eraseSt gR).corrAllowed P; rw [he]

theorem eraseSt_canon {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (tStar : ℕ) :
    canon tStar gL = canon tStar gR := by
  change canon tStar (eraseSt gL) = canon tStar (eraseSt gR); rw [he]

theorem eraseSt_leakDoom {StL StR Msg C : Type} {gL s₁L : SM.GameState StL Msg C}
    {gR s₁R : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR)
    (he₁ : eraseSt s₁L = eraseSt s₁R) (π : Policy) :
    π.leakDoom gL s₁L = π.leakDoom gR s₁R := by
  change π.leakDoom (eraseSt gL) (eraseSt s₁L) = π.leakDoom (eraseSt gR) (eraseSt s₁R)
  rw [he, he₁]

theorem eraseSt_corrDoom {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (π : Policy) (P : Party) :
    π.corrDoom gL P = π.corrDoom gR P := by
  change π.corrDoom (eraseSt gL) P = π.corrDoom (eraseSt gR) P; rw [he]

theorem eraseSt_record {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (Δ : ℕ) (P : Party)
    (stL : StL) (stR : StR) (r : Record Msg C) (isChall : Bool) :
    eraseSt (gL.record Δ P stL r isChall) = eraseSt (gR.record Δ P stR r isChall) := by
  have hL : eraseSt (gL.record Δ P stL r isChall) = (eraseSt gL).record Δ P () r isChall := by
    simp only [eraseSt, SM.GameState.record, SM.GameState.safeCh]; congr 1
  have hR : eraseSt (gR.record Δ P stR r isChall) = (eraseSt gR).record Δ P () r isChall := by
    simp only [eraseSt, SM.GameState.record, SM.GameState.safeCh]; congr 1
  rw [hL, hR, he]

theorem eraseSt_accept {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (P : Party)
    (stL : StL) (stR : StR) (pos : Pos) :
    eraseSt (gL.accept P stL pos) = eraseSt (gR.accept P stR pos) := by
  have hL : eraseSt (gL.accept P stL pos) = (eraseSt gL).accept P () pos := by
    simp only [eraseSt, SM.GameState.accept, SM.GameState.delete]
  have hR : eraseSt (gR.accept P stR pos) = (eraseSt gR).accept P () pos := by
    simp only [eraseSt, SM.GameState.accept, SM.GameState.delete]
  rw [hL, hR, he]

theorem eraseSt_afterCorr {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) (P : Party) :
    eraseSt (gL.afterCorr P) = eraseSt (gR.afterCorr P) := by
  change (eraseSt gL).afterCorr P = (eraseSt gR).afterCorr P; rw [he]

theorem epMgmt_map_eraseSt {St Msg C : Type} (g : SM.GameState St Msg C)
    (Δ qep : ℕ) (P : Party) (bad : Bool) :
    (g.epMgmt Δ qep P bad).map eraseSt = (eraseSt g).epMgmt Δ qep P bad := by
  unfold SM.GameState.epMgmt SM.GameState.safeCh SM.GameState.leak eraseSt
  dsimp only
  split
  · split
    · rfl
    · split <;> rfl
  · split <;> rfl

theorem epMgmt_st {St Msg C : Type} {g s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool} (h : g.epMgmt Δ qep P bad = some s₁) :
    s₁.st = g.st := by
  unfold SM.GameState.epMgmt at h
  split at h
  · split at h
    · contradiction
    · injection h with h; subst h
      split <;> rfl
  · split at h
    · contradiction
    · injection h with h; subst h; rfl

theorem eraseSt_epMgmt_none {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) {Δ qep : ℕ} {P : Party}
    {bad : Bool} (hL : gL.epMgmt Δ qep P bad = none) :
    gR.epMgmt Δ qep P bad = none := by
  have hmap := epMgmt_map_eraseSt gR Δ qep P bad
  rw [← he, ← epMgmt_map_eraseSt gL Δ qep P bad, hL, Option.map_none] at hmap
  exact Option.map_eq_none_iff.mp hmap

theorem eraseSt_epMgmt_some {StL StR Msg C : Type} {gL s₁L : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) {Δ qep : ℕ} {P : Party}
    {bad : Bool} (hL : gL.epMgmt Δ qep P bad = some s₁L) :
    ∃ s₁R, gR.epMgmt Δ qep P bad = some s₁R ∧ eraseSt s₁L = eraseSt s₁R ∧
      s₁L.st = gL.st ∧ s₁R.st = gR.st := by
  have hmap := epMgmt_map_eraseSt gR Δ qep P bad
  rw [← he, ← epMgmt_map_eraseSt gL Δ qep P bad, hL, Option.map_some] at hmap
  rcases Option.map_eq_some_iff.mp hmap with ⟨s₁R, hR, he₁⟩
  exact ⟨s₁R, hR, he₁.symm, epMgmt_st hL, epMgmt_st hR⟩

def GameInv {St Msg T E : Type} (g : SM.GameState St Msg (Header T × E)) : Prop :=
  (∀ r ∈ g.trans, r.ct.1.1 = r.pos.epoch) ∧
  (∀ x ∈ g.leaks, ∃ m, g.tL = some m ∧ x ≤ m)

theorem GameInv.leak {St Msg T E : Type} {g : SM.GameState St Msg (Header T × E)} {l : ℕ}
    (h : GameInv g) : GameInv (g.leak l) := by
  refine ⟨h.1, fun x hx => ?_⟩
  simp only [SM.GameState.leak, List.mem_cons] at hx
  refine ⟨maxOpt g.tL l, rfl, ?_⟩
  rcases hx with rfl | hx
  · exact le_rfl
  · rcases h.2 x hx with ⟨m, hm, hxm⟩
    rw [hm]; simp [maxOpt]; omega

theorem GameInv.epMgmt {St Msg T E : Type} {g s₁ : SM.GameState St Msg (Header T × E)}
    {Δ qep : ℕ} {P : Party} {bad : Bool} (h : GameInv g)
    (he : g.epMgmt Δ qep P bad = some s₁) : GameInv s₁ := by
  unfold SM.GameState.epMgmt at he
  split at he
  · split at he
    · contradiction
    · injection he with he; subst he
      have h₁ : GameInv (if bad && !g.safeCh Δ P then g.leak (g.epoch P + 1) else g) := by
        split
        · exact h.leak
        · exact h
      exact ⟨h₁.1, h₁.2⟩
  · split at he
    · contradiction
    · injection he with he; subst he; exact h

theorem GameInv.record {St Msg T E : Type} {s₁ : SM.GameState St Msg (Header T × E)}
    {Δ : ℕ} {P : Party} {st' : St} {r : Record Msg (Header T × E)} {isChall : Bool}
    (h : GameInv s₁) (hr : r.ct.1.1 = r.pos.epoch) :
    GameInv (s₁.record Δ P st' r isChall) := by
  refine ⟨fun r' hr' => ?_, h.2⟩
  simp only [SM.GameState.record, List.mem_cons] at hr'
  rcases hr' with rfl | hr'
  · exact hr
  · exact h.1 r' hr'

theorem GameInv.accept {St Msg T E : Type} {s : SM.GameState St Msg (Header T × E)}
    {P : Party} {st' : St} {pos : Pos} (h : GameInv s) :
    GameInv (s.accept P st' pos) := by
  refine ⟨fun r hr => ?_, h.2⟩
  simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr
  exact h.1 r hr.1

theorem GameInv.afterCorr {St Msg T E : Type} {s : SM.GameState St Msg (Header T × E)}
    {P : Party} (h : GameInv s) : GameInv (s.afterCorr P) := by
  unfold SM.GameState.afterCorr
  set s₁ : SM.GameState St Msg (Header T × E) :=
    { s with comp := (s.trans.filter (fun r => r.pos.sender == P.other)).map
                       (fun r => r.pos) ++ s.comp }
  have h₁ : GameInv s₁ := ⟨h.1, h.2⟩
  have h₂ := h₁.leak (l := max (s.epoch .A) (s.epoch .B))
  exact ⟨h₂.1, h₂.2⟩

theorem GameInv.inTransit_epoch {St Msg T E : Type} [DecidableEq T] [DecidableEq E]
    {s : SM.GameState St Msg (Header T × E)} {Q : Party} {c : Header T × E}
    {r : Record Msg (Header T × E)} (h : GameInv s) (hit : s.inTransit Q c = some r) :
    r.pos.epoch = c.1.1 := by
  unfold SM.GameState.inTransit at hit
  have hmem := List.mem_of_find?_eq_some hit
  have hp := List.find?_some hit
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  rw [← h.1 r hmem, hp.2]

def PartyRel (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ) (P : Party) (ep : ℕ)
    (vpL : PartyState (Option Γ) T Sig SS RS)
    (vpR : PartyState Γ T (Option Sig) SS RS) : Prop :=
  vpL.id = P ∧ vpR.id = P ∧
  vpL.tcur = ep ∧ vpR.tcur = ep ∧
  vpL.vS = vpR.vS ∧ vpL.vR = vpR.vR ∧ vpL.curCkaMsg = vpR.curCkaMsg ∧
  vpL.γ = (if tL.isNone || decide (healEpoch tL + Δcka ≤ ep) then some vpR.γ else none) ∧
  vpR.root = (if decide (tStar ≤ ep) || (tL.isSome && decide (ep < healEpoch tL))
    then some vpL.root else none)

def CKARel (Δcka : ℕ) (tL : Option ℕ)
    (gL : Ctx (Option Γ) T Sig SS RS M E)
    (gR : Ctx Γ T (Option Sig) SS RS M E)
    (cs : CKA.GameState Γ T) : Prop :=
  cs.b = true ∧
  ∀ P, tL.isSome = true → gL.epoch P < healEpoch tL + Δcka →
    cs.st P = (gR.st P).γ ∧ cs.epoch P = gL.epoch P

def PingPongRel (prng : PRFPRNG KR Sig I K) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (cs : CKA.GameState Γ T) : Prop :=
  (∀ t' > max (esL.g.epoch .A) (esL.g.epoch .B),
    esL.h.cache t' = none ∧ esR.h.cache t' = none) ∧
  ((esL.g.epoch .A = esL.g.epoch .B ∧ (esL.g.st .A).root = (esL.g.st .B).root) ∨
   ∃ P t0 Tc Ik,
     P.sendsIn (t0 + 1) = true ∧
     esL.g.epoch P = t0 + 1 ∧
     esL.g.epoch P.other = t0 ∧
     esL.h.cache (t0 + 1) = some (Tc, Ik) ∧
     (let p := prng.up (esL.g.st P.other).root Ik
      esR.h.cache (t0 + 1) = some (Tc,
        (if decide (tStar ≤ t0 + 1) || (tL.isSome && decide (t0 + 1 < healEpoch tL))
         then some p.1 else none), p.2) ∧
      (esL.g.st P).root = p.1) ∧
     (tL.isSome = true → t0 < healEpoch tL + Δcka →
       cs.epoch P = t0 + 1 ∧ cs.lastMsg = some Tc))

def PRNGRel (tL : Option ℕ) (tStar : ℕ)
    (gL : Ctx (Option Γ) T Sig SS RS M E)
    (ps : PRFPRNG.GameState Sig I K) : Prop :=
  let tmax := max (gL.epoch .A) (gL.epoch .B)
  tmax < tStar →
    ps.b = false ∧ ps.prf = false ∧ ps.prng = false ∧
    ps.corr = (tL.isSome && decide (tmax < healEpoch tL)) ∧
    ps.σ = (gL.st (Party.senderOf tmax)).root

/-- Full lockstep invariant between Left (`redCKA`) and Right (`redPRNG`) joint states. -/
def Sync (prng : PRFPRNG KR Sig I K) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) ×
      CKA.GameState Γ T)
    (sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K) : Prop :=
  sL.1.abort = false ∧ sR.1.abort = false ∧
  eraseSt sL.1.g = eraseSt sR.1.g ∧
  GameInv sL.1.g ∧
  (∀ P, PartyRel Δcka tL tStar P (sL.1.g.epoch P) (sL.1.g.st P) (sR.1.g.st P)) ∧
  CKARel Δcka tL sL.1.g sR.1.g sL.2 ∧
  PingPongRel prng Δcka tL tStar sL.1 sR.1 sL.2 ∧
  PRNGRel tL tStar sL.1.g sR.2

theorem Sync.privOutP_eq [DecidableEq M] (prng : PRFPRNG KR Sig I K) (Δcka : ℕ) (tL : Option ℕ)
    (tStar : ℕ) (b b' : Bool)
    {sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) ×
      CKA.GameState Γ T}
    {sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K}
    (hs : Sync prng Δcka tL tStar sL sR) :
    privOutP (2 + Δcka) ⟨false, tL, tStar⟩ b b' sL.1 =
      privOutP (2 + Δcka) ⟨false, tL, tStar⟩ b b' sR.1 := by
  rcases hs with ⟨habL, habR, he, -⟩
  simp only [privOutP, habL, habR, eraseSt_canon he tStar]

theorem sendsIn_other (P : Party) (t : ℕ) : P.other.sendsIn t = !(P.sendsIn t) := by
  rw [Bool.eq_iff_iff]
  cases P <;> simp [Party.other, Party.sendsIn]

theorem sendsIn_succ (P : Party) (t : ℕ) : P.sendsIn (t + 1) = !(P.sendsIn t) := by
  rw [Bool.eq_iff_iff]
  cases P <;> simp [Party.sendsIn] <;> omega

theorem senderOf_eq_of_sendsIn {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    Party.senderOf t = P := by
  cases P <;> simp [Party.sendsIn, Party.senderOf] at h ⊢ <;> omega

theorem PingPongRel.synced_of_sendsIn {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {tL : Option ℕ}
    {tStar : ℕ}
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)}
    {cs : CKA.GameState Γ T} {P : Party}
    (hpp : PingPongRel prng Δcka tL tStar esL esR cs)
    (hs : P.sendsIn (esL.g.epoch P + 1) = true) :
    esL.g.epoch .A = esL.g.epoch .B ∧ (esL.g.st .A).root = (esL.g.st .B).root := by
  rcases hpp.2 with hsync | ⟨Q, t0, Tc, Ik, hQ, hepQ, hepQo, -⟩
  · exact hsync
  · exfalso
    have hPQ : P = Q ∨ P = Q.other := by cases P <;> cases Q <;> decide
    rcases hPQ with rfl | rfl
    · rw [hepQ, sendsIn_succ, hQ] at hs; contradiction
    · rw [hepQo, sendsIn_other, hQ] at hs; contradiction

theorem PingPongRel.recv_step {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {tL : Option ℕ}
    {tStar : ℕ}
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)}
    {cs : CKA.GameState Γ T} (hpp : PingPongRel prng Δcka tL tStar esL esR cs) (P : Party) :
    let ep := esL.g.epoch P
    (esL.h.cache (ep + 1) = none ∧ esR.h.cache (ep + 1) = none) ∨
    (P.other.sendsIn (ep + 1) = true ∧
     esL.g.epoch P.other = ep + 1 ∧
     ∃ Tc Ik,
       esL.h.cache (ep + 1) = some (Tc, Ik) ∧
       (let p := prng.up (esL.g.st P).root Ik
        esR.h.cache (ep + 1) = some (Tc,
          (if decide (tStar ≤ ep + 1) || (tL.isSome && decide (ep + 1 < healEpoch tL))
           then some p.1 else none), p.2) ∧
        (esL.g.st P.other).root = p.1) ∧
       (tL.isSome = true → ep < healEpoch tL + Δcka →
         cs.epoch P.other = ep + 1 ∧ cs.lastMsg = some Tc)) := by
  intro ep
  rcases hpp with ⟨hcache, ⟨hAB, _⟩ | ⟨Q, t0, Tc, Ik, hQ, hepQ, hepQo, hcL, hcR, hcs⟩⟩
  · left
    apply hcache
    cases P <;> dsimp [ep] <;> omega
  · have hPQ : P = Q ∨ P = Q.other := by cases P <;> cases Q <;> decide
    rcases hPQ with rfl | rfl
    · left
      apply hcache
      cases P <;> dsimp [ep] at hepQ hepQo ⊢ <;> omega
    · right
      rw [Party.other_other]
      have hep : ep = t0 := hepQo
      rw [hep]
      exact ⟨hQ, hepQ, Tc, Ik, hcL, hcR, hcs⟩

section RunHMLemmas

variable {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS HS : Type}

theorem runHM_pure (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type} (a : α)
    (h : HS) (os : OS) :
    runHM oimpl (pure a : HM tspec HS α) h os = pure ((a, h), os) := by
  simp [runHM]

theorem runHM_bind (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α β : Type}
    (x : HM tspec HS α) (f : α → HM tspec HS β) (h : HS) (os : OS) :
    runHM oimpl (x >>= f) h os =
      runHM oimpl x h os >>= fun r => runHM oimpl (f r.1.1) r.1.2 r.2 := by
  simp [runHM, StateT.run_bind, simulateQ_bind]

theorem runHM_get (oimpl : QueryImpl tspec (StateT OS ProbComp)) (h : HS) (os : OS) :
    runHM oimpl (get : HM tspec HS HS) h os = pure ((h, h), os) := by
  simp [runHM]

theorem runHM_modify (oimpl : QueryImpl tspec (StateT OS ProbComp)) (f : HS → HS)
    (h : HS) (os : OS) :
    runHM oimpl (modify f : HM tspec HS Unit) h os = pure (((), f h), os) := by
  simp [runHM]

theorem runHM_sampleT (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (α : Type) [SampleableType α] (h : HS) (os : OS) :
    runHM oimpl (StateT.lift (sampleT α) : HM tspec HS α) h os =
      (fun x => ((x, h), os)) <$> ($ᵗ α : ProbComp α) := by
  simp [runHM, StateT.run_lift, simulateQ_outerFull_sampleT, map_eq_bind_pure_comp]

end RunHMLemmas

section RunHMCKA

variable [SampleableType CCoins] [SampleableType I]
  (cka : CKAScheme KC Γ CCoins T I) (Δcka tH : ℕ)

theorem runHM_cacheC (t : ℕ) (x : T × I) (h : CKAState T I) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (cacheC t x) h cs =
      pure (((), { cache := Function.update h.cache t (some x) }), cs) := by
  simp [cacheC, runHM_modify]

theorem runHM_liftC_corr (P : Party) (h : CKAState T I) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (liftC (CKA.corrQuery P)) h cs =
      pure ((if cs.allowCorr tH || cs.finished Δcka tH P then some (cs.st P) else none, h), cs) := by
  simp [runHM, liftC, CKA.corrQuery, outerFull, CKA.oracleImpl, CKA.corrImpl,
    StateT.run_lift, simulateQ_query]
  split <;> simp

theorem runHM_liftC_receive (P : Party) (h : CKAState T I) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (liftC (CKA.receiveQuery P)) h cs =
      if !(cs.canReceive P) then pure ((none, h), cs)
      else match cs.lastMsg with
        | none => pure ((none, h), cs)
        | some Tc =>
          pure ((some (), h), cs.afterReceive P (cka.receive (cs.st P) Tc).1) := by
  simp [runHM, liftC, CKA.receiveQuery, outerFull, CKA.oracleImpl, CKA.receiveImpl,
    StateT.run_lift, simulateQ_query]
  cases cs.canReceive P
  · simp
  · cases cs.lastMsg <;> simp

theorem runHM_liftC_sendBad (P : Party) (c : CCoins) (h : CKAState T I) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (liftC (CKA.sendWithAdversaryCoinsQuery P c)) h cs =
      if !(cs.canSend P) || !decide (cs.epoch P + 1 + 2 ≤ tH) then pure ((none, h), cs)
      else
        let out := cka.send (cs.st P) c
        pure ((some out.2, h), cs.afterSend P out.1 out.2.1) := by
  by_cases h1 : cs.canSend P <;>
    simp [runHM, liftC, CKA.sendWithAdversaryCoinsQuery, outerFull, CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl,
      StateT.run_lift, simulateQ_query, h1]
  split <;> simp

theorem runHM_liftC_send (P : Party) (h : CKAState T I) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka tH) (liftC (CKA.sendQuery P)) h cs =
      if !(cs.canSend P) || cs.epoch P + 1 == tH then pure ((none, h), cs)
      else
        (fun r =>
          let out := cka.send (cs.st P) r
          ((some out.2, h), cs.afterSend P out.1 out.2.1)) <$> ($ᵗ CCoins : ProbComp CCoins) := by
  by_cases h1 : cs.canSend P <;> by_cases h2 : cs.epoch P + 1 = tH <;>
    simp [runHM, liftC, CKA.sendQuery, outerFull, CKA.oracleImpl, CKA.sendImpl,
      StateT.run_lift, simulateQ_query, h1, h2, map_eq_bind_pure_comp]

theorem runHM_liftC_chall (P : Party) (h : CKAState T I) (cs : CKA.GameState Γ T)
    (hb : cs.b = true) :
    runHM (CKA.oracleImpl cka Δcka tH) (liftC (CKA.challQuery P)) h cs =
      if !(cs.canSend P) || cs.epoch P + 1 != tH then pure ((none, h), cs)
      else (do
        let r ← ($ᵗ CCoins : ProbComp CCoins)
        let out := cka.send (cs.st P) r
        let I' ← ($ᵗ I : ProbComp I)
        pure ((some (out.2.1, I'), h), cs.afterSend P out.1 out.2.1)) := by
  by_cases h1 : cs.canSend P <;> by_cases h2 : cs.epoch P + 1 = tH <;>
    simp [runHM, liftC, CKA.challQuery, outerFull, CKA.oracleImpl, CKA.challImpl,
      StateT.run_lift, simulateQ_query, hb, CKA.GameState.afterSend, h1, h2]

end RunHMCKA

section RunHMPRNG

variable [SampleableType I] [SampleableType K] [DecidableEq I]
  (prng : PRFPRNG KR Sig I K)

theorem runHM_liftP_process_some (Ik : I) (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) (hprf : ps.prf = false) :
    runHM (PRFPRNG.oracleImpl prng) (liftP (PRFPRNG.processQuery (some Ik))) h ps =
      let p := prng.up ps.σ Ik
      pure ((some p.2, h), { ps with σ := p.1, corr := ps.corr }) := by
  simp [runHM, liftP, PRFPRNG.processQuery, outerFull, PRFPRNG.oracleImpl,
    PRFPRNG.processImpl, PRFPRNG.samIfNec, StateT.run_lift, simulateQ_query, hprf]

theorem runHM_liftP_process_none (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) (hprf : ps.prf = false) :
    runHM (PRFPRNG.oracleImpl prng) (liftP (PRFPRNG.processQuery none)) h ps =
      (fun Ik =>
        let p := prng.up ps.σ Ik
        ((some p.2, h), { ps with σ := p.1, corr := false })) <$> ($ᵗ I : ProbComp I) := by
  simp [runHM, liftP, PRFPRNG.processQuery, outerFull, PRFPRNG.oracleImpl,
    PRFPRNG.processImpl, PRFPRNG.samIfNec, StateT.run_lift, simulateQ_query, hprf,
    map_eq_bind_pure_comp]

theorem runHM_liftP_corr (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) (hprf : ps.prf = false) :
    runHM (PRFPRNG.oracleImpl prng)
      (liftP (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K))) h ps =
      pure ((some ps.σ, h), { ps with corr := true }) := by
  simp [runHM, liftP, PRFPRNG.corrQuery, outerFull, PRFPRNG.oracleImpl,
    PRFPRNG.corrImpl, StateT.run_lift, simulateQ_query, hprf]

theorem runHM_processCorr_some (Ik : I) (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) (hprf : ps.prf = false) :
    runHM (PRFPRNG.oracleImpl prng) (processCorr (some Ik)) h ps =
      let p := prng.up ps.σ Ik
      pure ((some (some p.1, p.2), h), { ps with σ := p.1, corr := true }) := by
  unfold processCorr
  rw [runHM_bind, runHM_liftP_process_some prng Ik h ps hprf, pure_bind]
  dsimp only
  rw [runHM_bind,
    runHM_liftP_corr prng h { ps with σ := (prng.up ps.σ Ik).1, corr := ps.corr } hprf]
  simp [runHM_pure]

theorem runHM_liftP_challPrng_none (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) (hb : ps.b = false) (hprf : ps.prf = false) :
    runHM (PRFPRNG.oracleImpl prng) (liftP (PRFPRNG.challPrngQuery none)) h ps =
      (fun Ik =>
        let p := prng.up ps.σ Ik
        ((some p.2, h), { ps with σ := p.1, corr := false, prng := true })) <$>
          ($ᵗ I : ProbComp I) := by
  simp [runHM, liftP, PRFPRNG.challPrngQuery, outerFull, PRFPRNG.oracleImpl,
    PRFPRNG.challPrngImpl, PRFPRNG.samIfNec, StateT.run_lift, simulateQ_query,
    hb, hprf, map_eq_bind_pure_comp]

theorem runHM_liftP_challPrf (Ik : I) (h : PRNGState T Sig K)
    (ps : PRFPRNG.GameState Sig I K) (hb : ps.b = false) (hcorr : ps.corr = false)
    (hprng : ps.prng = false) :
    runHM (PRFPRNG.oracleImpl prng) (liftP (PRFPRNG.challPrfQuery Ik)) h ps =
      let p := prng.up ps.σ Ik
      pure ((some (p.1, p.2), h), { ps with prf := true }) := by
  simp [runHM, liftP, PRFPRNG.challPrfQuery, outerFull, PRFPRNG.oracleImpl,
    PRFPRNG.challPrfImpl, StateT.run_lift, simulateQ_query, hb, hcorr, hprng]

theorem validGuess_healed {Δcka : ℕ} {tL : Option ℕ} {tStar : ℕ}
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true) :
    tL = none ∨ ∃ l, tL = some l ∧ healEpoch tL = l + 2 ∧ healEpoch tL + Δcka ≤ tStar := by
  cases tL with
  | none => exact Or.inl rfl
  | some l =>
    simp [lastLeakGuessAdmissible, healedBy] at hvg
    exact Or.inr ⟨l, rfl, rfl, by dsimp [healEpoch]; omega⟩

theorem runHM_rootPRNG_known {Δcka : ℕ} {tL : Option ℕ} {tStar t : ℕ} {Ik : I} {σ : Sig}
    {σv : Option Sig} (h : PRNGState T Sig K) (ps : PRFPRNG.GameState Sig I K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hσv : tStar < t →
      σv = (if decide (tStar ≤ t - 1) || (tL.isSome && decide (t - 1 < healEpoch tL))
            then some σ else none))
    (ht0 : 0 < t → (t - 1 < tStar →
      ps.b = false ∧ ps.prf = false ∧ ps.prng = false ∧
      ps.corr = (tL.isSome && decide (t - 1 < healEpoch tL)) ∧ ps.σ = σ))
    (hz : t = 0 →
      ps.b = false ∧ ps.prf = false ∧ ps.prng = false ∧ ps.corr = false ∧ ps.σ = σ)
    (hnotH : ¬(tL.isSome = true ∧ t = healEpoch tL)) :
    ∃ ps',
      runHM (PRFPRNG.oracleImpl prng) (rootPRNG prng ⟨false, tL, tStar⟩ t Ik σv) h ps =
        pure ((some (if decide (tStar ≤ t) || (tL.isSome && decide (t < healEpoch tL))
                     then some (prng.up σ Ik).1 else none,
                   (prng.up σ Ik).2), h), ps') ∧
      (t < tStar →
        ps'.b = false ∧ ps'.prf = false ∧ ps'.prng = false ∧
        ps'.corr = (tL.isSome && decide (t < healEpoch tL)) ∧
        ps'.σ = (prng.up σ Ik).1) := by
  unfold rootPRNG
  by_cases hgt : tStar < t
  · have hle1 : decide (tStar ≤ t - 1) = true := decide_eq_true (by omega)
    have hle2 : decide (tStar ≤ t) = true := decide_eq_true (by omega)
    simp only [hgt, ↓reduceIte, hσv hgt, hle1, Bool.true_or, hle2, runHM_pure]
    exact ⟨ps, rfl, fun hlt => absurd hlt (by omega)⟩
  · simp only [hgt, ↓reduceIte]
    by_cases heq : t = tStar
    · subst heq
      have hcond : ((⟨false, tL, t⟩ : Mode).tL.isSome &&
          decide (t = (⟨false, tL, t⟩ : Mode).tH)) = false := by
        simp only [Bool.and_eq_false_imp]
        intro h1
        exact decide_eq_false (fun h2 => hnotH ⟨h1, h2⟩)
      simp only [↓reduceIte, hcond, Bool.false_eq_true]
      have hps : ps.b = false ∧ ps.prf = false ∧ ps.prng = false ∧ ps.corr = false ∧ ps.σ = σ := by
        by_cases hpos : 0 < t
        · have h1 := ht0 hpos (by omega)
          refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_, h1.2.2.2.2⟩
          rw [h1.2.2.2.1]
          rcases validGuess_healed hvg with rfl | ⟨l, rfl, hH, hle⟩
          · rfl
          · simp only [Option.isSome_some, Bool.true_and, decide_eq_false_iff_not, not_lt]
            have hne : t ≠ healEpoch (some l) := fun h => hnotH ⟨rfl, h⟩
            omega
        · exact hz (by omega)
      rcases hps with ⟨hb, hprf, hprng, hcorr, hσ⟩
      rw [runHM_bind, runHM_liftP_challPrf prng Ik h ps hb hcorr hprng, pure_bind]
      dsimp only
      rw [runHM_pure]
      refine ⟨{ ps with prf := true }, ?_, fun hlt => absurd hlt (by omega)⟩
      simp [hσ]
    · have hlt : t < tStar := by omega
      have hcond : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
          decide (t = (⟨false, tL, tStar⟩ : Mode).tH)) = false := by
        simp only [Bool.and_eq_false_imp]
        intro h1
        exact decide_eq_false (fun h2 => hnotH ⟨h1, h2⟩)
      simp only [heq, ↓reduceIte, hcond, Bool.false_eq_true]
      have hps : ps.b = false ∧ ps.prf = false ∧ ps.prng = false ∧ ps.σ = σ := by
        by_cases hpos : 0 < t
        · rcases ht0 hpos (by omega) with ⟨hb, hprf, hprng, _, hσ⟩
          exact ⟨hb, hprf, hprng, hσ⟩
        · rcases hz (by omega) with ⟨hb, hprf, hprng, _, hσ⟩
          exact ⟨hb, hprf, hprng, hσ⟩
      rcases hps with ⟨hb, hprf, hprng, hσ⟩
      have hnotle : decide (tStar ≤ t) = false := decide_eq_false (by omega)
      by_cases hltH : tL.isSome = true ∧ t < healEpoch tL
      · have hcond2 : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
            decide (t < (⟨false, tL, tStar⟩ : Mode).tH)) = true := by
          simp [Mode.tH, hltH.1, hltH.2]
        simp only [hcond2, ↓reduceIte]
        rw [runHM_processCorr_some prng Ik h ps hprf, hσ]
        refine ⟨{ ps with σ := (prng.up σ Ik).1, corr := true }, ?_, fun _ => ?_⟩
        · simp [hnotle, hltH.1, hltH.2]
        · refine ⟨hb, hprf, hprng, ?_, rfl⟩
          simp [hltH.1, hltH.2]
      · have hcond2 : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
            decide (t < (⟨false, tL, tStar⟩ : Mode).tH)) = false := by
          simp only [Bool.and_eq_false_imp]
          intro h1
          exact decide_eq_false (fun h2 => hltH ⟨h1, h2⟩)
        simp only [hcond2, Bool.false_eq_true, ↓reduceIte]
        rw [runHM_bind, runHM_liftP_process_some prng Ik h ps hprf, pure_bind]
        dsimp only
        rw [hσ, runHM_pure]
        have hfalse : (tL.isSome && decide (t < healEpoch tL)) = false := by
          cases htL : tL.isSome
          · rfl
          · simp only [Bool.true_and, decide_eq_false_iff_not]
            exact fun h => hltH ⟨htL, h⟩
        refine ⟨{ ps with σ := (prng.up σ Ik).1, corr := ps.corr }, ?_, fun _ => ?_⟩
        · simp [hnotle, hfalse]
        · refine ⟨hb, hprf, hprng, ?_, rfl⟩
          rw [hfalse]
          by_cases hpos : 0 < t
          · rw [(ht0 hpos (by omega)).2.2.2.1]
            cases htL : tL.isSome
            · rfl
            · simp only [Bool.true_and]
              have hne : t ≠ healEpoch tL := fun h => hnotH ⟨htL, h⟩
              have hnotlt : ¬(t < healEpoch tL) := fun h => hltH ⟨htL, h⟩
              exact decide_eq_false (by omega)
          · exact (hz (by omega)).2.2.2.1

theorem runHM_rootPRNG_heal {Δcka : ℕ} {tL : Option ℕ} {tStar t : ℕ} {Ik : I} {σ : Sig}
    {σv : Option Sig} (h : PRNGState T Sig K) (ps : PRFPRNG.GameState Sig I K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (htL : tL.isSome = true) (htH : t = healEpoch tL)
    (hps : ps.b = false ∧ ps.prf = false ∧ ps.prng = false ∧ ps.σ = σ) :
    ∃ ps' : I → PRFPRNG.GameState Sig I K,
      runHM (PRFPRNG.oracleImpl prng) (rootPRNG prng ⟨false, tL, tStar⟩ t Ik σv) h ps =
        (fun Ir =>
          let p := prng.up σ Ir
          ((some (if decide (tStar ≤ t) || (tL.isSome && decide (t < healEpoch tL))
                  then some p.1 else none, p.2), h), ps' Ir)) <$> ($ᵗ I : ProbComp I) ∧
      (∀ Ir, t < tStar →
        (ps' Ir).b = false ∧ (ps' Ir).prf = false ∧ (ps' Ir).prng = false ∧
        (ps' Ir).corr = (tL.isSome && decide (t < healEpoch tL)) ∧
        (ps' Ir).σ = (prng.up σ Ir).1) := by
  have hle : t ≤ tStar := by
    rcases validGuess_healed hvg with rfl | ⟨l, _, hH, hle⟩
    · simp at htL
    · omega
  have hng : ¬(tStar < t) := by omega
  rcases hps with ⟨hb, hprf, hprng, hσ⟩
  unfold rootPRNG
  simp only [hng, ↓reduceIte]
  by_cases heq : t = tStar
  · subst heq
    have hcond : ((⟨false, tL, t⟩ : Mode).tL.isSome &&
        decide (t = (⟨false, tL, t⟩ : Mode).tH)) = true := by
      simp [Mode.tH, htL, htH]
    simp only [↓reduceIte, hcond]
    rw [runHM_bind, runHM_liftP_challPrng_none prng h ps hb hprf]
    refine ⟨fun Ir => { ps with σ := (prng.up σ Ir).1, corr := true, prng := true }, ?_,
      fun _ hlt => absurd hlt (by omega)⟩
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    refine bind_congr fun Ir => ?_
    rw [runHM_bind,
      runHM_liftP_corr prng h { ps with σ := (prng.up ps.σ Ir).1, corr := false, prng := true } hprf]
    simp [runHM_pure, hσ]
  · have hlt : t < tStar := by omega
    have hcond : ((⟨false, tL, tStar⟩ : Mode).tL.isSome &&
        decide (t = (⟨false, tL, tStar⟩ : Mode).tH)) = true := by
      simp [Mode.tH, htL, htH]
    simp only [heq, ↓reduceIte, hcond]
    rw [runHM_bind, runHM_liftP_process_none prng h ps hprf]
    have hnotle : decide (tStar ≤ t) = false := decide_eq_false (by omega)
    have hnotltH : decide (t < healEpoch tL) = false := decide_eq_false (by omega)
    refine ⟨fun Ir => { ps with σ := (prng.up σ Ir).1, corr := false }, ?_, fun Ir _ => ?_⟩
    · simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      refine bind_congr fun Ir => ?_
      simp [runHM_pure, hσ, hnotle, hnotltH]
    · simp [hb, hprf, hprng, hnotltH]

end RunHMPRNG

/-! ### Receive and corruption step lemmas -/

def SyncOrDoom (prng : PRFPRNG KR Sig I K) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) ×
      CKA.GameState Γ T)
    (sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K) : Prop :=
  Sync prng Δcka tL tStar sL sR ∨ (Doom tL sL.1 ∧ Doom tL sR.1)

theorem epochs_of_not_corr_doom {St Msg C : Type} {tL : Option ℕ} {tStar : ℕ}
    {g : SM.GameState St Msg C} {P : Party}
    (hld : Policy.leakDoom ⟨false, tL, tStar⟩ g (g.afterCorr P) = false)
    (hcd : Policy.corrDoom ⟨false, tL, tStar⟩ g P = false) :
    tStar ≤ g.epoch P ∨
      ∃ l, tL = some l ∧ max (g.epoch .A) (g.epoch .B) ≤ l ∧ g.epoch P ≤ l := by
  set tmax := max (g.epoch .A) (g.epoch .B)
  set L := maxOpt g.tL tmax
  have hPmax : g.epoch P ≤ tmax := by cases P <;> simp [tmax]
  have htmaxL : tmax ≤ L := by dsimp [L]; cases g.tL <;> simp [maxOpt]
  have hmem : L ∈ (g.afterCorr P).leaks := by
    simp [SM.GameState.afterCorr, SM.GameState.leak, L, tmax]
  unfold Policy.leakDoom at hld
  dsimp only at hld
  rcases Bool.or_eq_false_iff.mp hld with ⟨hld1, hld2⟩
  rw [List.any_eq_false] at hld1
  by_cases hlt : L < tStar
  · have h1 := hld1 L hmem
    simp only [hlt, decide_true, Bool.and_true] at h1
    cases tL with
    | none => simp [ltOpt] at h1
    | some l =>
      simp only [ltOpt, decide_eq_true_eq, not_lt] at h1
      exact Or.inr ⟨l, rfl, le_trans htmaxL h1, le_trans hPmax (le_trans htmaxL h1)⟩
  · left
    have hgeL : tStar ≤ L := by omega
    have hany : ((g.afterCorr P).leaks.any fun l => decide (tStar ≤ l)) = true :=
      List.any_eq_true.mpr ⟨L, hmem, decide_eq_true hgeL⟩
    rw [hany, Bool.true_and, decide_eq_false_iff_not, not_lt] at hld2
    have hStmax : g.epoch (Party.senderOf tStar) ≤ tmax := by
      cases Party.senderOf tStar <;> simp [tmax]
    have hgetmax : tStar ≤ tmax := le_trans hld2 hStmax
    by_cases hPs : P = Party.senderOf tStar
    · subst hPs; exact hld2
    · have hPr : P = Party.receiverOf tStar := by
        unfold Party.receiverOf
        cases P <;> cases hS' : Party.senderOf tStar <;> simp_all [Party.other]
      subst hPr
      unfold Policy.corrDoom at hcd
      dsimp only at hcd
      have hgetmax' : decide (tStar ≤ max (g.epoch .A) (g.epoch .B)) = true :=
        decide_eq_true hgetmax
      simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hgetmax',
        Bool.and_true, Bool.true_and, decide_eq_false_iff_not, not_lt] at hcd
      exact hcd

theorem runHM_reveal_sync [DecidableEq T] [SampleableType CCoins] [SampleableType I]
    [SampleableType K] [DecidableEq I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (P : Party)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps))
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hld : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) = false)
    (hcd : Policy.corrDoom ⟨false, tL, tStar⟩ esL.g P = false) :
    let rp := realParty (esR.g.st P) (esR.g.st P).γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).reveal esL.g P (esL.g.st P)) esL.h cs =
      pure ((some rp, esL.h), cs) ∧
    runHM (PRFPRNG.oracleImpl prng)
      ((hooksPRNG cka prng fs ⟨false, tL, tStar⟩).reveal esR.g P (esR.g.st P)) esR.h ps =
      pure ((some rp, esR.h), ps) := by
  rcases hs with ⟨_, _, he, _, hp, hcka, _, _⟩
  dsimp only at he hp hcka
  have hP := hp P
  rcases hP with ⟨hidL, hidR, htcurL, htcurR, hvS, hvR, hTcur, hγ, hroot⟩
  have hreal : realParty (esL.g.st P) (esR.g.st P).γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR =
      realParty (esR.g.st P) (esR.g.st P).γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR := by
    simp [realParty, hidL, hidR, htcurL, htcurR, hTcur]
  have hrealR : realParty (esR.g.st P) (esR.g.st P).γ (esL.g.st P).root (esR.g.st P).vS (esR.g.st P).vR =
      realParty (esR.g.st P) (esR.g.st P).γ (esL.g.st P).root (esL.g.st P).vS (esL.g.st P).vR := by
    simp [realParty, hvS, hvR]
  have hep := epochs_of_not_corr_doom hld hcd
  have hroot_some : (esR.g.st P).root = some (esL.g.st P).root := by
    rw [hroot]
    rcases hep with hge | ⟨l, htL, _, hPl⟩
    · simp [hge]
    · have hltH : esL.g.epoch P < healEpoch (some l) := by dsimp [healEpoch]; omega
      simp [htL, hltH]
  constructor
  · unfold hooksCKA
    dsimp only
    by_cases hγc : (tL.isNone || decide (healEpoch tL + Δcka ≤ esL.g.epoch P)) = true
    · rw [hγ]
      simp [hγc, runHM_pure, hreal]
    · rw [hγ]
      simp only [hγc, Bool.false_eq_true, ↓reduceIte]
      rw [runHM_bind, runHM_liftC_corr]
      rcases hep with hge | ⟨l, htL, hmaxl, hPl⟩
      · exfalso
        rcases validGuess_healed hvg with rfl | ⟨l, rfl, hH, hle⟩
        · simp at hγc
        · have : decide (healEpoch (some l) + Δcka ≤ esL.g.epoch P) = true :=
            decide_eq_true (by omega)
          simp [this] at hγc
      · have hltA : esL.g.epoch .A < healEpoch tL + Δcka := by
          rw [htL]; dsimp [healEpoch]; omega
        have hltB : esL.g.epoch .B < healEpoch tL + Δcka := by
          rw [htL]; dsimp [healEpoch]; omega
        have hltP : esL.g.epoch P < healEpoch tL + Δcka := by
          rw [htL]; dsimp [healEpoch]; omega
        have hcsA := (hcka.2 .A (by simp [htL]) hltA).2
        have hcsB := (hcka.2 .B (by simp [htL]) hltB).2
        have hcsP := (hcka.2 P (by simp [htL]) hltP).1
        have hallow : cs.allowCorr (healEpoch tL) = true := by
          unfold CKA.GameState.allowCorr
          rw [hcsA, hcsB, htL]
          dsimp [healEpoch]
          exact decide_eq_true (by omega)
        simp [hallow, hcsP, runHM_pure, hreal]
  · unfold hooksPRNG
    dsimp only
    rw [hroot_some, runHM_pure, hrealR]

theorem runEM_corrE_sync [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (P : Party)
    (sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) ×
      CKA.GameState Γ T)
    (sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K)
    (hs : Sync prng Δcka tL tStar sL sR)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true) :
    ∃ ans sL' sR',
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (corrE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) ⟨false, tL, tStar⟩ P) sL =
        pure (ans, sL') ∧
      runEM (PRFPRNG.oracleImpl prng)
        (corrE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) ⟨false, tL, tStar⟩ P) sR =
        pure (ans, sR') ∧
      SyncOrDoom prng Δcka tL tStar sL' sR' := by
  rcases sL with ⟨esL, cs⟩
  rcases sR with ⟨esR, ps⟩
  have habL : esL.abort = false := hs.1
  have habR : esR.abort = false := hs.2.1
  have he : eraseSt esL.g = eraseSt esR.g := hs.2.2.1
  have hwin := eraseSt_win he
  have hca := eraseSt_corrAllowed he P
  unfold corrE
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]
  dsimp only
  rw [habL, habR, ← hwin, ← hca]
  by_cases hguard : (esL.g.win || !esL.g.corrAllowed P) = true
  · simp only [Bool.false_or, hguard, ↓reduceIte, runEM_pure]
    exact ⟨none, (esL, cs), (esR, ps), rfl, rfl, Or.inl hs⟩
  · simp only [Bool.false_or, hguard, Bool.false_eq_true, ↓reduceIte]
    have he_ac := eraseSt_afterCorr he P
    have hld_eq := eraseSt_leakDoom he he_ac ⟨false, tL, tStar⟩
    have hcd_eq := eraseSt_corrDoom he ⟨false, tL, tStar⟩ P
    rw [← hld_eq, ← hcd_eq]
    by_cases hdoom : (Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) ||
        Policy.corrDoom ⟨false, tL, tStar⟩ esL.g P) = true
    · simp only [hdoom, ↓reduceIte, runEM_abort_pure]
      exact ⟨none, ({ esL with abort := true }, cs), ({ esR with abort := true }, ps),
        rfl, rfl, Or.inr ⟨Or.inl rfl, Or.inl rfl⟩⟩
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
      have hdoom' : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g (esL.g.afterCorr P) = false ∧
          Policy.corrDoom ⟨false, tL, tStar⟩ esL.g P = false :=
        Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hdoom)
      rcases runHM_reveal_sync cka prng fs Δcka tL tStar P esL cs esR ps hs hvg
        hdoom'.1 hdoom'.2 with ⟨hrevL, hrevR⟩
      rw [runEM_bind, runEM_liftH, hrevL, map_pure, pure_bind]
      dsimp only
      rw [runEM_modify_pure]
      rw [runEM_bind, runEM_liftH, hrevR, map_pure, pure_bind]
      dsimp only
      rw [runEM_modify_pure]
      refine ⟨_, _, _, rfl, rfl, Or.inl ?_⟩
      rcases hs with ⟨_, _, _, hinv, hp, hcka, hpp, hprng⟩
      exact ⟨habL, habR, he_ac, hinv.afterCorr, hp, hcka, hpp, hprng⟩

def RecvStep (cka : CKAScheme KC Γ CCoins T I)
    (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (cs : CKA.GameState Γ T) (P : Party) (t : ℕ)
    (st'L : PartyState (Option Γ) T Sig SS RS)
    (st'R : PartyState Γ T (Option Sig) SS RS) : Prop :=
  let ep := esL.g.epoch P
  (t ≤ ep ∧ st'L.tcur = ep ∧ st'L.root = (esL.g.st P).root ∧ st'R.γ = (esR.g.st P).γ ∧
    PartyRel Δcka tL tStar P ep st'L st'R) ∨
  (t = ep + 1 ∧ P.sendsIn (ep + 1) = false ∧
    st'L.id = P ∧ st'R.id = P ∧ st'L.tcur = ep + 1 ∧ st'R.tcur = ep + 1 ∧
    st'L.vS = st'R.vS ∧ st'L.vR = st'R.vR ∧ st'L.curCkaMsg = st'R.curCkaMsg ∧
    st'L.γ = (esL.g.st P).γ.map (fun _ => st'R.γ) ∧
    st'R.root = (if decide (tStar ≤ ep + 1) || (tL.isSome && decide (ep + 1 < healEpoch tL))
                 then some st'L.root else none) ∧
    esL.g.epoch P.other = ep + 1 ∧
    (esL.g.st P.other).root = st'L.root ∧
    ∃ Tc, st'R.γ = (cka.receive (esR.g.st P).γ Tc).1 ∧
      (tL.isSome = true → ep < healEpoch tL + Δcka →
        cs.epoch P.other = ep + 1 ∧ cs.lastMsg = some Tc))

theorem runHM_vRecv_sync [DecidableEq T] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (P : Party) (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps)) :
    (runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (vRecv (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) c rec)
        esL.h cs = pure ((some none, esL.h), cs) ∧
      runHM (PRFPRNG.oracleImpl prng)
        (vRecv (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) c rec)
        esR.h ps = pure ((some none, esR.h), ps)) ∨
    ∃ st'L st'R i m,
      runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (vRecv (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) c rec)
        esL.h cs = pure ((some (some (st'L, c.1.1, i, m)), esL.h), cs) ∧
      runHM (PRFPRNG.oracleImpl prng)
        (vRecv (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) c rec)
        esR.h ps = pure ((some (some (st'R, c.1.1, i, m)), esR.h), ps) ∧
      RecvStep cka Δcka tL tStar esL esR cs P c.1.1 st'L st'R := by
  rcases hs with ⟨_, _, _, _, hp, _, hpp, _⟩
  dsimp only at hp hpp
  rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hvS, hvR, hTcur, hγ, hroot⟩
  unfold vRecv
  dsimp only
  rw [hidL, hidR, htcurL, htcurR]
  by_cases hbad : (P.sendsIn c.1.1 || decide (esL.g.epoch P + 1 < c.1.1)) = true
  · left
    simp [hbad, runHM_pure]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    have hbad' : P.sendsIn c.1.1 = false ∧ c.1.1 ≤ esL.g.epoch P + 1 := by
      rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hbad) with ⟨h1, h2⟩
      exact ⟨h1, by have := of_decide_eq_false h2; omega⟩
    by_cases hstep : c.1.1 = esL.g.epoch P + 1
    · simp only [hstep, ↓reduceIte]
      cases hTn : c.1.2 with
      | none =>
        left
        simp [runHM_pure]
      | some Tn =>
        have hsends : P.sendsIn (esL.g.epoch P + 1) = false := by
          rw [← hstep]; exact hbad'.1
        rcases hpp.recv_step P with ⟨hcL, hcR⟩ |
          ⟨_, hepO, Tc, Ik, hcL, ⟨hcR, hrootO⟩, hcsO⟩
        · left
          unfold hooksCKA hooksPRNG
          simp [runHM_bind, runHM_get, hcL, hcR, runHM_pure]
        · by_cases hTc : Tc = Tn
          · subst hTc
            unfold hooksCKA hooksPRNG
            simp only [runHM_bind, runHM_get, pure_bind, hcL, hcR, ↓reduceIte, runHM_pure,
              Function.update_self]
            cases hfs : fs.receive (fs.initReceiver (prng.up (esL.g.st P).root Ik).2) c.1 c.2 with
            | none =>
              left; simp [runHM_pure]
            | some res =>
              rcases res with ⟨v', i, m⟩
              right
              refine ⟨_, _, i, m, by rw [runHM_pure], by rw [runHM_pure], Or.inr ?_⟩
              refine ⟨rfl, hsends, rfl, rfl, rfl, rfl, hvS, ?_, hTcur, ?_, rfl,
                hepO, hrootO, Tc, rfl, hcsO⟩
              · rw [hvR]
              · cases hγ' : (esL.g.st P).γ with
                | none => rfl
                | some γ0 =>
                  have hγeq : γ0 = (esR.g.st P).γ := by
                    rw [hγ] at hγ'
                    split at hγ'
                    · exact Option.some.inj hγ'.symm
                    · contradiction
                  simp [hγeq]
          · left
            unfold hooksCKA hooksPRNG
            simp [runHM_bind, runHM_get, hcL, hcR, hTc, runHM_pure]
    · have hle : c.1.1 ≤ esL.g.epoch P := by omega
      simp only [hstep, ↓reduceIte, pure_bind]
      rw [hvR]
      cases hvRt : (esR.g.st P).vR c.1.1 with
      | none =>
        left; simp [runHM_pure]
      | some v =>
        unfold hooksCKA hooksPRNG
        dsimp only
        rw [runHM_bind, runHM_pure, pure_bind, runHM_bind, runHM_pure, pure_bind]
        dsimp only
        cases hfs : fs.receive v c.1 c.2 with
        | none =>
          left; simp [runHM_pure]
        | some res =>
          rcases res with ⟨v', i, m⟩
          right
          refine ⟨_, _, i, m, by rw [runHM_pure], by rw [runHM_pure], Or.inl ?_⟩
          refine ⟨hle, htcurL, rfl, rfl, hidL, hidR, htcurL, htcurR, hvS, rfl, hTcur, hγ, hroot⟩

theorem accept_update_st {St Msg C : Type} (s : SM.GameState St Msg C) (P : Party)
    (st₁ st₂ : St) (pos : Pos) :
    { s.accept P st₁ pos with st := Function.update (s.accept P st₁ pos).st P st₂ } =
      s.accept P st₂ pos := by
  simp [SM.GameState.accept]

theorem runEM_commitE_sync [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (P : Party) (pos : Pos)
    (st'L : PartyState (Option Γ) T Sig SS RS)
    (st'R : PartyState Γ T (Option Sig) SS RS)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps))
    (hr : RecvStep cka Δcka tL tStar esL esR cs P pos.epoch st'L st'R) :
    ∃ s₁L s₁R cs',
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (commitE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) st'L pos)
        (esL, cs) = pure (some s₁L, (esL, cs')) ∧
      runEM (PRFPRNG.oracleImpl prng)
        (commitE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
        (esR, ps) = pure (some s₁R, (esR, ps)) ∧
      Sync prng Δcka tL tStar ({ esL with g := s₁L }, cs') ({ esR with g := s₁R }, ps) := by
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only at habL habR he hinv hp hcka hpp hprng
  rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hvS, hvR, hTcur, hγ, hroot⟩
  have hcommR :
      runEM (PRFPRNG.oracleImpl prng)
        (commitE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) esR.g P (esR.g.st P) st'R pos)
        (esR, ps) = pure (some (esR.g.accept P st'R pos), (esR, ps)) := by
    unfold commitE hooksPRNG
    simp [runEM_bind, runEM_liftH, runHM_pure, runEM_pure, accept_update_st]
  rcases hr with ⟨hle, hst_tcur, hst_root, hst_γ, hp'⟩ |
    ⟨ht_step, hsends, hidL', hidR', htcurL', htcurR', hvS', hvR', hTcur',
      hγ', hroot', hepO, hrootO, Tc, hγR', hcsO⟩
  ·
    have hnotlt : ¬((esL.g.st P).tcur < st'L.tcur) := by omega
    have hcommL :
        runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (commitE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) st'L pos)
          (esL, cs) = pure (some (esL.g.accept P st'L pos), (esL, cs)) := by
      unfold commitE hooksCKA
      simp [runEM_bind, runEM_liftH, hnotlt, runHM_pure, runEM_pure, accept_update_st]
    refine ⟨esL.g.accept P st'L pos, esR.g.accept P st'R pos, cs, hcommL, hcommR, ?_⟩
    have hep_eq : ∀ Q, (esL.g.accept P st'L pos).epoch Q = esL.g.epoch Q := by
      intro Q
      simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self, Nat.max_eq_left hle]
      · simp [Function.update_of_ne hQP]
    have hroot_eq : ∀ Q, ((esL.g.accept P st'L pos).st Q).root = (esL.g.st Q).root := by
      intro Q
      simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self, hst_root]
      · simp [Function.update_of_ne hQP]
    have hγ_eq : ∀ Q, ((esR.g.accept P st'R pos).st Q).γ = (esR.g.st Q).γ := by
      intro Q
      simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self, hst_γ]
      · simp [Function.update_of_ne hQP]
    refine ⟨habL, habR, eraseSt_accept he P st'L st'R pos, hinv.accept, ?_, ?_, ?_, ?_⟩
    · intro Q
      rw [hep_eq Q]
      simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self]; exact hp'
      · simp [Function.update_of_ne hQP]; exact hp Q
    · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
      rw [hep_eq Q] at hlt ⊢
      rw [hγ_eq Q]
      exact hcka.2 Q htL hlt
    · refine ⟨?_, ?_⟩
      · intro t' ht'
        rw [hep_eq .A, hep_eq .B] at ht'
        exact hpp.1 t' ht'
      · rcases hpp.2 with ⟨h1, h2⟩ | ⟨Q, t0, Tc0, Ik0, h1, h2, h3, h4, h5, h6⟩
        · left
          rw [hep_eq .A, hep_eq .B, hroot_eq .A, hroot_eq .B]
          exact ⟨h1, h2⟩
        · right
          refine ⟨Q, t0, Tc0, Ik0, h1, ?_, ?_, h4, ?_, h6⟩
          · rw [hep_eq Q]; exact h2
          · rw [hep_eq Q.other]; exact h3
          · rw [hroot_eq Q.other, hroot_eq Q]; exact h5
    · unfold PRNGRel at hprng ⊢
      dsimp only at hprng ⊢
      rw [hep_eq .A, hep_eq .B, hroot_eq]
      exact hprng
  ·
    set ep := esL.g.epoch P
    have hlt_tcur : (esL.g.st P).tcur < st'L.tcur := by omega
    have hmax_ep : max (esL.g.epoch P) pos.epoch = ep + 1 := by omega
    have hep_acc : ∀ (stL : PartyState (Option Γ) T Sig SS RS) (Q : Party),
        (esL.g.accept P stL pos).epoch Q = ep + 1 := by
      intro stL Q
      simp only [SM.GameState.accept, SM.GameState.delete]
      by_cases hQP : Q = P
      · subst hQP; simp [Function.update_self, hmax_ep]
      · have hQo : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
        subst hQo; simp [Function.update_of_ne hQP, hepO]
    have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = ep + 1 := by
      cases P <;> simp [Party.other] at hepO <;> simp [ep, hepO]
    have hSO : Party.senderOf (ep + 1) = P.other := by
      apply senderOf_eq_of_sendsIn
      rw [sendsIn_other, hsends]; rfl
    have hneO : P.other ≠ P := by cases P <;> decide
    by_cases hγc : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = true
    ·
      have hγ_some : (esL.g.st P).γ = some (esR.g.st P).γ := by
        rw [hγ]; simp [hγc]
      have hisNone : (esL.g.st P).γ.isNone = false := by simp [hγ_some]
      have hcommL :
          runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
            (commitE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) st'L pos)
            (esL, cs) = pure (some (esL.g.accept P st'L pos), (esL, cs)) := by
        unfold commitE hooksCKA
        simp [runEM_bind, runEM_liftH, hisNone, runHM_pure, runEM_pure, accept_update_st]
      refine ⟨esL.g.accept P st'L pos, esR.g.accept P st'R pos, cs, hcommL, hcommR, ?_⟩
      refine ⟨habL, habR, eraseSt_accept he P st'L st'R pos, hinv.accept, ?_, ?_, ?_, ?_⟩
      · intro Q
        simp only [SM.GameState.accept, SM.GameState.delete]
        by_cases hQP : Q = P
        · subst hQP
          simp only [Function.update_self, hmax_ep]
          have hγc' : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)) = true := by
            rcases Bool.or_eq_true_iff.mp hγc with h1 | h2
            · simp [h1]
            · have := of_decide_eq_true h2
              simp [decide_eq_true (by omega : healEpoch tL + Δcka ≤ ep + 1)]
          refine ⟨hidL', hidR', htcurL', htcurR', hvS', hvR', hTcur', ?_, hroot'⟩
          rw [hγ', hγ_some]; simp [hγc']
        · have hQo : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst hQo
          simp only [Function.update_of_ne hQP]
          exact hp P.other
      · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
        rw [hep_acc st'L Q] at hlt
        exfalso
        have h1 : tL.isNone = false := by cases tL <;> simp_all
        have h2 : decide (healEpoch tL + Δcka ≤ ep) = false := decide_eq_false (by omega)
        rw [h1, h2] at hγc; contradiction
      · refine ⟨?_, Or.inl ?_⟩
        · intro t' ht'
          rw [hep_acc st'L .A, hep_acc st'L .B, Nat.max_self, ← hmax_old] at ht'
          exact hpp.1 t' ht'
        · rw [hep_acc st'L .A, hep_acc st'L .B]
          refine ⟨rfl, ?_⟩
          simp only [SM.GameState.accept, SM.GameState.delete]
          cases P <;> simp [Party.other] at hrootO <;> simp [hrootO]
      · unfold PRNGRel at hprng ⊢
        dsimp only at hprng ⊢
        rw [hep_acc st'L .A, hep_acc st'L .B, Nat.max_self]
        rw [hmax_old] at hprng
        intro hlt
        rcases hprng hlt with ⟨hb, hprf, hprng', hcorr, hσ⟩
        refine ⟨hb, hprf, hprng', hcorr, ?_⟩
        rw [hσ, hSO]
        simp [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne hneO]
    ·
      rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hγc) with ⟨htL_none, hlt_heal⟩
      have htL_some : tL.isSome = true := by cases tL <;> simp_all
      have hep_lt : ep < healEpoch tL + Δcka := by
        have := of_decide_eq_false hlt_heal; omega
      have hγ_none : (esL.g.st P).γ = none := by rw [hγ]; simp [hγc]
      have hisNone : (esL.g.st P).γ.isNone = true := by simp [hγ_none]
      rcases hcka.2 P htL_some hep_lt with ⟨hcs_stP, hcs_epP⟩
      rcases hcsO htL_some hep_lt with ⟨hcs_epO, hcs_last⟩
      have hcanR : cs.canReceive P = true := by
        unfold CKA.GameState.canReceive
        simp [hcs_epO, hcs_epP, ep]
      set cs' := cs.afterReceive P st'R.γ
      have hcond_comm : (decide ((esL.g.st P).tcur < st'L.tcur) && (esL.g.st P).γ.isNone) = true := by
        simp [hlt_tcur, hisNone]
      by_cases hfin : healEpoch tL + Δcka ≤ ep + 1
      ·
        set new'L := { st'L with γ := some st'R.γ }
        have hfin_cs' : cs'.finished Δcka (healEpoch tL) P = true := by
          unfold CKA.GameState.finished
          simp [cs', CKA.GameState.afterReceive, Function.update_self, hcs_epP, ep, hfin]
        have hfin_mo : ({ auth := false, tL := tL, tStar := tStar } : Mode).tH + Δcka ≤ ep + 1 := hfin
        have hhmL :
            runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
              ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).commit
                (esL.g.accept P st'L pos) P (esL.g.st P) st'L)
              esL.h cs = pure ((some new'L, esL.h), cs') := by
          unfold hooksCKA
          dsimp only
          simp only [hcond_comm, ↓reduceIte]
          rw [runHM_bind, runHM_liftC_receive]
          simp only [hcanR, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs_last,
            hcs_stP, ← hγR', pure_bind]
          change runHM (CKA.oracleImpl cka Δcka (healEpoch tL)) _ esL.h cs' = _
          rw [htcurL']
          simp only [hfin_mo, ↓reduceIte]
          rw [runHM_bind, runHM_liftC_corr]
          have hst_cs' : cs'.st P = st'R.γ := by
            simp [cs', CKA.GameState.afterReceive, Function.update_self]
          simp only [hfin_cs', Bool.or_true, ↓reduceIte, hst_cs', pure_bind, runHM_pure]
          simp [new'L, htcurL']
        have hcommL :
            runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
              (commitE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) st'L pos)
              (esL, cs) = pure (some (esL.g.accept P new'L pos), (esL, cs')) := by
          unfold commitE
          rw [runEM_bind, runEM_liftH, hhmL]
          simp [runEM_pure, accept_update_st]
        refine ⟨esL.g.accept P new'L pos, esR.g.accept P st'R pos, cs', hcommL, hcommR, ?_⟩
        refine ⟨habL, habR, eraseSt_accept he P new'L st'R pos, hinv.accept, ?_, ?_, ?_, ?_⟩
        · intro Q
          simp only [SM.GameState.accept, SM.GameState.delete]
          by_cases hQP : Q = P
          · subst hQP
            simp only [Function.update_self, hmax_ep]
            have hγc' : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)) = true := by
              simp [decide_eq_true hfin]
            refine ⟨hidL', hidR', htcurL', htcurR', hvS', hvR', hTcur', ?_, hroot'⟩
            simp [new'L, hγc']
          · have hQo : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
            subst hQo
            simp only [Function.update_of_ne hQP]
            exact hp P.other
        · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
          rw [hep_acc new'L Q] at hlt
          omega
        · refine ⟨?_, Or.inl ?_⟩
          · intro t' ht'
            rw [hep_acc new'L .A, hep_acc new'L .B, Nat.max_self, ← hmax_old] at ht'
            exact hpp.1 t' ht'
          · rw [hep_acc new'L .A, hep_acc new'L .B]
            refine ⟨rfl, ?_⟩
            simp only [SM.GameState.accept, SM.GameState.delete]
            cases P <;> simp [Party.other] at hrootO <;> simp [new'L, hrootO]
        · unfold PRNGRel at hprng ⊢
          dsimp only at hprng ⊢
          rw [hep_acc new'L .A, hep_acc new'L .B, Nat.max_self]
          rw [hmax_old] at hprng
          intro hlt
          rcases hprng hlt with ⟨hb, hprf, hprng', hcorr, hσ⟩
          refine ⟨hb, hprf, hprng', hcorr, ?_⟩
          rw [hσ, hSO]
          simp [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne hneO]
      ·
        have hfin_mo : ¬(({ auth := false, tL := tL, tStar := tStar } : Mode).tH + Δcka ≤ ep + 1) := hfin
        have hhmL :
            runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
              ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).commit
                (esL.g.accept P st'L pos) P (esL.g.st P) st'L)
              esL.h cs = pure ((some st'L, esL.h), cs') := by
          unfold hooksCKA
          dsimp only
          simp only [hcond_comm, ↓reduceIte]
          rw [runHM_bind, runHM_liftC_receive]
          simp only [hcanR, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs_last,
            hcs_stP, ← hγR', pure_bind]
          change runHM (CKA.oracleImpl cka Δcka (healEpoch tL)) _ esL.h cs' = _
          rw [htcurL']
          simp only [hfin_mo, ↓reduceIte, runHM_pure]
        have hcommL :
            runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
              (commitE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) esL.g P (esL.g.st P) st'L pos)
              (esL, cs) = pure (some (esL.g.accept P st'L pos), (esL, cs')) := by
          unfold commitE
          rw [runEM_bind, runEM_liftH, hhmL]
          simp [runEM_pure, accept_update_st]
        refine ⟨esL.g.accept P st'L pos, esR.g.accept P st'R pos, cs', hcommL, hcommR, ?_⟩
        refine ⟨habL, habR, eraseSt_accept he P st'L st'R pos, hinv.accept, ?_, ?_, ?_, ?_⟩
        · intro Q
          simp only [SM.GameState.accept, SM.GameState.delete]
          by_cases hQP : Q = P
          · subst hQP
            simp only [Function.update_self, hmax_ep]
            have hγc' : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)) = false := by
              simp [htL_none, decide_eq_false hfin]
            refine ⟨hidL', hidR', htcurL', htcurR', hvS', hvR', hTcur', ?_, hroot'⟩
            rw [hγ', hγ_none, hγc']; rfl
          · have hQo : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
            subst hQo
            simp only [Function.update_of_ne hQP]
            exact hp P.other
        · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
          rw [hep_acc st'L Q] at hlt ⊢
          simp only [cs', CKA.GameState.afterReceive, SM.GameState.accept, SM.GameState.delete]
          by_cases hQP : Q = P
          · subst hQP
            simp [Function.update_self, hcs_epP, ep]
          · have hQo : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
            subst hQo
            simp only [Function.update_of_ne hQP]
            rw [← hepO] at hlt ⊢
            exact hcka.2 P.other htL hlt
        · refine ⟨?_, Or.inl ?_⟩
          · intro t' ht'
            rw [hep_acc st'L .A, hep_acc st'L .B, Nat.max_self, ← hmax_old] at ht'
            exact hpp.1 t' ht'
          · rw [hep_acc st'L .A, hep_acc st'L .B]
            refine ⟨rfl, ?_⟩
            simp only [SM.GameState.accept, SM.GameState.delete]
            cases P <;> simp [Party.other] at hrootO <;> simp [hrootO]
        · unfold PRNGRel at hprng ⊢
          dsimp only at hprng ⊢
          rw [hep_acc st'L .A, hep_acc st'L .B, Nat.max_self]
          rw [hmax_old] at hprng
          intro hlt
          rcases hprng hlt with ⟨hb, hprf, hprng', hcorr, hσ⟩
          refine ⟨hb, hprf, hprng', hcorr, ?_⟩
          rw [hσ, hSO]
          simp [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne hneO]

theorem Sync.set_win {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {tL : Option ℕ} {tStar : ℕ}
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {cs : CKA.GameState Γ T}
    {esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)}
    {ps : PRFPRNG.GameState Sig I K}
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps)) :
    Sync prng Δcka tL tStar
      ({ esL with g := { esL.g with win := true } }, cs)
      ({ esR with g := { esR.g with win := true } }, ps) := by
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  refine ⟨habL, habR, ?_, ⟨hinv.1, hinv.2⟩, hp, hcka, hpp, hprng⟩
  change { eraseSt esL.g with win := true } = { eraseSt esR.g with win := true }
  rw [he]

theorem runEM_map_modify {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS HS Γv Sv SSv RSv : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type}
    (f : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS →
      EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (a : α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl ((fun _ => a) <$> modify f) s = pure (a, (f s.1, s.2)) := by
  simp [runEM]

theorem runEM_deliverE_sync [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka maxSkip : ℕ) (cfg : Config M)
    (tL : Option ℕ) (tStar : ℕ) (q : Party × (Header T × E))
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps)) :
    ∃ out sL' sR',
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (deliverE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) maxSkip cfg q) (esL, cs) =
        pure (out, sL') ∧
      runEM (PRFPRNG.oracleImpl prng)
        (deliverE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) maxSkip cfg q) (esR, ps) =
        pure (out, sR') ∧
      Sync prng Δcka tL tStar sL' sR' := by
  rcases q with ⟨P, c⟩
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  have hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps) :=
    ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only at habL habR he hinv
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  have htr_eq : esR.g.inTransit P.other c = esL.g.inTransit P.other c :=
    (eraseSt_inTransit he P.other c).symm
  unfold deliverE
  dsimp only
  rw [runEM_bind, runEM_get, runEM_bind, runEM_get]
  simp only [pure_bind]
  rw [habL, habR, hwin]
  by_cases hw : (false || esL.g.win) = true
  · refine ⟨none, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;> simp [hw, runEM_pure]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    rw [htr_eq]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      refine ⟨none, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;> simp [runEM_pure]
    | some r =>
      dsimp only
      have hmust_eq : esR.g.mustBeCorrect maxSkip P r = esL.g.mustBeCorrect maxSkip P r :=
        (eraseSt_mustBeCorrect he maxSkip P r).symm
      rw [runEM_bind, runEM_liftH, runEM_bind, runEM_liftH]
      rcases runHM_vRecv_sync cka prng fs Δcka tL tStar P c (some r) esL cs esR ps hs with
        ⟨hL, hR⟩ | ⟨st'L, st'R, i, m, hL, hR, hstep⟩
      · rw [hL, hR]
        simp only [map_pure, pure_bind]
        rw [hmust_eq]
        by_cases hmust : (cfg.deliverWin && esL.g.mustBeCorrect maxSkip P r) = true
        · refine ⟨some .rejected, ({ esL with g := { esL.g with win := true } }, cs),
            ({ esR with g := { esR.g with win := true } }, ps), ?_, ?_, hs.set_win⟩ <;>
            simp [hmust, runEM_map_modify]
        · refine ⟨some .rejected, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
            simp [hmust, runEM_pure]
      · rw [hL, hR]
        simp only [map_pure, pure_bind]
        have hr_ep : r.pos.epoch = c.1.1 := hinv.inTransit_epoch htr
        have hstep' : RecvStep cka Δcka tL tStar esL esR cs P r.pos.epoch st'L st'R :=
          hr_ep ▸ hstep
        rcases runEM_commitE_sync cka prng fs Δcka tL tStar P r.pos st'L st'R esL cs esR ps hs hstep' with
          ⟨g'L, g'R, cs', hcommL, hcommR, hs'⟩
        rw [runEM_bind, hcommL, runEM_bind, hcommR]
        simp only [pure_bind]
        rw [hmust_eq]
        have hchall_eq : esR.g.chall = esL.g.chall := (eraseSt_chall he).symm
        rw [hchall_eq]
        set bad := (cfg.deliverWin && esL.g.mustBeCorrect maxSkip P r) &&
          !(decide ((c.1.1, i, m) = (r.pos.epoch, r.pos.idx, r.msg)))
        by_cases hbad : bad = true
        · refine ⟨some (.accepted c.1.1 i (if esL.g.chall.contains r.pos then none else some m)),
            ({ esL with g := { g'L with win := true } }, cs'),
            ({ esR with g := { g'R with win := true } }, ps), ?_, ?_, hs'.set_win⟩ <;>
            simp [bad, hbad, runEM_map_modify]
        · refine ⟨some (.accepted c.1.1 i (if esL.g.chall.contains r.pos then none else some m)),
            ({ esL with g := g'L }, cs'), ({ esR with g := g'R }, ps), ?_, ?_, hs'⟩ <;>
            simp [bad, hbad, runEM_map_modify]

theorem runEM_injectE_sync [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (cfg : Config M)
    (tL : Option ℕ) (tStar : ℕ) (q : Party × (Header T × E))
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps)) :
    ∃ out sL' sR',
      runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
        (injectE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩) (2 + Δcka) qep cfg q) (esL, cs) =
        pure (out, sL') ∧
      runEM (PRFPRNG.oracleImpl prng)
        (injectE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩) (2 + Δcka) qep cfg q) (esR, ps) =
        pure (out, sR') ∧
      Sync prng Δcka tL tStar sL' sR' := by
  rcases q with ⟨P, c⟩
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  have hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps) :=
    ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only at habL habR he hinv
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  have htr_eq : esR.g.inTransit P.other c = esL.g.inTransit P.other c :=
    (eraseSt_inTransit he P.other c).symm
  have hsafe_eq : esR.g.safeInj (2 + Δcka) = esL.g.safeInj (2 + Δcka) :=
    (eraseSt_safeInj he (2 + Δcka)).symm
  unfold injectE
  dsimp only
  rw [runEM_bind, runEM_get, runEM_bind, runEM_get]
  simp only [pure_bind]
  rw [habL, habR, hwin, htr_eq, hsafe_eq]
  by_cases hg : ((false || esL.g.win || (esL.g.inTransit P.other c).isSome) ||
      !esL.g.safeInj (2 + Δcka)) = true
  · refine ⟨none, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
      (rw [ite_bool_true hg]; exact runEM_pure _ _ _)
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    rw [runEM_bind, runEM_liftH, runEM_bind, runEM_liftH]
    rcases runHM_vRecv_sync cka prng fs Δcka tL tStar P c none esL cs esR ps hs with
      ⟨hL, hR⟩ | ⟨st'L, st'R, i, m, hL, hR, hstep⟩
    · rw [hL, hR]
      refine ⟨some .rejected, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
        simp [map_pure, pure_bind, runEM_pure]
    · rw [hL, hR]
      simp only [map_pure, pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · refine ⟨some .rejected, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
          simp [hqep, runEM_pure]
      · simp only [hqep, ↓reduceIte]
        set pos : Pos := ⟨P.other, c.1.1, i⟩
        have htriv_eq : esR.g.trivial (2 + Δcka) pos = esL.g.trivial (2 + Δcka) pos :=
          (eraseSt_trivial he (2 + Δcka) pos).symm
        rw [htriv_eq]
        by_cases htriv : esL.g.trivial (2 + Δcka) pos = true
        · simp only [htriv, ↓reduceIte]
          rcases runEM_commitE_sync cka prng fs Δcka tL tStar P pos st'L st'R esL cs esR ps hs hstep with
            ⟨g'L, g'R, cs', hcommL, hcommR, hs'⟩
          rw [runEM_bind, hcommL, runEM_bind, hcommR]
          refine ⟨some (.accepted c.1.1 i (some m)),
            ({ esL with g := g'L }, cs'), ({ esR with g := g'R }, ps), ?_, ?_, hs'⟩ <;>
            simp [pure_bind, runEM_map_modify]
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : cfg.injectFull c.1.1 = true
          · refine ⟨some .rejected, ({ esL with g := { esL.g with win := true } }, cs),
              ({ esR with g := { esR.g with win := true } }, ps), ?_, ?_, hs.set_win⟩ <;>
              simp [hfull, runEM_map_modify]
          · refine ⟨some .rejected, (esL, cs), (esR, ps), ?_, ?_, hs⟩ <;>
              simp [hfull, runEM_pure]

/-! ### Send step and adversary coupling -/

def sendCore {ι : Type} {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ : ℕ) (s₁ : Ctx Γv T Sv SSv RSv M E) (P : Party) (m : M)
    (pair : Option (M × M)) (r : Option CCoins) (isChall : Bool) :
    EM tspec Γv T Sv SSv RSv M E HS (Option (Header T × E)) := do
  match ← liftH (vSend hk s₁ P (s₁.st P) m pair r) with
  | none =>
    abortE
    return none
  | some (st', c) =>
    modify fun es =>
      { es with g := s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall }
    return some c

theorem runEM_sendCore_doom {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {OS Γv Sv SSv RSv HS : Type} [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    {tL : Option ℕ} (Δ : ℕ) (s₁ : Ctx Γv T Sv SSv RSv M E) (P : Party) (m : M)
    (pair : Option (M × M)) (r : Option CCoins) (isChall : Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hm : MissedTL tL s₁)
    {res : Option (Header T × E) × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)}
    (hres : res ∈ support (runEM oimpl (sendCore hk Δ s₁ P m pair r isChall) s)) :
    Doom tL res.2.1 := by
  unfold sendCore at hres
  rw [runEM_bind, mem_support_bind_iff] at hres
  rcases hres with ⟨r₁, _, hres⟩
  cases hvs : r₁.1 with
  | none =>
    rw [hvs, runEM_abort_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres; exact Or.inl rfl
  | some stc =>
    rcases stc with ⟨st', c⟩
    rw [hvs, runEM_modify_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres; exact Or.inr hm.record

theorem evalEng_sendCore_of_missedTL {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {OS Γv Sv SSv RSv HS : Type} [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (s₁ : Ctx Γv T Sv SSv RSv M E) (P : Party) (m : M)
    (pair : Option (M × M)) (rcoins : Option CCoins) (isChall : Bool)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hm : MissedTL π.tL s₁) :
    DEq (runEM oimpl (sendCore hk Δ s₁ P m pair rcoins isChall) s >>=
          fun r => evalEng oimpl hk Δ qep maxSkip cfg π b (k r.1) r.2)
        ($ᵗ Bool : ProbComp Bool) := by
  refine (DEq.bind_right_supp _ fun r hr => ?_).trans (DEq.bind_const _ _)
  exact evalEng_doom oimpl hk Δ qep maxSkip cfg π b (k r.1) r.2
    (runEM_sendCore_doom oimpl hk Δ s₁ P m pair rcoins isChall s hm hr)

theorem eraseSt_missedTL {StL StR Msg C : Type} {gL : SM.GameState StL Msg C}
    {gR : SM.GameState StR Msg C} (he : eraseSt gL = eraseSt gR) {tL : Option ℕ}
    (hm : MissedTL tL gL) : MissedTL tL gR := by
  rcases hm with ⟨l, htL, hA, hB, hmax, hnl⟩
  rw [eraseSt_epoch he] at hA hB hmax
  rw [eraseSt_leaks he] at hnl
  exact ⟨l, htL, hA, hB, hmax, hnl⟩

theorem epMgmt_sendsIn_true {St Msg C : Type} {g s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hsends : P.sendsIn (g.epoch P + 1) = true)
    (he : g.epMgmt Δ qep P bad = some s₁) :
    let g₁ := if bad && !g.safeCh Δ P then g.leak (g.epoch P + 1) else g
    s₁ = { g₁ with epoch := Function.update g.epoch P (g.epoch P + 1),
                   idx := Function.update g.idx P 0 } := by
  unfold SM.GameState.epMgmt at he
  simp only [hsends, ↓reduceIte] at he
  split at he
  · contradiction
  · injection he with he
    rw [← he]
    split <;> rfl

theorem epMgmt_sendsIn_false {St Msg C : Type} {g s₁ : SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hsends : P.sendsIn (g.epoch P + 1) = false)
    (he : g.epMgmt Δ qep P bad = some s₁) :
    s₁ = g := by
  unfold SM.GameState.epMgmt at he
  simp only [hsends, Bool.false_eq_true, ↓reduceIte] at he
  split at he
  · contradiction
  · exact Option.some.inj he.symm

theorem missedTL_of_bad_send {St Msg T E : Type}
    {g s₁ : SM.GameState St Msg (Header T × E)}
    {Δcka qep l tStar : ℕ} {P : Party}
    (hinv : GameInv g)
    (hAB : g.epoch .A = g.epoch .B)
    (hsends : P.sendsIn (g.epoch P + 1) = true)
    (hep : g.epMgmt (2 + Δcka) qep P true = some s₁)
    (hld : Policy.leakDoom ⟨false, some l, tStar⟩ g s₁ = false)
    (hvh : healEpoch (some l) + Δcka ≤ tStar)
    (hunh : g.epoch P < healEpoch (some l) + Δcka)
    (hlt : l < g.epoch P + 1) :
    MissedTL (some l) s₁ := by
  have hs₁ := epMgmt_sendsIn_true hsends hep
  dsimp only [Bool.true_and] at hs₁
  have hepA : g.epoch .A = g.epoch P := by cases P <;> simp [hAB]
  have hepB : g.epoch .B = g.epoch P := by cases P <;> simp [hAB]
  have hA : l ≤ s₁.epoch .A := by
    rw [hs₁]; cases P <;> simp [Function.update, hepA] <;> omega
  have hB : l ≤ s₁.epoch .B := by
    rw [hs₁]; cases P <;> simp [Function.update, hepB] <;> omega
  have hmax : l < max (s₁.epoch .A) (s₁.epoch .B) := by
    rw [hs₁]; cases P <;> simp [Function.update, hepA, hepB] <;> omega
  refine ⟨l, rfl, hA, hB, hmax, ?_⟩
  cases htL : g.tL with
  | none =>
    have hnl_g : l ∉ g.leaks := by
      intro hl
      rcases hinv.2 l hl with ⟨m, hm, _⟩
      rw [htL] at hm; contradiction
    rw [hs₁]
    dsimp only
    split
    · simp only [SM.GameState.leak, htL, maxOpt, List.mem_cons, not_or]
      exact ⟨by omega, hnl_g⟩
    · exact hnl_g
  | some m =>
    by_cases hml : m < l
    · have hnl_g : l ∉ g.leaks := by
        intro hl
        rcases hinv.2 l hl with ⟨m', hm', hlm'⟩
        rw [htL] at hm'; injection hm' with hm'; subst hm'
        omega
      rw [hs₁]
      dsimp only
      split
      · simp only [SM.GameState.leak, htL, maxOpt, List.mem_cons, not_or]
        exact ⟨by omega, hnl_g⟩
      · exact hnl_g
    · exfalso
      have hsc : (!g.safeCh (2 + Δcka) P) = true := by
        simp only [SM.GameState.safeCh, htL, healedBy, Bool.not_eq_true', decide_eq_false_iff_not,
          not_le]
        dsimp [healEpoch] at hunh
        omega
      have hs₁_leak : s₁.leaks = max m (g.epoch P + 1) :: g.leaks := by
        rw [hs₁]
        simp [hsc, SM.GameState.leak, htL, maxOpt]
      set L := max m (g.epoch P + 1)
      have hmem : L ∈ s₁.leaks := by rw [hs₁_leak]; exact List.mem_cons_self
      have hlL : l < L := by dsimp [L]; omega
      unfold Policy.leakDoom at hld
      dsimp only at hld
      rcases Bool.or_eq_false_iff.mp hld with ⟨hld1, hld2⟩
      rw [List.any_eq_false] at hld1
      have h1 := hld1 L hmem
      have hltOpt : ltOpt (some l) L = true := decide_eq_true hlL
      simp only [hltOpt, Bool.true_and, decide_eq_true_eq, not_lt] at h1
      have hany : (s₁.leaks.any fun x => decide (tStar ≤ x)) = true :=
        List.any_eq_true.mpr ⟨L, hmem, decide_eq_true h1⟩
      simp only [hany, Bool.true_and, decide_eq_false_iff_not, not_lt] at hld2
      have hsend_ep : g.epoch (Party.senderOf tStar) = g.epoch P := by
        cases Party.senderOf tStar <;> simp [hepA, hepB]
      dsimp [healEpoch] at hunh hvh
      omega

theorem vSend_of_sendsIn_true {ι : Type} {tspec : OracleSpec.{0, 0} ι} {Γv Sv HS : Type}
    [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SS RS)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hfs : ∀ ctx P t ss h m pair, hk.fsSend ctx P t ss h m pair = pure (some (fs.send ss h m)))
    (ctx : Ctx Γv T Sv SS RS M E) (P : Party) (s : VP Γv T Sv SS RS) (m : M)
    (pair : Option (M × M)) (r : Option CCoins)
    (hsends : s.id.sendsIn (s.tcur + 1) = true) :
    vSend hk ctx P s m pair r = (do
      match ← hk.startSend ctx P (s.tcur + 1) s.γ s.root r with
      | none => pure none
      | some (γ', T', σ', ss) =>
        let h : Header T := (s.tcur + 1, some T')
        let fsOut := fs.send ss h m
        pure (some ({ s with tcur := s.tcur + 1, γ := γ', curCkaMsg := some T', root := σ',
                             vS := some fsOut.1 }, (h, fsOut.2)))) := by
  unfold vSend
  simp only [hsends, ↓reduceIte]
  refine bind_congr fun res => ?_
  cases res with
  | none => simp
  | some val =>
    rcases val with ⟨γ', T', σ', ss⟩
    simp [hfs]

theorem vSend_of_sendsIn_false {ι : Type} {tspec : OracleSpec.{0, 0} ι} {Γv Sv HS : Type}
    [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SS RS)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hfs : ∀ ctx P t ss h m pair, hk.fsSend ctx P t ss h m pair = pure (some (fs.send ss h m)))
    (ctx : Ctx Γv T Sv SS RS M E) (P : Party) (s : VP Γv T Sv SS RS) (m : M)
    (pair : Option (M × M)) (r : Option CCoins)
    (hsends : s.id.sendsIn (s.tcur + 1) = false) :
    vSend hk ctx P s m pair r =
      let h : Header T := (s.tcur, s.curCkaMsg)
      match s.vS with
      | none => pure (some (s, (h, default)))
      | some v =>
        let fsOut := fs.send v h m
        pure (some ({ s with vS := some fsOut.1 }, (h, fsOut.2))) := by
  unfold vSend
  simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
  cases s.vS with
  | none => rfl
  | some v => simp [hfs]

theorem runEM_sendCore_sendsIn_true {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {OS Γv Sv HS : Type} [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SS RS)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hfs : ∀ ctx P t ss h m pair, hk.fsSend ctx P t ss h m pair = pure (some (fs.send ss h m)))
    (Δ : ℕ) (s₁ : Ctx Γv T Sv SS RS M E) (P : Party) (m : M)
    (pair : Option (M × M)) (r : Option CCoins) (isChall : Bool)
    (es : EState (VP Γv T Sv SS RS) M (Header T × E) HS) (os : OS)
    (hsends : (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1) = true) :
    runEM oimpl (sendCore hk Δ s₁ P m pair r isChall) (es, os) =
      runHM oimpl (hk.startSend s₁ P ((s₁.st P).tcur + 1) (s₁.st P).γ (s₁.st P).root r) es.h os >>=
        fun res =>
          match res.1.1 with
          | none => pure (none, ({ es with h := res.1.2, abort := true }, res.2))
          | some (γ', T', σ', ss) =>
            let h : Header T := ((s₁.st P).tcur + 1, some T')
            let fsOut := fs.send ss h m
            let st' := { s₁.st P with tcur := (s₁.st P).tcur + 1, γ := γ', curCkaMsg := some T',
                                      root := σ', vS := some fsOut.1 }
            let c := (h, fsOut.2)
            pure (some c,
              ({ es with g := s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall,
                         h := res.1.2 }, res.2)) := by
  unfold sendCore
  rw [runEM_bind, runEM_liftH, vSend_of_sendsIn_true hk fs hfs s₁ P (s₁.st P) m pair r hsends,
    runHM_bind, bind_map_left, bind_assoc]
  refine bind_congr fun res => ?_
  cases res.1.1 with
  | none =>
    simp [runHM_pure, runEM, abortE]
  | some val =>
    rcases val with ⟨γ', T', σ', ss⟩
    simp [runHM_pure, runEM]

theorem runEM_sendCore_sendsIn_false {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {OS Γv Sv HS : Type} [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SS RS)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hfs : ∀ ctx P t ss h m pair, hk.fsSend ctx P t ss h m pair = pure (some (fs.send ss h m)))
    (Δ : ℕ) (s₁ : Ctx Γv T Sv SS RS M E) (P : Party) (m : M)
    (pair : Option (M × M)) (r : Option CCoins) (isChall : Bool)
    (es : EState (VP Γv T Sv SS RS) M (Header T × E) HS) (os : OS)
    (hsends : (s₁.st P).id.sendsIn ((s₁.st P).tcur + 1) = false) :
    runEM oimpl (sendCore hk Δ s₁ P m pair r isChall) (es, os) =
      let h : Header T := ((s₁.st P).tcur, (s₁.st P).curCkaMsg)
      let stc : VP Γv T Sv SS RS × (Header T × E) := match (s₁.st P).vS with
        | none => (s₁.st P, (h, default))
        | some v =>
          let fsOut := fs.send v h m
          ({ s₁.st P with vS := some fsOut.1 }, (h, fsOut.2))
      pure (some stc.2,
        ({ es with g := s₁.record Δ P stc.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, stc.2⟩ isChall },
          os)) := by
  unfold sendCore
  rw [runEM_bind, runEM_liftH, vSend_of_sendsIn_false hk fs hfs s₁ P (s₁.st P) m pair r hsends]
  cases (s₁.st P).vS with
  | none =>
    simp [runHM_pure, runEM]
  | some v =>
    simp [runHM_pure, runEM]

theorem sync_after_same_send [Inhabited E]
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ) (P : Party) (m : M) (isChall : Bool)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps)) :
    let h : Header T := (esL.g.epoch P, (esL.g.st P).curCkaMsg)
    let stcL : PartyState (Option Γ) T Sig SS RS × (Header T × E) := match (esL.g.st P).vS with
      | none => (esL.g.st P, (h, default))
      | some v =>
        let fsOut := fs.send v h m
        ({ esL.g.st P with vS := some fsOut.1 }, (h, fsOut.2))
    let stcR : PartyState Γ T (Option Sig) SS RS × (Header T × E) := match (esL.g.st P).vS with
      | none => (esR.g.st P, (h, default))
      | some v =>
        let fsOut := fs.send v h m
        ({ esR.g.st P with vS := some fsOut.1 }, (h, fsOut.2))
    let recL : Record M (Header T × E) := ⟨⟨P, esL.g.epoch P, esL.g.idx P + 1⟩, m, stcL.2⟩
    Sync prng Δcka tL tStar
      ({ esL with g := esL.g.record (2 + Δcka) P stcL.1 recL isChall }, cs)
      ({ esR with g := esR.g.record (2 + Δcka) P stcR.1 recL isChall }, ps) := by
  intro h stcL stcR recL
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only at habL habR he hinv hp hcka hpp hprng
  have hstc2 : stcR.2 = stcL.2 := by
    dsimp [stcL, stcR]; cases (esL.g.st P).vS <;> rfl
  have hrec : recL.ct.1.1 = recL.pos.epoch := by
    dsimp [recL, stcL, h]; cases (esL.g.st P).vS <;> rfl
  have hrootL : stcL.1.root = (esL.g.st P).root := by
    dsimp [stcL]; cases (esL.g.st P).vS <;> rfl
  have hγR : stcR.1.γ = (esR.g.st P).γ := by
    dsimp [stcR]; cases (esL.g.st P).vS <;> rfl
  have hstL_root : ∀ Q, ((esL.g.record (2 + Δcka) P stcL.1 recL isChall).st Q).root =
      (esL.g.st Q).root := by
    intro Q
    by_cases hQP : Q = P
    · subst hQP; simp [SM.GameState.record, hrootL]
    · simp [SM.GameState.record, hQP]
  have hstR_γ : ∀ Q, ((esR.g.record (2 + Δcka) P stcR.1 recL isChall).st Q).γ =
      (esR.g.st Q).γ := by
    intro Q
    by_cases hQP : Q = P
    · subst hQP; simp [SM.GameState.record, hγR]
    · simp [SM.GameState.record, hQP]
  refine ⟨habL, habR,
    eraseSt_record he (2 + Δcka) P stcL.1 stcR.1 recL isChall,
    hinv.record hrec, ?_, ?_, ?_, ?_⟩
  · intro Q
    by_cases hQP : Q = P
    · subst hQP
      simp only [SM.GameState.record, Function.update_self]
      rcases hp Q with ⟨hidL, hidR, htcurL, htcurR, hvS, hvR, hTcur, hγ, hroot⟩
      dsimp [stcL, stcR]
      cases (esL.g.st Q).vS with
      | none => exact ⟨hidL, hidR, htcurL, htcurR, hvS, hvR, hTcur, hγ, hroot⟩
      | some v => exact ⟨hidL, hidR, htcurL, htcurR, rfl, hvR, hTcur, hγ, hroot⟩
    · simp only [SM.GameState.record, Function.update_of_ne hQP]
      exact hp Q
  · refine ⟨hcka.1, fun Q htL hlt => ?_⟩
    rw [hstR_γ Q]
    exact hcka.2 Q htL hlt
  · refine ⟨hpp.1, ?_⟩
    rcases hpp.2 with ⟨hAB, hrootAB⟩ | ⟨Q, t0, Tc, Ik, hQ, hepQ, hepQo, hcL, hcR, hcs⟩
    · left
      refine ⟨hAB, ?_⟩
      rw [hstL_root .A, hstL_root .B, hrootAB]
    · right
      refine ⟨Q, t0, Tc, Ik, hQ, hepQ, hepQo, hcL, ?_, hcs⟩
      rw [hstL_root Q.other, hstL_root Q]
      exact hcR
  · intro hlt
    rcases hprng hlt with ⟨hb, hprf, hprng1, hcorr, hσ⟩
    refine ⟨hb, hprf, hprng1, hcorr, ?_⟩
    rw [hstL_root]
    exact hσ

theorem sync_after_new_send [Inhabited E]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (tStar : ℕ) (P : Party) (m : M) (bad isChall : Bool)
    (coins : CCoins) (Ik : I)
    (s₁L : Ctx (Option Γ) T Sig SS RS M E)
    (s₁R : Ctx Γ T (Option Sig) SS RS M E)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps ps' : PRFPRNG.GameState Sig I K)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps))
    (hsends : P.sendsIn (esL.g.epoch P + 1) = true)
    (hepL : esL.g.epMgmt (2 + Δcka) qep P bad = some s₁L)
    (hepR : esR.g.epMgmt (2 + Δcka) qep P bad = some s₁R)
    (hps' : esL.g.epoch P + 1 < tStar →
      ps'.b = false ∧ ps'.prf = false ∧ ps'.prng = false ∧
      ps'.corr = (tL.isSome && decide (esL.g.epoch P + 1 < healEpoch tL)) ∧
      ps'.σ = (prng.up (esL.g.st P).root Ik).1) :
    let ep := esL.g.epoch P
    let c_cka := cka.send (esR.g.st P).γ coins
    let p := prng.up (esL.g.st P).root Ik
    let γ'L : Option Γ :=
      if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1) then some c_cka.1 else none
    let σ'R : Option Sig :=
      if decide (tStar ≤ ep + 1) || (tL.isSome && decide (ep + 1 < healEpoch tL))
      then some p.1 else none
    let h : Header T := (ep + 1, some c_cka.2.1)
    let fsOut := fs.send (fs.initSender p.2) h m
    let st'L : PartyState (Option Γ) T Sig SS RS :=
      { s₁L.st P with tcur := ep + 1, γ := γ'L, curCkaMsg := some c_cka.2.1,
                      root := p.1, vS := some fsOut.1 }
    let st'R : PartyState Γ T (Option Sig) SS RS :=
      { s₁R.st P with tcur := ep + 1, γ := c_cka.1, curCkaMsg := some c_cka.2.1,
                      root := σ'R, vS := some fsOut.1 }
    let c := (h, fsOut.2)
    let recL : Record M (Header T × E) := ⟨⟨P, s₁L.epoch P, s₁L.idx P + 1⟩, m, c⟩
    let recR : Record M (Header T × E) := ⟨⟨P, s₁R.epoch P, s₁R.idx P + 1⟩, m, c⟩
    let h'L : CKAState T I :=
      { cache := Function.update esL.h.cache (ep + 1) (some (c_cka.2.1, Ik)) }
    let h'R : PRNGState T Sig K :=
      { cache := Function.update esR.h.cache (ep + 1) (some (c_cka.2.1, σ'R, p.2)) }
    let cs' : CKA.GameState Γ T :=
      if tL.isNone || decide (healEpoch tL + Δcka ≤ ep) then cs
      else cs.afterSend P c_cka.1 c_cka.2.1
    Sync prng Δcka tL tStar
      ({ esL with g := s₁L.record (2 + Δcka) P st'L recL isChall, h := h'L }, cs')
      ({ esR with g := s₁R.record (2 + Δcka) P st'R recR isChall, h := h'R }, ps') := by
  intro ep c_cka p γ'L σ'R h fsOut st'L st'R c recL recR h'L h'R cs'
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only at habL habR he hinv hp hcka hpp hprng
  rcases eraseSt_epMgmt_some he hepL with ⟨s₁R', hepR', he₁, hst₁L, hst₁R⟩
  rw [hepR] at hepR'; injection hepR' with hepR'; subst hepR'
  have hs₁L_eq := epMgmt_sendsIn_true hsends hepL
  have hep₁L : s₁L.epoch = Function.update esL.g.epoch P (ep + 1) := by
    rw [hs₁L_eq]
  have hrec_eq : recR = recL := by
    dsimp [recL, recR]
    rw [eraseSt_epoch he₁, eraseSt_idx he₁]
  have hrec_ep : recL.ct.1.1 = recL.pos.epoch := by
    dsimp [recL, c, h]; rw [hep₁L, Function.update_self]
  rcases hpp.synced_of_sendsIn hsends with ⟨hAB, hrootAB⟩
  have hep_other : esL.g.epoch P.other = ep := by
    cases P <;> dsimp [ep] <;> omega
  have hroot_other : (esL.g.st P.other).root = (esL.g.st P).root := by
    cases P <;> simp [Party.other, hrootAB]
  refine ⟨habL, habR,
    hrec_eq ▸ eraseSt_record he₁ (2 + Δcka) P st'L st'R recL isChall,
    (hinv.epMgmt hepL).record hrec_ep, ?_, ?_, ?_, ?_⟩
  · intro Q
    by_cases hQP : Q = P
    · subst hQP
      simp only [SM.GameState.record, hep₁L, Function.update_self]
      rcases hp Q with ⟨hidL, hidR, _, _, _, hvR, _, _, _⟩
      dsimp [st'L, st'R]
      rw [hst₁L, hst₁R]
      exact ⟨hidL, hidR, rfl, rfl, rfl, hvR, rfl, rfl, rfl⟩
    · simp only [SM.GameState.record, hep₁L, Function.update_of_ne hQP, hst₁L, hst₁R]
      exact hp Q
  · refine ⟨?_, fun Q htL hQlt => ?_⟩
    · dsimp [cs']
      split
      · exact hcka.1
      · exact hcka.1
    · simp only [SM.GameState.record, hep₁L] at hQlt ⊢
      have hunh : ep < healEpoch tL + Δcka := by
        by_cases hQP : Q = P
        · subst hQP; simp only [Function.update_self] at hQlt; omega
        · simp only [Function.update_of_ne hQP] at hQlt
          have hQep : esL.g.epoch Q = ep := by cases P <;> cases Q <;> dsimp [ep] <;> omega
          omega
      have hcond : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = false := by
        cases tL with
        | none => simp at htL
        | some l => simp [decide_eq_false (by omega : ¬(healEpoch (some l) + Δcka ≤ ep))]
      have hcs' : cs' = cs.afterSend P c_cka.1 c_cka.2.1 := by
        dsimp [cs']; rw [hcond]; rfl
      rw [hcs']
      by_cases hQP : Q = P
      · subst hQP
        simp only [CKA.GameState.afterSend, Function.update_self]
        exact ⟨rfl, by rw [(hcka.2 Q htL hunh).2]⟩
      · simp only [CKA.GameState.afterSend, Function.update_of_ne hQP, hst₁R] at hQlt ⊢
        exact hcka.2 Q htL hQlt
  · have hmax_new :
        max ((s₁L.record (2 + Δcka) P st'L recL isChall).epoch .A)
            ((s₁L.record (2 + Δcka) P st'L recL isChall).epoch .B) = ep + 1 := by
      simp only [SM.GameState.record, hep₁L]
      cases P <;> simp [Function.update, hAB, ep]
    refine ⟨fun t' ht' => ?_, Or.inr ⟨P, ep, c_cka.2.1, Ik, hsends, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hmax_new] at ht'
      have hne : t' ≠ ep + 1 := by omega
      dsimp [h'L, h'R]
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      apply hpp.1 t'
      cases P <;> simp [hAB, ep] at ht' ⊢ <;> omega
    · simp [SM.GameState.record, hep₁L]
    · simp [SM.GameState.record, hep₁L, Party.other_ne, hep_other]
    · dsimp [h'L]; rw [Function.update_self]
    · simp only [SM.GameState.record, hst₁L, Function.update_of_ne (Party.other_ne P),
        Function.update_self, hroot_other]
      dsimp [h'R, st'L, p]
      rw [Function.update_self]
      exact ⟨rfl, rfl⟩
    · intro htL hunh
      have hcond : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = false := by
        cases tL with
        | none => simp at htL
        | some l => simp [decide_eq_false (by omega : ¬(healEpoch (some l) + Δcka ≤ ep))]
      have hcs' : cs' = cs.afterSend P c_cka.1 c_cka.2.1 := by
        dsimp [cs']; rw [hcond]; rfl
      rw [hcs']
      simp [CKA.GameState.afterSend, (hcka.2 P htL hunh).2, ep]
  · intro hlt
    have hmax_new :
        max ((s₁L.record (2 + Δcka) P st'L recL isChall).epoch .A)
            ((s₁L.record (2 + Δcka) P st'L recL isChall).epoch .B) = ep + 1 := by
      simp only [SM.GameState.record, hep₁L]
      cases P <;> simp [Function.update, hAB, ep]
    rw [hmax_new] at hlt ⊢
    rw [senderOf_eq_of_sendsIn hsends]
    simp only [SM.GameState.record, Function.update_self]
    exact hps' hlt

theorem runHM_hooksCKA_startSend_none_some [DecidableEq T] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig) (coins : CCoins)
    (h : CKAState T I) (cs : CKA.GameState Γ T)
    (htL : tL.isNone = false) (hcanSend : cs.canSend P = true)
    (hallow : decide (cs.epoch P + 1 + 2 ≤ healEpoch tL) = true)
    (hcsep : cs.epoch P = ep) (hcsst : cs.st P = γ) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).startSend ctx P (ep + 1) none σ (some coins))
      h cs =
      pure ((some (if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)
                   then some (cka.send γ coins).1 else none,
        (cka.send γ coins).2.1,
        (prng.up σ (cka.send γ coins).2.2).1,
        fs.initSender (prng.up σ (cka.send γ coins).2.2).2),
        { cache := Function.update h.cache (ep + 1)
            (some ((cka.send γ coins).2.1, (cka.send γ coins).2.2)) }),
        cs.afterSend P (cka.send γ coins).1 (cka.send γ coins).2.1) := by
  unfold hooksCKA
  dsimp only
  rw [runHM_bind, runHM_liftC_sendBad]
  simp only [hcanSend, Bool.not_true, hallow, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, hcsst, pure_bind]
  rw [runHM_bind, runHM_cacheC, pure_bind]
  by_cases hfin : healEpoch tL + Δcka ≤ ep + 1
  · have hfin' : (⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1 := hfin
    simp only [hfin', ↓reduceIte]
    rw [runHM_bind, runHM_liftC_corr, pure_bind]
    simp [CKA.GameState.finished, CKA.GameState.afterSend, hcsep, hfin, runHM_pure]
  · have hfin' : ¬((⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1) := hfin
    simp [hfin', htL, hfin, runHM_pure]

theorem runHM_hooksCKA_startSend_none_heal [DecidableEq T] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig)
    (h : CKAState T I) (cs : CKA.GameState Γ T)
    (htL : tL.isNone = false) (hcanSend : cs.canSend P = true)
    (heqH : ep + 1 = healEpoch tL) (hcsb : cs.b = true)
    (hcsep : cs.epoch P = ep) (hcsst : cs.st P = γ) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).startSend ctx P (ep + 1) none σ none)
      h cs =
      (($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
        ($ᵗ I : ProbComp I) >>= fun Ir =>
        pure ((some (if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)
                     then some (cka.send γ coins).1 else none,
          (cka.send γ coins).2.1,
          (prng.up σ Ir).1,
          fs.initSender (prng.up σ Ir).2),
          { cache := Function.update h.cache (ep + 1)
              (some ((cka.send γ coins).2.1, Ir)) }),
          cs.afterSend P (cka.send γ coins).1 (cka.send γ coins).2.1)) := by
  have hcs_eqH : (cs.epoch P + 1 != healEpoch tL) = false := by
    rw [hcsep]; simp [heqH]
  have hiteH :
      ∀ {α : Type} (x y : α),
        (if ep + 1 = (⟨false, tL, tStar⟩ : Mode).tH then x else y) = x := by
    intro α x y; change (if ep + 1 = healEpoch tL then x else y) = x
    split <;> [rfl; contradiction]
  unfold hooksCKA
  dsimp only
  rw [hiteH, runHM_bind, runHM_liftC_chall cka Δcka (healEpoch tL) P h cs hcsb]
  simp only [hcanSend, Bool.not_true, hcs_eqH, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, hcsst, bind_assoc, pure_bind]
  refine bind_congr fun coins => bind_congr fun Ir => ?_
  rw [runHM_bind, runHM_cacheC, pure_bind]
  by_cases hfin : healEpoch tL + Δcka ≤ ep + 1
  · have hfin' : (⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1 := hfin
    simp only [hfin', ↓reduceIte]
    rw [runHM_bind, runHM_liftC_corr, pure_bind]
    simp [CKA.GameState.finished, CKA.GameState.afterSend, hcsep, hfin, runHM_pure]
  · have hfin' : ¬((⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1) := hfin
    simp [hfin', htL, hfin, runHM_pure]

theorem runHM_hooksCKA_startSend_none_send [DecidableEq T] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (ep : ℕ) (γ : Γ) (σ : Sig)
    (h : CKAState T I) (cs : CKA.GameState Γ T)
    (htL : tL.isNone = false) (hcanSend : cs.canSend P = true)
    (hneH : ep + 1 ≠ healEpoch tL)
    (hcsep : cs.epoch P = ep) (hcsst : cs.st P = γ) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
      ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).startSend ctx P (ep + 1) none σ none)
      h cs =
      (($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
        pure ((some (if tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)
                     then some (cka.send γ coins).1 else none,
          (cka.send γ coins).2.1,
          (prng.up σ (cka.send γ coins).2.2).1,
          fs.initSender (prng.up σ (cka.send γ coins).2.2).2),
          { cache := Function.update h.cache (ep + 1)
              (some ((cka.send γ coins).2.1, (cka.send γ coins).2.2)) }),
          cs.afterSend P (cka.send γ coins).1 (cka.send γ coins).2.1)) := by
  have hcs_neH : (cs.epoch P + 1 == healEpoch tL) = false := by
    rw [hcsep]; exact beq_eq_false_iff_ne.mpr hneH
  have hiteH :
      ∀ {α : Type} (x y : α),
        (if ep + 1 = (⟨false, tL, tStar⟩ : Mode).tH then x else y) = y := by
    intro α x y; change (if ep + 1 = healEpoch tL then x else y) = y
    split <;> [contradiction; rfl]
  unfold hooksCKA
  dsimp only
  rw [hiteH, runHM_bind, runHM_liftC_send cka Δcka (healEpoch tL) P h cs]
  simp only [hcanSend, Bool.not_true, hcs_neH, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, hcsst, bind_map_left]
  refine bind_congr fun coins => ?_
  rw [runHM_bind, runHM_cacheC, pure_bind]
  by_cases hfin : healEpoch tL + Δcka ≤ ep + 1
  · have hfin' : (⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1 := hfin
    simp only [hfin', ↓reduceIte]
    rw [runHM_bind, runHM_liftC_corr, pure_bind]
    simp [CKA.GameState.finished, CKA.GameState.afterSend, hcsep, hfin, runHM_pure]
  · have hfin' : ¬((⟨false, tL, tStar⟩ : Mode).tH + Δcka ≤ ep + 1) := hfin
    simp [hfin', htL, hfin, runHM_pure]

theorem prng_pre_of_sync_sendsIn {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {tL : Option ℕ}
    {tStar : ℕ}
    {esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {cs : CKA.GameState Γ T}
    {esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)}
    {ps : PRFPRNG.GameState Sig I K} {P : Party}
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps))
    (hsends : P.sendsIn (esL.g.epoch P + 1) = true) :
    let ep := esL.g.epoch P
    (esR.g.st P).root =
      (if decide (tStar ≤ ep) || (tL.isSome && decide (ep < healEpoch tL))
       then some (esL.g.st P).root else none) ∧
    (ep < tStar →
      ps.b = false ∧ ps.prf = false ∧ ps.prng = false ∧
      ps.corr = (tL.isSome && decide (ep < healEpoch tL)) ∧
      ps.σ = (esL.g.st P).root) := by
  intro ep
  rcases hs with ⟨_, _, _, _, hp, _, hpp, hprng⟩
  dsimp only at hp hpp hprng
  refine ⟨(hp P).2.2.2.2.2.2.2.2, fun hlt => ?_⟩
  rcases hpp.synced_of_sendsIn hsends with ⟨hAB, hrootAB⟩
  have hmax : max (esL.g.epoch .A) (esL.g.epoch .B) = ep := by
    cases P <;> simp [hAB, ep]
  have hprng' := hprng
  dsimp [PRNGRel] at hprng'
  rw [hmax] at hprng'
  rcases hprng' hlt with ⟨hb, hprf, hprng1, hcorr, hσ⟩
  refine ⟨hb, hprf, hprng1, hcorr, hσ.trans ?_⟩
  cases Party.senderOf ep <;> cases P <;> simp [hrootAB]

theorem evalEng_sendCore_sync [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (b : Bool) (P : Party) (m : M) (pair : Option (M × M)) (rcoins : Option CCoins)
    (isChall : Bool)
    (s₁L : Ctx (Option Γ) T Sig SS RS M E)
    (s₁R : Ctx Γ T (Option Sig) SS RS M E)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps))
    (hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁L)
    (hepR : esR.g.epMgmt (2 + Δcka) qep P rcoins.isSome = some s₁R)
    (hld : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L = false)
    (ih : ∀ r sL' sR', Sync prng Δcka tL tStar sL' sR' →
      DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sL')
          (evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sR')) :
    DEq (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (sendCore (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) s₁L P m pair rcoins isChall) (esL, cs) >>=
          fun r => evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
        (runEM (PRFPRNG.oracleImpl prng)
          (sendCore (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) s₁R P m pair rcoins isChall) (esR, ps) >>=
          fun r => evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2) := by
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  have hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps) :=
    ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only at habL habR he hinv hp hcka hpp hprng
  rcases eraseSt_epMgmt_some he hepL with ⟨s₁R', hepR', he₁, hst₁L, hst₁R⟩
  rw [hepR] at hepR'; injection hepR' with hepR'; subst hepR'
  by_cases hmL : MissedTL tL s₁L
  · have hmR : MissedTL tL s₁R := eraseSt_missedTL he₁ hmL
    exact (evalEng_sendCore_of_missedTL _ _ (2 + Δcka) qep fs.maxSkip (Config.priv tStar)
      ⟨false, tL, tStar⟩ b s₁L P m pair rcoins isChall k (esL, cs) hmL).trans
      (evalEng_sendCore_of_missedTL _ _ (2 + Δcka) qep fs.maxSkip (Config.priv tStar)
        ⟨false, tL, tStar⟩ b s₁R P m pair rcoins isChall k (esR, ps) hmR).symm
  · rcases hp P with ⟨hidL, hidR, htcurL, htcurR, hvS, hvR, hTcur, hγ, hroot⟩
    set ep := esL.g.epoch P
    have hfsL : ∀ ctx P t ss h m pair,
        (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).fsSend ctx P t ss h m pair =
          pure (some (fs.send ss h m)) := fun _ _ _ _ _ _ _ => rfl
    have hfsR : ∀ ctx P t ss h m pair,
        (hooksPRNG cka prng fs ⟨false, tL, tStar⟩).fsSend ctx P t ss h m pair =
          pure (some (fs.send ss h m)) := fun _ _ _ _ _ _ _ => rfl
    by_cases hsends : P.sendsIn (ep + 1) = true
    · have hsendsL : (s₁L.st P).id.sendsIn ((s₁L.st P).tcur + 1) = true := by
        rw [hst₁L, hidL, htcurL]; exact hsends
      have hsendsR : (s₁R.st P).id.sendsIn ((s₁R.st P).tcur + 1) = true := by
        rw [hst₁R, hidR, htcurR]; exact hsends
      rw [runEM_sendCore_sendsIn_true _ _ fs hfsL _ s₁L P m pair rcoins isChall esL cs hsendsL,
          runEM_sendCore_sendsIn_true _ _ fs hfsR _ s₁R P m pair rcoins isChall esR ps hsendsR]
      simp only [hst₁L, hst₁R, htcurL, htcurR]
      rcases prng_pre_of_sync_sendsIn hs hsends with ⟨hroot_pre, hps_pre⟩
      rcases hpp.synced_of_sendsIn hsends with ⟨hAB, _⟩
      by_cases hloc : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = true
      ·
        have hγ_some : (esL.g.st P).γ = some (esR.g.st P).γ := by rw [hγ, hloc]; rfl
        have hloc_next : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep + 1)) = true := by
          rcases Bool.or_eq_true_iff.mp hloc with h1 | h2
          · simp [h1]
          · simp only [decide_eq_true_eq] at h2
            simp [decide_eq_true (by omega : healEpoch tL + Δcka ≤ ep + 1)]
        have hnotH : ¬(tL.isSome = true ∧ ep + 1 = healEpoch tL) := by
          rintro ⟨htL, heqH⟩
          rcases Bool.or_eq_true_iff.mp hloc with h1 | h2
          · cases tL <;> simp at h1 htL
          · simp only [decide_eq_true_eq] at h2; omega
        rw [hγ_some]
        cases rcoins with
        | some coins =>
          rcases runHM_rootPRNG_known prng esR.h ps hvg (fun _ => hroot_pre)
            (fun _ => hps_pre) (by omega) hnotH (Ik := (cka.send (esR.g.st P).γ coins).2.2) with
            ⟨ps', hroot_run, hps'⟩
          have hstartL :
              runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
                ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).startSend
                  s₁L P (ep + 1) (some (esR.g.st P).γ) (esL.g.st P).root (some coins)) esL.h cs =
                let c := cka.send (esR.g.st P).γ coins
                let p := prng.up (esL.g.st P).root c.2.2
                pure ((some (some c.1, c.2.1, p.1, fs.initSender p.2),
                  { cache := Function.update esL.h.cache (ep + 1) (some (c.2.1, c.2.2)) }), cs) := by
            unfold hooksCKA
            dsimp only
            rw [runHM_bind, runHM_pure, pure_bind]
            dsimp only
            rw [runHM_bind, runHM_cacheC, pure_bind, runHM_pure]
          have hstartR :
              runHM (PRFPRNG.oracleImpl prng)
                ((hooksPRNG cka prng fs ⟨false, tL, tStar⟩).startSend
                  s₁R P (ep + 1) (esR.g.st P).γ (esR.g.st P).root (some coins)) esR.h ps =
                let c := cka.send (esR.g.st P).γ coins
                let p := prng.up (esL.g.st P).root c.2.2
                let σ'R := if decide (tStar ≤ ep + 1) || (tL.isSome && decide (ep + 1 < healEpoch tL))
                           then some p.1 else none
                pure ((some (c.1, c.2.1, σ'R, fs.initSender p.2),
                  { cache := Function.update esR.h.cache (ep + 1) (some (c.2.1, σ'R, p.2)) }), ps') := by
            unfold hooksPRNG
            dsimp only
            rw [runHM_bind, runHM_pure, pure_bind]
            dsimp only
            rw [runHM_bind, hroot_run, pure_bind]
            dsimp only
            rw [runHM_bind, runHM_modify, pure_bind, runHM_pure]
          rw [hstartL, hstartR]
          simp only [pure_bind]
          have hsync' := sync_after_new_send cka prng fs Δcka qep tL tStar P m true isChall
            coins (cka.send (esR.g.st P).γ coins).2.2 s₁L s₁R esL cs esR ps ps'
            hs hsends hepL hepR hps'
          dsimp only [ep] at hloc hloc_next ⊢
          simp only [hst₁L, hst₁R, hloc_next, hloc, ↓reduceIte] at hsync'
          exact ih _ _ _ hsync'
        | none =>
          have hstartL :
              runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
                ((hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩).startSend
                  s₁L P (ep + 1) (some (esR.g.st P).γ) (esL.g.st P).root none) esL.h cs =
                ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                  let c := cka.send (esR.g.st P).γ coins
                  let p := prng.up (esL.g.st P).root c.2.2
                  pure ((some (some c.1, c.2.1, p.1, fs.initSender p.2),
                    { cache := Function.update esL.h.cache (ep + 1) (some (c.2.1, c.2.2)) }), cs) := by
            unfold hooksCKA
            dsimp only
            rw [runHM_bind, runHM_sampleT, bind_map_left]
            refine bind_congr fun coins => ?_
            dsimp only
            rw [runHM_bind, runHM_cacheC, pure_bind, runHM_pure]
          rw [hstartL]
          unfold hooksPRNG
          dsimp only
          rw [runHM_bind, runHM_sampleT, bind_map_left]
          simp only [bind_assoc]
          refine DEq.bind_right ($ᵗ CCoins) fun coins => ?_
          rcases runHM_rootPRNG_known prng esR.h ps hvg (fun _ => hroot_pre)
            (fun _ => hps_pre) (by omega) hnotH (Ik := (cka.send (esR.g.st P).γ coins).2.2) with
            ⟨ps', hroot_run, hps'⟩
          rw [runHM_bind, hroot_run]
          simp only [pure_bind]
          rw [runHM_bind, runHM_modify]
          simp only [pure_bind, runHM_pure]
          have hsync' := sync_after_new_send cka prng fs Δcka qep tL tStar P m false isChall
            coins (cka.send (esR.g.st P).γ coins).2.2 s₁L s₁R esL cs esR ps ps'
            hs hsends hepL hepR hps'
          dsimp only [ep] at hloc hloc_next ⊢
          simp only [hst₁L, hst₁R, hloc_next, hloc, ↓reduceIte] at hsync'
          exact ih _ _ _ hsync'
      ·
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at hloc
        rcases hloc with ⟨htL_not_none, hunh⟩
        have htL_some : tL.isSome = true := by cases tL <;> simp at htL_not_none ⊢
        have htL_none_false : tL.isNone = false := by cases tL <;> simp at htL_not_none ⊢
        have hloc_false : (tL.isNone || decide (healEpoch tL + Δcka ≤ ep)) = false := by
          simp [htL_none_false, decide_eq_false (by omega : ¬(healEpoch tL + Δcka ≤ ep))]
        have hγ_none : (esL.g.st P).γ = none := by rw [hγ, hloc_false]; rfl
        rw [hγ_none]
        have hPO : esL.g.epoch P.other = ep := by cases P <;> dsimp [ep, Party.other] <;> omega
        have hunh_other : esL.g.epoch P.other < healEpoch tL + Δcka := by rw [hPO]; exact hunh
        rcases hcka.2 P htL_some hunh with ⟨hcs_stP, hcs_epP⟩
        rcases hcka.2 P.other htL_some hunh_other with ⟨_, hcs_epO⟩
        have hcanSend : cs.canSend P = true := by
          unfold CKA.GameState.canSend
          rw [hcs_epP, hcs_epO]
          simp [hPO, ep, hsends]
        cases rcoins with
        | some coins =>
          rcases Option.isSome_iff_exists.mp htL_some with ⟨l, htL_eq⟩
          by_cases hle_l : ep + 1 ≤ l
          ·
            have hallow : decide (cs.epoch P + 1 + 2 ≤ healEpoch tL) = true := by
              rw [hcs_epP, htL_eq]; dsimp [healEpoch, ep]; exact decide_eq_true (by omega)
            have hnotH : ¬(tL.isSome = true ∧ ep + 1 = healEpoch tL) := by
              rw [htL_eq]; dsimp [healEpoch]; omega
            rcases runHM_rootPRNG_known prng esR.h ps hvg (fun _ => hroot_pre)
              (fun _ => hps_pre) (by omega) hnotH (Ik := (cka.send (esR.g.st P).γ coins).2.2) with
              ⟨ps', hroot_run, hps'⟩
            rw [runHM_hooksCKA_startSend_none_some cka prng fs Δcka tL tStar s₁L P ep
              (esR.g.st P).γ (esL.g.st P).root coins esL.h cs
              htL_none_false hcanSend hallow hcs_epP hcs_stP]
            simp only [pure_bind]
            unfold hooksPRNG
            dsimp only
            rw [runHM_bind, runHM_pure]
            simp only [pure_bind]
            rw [runHM_bind, hroot_run]
            simp only [pure_bind]
            rw [runHM_bind, runHM_modify]
            simp only [pure_bind, runHM_pure]
            have hsync' := sync_after_new_send cka prng fs Δcka qep tL tStar P m true isChall
              coins (cka.send (esR.g.st P).γ coins).2.2 s₁L s₁R esL cs esR ps ps'
              hs hsends hepL hepR hps'
            dsimp only [ep] at hloc_false ⊢
            simp only [hst₁L, hst₁R, hloc_false, Bool.false_eq_true, ↓reduceIte] at hsync'
            exact ih _ _ _ hsync'
          ·
            have hlt_l : l < ep + 1 := by omega
            have hvh : healEpoch (some l) + Δcka ≤ tStar := by
              rcases validGuess_healed hvg with hnone | ⟨l', heq', _, hvh'⟩
              · rw [htL_eq] at hnone; contradiction
              · rw [htL_eq] at heq'; injection heq' with heq'; subst heq'
                rw [htL_eq] at hvh'; exact hvh'
            have hmL' : MissedTL tL s₁L := by
              subst htL_eq
              exact missedTL_of_bad_send hinv hAB hsends hepL hld hvh hunh hlt_l
            exact absurd hmL' hmL
        | none =>
          by_cases heqH : ep + 1 = healEpoch tL
          ·
            have hep_lt_tStar : ep < tStar := by
              rcases validGuess_healed hvg with hnone | ⟨l, _, _, hvh⟩
              · rw [hnone] at htL_some; contradiction
              · omega
            rcases hps_pre hep_lt_tStar with ⟨hps_b, hps_prf, hps_prng, _, hps_σ⟩
            rw [runHM_hooksCKA_startSend_none_heal cka prng fs Δcka tL tStar s₁L P ep
              (esR.g.st P).γ (esL.g.st P).root esL.h cs
              htL_none_false hcanSend heqH hcka.1 hcs_epP hcs_stP]
            simp only [bind_assoc, pure_bind]
            unfold hooksPRNG
            dsimp only
            rw [runHM_bind, runHM_sampleT, bind_map_left]
            simp only [bind_assoc]
            refine DEq.bind_right ($ᵗ CCoins) fun coins => ?_
            rcases runHM_rootPRNG_heal (prng := prng) esR.h ps hvg htL_some heqH
              ⟨hps_b, hps_prf, hps_prng, hps_σ⟩
              (Ik := (cka.send (esR.g.st P).γ coins).2.2) (σv := (esR.g.st P).root) with
              ⟨ps', hroot_heal, hps'⟩
            rw [runHM_bind, hroot_heal, bind_map_left]
            simp only [bind_assoc]
            refine DEq.bind_right ($ᵗ I) fun Ir => ?_
            rw [runHM_bind, runHM_modify]
            simp only [pure_bind, runHM_pure]
            have hsync' := sync_after_new_send cka prng fs Δcka qep tL tStar P m false isChall
              coins Ir s₁L s₁R esL cs esR ps (ps' Ir)
              hs hsends hepL hepR (hps' Ir)
            dsimp only [ep] at hloc_false ⊢
            simp only [hst₁L, hst₁R, hloc_false, Bool.false_eq_true, ↓reduceIte] at hsync'
            exact ih _ _ _ hsync'
          ·
            have hnotH : ¬(tL.isSome = true ∧ ep + 1 = healEpoch tL) := fun h => heqH h.2
            rw [runHM_hooksCKA_startSend_none_send cka prng fs Δcka tL tStar s₁L P ep
              (esR.g.st P).γ (esL.g.st P).root esL.h cs
              htL_none_false hcanSend heqH hcs_epP hcs_stP]
            simp only [bind_assoc, pure_bind]
            unfold hooksPRNG
            dsimp only
            rw [runHM_bind, runHM_sampleT, bind_map_left]
            simp only [bind_assoc]
            refine DEq.bind_right ($ᵗ CCoins) fun coins => ?_
            rcases runHM_rootPRNG_known prng esR.h ps hvg (fun _ => hroot_pre)
              (fun _ => hps_pre) (by omega) hnotH (Ik := (cka.send (esR.g.st P).γ coins).2.2) with
              ⟨ps', hroot_run, hps'⟩
            rw [runHM_bind, hroot_run]
            simp only [pure_bind]
            rw [runHM_bind, runHM_modify]
            simp only [pure_bind, runHM_pure]
            have hsync' := sync_after_new_send cka prng fs Δcka qep tL tStar P m false isChall
              coins (cka.send (esR.g.st P).γ coins).2.2 s₁L s₁R esL cs esR ps ps'
              hs hsends hepL hepR hps'
            dsimp only [ep] at hloc_false ⊢
            simp only [hst₁L, hst₁R, hloc_false, Bool.false_eq_true, ↓reduceIte] at hsync'
            exact ih _ _ _ hsync'
    ·
      have hsendsF : P.sendsIn (ep + 1) = false :=
         Bool.eq_false_iff.mpr hsends
      have hs₁L_eq := epMgmt_sendsIn_false hsendsF hepL
      have hs₁R_eq := epMgmt_sendsIn_false (eraseSt_epoch he ▸ hsendsF) hepR
      subst hs₁L_eq; subst hs₁R_eq
      have hsendsL : (esL.g.st P).id.sendsIn ((esL.g.st P).tcur + 1) = false := by
        rw [hidL, htcurL]; exact hsendsF
      have hsendsR : (esR.g.st P).id.sendsIn ((esR.g.st P).tcur + 1) = false := by
        rw [hidR, htcurR]; exact hsendsF
      rw [runEM_sendCore_sendsIn_false _ _ fs hfsL _ esL.g P m pair rcoins isChall esL cs hsendsL,
          runEM_sendCore_sendsIn_false _ _ fs hfsR _ esR.g P m pair rcoins isChall esR ps hsendsR]
      simp only [htcurL, htcurR, ← hTcur, ← hvS, pure_bind]
      have hepochR : esR.g.epoch P = esL.g.epoch P := (congrFun (eraseSt_epoch he) P).symm
      have hidxR : esR.g.idx P = esL.g.idx P := (congrFun (eraseSt_idx he) P).symm
      have hsync' := sync_after_same_send prng fs Δcka tL tStar P m isChall esL cs esR ps hs
      dsimp only [ep] at htcurL htcurR hsync' ⊢
      rw [hepochR, hidxR]
      cases hvs : (esL.g.st P).vS <;>
        (simp only [hvs, htcurL, htcurR, ← hTcur] at hsync' ⊢; exact ih _ _ _ hsync')

theorem evalEng_transmitE_sync [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (b : Bool) (P : Party) (m : M) (rcoins : Option CCoins)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps))
    (ih : ∀ r sL' sR', Sync prng Δcka tL tStar sL' sR' →
      DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sL')
          (evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sR')) :
    DEq (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (transmitE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep ⟨false, tL, tStar⟩ ⟨P, m, rcoins⟩) (esL, cs) >>=
          fun r => evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
        (runEM (PRFPRNG.oracleImpl prng)
          (transmitE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep ⟨false, tL, tStar⟩ ⟨P, m, rcoins⟩) (esR, ps) >>=
          fun r => evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2) := by
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  have hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps) :=
    ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only at habL habR he hinv
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  unfold transmitE
  dsimp only
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]
  dsimp only
  rw [habL, habR, hwin]
  by_cases hg : (false || esL.g.win) = true
  · simp only [hg, ↓reduceIte, runEM_pure, pure_bind]
    exact ih none (esL, cs) (esR, ps) hs
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    cases hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome with
    | none =>
      rw [eraseSt_epMgmt_none he hepL, runEM_pure, runEM_pure, pure_bind, pure_bind]
      exact ih none (esL, cs) (esR, ps) hs
    | some s₁L =>
      rcases eraseSt_epMgmt_some he hepL with ⟨s₁R, hepR, he₁, _, _⟩
      rw [hepR]
      dsimp only
      have hld_eq : Policy.leakDoom ⟨false, tL, tStar⟩ esR.g s₁R =
          Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L :=
        (eraseSt_leakDoom he he₁ ⟨false, tL, tStar⟩).symm
      rw [hld_eq]
      cases hld : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact evalEng_sendCore_sync cka prng fs Δcka qep tL tStar b P m none rcoins false
          s₁L s₁R esL cs esR ps k hvg hs hepL hepR hld ih
      · simp only [↓reduceIte, runEM_abort_pure, pure_bind]
        exact (evalEng_doom _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).trans
          (evalEng_doom _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).symm

theorem evalEng_challE_sync [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (b : Bool) (P : Party) (m₀ m₁ : M) (rcoins : Option CCoins)
    (esL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (cs : CKA.GameState Γ T)
    (esR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K))
    (ps : PRFPRNG.GameState Sig I K)
    (k : Option (Header T × E) →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps))
    (ih : ∀ r sL' sR', Sync prng Δcka tL tStar sL' sR' →
      DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sL')
          (evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r) sR')) :
    DEq (runEM (CKA.oracleImpl cka Δcka (healEpoch tL))
          (challE (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨P, m₀, m₁, rcoins⟩) (esL, cs) >>=
          fun r => evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
            (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2)
        (runEM (PRFPRNG.oracleImpl prng)
          (challE (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep (Config.priv tStar) ⟨false, tL, tStar⟩ ⟨P, m₀, m₁, rcoins⟩) (esR, ps) >>=
          fun r => evalEng (PRFPRNG.oracleImpl prng)
            (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b (k r.1) r.2) := by
  rcases hs with ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  have hs : Sync prng Δcka tL tStar (esL, cs) (esR, ps) :=
    ⟨habL, habR, he, hinv, hp, hcka, hpp, hprng⟩
  dsimp only at habL habR he hinv
  have hwin : esR.g.win = esL.g.win := (eraseSt_win he).symm
  unfold challE
  dsimp only
  rw [runEM_bind, runEM_get, pure_bind, runEM_bind, runEM_get, pure_bind]
  dsimp only
  rw [habL, habR, hwin]
  by_cases hg : (false || esL.g.win) = true
  · simp only [hg, ↓reduceIte, runEM_pure, pure_bind]
    exact ih none (esL, cs) (esR, ps) hs
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    cases hepL : esL.g.epMgmt (2 + Δcka) qep P rcoins.isSome with
    | none =>
      rw [eraseSt_epMgmt_none he hepL, runEM_pure, runEM_pure, pure_bind, pure_bind]
      exact ih none (esL, cs) (esR, ps) hs
    | some s₁L =>
      rcases eraseSt_epMgmt_some he hepL with ⟨s₁R, hepR, he₁, _, _⟩
      rw [hepR]
      dsimp only
      have hsc_eq : s₁R.safeCh (2 + Δcka) P = s₁L.safeCh (2 + Δcka) P :=
        (eraseSt_safeCh he₁ (2 + Δcka) P).symm
      have hep₁_eq : s₁R.epoch P = s₁L.epoch P := (congrFun (eraseSt_epoch he₁) P).symm
      have hb_eq : esR.g.b = esL.g.b := (eraseSt_b he).symm
      have hchallOK_eq :
          (Config.priv (Msg := M) tStar).challAllowedIn (s₁R.epoch P) =
            (Config.priv (Msg := M) tStar).challAllowedIn (s₁L.epoch P) := by rw [hep₁_eq]
      rw [hsc_eq, hchallOK_eq]
      by_cases hsc :
          (!s₁L.safeCh (2 + Δcka) P || !(Config.priv (Msg := M) tStar).challAllowedIn (s₁L.epoch P)) = true
      · simp only [hsc, ↓reduceIte, runEM_pure, pure_bind]
        exact ih none (esL, cs) (esR, ps) hs
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte]
        have hld_eq : Policy.leakDoom ⟨false, tL, tStar⟩ esR.g s₁R =
            Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L :=
          (eraseSt_leakDoom he he₁ ⟨false, tL, tStar⟩).symm
        rw [hld_eq]
        cases hld : Policy.leakDoom ⟨false, tL, tStar⟩ esL.g s₁L
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hm_eq :
              ((Config.priv (Msg := M) tStar).challMsg (s₁R.epoch P)).getD
                (if esR.g.b then m₁ else m₀) =
              ((Config.priv (Msg := M) tStar).challMsg (s₁L.epoch P)).getD
                (if esL.g.b then m₁ else m₀) := by rw [hep₁_eq, hb_eq]
          rw [hm_eq]
          set m := ((Config.priv (Msg := M) tStar).challMsg (s₁L.epoch P)).getD
            (if esL.g.b then m₁ else m₀)
          exact evalEng_sendCore_sync cka prng fs Δcka qep tL tStar b P m (some (m₀, m₁)) rcoins true
            s₁L s₁R esL cs esR ps k hvg hs hepL hepR hld ih
        · simp only [↓reduceIte, runEM_abort_pure, pure_bind]
          exact (evalEng_doom _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).trans
            (evalEng_doom _ _ _ _ _ _ _ _ _ _ (Or.inl rfl)).symm

theorem runEM_coinsE_bind {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS Γv Sv SSv RSv HS α : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp)) (n : ℕ)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (f : Fin (n + 1) × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) → ProbComp α) :
    runEM oimpl (coinsE n : EM tspec Γv T Sv SSv RSv M E HS _) s >>= f =
      (query (spec := unifSpec) n : ProbComp _) >>= fun x => f (x, s) := by
  simp [runEM, coinsE, outerFull, StateT.run_lift, simulateQ_query]

theorem evalEng_sync [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I]
    [Inhabited E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (sL : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I) ×
      CKA.GameState Γ T)
    (sR : EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true)
    (hs : Sync prng Δcka tL tStar sL sR) :
    DEq (evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
          (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b oa sL)
        (evalEng (PRFPRNG.oracleImpl prng)
          (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
          (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b oa sR) := by
  induction oa using OracleComp.inductionOn generalizing sL sR with
  | pure b' =>
    rw [evalEng_pure, evalEng_pure, hs.privOutP_eq]
  | query_bind q k ih =>
    rw [evalEng_query_bind, evalEng_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    rcases sL with ⟨esL, cs⟩
    rcases sR with ⟨esR, ps⟩
    rcases q with n | ⟨⟨⟨⟨⟨P, m, rcoins⟩ | ⟨P, m₀, m₁, rcoins⟩⟩ | ⟨P, c⟩⟩ | ⟨P, c⟩⟩ | P⟩
    ·
      change DEq (runEM _ (coinsE n) (esL, cs) >>= _) (runEM _ (coinsE n) (esR, ps) >>= _)
      rw [runEM_coinsE_bind, runEM_coinsE_bind]
      exact DEq.bind_right _ fun x => ih x (esL, cs) (esR, ps) hs
    ·
      exact evalEng_transmitE_sync cka prng fs Δcka qep tL tStar b P m rcoins
        esL cs esR ps k hvg hs ih
    ·
      exact evalEng_challE_sync cka prng fs Δcka qep tL tStar b P m₀ m₁ rcoins
        esL cs esR ps k hvg hs ih
    ·
      rcases runEM_deliverE_sync cka prng fs Δcka fs.maxSkip (Config.priv tStar) tL tStar
        ⟨P, c⟩ esL cs esR ps hs with ⟨out, sL', sR', hL, hR, hs'⟩
      change DEq (runEM _ (deliverE _ _ _ ⟨P, c⟩) (esL, cs) >>= _)
                 (runEM _ (deliverE _ _ _ ⟨P, c⟩) (esR, ps) >>= _)
      rw [hL, hR, pure_bind, pure_bind]
      exact ih out sL' sR' hs'
    ·
      rcases runEM_injectE_sync cka prng fs Δcka qep (Config.priv tStar) tL tStar ⟨P, c⟩
        esL cs esR ps hs with ⟨out, sL', sR', hL, hR, hs'⟩
      change DEq (runEM _ (injectE _ _ _ _ ⟨P, c⟩) (esL, cs) >>= _)
                 (runEM _ (injectE _ _ _ _ ⟨P, c⟩) (esR, ps) >>= _)
      rw [hL, hR, pure_bind, pure_bind]
      exact ih out sL' sR' hs'
    ·
      rcases runEM_corrE_sync cka prng fs Δcka tL tStar P (esL, cs) (esR, ps) hs hvg with
        ⟨out, sL', sR', hL, hR, hsd⟩
      change DEq (runEM _ (corrE _ _ P) (esL, cs) >>= _)
                 (runEM _ (corrE _ _ P) (esR, ps) >>= _)
      rw [hL, hR, pure_bind, pure_bind]
      rcases hsd with hs' | ⟨hdL, hdR⟩
      · exact ih out sL' sR' hs'
      · exact (evalEng_doom _ _ _ _ _ _ _ _ _ sL' hdL).trans
          (evalEng_doom _ _ _ _ _ _ _ _ _ sR' hdR).symm

/-! ### Initial state coupling and main proof -/

theorem init_sync
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (b : Bool) (kr : KR) (kc_game kc : KC)
    (ps₁ : PRFPRNG.GameState Sig I K)
    (hkc : tL.isSome = true → kc_game = kc)
    (hps₁ : 0 < tStar →
      ps₁.b = false ∧ ps₁.prf = false ∧ ps₁.prng = false ∧
      ps₁.corr = (tL.isSome && decide (0 < healEpoch tL)) ∧
      ps₁.σ = (prng.up (prng.init kr) lam).1) :
    let out := prng.up (prng.init kr) lam
    let γAL : Option Γ := if tL.isNone then some (cka.initA kc) else none
    let γBL : Option Γ := if tL.isNone then some (cka.initB kc) else none
    let σR : Option Sig :=
      if decide (tStar ≤ 0) || (tL.isSome && decide (0 < healEpoch tL))
      then some out.1 else none
    let pL := mkParties (T := T) γAL γBL out.1 (fs.initSender out.2) (fs.initReceiver out.2)
    let pR := mkParties (T := T) (cka.initA kc) (cka.initB kc) σR
      (fs.initSender out.2) (fs.initReceiver out.2)
    let gL : Ctx (Option Γ) T Sig SS RS M E :=
      { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
    let gR : Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with | .A => pR.1 | .B => pR.2, b }
    Sync prng Δcka tL tStar
      ({ g := gL, h := {} }, CKA.initState cka kc_game true)
      ({ g := gR, h := {} }, ps₁) := by
  intro out γAL γBL σR pL pR gL gR
  refine ⟨rfl, rfl, rfl, ⟨fun _ h => by contradiction, fun _ h => by contradiction⟩,
    ?_, ?_, ?_, ?_⟩
  · intro P
    cases tL <;> cases P <;>
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩ <;>
      simp [gL, gR, pL, pR, mkParties, γAL, γBL, healEpoch]
  · refine ⟨rfl, fun P htL _ => ?_⟩
    rw [hkc htL]
    cases P <;> exact ⟨rfl, rfl⟩
  · refine ⟨fun _ _ => ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · intro hlt
    exact hps₁ hlt

theorem runHM_initCKA_none [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka tStar : ℕ)
    (h : CKAState T I) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch none))
      (initCKA cka prng fs lam ⟨false, none, tStar⟩) h cs =
      ($ᵗ KR : ProbComp KR) >>= fun kr =>
        ($ᵗ KC : ProbComp KC) >>= fun kc =>
          let out := prng.up (prng.init kr) lam
          pure ((some (mkParties (some (cka.initA kc)) (some (cka.initB kc)) out.1
                  (fs.initSender out.2) (fs.initReceiver out.2)), h), cs) := by
  unfold initCKA
  dsimp only
  rw [runHM_bind, runHM_sampleT, bind_map_left]
  refine bind_congr fun kr => ?_
  dsimp only
  rw [runHM_bind, runHM_sampleT, bind_map_left]
  refine bind_congr fun kc => ?_
  dsimp only
  rw [runHM_bind, runHM_pure, pure_bind]
  dsimp only
  rw [runHM_pure]

theorem runHM_initCKA_some [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka l tStar : ℕ)
    (h : CKAState T I) (cs : CKA.GameState Γ T) :
    runHM (CKA.oracleImpl cka Δcka (healEpoch (some l)))
      (initCKA cka prng fs lam ⟨false, some l, tStar⟩) h cs =
      ($ᵗ KR : ProbComp KR) >>= fun kr =>
        let out := prng.up (prng.init kr) lam
        pure ((some (mkParties none none out.1
                (fs.initSender out.2) (fs.initReceiver out.2)), h), cs) := by
  unfold initCKA
  dsimp only
  rw [runHM_bind, runHM_sampleT, bind_map_left]
  refine bind_congr fun kr => ?_
  dsimp only
  rw [runHM_bind, runHM_pure, pure_bind]
  dsimp only
  rw [runHM_pure]

theorem branch_redCKAPriv_dEq_redPRNGPriv
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    DEq (CKA.branch cka Δcka (healEpoch tL) true
          (redCKAPriv cka prng fs lam Δcka qep tL tStar A))
        (PRFPRNG.branch prng false
          (redPRNGPriv cka prng fs lam Δcka qep tL tStar A)) := by
  have hLHS :
      CKA.branch cka Δcka (healEpoch tL) true
          (redCKAPriv cka prng fs lam Δcka qep tL tStar A) =
        (($ᵗ KC : ProbComp KC) >>= fun kc =>
          ($ᵗ Bool : ProbComp Bool) >>= fun b =>
          runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
            (initCKA cka prng fs lam ⟨false, tL, tStar⟩) {}
            (CKA.initState cka kc true) >>= fun x =>
          match x.1.1 with
          | none => ($ᵗ Bool : ProbComp Bool)
          | some (vA, vB) =>
            let g : Ctx (Option Γ) T Sig SS RS M E :=
              { st := fun P => match P with | .A => vA | .B => vB, b }
            evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
              (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
              (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b A
              ({ g, h := x.1.2 }, x.2)) := by
    refine bind_congr fun kc => ?_
    unfold redCKAPriv runCKA
    change Prod.fst <$> (simulateQ (outerFull (CKA.oracleImpl cka Δcka (healEpoch tL))) _).run
      (CKA.initState cka kc true) = _
    simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
      simulateQ_outerFull_sampleT, bind_map_left, map_bind, runHM]
    refine bind_congr fun b => bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
    cases vs with
    | none =>
      simp [simulateQ_outerFull_sampleT]
    | some vAvB =>
      rcases vAvB with ⟨vA, vB⟩
      simp only [evalEng, runEM, simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure,
        StateT.run_pure, pure_bind, bind_map_left, simulateQ_outerFull_privOut]
      rfl
  have hRHS :
      PRFPRNG.branch prng false
          (redPRNGPriv cka prng fs lam Δcka qep tL tStar A) =
        (($ᵗ KR : ProbComp KR) >>= fun kr =>
          ($ᵗ Bool : ProbComp Bool) >>= fun b =>
          runHM (PRFPRNG.oracleImpl prng)
            (initPRNG cka prng fs lam ⟨false, tL, tStar⟩) {}
            { σ := prng.init kr, b := false } >>= fun x =>
          match x.1.1 with
          | none => ($ᵗ Bool : ProbComp Bool)
          | some (vA, vB) =>
            let g : Ctx Γ T (Option Sig) SS RS M E :=
              { st := fun P => match P with | .A => vA | .B => vB, b }
            evalEng (PRFPRNG.oracleImpl prng)
              (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
              (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b A
              ({ g, h := x.1.2 }, x.2)) := by
    refine bind_congr fun kr => ?_
    unfold redPRNGPriv runPRNG
    change Prod.fst <$> (simulateQ (outerFull (PRFPRNG.oracleImpl prng)) _).run
      { σ := prng.init kr, b := false } = _
    simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
      simulateQ_outerFull_sampleT, bind_map_left, map_bind, runHM]
    refine bind_congr fun b => bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
    cases vs with
    | none =>
      simp [simulateQ_outerFull_sampleT]
    | some vAvB =>
      rcases vAvB with ⟨vA, vB⟩
      simp only [evalEng, runEM, simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure,
        StateT.run_pure, pure_bind, bind_map_left, simulateQ_outerFull_privOut]
      rfl
  rw [hLHS, hRHS]
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL tStar = true
  ·
    have hnotH0 : ¬(tL.isSome = true ∧ 0 = healEpoch tL) := by
      rintro ⟨htL, h0⟩
      cases tL with
      | none => simp at htL
      | some l => simp [healEpoch] at h0
    have hPRNG :
        DEq (($ᵗ KR : ProbComp KR) >>= fun kr =>
              ($ᵗ Bool : ProbComp Bool) >>= fun b =>
              runHM (PRFPRNG.oracleImpl prng)
                (initPRNG cka prng fs lam ⟨false, tL, tStar⟩) {}
                { σ := prng.init kr, b := false } >>= fun x =>
              match x.1.1 with
              | none => ($ᵗ Bool : ProbComp Bool)
              | some (vA, vB) =>
                let g : Ctx Γ T (Option Sig) SS RS M E :=
                  { st := fun P => match P with | .A => vA | .B => vB, b }
                evalEng (PRFPRNG.oracleImpl prng)
                  (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
                  (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b A
                  ({ g, h := x.1.2 }, x.2))
            (($ᵗ Bool : ProbComp Bool) >>= fun b =>
              ($ᵗ KR : ProbComp KR) >>= fun kr =>
              ($ᵗ KC : ProbComp KC) >>= fun kc =>
              evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
                (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
                (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b A
                (let out := prng.up (prng.init kr) lam
                 let γAL : Option Γ := if tL.isNone then some (cka.initA kc) else none
                 let γBL : Option Γ := if tL.isNone then some (cka.initB kc) else none
                 let pL := mkParties (T := T) γAL γBL out.1
                   (fs.initSender out.2) (fs.initReceiver out.2)
                 let gL : Ctx (Option Γ) T Sig SS RS M E :=
                   { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
                 ({ g := gL, h := {} }, CKA.initState cka kc true))) := by
      refine (DEq.swap ($ᵗ KR) ($ᵗ Bool) _).trans (DEq.bind_right ($ᵗ Bool) fun b => ?_)
      refine DEq.bind_right ($ᵗ KR) fun kr => ?_
      unfold initPRNG
      rw [runHM_bind, runHM_sampleT, bind_map_left, bind_assoc]
      refine DEq.bind_right ($ᵗ KC) fun kc => ?_
      dsimp only
      rcases runHM_rootPRNG_known prng ({} : PRNGState T Sig K)
        { σ := prng.init kr, b := false } hvg (fun h => absurd h (by omega))
        (fun h => absurd h (by omega)) (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) hnotH0
        (Ik := lam) (σv := none) with ⟨ps₁, hroot0, hps₁⟩
      rw [runHM_bind, hroot0, pure_bind]
      dsimp only
      rw [runHM_pure, pure_bind]
      dsimp only
      exact (evalEng_sync cka prng fs Δcka qep tL tStar b A _ _ hvg
        (init_sync cka prng fs lam Δcka tL tStar b kr kc kc ps₁ (fun _ => rfl) hps₁)).symm
    refine DEq.trans ?_ hPRNG.symm
    cases tL with
    | none =>
      have hCKA_none :
          ∀ kc_game : KC,
            DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
                  runHM (CKA.oracleImpl cka Δcka (healEpoch none))
                    (initCKA cka prng fs lam ⟨false, none, tStar⟩) {}
                    (CKA.initState cka kc_game true) >>= fun x =>
                  match x.1.1 with
                  | none => ($ᵗ Bool : ProbComp Bool)
                  | some (vA, vB) =>
                    let g : Ctx (Option Γ) T Sig SS RS M E :=
                      { st := fun P => match P with | .A => vA | .B => vB, b }
                    evalEng (CKA.oracleImpl cka Δcka (healEpoch none))
                      (hooksCKA cka prng fs Δcka ⟨false, none, tStar⟩)
                      (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, none, tStar⟩ b A
                      ({ g, h := x.1.2 }, x.2))
                (($ᵗ Bool : ProbComp Bool) >>= fun b =>
                  ($ᵗ KR : ProbComp KR) >>= fun kr =>
                  ($ᵗ KC : ProbComp KC) >>= fun kc =>
                  evalEng (CKA.oracleImpl cka Δcka (healEpoch none))
                    (hooksCKA cka prng fs Δcka ⟨false, none, tStar⟩)
                    (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, none, tStar⟩ b A
                    (let out := prng.up (prng.init kr) lam
                     let pL := mkParties (T := T) (some (cka.initA kc)) (some (cka.initB kc)) out.1
                       (fs.initSender out.2) (fs.initReceiver out.2)
                     let gL : Ctx (Option Γ) T Sig SS RS M E :=
                       { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
                     ({ g := gL, h := {} }, CKA.initState cka kc true))) := by
        intro kc_game
        refine DEq.bind_right ($ᵗ Bool) fun b => ?_
        rw [runHM_initCKA_none, bind_assoc]
        refine DEq.bind_right ($ᵗ KR) fun kr => ?_
        rw [bind_assoc]
        refine DEq.bind_right ($ᵗ KC) fun kc => ?_
        rw [pure_bind]
        dsimp only
        rcases runHM_rootPRNG_known prng ({} : PRNGState T Sig K)
          { σ := prng.init kr, b := false } hvg (fun h => absurd h (by omega))
          (fun h => absurd h (by omega)) (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) hnotH0
          (Ik := lam) (σv := none) with ⟨ps₁, _, hps₁⟩
        exact (evalEng_sync cka prng fs Δcka qep none tStar b A _ _ hvg
          (init_sync cka prng fs lam Δcka none tStar b kr kc_game kc ps₁
            (fun h => by contradiction) hps₁)).trans
          (evalEng_sync cka prng fs Δcka qep none tStar b A _ _ hvg
            (init_sync cka prng fs lam Δcka none tStar b kr kc kc ps₁
              (fun _ => rfl) hps₁)).symm
      exact (DEq.bind_right ($ᵗ KC) hCKA_none).trans (DEq.bind_const ($ᵗ KC) _)
    | some l =>
      have hCKA_some :
          DEq (($ᵗ KC : ProbComp KC) >>= fun kc =>
                ($ᵗ Bool : ProbComp Bool) >>= fun b =>
                runHM (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                  (initCKA cka prng fs lam ⟨false, some l, tStar⟩) {}
                  (CKA.initState cka kc true) >>= fun x =>
                match x.1.1 with
                | none => ($ᵗ Bool : ProbComp Bool)
                | some (vA, vB) =>
                  let g : Ctx (Option Γ) T Sig SS RS M E :=
                    { st := fun P => match P with | .A => vA | .B => vB, b }
                  evalEng (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                    (hooksCKA cka prng fs Δcka ⟨false, some l, tStar⟩)
                    (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, some l, tStar⟩ b A
                    ({ g, h := x.1.2 }, x.2))
              (($ᵗ KC : ProbComp KC) >>= fun kc =>
                ($ᵗ Bool : ProbComp Bool) >>= fun b =>
                ($ᵗ KR : ProbComp KR) >>= fun kr =>
                evalEng (CKA.oracleImpl cka Δcka (healEpoch (some l)))
                  (hooksCKA cka prng fs Δcka ⟨false, some l, tStar⟩)
                  (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, some l, tStar⟩ b A
                  (let out := prng.up (prng.init kr) lam
                   let pL := mkParties (T := T) none none out.1
                     (fs.initSender out.2) (fs.initReceiver out.2)
                   let gL : Ctx (Option Γ) T Sig SS RS M E :=
                     { st := fun P => match P with | .A => pL.1 | .B => pL.2, b }
                   ({ g := gL, h := {} }, CKA.initState cka kc true))) := by
        refine DEq.bind_right ($ᵗ KC) fun kc => DEq.bind_right ($ᵗ Bool) fun b => ?_
        rw [runHM_initCKA_some, bind_assoc]
        refine DEq.bind_right ($ᵗ KR) fun kr => ?_
        rw [pure_bind]
      refine hCKA_some.trans ?_
      refine (DEq.swap ($ᵗ KC) ($ᵗ Bool) _).trans (DEq.bind_right ($ᵗ Bool) fun b => ?_)
      exact DEq.swap ($ᵗ KC) ($ᵗ KR) _
  ·
    have hvgF : lastLeakGuessAdmissible (2 + Δcka) tL tStar = false := Bool.eq_false_iff.mpr hvg
    have hL :
        DEq (($ᵗ KC : ProbComp KC) >>= fun kc =>
              ($ᵗ Bool : ProbComp Bool) >>= fun b =>
              runHM (CKA.oracleImpl cka Δcka (healEpoch tL))
                (initCKA cka prng fs lam ⟨false, tL, tStar⟩) {}
                (CKA.initState cka kc true) >>= fun x =>
              match x.1.1 with
              | none => ($ᵗ Bool : ProbComp Bool)
              | some (vA, vB) =>
                let g : Ctx (Option Γ) T Sig SS RS M E :=
                  { st := fun P => match P with | .A => vA | .B => vB, b }
                evalEng (CKA.oracleImpl cka Δcka (healEpoch tL))
                  (hooksCKA cka prng fs Δcka ⟨false, tL, tStar⟩)
                  (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b A
                  ({ g, h := x.1.2 }, x.2))
            ($ᵗ Bool : ProbComp Bool) := by
      refine (DEq.bind_right ($ᵗ KC) fun kc => ?_).trans (DEq.bind_const ($ᵗ KC) _)
      refine (DEq.bind_right ($ᵗ Bool) fun b => ?_).trans (DEq.bind_const ($ᵗ Bool) _)
      refine (DEq.bind_right _ fun x => ?_).trans (DEq.bind_const _ _)
      cases x.1.1 with
      | none => exact DEq.refl _
      | some vAvB =>
        rcases vAvB with ⟨vA, vB⟩
        exact evalEng_invalid _ _ (2 + Δcka) qep fs.maxSkip (Config.priv tStar)
          ⟨false, tL, tStar⟩ b A _ hvgF
    have hR :
        DEq (($ᵗ KR : ProbComp KR) >>= fun kr =>
              ($ᵗ Bool : ProbComp Bool) >>= fun b =>
              runHM (PRFPRNG.oracleImpl prng)
                (initPRNG cka prng fs lam ⟨false, tL, tStar⟩) {}
                { σ := prng.init kr, b := false } >>= fun x =>
              match x.1.1 with
              | none => ($ᵗ Bool : ProbComp Bool)
              | some (vA, vB) =>
                let g : Ctx Γ T (Option Sig) SS RS M E :=
                  { st := fun P => match P with | .A => vA | .B => vB, b }
                evalEng (PRFPRNG.oracleImpl prng)
                  (hooksPRNG cka prng fs ⟨false, tL, tStar⟩)
                  (2 + Δcka) qep fs.maxSkip (Config.priv tStar) ⟨false, tL, tStar⟩ b A
                  ({ g, h := x.1.2 }, x.2))
            ($ᵗ Bool : ProbComp Bool) := by
      refine (DEq.bind_right ($ᵗ KR) fun kr => ?_).trans (DEq.bind_const ($ᵗ KR) _)
      refine (DEq.bind_right ($ᵗ Bool) fun b => ?_).trans (DEq.bind_const ($ᵗ Bool) _)
      refine (DEq.bind_right _ fun x => ?_).trans (DEq.bind_const _ _)
      cases x.1.1 with
      | none => exact DEq.refl _
      | some vAvB =>
        rcases vAvB with ⟨vA, vB⟩
        exact evalEng_invalid _ _ (2 + Δcka) qep fs.maxSkip (Config.priv tStar)
          ⟨false, tL, tStar⟩ b A _ hvgF
    exact hL.trans hR.symm

end SyncInvariant

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

/-- Lemma 14: ideal CKA bias of `redCKAPriv` is bounded by the real PRF-PRNG bias of `redPRNGPriv`. -/
theorem lemma14_proof (_hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAPriv cka prng fs lam Δcka qep tL t A)].boolBias ≤
      𝒟[PRFPRNG.branch prng false (redPRNGPriv cka prng fs lam Δcka qep tL t A)].boolBias := by
  rw [(branch_redCKAPriv_dEq_redPRNGPriv cka prng fs lam Δcka qep tL t A).evalDist_eq]

end CryptoGames.SM.Construction.PrivL14

