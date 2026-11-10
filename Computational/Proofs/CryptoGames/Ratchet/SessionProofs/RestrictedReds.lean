/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalSim
public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed
public import Computational.Proofs.CryptoGames.SM.ReductionsQueries
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs

/-!
# Restricted-reduction query invariants (`auth_restricted` and `priv_restricted`)

**Checked by Lean.** Proves that the FS-AEAD reductions `redFSAuth`, `redFSPriv`, and `redFSPrivCoin` applied to `Thm1.challSim` and `ThmB.privRedB` satisfy `FSAEAD.EqualPubChallenges` and `FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1)`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM.Proofs.RestrictedReds

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction
  SM.Engine CKA AEADScheme MACScheme WireAEAD FSAEAD

/-! ## `SafePost` and `SafeS` combinators -/

section SafePost

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}
  {Q : ι → Prop} {σ α β : Type}

/-- `SafePost Q P oa` states that `oa` makes no queries satisfying `Q` and every pure return
value satisfies `P`. -/
inductive SafePost (Q : ι → Prop) {α : Type} (P : α → Prop) : OracleComp spec α → Prop
  | pure {x : α} (h : P x) : SafePost Q P (pure x)
  | query_bind {t : ι} {mx : spec.Range t → OracleComp spec α}
      (hQt : ¬ Q t) (h : ∀ u, SafePost Q P (mx u)) :
      SafePost Q P (liftM (OracleSpec.query t) >>= mx)

theorem SafePost.to_isQueryBoundP [DecidablePred Q] {P : α → Prop} {oa : OracleComp spec α}
    (h : SafePost Q P oa) : IsQueryBoundP oa Q 0 := by
  induction h with
  | pure _ => trivial
  | @query_bind t mx hQt _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl hQt, fun u => by simpa [hQt] using ih u⟩

theorem SafePost.of_isQueryBoundP [DecidablePred Q] {oa : OracleComp spec α}
    (h : IsQueryBoundP oa Q 0) : SafePost Q (fun _ => True) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => exact SafePost.pure trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have hQt : ¬ Q t := h.1.resolve_right (Nat.not_lt_zero 0)
    exact SafePost.query_bind hQt fun u => ih u (by simpa [hQt] using h.2 u)

theorem SafePost.true_of_false (oa : OracleComp spec α) :
    SafePost (fun _ => False) (fun _ => True) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => exact SafePost.pure trivial
  | query_bind _ _ ih => exact SafePost.query_bind not_false ih

theorem SafePost.bind {P : α → Prop} {R : β → Prop} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} (hoa : SafePost Q P oa)
    (hob : ∀ a, P a → SafePost Q R (ob a)) :
    SafePost Q R (oa >>= ob) := by
  induction hoa with
  | pure h =>
    rw [pure_bind]
    exact hob _ h
  | query_bind hQt _ ih =>
    rw [bind_assoc]
    exact SafePost.query_bind hQt ih

theorem SafePost.mono {P R : α → Prop} {oa : OracleComp spec α}
    (hoa : SafePost Q P oa) (hPR : ∀ a, P a → R a) : SafePost Q R oa := by
  induction hoa with
  | pure h => exact SafePost.pure (hPR _ h)
  | query_bind hQt _ ih => exact SafePost.query_bind hQt ih

theorem SafePost.map {P : α → Prop} {R : β → Prop} (f : α → β) {oa : OracleComp spec α}
    (hoa : SafePost Q P oa) (hf : ∀ a, P a → R (f a)) : SafePost Q R (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact hoa.bind fun a ha => SafePost.pure (hf a ha)

theorem SafePost.query {t : spec.Domain} (hQt : ¬ Q t) :
    SafePost Q (fun _ => True) (query (spec := spec) t : OracleComp spec (spec.Range t)) := by
  change SafePost Q (fun _ => True) (liftM (spec.query t))
  rw [← bind_pure (liftM (spec.query t))]
  exact SafePost.query_bind hQt fun _ => SafePost.pure trivial

theorem SafePost.liftComp_unif {τ : Type} {tspec : OracleSpec.{0, 0} τ}
    {Q : (unifSpec + tspec).Domain → Prop} (hQu : ∀ u, ¬ Q (.inl u))
    (mx : ProbComp α) :
    SafePost Q (fun _ => True) (liftM mx : OracleComp (unifSpec + tspec) α) := by
  change SafePost Q (fun _ => True) (liftComp mx (unifSpec + tspec))
  induction mx using OracleComp.inductionOn with
  | pure _ => exact SafePost.pure trivial
  | query_bind t mx ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    exact SafePost.query_bind (hQu t) ih

/-- `SafeS Q I P x` states that from any state satisfying `I`, running `x` makes no `Q`-queries
and every `(a, s')` returned satisfies `P a s'`. -/
def SafeS (Q : ι → Prop) {σ α : Type} (I : σ → Prop) (P : α → σ → Prop)
    (x : StateT σ (OracleComp spec) α) : Prop :=
  ∀ s, I s → SafePost Q (fun r => P r.1 r.2) (x.run s)

theorem safeS_pure {I : σ → Prop} {P : α → σ → Prop} (a : α) (h : ∀ s, I s → P a s) :
    SafeS (spec := spec) Q I P (pure a) := fun s hs => by
  rw [StateT.run_pure]
  exact SafePost.pure (h s hs)

theorem safeS_pure_true {I : σ → Prop} (a : α) :
    SafeS (spec := spec) Q I (fun _ s => I s) (pure a) :=
  safeS_pure a fun _ hs => hs

theorem safeS_bind {I : σ → Prop} {P : α → σ → Prop} {R : β → σ → Prop}
    {x : StateT σ (OracleComp spec) α} {f : α → StateT σ (OracleComp spec) β}
    (hx : SafeS Q I P x) (hf : ∀ a, SafeS Q (P a) R (f a)) :
    SafeS Q I R (x >>= f) := fun s hs => by
  rw [StateT.run_bind]
  exact (hx s hs).bind fun p hp => hf p.1 p.2 hp

theorem safeS_bind_true {I : σ → Prop} {R : β → σ → Prop}
    {x : StateT σ (OracleComp spec) α} {f : α → StateT σ (OracleComp spec) β}
    (hx : SafeS Q I (fun _ s => I s) x) (hf : ∀ a, SafeS Q I R (f a)) :
    SafeS Q I R (x >>= f) :=
  safeS_bind hx hf

theorem safeS_bind_and {I : σ → Prop} {C : α → Prop} {R : β → σ → Prop}
    {x : StateT σ (OracleComp spec) α} {f : α → StateT σ (OracleComp spec) β}
    (hx : SafeS Q I (fun a s => C a ∧ I s) x)
    (hf : ∀ a, C a → SafeS Q I R (f a)) :
    SafeS Q I R (x >>= f) := fun s hs => by
  rw [StateT.run_bind]
  exact (hx s hs).bind fun p hp => hf p.1 hp.1 p.2 hp.2

theorem safeS_get_bind {I : σ → Prop} {R : α → σ → Prop}
    {f : σ → StateT σ (OracleComp spec) α}
    (hf : ∀ s, I s → SafeS Q I R (f s)) :
    SafeS Q I R (get >>= f) := fun s hs => by
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf s hs s hs

theorem safeS_set {I : σ → Prop} {P : PUnit → σ → Prop} (s' : σ) (h : ∀ s, I s → P () s') :
    SafeS (spec := spec) Q I P (set s') := fun s hs => by
  rw [StateT.run_set]
  exact SafePost.pure (h s hs)

theorem safeS_set_true {I : σ → Prop} (s' : σ) (h : ∀ s, I s → I s') :
    SafeS (spec := spec) Q I (fun _ s => I s) (set s') :=
  safeS_set s' h

theorem safeS_modify {I : σ → Prop} {P : PUnit → σ → Prop} (g : σ → σ)
    (h : ∀ s, I s → P () (g s)) :
    SafeS (spec := spec) Q I P (modify g) := fun s hs => by
  rw [StateT.run_modify]
  exact SafePost.pure (h s hs)

theorem safeS_modify_true {I : σ → Prop} (g : σ → σ)
    (h : ∀ s, I s → I (g s)) :
    SafeS (spec := spec) Q I (fun _ s => I s) (modify g) :=
  safeS_modify g h

theorem safeS_lift_true {I : σ → Prop} {x : OracleComp spec α}
    (hx : SafePost Q (fun _ => True) x) :
    SafeS Q I (fun _ s => I s) (StateT.lift x) := fun s hs =>
  hx.bind fun _ _ => SafePost.pure hs

theorem safeS_lift_query {I : σ → Prop} {t : spec.Domain} (hQt : ¬ Q t) :
    SafeS Q I (fun _ s => I s)
      (StateT.lift (query (spec := spec) t : OracleComp spec (spec.Range t))) :=
  safeS_lift_true (SafePost.query hQt)

theorem safeS_bind_query {I : σ → Prop} {R : β → σ → Prop}
    {t : spec.Domain} {f : spec.Range t → StateT σ (OracleComp spec) β}
    (hQt : ¬ Q t) (hf : ∀ a, SafeS Q I R (f a)) :
    SafeS Q I R
      (StateT.lift (query (spec := spec) t : OracleComp spec (spec.Range t)) >>= f) :=
  safeS_bind_true (safeS_lift_query hQt) hf

theorem SafePost.simulateQ_run
    {p : ι → Prop} {Q : ι' → Prop} {I : σ → Prop}
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    {oa : OracleComp spec α}
    (hoa : SafePost p (fun _ => True) oa)
    (hstep : ∀ t, ¬ p t → SafeS Q I (fun _ s => I s) (impl t))
    {s : σ} (hs : I s) :
    SafePost Q (fun r => I r.2) ((simulateQ impl oa).run s) := by
  induction hoa generalizing s with
  | pure _ =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact SafePost.pure hs
  | @query_bind t mx hpt _ ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    have hlift : SafePost Q (fun r => I r.2)
        ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s) := by
      simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t hpt s hs
    exact hlift.bind fun pu hpu => ih pu.1 hpu

end SafePost

/-! ## Equal public challenges for `challSim` and `privRedB` -/

section SimEqualPub

variable {St Msg Coins C Pub : Type} [DecidableEq Msg] [DecidableEq C] [DecidableEq Pub]

abbrev QSM (pubOf : Msg → Pub) : (unifSpec + SM.spec St Msg Coins C).Domain → Prop :=
  fun t => SM.unequalPubChall (St := St) (Coins := Coins) (C := C) pubOf t = true

theorem hQu_QSM (pubOf : Msg → Pub) (u : ℕ) :
    ¬ QSM (St := St) (Coins := Coins) (C := C) pubOf (.inl u) := by
  simp [QSM, SM.unequalPubChall]

theorem safeS_thm1_simOracles (Δ qep : ℕ) (pubOf : Msg → Pub)
    (o : (SM.spec St Msg Coins C).Domain) :
    SafeS (QSM (St := St) (Coins := Coins) (C := C) pubOf) (fun _ => True) (fun _ _ => True)
      (Thm1.simOracles (St := St) (Coins := Coins) Δ qep (fun _ => none) none o) := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change SafeS _ _ _ (Thm1.simTransmit (St := St) Δ qep (P, m, r))
    unfold Thm1.simTransmit SM.transmitQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
    cases res <;> cases s.epMgmt Δ qep P r.isSome
    all_goals first
      | exact safeS_pure_true _
      | exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (Thm1.simChall (St := St) Δ qep (fun _ => none) none (P, m₀, m₁, r))
    unfold Thm1.simChall Thm1.simSend SM.transmitQuery
    refine safeS_get_bind fun s _ => ?_
    cases s.epMgmt Δ qep P r.isSome with
    | none => exact safeS_pure_true _
    | some s₁ =>
      dsimp only
      cases s₁.safeCh Δ P
      · exact safeS_pure_true _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
        cases res
        · exact safeS_pure_true _
        · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (Thm1.simDeliver (St := St) (Coins := Coins) (P, c))
    unfold Thm1.simDeliver SM.deliverQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
    cases res with
    | none => exact safeS_pure_true _
    | some rr =>
      cases rr <;> cases s.inTransit P.other c
      all_goals first
        | exact safeS_pure_true _
        | exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (Thm1.simInject (St := St) (Coins := Coins) (P, c))
    unfold Thm1.simInject SM.injectQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
    cases res with
    | none => exact safeS_pure_true _
    | some rr =>
      cases rr
      · exact safeS_pure_true _
      · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (Thm1.simCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P)
    unfold Thm1.simCorr SM.corrQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
    cases res <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
    · exact safeS_pure_true _
    · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _

theorem challSim_equalPub (Δ qep : ℕ) (pubOf : Msg → Pub) (A : SM.Adversary St Msg Coins C) :
    SM.EqualPubChalls pubOf (Thm1.challSim Δ qep A) := by
  unfold SM.EqualPubChalls
  dsimp only [Thm1.challSim, Thm1.simRun]
  rw [bind_assoc]
  refine SafePost.to_isQueryBoundP (P := fun _ => True) ?_
  refine (SafePost.liftComp_unif (hQu_QSM (St := St) (Coins := Coins) (C := C) pubOf) ($ᵗ Bool)).bind
    fun b _ => ?_
  rw [bind_assoc, StateT.run'_eq]
  have hsim : SafePost (QSM (St := St) (Coins := Coins) (C := C) pubOf) (fun _ => True)
      ((simulateQ (Thm1.simImpl Δ qep (fun _ => none) none) A).run
        ({ st := fun _ => (), b } : Thm1.Mirror Msg C)) := by
    refine SafePost.simulateQ_run (I := fun _ => True) (SafePost.true_of_false A) ?_ trivial
    rintro (u | o) _
    · exact safeS_lift_query (hQu_QSM (St := St) (Coins := Coins) (C := C) pubOf u)
    · exact safeS_thm1_simOracles Δ qep pubOf o
  exact (hsim.map (R := fun _ => True) Prod.fst (fun _ _ => trivial)).bind fun _ _ =>
    SafePost.pure trivial

theorem safeS_thmB_simOracles (Δ qep i : ℕ) (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hpub : ∀ m, pubOf (blank m) = pubOf m)
    (o : (SM.spec St Msg Coins C).Domain) :
    SafeS (QSM (St := St) (Coins := Coins) (C := C) pubOf) (fun _ => True) (fun _ _ => True)
      (ThmB.simOracles (St := St) (Coins := Coins) Δ qep
        (fun t => if t < i then some blank else none) (some (i, blank)) o) := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change SafeS _ _ _ (ThmB.simTransmit (St := St) Δ qep (P, m, r))
    unfold ThmB.simTransmit SM.transmitQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
    cases res <;> cases s.epMgmt Δ qep P r.isSome
    all_goals first
      | exact safeS_pure_true _
      | exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (ThmB.simChall (St := St) Δ qep
      (fun t => if t < i then some blank else none) (some (i, blank)) (P, m₀, m₁, r))
    unfold ThmB.simChall ThmB.simSend SM.transmitQuery SM.challQuery
    refine safeS_get_bind fun s _ => ?_
    cases s.epMgmt Δ qep P r.isSome with
    | none => exact safeS_pure_true _
    | some s₁ =>
      dsimp only
      cases s₁.safeCh Δ P
      · exact safeS_pure_true _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hti : s₁.epoch P = i
        · simp only [hti, ↓reduceIte]
          refine safeS_bind_query (by simp [QSM, SM.unequalPubChall, hpub]) fun res => ?_
          cases res
          · exact safeS_pure_true _
          · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
        · simp only [hti, ↓reduceIte]
          refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
          cases res
          · exact safeS_pure_true _
          · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (ThmB.simDeliver (St := St) (Coins := Coins) (P, c))
    unfold ThmB.simDeliver SM.deliverQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
    cases res with
    | none => exact safeS_pure_true _
    | some rr =>
      cases rr <;> cases s.inTransit P.other c
      all_goals first
        | exact safeS_pure_true _
        | exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (ThmB.simInject (St := St) (Coins := Coins) (P, c))
    unfold ThmB.simInject SM.injectQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
    cases res with
    | none => exact safeS_pure_true _
    | some rr =>
      cases rr
      · exact safeS_pure_true _
      · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (ThmB.simCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P)
    unfold ThmB.simCorr SM.corrQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QSM, SM.unequalPubChall]) fun res => ?_
    cases res <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
    · exact safeS_pure_true _
    · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _

theorem privRedB_equalPub_local (Δ qep i : ℕ) (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hpub : ∀ m, pubOf (blank m) = pubOf m) (A : SM.Adversary St Msg Coins C) :
    SM.EqualPubChalls pubOf (ThmB.privRedB Δ qep i blank A) := by
  unfold SM.EqualPubChalls
  dsimp only [ThmB.privRedB, ThmB.simRun]
  rw [bind_assoc]
  refine SafePost.to_isQueryBoundP (P := fun _ => True) ?_
  refine (SafePost.liftComp_unif (hQu_QSM (St := St) (Coins := Coins) (C := C) pubOf) ($ᵗ Bool)).bind
    fun b _ => ?_
  rw [bind_assoc, StateT.run'_eq]
  have hsim : SafePost (QSM (St := St) (Coins := Coins) (C := C) pubOf) (fun _ => True)
      ((simulateQ (ThmB.simImpl Δ qep (fun t => if t < i then some blank else none) (some (i, blank))) A).run
        ({ st := fun _ => (), b } : Thm1.Mirror Msg C)) := by
    refine SafePost.simulateQ_run (I := fun _ => True) (SafePost.true_of_false A) ?_ trivial
    rintro (u | o) _
    · exact safeS_lift_query (hQu_QSM (St := St) (Coins := Coins) (C := C) pubOf u)
    · exact safeS_thmB_simOracles Δ qep i pubOf blank hpub o
  exact (hsim.map (R := fun _ => True) Prod.fst (fun _ _ => trivial)).bind fun _ _ =>
    SafePost.pure trivial

end SimEqualPub

/-! ## `redFS` state invariant and query preservation -/

section RedFS

open ReductionsQueries

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] [DecidableEq Pub]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

theorem sendsIn_succ_of_false (P : Party) (t : ℕ) (h : P.sendsIn t = false) :
    P.sendsIn (t + 1) = true := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

/-- Virtual party-state invariant restricting external sending and receiving sessions to epoch `tStar`. -/
structure InvVP (tStar : ℕ) (vp : VP Γ T Sig (Option SS) (Option RS)) : Prop where
  vS_ext : vp.id.sendsIn (vp.tcur + 1) = false → vp.vS = some none → vp.tcur = tStar
  vR_ext : ∀ t, vp.vR t = some none → t = tStar

/-- Bookkeeping state invariant restricting cached external sessions to epoch `tStar`. -/
def InvFS (tStar : ℕ) (s : FSState T Sig K I SS RS E) : Prop :=
  ∀ t Tc σc k, s.cache t = some (Tc, σc, k, true) → t = tStar

structure InvE (tStar : ℕ)
    (es : EState (VP Γ T Sig (Option SS) (Option RS)) M (Header T × E)
      (FSState T Sig K I SS RS E)) : Prop where
  vp : ∀ P, InvVP tStar (es.g.st P)
  fs : InvFS tStar es.h

theorem invFS_empty (tStar : ℕ) : InvFS tStar ({} : FSState T Sig K I SS RS E) := by
  rintro _ _ _ _ ⟨⟩

theorem epMgmt_st {VPt Msg C : Type} (Δ qep : ℕ) {g s₁ : SM.GameState VPt Msg C}
    {P : Party} {bad : Bool} (h : g.epMgmt Δ qep P bad = some s₁) :
    s₁.st = g.st := by
  unfold SM.GameState.epMgmt SM.GameState.leak at h
  dsimp only at h
  split_ifs at h <;> cases h <;> rfl

theorem invVP_record {tStar : ℕ} (Δ : ℕ) {s₁ : Ctx Γ T Sig (Option SS) (Option RS) M E}
    (hs₁ : ∀ Q, InvVP tStar (s₁.st Q)) (P : Party)
    {st' : VP Γ T Sig (Option SS) (Option RS)} (hst' : InvVP tStar st')
    (r : SM.Record M (Header T × E)) (isChall : Bool) :
    ∀ Q, InvVP tStar ((s₁.record Δ P st' r isChall).st Q) := by
  intro Q
  simp only [SM.GameState.record]
  by_cases hQ : Q = P
  · subst hQ; simpa using hst'
  · simpa [hQ] using hs₁ Q

theorem invVP_accept {tStar : ℕ} {s : Ctx Γ T Sig (Option SS) (Option RS) M E}
    (hs : ∀ Q, InvVP tStar (s.st Q)) (P : Party)
    {st' : VP Γ T Sig (Option SS) (Option RS)} (hst' : InvVP tStar st') (pos : SM.Pos) :
    ∀ Q, InvVP tStar ((s.accept P st' pos).st Q) := by
  intro Q
  simp only [SM.GameState.accept, SM.GameState.delete]
  by_cases hQ : Q = P
  · subst hQ; simpa using hst'
  · simpa [hQ] using hs Q

/-- Predicate bundling the assumptions that `Q` holds on no uniform sampling, corruption,
or epoch-`tStar` FS-AEAD queries satisfying `transOk` / `challOk`. -/
structure ValidQGen (Q : (RSpec SS RS T M E).Domain → Prop) (mo : Mode)
    (transOk : M → Prop) (challOk : M → M → Prop) : Prop where
  u : ∀ u, ¬ Q (.inl u)
  cs : ¬ Q (.inr (.inl (.inl (.inl (.inr ())))))
  cr : ¬ Q (.inr (.inl (.inl (.inr ()))))
  t : ∀ h m, h.1 = mo.tStar → transOk m → ¬ Q (.inr (.inl (.inl (.inl (.inl (.inl ⟨h, m⟩))))))
  c : ∀ h m₀ m₁, h.1 = mo.tStar → challOk m₀ m₁ →
    ¬ Q (.inr (.inl (.inl (.inl (.inl (.inr ⟨h, m₀, m₁⟩))))))
  d : ∀ h e, h.1 = mo.tStar → ¬ Q (.inr (.inl (.inr ⟨h, e⟩)))
  i : ∀ h e, h.1 = mo.tStar → ¬ Q (.inr (.inr ⟨h, e⟩))

abbrev ValidQ (Q : (RSpec SS RS T M E).Domain → Prop) (mo : Mode) (pubOf : M → Pub) : Prop :=
  ValidQGen (SS := SS) (RS := RS) (E := E) Q mo (fun _ => True) (fun m₀ m₁ => pubOf m₀ = pubOf m₁)

variable {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode}
  {transOk : M → Prop} {challOk : M → M → Prop} {pubOf : M → Pub}
  (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q mo transOk challOk)
  (hQ₀ : ValidQ (SS := SS) (RS := RS) (E := E) Q mo pubOf)
  (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (j : ℕ)

include hQ in
theorem safePost_sampleT (α : Type) [SampleableType α] :
    SafePost Q (fun _ => True) (sampleT (tspec := FSpec SS RS T M E) α) :=
  SafePost.liftComp_unif hQ.u ($ᵗ α)

include hQ in
theorem safeS_lift_sampleT {σ : Type} {I : σ → Prop} (α : Type) [SampleableType α] :
    SafeS Q I (fun _ s => I s)
      (StateT.lift (sampleT (tspec := FSpec SS RS T M E) α) :
        StateT σ (OracleComp (RSpec SS RS T M E)) α) :=
  safeS_lift_true (safePost_sampleT hQ α)

include hQ in
theorem safeS_lookupF (Ik : I) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun _ s => InvFS mo.tStar s) (lookupF Ik) := by
  unfold lookupF
  refine safeS_get_bind fun s _ => ?_
  cases s.table.lookup Ik with
  | some k => exact safeS_pure_true k
  | none =>
    refine safeS_bind_true (safeS_lift_sampleT hQ K) fun k => ?_
    exact safeS_bind_true (safeS_modify_true _ (fun _ hs => hs)) fun _ => safeS_pure_true k

theorem safeS_isExt (Ik : I) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun _ s => InvFS mo.tStar s) (isExt j Ik) := by
  unfold isExt
  refine safeS_get_bind fun s hs => ?_
  split_ifs
  · exact safeS_pure_true _
  · exact safeS_bind_true (safeS_set_true _ (fun _ _ => hs)) fun _ => safeS_pure_true _

theorem safeS_extOf (sid : Option I) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun ext s => (ext = true → sid.isSome = true) ∧ InvFS mo.tStar s) (extOf j sid) := by
  unfold extOf
  cases sid with
  | none =>
    exact safeS_pure false fun _ hs => ⟨by rintro ⟨⟩, hs⟩
  | some Ik =>
    exact fun s hs => (safeS_isExt j Ik s hs).mono fun _ h => ⟨fun _ => rfl, h⟩

include hQ in
theorem safeS_rootFS (t : ℕ) (Ik : I) (σ : Sig) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun p s => (p.2.2.isSome = true → t = mo.tStar) ∧ InvFS mo.tStar s)
      (rootFS prng mo t Ik σ) := by
  unfold rootFS
  by_cases h1 : mo.tStar < t
  · simp only [h1, ↓reduceIte]
    exact safeS_pure _ fun _ hs => ⟨by rintro ⟨⟩, hs⟩
  · simp only [h1, ↓reduceIte]
    by_cases h2 : t = mo.tStar
    · rw [if_pos h2]
      split_ifs
      · refine safeS_bind_true (safeS_lift_sampleT hQ I) fun Ir => ?_
        refine safeS_bind_true (safeS_lift_sampleT hQ K) fun k => ?_
        exact safeS_pure _ fun _ hs => ⟨fun _ => h2, hs⟩
      · refine safeS_bind_true (safeS_lookupF hQ Ik) fun k => ?_
        exact safeS_pure _ fun _ hs => ⟨fun _ => h2, hs⟩
    · rw [if_neg h2]
      split_ifs
      · refine safeS_bind_true (safeS_lift_sampleT hQ I) fun Ir => ?_
        exact safeS_pure _ fun _ hs => ⟨by rintro ⟨⟩, hs⟩
      · exact safeS_pure _ fun _ hs => ⟨by rintro ⟨⟩, hs⟩

include hQ in
theorem safeS_initFS :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun vs s => (∀ vA vB, vs = some (vA, vB) → InvVP mo.tStar vA ∧ InvVP mo.tStar vB) ∧
        InvFS mo.tStar s)
      (initFS cka prng fs lam mo j) := by
  unfold initFS
  refine safeS_bind_true (safeS_lift_sampleT hQ KR) fun kr => ?_
  refine safeS_bind_true (safeS_lift_sampleT hQ KC) fun kc => ?_
  refine safeS_bind_and (safeS_rootFS hQ prng 0 lam (prng.init kr)) fun p hp => ?_
  refine safeS_bind_and (safeS_extOf j p.2.2) fun ext hext => ?_
  refine safeS_pure _ fun s' hs' => ⟨?_, hs'⟩
  intro vA vB hvs
  cases hvs
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro _ h; cases h
  · intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      simp only [mkParties, ↓reduceIte, Option.some.injEq] at ht
      by_cases he : ext = true
      · exact hp (hext he)
      · simp [he] at ht
    · simp [mkParties, ht0] at ht
  · intro _ h
    simp only [mkParties, Option.some.injEq] at h
    by_cases he : ext = true
    · exact hp (hext he)
    · simp [he] at h
  · intro _ h; cases h

include hQ in
theorem safeS_startSend (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (r : Option CCoins) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s => (∀ γ' T' σ' ss, res = some (γ', T', σ', ss) → ss = none → t = mo.tStar) ∧
        InvFS mo.tStar s)
      ((hooksFS cka prng fs Δcka mo j).startSend ctx P t γ σ r) := by
  dsimp only [hooksFS]
  have hbody : ∀ c : CCoins,
      SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun res s => (∀ γ' T' σ' ss, res = some (γ', T', σ', ss) → ss = none → t = mo.tStar) ∧
          InvFS mo.tStar s)
        (do
          let (σ', k, sid) ← rootFS prng mo t (cka.send γ c).2.2 σ
          let ext ← extOf j sid
          modify fun s => { s with cache := Function.update s.cache t (some ((cka.send γ c).2.1, σ', k, ext)) }
          return some ((cka.send γ c).1, (cka.send γ c).2.1, σ', if ext then none else some (fs.initSender k))) := by
    intro c
    refine safeS_bind_and (safeS_rootFS hQ prng t (cka.send γ c).2.2 σ) fun p hp => ?_
    refine safeS_bind_and (safeS_extOf j p.2.2) fun ext hext => ?_
    refine safeS_bind_true
      (safeS_modify_true _ fun s' hs' => by
        intro t' Tc σc k hcache
        by_cases htt' : t' = t
        · subst htt'
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hcache
          exact hp (hext hcache.2.2.2)
        · simp only [Function.update_of_ne htt'] at hcache
          exact hs' t' Tc σc k hcache)
      fun _ => ?_
    refine safeS_pure _ fun s' hs' => ⟨?_, hs'⟩
    intro γ' T' σ' ss hres hss
    cases hres
    by_cases he : ext = true
    · exact hp (hext he)
    · simp [he] at hss
  cases r with
  | some c =>
    simp only [pure_bind]
    exact hbody c
  | none =>
    exact safeS_bind_true (safeS_lift_sampleT hQ CCoins) hbody

include hQ in
theorem safeS_startRecv (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (γ : Γ) (σ : Sig) (Tn : T) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s => (∀ γ' σ' rs, res = some (some (γ', σ', rs)) → rs = none → t = mo.tStar) ∧
        InvFS mo.tStar s)
      ((hooksFS cka prng fs Δcka mo j).startRecv ctx P t γ σ Tn) := by
  dsimp only [hooksFS]
  have hmiss : SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s => (∀ γ' σ' rs, res = some (some (γ', σ', rs)) → rs = none → t = mo.tStar) ∧
        InvFS mo.tStar s)
      (if mo.auth && decide (t = mo.tStar) then
        if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
        else do
          let kk := cka.receive γ Tn
          let k' ← lookupF kk.2
          let ext ← isExt j kk.2
          return some (some (kk.1, (prng.up σ kk.2).1, if ext then none else some (fs.initReceiver k')))
      else pure (some none)) := by
    by_cases ha : (mo.auth && decide (t = mo.tStar)) = true
    · have ht : t = mo.tStar := by simpa using (Bool.and_eq_true _ _).mp ha |>.2
      simp only [ha, ↓reduceIte]
      split_ifs
      · exact safeS_pure none fun _ hs => ⟨by rintro _ _ _ ⟨⟩, hs⟩
      · refine safeS_bind_true (safeS_lookupF hQ (cka.receive γ Tn).2) fun k' => ?_
        refine safeS_bind_true (safeS_isExt j (cka.receive γ Tn).2) fun ext => ?_
        exact safeS_pure _ fun _ hs => ⟨fun _ _ _ _ _ => ht, hs⟩
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact safeS_pure (some none) fun _ hs => ⟨by rintro _ _ _ ⟨⟩, hs⟩
  refine safeS_get_bind fun s hs => ?_
  cases hcache : s.cache t with
  | some quad =>
    rcases quad with ⟨Tc, σc, k, ext⟩
    by_cases hTc : Tc = Tn
    · simp only [hTc, ↓reduceIte]
      refine safeS_pure _ fun s' hs' => ⟨?_, hs'⟩
      intro γ' σ' rs hres hrs
      cases hres
      by_cases he : ext = true
      · subst he
        exact hs t Tc σc k hcache
      · simp [he] at hrs
    · simp only [hTc, ↓reduceIte]
      exact hmiss
  | none =>
    exact hmiss

include hQ in
theorem safeS_fsSendGen (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (ssv : Option SS) (h : Header T) (m : M) (pair : Option (M × M))
    (hssv : ssv = none → h.1 = mo.tStar)
    (hm : pair = none → transOk m)
    (hpair : ∀ m₀ m₁, pair = some (m₀, m₁) → challOk m₀ m₁) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s => (∀ ssv' e, res = some (ssv', e) → ssv' = none → h.1 = mo.tStar) ∧
        InvFS mo.tStar s)
      ((hooksFS cka prng fs Δcka mo j).fsSend ctx P t ssv h m pair) := by
  dsimp only [hooksFS]
  cases ssv with
  | some ss =>
    exact safeS_pure _ fun _ hs => ⟨by rintro _ _ ⟨⟩ ⟨⟩, hs⟩
  | none =>
    have hh : h.1 = mo.tStar := hssv rfl
    refine safeS_get_bind fun s hs => ?_
    rcases s.ext with _ | ⟨ss, rs⟩
    · have hsend : SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
          (fun res s' => (∀ (ssv' : Option SS) (e : E), res = some (ssv', e) → ssv' = none → h.1 = mo.tStar) ∧
            InvFS mo.tStar s')
          (do
            let e? ← match pair with
              | some (m₀, m₁) =>
                liftF (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS) h m₀ m₁)
              | none =>
                liftF (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS) h m)
            match e? with
            | none => return none
            | some e =>
              modify fun s => { s with fsCount := s.fsCount + 1,
                                       fsTrans := (s.fsCount + 1, h, e) :: s.fsTrans }
              return some (none, e)) := by
        cases pair with
        | none =>
          dsimp only [liftF, FSAEAD.transmitQuery]
          refine safeS_bind_query (hQ.t h m hh (hm rfl)) fun e? => ?_
          cases e? with
          | none => exact safeS_pure none fun _ hs => ⟨by rintro _ _ ⟨⟩, hs⟩
          | some e =>
            refine safeS_bind_true (safeS_modify_true _ (fun _ hs => hs)) fun _ => ?_
            exact safeS_pure _ fun _ hs => ⟨fun _ _ _ _ => hh, hs⟩
        | some mm =>
          rcases mm with ⟨m₀, m₁⟩
          dsimp only [liftF, FSAEAD.challengeQuery]
          refine safeS_bind_query (hQ.c h m₀ m₁ hh (hpair m₀ m₁ rfl)) fun e? => ?_
          cases e? with
          | none => exact safeS_pure none fun _ hs => ⟨by rintro _ _ ⟨⟩, hs⟩
          | some e =>
            refine safeS_bind_true (safeS_modify_true _ (fun _ hs => hs)) fun _ => ?_
            exact safeS_pure _ fun _ hs => ⟨fun _ _ _ _ => hh, hs⟩
      by_cases hc : (!ctx.safeCh (2 + Δcka) P && !s.fsSCorr) = true
      · simp only [hc, ↓reduceIte]
        dsimp only [liftF, FSAEAD.corruptSenderQuery]
        refine safeS_bind_query hQ.cs fun r => ?_
        cases r with
        | none =>
          simp only [pure_bind, Bool.not_false, ↓reduceIte]
          exact safeS_pure none fun _ hs => ⟨by rintro _ _ ⟨⟩, hs⟩
        | some _ =>
          refine safeS_bind_true (safeS_modify_true _ (fun _ hs => hs)) fun _ => ?_
          simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact hsend
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_true]
        exact hsend
    · refine safeS_bind_true (safeS_set_true _ (fun _ _ => hs)) fun _ => ?_
      exact safeS_pure _ fun _ hs' => ⟨fun _ _ _ _ => hh, hs'⟩

include hQ₀ in
theorem safeS_fsSend (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (ssv : Option SS) (h : Header T) (m : M) (pair : Option (M × M))
    (hssv : ssv = none → h.1 = mo.tStar)
    (hpair : ∀ m₀ m₁, pair = some (m₀, m₁) → pubOf m₀ = pubOf m₁) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s => (∀ ssv' e, res = some (ssv', e) → ssv' = none → h.1 = mo.tStar) ∧
        InvFS mo.tStar s)
      ((hooksFS cka prng fs Δcka mo j).fsSend ctx P t ssv h m pair) :=
  safeS_fsSendGen hQ₀ cka prng fs Δcka j ctx P t ssv h m pair hssv (fun _ => trivial) hpair

include hQ in
theorem safeS_fsRecv (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (rsv : Option RS) (h : Header T) (e : E)
    (rec : Option (SM.Record M (Header T × E)))
    (hrsv : rsv = none → h.1 = mo.tStar) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s => (∀ rsv' i m, res = some (some (rsv', i, m)) → rsv' = none → h.1 = mo.tStar) ∧
        InvFS mo.tStar s)
      ((hooksFS cka prng fs Δcka mo j).fsRecv ctx P t rsv h e rec) := by
  dsimp only [hooksFS]
  cases rsv with
  | some rs =>
    refine safeS_pure _ fun _ hs => ⟨?_, hs⟩
    intro rsv' i m hres hr
    subst hr
    cases hrec : fs.receive rs h e <;> simp [hrec] at hres
  | none =>
    have hh : h.1 = mo.tStar := hrsv rfl
    refine safeS_get_bind fun s hs => ?_
    rcases s.ext with _ | ⟨ss, rs⟩
    · by_cases hm : (s.fsTrans.find? (fun x => x.2 == (h, e))).isSome = true
      · simp only [hm, ↓reduceIte]
        dsimp only [liftF, FSAEAD.deliverQuery]
        refine safeS_bind_query (hQ.d h e hh) fun res => ?_
        cases res with
        | none => exact safeS_pure none fun _ hs => ⟨by rintro _ _ _ ⟨⟩, hs⟩
        | some rr =>
          cases rr with
          | rejected => exact safeS_pure (some none) fun _ hs => ⟨by rintro _ _ _ ⟨⟩, hs⟩
          | accepted i mo' =>
            refine safeS_bind_true (safeS_modify_true _ (fun _ hs => hs)) fun _ => ?_
            cases mo' <;> cases rec <;>
              exact safeS_pure _ fun _ hs => ⟨fun _ _ _ _ _ => hh, hs⟩
      · simp only [hm, Bool.false_eq_true, ↓reduceIte]
        dsimp only [liftF, FSAEAD.injectQuery]
        refine safeS_bind_query (hQ.i h e hh) fun res => ?_
        cases res with
        | none => exact safeS_pure none fun _ hs => ⟨by rintro _ _ _ ⟨⟩, hs⟩
        | some rr =>
          cases rr with
          | rejected => exact safeS_pure (some none) fun _ hs => ⟨by rintro _ _ _ ⟨⟩, hs⟩
          | accepted i mo' =>
            refine safeS_bind_true (safeS_modify_true _ (fun _ hs => hs)) fun _ => ?_
            cases mo' <;> cases rec <;>
              exact safeS_pure _ fun _ hs => ⟨fun _ _ _ _ _ => hh, hs⟩
    · dsimp only
      rcases fs.receive rs h e with _ | ⟨rs', i, m⟩
      · dsimp only
        exact safeS_pure (some none) fun _ hs' => ⟨by rintro _ _ _ ⟨⟩, hs'⟩
      · dsimp only
        refine safeS_bind_true (safeS_set_true _ (fun _ _ => hs)) fun _ => ?_
        exact safeS_pure _ fun _ hs' => ⟨fun _ _ _ _ _ => hh, hs'⟩

include hQ in
theorem safeS_reveal (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (vp : PartyState Γ T Sig (Option SS) (Option RS)) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun _ s => InvFS mo.tStar s)
      ((hooksFS cka prng fs Δcka mo j).reveal ctx P vp) := by
  dsimp only [hooksFS]
  have hrecv : ∀ vS : Option SS,
      SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
        (fun _ s => InvFS mo.tStar s)
        (do
          let rsExt? : Option (Option RS) ← match vp.vR mo.tStar with
            | some none => do
              match (← get).ext with
              | some (_, rs) => pure (some (some rs))
              | none =>
                if mo.auth then pure none
                else
                  match ← liftF (FSAEAD.corruptReceiverQuery (SenderState := SS) (ReceiverState := RS)
                      (AssocData := Header T) (Message := M) (Ciphertext := E)) with
                  | none => pure none
                  | some (ss, rs) =>
                    modify fun s => { s with ext := some (ss, rs) }
                    pure (some (some rs))
            | _ => pure (some none)
          match rsExt? with
          | none => return none
          | some rsExt =>
            let vR : ℕ → Option RS := fun t => match vp.vR t with
              | some (some rs) => some rs
              | some none => rsExt
              | none => none
            return some (realParty vp vp.γ vp.root vS vR)) := by
    intro vS
    cases vp.vR mo.tStar with
    | none => simp only [pure_bind]; exact safeS_pure_true _
    | some rsv =>
      cases rsv with
      | some rs => simp only [pure_bind]; exact safeS_pure_true _
      | none =>
        refine safeS_get_bind fun s _ => ?_
        cases s.ext with
        | some sr => simp only [pure_bind]; exact safeS_pure_true _
        | none =>
          split_ifs
          · simp only [pure_bind]; exact safeS_pure_true none
          · dsimp only [liftF, FSAEAD.corruptReceiverQuery]
            refine safeS_bind_query hQ.cr fun r => ?_
            cases r with
            | none => simp only [pure_bind]; exact safeS_pure_true none
            | some sr =>
              refine safeS_bind_true (safeS_modify_true _ (fun _ hs => hs)) fun _ => ?_
              simp only [pure_bind]; exact safeS_pure_true _
  cases vp.vS with
  | none => simp only [pure_bind]; exact hrecv none
  | some ssv =>
    cases ssv with
    | some ss => simp only [pure_bind]; exact hrecv (some ss)
    | none =>
      refine safeS_get_bind fun s _ => ?_
      cases s.ext with
      | some sr => simp only [pure_bind]; exact hrecv (some sr.1)
      | none =>
        dsimp only [liftF, FSAEAD.corruptSenderQuery]
        refine safeS_bind_query hQ.cs fun r => ?_
        cases r with
        | none => simp only [pure_bind]; exact safeS_pure_true none
        | some ss =>
          refine safeS_bind_true (safeS_modify_true _ (fun _ hs => hs)) fun _ => ?_
          simp only [pure_bind]; exact hrecv (some ss)

include hQ in
theorem safeS_vSendGen (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS)) (hs : InvVP mo.tStar s)
    (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (hm : pair = none → transOk m)
    (hpair : ∀ m₀ m₁, pair = some (m₀, m₁) → challOk m₀ m₁) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s' => (∀ vp' c, res = some (vp', c) → InvVP mo.tStar vp') ∧ InvFS mo.tStar s')
      (vSend (hooksFS cka prng fs Δcka mo j) ctx P s m pair r) := by
  unfold vSend
  by_cases h1 : s.id.sendsIn (s.tcur + 1) = true
  · simp only [h1, ↓reduceIte]
    refine safeS_bind_and (safeS_startSend hQ cka prng fs Δcka j ctx P (s.tcur + 1) s.γ s.root r)
      fun res hres => ?_
    cases res with
    | none =>
      simp only [pure_bind]
      exact safeS_pure none fun _ hfs => ⟨by rintro _ _ ⟨⟩, hfs⟩
    | some quad =>
      rcases quad with ⟨γ', T', σ', ss⟩
      simp only [pure_bind]
      refine safeS_bind_and
        (safeS_fsSendGen hQ cka prng fs Δcka j ctx P (s.tcur + 1) ss (s.tcur + 1, some T')
          m pair (fun hss => hres γ' T' σ' ss rfl hss) hm hpair)
        fun res' hres' => ?_
      cases res' with
      | none => exact safeS_pure none fun _ hfs => ⟨by rintro _ _ ⟨⟩, hfs⟩
      | some ve =>
        rcases ve with ⟨v', e⟩
        refine safeS_pure _ fun _ hfs => ⟨?_, hfs⟩
        intro vp' c hres''
        cases hres''
        exact ⟨fun _ hv' => hres' v' e rfl (Option.some.inj hv'), hs.vR_ext⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind]
    have h1f : s.id.sendsIn (s.tcur + 1) = false := Bool.eq_false_iff.mpr h1
    cases hv : s.vS with
    | none =>
      refine safeS_pure _ fun _ hfs => ⟨?_, hfs⟩
      intro vp' c hres
      cases hres
      exact ⟨fun _ h => (by rw [hv] at h; cases h), hs.vR_ext⟩
    | some v =>
      refine safeS_bind_and
        (safeS_fsSendGen hQ cka prng fs Δcka j ctx P s.tcur v (s.tcur, s.curCkaMsg)
          m pair (fun hv0 => by subst hv0; exact hs.vS_ext h1f hv) hm hpair)
        fun res' hres' => ?_
      cases res' with
      | none => exact safeS_pure none fun _ hfs => ⟨by rintro _ _ ⟨⟩, hfs⟩
      | some ve =>
        rcases ve with ⟨v', e⟩
        refine safeS_pure _ fun _ hfs => ⟨?_, hfs⟩
        intro vp' c hres
        cases hres
        exact ⟨fun _ hv' => hres' v' e rfl (Option.some.inj hv'), hs.vR_ext⟩

include hQ₀ in
theorem safeS_vSend (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS)) (hs : InvVP mo.tStar s)
    (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (hpair : ∀ m₀ m₁, pair = some (m₀, m₁) → pubOf m₀ = pubOf m₁) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s' => (∀ vp' c, res = some (vp', c) → InvVP mo.tStar vp') ∧ InvFS mo.tStar s')
      (vSend (hooksFS cka prng fs Δcka mo j) ctx P s m pair r) :=
  safeS_vSendGen hQ₀ cka prng fs Δcka j ctx P s hs m pair r (fun _ => trivial) hpair

include hQ in
theorem safeS_vRecv (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS)) (hs : InvVP mo.tStar s)
    (c : Header T × E) (rec : Option (SM.Record M (Header T × E))) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s' => (∀ vp' t' i' m', res = some (some (vp', t', i', m')) → InvVP mo.tStar vp') ∧
        InvFS mo.tStar s')
      (vRecv (hooksFS cka prng fs Δcka mo j) ctx P s c rec) := by
  unfold vRecv
  by_cases h1 : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure (some none) fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    have hsend_f : s.id.sendsIn c.1.1 = false := by
      cases hsnd : s.id.sendsIn c.1.1
      · rfl
      · simp [hsnd] at h1
    by_cases h2 : c.1.1 = s.tcur + 1
    · rw [if_pos h2]
      cases c.1.2 with
      | none =>
        simp only [pure_bind]
        exact safeS_pure (some none) fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
      | some Tn =>
        refine safeS_bind_and (safeS_startRecv hQ cka prng fs Δcka j ctx P c.1.1 s.γ s.root Tn)
          fun res hres => ?_
        cases res with
        | none =>
          simp only [pure_bind]
          exact safeS_pure none fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
        | some inner =>
          cases inner with
          | none =>
            simp only [pure_bind]
            exact safeS_pure (some none) fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
          | some triple =>
            rcases triple with ⟨γ', σ', rs⟩
            simp only [pure_bind, Function.update_self]
            refine safeS_bind_and
              (safeS_fsRecv hQ cka prng fs Δcka j ctx P c.1.1 rs c.1 c.2 rec
                (fun hrs => hres γ' σ' rs rfl hrs))
              fun res' hres' => ?_
            cases res' with
            | none => exact safeS_pure none fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
            | some inner' =>
              cases inner' with
              | none => exact safeS_pure (some none) fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
              | some vim =>
                rcases vim with ⟨v', i, m⟩
                refine safeS_pure _ fun _ hfs => ⟨?_, hfs⟩
                intro vp' t' i' m' hres''
                cases hres''
                refine ⟨fun hnext _ => ?_, fun t'' ht'' => ?_⟩
                · rw [sendsIn_succ_of_false s.id c.1.1 hsend_f] at hnext
                  cases hnext
                · by_cases htt'' : t'' = c.1.1
                  · subst htt''
                    simp only [Function.update_self, Option.some.injEq] at ht''
                    exact hres' v' i m rfl ht''
                  · simp only [Function.update_of_ne htt''] at ht''
                    exact hs.vR_ext t'' ht''
    · rw [if_neg h2]
      simp only [pure_bind]
      cases hv : s.vR c.1.1 with
      | none => exact safeS_pure (some none) fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
      | some v =>
        refine safeS_bind_and
          (safeS_fsRecv hQ cka prng fs Δcka j ctx P c.1.1 v c.1 c.2 rec
            (fun hv0 => by subst hv0; exact hs.vR_ext c.1.1 hv))
          fun res' hres' => ?_
        cases res' with
        | none => exact safeS_pure none fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
        | some inner =>
          cases inner with
          | none => exact safeS_pure (some none) fun _ hfs => ⟨by rintro _ _ _ _ ⟨⟩, hfs⟩
          | some vim =>
            rcases vim with ⟨v', i, m⟩
            refine safeS_pure _ fun _ hfs => ⟨?_, hfs⟩
            intro vp' t' i' m' hres
            cases hres
            refine ⟨hs.vS_ext, fun t'' ht'' => ?_⟩
            by_cases htt'' : t'' = c.1.1
            · subst htt''
              simp only [Function.update_self, Option.some.injEq] at ht''
              exact hres' v' i m rfl ht''
            · simp only [Function.update_of_ne htt''] at ht''
              exact hs.vR_ext t'' ht''

theorem safeS_liftH_true {α : Type}
    {x : HM (FSpec SS RS T M E) (FSState T Sig K I SS RS E) α}
    (hx : SafeS Q (InvFS mo.tStar) (fun _ s => InvFS mo.tStar s) x) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es) (liftH x) := fun es hes => by
  unfold liftH
  exact (hx es.h hes.fs).bind fun p hp => SafePost.pure ⟨hes.vp, hp⟩

theorem safeS_liftH_and {α : Type} {C : α → Prop}
    {x : HM (FSpec SS RS T M E) (FSState T Sig K I SS RS E) α}
    (hx : SafeS Q (InvFS mo.tStar) (fun a s => C a ∧ InvFS mo.tStar s) x) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar)
      (fun a es => C a ∧ InvE mo.tStar es) (liftH x) := fun es hes => by
  unfold liftH
  exact (hx es.h hes.fs).bind fun p hp => SafePost.pure ⟨hp.1, ⟨hes.vp, hp.2⟩⟩

theorem safeS_abortE :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (abortE : EM (FSpec SS RS T M E) Γ T Sig (Option SS) (Option RS) M E
        (FSState T Sig K I SS RS E) Unit) := by
  unfold abortE
  exact safeS_modify_true _ fun _ hes => ⟨hes.vp, hes.fs⟩

theorem safeS_commitE (s : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (hs : ∀ P, InvVP mo.tStar (s.st P)) (P : Party)
    (old new : VP Γ T Sig (Option SS) (Option RS)) (hnew : InvVP mo.tStar new) (pos : SM.Pos) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar)
      (fun s₁? es => (∀ s₁, s₁? = some s₁ → ∀ P', InvVP mo.tStar (s₁.st P')) ∧ InvE mo.tStar es)
      (commitE (hooksFS cka prng fs Δcka mo j) s P old new pos) := by
  unfold commitE
  dsimp only [hooksFS]
  refine safeS_bind_and
    (safeS_liftH_and (mo := mo) (safeS_pure (some new) fun _ hfs => ⟨rfl, hfs⟩))
    fun res hres => ?_
  subst hres
  refine safeS_pure _ fun _ hes' => ⟨?_, hes'⟩
  intro s₁ hs₁ P'
  cases hs₁
  dsimp only
  by_cases hP' : P' = P
  · subst hP'
    simpa using hnew
  · simpa [hP'] using invVP_accept hs P hnew pos P'

include hQ in
theorem safeS_transmitEGen (q : Party × M × Option CCoins) (hm : transOk q.2.1) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.policy q) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  refine safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact safeS_pure_true none
    | some s₁ =>
      have hst₁ : ∀ P', InvVP mo.tStar (s₁.st P') := by
        rw [epMgmt_st (2 + Δcka) qep hep]
        exact hes.vp
      by_cases h2 : mo.policy.leakDoom es.g s₁ = true
      · simp only [h2, ↓reduceIte]
        exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine safeS_bind_and
          (safeS_liftH_and (mo := mo)
            (safeS_vSendGen hQ cka prng fs Δcka j s₁ P (s₁.st P) (hst₁ P) m
              none r (fun _ => hm) (by rintro _ _ ⟨⟩)))
          fun res hres => ?_
        cases res with
        | none =>
          exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
        | some sc =>
          rcases sc with ⟨st', c⟩
          have hst' : InvVP mo.tStar st' := hres st' c rfl
          exact safeS_bind_true
            (safeS_modify_true _ fun _ h =>
              ⟨invVP_record (2 + Δcka) hst₁ P hst' _ false, h.fs⟩)
            fun _ => safeS_pure_true (some c)

include hQ₀ in
theorem safeS_transmitE (q : Party × M × Option CCoins) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.policy q) :=
  safeS_transmitEGen hQ₀ cka prng fs Δcka qep j q trivial

include hQ in
theorem safeS_challEGen (q : Party × M × M × Option CCoins)
    (heq : challOk q.2.1 q.2.2.1) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg mo.policy q) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  refine safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact safeS_pure_true none
    | some s₁ =>
      have hst₁ : ∀ P', InvVP mo.tStar (s₁.st P') := by
        rw [epMgmt_st (2 + Δcka) qep hep]
        exact hes.vp
      by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !(mo.cfg (M := M)).challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]
        exact safeS_pure_true none
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : mo.policy.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          have hpair : ∀ x₀ x₁, some (m₀, m₁) = some (x₀, x₁) → challOk x₀ x₁ := by
            intro x₀ x₁ h
            cases h
            exact heq
          refine safeS_bind_and
            (safeS_liftH_and (mo := mo)
              (safeS_vSendGen hQ cka prng fs Δcka j s₁ P (s₁.st P) (hst₁ P) _
                (some (m₀, m₁)) r (by rintro ⟨⟩) hpair))
            fun res hres => ?_
          cases res with
          | none =>
            exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
          | some sc =>
            rcases sc with ⟨st', c⟩
            have hst' : InvVP mo.tStar st' := hres st' c rfl
            exact safeS_bind_true
              (safeS_modify_true _ fun _ h =>
                ⟨invVP_record (2 + Δcka) hst₁ P hst' _ true, h.fs⟩)
              fun _ => safeS_pure_true (some c)

include hQ₀ in
theorem safeS_challE (q : Party × M × M × Option CCoins)
    (heq : pubOf q.2.1 = pubOf q.2.2.1) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg mo.policy q) :=
  safeS_challEGen hQ₀ cka prng fs Δcka qep j q heq

include hQ in
theorem safeS_deliverE (q : Party × (Header T × E)) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip mo.cfg q) := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  refine safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact safeS_pure_true none
    | some r =>
      refine safeS_bind_and
        (safeS_liftH_and (mo := mo)
          (safeS_vRecv hQ cka prng fs Δcka j es.g P (es.g.st P) (hes.vp P) c (some r)))
        fun res hres => ?_
      cases res with
      | none =>
        exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
      | some inner =>
        cases inner with
        | none =>
          by_cases h2 : ((mo.cfg (M := M)).deliverWin && es.g.mustBeCorrect fs.maxSkip P r) = true
          · simp only [h2, ↓reduceIte]
            exact safeS_bind_true (safeS_modify_true _ fun _ h => ⟨h.vp, h.fs⟩)
              fun _ => safeS_pure_true (some RecvResult.rejected)
          · simp only [h2, Bool.false_eq_true, ↓reduceIte, pure_bind]
            exact safeS_pure_true (some RecvResult.rejected)
        | some stim =>
          rcases stim with ⟨st', t', i', m'⟩
          have hst' : InvVP mo.tStar st' := hres st' t' i' m' rfl
          refine safeS_bind_and
            (safeS_commitE cka prng fs Δcka j es.g hes.vp P (es.g.st P) st' hst' r.pos)
            fun s₁? hs₁? => ?_
          cases s₁? with
          | none => exact safeS_pure_true none
          | some s₁ =>
            have hs₁ : ∀ P', InvVP mo.tStar (s₁.st P') := hs₁? s₁ rfl
            exact safeS_bind_true
              (safeS_modify_true _ fun _ h' => ⟨fun P' => by split_ifs <;> exact hs₁ P', h'.fs⟩)
              fun _ => safeS_pure_true _

include hQ in
theorem safeS_injectE (q : Party × (Header T × E)) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (injectE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q) := by
  rcases q with ⟨P, c⟩
  unfold injectE
  refine safeS_get_bind fun es hes => ?_
  by_cases h1 :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    refine safeS_bind_and
      (safeS_liftH_and (mo := mo)
        (safeS_vRecv hQ cka prng fs Δcka j es.g P (es.g.st P) (hes.vp P) c none))
      fun res hres => ?_
    cases res with
    | none =>
      exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
    | some inner =>
      cases inner with
      | none => exact safeS_pure_true (some RecvResult.rejected)
      | some stim =>
        rcases stim with ⟨st', t', i', m'⟩
        have hst' : InvVP mo.tStar st' := hres st' t' i' m' rfl
        by_cases h2 : qep + 1 < t'
        · simp only [h2, ↓reduceIte]
          exact safeS_pure_true (some RecvResult.rejected)
        · simp only [h2, ↓reduceIte]
          by_cases h3 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
          · simp only [h3, ↓reduceIte]
            refine safeS_bind_and
              (safeS_commitE cka prng fs Δcka j es.g hes.vp P (es.g.st P) st' hst'
                ⟨P.other, t', i'⟩)
              fun s₁? hs₁? => ?_
            cases s₁? with
            | none => exact safeS_pure_true none
            | some s₁ =>
              have hs₁ : ∀ P', InvVP mo.tStar (s₁.st P') := hs₁? s₁ rfl
              exact safeS_bind_true
                (safeS_modify_true _ fun _ h' => ⟨hs₁, h'.fs⟩)
                fun _ => safeS_pure_true _
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            by_cases h4 : (mo.cfg (M := M)).injectFull t' = true
            · simp only [h4, ↓reduceIte]
              exact safeS_bind_true (safeS_modify_true _ fun _ h => ⟨h.vp, h.fs⟩)
                fun _ => safeS_pure_true (some RecvResult.rejected)
            · simp only [h4, Bool.false_eq_true, ↓reduceIte, pure_bind]
              exact safeS_pure_true (some RecvResult.rejected)

include hQ in
theorem safeS_corrE (P : Party) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (corrE (hooksFS cka prng fs Δcka mo j) mo.policy P) := by
  unfold corrE
  refine safeS_get_bind fun es hes => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowed P) = true
  · simp only [h1, ↓reduceIte]
    exact safeS_pure_true none
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine safeS_bind_true
        (safeS_liftH_true (mo := mo)
          (safeS_reveal hQ cka prng fs Δcka j es.g P (es.g.st P)))
        fun res => ?_
      cases res with
      | none => exact safeS_bind_true (safeS_abortE (mo := mo)) fun _ => safeS_pure_true none
      | some st =>
        refine safeS_bind_true
          (safeS_modify_true _ fun _ h => ⟨hes.vp, h.fs⟩)
          fun _ => safeS_pure_true (some st)

include hQ in
theorem safeS_coinsE (n : ℕ) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (coinsE n : EM (FSpec SS RS T M E) Γ T Sig (Option SS) (Option RS) M E
        (FSState T Sig K I SS RS E) (Fin (n + 1))) :=
  safeS_lift_query (hQ.u n)

include hQ in
theorem safePost_runFSGen
    {badQ : (unifSpec + SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain → Prop}
    [DecidablePred badQ]
    (b : Bool) (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hB : B.IsQueryBoundP badQ 0)
    (htrans : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inl q))))) → transOk q.2.1)
    (hchall : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inr q))))) → challOk q.2.1 q.2.2.1) :
    SafePost Q (fun _ => True) (runFS cka prng fs lam Δcka qep mo j b B) := by
  unfold runFS engRun
  refine (safeS_initFS hQ cka prng fs lam j {} (invFS_empty mo.tStar)).bind fun p hp => ?_
  rcases p with ⟨vs, h⟩
  cases vs with
  | none => exact SafePost.pure trivial
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    rcases hp.1 vA vB rfl with ⟨hvA, hvB⟩
    have hes₀ : InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
        (M := M) (E := E) mo.tStar
        { g := { st := fun P => match P with | .A => vA | .B => vB, b }, h } :=
      ⟨fun P => by cases P <;> assumption, hp.2⟩
    have hsim : SafePost Q (fun r => InvE mo.tStar r.2)
        ((simulateQ (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg
          mo.policy) B).run
          { g := { st := fun P => match P with | .A => vA | .B => vB, b }, h }) := by
      refine SafePost.simulateQ_run (SafePost.of_isQueryBoundP hB) ?_ hes₀
      rintro (u | t) hpt
      · exact safeS_coinsE hQ u
      · rcases t with ((((q | q) | q) | q) | P)
        · exact safeS_transmitEGen hQ cka prng fs Δcka qep j q (htrans q hpt)
        · exact safeS_challEGen hQ cka prng fs Δcka qep j q (hchall q hpt)
        · exact safeS_deliverE hQ cka prng fs Δcka j q
        · exact safeS_injectE hQ cka prng fs Δcka qep j q
        · exact safeS_corrE hQ cka prng fs Δcka j P
    exact hsim.bind fun _ _ => SafePost.pure trivial

include hQ₀ in
theorem safePost_runFS (b : Bool) (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (heq : SM.EqualPubChalls pubOf B) :
    SafePost Q (fun _ => True) (runFS cka prng fs lam Δcka qep mo j b B) :=
  safePost_runFSGen hQ₀ cka prng fs lam Δcka qep j b B heq
    (fun _ _ => trivial) (fun q hpt => by simpa [QSM, SM.unequalPubChall] using hpt)

theorem safePost_redFSAuthGen {Q : (RSpec SS RS T M E).Domain → Prop}
    {transOk : M → Prop} {challOk : M → M → Prop}
    {badQ : (unifSpec + SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain → Prop}
    [DecidablePred badQ]
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q ⟨true, tL, t⟩ transOk challOk)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hB : B.IsQueryBoundP badQ 0)
    (htrans : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inl q))))) → transOk q.2.1)
    (hchall : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inr q))))) → challOk q.2.1 q.2.2.1) :
    SafePost Q (fun _ => True) (redFSAuth cka prng fs lam Δcka qep j tL t B) := by
  unfold redFSAuth
  exact (safePost_runFSGen hQ cka prng fs lam Δcka qep j false B hB htrans hchall).bind fun _ _ =>
    safePost_sampleT hQ Bool

theorem safePost_redFSAuth {Q : (RSpec SS RS T M E).Domain → Prop} {pubOf : M → Pub}
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQ (SS := SS) (RS := RS) (E := E) Q ⟨true, tL, t⟩ pubOf)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (heq : SM.EqualPubChalls pubOf B) :
    SafePost Q (fun _ => True) (redFSAuth cka prng fs lam Δcka qep j tL t B) :=
  safePost_redFSAuthGen cka prng fs lam Δcka qep j tL t hQ B heq
    (fun _ _ => trivial) (fun q hpt => by simpa [QSM, SM.unequalPubChall] using hpt)

theorem safePost_redFSPrivGen {Q : (RSpec SS RS T M E).Domain → Prop}
    {transOk : M → Prop} {challOk : M → M → Prop}
    {badQ : (unifSpec + SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain → Prop}
    [DecidablePred badQ]
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q ⟨false, tL, t⟩ transOk challOk)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hB : B.IsQueryBoundP badQ 0)
    (htrans : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inl q))))) → transOk q.2.1)
    (hchall : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inr q))))) → challOk q.2.1 q.2.2.1) :
    SafePost Q (fun _ => True) (redFSPriv cka prng fs lam Δcka qep tL t B) := by
  unfold redFSPriv
  refine (safePost_runFSGen hQ cka prng fs lam Δcka qep 0 false B hB htrans hchall).bind fun res _ => ?_
  cases res with
  | none => exact safePost_sampleT hQ Bool
  | some p =>
    rcases p with ⟨b', es⟩
    dsimp only
    split_ifs
    · exact SafePost.pure trivial
    · exact safePost_sampleT hQ Bool

theorem safePost_redFSPriv {Q : (RSpec SS RS T M E).Domain → Prop} {pubOf : M → Pub}
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQ (SS := SS) (RS := RS) (E := E) Q ⟨false, tL, t⟩ pubOf)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (heq : SM.EqualPubChalls pubOf B) :
    SafePost Q (fun _ => True) (redFSPriv cka prng fs lam Δcka qep tL t B) :=
  safePost_redFSPrivGen cka prng fs lam Δcka qep tL t hQ B heq
    (fun _ _ => trivial) (fun q hpt => by simpa [QSM, SM.unequalPubChall] using hpt)

theorem safePost_redFSPrivCoinGen {Q : (RSpec SS RS T M E).Domain → Prop}
    {transOk : M → Prop} {challOk : M → M → Prop}
    {badQ : (unifSpec + SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain → Prop}
    [DecidablePred badQ]
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQGen (SS := SS) (RS := RS) (E := E) Q ⟨false, tL, t⟩ transOk challOk)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hB : B.IsQueryBoundP badQ 0)
    (htrans : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inl q))))) → transOk q.2.1)
    (hchall : ∀ q, ¬ badQ (.inr (.inl (.inl (.inl (.inr q))))) → challOk q.2.1 q.2.2.1) :
    SafePost Q (fun _ => True) (redFSPrivCoin cka prng fs lam Δcka qep tL t B) := by
  unfold redFSPrivCoin
  exact (safePost_runFSGen hQ cka prng fs lam Δcka qep 0 false B hB htrans hchall).bind fun _ _ =>
    safePost_sampleT hQ Bool

theorem safePost_redFSPrivCoin {Q : (RSpec SS RS T M E).Domain → Prop} {pubOf : M → Pub}
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQ (SS := SS) (RS := RS) (E := E) Q ⟨false, tL, t⟩ pubOf)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (heq : SM.EqualPubChalls pubOf B) :
    SafePost Q (fun _ => True) (redFSPrivCoin cka prng fs lam Δcka qep tL t B) :=
  safePost_redFSPrivCoinGen cka prng fs lam Δcka qep tL t hQ B heq
    (fun _ _ => trivial) (fun q hpt => by simpa [QSM, SM.unequalPubChall] using hpt)

theorem validQ_unequalPubChall {M' : Type} (mo : Mode) :
    ValidQ (SS := SS) (RS := RS) (T := T) (M := Pub × M') (E := E) (Pub := Pub)
      (fun t => FSAEAD.unequalPubChall (SS := SS) (RS := RS) (AD := Header T) (Pub := Pub)
        (M := M') (C := E) t = true)
      mo Prod.fst where
  u _ := by simp [FSAEAD.unequalPubChall]
  cs := by simp [FSAEAD.unequalPubChall]
  cr := by simp [FSAEAD.unequalPubChall]
  t _ _ _ _ := by simp [FSAEAD.unequalPubChall]
  c _ _ _ _ heq := by simp [FSAEAD.unequalPubChall, heq]
  d _ _ _ := by simp [FSAEAD.unequalPubChall]
  i _ _ _ := by simp [FSAEAD.unequalPubChall]

theorem validQ_offClass (mo : Mode) (pubOf : M → Pub) :
    ValidQ (SS := SS) (RS := RS) (T := T) (M := M) (E := E) (Pub := Pub)
      (fun t => FSAEAD.queryADOutsideClass (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (C := E)
        (fun h : Header T => h.1) mo.tStar t = true)
      mo pubOf where
  u _ := by simp [FSAEAD.queryADOutsideClass]
  cs := by simp [FSAEAD.queryADOutsideClass]
  cr := by simp [FSAEAD.queryADOutsideClass]
  t _ _ ht _ := by simp [FSAEAD.queryADOutsideClass, ht]
  c _ _ _ ht _ := by simp [FSAEAD.queryADOutsideClass, ht]
  d _ _ ht := by simp [FSAEAD.queryADOutsideClass, ht]
  i _ _ ht := by simp [FSAEAD.queryADOutsideClass, ht]

end RedFS

section Targets

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem auth_restricted_proof (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (heq : SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) A) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    FSAEAD.EqualPubChallenges (redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep j tL t (Thm1.challSim (2 + 1) qep A)) ∧
      FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) (redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep j tL t (Thm1.challSim (2 + 1) qep A)) := by
  have heqB : SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (Thm1.challSim (2 + 1) qep A) :=
    challSim_equalPub (2 + 1) qep (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) A
  refine ⟨?_, ⟨t, ?_⟩⟩
  · exact SafePost.to_isQueryBoundP
      (safePost_redFSAuth (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
        lam 1 qep j tL t (validQ_unequalPubChall ⟨true, tL, t⟩) (Thm1.challSim (2 + 1) qep A) heqB)
  · exact SafePost.to_isQueryBoundP
      (safePost_redFSAuth (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
        lam 1 qep j tL t (validQ_offClass ⟨true, tL, t⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1))
        (Thm1.challSim (2 + 1) qep A) heqB)

theorem priv_restricted_proof (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (heq : SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) A) (tL : Option ℕ) (i : ℕ)
    (blank : LibsignalMsgPublicPart × Plain ℓ → LibsignalMsgPublicPart × Plain ℓ) (hblank : ∀ m, (blank m).1 = m.1) :
    let fs := lFS C codec ℓ encT idOf maxSkip
    let B := ThmB.privRedB (2 + 1) qep i blank A
    (FSAEAD.EqualPubChallenges (redFSPriv (dhScheme Dh) (rootPRNG C.F encPt) fs lam 1 qep tL i B) ∧
      FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1)
        (redFSPriv (dhScheme Dh) (rootPRNG C.F encPt) fs lam 1 qep tL i B)) ∧
    (FSAEAD.EqualPubChallenges (redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt) fs lam 1 qep tL i B) ∧
      FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1)
        (redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt) fs lam 1 qep tL i B)) := by
  dsimp only
  have heqB : SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
      (ThmB.privRedB (2 + 1) qep i blank A) :=
    privRedB_equalPub_local (2 + 1) qep i (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) blank hblank A
  refine ⟨⟨?_, ⟨i, ?_⟩⟩, ⟨?_, ⟨i, ?_⟩⟩⟩
  · exact SafePost.to_isQueryBoundP
      (safePost_redFSPriv (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
        lam 1 qep tL i (validQ_unequalPubChall ⟨false, tL, i⟩)
        (ThmB.privRedB (2 + 1) qep i blank A) heqB)
  · exact SafePost.to_isQueryBoundP
      (safePost_redFSPriv (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
        lam 1 qep tL i (validQ_offClass ⟨false, tL, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1))
        (ThmB.privRedB (2 + 1) qep i blank A) heqB)
  · exact SafePost.to_isQueryBoundP
      (safePost_redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
        lam 1 qep tL i (validQ_unequalPubChall ⟨false, tL, i⟩)
        (ThmB.privRedB (2 + 1) qep i blank A) heqB)
  · exact SafePost.to_isQueryBoundP
      (safePost_redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
        lam 1 qep tL i (validQ_offClass ⟨false, tL, i⟩ (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1))
        (ThmB.privRedB (2 + 1) qep i blank A) heqB)

end Targets
end CryptoGames.LibsignalSM.Proofs.RestrictedReds
