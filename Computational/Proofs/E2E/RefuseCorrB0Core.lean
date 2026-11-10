/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1A
public import Computational.Proofs.E2E.UniformStartHop

/-!
# Generic `Adversary.refuseCorrB0` SM game wrapper

**Checked by Lean.** Defines the `Adversary.refuseCorrB0` wrapper enforcing `noBobCorrInEpoch0`
(`DEV-LS33`) and `noBobCorrWhileAliceBelowEpoch10` (`DEV-LS34`) locally, and proves query-bound
preservation (`refuseCorrB0_queries`) and exact R-game equivalence (`gameR_withNoCorrB0_eq`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.RefuseCorrB0

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq
  CryptoVerification.E2E.HeadlineU CryptoVerification.E2E.SpkHop1

/-- Add `noBobCorrInEpoch0` (`DEV-LS33`) and `noBobCorrWhileAliceBelowEpoch10` (`DEV-LS34`) to `cfg.corrOK`. -/
def withNoCorrB0 {St Msg C : Type} (cfg : ConfigR St Msg C) : ConfigR St Msg C :=
  { cfg with corrOK := fun s P => cfg.corrOK s P && noBobCorrInEpoch0 s P && noBobCorrWhileAliceBelowEpoch10 s P }

/-- Observable game-state shadow tracked by the `refuseCorrB0` wrapper: party epochs,
within-epoch indices, and in-transit `(pos, ct)` pairs. -/
structure RefuseState (C : Type) where
  epoch : Party → ℕ := fun _ => 0
  idx : Party → ℕ := fun _ => 0
  trans : List (SM.Pos × C) := []

namespace RefuseState

variable {C : Type}

def onSend (rs : RefuseState C) (P : Party) (c : C) : RefuseState C :=
  let ep' :=
    if P.sendsIn (rs.epoch P + 1) then Function.update rs.epoch P (rs.epoch P + 1) else rs.epoch
  let idx₀ := if P.sendsIn (rs.epoch P + 1) then Function.update rs.idx P 0 else rs.idx
  let pos : SM.Pos := ⟨P, ep' P, idx₀ P + 1⟩
  { epoch := ep'
    idx := Function.update idx₀ P (idx₀ P + 1)
    trans := (pos, c) :: rs.trans }

def onAccept (rs : RefuseState C) (P : Party) (pos : SM.Pos) : RefuseState C :=
  { rs with
    epoch := Function.update rs.epoch P (max (rs.epoch P) pos.epoch)
    trans := rs.trans.filter (fun pc => pc.1 != pos) }

def onDeliver [DecidableEq C] (rs : RefuseState C) (P : Party) (c : C) : RefuseState C :=
  match rs.trans.find? (fun pc => pc.1.sender == P.other && decide (pc.2 = c)) with
  | some (pos, _) => rs.onAccept P pos
  | none => rs

def ofGameState {St Msg : Type} (s : GameState St Msg C) : RefuseState C :=
  { epoch := s.epoch
    idx := s.idx
    trans := s.trans.map (fun r => (r.pos, r.ct)) }

end RefuseState

abbrev RefuseM (St Msg Coins C : Type) := StateT (RefuseState C) (AdversaryComp St Msg Coins C)

def refuseTransmit {St Msg Coins C : Type} :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) (RefuseM St Msg Coins C) :=
  fun ⟨P, m, r⟩ => do
    let res ← StateT.lift (transmitQuery (St := St) P m r)
    match res with
    | some c =>
      let rs ← get
      set (rs.onSend P c)
    | none => pure ()
    return res

def refuseChall {St Msg Coins C : Type} :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) (RefuseM St Msg Coins C) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let res ← StateT.lift (challQuery (St := St) P m₀ m₁ r)
    match res with
    | some c =>
      let rs ← get
      set (rs.onSend P c)
    | none => pure ()
    return res

def refuseDeliver {St Msg Coins C : Type} [DecidableEq C] :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) (RefuseM St Msg Coins C) :=
  fun ⟨P, c⟩ => do
    let res ← StateT.lift (deliverQuery (St := St) (Coins := Coins) P c)
    match res with
    | some (.accepted _ _ _) =>
      let rs ← get
      set (rs.onDeliver P c)
    | _ => pure ()
    return res

def refuseInject {St Msg Coins C : Type} :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) (RefuseM St Msg Coins C) :=
  fun ⟨P, c⟩ => do
    let res ← StateT.lift (injectQuery (St := St) (Coins := Coins) P c)
    match res with
    | some (.accepted t' i' _) =>
      let rs ← get
      set (rs.onAccept P ⟨P.other, t', i'⟩)
    | _ => pure ()
    return res

def refuseCorr {St Msg Coins C : Type} :
    QueryImpl (Party →ₒ Option St) (RefuseM St Msg Coins C) :=
  fun P => do
    let rs ← get
    if (P == .B && (rs.epoch .B == 0)) || (P == .B && decide (rs.epoch .A < 10)) then
      return none
    else
      StateT.lift (corrQuery (Msg := Msg) (Coins := Coins) (C := C) P)

def refuseCorrB0Impl {St Msg Coins C : Type} [DecidableEq C] :
    QueryImpl (unifSpec + spec St Msg Coins C) (RefuseM St Msg Coins C) :=
  let c : QueryImpl unifSpec (RefuseM St Msg Coins C) := fun n =>
    StateT.lift (query (spec := unifSpec + spec St Msg Coins C) (.inl n))
  let i₁ : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) (RefuseM St Msg Coins C) :=
    refuseTransmit
  let i₂ : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) (RefuseM St Msg Coins C) :=
    refuseChall
  let i₃ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) (RefuseM St Msg Coins C) :=
    refuseDeliver
  let i₄ : QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) (RefuseM St Msg Coins C) :=
    refuseInject
  let i₅ : QueryImpl (Party →ₒ Option St) (RefuseM St Msg Coins C) :=
    refuseCorr
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

/-- Wrap `A` to refuse `corr-B` locally in epoch 0 (`DEV-LS33`) and while `epoch A < 10`
(`DEV-LS34`). -/
def _root_.CryptoGames.SM.Adversary.refuseCorrB0 {St Msg Coins C : Type} [DecidableEq C]
    (A : Adversary St Msg Coins C) : Adversary St Msg Coins C :=
  (simulateQ refuseCorrB0Impl A).run' {}

section Queries

variable {St Msg Coins C : Type} [DecidableEq C]

omit [DecidableEq C] in
private lemma query_eq_liftM (t : (unifSpec + spec St Msg Coins C).Domain) :
    (query (spec := unifSpec + spec St Msg Coins C) t : AdversaryComp St Msg Coins C _) =
      liftM ((unifSpec + spec St Msg Coins C).query t) := rfl

private lemma stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type} (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

private lemma isQueryBoundP_refuseOracles
    (o : (spec St Msg Coins C).Domain) (rs : RefuseState C) :
    IsQueryBoundP
      ((refuseCorrB0Impl (St := St) (Msg := Msg) (Coins := Coins) (C := C) (.inr o)).run rs)
      (· matches Sum.inr _) 1 := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change IsQueryBoundP
      ((refuseTransmit (St := St) (Msg := Msg) (Coins := Coins) (C := C) (P, m, r)).run rs)
      (· matches Sum.inr _) 1
    unfold refuseTransmit transmitQuery
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> simp
  · change IsQueryBoundP
      ((refuseChall (St := St) (Msg := Msg) (Coins := Coins) (C := C) (P, m₀, m₁, r)).run rs)
      (· matches Sum.inr _) 1
    unfold refuseChall challQuery
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> simp
  · change IsQueryBoundP
      ((refuseDeliver (St := St) (Msg := Msg) (Coins := Coins) (C := C) (P, c)).run rs)
      (· matches Sum.inr _) 1
    unfold refuseDeliver deliverQuery
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp
  · change IsQueryBoundP
      ((refuseInject (St := St) (Msg := Msg) (Coins := Coins) (C := C) (P, c)).run rs)
      (· matches Sum.inr _) 1
    unfold refuseInject injectQuery
    simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind]
    rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp
  · change IsQueryBoundP ((refuseCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P).run rs)
      (· matches Sum.inr _) 1
    unfold refuseCorr corrQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp only [StateT.run_pure]
      exact isQueryBoundP_pure _ _ 1
    · simp only [stateT_lift_run]
      rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩

/-- Query bounds carry over to `A.refuseCorrB0`. -/
theorem refuseCorrB0_queries (A : Adversary St Msg Coins C) (q : ℕ)
    (hq : MakesAtMostQueries A q) :
    MakesAtMostQueries A.refuseCorrB0 q := by
  unfold MakesAtMostQueries Adversary.refuseCorrB0
  have hsim : IsQueryBoundP
      ((simulateQ (refuseCorrB0Impl (St := St) (Msg := Msg) (Coins := Coins) (C := C)) A).run
        ({} : RefuseState C))
      (· matches Sum.inr _) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ ({} : RefuseState C)
    · rintro (n | o) hp rs
      · cases hp
      · exact isQueryBoundP_refuseOracles o rs
    · rintro (n | o) hnp rs
      · change IsQueryBoundP
          ((StateT.lift (query (spec := unifSpec + spec St Msg Coins C) (.inl n)) :
            RefuseM St Msg Coins C _).run rs)
          (· matches Sum.inr _) 0
        simp only [stateT_lift_run]
        rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by rintro ⟨⟩), fun _ => by simp⟩
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

end Queries

section Coupling

variable {Key St Msg Coins RCoins C : Type}
variable [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]

abbrev fullImplG (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (unifSpec + spec St Msg Coins C)
      (StateT (GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) ProbComp) +
    oracleImplR sm Δ qep cfg

omit [DecidableEq Msg] [DecidableEq C] in
theorem ofGameState_record_epMgmt {s s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hep : s.epMgmt Δ qep P bad = some s₁) (st' : St) (m : Msg) (c : C) (isChall : Bool) :
    RefuseState.ofGameState (s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall) =
      (RefuseState.ofGameState s).onSend P c := by
  unfold GameState.epMgmt at hep
  by_cases hsends : P.sendsIn (s.epoch P + 1) = true
  · simp only [hsends, ↓reduceIte] at hep
    split at hep
    · contradiction
    · injection hep with hep
      subst hep
      split <;> simp [RefuseState.ofGameState, RefuseState.onSend, GameState.record,
        GameState.leak, hsends]
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hep
    split at hep
    · contradiction
    · injection hep with hep
      subst hep
      simp [RefuseState.ofGameState, RefuseState.onSend, GameState.record, hsends]

omit [DecidableEq Msg] [DecidableEq C] in
theorem ofGameState_accept (s : GameState St Msg C) (P : Party) (st' : St) (pos : SM.Pos) :
    RefuseState.ofGameState (s.accept P st' pos) = (RefuseState.ofGameState s).onAccept P pos := by
  simp only [RefuseState.ofGameState, RefuseState.onAccept, GameState.accept, GameState.delete]
  rw [List.filter_map]
  rfl

omit [DecidableEq Msg] in
theorem find_map_trans_of_inTransit {s : GameState St Msg C} {Q : Party} {c : C}
    {r : Record Msg C} (htr : s.inTransit Q c = some r) :
    (s.trans.map (fun r => (r.pos, r.ct))).find?
      (fun pc => pc.1.sender == Q && decide (pc.2 = c)) = some (r.pos, r.ct) := by
  unfold GameState.inTransit at htr
  rw [List.find?_map]
  change Option.map (fun r => (r.pos, r.ct))
    (s.trans.find? (fun r => r.pos.sender == Q && decide (r.ct = c))) = some (r.pos, r.ct)
  rw [htr]
  rfl

omit [DecidableEq Msg] in
theorem onDeliver_ofGameState_of_inTransit {s : GameState St Msg C}
    {P : Party} {c : C} {r : Record Msg C} (htr : s.inTransit P.other c = some r)
    (st' : St) :
    (RefuseState.ofGameState s).onDeliver P c =
      RefuseState.ofGameState (s.accept P st' r.pos) := by
  unfold RefuseState.onDeliver
  change (match (s.trans.map (fun r => (r.pos, r.ct))).find?
      (fun pc => pc.1.sender == P.other && decide (pc.2 = c)) with
    | some (pos, _) => (RefuseState.ofGameState s).onAccept P pos
    | none => RefuseState.ofGameState s) = RefuseState.ofGameState (s.accept P st' r.pos)
  rw [find_map_trans_of_inTransit htr, ofGameState_accept]

omit [DecidableEq Msg] [DecidableEq C] in
@[simp] theorem ofGameState_afterCorr (s : GameState St Msg C) (P : Party) :
    RefuseState.ofGameState (s.afterCorr P) = RefuseState.ofGameState s := rfl

omit [DecidableEq Msg] [DecidableEq C] in
@[simp] theorem ofGameState_with_win (s : GameState St Msg C) (w : Bool) :
    RefuseState.ofGameState { s with win := w } = RefuseState.ofGameState s := rfl

theorem transmitR_refuse_eq
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (x : Party × Msg × Option Coins) (s : GameState St Msg C) :
    (simulateQ (fullImplG sm Δ qep cfg)
      ((refuseTransmit x).run (RefuseState.ofGameState s))).run s =
      (fun p => ((p.1, RefuseState.ofGameState p.2), p.2)) <$>
        (transmitR sm Δ qep (withNoCorrB0 cfg) x).run s := by
  rcases x with ⟨P, m, r⟩
  unfold refuseTransmit
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, simulateQ_bind,
    transmitQuery, simulateQ_oracleSpec_query, fullImplG, QueryImpl.add_apply, oracleImplR]
  rw [map_eq_bind_pure_comp]
  unfold transmitR transmitImpl withNoCorrB0
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hok : cfg.sendOK s P = true
  · by_cases hwin : s.win = true
    · simp [hok, hwin]
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind, hwin, StateT.run_monadLift, bind_assoc]
      congr 1
      funext cb
      cases hep : s.epMgmt Δ qep P cb.2 with
      | none => simp
      | some s₁ =>
        have hrec := ofGameState_record_epMgmt hep (sm.sendPart.send (s₁.st P) m cb.1).1 m
          (sm.sendPart.send (s₁.st P) m cb.1).2 false
        simp [hrec]
  · simp [hok]

theorem challR_refuse_eq
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (x : Party × Msg × Msg × Option Coins) (s : GameState St Msg C) :
    (simulateQ (fullImplG sm Δ qep cfg)
      ((refuseChall x).run (RefuseState.ofGameState s))).run s =
      (fun p => ((p.1, RefuseState.ofGameState p.2), p.2)) <$>
        (challR sm Δ qep (withNoCorrB0 cfg) x).run s := by
  rcases x with ⟨P, m₀, m₁, r⟩
  unfold refuseChall
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, simulateQ_bind,
    challQuery, simulateQ_oracleSpec_query, fullImplG, QueryImpl.add_apply, oracleImplR]
  rw [map_eq_bind_pure_comp]
  unfold challR challImpl withNoCorrB0
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hok : cfg.sendOK s P = true
  · by_cases hwin : s.win = true
    · simp [hok, hwin]
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind, hwin, StateT.run_monadLift, bind_assoc]
      congr 1
      funext cb
      cases hep : s.epMgmt Δ qep P cb.2 with
      | none => simp
      | some s₁ =>
        dsimp only []
        by_cases hch : (!s₁.safeCh Δ P || !cfg.base.challAllowedIn (s₁.epoch P)) = true
        · simp [hch]
        · set msg := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
          have hrec := ofGameState_record_epMgmt hep (sm.sendPart.send (s₁.st P) msg cb.1).1 msg
            (sm.sendPart.send (s₁.st P) msg cb.1).2 true
          simp [hch, hrec]
  · simp [hok]

theorem deliverR_refuse_eq
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (x : Party × C) (s : GameState St Msg C) :
    (simulateQ (fullImplG sm Δ qep cfg)
      ((refuseDeliver x).run (RefuseState.ofGameState s))).run s =
      (fun p => ((p.1, RefuseState.ofGameState p.2), p.2)) <$>
        (deliverR sm (withNoCorrB0 cfg) x).run s := by
  rcases x with ⟨P, c⟩
  unfold refuseDeliver
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, simulateQ_bind,
    deliverQuery, simulateQ_oracleSpec_query, fullImplG, QueryImpl.add_apply, oracleImplR]
  rw [map_eq_bind_pure_comp]
  unfold deliverR withNoCorrB0
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hwin : s.win
  · cases htr : s.inTransit P.other c with
    | none => simp
    | some r =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        bind_assoc, pure_bind]
      congr 1
      funext rc
      cases hrcv : sm.receive (s.st P) c rc with
      | none =>
        dsimp only []
        split_ifs <;> simp
      | some v =>
        rcases v with ⟨st', t', i', m'⟩
        dsimp only []
        have hdel := onDeliver_ofGameState_of_inTransit htr st'
        split_ifs <;> simp [hdel]
  · simp

theorem injectR_refuse_eq
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (x : Party × C) (s : GameState St Msg C) :
    (simulateQ (fullImplG sm Δ qep cfg)
      ((refuseInject x).run (RefuseState.ofGameState s))).run s =
      (fun p => ((p.1, RefuseState.ofGameState p.2), p.2)) <$>
        (injectR sm Δ qep (withNoCorrB0 cfg) x).run s := by
  rcases x with ⟨P, c⟩
  unfold refuseInject
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, simulateQ_bind,
    injectQuery, simulateQ_oracleSpec_query, fullImplG, QueryImpl.add_apply, oracleImplR]
  rw [map_eq_bind_pure_comp]
  unfold injectR withNoCorrB0
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond : (s.win || (s.inTransit P.other c).isSome || !s.safeInj Δ || !cfg.injOK c) = true
  · simp [hcond]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      bind_assoc, pure_bind]
    congr 1
    funext rc
    cases hrcv : sm.receive (s.st P) c rc with
    | none => simp
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      dsimp only []
      split_ifs <;> simp [ofGameState_accept]

theorem corrR_refuse_eq
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (P : Party) (s : GameState St Msg C) :
    (simulateQ (fullImplG sm Δ qep cfg)
      ((refuseCorr P).run (RefuseState.ofGameState s))).run s =
      (fun p => ((p.1, RefuseState.ofGameState p.2), p.2)) <$>
        (corrR (withNoCorrB0 cfg) P).run s := by
  unfold refuseCorr corrR withNoCorrB0 noBobCorrInEpoch0 noBobCorrWhileAliceBelowEpoch10
  have hepB : (RefuseState.ofGameState s).epoch .B = s.epoch .B := rfl
  have hepA : (RefuseState.ofGameState s).epoch .A = s.epoch .A := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hepB, hepA]
  by_cases hB : ((P == .B && (s.epoch .B == 0)) || (P == .B && decide (s.epoch .A < 10))) = true
  · rcases Bool.or_eq_true_iff.mp hB with hB0 | hBW
    · simp only [hB0, Bool.true_or, ↓reduceIte, Bool.not_true, Bool.and_false]
      simp
    · simp only [hBW, Bool.or_true, ↓reduceIte, Bool.not_true, Bool.and_false]
      simp
  · have hB0 : (P == .B && (s.epoch .B == 0)) = false := by
      cases h : (P == .B && (s.epoch .B == 0))
      · rfl
      · exfalso; rw [h, Bool.true_or] at hB; exact hB rfl
    have hBW : (P == .B && decide (s.epoch .A < 10)) = false := by
      cases h : (P == .B && decide (s.epoch .A < 10))
      · rfl
      · exfalso; rw [h, Bool.or_true] at hB; exact hB rfl
    simp only [hB0, hBW, Bool.or_self, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.and_true, stateT_lift_run, simulateQ_bind, simulateQ_pure, corrQuery,
      simulateQ_oracleSpec_query, fullImplG, QueryImpl.add_apply, oracleImplR, corrR,
      StateT.run_bind, StateT.run_get, pure_bind, map_eq_bind_pure_comp]
    by_cases hcond :
        (s.win || !s.corrAllowed P || (cfg.r1 && inWindow s P) || !cfg.corrOK s P) = true <;>
      { simp only [hcond, ↓reduceIte]; simp }

theorem refuseCorrB0_step_eq
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    (s : GameState St Msg C) :
    (simulateQ (fullImplG sm Δ qep cfg)
      ((refuseCorrB0Impl t).run (RefuseState.ofGameState s))).run s =
      (fun p => ((p.1, RefuseState.ofGameState p.2), p.2)) <$>
        (fullImplG sm Δ qep (withNoCorrB0 cfg) t).run s := by
  rcases t with n | ((((x | x) | x) | x) | P)
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, stateT_lift_run, simulateQ_bind,
      simulateQ_pure, simulateQ_oracleSpec_query, fullImplG]
    change ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) >>=
        fun u => pure ((u, RefuseState.ofGameState s), s)) =
      (fun p => ((p.1, RefuseState.ofGameState p.2), p.2)) <$>
        ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) >>= fun u => pure (u, s))
    simp [map_eq_bind_pure_comp, bind_assoc]
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplG, oracleImplR]
    exact transmitR_refuse_eq sm Δ qep cfg x s
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplG, oracleImplR]
    exact challR_refuse_eq sm Δ qep cfg x s
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplG, oracleImplR]
    exact deliverR_refuse_eq sm Δ qep cfg x s
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplG, oracleImplR]
    exact injectR_refuse_eq sm Δ qep cfg x s
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplG, oracleImplR]
    exact corrR_refuse_eq sm Δ qep cfg P s

theorem simulateQ_refuseCorrB0_run_eq
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    {α : Type} (oa : AdversaryComp St Msg Coins C α)
    (s : GameState St Msg C) :
    Prod.map Prod.fst id <$>
      (simulateQ (fullImplG sm Δ qep cfg)
        ((simulateQ refuseCorrB0Impl oa).run (RefuseState.ofGameState s))).run s =
      (simulateQ (fullImplG sm Δ qep (withNoCorrB0 cfg)) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [refuseCorrB0_step_eq sm Δ qep cfg t s, bind_map_left, map_eq_bind_pure_comp,
      bind_assoc]
    apply bind_congr_of_support
    intro z _
    dsimp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    rw [← ih z.1 z.2, map_eq_bind_pure_comp]

theorem runR_withNoCorrB0_eq [SampleableType Key]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (_hsendOK : cfg.sendOK = noBobSendInEpoch0 := by rfl)
    (b : Bool) (A : Adversary St Msg Coins C) :
    runR sm Δ qep (withNoCorrB0 cfg) b A =
      runR sm Δ qep cfg b A.refuseCorrB0 := by
  unfold runR Adversary.refuseCorrB0
  congr 1
  funext k
  dsimp only []
  have hinit : RefuseState.ofGameState (initState sm.sendPart k b) = {} := rfl
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, ← hinit]
  exact (simulateQ_refuseCorrB0_run_eq sm Δ qep cfg A (initState sm.sendPart k b)).symm

/-- Running `A` in `withNoCorrB0 cfg` produces the same R-game distribution as running
`A.refuseCorrB0` in `cfg`. -/
theorem gameR_withNoCorrB0_eq [SampleableType Key]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (hsendOK : cfg.sendOK = noBobSendInEpoch0 := by rfl)
    (A : Adversary St Msg Coins C) :
    gameR sm Δ qep (withNoCorrB0 cfg) A =
      gameR sm Δ qep cfg A.refuseCorrB0 := by
  unfold gameR
  congr 1
  funext b
  rw [runR_withNoCorrB0_eq sm Δ qep cfg hsendOK b A]

end Coupling

@[simp] theorem sessionSchemeU_eq_libSessionU (P : Params Bytes Unit) (ℓ : ℕ) :
    sessionSchemeU P ℓ = libSessionU P ℓ := rfl

@[simp] theorem configSpkS_eq_configR1OnCurveSpk {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) {St Msg : Type} :
    (configRefuseEarlyBobCorr decT encT : SM.ConfigR St Msg Bytes) =
      configR1OnCurveSpk (ratchetKeyAdmissible protoSignalCodec decT encT) := rfl

end CryptoVerification.E2E.RefuseCorrB0
