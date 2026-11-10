/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import ToMathlib.MeasureTheory.Measure.Bool
import Mathlib.Tactic.Ring
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

set_option autoImplicit false

/-!
# Faithfulness and identical-until-bad lemmas for `gameRCoinLogged`

**Checked by Lean.**

Proves `GameRCoinLoggedFaithful` (forgetting the `WriterT` send-coin log of `gameRCoinLogged`
equals `SM.gameR`) together with prefix-closed online identical-until-bad, halted-game, and
`boolDist`/`boolBias` transfer lemmas for `smSchemeCoinLogged` and `sessionKemFailProb`.
-/

namespace Computational.Proofs.SpecLemmas.Session.GameRCoinLogged

open MeasureTheory (Measure IsProbabilityMeasure lintegral_congr lintegral_indicator)
open OracleComp OracleSpec
open scoped ENNReal
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey PublicKey)
open CryptoGames.SM (Adversary ConfigR GameState RecvResult challImpl challR corrR deliverR
  gameR initState injectR oracleImplR runR samIfNec spec transmitImpl transmitR)
open CryptoVerification.E2E (Bytes GameRCoinLoggedFaithful SMSchemeRM challRM
  configRefuseEarlyBobCorr deliverRM gameRCoinLogged injectRM liftStateT oracleImplRM
  paramsIdsWithSpqr sessionKemFailProb sessionSchemeFixedSpk smSchemeCoinLogged transmitRM)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes coinBytes_length
  spqrV1SessionUniformCoins)

local instance instLawfulMonadWriterTListCoin {Coins : Type} {M : Type → Type}
    [Monad M] [LawfulMonad M] : LawfulMonad (WriterT (List Coins) M) :=
  LawfulMonad.mk'
    (id_map := fun _ => by ext; simp)
    (pure_bind := fun _ _ => by ext; simp)
    (bind_assoc := fun _ _ _ => by ext; simp)
    (bind_pure_comp := fun _ _ => by ext; simp)

/-! ## Forgetful homomorphism and `GameRCoinLoggedFaithful` -/

def forgetCoinW {Coins α : Type} (m : WriterT (List Coins) ProbComp α) : ProbComp α :=
  Prod.fst <$> m.run

@[simp] theorem forgetCoinW_pure {Coins α : Type} (a : α) :
    forgetCoinW (Coins := Coins) (pure a) = pure a := by simp [forgetCoinW]

@[simp] theorem forgetCoinW_map {Coins α β : Type} (f : α → β)
    (m : WriterT (List Coins) ProbComp α) :
    forgetCoinW (f <$> m) = f <$> forgetCoinW m := by simp [forgetCoinW, Functor.map_map]

@[simp] theorem forgetCoinW_bind {Coins α β : Type}
    (m : WriterT (List Coins) ProbComp α) (k : α → WriterT (List Coins) ProbComp β) :
    forgetCoinW (m >>= k) = forgetCoinW m >>= fun a => forgetCoinW (k a) := by
  simp [forgetCoinW, map_eq_bind_pure_comp, bind_assoc]

@[simp] theorem forgetCoinW_tell {Coins : Type} (w : List Coins) :
    forgetCoinW (MonadWriter.tell w : WriterT (List Coins) ProbComp PUnit) = pure ⟨⟩ := by
  simp [forgetCoinW, MonadWriter.tell]

@[simp] theorem forgetCoinW_liftM {Coins α : Type} (c : ProbComp α) :
    forgetCoinW (liftM c : WriterT (List Coins) ProbComp α) = c := by
  dsimp [forgetCoinW, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [Functor.map_map]

@[simp] theorem smSchemeCoinLogged_send_run {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (m : Msg) (r : Coins) :
    ((smSchemeCoinLogged sm).send st m r).run = pure (sm.send st m r, [r]) := by
  simp [smSchemeCoinLogged, MonadWriter.tell]

@[simp] theorem smSchemeCoinLogged_receive_run {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (c : C) (rc : RCoins) :
    ((smSchemeCoinLogged sm).receive st c rc).run = pure (sm.receive st c rc, []) := by
  simp [smSchemeCoinLogged]

@[simp] theorem smSchemeCoinLogged_initState {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (k : Key) (b : Bool) :
    (smSchemeCoinLogged sm).initState k b = initState sm.sendPart k b := rfl

def pureCoinSchemeRM {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM ProbComp Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := pure (sm.send st m r)
  receive st c rc := pure (sm.receive st c rc)

def forgetCoinS1 {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) : StateT σ ProbComp α :=
  fun s => forgetCoinW (m.run s)

@[simp] theorem forgetCoinS1_run {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) (s : σ) :
    (forgetCoinS1 m).run s = forgetCoinW (m.run s) := rfl

@[simp] theorem forgetCoinS1_pure {Coins σ α : Type} (a : α) :
    forgetCoinS1 (pure a : StateT σ (WriterT (List Coins) ProbComp) α) = pure a := by ext s; simp

@[simp] theorem forgetCoinS1_map {Coins σ α β : Type} (f : α → β)
    (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    forgetCoinS1 (f <$> m) = f <$> forgetCoinS1 m := by ext s; simp

@[simp] theorem forgetCoinS1_bind {Coins σ α β : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α)
    (k : α → StateT σ (WriterT (List Coins) ProbComp) β) :
    forgetCoinS1 (m >>= k) = forgetCoinS1 m >>= fun a => forgetCoinS1 (k a) := by ext s; simp

@[simp] theorem forgetCoinS1_get {Coins σ : Type} :
    forgetCoinS1 (get : StateT σ (WriterT (List Coins) ProbComp) σ) = get := by ext s; simp

@[simp] theorem forgetCoinS1_set {Coins σ : Type} (s' : σ) :
    forgetCoinS1 (set s' : StateT σ (WriterT (List Coins) ProbComp) PUnit) = set s' := by ext s; simp

@[simp] theorem forgetCoinS1_lift {Coins σ α : Type} (m : WriterT (List Coins) ProbComp α) :
    forgetCoinS1 (StateT.lift m : StateT σ (WriterT (List Coins) ProbComp) α) =
      StateT.lift (forgetCoinW m) := by ext s; simp [StateT.run_lift]

@[simp] theorem forgetCoinS1_liftStateT {Coins σ α : Type} (x : StateT σ ProbComp α) :
    forgetCoinS1 (liftStateT (n := WriterT (List Coins) ProbComp) x) = x := by
  ext s; exact forgetCoinW_liftM (x s)

private theorem oracleImplRM_pure_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (spec St Msg Coins C).Domain) :
    oracleImplRM (pureCoinSchemeRM sm) Δ qep cfg q = oracleImplR sm Δ qep cfg q := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change transmitRM (pureCoinSchemeRM sm) Δ qep cfg (P, m, r) = transmitR sm Δ qep cfg (P, m, r)
    ext gs; unfold transmitRM transmitR transmitImpl SMSchemeR.sendPart pureCoinSchemeRM liftM monadLift
    dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs P
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]
        congr 1
      · simp only [↓reduceIte]
  · change challRM (pureCoinSchemeRM sm) Δ qep cfg (P, m₀, m₁, r) = challR sm Δ qep cfg (P, m₀, m₁, r)
    ext gs; unfold challRM challR challImpl SMSchemeR.sendPart pureCoinSchemeRM liftM monadLift
    dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs P
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]
        congr 1
      · simp only [↓reduceIte]
  · change deliverRM (pureCoinSchemeRM sm) cfg (P, c) = deliverR sm cfg (P, c)
    ext gs; unfold deliverRM deliverR pureCoinSchemeRM liftM monadLift
    dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases gs.inTransit P.other c with
      | none => rfl
      | some r => simp only [StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]; congr 1
    · simp only [↓reduceIte]
  · change injectRM (pureCoinSchemeRM sm) Δ qep cfg (P, c) = injectR sm Δ qep cfg (P, c)
    ext gs; unfold injectRM injectR pureCoinSchemeRM liftM monadLift
    dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases (gs.win || (gs.inTransit P.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]
      congr 1
    · simp only [↓reduceIte]
  · rfl

theorem forgetCoinS1_oracleImplRM_smSchemeCoinLogged {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (spec St Msg Coins C).Domain) :
    forgetCoinS1 (oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg q) =
      oracleImplR sm Δ qep cfg q := by
  rw [← oracleImplRM_pure_eq sm Δ qep cfg q]
  have hsend : ∀ s m r,
      forgetCoinW ((smSchemeCoinLogged sm).send s m r) = (pureCoinSchemeRM sm).send s m r := by
    intro s m r; simp [smSchemeCoinLogged, pureCoinSchemeRM]
  have hrecv : ∀ s c rc,
      forgetCoinW ((smSchemeCoinLogged sm).receive s c rc) =
        (pureCoinSchemeRM sm).receive s c rc := by
    intro s c rc; simp [smSchemeCoinLogged, pureCoinSchemeRM]
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change forgetCoinS1 (transmitRM _ Δ qep cfg (P, m, r)) = transmitRM _ Δ qep cfg (P, m, r)
    unfold transmitRM; simp only [forgetCoinS1_bind, forgetCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact forgetCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, forgetCoinS1_bind,
        forgetCoinS1_lift, forgetCoinW_liftM, forgetCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact forgetCoinS1_pure _
      | some s₁ => simp [hsend]
  · change forgetCoinS1 (challRM _ Δ qep cfg (P, m₀, m₁, r)) = challRM _ Δ qep cfg (P, m₀, m₁, r)
    unfold challRM; simp only [forgetCoinS1_bind, forgetCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact forgetCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, forgetCoinS1_bind,
        forgetCoinS1_lift, forgetCoinW_liftM, forgetCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact forgetCoinS1_pure _
      | some s₁ =>
        dsimp only
        cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;> simp [hsend]
  · change forgetCoinS1 (deliverRM _ cfg (P, c)) = deliverRM _ cfg (P, c)
    unfold deliverRM; simp only [forgetCoinS1_bind, forgetCoinS1_get]; congr 1; funext s
    cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, forgetCoinS1_pure]
    cases s.inTransit P.other c with
    | none => exact forgetCoinS1_pure _
    | some r =>
      dsimp only; simp only [forgetCoinS1_bind, forgetCoinS1_lift, forgetCoinW_liftM]
      congr 1; funext rc; rw [hrecv]; congr 1; funext out
      cases out with
      | none => split_ifs <;> simp
      | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · change forgetCoinS1 (injectRM _ Δ qep cfg (P, c)) = injectRM _ Δ qep cfg (P, c)
    unfold injectRM; simp only [forgetCoinS1_bind, forgetCoinS1_get]; congr 1; funext s
    cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, forgetCoinS1_bind, forgetCoinS1_lift,
        forgetCoinW_liftM, forgetCoinS1_pure]
    congr 1; funext rc; rw [hrecv]; congr 1; funext out
    cases out with
    | none => exact forgetCoinS1_pure _
    | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · exact forgetCoinS1_liftStateT _

theorem forgetCoinS1_simulateQ {Coins ι σ : Type} {ospec : OracleSpec ι}
    (impl₁ : QueryImpl ospec (StateT σ (WriterT (List Coins) ProbComp)))
    (impl₂ : QueryImpl ospec (StateT σ ProbComp))
    (himpl : ∀ t, forgetCoinS1 (impl₁ t) = impl₂ t) {α : Type} (oa : OracleComp ospec α) :
    forgetCoinS1 (simulateQ impl₁ oa) = simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, forgetCoinS1_bind, himpl t,
      simulateQ_bind, simulateQ_spec_query]
    exact congrArg (impl₂ t >>= ·) (funext ih)

/-- Forgetting the send-coin log of `gameRCoinLogged` equals `SM.gameR`. -/
theorem fst_gameRCoinLogged {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    Prod.fst <$> gameRCoinLogged sm Δ qep cfg A = gameR sm Δ qep cfg A := by
  change forgetCoinW (do
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let k ← liftM ($ᵗ Key : ProbComp Key)
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (GameState St Msg C) (WriterT (List Coins) ProbComp)) +
      oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg
    let (b', s) ← (simulateQ impl A).run ((smSchemeCoinLogged sm).initState k b)
    return (b == b' || s.win)) = gameR sm Δ qep cfg A
  unfold gameR runR; simp only [forgetCoinW_bind, forgetCoinW_liftM, bind_assoc]
  congr 1; funext b; congr 1; funext k
  have himpl : ∀ t : (unifSpec + spec St Msg Coins C).Domain,
      forgetCoinS1
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (GameState St Msg C) (WriterT (List Coins) ProbComp)) +
          oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg) t) =
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState St Msg C) ProbComp) +
          oracleImplR sm Δ qep cfg) t) := by
    rintro (u | q)
    · ext gs
      change forgetCoinW ((StateT.lift (liftM (QueryImpl.ofLift unifSpec ProbComp u) :
        WriterT (List Coins) ProbComp _)).run gs) =
        (StateT.lift (QueryImpl.ofLift unifSpec ProbComp u)).run gs
      simp [StateT.run_lift]
    · exact forgetCoinS1_oracleImplRM_smSchemeCoinLogged sm Δ qep cfg q
  rw [← forgetCoinS1_run, forgetCoinS1_simulateQ _ _ himpl A, smSchemeCoinLogged_initState]; simp

theorem fst_bind_gameRCoinLogged {α Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (oa : ProbComp α) (sm : α → SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : α → Adversary St Msg Coins C) :
    Prod.fst <$> (oa >>= fun o => gameRCoinLogged (sm o) Δ qep cfg (A o)) =
      (oa >>= fun o => gameR (sm o) Δ qep cfg (A o)) := by
  rw [map_eq_bind_pure_comp, bind_assoc]; congr 1; funext o
  rw [← map_eq_bind_pure_comp, fst_gameRCoinLogged]

theorem evalDist_fst_gameRCoinLogged {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    𝒟[Prod.fst <$> gameRCoinLogged sm Δ qep cfg A] = 𝒟[gameR sm Δ qep cfg A] :=
  congrArg evalDist (fst_gameRCoinLogged sm Δ qep cfg A)

theorem evalDist_fst_bind_gameRCoinLogged {α Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (oa : ProbComp α) (sm : α → SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : α → Adversary St Msg Coins C) :
    𝒟[Prod.fst <$> (oa >>= fun o => gameRCoinLogged (sm o) Δ qep cfg (A o))] =
      𝒟[oa >>= fun o => gameR (sm o) Δ qep cfg (A o)] :=
  congrArg evalDist (fst_bind_gameRCoinLogged oa sm Δ qep cfg A)

/-- Forgetting the send-coin log of `gameRCoinLogged` preserves `evalDist` (`GameRCoinLoggedFaithful`). -/
theorem gameRCoinLogged_faithful : GameRCoinLoggedFaithful :=
  fun sm Δ qep cfg A => evalDist_fst_gameRCoinLogged sm Δ qep cfg A

/-! ## `KemFailBad` over 64-byte send tapes -/

theorem tapePairFails_coinBytes_eq (K : MlKem) (r₁ r₂ : BitVec 512) :
    K.tapePairFails (coinBytes r₁) (coinBytes r₂) =
      K.honestExchangeFails ⟨coinBytes r₁, coinBytes_length r₁⟩
        ⟨(coinBytes r₂).take 32, by simp [coinBytes_length r₂]⟩ := by
  unfold MlKem.tapePairFails; simp [coinBytes_length r₁, coinBytes_length r₂]

theorem kemFailBad_eq_true_iff (K : MlKem) (tapes : List (List (BitVec 8))) :
    K.KemFailBad tapes = true ↔ ∃ t₁ ∈ tapes, ∃ t₂ ∈ tapes, K.tapePairFails t₁ t₂ = true := by
  simp [MlKem.KemFailBad, List.any_eq_true]

theorem kemFailBad_map_coinBytes_eq_true_iff (K : MlKem) (log : List (BitVec 512)) :
    K.KemFailBad (log.map coinBytes) = true ↔
      ∃ r₁ ∈ log, ∃ r₂ ∈ log, K.honestExchangeFails ⟨coinBytes r₁, coinBytes_length r₁⟩
        ⟨(coinBytes r₂).take 32, by simp [coinBytes_length r₂]⟩ = true := by
  simp [kemFailBad_eq_true_iff, tapePairFails_coinBytes_eq]

theorem kemFailBad_map_coinBytes_eq_false_iff (K : MlKem) (log : List (BitVec 512)) :
    K.KemFailBad (log.map coinBytes) = false ↔
      ∀ r₁ ∈ log, ∀ r₂ ∈ log, K.honestExchangeFails ⟨coinBytes r₁, coinBytes_length r₁⟩
        ⟨(coinBytes r₂).take 32, by simp [coinBytes_length r₂]⟩ = false := by
  simp [MlKem.KemFailBad, List.any_eq_false, tapePairFails_coinBytes_eq]

theorem kemFailBad_mono_subset (K : MlKem) {l₁ l₂ : List (List (BitVec 8))}
    (hsub : l₁ ⊆ l₂) (h : K.KemFailBad l₁ = true) : K.KemFailBad l₂ = true := by
  rw [kemFailBad_eq_true_iff] at h ⊢; rcases h with ⟨t₁, ht₁, t₂, ht₂, hfail⟩
  exact ⟨t₁, hsub ht₁, t₂, hsub ht₂, hfail⟩

theorem kemFailBad_eq_false_of_subset (K : MlKem) {l₁ l₂ : List (List (BitVec 8))}
    (hsub : l₁ ⊆ l₂) (h : K.KemFailBad l₂ = false) : K.KemFailBad l₁ = false := by
  cases h₁ : K.KemFailBad l₁
  · rfl
  · rw [kemFailBad_mono_subset K hsub h₁] at h; cases h

theorem kemFailBad_map_coinBytes_mono_subset (K : MlKem) {w₁ w₂ : List (BitVec 512)}
    (hsub : w₁ ⊆ w₂) (h : K.KemFailBad (w₁.map coinBytes) = true) :
    K.KemFailBad (w₂.map coinBytes) = true :=
  kemFailBad_mono_subset K (List.map_subset coinBytes hsub) h

abbrev kemFailBadLog (K : MlKem) (w : List (BitVec 512)) : Bool :=
  K.KemFailBad (w.map coinBytes)

/-- A predicate on coin logs is prefix-closed when extending a bad log never makes it good again. -/
def PrefixClosed {Coins : Type} (good : List Coins → Prop) : Prop :=
  ∀ w₁ w₂, good (w₁ ++ w₂) → good w₁

theorem prefixClosed_kemFailBad_false (K : MlKem) :
    PrefixClosed (fun w : List (BitVec 512) => K.KemFailBad (w.map coinBytes) = false) := by
  intro w₁ w₂ h; rw [List.map_append] at h
  exact kemFailBad_eq_false_of_subset K (List.subset_append_left _ _) h

/-! ## Prefix-closed online identical-until-bad -/

def embedCoinW {Coins α : Type} (m : WriterT (List Coins) ProbComp α) :
    StateT (List Coins) ProbComp α :=
  fun pre => (fun zw => (zw.1, pre ++ zw.2)) <$> m.run

@[simp] theorem embedCoinW_run {Coins α : Type}
    (m : WriterT (List Coins) ProbComp α) (pre : List Coins) :
    (embedCoinW m).run pre = (fun zw => (zw.1, pre ++ zw.2)) <$> m.run := rfl

@[simp] theorem embedCoinW_run_nil {Coins α : Type} (m : WriterT (List Coins) ProbComp α) :
    (embedCoinW m).run [] = m.run := by simp

@[simp] theorem embedCoinW_pure {Coins α : Type} (a : α) :
    embedCoinW (pure a : WriterT (List Coins) ProbComp α) = pure a := by ext pre; simp

@[simp] theorem embedCoinW_map {Coins α β : Type} (f : α → β)
    (m : WriterT (List Coins) ProbComp α) :
    embedCoinW (f <$> m) = f <$> embedCoinW m := by ext pre; simp [Functor.map_map]

@[simp] theorem embedCoinW_liftM {Coins α : Type} (c : ProbComp α) :
    embedCoinW (liftM c : WriterT (List Coins) ProbComp α) = liftM c := by
  ext pre
  change (fun zw => (zw.1, pre ++ zw.2)) <$> (liftM c : WriterT (List Coins) ProbComp α).run =
    (StateT.lift c).run pre
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [map_eq_bind_pure_comp]

@[simp] theorem embedCoinW_bind {Coins α β : Type}
    (m : WriterT (List Coins) ProbComp α) (k : α → WriterT (List Coins) ProbComp β) :
    embedCoinW (m >>= k) = embedCoinW m >>= fun a => embedCoinW (k a) := by
  ext pre
  simp only [embedCoinW_run, WriterT.run_bind, StateT.run_bind, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind, List.append_assoc]; rfl

@[simp] theorem embedCoinW_smSchemeCoinLogged_send {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (m : Msg) (r : Coins) :
    embedCoinW ((smSchemeCoinLogged sm).send st m r) =
      (fun pre => pure (sm.send st m r, pre ++ [r])) := by
  ext pre; change _ = pure (sm.send st m r, pre ++ [r]); simp

@[simp] theorem embedCoinW_smSchemeCoinLogged_receive {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (c : C) (rc : RCoins) :
    embedCoinW ((smSchemeCoinLogged sm).receive st c rc) = pure (sm.receive st c rc) := by
  ext pre; simp

def embedCoinS1 {Coins σ α : Type} (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    StateT σ (StateT (List Coins) ProbComp) α :=
  fun s => embedCoinW (m.run s)

@[simp] theorem embedCoinS1_run {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) (s : σ) :
    (embedCoinS1 m).run s = embedCoinW (m.run s) := rfl

@[simp] theorem embedCoinS1_pure {Coins σ α : Type} (a : α) :
    embedCoinS1 (pure a : StateT σ (WriterT (List Coins) ProbComp) α) = pure a := by ext s pre; simp

@[simp] theorem embedCoinS1_map {Coins σ α β : Type} (f : α → β)
    (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    embedCoinS1 (f <$> m) = f <$> embedCoinS1 m := by ext s pre; simp

@[simp] theorem embedCoinS1_bind {Coins σ α β : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α)
    (k : α → StateT σ (WriterT (List Coins) ProbComp) β) :
    embedCoinS1 (m >>= k) = embedCoinS1 m >>= fun a => embedCoinS1 (k a) := by ext s pre; simp

@[simp] theorem embedCoinS1_get {Coins σ : Type} :
    embedCoinS1 (get : StateT σ (WriterT (List Coins) ProbComp) σ) = get := by ext s pre; simp

@[simp] theorem embedCoinS1_set {Coins σ : Type} (s' : σ) :
    embedCoinS1 (set s' : StateT σ (WriterT (List Coins) ProbComp) PUnit) = set s' := by
  ext s pre; simp

@[simp] theorem embedCoinS1_lift {Coins σ α : Type} (m : WriterT (List Coins) ProbComp α) :
    embedCoinS1 (StateT.lift m : StateT σ (WriterT (List Coins) ProbComp) α) =
      StateT.lift (embedCoinW m) := by ext s pre; simp [StateT.run_lift]

@[simp] theorem embedCoinS1_liftStateT {Coins σ α : Type} (x : StateT σ ProbComp α) :
    embedCoinS1 (liftStateT (n := WriterT (List Coins) ProbComp) x) =
      liftStateT (n := StateT (List Coins) ProbComp) x := by
  ext s pre; exact congrFun (congrArg StateT.run (embedCoinW_liftM (x s))) pre

theorem embedCoinS1_simulateQ {Coins ι σ : Type} {ospec : OracleSpec ι}
    (impl₁ : QueryImpl ospec (StateT σ (WriterT (List Coins) ProbComp)))
    (impl₂ : QueryImpl ospec (StateT σ (StateT (List Coins) ProbComp)))
    (himpl : ∀ t, embedCoinS1 (impl₁ t) = impl₂ t) {α : Type} (oa : OracleComp ospec α) :
    embedCoinS1 (simulateQ impl₁ oa) = simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, embedCoinS1_bind, himpl t,
      simulateQ_bind, simulateQ_spec_query]
    exact congrArg (impl₂ t >>= ·) (funext ih)

/-- Once the coin log fails `good`, every output state of `m` stays outside `good`. -/
def PreservesBad {Coins α : Type} (good : List Coins → Prop)
    (m : StateT (List Coins) ProbComp α) : Prop :=
  ∀ log, ¬ good log → ∀ z ∈ support (m.run log), ¬ good z.2

theorem PreservesBad.pure {Coins α : Type} (good : List Coins → Prop) (a : α) :
    PreservesBad good (pure a : StateT (List Coins) ProbComp α) := by
  intro log hbad z hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact hbad

theorem PreservesBad.liftM {Coins α : Type} (good : List Coins → Prop) (c : ProbComp α) :
    PreservesBad good (liftM c : StateT (List Coins) ProbComp α) := by
  intro log hbad z hz
  change z ∈ support ((StateT.lift c).run log) at hz
  simp only [StateT.run_lift, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hz
  rcases hz with ⟨_, _, rfl⟩; exact hbad

theorem PreservesBad.append {Coins α : Type} {good : List Coins → Prop}
    (hpref : PrefixClosed good) (f : List Coins → α × List Coins)
    (hf : ∀ log, ∃ sfx, (f log).2 = log ++ sfx) :
    PreservesBad good (fun log => Pure.pure (f log)) := by
  intro log hbad z hz
  change z ∈ support (Pure.pure (f log)) at hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz; rcases hf log with ⟨sfx, heq⟩
  exact fun hg => hbad (hpref log sfx (heq ▸ hg))

theorem PreservesBad.embedCoinW {Coins α : Type} {good : List Coins → Prop}
    (hpref : PrefixClosed good) (m : WriterT (List Coins) ProbComp α) :
    PreservesBad good (embedCoinW m) := by
  intro log hbad z hz
  rw [embedCoinW_run, support_map, Set.mem_image] at hz
  rcases hz with ⟨zw, _, rfl⟩
  exact fun hg => hbad (hpref log zw.2 hg)

theorem PreservesBad.bind {Coins α β : Type} {good : List Coins → Prop}
    {m : StateT (List Coins) ProbComp α} {k : α → StateT (List Coins) ProbComp β}
    (hm : PreservesBad good m) (hk : ∀ a, PreservesBad good (k a)) :
    PreservesBad good (m >>= k) := by
  intro log hbad z hz
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
  rcases hz with ⟨x, hx, hz⟩; exact hk x.1 x.2 (hm log hbad x hx) z hz

/-- Online prefix-aware identical-until-bad agreement on `StateT (List Coins) ProbComp`. -/
structure AgreeOnline {Coins α : Type} (good : List Coins → Prop)
    (m₁ m₂ : StateT (List Coins) ProbComp α) : Prop where
  pres₁ : PreservesBad good m₁
  pres₂ : PreservesBad good m₂
  agree : ∀ log, good log → ∀ p : α × List Coins → Prop,
    Pr{let z ← m₁.run log}[p z ∧ good z.2] = Pr{let z ← m₂.run log}[p z ∧ good z.2]

theorem AgreeOnline.refl {Coins α : Type} {good : List Coins → Prop}
    {m : StateT (List Coins) ProbComp α} (hm : PreservesBad good m) : AgreeOnline good m m :=
  ⟨hm, hm, fun _ _ _ => rfl⟩

theorem AgreeOnline.pure {Coins α : Type} (good : List Coins → Prop) (a : α) :
    AgreeOnline good (pure a : StateT (List Coins) ProbComp α) (pure a) :=
  AgreeOnline.refl (PreservesBad.pure good a)

theorem AgreeOnline.liftM {Coins α : Type} (good : List Coins → Prop) (c : ProbComp α) :
    AgreeOnline good (liftM c : StateT (List Coins) ProbComp α) (liftM c) :=
  AgreeOnline.refl (PreservesBad.liftM good c)

theorem AgreeOnline.bind {Coins α β : Type} {good : List Coins → Prop}
    {m₁ m₂ : StateT (List Coins) ProbComp α} {k₁ k₂ : α → StateT (List Coins) ProbComp β}
    (hm : AgreeOnline good m₁ m₂) (hk : ∀ a, AgreeOnline good (k₁ a) (k₂ a)) :
    AgreeOnline good (m₁ >>= k₁) (m₂ >>= k₂) where
  pres₁ := PreservesBad.bind hm.pres₁ fun a => (hk a).pres₁
  pres₂ := PreservesBad.bind hm.pres₂ fun a => (hk a).pres₂
  agree log hlog p := by
    simp only [StateT.run_bind]
    let : MeasurableSpace (α × List Coins) := ⊤
    let G : Set (α × List Coins) := {x | good x.2}
    let F (k : α → StateT (List Coins) ProbComp β) (x : α × List Coins) : ℝ≥0∞ :=
      Pr{let z ← (k x.1).run x.2}[p z ∧ good z.2]
    have hF_ind₁ (x : α × List Coins) : F k₁ x = G.indicator (F k₁) x := by
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨_, hg⟩ =>
          (hk x.1).pres₁ x.2 hx z hz hg
    have hF_ind₂ (x : α × List Coins) : F k₂ x = G.indicator (F k₂) x := by
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨_, hg⟩ =>
          (hk x.1).pres₂ x.2 hx z hz hg
    have hF_eq_G (x : α × List Coins) : G.indicator (F k₁) x = G.indicator (F k₂) x := by
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact (hk x.1).agree x.2 hx p
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    have hrestrict : 𝒟[m₁.run log].restrict G = 𝒟[m₂.run log].restrict G := by
      refine Measure.ext fun A hA => ?_
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
      change 𝒟[m₁.run log] {z | z ∈ A ∧ good z.2} = 𝒟[m₂.run log] {z | z ∈ A ∧ good z.2}
      rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
      exact hm.agree log hlog (· ∈ A)
    rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
    change ∫⁻ x, F k₁ x ∂𝒟[m₁.run log] = ∫⁻ x, F k₂ x ∂𝒟[m₂.run log]
    calc ∫⁻ x, F k₁ x ∂𝒟[m₁.run log]
        = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[m₁.run log] :=
            lintegral_congr fun x => by rw [hF_ind₁ x, hF_eq_G x]
      _ = ∫⁻ x, F k₂ x ∂(𝒟[m₁.run log].restrict G) := lintegral_indicator MeasurableSet.of_discrete _
      _ = ∫⁻ x, F k₂ x ∂(𝒟[m₂.run log].restrict G) := by rw [hrestrict]
      _ = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[m₂.run log] :=
            (lintegral_indicator MeasurableSet.of_discrete _).symm
      _ = ∫⁻ x, F k₂ x ∂𝒟[m₂.run log] := lintegral_congr fun x => (hF_ind₂ x).symm

def AgreeOnlineS1 {Coins σ α : Type} (good : List Coins → Prop)
    (m₁ m₂ : StateT σ (StateT (List Coins) ProbComp) α) : Prop :=
  ∀ s, AgreeOnline good (m₁.run s) (m₂.run s)

theorem AgreeOnlineS1.pure {Coins σ α : Type} (good : List Coins → Prop) (a : α) :
    AgreeOnlineS1 good (pure a : StateT σ (StateT (List Coins) ProbComp) α) (pure a) :=
  fun s => AgreeOnline.pure good (a, s)

theorem AgreeOnlineS1.get {Coins σ : Type} (good : List Coins → Prop) :
    AgreeOnlineS1 good (get : StateT σ (StateT (List Coins) ProbComp) σ) get :=
  fun s => AgreeOnline.pure good (s, s)

theorem AgreeOnlineS1.set {Coins σ : Type} (good : List Coins → Prop) (s' : σ) :
    AgreeOnlineS1 good (set s' : StateT σ (StateT (List Coins) ProbComp) PUnit) (set s') :=
  fun _ => AgreeOnline.pure good ((), s')

theorem AgreeOnlineS1.lift {Coins σ α : Type} {good : List Coins → Prop}
    {m₁ m₂ : StateT (List Coins) ProbComp α} (hm : AgreeOnline good m₁ m₂) :
    AgreeOnlineS1 good (StateT.lift m₁ : StateT σ (StateT (List Coins) ProbComp) α)
      (StateT.lift m₂ : StateT σ (StateT (List Coins) ProbComp) α) :=
  fun s => by simp only [StateT.run_lift]; exact AgreeOnline.bind hm fun a => AgreeOnline.pure good (a, s)

theorem AgreeOnlineS1.bind {Coins σ α β : Type} {good : List Coins → Prop}
    {m₁ m₂ : StateT σ (StateT (List Coins) ProbComp) α}
    {k₁ k₂ : α → StateT σ (StateT (List Coins) ProbComp) β}
    (hm : AgreeOnlineS1 good m₁ m₂) (hk : ∀ a, AgreeOnlineS1 good (k₁ a) (k₂ a)) :
    AgreeOnlineS1 good (m₁ >>= k₁) (m₂ >>= k₂) :=
  fun s => by simp only [StateT.run_bind]; exact AgreeOnline.bind (hm s) fun x => hk x.1 x.2

theorem AgreeOnlineS1.simulateQ {Coins ι σ : Type} {ospec : OracleSpec ι} {good : List Coins → Prop}
    (impl₁ impl₂ : QueryImpl ospec (StateT σ (StateT (List Coins) ProbComp)))
    (himpl : ∀ t, AgreeOnlineS1 good (impl₁ t) (impl₂ t)) {α : Type} (oa : OracleComp ospec α) :
    AgreeOnlineS1 good (simulateQ impl₁ oa) (simulateQ impl₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact AgreeOnlineS1.pure good a
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact AgreeOnlineS1.bind (himpl t) ih

def smSchemeCoinState {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM (StateT (List Coins) ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := fun log => pure (sm.send st m r, log ++ [r])
  receive st c rc := pure (sm.receive st c rc)

/-- Online-halted `transmit` oracle returning `none` once `badLog (log ++ [coins]) = true`. -/
def transmitRHalted {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let isBad ← StateT.lift (fun log => let log' := log ++ [coins]; pure (badLog log', log'))
      if isBad then return none
      else
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        return some out.2

/-- Online-halted `chall` oracle returning `none` once `badLog (log ++ [coins]) = true`. -/
def challRHalted {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (Coins × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let isBad ← StateT.lift (fun log => let log' := log ++ [coins]; pure (badLog log', log'))
      if isBad then return none
      else
        let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        return some out.2

def oracleImplRHalted {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (spec St Msg Coins C)
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) :=
  transmitRHalted badLog sm Δ qep cfg + challRHalted badLog sm Δ qep cfg +
    deliverRM (smSchemeCoinState sm) cfg + injectRM (smSchemeCoinState sm) Δ qep cfg +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)))

/-- Online-halted `SM.gameR` answering `none` on sends that trigger `badLog`. -/
def gameRCoinHalted {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (badLog : List Coins → Bool) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg Coins C) :
    ProbComp (Bool × List Coins) :=
  (StateT.run · []) do
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let k ← liftM ($ᵗ Key : ProbComp Key)
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
      oracleImplRHalted badLog sm Δ qep cfg
    let (b', s) ← (simulateQ impl A).run (initState sm.sendPart k b)
    return (b == b' || s.win)

private theorem embedCoinS1_oracleImplRM_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (spec St Msg Coins C).Domain) :
    embedCoinS1 (oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg q) =
      oracleImplRM (smSchemeCoinState sm) Δ qep cfg q := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change embedCoinS1 (transmitRM (smSchemeCoinLogged sm) Δ qep cfg (P, m, r)) =
      transmitRM (smSchemeCoinState sm) Δ qep cfg (P, m, r)
    unfold transmitRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact embedCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind,
        embedCoinS1_lift, embedCoinW_liftM, embedCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact embedCoinS1_pure _
      | some s₁ => simp [smSchemeCoinState]
  · change embedCoinS1 (challRM (smSchemeCoinLogged sm) Δ qep cfg (P, m₀, m₁, r)) =
      challRM (smSchemeCoinState sm) Δ qep cfg (P, m₀, m₁, r)
    unfold challRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact embedCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind,
        embedCoinS1_lift, embedCoinW_liftM, embedCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact embedCoinS1_pure _
      | some s₁ =>
        dsimp only
        cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;>
          simp [smSchemeCoinState]
  · change embedCoinS1 (deliverRM (smSchemeCoinLogged sm) cfg (P, c)) =
      deliverRM (smSchemeCoinState sm) cfg (P, c)
    unfold deliverRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_pure]
    cases s.inTransit P.other c with
    | none => exact embedCoinS1_pure _
    | some r =>
      dsimp only
      simp only [embedCoinS1_bind, embedCoinS1_lift, embedCoinW_liftM,
        embedCoinW_smSchemeCoinLogged_receive, smSchemeCoinState]
      congr 1; funext rc; congr 1; funext out
      cases out with
      | none => split_ifs <;> simp
      | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · change embedCoinS1 (injectRM (smSchemeCoinLogged sm) Δ qep cfg (P, c)) =
      injectRM (smSchemeCoinState sm) Δ qep cfg (P, c)
    unfold injectRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind, embedCoinS1_lift,
        embedCoinW_liftM, embedCoinW_smSchemeCoinLogged_receive, embedCoinS1_pure, smSchemeCoinState]
    congr 1; funext rc; congr 1; funext out
    cases out with
    | none => exact embedCoinS1_pure _
    | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · exact embedCoinS1_liftStateT _

private theorem gameRCoinLogged_eq_state {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    gameRCoinLogged sm Δ qep cfg A =
      (StateT.run · []) do
        let b ← liftM ($ᵗ Bool : ProbComp Bool); let k ← liftM ($ᵗ Key : ProbComp Key)
        let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
          oracleImplRM (smSchemeCoinState sm) Δ qep cfg
        let (b', s) ← (simulateQ impl A).run (initState sm.sendPart k b)
        return (b == b' || s.win) := by
  unfold gameRCoinLogged; rw [← embedCoinW_run_nil]; congr 1
  simp only [embedCoinW_bind, embedCoinW_liftM, smSchemeCoinLogged_initState]
  congr 1; funext b; congr 1; funext k
  have himpl : ∀ t : (unifSpec + spec St Msg Coins C).Domain,
      embedCoinS1 (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState St Msg C) (WriterT (List Coins) ProbComp)) +
        oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg) t) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
        oracleImplRM (smSchemeCoinState sm) Δ qep cfg) t) := by
    rintro (u | q)
    · change embedCoinS1 (StateT.lift (liftM (QueryImpl.ofLift unifSpec ProbComp u))) =
        StateT.lift (liftM (QueryImpl.ofLift unifSpec ProbComp u))
      rw [embedCoinS1_lift, embedCoinW_liftM]
    · exact embedCoinS1_oracleImplRM_eq sm Δ qep cfg q
  rw [← embedCoinS1_run, embedCoinS1_simulateQ _ _ himpl A]; ext pre; simp

private theorem agreeOnline_oracleImplRM {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    {good : List Coins → Prop}
    (sm₁ sm₂ : SMSchemeRM (StateT (List Coins) ProbComp) Key St Msg Coins RCoins C)
    (hsend : ∀ s m coins, AgreeOnline good (sm₁.send s m coins) (sm₂.send s m coins))
    (hrecv : ∀ s c rc, AgreeOnline good (sm₁.receive s c rc) (sm₂.receive s c rc))
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : (spec St Msg Coins C).Domain) :
    AgreeOnlineS1 good (oracleImplRM sm₁ Δ qep cfg q) (oracleImplRM sm₂ Δ qep cfg q) := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change AgreeOnlineS1 good (transmitRM sm₁ Δ qep cfg (P, m, r)) (transmitRM sm₂ Δ qep cfg (P, m, r))
    unfold transmitRM; refine AgreeOnlineS1.bind (AgreeOnlineS1.get good) fun s => ?_
    cases cfg.sendOK s P
    · exact AgreeOnlineS1.pure good _
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; cases s.win
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine AgreeOnlineS1.bind (AgreeOnlineS1.lift (AgreeOnline.liftM good _)) fun ⟨coins, bf⟩ => ?_
        cases s.epMgmt Δ qep P bf with
        | none => exact AgreeOnlineS1.pure good _
        | some s₁ => exact AgreeOnlineS1.bind (AgreeOnlineS1.lift (hsend _ _ _)) fun out =>
            AgreeOnlineS1.bind (AgreeOnlineS1.set good _) fun _ => AgreeOnlineS1.pure good _
      · exact AgreeOnlineS1.pure good _
  · change AgreeOnlineS1 good (challRM sm₁ Δ qep cfg (P, m₀, m₁, r)) (challRM sm₂ Δ qep cfg (P, m₀, m₁, r))
    unfold challRM; refine AgreeOnlineS1.bind (AgreeOnlineS1.get good) fun s => ?_
    cases cfg.sendOK s P
    · exact AgreeOnlineS1.pure good _
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; cases s.win
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine AgreeOnlineS1.bind (AgreeOnlineS1.lift (AgreeOnline.liftM good _)) fun ⟨coins, bf⟩ => ?_
        cases s.epMgmt Δ qep P bf with
        | none => exact AgreeOnlineS1.pure good _
        | some s₁ =>
          dsimp only; cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact AgreeOnlineS1.bind (AgreeOnlineS1.lift (hsend _ _ _)) fun out =>
              AgreeOnlineS1.bind (AgreeOnlineS1.set good _) fun _ => AgreeOnlineS1.pure good _
          · exact AgreeOnlineS1.pure good _
      · exact AgreeOnlineS1.pure good _
  · change AgreeOnlineS1 good (deliverRM sm₁ cfg (P, c)) (deliverRM sm₂ cfg (P, c))
    unfold deliverRM; refine AgreeOnlineS1.bind (AgreeOnlineS1.get good) fun s => ?_
    cases s.win
    · simp only [Bool.false_eq_true, ↓reduceIte]; cases s.inTransit P.other c with
      | none => exact AgreeOnlineS1.pure good _
      | some r =>
        dsimp only; refine AgreeOnlineS1.bind (AgreeOnlineS1.lift (AgreeOnline.liftM good _)) fun rc =>
          AgreeOnlineS1.bind (AgreeOnlineS1.lift (hrecv _ _ _)) fun out => ?_
        cases out with
        | none =>
          dsimp only; split_ifs
          · exact AgreeOnlineS1.bind (AgreeOnlineS1.set good _) fun _ => AgreeOnlineS1.pure good _
          · exact AgreeOnlineS1.pure good _
        | some x =>
          rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;>
            exact AgreeOnlineS1.bind (AgreeOnlineS1.set good _) fun _ => AgreeOnlineS1.pure good _
    · exact AgreeOnlineS1.pure good _
  · change AgreeOnlineS1 good (injectRM sm₁ Δ qep cfg (P, c)) (injectRM sm₂ Δ qep cfg (P, c))
    unfold injectRM; refine AgreeOnlineS1.bind (AgreeOnlineS1.get good) fun s => ?_
    cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine AgreeOnlineS1.bind (AgreeOnlineS1.lift (AgreeOnline.liftM good _)) fun rc =>
        AgreeOnlineS1.bind (AgreeOnlineS1.lift (hrecv _ _ _)) fun out => ?_
      cases out with
      | none => exact AgreeOnlineS1.pure good _
      | some x =>
        rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs
        · exact AgreeOnlineS1.pure good _
        · exact AgreeOnlineS1.bind (AgreeOnlineS1.set good _) fun _ => AgreeOnlineS1.pure good _
        · exact AgreeOnlineS1.bind (AgreeOnlineS1.set good _) fun _ => AgreeOnlineS1.pure good _
        · exact AgreeOnlineS1.bind (AgreeOnlineS1.pure good _) fun _ => AgreeOnlineS1.pure good _
    · exact AgreeOnlineS1.pure good _
  · intro gs; exact AgreeOnline.liftM good (corrR cfg P gs)

private theorem agreeOnline_append_of_eq {Coins α : Type} {good : List Coins → Prop}
    (hpref : PrefixClosed good) (r : Coins) (x₁ x₂ : List Coins → α)
    (heq : ∀ log, good (log ++ [r]) → x₁ (log ++ [r]) = x₂ (log ++ [r])) :
    AgreeOnline good (fun log => pure (x₁ (log ++ [r]), log ++ [r]))
      (fun log => pure (x₂ (log ++ [r]), log ++ [r])) := by
  refine ⟨PreservesBad.append hpref _ (fun log => ⟨[r], rfl⟩),
    PreservesBad.append hpref _ (fun log => ⟨[r], rfl⟩), fun log _ q => ?_⟩
  let log' := log ++ [r]
  have hgoal : Pr{let z ← (pure (x₁ log', log') : ProbComp (α × List Coins))}[q z ∧ good z.2] =
      Pr{let z ← (pure (x₂ log', log') : ProbComp (α × List Coins))}[q z ∧ good z.2] := by
    by_cases hg : good log'
    · rw [heq log hg]
    · have hzero (x : α) : Pr{let z ← (pure (x, log') : ProbComp (α × List Coins))}[q z ∧ good z.2] = 0 :=
        prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨_, hz2⟩ => by
          rw [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hg hz2
      rw [hzero, hzero]
  exact hgoal

private theorem agreeOnlineS1_send_halted {Key St Msg Coins RCoins C : Type}
    {badLog : List Coins → Bool} (hpref : PrefixClosed (fun w => badLog w = false))
    (sm : SMSchemeR Key St Msg Coins RCoins C)
    (st : St) (msg : Msg) (coins : Coins) (recSt : St × C → GameState St Msg C) :
    AgreeOnlineS1 (fun w => badLog w = false)
      (do
        let out ← StateT.lift ((smSchemeCoinState sm).send st msg coins)
        set (recSt out); return some out.2 :
        StateT (GameState St Msg C) (StateT (List Coins) ProbComp) (Option C))
      (do
        let isBad ← StateT.lift (fun log : List Coins =>
          let log' := log ++ [coins]; pure (badLog log', log'))
        if isBad then return none
        else let out := sm.send st msg coins; set (recSt out); return some out.2 :
        StateT (GameState St Msg C) (StateT (List Coins) ProbComp) (Option C)) := by
  intro gs; let out := sm.send st msg coins
  have h₁ : ((do
      let o ← StateT.lift ((smSchemeCoinState sm).send st msg coins)
      set (recSt o); return some o.2 :
      StateT (GameState St Msg C) (StateT (List Coins) ProbComp) (Option C)).run gs) =
    (fun log => pure ((some out.2, recSt out), log ++ [coins])) := by
    ext log
    simp only [smSchemeCoinState, StateT.run_bind, StateT.run_lift, StateT.run_map,
      StateT.run_set, bind_pure_comp, map_pure]
    rfl
  let chk : StateT (List Coins) ProbComp Bool :=
    fun l => let log' := l ++ [coins]; pure (badLog log', log')
  have h₂ : ((do
      let isBad ← StateT.lift chk
      if isBad then return none
      else let o := sm.send st msg coins; set (recSt o); return some o.2 :
      StateT (GameState St Msg C) (StateT (List Coins) ProbComp) (Option C)).run gs) =
    (fun log =>
      let log' := log ++ [coins]
      pure (if badLog log' then (none, gs) else (some out.2, recSt out), log')) := by
    ext log
    have hchk : chk.run log = pure (badLog (log ++ [coins]), log ++ [coins]) := rfl
    change _ = pure (if badLog (log ++ [coins]) then (none, gs) else (some out.2, recSt out),
      log ++ [coins])
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_map, hchk, bind_pure_comp, map_pure,
      pure_bind]
    cases badLog (log ++ [coins]) <;>
      simp only [↓reduceIte, Bool.false_eq_true, StateT.run_pure, StateT.run_set, StateT.run_map,
        map_pure]; rfl
  rw [h₁]; exact Eq.subst (motive := fun x => AgreeOnline _ _ x) (Eq.symm h₂)
    (agreeOnline_append_of_eq hpref coins
      (fun _ => (some out.2, recSt out))
      (fun log' => if badLog log' then (none, gs) else (some out.2, recSt out))
      (fun log hg => by simp [hg]))

/-- `gameRCoinLogged` agrees with `gameRCoinHalted` off `badLog` when `badLog = false` is prefix-closed. -/
theorem gameRCoinLogged_agree_halted {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (badLog : List Coins → Bool) (hnil : badLog [] = false)
    (hpref : PrefixClosed (fun w => badLog w = false)) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg Coins C) (p : Bool × List Coins → Prop) :
    Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[p z ∧ badLog z.2 = false] =
      Pr{let z ← gameRCoinHalted badLog sm Δ qep cfg A}[p z ∧ badLog z.2 = false] := by
  rw [gameRCoinLogged_eq_state]; unfold gameRCoinHalted
  let good : List Coins → Prop := fun w => badLog w = false
  have himpl (t : (unifSpec + spec St Msg Coins C).Domain) :
      AgreeOnlineS1 good (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
        oracleImplRM (smSchemeCoinState sm) Δ qep cfg) t)
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
        oracleImplRHalted badLog sm Δ qep cfg) t) := by
    rcases t with u | (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · exact AgreeOnlineS1.lift (AgreeOnline.liftM good _)
    · change AgreeOnlineS1 good (transmitRM _ Δ qep cfg (P, m, r)) (transmitRHalted _ _ Δ qep cfg (P, m, r))
      unfold transmitRM transmitRHalted; refine AgreeOnlineS1.bind (AgreeOnlineS1.get good) fun s => ?_
      cases cfg.sendOK s P
      · exact AgreeOnlineS1.pure good _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; cases s.win
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine AgreeOnlineS1.bind (AgreeOnlineS1.lift (AgreeOnline.liftM good _)) fun ⟨coins, bf⟩ => ?_
          cases s.epMgmt Δ qep P bf with
          | none => exact AgreeOnlineS1.pure good _
          | some s₁ => exact agreeOnlineS1_send_halted hpref sm (s₁.st P) m coins _
        · exact AgreeOnlineS1.pure good _
    · change AgreeOnlineS1 good (challRM _ Δ qep cfg (P, m₀, m₁, r)) (challRHalted _ _ Δ qep cfg (P, m₀, m₁, r))
      unfold challRM challRHalted; refine AgreeOnlineS1.bind (AgreeOnlineS1.get good) fun s => ?_
      cases cfg.sendOK s P
      · exact AgreeOnlineS1.pure good _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; cases s.win
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine AgreeOnlineS1.bind (AgreeOnlineS1.lift (AgreeOnline.liftM good _)) fun ⟨coins, bf⟩ => ?_
          cases s.epMgmt Δ qep P bf with
          | none => exact AgreeOnlineS1.pure good _
          | some s₁ =>
            dsimp only; cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact agreeOnlineS1_send_halted hpref sm (s₁.st P) _ coins _
            · exact AgreeOnlineS1.pure good _
        · exact AgreeOnlineS1.pure good _
    · exact agreeOnline_oracleImplRM (smSchemeCoinState sm) (smSchemeCoinState sm)
        (fun s m c => AgreeOnline.refl (PreservesBad.append hpref _ (fun log => ⟨[c], rfl⟩)))
        (fun s c rc => AgreeOnline.pure good _) Δ qep cfg (.inl (.inl (.inr (P, c))))
    · exact agreeOnline_oracleImplRM (smSchemeCoinState sm) (smSchemeCoinState sm)
        (fun s m c => AgreeOnline.refl (PreservesBad.append hpref _ (fun log => ⟨[c], rfl⟩)))
        (fun s c rc => AgreeOnline.pure good _) Δ qep cfg (.inl (.inr (P, c)))
    · intro gs; exact AgreeOnline.liftM good (corrR cfg P gs)
  exact (AgreeOnline.bind (AgreeOnline.liftM good _) fun b =>
    AgreeOnline.bind (AgreeOnline.liftM good _) fun k =>
      AgreeOnline.bind (AgreeOnlineS1.simulateQ _ _ himpl A (initState sm.sendPart k b))
        fun ⟨b', s⟩ => AgreeOnline.pure good (b == b' || s.win)).agree [] hnil p

/-- Schemes whose `send` agrees away from `badCoin` induce identical `gameRCoinLogged` distributions off `badCoin`. -/
theorem gameRCoinLogged_agree_of_send {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (sm₁ sm₂ : SMSchemeR Key St Msg Coins RCoins C)
    (hinitA : sm₁.initA = sm₂.initA) (hinitB : sm₁.initB = sm₂.initB)
    (hrecv : sm₁.receive = sm₂.receive) {badCoin : Coins → Prop}
    (hsend : ∀ st m r, ¬ badCoin r → sm₁.send st m r = sm₂.send st m r)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg Coins C)
    (p : Bool × List Coins → Prop) :
    Pr{let z ← gameRCoinLogged sm₁ Δ qep cfg A}[p z ∧ ∀ r ∈ z.2, ¬ badCoin r] =
      Pr{let z ← gameRCoinLogged sm₂ Δ qep cfg A}[p z ∧ ∀ r ∈ z.2, ¬ badCoin r] := by
  rw [gameRCoinLogged_eq_state, gameRCoinLogged_eq_state]
  let good : List Coins → Prop := fun w => ∀ r ∈ w, ¬ badCoin r
  have hpref : PrefixClosed good := fun w₁ w₂ h r hr => h r (List.mem_append_left w₂ hr)
  have hnil : good [] := fun _ hr => nomatch hr
  have hinit : initState sm₁.sendPart = initState sm₂.sendPart := by
    ext k b : 2; unfold initState SMSchemeR.sendPart; congr 1; funext P; cases P <;> simp [hinitA, hinitB]
  rw [hinit]
  have hs : ∀ st m r, AgreeOnline good
      ((smSchemeCoinState sm₁).send st m r) ((smSchemeCoinState sm₂).send st m r) :=
    fun st m r => agreeOnline_append_of_eq hpref r
      (fun _ => sm₁.send st m r) (fun _ => sm₂.send st m r)
      (fun log hg => hsend st m r (hg r (List.mem_append_right log (List.mem_singleton.mpr rfl))))
  have hr_eq : ∀ st c rc, AgreeOnline good
      ((smSchemeCoinState sm₁).receive st c rc) ((smSchemeCoinState sm₂).receive st c rc) := by
    intro st c rc; unfold smSchemeCoinState; rw [hrecv]; exact AgreeOnline.pure good _
  have himpl (t : (unifSpec + spec St Msg Coins C).Domain) :
      AgreeOnlineS1 good
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
          oracleImplRM (smSchemeCoinState sm₁) Δ qep cfg) t)
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
          oracleImplRM (smSchemeCoinState sm₂) Δ qep cfg) t) := by
    rcases t with u | q
    · exact AgreeOnlineS1.lift (AgreeOnline.liftM good _)
    · exact agreeOnline_oracleImplRM _ _ hs hr_eq Δ qep cfg q
  exact (AgreeOnline.bind (AgreeOnline.liftM good _) fun b =>
    AgreeOnline.bind (AgreeOnline.liftM good _) fun k =>
      AgreeOnline.bind (AgreeOnlineS1.simulateQ _ _ himpl A (initState sm₂.sendPart k b))
        fun ⟨b', s⟩ => AgreeOnline.pure good (b == b' || s.win)).agree [] hnil p

/-! ## Boolean distance and bias transfer -/

theorem boolDist_fst_le_prEvent_of_good_le {β : Type}
    (exp : ProbComp (Bool × β)) (exp₀ : ProbComp Bool) (badEv : Bool × β → Prop)
    (hgood : ∀ b : Bool, Pr{let z ← exp}[z.1 = b ∧ ¬ badEv z] ≤ Pr{let b' ← exp₀}[b' = b]) :
    (𝒟[Prod.fst <$> exp]).boolDist (𝒟[exp₀]) ≤ Pr{let z ← exp}[badEv z] := by
  let : MeasurableSpace (Bool × β) := ⊤
  refine Measure.boolDist_le_of_apply_le _ _ fun b => ?_
  have hsing : ({b} : Set Bool) = {x | x = b} := Set.ext fun _ => Set.mem_singleton_iff
  have hfst : (𝒟[Prod.fst <$> exp]) {b} = (𝒟[exp]) {z | z.1 = b} := by
    rw [hsing, ← prEvent_eq_evalDist_of_discrete, prEvent_map, prEvent_eq_evalDist_of_discrete]
  have hrhs : (𝒟[exp₀]) {b} = Pr{let b' ← exp₀}[b' = b] := by
    rw [hsing, ← prEvent_eq_evalDist_of_discrete]
  rw [hfst, hrhs]
  have hsub : {z : Bool × β | z.1 = b} ⊆ {z | z.1 = b ∧ ¬ badEv z} ∪ {z | badEv z} :=
    fun z hz => by by_cases hb : badEv z <;> [exact Or.inr hb; exact Or.inl ⟨hz, hb⟩]
  calc (𝒟[exp]) {z | z.1 = b}
      ≤ (𝒟[exp]) ({z | z.1 = b ∧ ¬ badEv z} ∪ {z | badEv z}) := MeasureTheory.measure_mono hsub
    _ ≤ (𝒟[exp]) {z | z.1 = b ∧ ¬ badEv z} + (𝒟[exp]) {z | badEv z} :=
        MeasureTheory.measure_union_le _ _
    _ = Pr{let z ← exp}[z.1 = b ∧ ¬ badEv z] + Pr{let z ← exp}[badEv z] := by
        rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
    _ ≤ Pr{let b' ← exp₀}[b' = b] + Pr{let z ← exp}[badEv z] := by gcongr; exact hgood b

theorem boolDist_fst_le_prEvent_of_agree {β : Type}
    (exp exp₀ : ProbComp (Bool × β)) (badEv : Bool × β → Prop)
    (hagree : ∀ p : Bool × β → Prop,
      Pr{let z ← exp}[p z ∧ ¬ badEv z] = Pr{let z ← exp₀}[p z ∧ ¬ badEv z]) :
    (𝒟[Prod.fst <$> exp]).boolDist (𝒟[Prod.fst <$> exp₀]) ≤ Pr{let z ← exp}[badEv z] := by
  let : MeasurableSpace (Bool × β) := ⊤
  refine boolDist_fst_le_prEvent_of_good_le exp (Prod.fst <$> exp₀) badEv fun b => ?_
  rw [hagree fun z => z.1 = b, prEvent_map, prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  exact MeasureTheory.measure_mono fun _ h => h.1

theorem boolBias_le_add_two_mul_of_boolDist_le (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (ε : ℝ≥0∞) (h : μ.boolDist ν ≤ ε) :
    μ.boolBias ≤ ν.boolBias + 2 * ε := by
  have hbd : μ.boolDist ν = ENNReal.absDiff (μ {true}) (ν {true}) := Measure.boolDist.eq_1 μ ν
  calc μ.boolBias = 2 * ENNReal.absDiff (μ {true}) (1 / 2) :=
        Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure μ
    _ ≤ 2 * (ENNReal.absDiff (μ {true}) (ν {true}) + ENNReal.absDiff (ν {true}) (1 / 2)) := by
        gcongr; exact ENNReal.absDiff_triangle _ _ _
    _ = 2 * ENNReal.absDiff (ν {true}) (1 / 2) + 2 * μ.boolDist ν := by rw [← hbd]; ring
    _ = ν.boolBias + 2 * μ.boolDist ν := by
        rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν]
    _ ≤ ν.boolBias + 2 * ε := by gcongr

theorem boolBias_gameR_le_add_two_mul_of_good_le {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) (H : ProbComp Bool) (badLog : List Coins → Prop)
    (hgood : ∀ b : Bool,
      Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[z.1 = b ∧ ¬ badLog z.2] ≤ Pr{let b' ← H}[b' = b]) :
    (𝒟[gameR sm Δ qep cfg A]).boolBias ≤
      (𝒟[H]).boolBias + 2 * Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[badLog z.2] := by
  rw [← evalDist_fst_gameRCoinLogged sm Δ qep cfg A]
  exact boolBias_le_add_two_mul_of_boolDist_le _ _ _
    (boolDist_fst_le_prEvent_of_good_le _ H (fun z => badLog z.2) hgood)

theorem boolBias_bind_gameR_le_add_two_mul_of_good_le {α Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (oa : ProbComp α) (sm : α → SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : α → Adversary St Msg Coins C)
    (H : α → ProbComp Bool) (badLog : List Coins → Prop)
    (hgood : ∀ o ∈ support oa, ∀ b : Bool,
      Pr{let z ← gameRCoinLogged (sm o) Δ qep cfg (A o)}[z.1 = b ∧ ¬ badLog z.2] ≤ Pr{let b' ← H o}[b' = b]) :
    (𝒟[oa >>= fun o => gameR (sm o) Δ qep cfg (A o)]).boolBias ≤
      (𝒟[oa >>= H]).boolBias +
        2 * Pr{let z ← oa >>= fun o => gameRCoinLogged (sm o) Δ qep cfg (A o)}[badLog z.2] := by
  rw [← evalDist_fst_bind_gameRCoinLogged oa sm Δ qep cfg A]
  refine boolBias_le_add_two_mul_of_boolDist_le _ _ _ (boolDist_fst_le_prEvent_of_good_le
    (oa >>= fun o => gameRCoinLogged (sm o) Δ qep cfg (A o)) (oa >>= H) (fun z => badLog z.2) fun b => ?_)
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  refine MeasureTheory.lintegral_mono_ae ?_; rw [MeasureTheory.ae_iff]
  have hsub : {o : α | ¬ Pr{let z ← gameRCoinLogged (sm o) Δ qep cfg (A o)}[z.1 = b ∧ ¬ badLog z.2] ≤
      Pr{let b' ← H o}[b' = b]} ⊆ (support oa)ᶜ := fun o ho hmem => ho (hgood o hmem b)
  have hsupp : (𝒟[oa]) (support oa)ᶜ = 0 := by
    change (𝒟[oa]) {o | o ∉ support oa} = 0; rw [← prEvent_eq_evalDist_of_discrete]
    exact prEvent_eq_zero_of_forall_mem_support oa _ fun o ho hnot => hnot ho
  exact MeasureTheory.measure_mono_null hsub hsupp

theorem boolBias_session_le_of_good_le {α : Type}
    (C : Crypto) (K : MlKem) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (H : α → ProbComp Bool)
    (hgood : ∀ o ∈ support oa, ∀ b : Bool,
      Pr{let z ← gameRCoinLogged (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) (ida o) (idb o)) ℓ (s o))
          3 qep (configRefuseEarlyBobCorr decT encT) (A o)}[
            z.1 = b ∧ K.KemFailBad (z.2.map coinBytes) = false] ≤ Pr{let b' ← H o}[b' = b]) :
    (𝒟[oa >>= fun o => gameR (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) (ida o) (idb o)) ℓ (s o))
        3 qep (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= H]).boolBias + 2 * sessionKemFailProb C K ℓ decT encT qep oa ida idb s A := by
  unfold sessionKemFailProb
  refine boolBias_bind_gameR_le_add_two_mul_of_good_le oa _ 3 qep _ A H
    (fun w => K.KemFailBad (w.map coinBytes) = true) fun o ho b => ?_
  simpa only [Bool.not_eq_true] using hgood o ho b

/-- Bounds the `SessionSecure` game bias by `gameRCoinHalted` plus twice `sessionKemFailProb`. -/
theorem boolBias_session_le_halted_add_two_mul_sessionKemFailProb {α : Type}
    (C : Crypto) (K : MlKem) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    let sm := fun o => sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) (ida o) (idb o)) ℓ (s o)
    (𝒟[oa >>= fun o => gameR (sm o) 3 qep (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= fun o =>
          Prod.fst <$> gameRCoinHalted (kemFailBadLog K) (sm o) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias +
        2 * sessionKemFailProb C K ℓ decT encT qep oa ida idb s A := by
  let : MeasurableSpace (Bool × List (BitVec 512)) := ⊤
  refine boolBias_session_le_of_good_le C K ℓ decT encT qep oa ida idb s A _ fun o _ b => ?_
  rw [gameRCoinLogged_agree_halted (kemFailBadLog K) rfl
      (prefixClosed_kemFailBad_false K) _ 3 qep _ (A o) (fun z => z.1 = b),
    prEvent_map, prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
  exact MeasureTheory.measure_mono fun _ h => h.1

theorem sessionKemFailProb_eq_lintegral {α : Type}
    (C : Crypto) (K : MlKem) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    letI : MeasurableSpace α := ⊤
    let g := fun o => gameRCoinLogged
      (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) (ida o) (idb o)) ℓ (s o))
      3 qep (configRefuseEarlyBobCorr decT encT) (A o)
    sessionKemFailProb C K ℓ decT encT qep oa ida idb s A =
      ∫⁻ o, Pr{let z ← g o}[K.KemFailBad (z.2.map coinBytes) = true] ∂𝒟[oa] := by
  let : MeasurableSpace α := ⊤
  unfold sessionKemFailProb
  exact prEvent_bind_eq_lintegral_of_discrete oa _ _

end Computational.Proofs.SpecLemmas.Session.GameRCoinLogged
