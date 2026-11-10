/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedCoupling
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure

/-!
# Online Coin-Log to `SessionHaltTracker` Coupling

Proves the per-query identical-until-bad coupling between `oracleLoggedTracked` and
`oracleHaltedLogged` (`oracleLogged_agree_halted`) and lifts it across the multi-session E2E
driver (`cliE2EExpWithKiCoinLogged_good_le_sessionTracked_pr`).
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.MainHaltedOnline

open scoped ENNReal BigOperators
open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (ConfigR GameState corrR deliverR injectR samIfNec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHModelInst BHE2EDrvState BHE2ESmResp Bytes ModelDriverInstanceMeta
  SampledSessionKey allTestedSessionsFresh bhDecodePreKeyMsgE bhDrvKiQueryOk bhE2EDrvInstClean
  bhE2EDrvWon bhE2EFinishStartSpk bhE2EGuard bhE2EInstIkACorr bhE2EMirror bhExpectedPreKeyMsg
  bhHdrOfPreKeyMsg bhInitRegId bhIsBobAcceptSMResp bhIsBobRecvSMQuery bhKeySOf bhNoOpkRespPromoted
  bhPackSmResp bhTargetGameSpec bhUnpackSmResp compositionLocalStart configRefuseEarlyBobCorr
  liftStateT oracleImplRM paramsIdsWithSpqr sessionSchemeFixedSpk shortCiphertext
  smSchemeCoinLogged wirePrekey)
open Computational.Proofs.LibsignalCli.MainHaltedCoupling (AgreeInv CoinLogM PreservesInvBad
  ProjectsToHalted ProjectsToLogged SessionHaltTracker ValidBadLog ValidSessionHaltTracker
  bhDecodeSmWireQuery bhE2EDrvImplWithSessionTracked bhE2EExpWithKiSessionTracked
  bhE2ELocalStartSessionTracked bhE2EStepLocalSmCoinLogged bhE2EStepLocalSmSessionTracked
  challHaltedLogged challLoggedTracked cliE2EDrvImplWithCoinLogged cliE2EExpWithKiCoinLogged
  deliverBothLogged oracleHaltedLogged oracleHaltedLogged_proj oracleImplRSessionTracked
  oracleLoggedTracked oracleLoggedTracked_proj transmitHaltedLogged transmitLoggedTracked)

/-! ## Monad and measure helpers -/

private def liftProb2 {σ Coins α : Type} (c : ProbComp α) :
    StateT σ (StateT (List Coins) ProbComp) α :=
  StateT.lift (StateT.lift c)

private local instance instLawfulMonadWriterTListCoin {Coins : Type} {M : Type → Type}
    [Monad M] [LawfulMonad M] : LawfulMonad (WriterT (List Coins) M) :=
  LawfulMonad.mk' (id_map := fun {_} _ => by ext; simp)
    (pure_bind := fun {_ _} _ _ => by ext; simp)
    (bind_assoc := fun {_ _ _} _ _ _ => by ext; simp)
    (bind_pure_comp := fun {_ _} _ _ => by ext; simp)

private theorem liftProb2_run {σ Coins α : Type} (c : ProbComp α) (s : σ) (gLog : List Coins) :
    ((liftProb2 c).run s).run gLog = (fun a => ((a, s), gLog)) <$> c := by
  dsimp [liftProb2, StateT.lift, StateT.run]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem liftProb2_agreeInv {σ Coins α : Type}
    (good : List Coins → Prop) (Inv : σ → List Coins → Prop) (c : ProbComp α) :
    AgreeInv good Inv (liftProb2 c) (liftProb2 c) :=
  AgreeInv.refl
    { pres_bad := fun s gLog hbad z hz => by
        rw [liftProb2_run, support_map] at hz
        rcases hz with ⟨a, _, rfl⟩; exact hbad
      pres_inv := fun s gLog hinv z hz => by
        rw [liftProb2_run, support_map] at hz
        rcases hz with ⟨a, _, rfl⟩; exact hinv }

@[simp] private theorem liftM_writer_run {Coins α : Type} (c : ProbComp α) :
    (liftM c : WriterT (List Coins) ProbComp α).run = (fun a => (a, [])) <$> c := by
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]

private theorem liftProb2_projLogged {σ τ Coins α : Type} (c : ProbComp α) :
    ProjectsToLogged (σ := σ) (τ := τ) (Coins := Coins)
      (liftProb2 c) (liftM c : StateT σ (WriterT (List Coins) ProbComp) α) := by
  intro s tracks gLog
  rw [liftProb2_run]
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift, StateT.run,
    WriterT.liftTell, WriterT.run]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem liftProb2_projHalted {σH Coins α : Type} (c : ProbComp α) :
    ProjectsToHalted (σH := σH) (Coins := Coins)
      (liftProb2 c) (liftM c : StateT σH ProbComp α) := by
  intro s gLog
  rw [liftProb2_run]
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift, StateT.run]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem prEvent_map_eq {α β : Type} (f : α → β) (c : ProbComp α) (P : β → Prop) :
    Pr{let y ← f <$> c}[P y] = Pr{let x ← c}[P (f x)] := by
  simp only [Functor.map_map]

private theorem prEvent_pure_send_branch_eq {α τ Coins : Type}
    (badGlobal : List Coins → Bool) (gLog : List Coins) (coins : Coins)
    (isBad : Bool) (hGood : badGlobal (gLog ++ [coins]) = false → isBad = false)
    (xGood xHalt : α) (trGood trHalt : τ)
    (p : α × (τ × List Coins) → Prop) :
    Pr{let z ← (Pure.pure (xGood, (trGood, gLog ++ [coins])) : ProbComp _)}[
        p z ∧ badGlobal z.2.2 = false] =
      Pr{let z ← (if isBad then Pure.pure (xHalt, (trHalt, gLog ++ [coins]))
          else Pure.pure (xGood, (trGood, gLog ++ [coins])) : ProbComp _)}[
        p z ∧ badGlobal z.2.2 = false] := by
  by_cases hbg : badGlobal (gLog ++ [coins]) = false
  · simp only [hGood hbg, Bool.false_eq_true, ↓reduceIte]
  · cases isBad
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      rw [prEvent_eq_zero_of_forall_mem_support, prEvent_eq_zero_of_forall_mem_support]
      · intro z hz
        rw [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact fun h => hbg h.2
      · intro z hz
        rw [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact fun h => hbg h.2

/-! ## Single-query session oracle support and agreement -/

private theorem liftStateT_step_support {σ τ Coins α : Type}
    (x : StateT σ ProbComp α) (s : σ) (tr₀ : τ) (gLog : List Coins)
    {z : (α × σ) × (τ × List Coins)}
    (hz : z ∈ support
      (((liftStateT x : StateT σ (StateT (τ × List Coins) ProbComp) α).run s).run (tr₀, gLog))) :
    z.2 = (tr₀, gLog) := by
  dsimp [liftStateT, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
    StateT.lift, StateT.run] at hz
  simp only [support_bind, Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hz
  rcases hz with ⟨_, _, rfl⟩
  rfl

theorem oracleLoggedTracked_step {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    {badGlobal : List Coins → Bool} {T : SessionHaltTracker St Msg Coins C Key τ}
    {TrInv : τ → List Coins → Prop} (hT : ValidSessionHaltTracker badGlobal T TrInv)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (gs : GameState St Msg C) (tr₀ : τ) (gLog : List Coins)
    {z : ((CryptoGames.SM.spec St Msg Coins C).Range q × GameState St Msg C) × (τ × List Coins)}
    (hz : z ∈ support (((oracleLoggedTracked T sm Δ qep cfg q).run gs).run (tr₀, gLog))) :
    (z.2.2 = gLog ∨ ∃ c, z.2.2 = gLog ++ [c]) ∧ (TrInv tr₀ gLog → TrInv z.2.1 z.2.2) := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change z ∈ support (((transmitLoggedTracked T sm Δ qep cfg (P, m, r)).run gs).run (tr₀, gLog)) at hz
    unfold transmitLoggedTracked at hz
    dsimp only at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hok : cfg.sendOK gs P
    · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact ⟨.inl rfl, id⟩
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
      cases hwin : gs.win
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift] at hz
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift] at hz
        simp only [bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
        rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨.inl rfl, id⟩
        | some s₁ =>
          simp only [hep, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨.inr ⟨coins, rfl⟩, fun htr => (hT.send_good s₁ P coins htr).2.2 _⟩
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨.inl rfl, id⟩
  · change z ∈ support (((challLoggedTracked T sm Δ qep cfg (P, m₀, m₁, r)).run gs).run (tr₀, gLog)) at hz
    unfold challLoggedTracked at hz
    dsimp only at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hok : cfg.sendOK gs P
    · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact ⟨.inl rfl, id⟩
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
      cases hwin : gs.win
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift] at hz
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift] at hz
        simp only [bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
        rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨.inl rfl, id⟩
        | some s₁ =>
          simp only [hep] at hz
          cases hch : (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              StateT.run_get, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨.inr ⟨coins, rfl⟩, fun htr => (hT.send_good s₁ P coins htr).2.2 _⟩
          · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨.inl rfl, id⟩
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨.inl rfl, id⟩
  · change z ∈ support (((deliverBothLogged T sm cfg (P, c)).run gs).run (tr₀, gLog)) at hz
    unfold deliverBothLogged at hz
    dsimp only at hz
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind] at hz
    dsimp [liftStateT, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
      StateT.lift, StateT.run] at hz
    simp only [bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨⟨res, gs'⟩, _, rfl⟩
    exact ⟨.inl rfl, fun htr => hT.inv_deliver gs P c res htr⟩
  · have heq := liftStateT_step_support (injectR sm Δ qep cfg (P, c)) gs tr₀ gLog hz
    exact ⟨.inl (congrArg Prod.snd heq), fun htr => by simpa [heq] using htr⟩
  · have heq := liftStateT_step_support (corrR cfg P) gs tr₀ gLog hz
    exact ⟨.inl (congrArg Prod.snd heq), fun htr => by simpa [heq] using htr⟩

theorem oracleHaltedLogged_step {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    {badGlobal : List Coins → Bool} {T : SessionHaltTracker St Msg Coins C Key τ}
    {TrInv : τ → List Coins → Prop} (hT : ValidSessionHaltTracker badGlobal T TrInv)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (gs : GameState St Msg C) (tr₀ : τ) (gLog : List Coins)
    {z : ((CryptoGames.SM.spec St Msg Coins C).Range q × GameState St Msg C) × (τ × List Coins)}
    (hz : z ∈ support (((oracleHaltedLogged T sm Δ qep cfg q).run gs).run (tr₀, gLog))) :
    (z.2.2 = gLog ∨ ∃ c, z.2.2 = gLog ++ [c]) ∧ (TrInv tr₀ gLog → TrInv z.2.1 z.2.2) := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change z ∈ support (((transmitHaltedLogged T sm Δ qep cfg (P, m, r)).run gs).run (tr₀, gLog)) at hz
    unfold transmitHaltedLogged at hz
    dsimp only at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hok : cfg.sendOK gs P
    · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact ⟨.inl rfl, id⟩
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
      cases hwin : gs.win
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift] at hz
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift] at hz
        simp only [bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
        rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨.inl rfl, id⟩
        | some s₁ =>
          simp only [hep, StateT.run_bind, StateT.run_lift, StateT.run_get,
            bind_assoc, pure_bind] at hz
          cases hb : (T.checkSend s₁ P coins tr₀).1
          · simp only [hb, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨.inr ⟨coins, rfl⟩, fun htr => (hT.send_good s₁ P coins htr).2.2 _⟩
          · simp only [hb, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_set,
              StateT.run_pure, bind_assoc, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨.inr ⟨coins, rfl⟩, fun htr => (hT.send_good s₁ P coins htr).2.1⟩
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨.inl rfl, id⟩
  · change z ∈ support (((challHaltedLogged T sm Δ qep cfg (P, m₀, m₁, r)).run gs).run (tr₀, gLog)) at hz
    unfold challHaltedLogged at hz
    dsimp only at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hok : cfg.sendOK gs P
    · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact ⟨.inl rfl, id⟩
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
      cases hwin : gs.win
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift] at hz
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift] at hz
        simp only [bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
        rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨.inl rfl, id⟩
        | some s₁ =>
          simp only [hep] at hz
          cases hch : (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              StateT.run_get, bind_assoc, pure_bind] at hz
            cases hb : (T.checkSend s₁ P coins tr₀).1
            · simp only [hb, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
                StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨.inr ⟨coins, rfl⟩, fun htr => (hT.send_good s₁ P coins htr).2.2 _⟩
            · simp only [hb, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_set,
                StateT.run_pure, bind_assoc, pure_bind,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨.inr ⟨coins, rfl⟩, fun htr => (hT.send_good s₁ P coins htr).2.1⟩
          · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨.inl rfl, id⟩
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨.inl rfl, id⟩
  · change z ∈ support (((deliverBothLogged T sm cfg (P, c)).run gs).run (tr₀, gLog)) at hz
    unfold deliverBothLogged at hz
    dsimp only at hz
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind] at hz
    dsimp [liftStateT, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
      StateT.lift, StateT.run] at hz
    simp only [bind_assoc, pure_bind, support_bind, Set.mem_iUnion, exists_prop,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨⟨res, gs'⟩, _, rfl⟩
    exact ⟨.inl rfl, fun htr => hT.inv_deliver gs P c res htr⟩
  · have heq := liftStateT_step_support (injectR sm Δ qep cfg (P, c)) gs tr₀ gLog hz
    exact ⟨.inl (congrArg Prod.snd heq), fun htr => by simpa [heq] using htr⟩
  · have heq := liftStateT_step_support (corrR cfg P) gs tr₀ gLog hz
    exact ⟨.inl (congrArg Prod.snd heq), fun htr => by simpa [heq] using htr⟩

theorem oracleLogged_agree_halted {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    {badGlobal : List Coins → Bool} {T : SessionHaltTracker St Msg Coins C Key τ}
    {TrInv : τ → List Coins → Prop} (hT : ValidSessionHaltTracker badGlobal T TrInv)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (gs : GameState St Msg C) (tr₀ : τ) (gLog : List Coins) (htr₀ : TrInv tr₀ gLog)
    (p : ((CryptoGames.SM.spec St Msg Coins C).Range q × GameState St Msg C) × (τ × List Coins) → Prop) :
    Pr{let z ← ((oracleLoggedTracked T sm Δ qep cfg q).run gs).run (tr₀, gLog)}[
        p z ∧ badGlobal z.2.2 = false] =
      Pr{let z ← ((oracleHaltedLogged T sm Δ qep cfg q).run gs).run (tr₀, gLog)}[
        p z ∧ badGlobal z.2.2 = false] := by
  let : MeasurableSpace (Coins × Bool) := ⊤
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change Pr{let z ← ((transmitLoggedTracked T sm Δ qep cfg (P, m, r)).run gs).run (tr₀, gLog)}[
        p z ∧ badGlobal z.2.2 = false] =
      Pr{let z ← ((transmitHaltedLogged T sm Δ qep cfg (P, m, r)).run gs).run (tr₀, gLog)}[
        p z ∧ badGlobal z.2.2 = false]
    unfold transmitLoggedTracked transmitHaltedLogged
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hok : cfg.sendOK gs P
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hwin : gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift]
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
        simp only [bind_assoc, pure_bind]
        rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
        congr 1; funext ⟨coins, bad⟩
        cases gs.epMgmt Δ qep P bad with
        | none => rfl
        | some s₁ =>
          simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, map_eq_bind_pure_comp,
            Function.comp_apply]
          exact (prEvent_pure_send_branch_eq badGlobal gLog coins
            (T.checkSend s₁ P coins tr₀).1 (hT.send_good s₁ P coins htr₀).1 _ (none, gs) _
            (T.checkSend s₁ P coins tr₀).2 p).trans
            (by cases (T.checkSend s₁ P coins tr₀).1 <;>
                simp [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
                  map_eq_bind_pure_comp])
      · simp only [↓reduceIte]
  · change Pr{let z ← ((challLoggedTracked T sm Δ qep cfg (P, m₀, m₁, r)).run gs).run (tr₀, gLog)}[
        p z ∧ badGlobal z.2.2 = false] =
      Pr{let z ← ((challHaltedLogged T sm Δ qep cfg (P, m₀, m₁, r)).run gs).run (tr₀, gLog)}[
        p z ∧ badGlobal z.2.2 = false]
    unfold challLoggedTracked challHaltedLogged
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hok : cfg.sendOK gs P
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hwin : gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift]
        dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
        simp only [bind_assoc, pure_bind]
        rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
        congr 1; funext ⟨coins, bad⟩
        cases gs.epMgmt Δ qep P bad with
        | none => rfl
        | some s₁ =>
          dsimp only
          cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
              StateT.run_get, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
              map_eq_bind_pure_comp, Function.comp_apply]
            exact (prEvent_pure_send_branch_eq badGlobal gLog coins
              (T.checkSend s₁ P coins tr₀).1 (hT.send_good s₁ P coins htr₀).1 _ (none, gs) _
              (T.checkSend s₁ P coins tr₀).2 p).trans
              (by cases (T.checkSend s₁ P coins tr₀).1 <;>
                  simp [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
                    map_eq_bind_pure_comp])
          · rfl
      · simp only [↓reduceIte]
  · change Pr{let z ← ((deliverBothLogged T sm cfg (P, c)).run gs).run (tr₀, gLog)}[
        p z ∧ badGlobal z.2.2 = false] =
      Pr{let z ← ((deliverBothLogged T sm cfg (P, c)).run gs).run (tr₀, gLog)}[
        p z ∧ badGlobal z.2.2 = false]
    rfl
  · change Pr{let z ← (((liftStateT (injectR sm Δ qep cfg (P, c)) :
          StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp) _).run gs).run (tr₀, gLog))}[
        p z ∧ badGlobal z.2.2 = false] =
      Pr{let z ← (((liftStateT (injectR sm Δ qep cfg (P, c)) :
          StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp) _).run gs).run (tr₀, gLog))}[
        p z ∧ badGlobal z.2.2 = false]
    rfl
  · change Pr{let z ← (((liftStateT (corrR cfg P) :
          StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp) _).run gs).run (tr₀, gLog))}[
        p z ∧ badGlobal z.2.2 = false] =
      Pr{let z ← (((liftStateT (corrR cfg P) :
          StateT (GameState St Msg C) (StateT (τ × List Coins) ProbComp) _).run gs).run (tr₀, gLog))}[
        p z ∧ badGlobal z.2.2 = false]
    rfl

/-! ## Promotion and wire-decode equivalence helpers -/

private theorem bhE2ELocalStartSessionTracked_proj {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (tracks : List τ) (sid : SignalPqxdh.SessionId S) :
    (fun p => (p.1, p.2.1)) <$>
        bhE2ELocalStartSessionTracked initTrack ki C K bMode? (σ, tracks) sid =
      compositionLocalStart ki C K bMode? σ sid := by
  unfold bhE2ELocalStartSessionTracked compositionLocalStart
  dsimp only
  cases bhE2EGuard σ sid <;> simp [map_eq_bind_pure_comp, bind_assoc]

private theorem bhE2ELocalStartSessionTracked_support {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    (σ : BHE2EDrvState S ℓ) (tracks : List τ) (sid : SignalPqxdh.SessionId S)
    {p : Option ℕ × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support (bhE2ELocalStartSessionTracked initTrack ki C K bMode? (σ, tracks) sid))
    {t : τ} (ht : t ∈ p.2.2) :
    t ∈ tracks ∨ ∃ k, t = initTrack k := by
  unfold bhE2ELocalStartSessionTracked at hp
  dsimp only at hp
  cases h : bhE2EGuard σ sid with
  | none =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hp; subst hp; exact .inl ht
  | some g =>
    rcases g with ⟨_, _, u, j⟩
    simp only [h, support_bind, Set.mem_iUnion, exists_prop, support_pure,
      Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
    dsimp only at ht
    split at ht
    · rcases List.mem_append.mp ht with hm | hm
      · exact .inl hm
      · exact .inr ⟨_, List.mem_singleton.mp hm⟩
    · exact .inl ht

private theorem bhE2EStepLocalSmCoinLogged_eq_decode {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSmCoinLogged C K qep decT encT σ i q = (do
      if !bhE2EDrvInstClean σ i then return ((none, none, none), σ)
      else
        match σ.insts[i]?, σ.instMeta[i]? with
        | some d, some im =>
          if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
            let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
            let σ' := { σ with instMeta := σ.instMeta.set i imCorr }
            return ((none, none, none), σ')
          else
            match d.gs with
            | none => return ((none, none, none), σ)
            | some gs =>
              match bhDecodeSmWireQuery im d q with
              | none => return ((none, none, none), σ)
              | some q' =>
                let spqr := spqrV1SessionUniformCoins C.F K
                let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
                let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
                let (r, gs') ← (oracleImplRM (smSchemeCoinLogged sch) (2 + 1) qep cfg q').run gs
                let accepted := bhIsBobAcceptSMResp q' r
                let im' := if !im.bobAccepted && accepted then
                    { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                  else im
                let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                   instMeta := σ.instMeta.set i im' }
                return (bhPackSmResp q' r, σ1)
        | _, _ => return ((none, none, none), σ)) := by
  unfold bhE2EStepLocalSmCoinLogged
  cases bhE2EDrvInstClean σ i
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases σ.insts[i]? with
    | none => rfl
    | some d =>
      cases σ.instMeta[i]? with
      | none => rfl
      | some im =>
        dsimp only
        cases (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases d.gs with
          | none => rfl
          | some gs =>
            dsimp only
            rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
            · rfl
            · rfl
            · cases P
              · dsimp [bhDecodeSmWireQuery]; cases (bhDecodePreKeyMsgE c).isSome <;> rfl
              · dsimp [bhDecodeSmWireQuery]
                cases hba : im.bobAccepted
                · simp only [Bool.not_false, ↓reduceIte]
                  cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some _ => dsimp only; first | rfl | (split_ifs <;> rfl)
                · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some _ => dsimp only; first | rfl | (split_ifs <;> rfl)
            · cases P
              · dsimp [bhDecodeSmWireQuery]; cases (bhDecodePreKeyMsgE c).isSome <;> rfl
              · dsimp [bhDecodeSmWireQuery]
                cases hba : im.bobAccepted
                · simp only [Bool.not_false, ↓reduceIte]
                · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  cases bhDecodePreKeyMsgE c with
                  | none => rfl
                  | some _ => dsimp only; first | rfl | (split_ifs <;> rfl)
            · rfl
        · rfl

/-! ## Coupled multi-session E2E driver and main inequality -/

private def stepLocalSmCore {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (initTrack : SampledSessionKey → τ)
    (ora : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512)
        (BitVec 256) Bytes → ConfigR (GhostState Bytes) (Plain ℓ) Bytes →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
          (StateT (τ × List (BitVec 512)) ProbComp)))
    (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (tracks : List τ) (i : ℕ)
    (q q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) :
    StateT (BHE2EDrvState S ℓ × List τ) (StateT (List (BitVec 512)) ProbComp)
      ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range q) := do
  let spqr := spqrV1SessionUniformCoins C.F K
  let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
  let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
  let tr₀ := (tracks[i]?).getD (initTrack default)
  let gLog ← StateT.lift get
  let z ← liftProb2 (((ora sch cfg q').run gs).run (tr₀, gLog))
  let r := z.1.1
  let gs' := z.1.2
  let tr' := z.2.1
  let gLog' := z.2.2
  let accepted := bhIsBobAcceptSMResp q' r
  let im' := if !im.bobAccepted && accepted then
      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
    else im
  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                     instMeta := σ.instMeta.set i im' }
  set (σ1, tracks.set i tr')
  StateT.lift (set gLog')
  return bhUnpackSmResp q (bhPackSmResp q' r)

private def stepLocalSmCoupled {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (initTrack : SampledSessionKey → τ)
    (ora : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512)
        (BitVec 256) Bytes → ConfigR (GhostState Bytes) (Plain ℓ) Bytes →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
          (StateT (τ × List (BitVec 512)) ProbComp)))
    (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    StateT (BHE2EDrvState S ℓ × List τ) (StateT (List (BitVec 512)) ProbComp)
      ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range q) := do
  let σH ← get
  let σ := σH.1
  let tracks := σH.2
  if !bhE2EDrvInstClean σ i then return bhUnpackSmResp q (none, none, none)
  else
    match σ.insts[i]?, σ.instMeta[i]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
        let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
        let σ' := { σ with instMeta := σ.instMeta.set i imCorr }
        set (σ', tracks)
        return bhUnpackSmResp q (none, none, none)
      else
        match d.gs with
        | none => return bhUnpackSmResp q (none, none, none)
        | some gs =>
          match bhDecodeSmWireQuery im d q with
          | none => return bhUnpackSmResp q (none, none, none)
          | some q' => stepLocalSmCore initTrack ora C K decT encT σ tracks i q q' d im gs
    | _, _ => return bhUnpackSmResp q (none, none, none)

private def drvImplCoupled {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (initTrack : SampledSessionKey → τ)
    (ora : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512)
        (BitVec 256) Bytes → ConfigR (GhostState Bytes) (Plain ℓ) Bytes →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
          (StateT (τ × List (BitVec 512)) ProbComp)))
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ × List τ) (StateT (List (BitVec 512)) ProbComp)) := fun q =>
  match q with
  | .inl n => liftProb2 (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σH ← get
    let σ := σH.1
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← liftProb2 ((ki kq).run σ.st)
      set (bhE2EMirror { σ with st := st' } kq kr, σH.2)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σH ← get
    let (idx?, σH') ← liftProb2 (bhE2ELocalStartSessionTracked initTrack ki C K (some σH.1.b) σH sid)
    set σH'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => stepLocalSmCoupled initTrack ora C K decT encT i sq

private theorem stepLocalSmCoupled_run_some {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (initTrack : SampledSessionKey → τ)
    (ora : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512)
        (BitVec 256) Bytes → ConfigR (GhostState Bytes) (Plain ℓ) Bytes →
      QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
          (StateT (τ × List (BitVec 512)) ProbComp)))
    (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (tracks : List τ) (gLog : List (BitVec 512))
    (i : ℕ) (q q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) :
    (((stepLocalSmCore initTrack ora C K decT encT σ tracks i q q' d im gs).run
        (σ, tracks)).run gLog) =
      (fun z =>
          let r := z.1.1
          let gs' := z.1.2
          let tr' := z.2.1
          let gLog' := z.2.2
          let im' := if !im.bobAccepted && bhIsBobAcceptSMResp q' r then
              { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
            else im
          let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                             instMeta := σ.instMeta.set i im' }
          ((bhUnpackSmResp q (bhPackSmResp q' r), (σ1, tracks.set i tr')), gLog')) <$>
        (((ora (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
            (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT)
            q').run gs).run ((tracks[i]?).getD (initTrack default), gLog)) := by
  dsimp only [stepLocalSmCore, liftProb2, StateT.lift, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, StateT.set, pure, StateT.pure]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem drvImplLogged_proj {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (t : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    ProjectsToLogged
      (drvImplCoupled T.init (fun sch cfg => oracleLoggedTracked T sch (2 + 1) qep cfg)
        P ki C K decT encT t)
      (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT t) := by
  intro σ tracks gLog
  rcases t with n | ((kq | ctl) | ⟨i, sq⟩)
  · exact liftProb2_projLogged _ σ tracks gLog
  · dsimp only [drvImplCoupled, cliE2EDrvImplWithCoinLogged]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases h1 : (!bhDrvKiQueryOk P σ.toModelDriverBase kq)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases kq <;> dsimp only
      all_goals
        try split_ifs
      all_goals
        simp [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_pure, liftProb2_run,
          WriterT.run_bind, WriterT.run_pure, map_eq_bind_pure_comp, bind_assoc,
          List.append_nil]
    · simp [WriterT.run_pure, List.append_nil]
  · cases ctl with
    | startDR sid =>
      dsimp only [drvImplCoupled, cliE2EDrvImplWithCoinLogged]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
        pure_bind, WriterT.run_bind, WriterT.run_pure, liftProb2_run, liftM_writer_run]
      rw [← bhE2ELocalStartSessionTracked_proj T.init ki C K (some σ.b) σ tracks sid]
      simp [map_eq_bind_pure_comp, bind_assoc, List.append_nil]
  · dsimp only [drvImplCoupled, stepLocalSmCoupled, cliE2EDrvImplWithCoinLogged]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, WriterT.run_bind, StateT.run_lift]
    rw [bhE2EStepLocalSmCoinLogged_eq_decode]
    cases bhE2EDrvInstClean σ i
    · simp [WriterT.run_pure, List.append_nil]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases σ.insts[i]? with
      | none => simp [WriterT.run_pure, List.append_nil]
      | some d =>
        cases σ.instMeta[i]? with
        | none => simp [WriterT.run_pure, List.append_nil]
        | some im =>
          dsimp only
          cases (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases d.gs with
            | none => simp [WriterT.run_pure, List.append_nil]
            | some gs =>
              dsimp only
              cases bhDecodeSmWireQuery im d sq with
              | none => simp [WriterT.run_pure, List.append_nil]
              | some q' =>
                dsimp only
                rw [stepLocalSmCoupled_run_some]
                let spqr := spqrV1SessionUniformCoins C.F K
                let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
                let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
                let tr₀ := (tracks[i]?).getD (T.init default)
                let post (r : _) (gs' : _) : BHE2ESmResp ℓ × BHE2EDrvState S ℓ :=
                  let im' := if !im.bobAccepted && bhIsBobAcceptSMResp q' r then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  (bhPackSmResp q' r,
                    { σ with insts := σ.insts.set i { d with gs := some gs' },
                             instMeta := σ.instMeta.set i im' })
                have hlhs :
                    (fun z => ((z.1.1, z.1.2.1), z.2)) <$>
                      ((fun z =>
                        ((bhUnpackSmResp sq (post z.1.1 z.1.2).1,
                          ((post z.1.1 z.1.2).2, tracks.set i z.2.1)), z.2.2)) <$>
                        (((oracleLoggedTracked T sch (2 + 1) qep cfg q').run gs).run (tr₀, gLog))) =
                    (fun y : ((_ × _) × List (BitVec 512)) =>
                        ((bhUnpackSmResp sq (post y.1.1 y.1.2).1, (post y.1.1 y.1.2).2), y.2)) <$>
                      ((fun z => (z.1, z.2.2)) <$>
                        (((oracleLoggedTracked T sch (2 + 1) qep cfg q').run gs).run (tr₀, gLog))) := by
                  simp [Functor.map_map]
                change (fun z => ((z.1.1, z.1.2.1), z.2)) <$>
                    ((fun z =>
                      ((bhUnpackSmResp sq (post z.1.1 z.1.2).1,
                        ((post z.1.1 z.1.2).2, tracks.set i z.2.1)), z.2.2)) <$>
                      (((oracleLoggedTracked T sch (2 + 1) qep cfg q').run gs).run (tr₀, gLog))) = _
                rw [hlhs, oracleLoggedTracked_proj]
                simp [WriterT.run_bind, WriterT.run_pure, StateT.run_set,
                  StateT.run_pure, map_eq_bind_pure_comp, bind_assoc,
                  List.append_nil, spqr, sch, cfg, post]
          · simp [WriterT.run_pure, StateT.run_set,
              StateT.run_pure, List.append_nil]

private theorem drvImplHalted_proj {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (t : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    ProjectsToHalted
      (drvImplCoupled T.init (fun sch cfg => oracleHaltedLogged T sch (2 + 1) qep cfg)
        P ki C K decT encT t)
      (bhE2EDrvImplWithSessionTracked T P ki C K qep decT encT t) := by
  intro σH gLog
  rcases σH with ⟨σ, tracks⟩
  rcases t with n | ((kq | ctl) | ⟨i, sq⟩)
  · exact liftProb2_projHalted _ (σ, tracks) gLog
  · dsimp only [drvImplCoupled, bhE2EDrvImplWithSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases h1 : (!bhDrvKiQueryOk P σ.toModelDriverBase kq)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases kq <;> dsimp only
      all_goals
        try split_ifs
      all_goals
        simp [StateT.run_bind, StateT.run_set, StateT.run_pure, liftProb2_run,
          map_eq_bind_pure_comp, bind_assoc]
    · simp
  · cases ctl with
    | startDR sid =>
      dsimp only [drvImplCoupled, bhE2EDrvImplWithSessionTracked]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        pure_bind, liftProb2_run]
      dsimp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.lift, StateT.run]
      simp [map_eq_bind_pure_comp, bind_assoc]
  · dsimp only [drvImplCoupled, stepLocalSmCoupled, bhE2EDrvImplWithSessionTracked,
      bhE2EStepLocalSmSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bhE2EDrvInstClean σ i
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases σ.insts[i]? with
      | none => simp
      | some d =>
        cases σ.instMeta[i]? with
        | none => simp
        | some im =>
          dsimp only
          cases (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases d.gs with
            | none => simp
            | some gs =>
              dsimp only
              cases bhDecodeSmWireQuery im d sq with
              | none => simp
              | some q' =>
                dsimp only
                rw [stepLocalSmCoupled_run_some]
                let spqr := spqrV1SessionUniformCoins C.F K
                let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
                let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
                let tr₀ := (tracks[i]?).getD (T.init default)
                let post (r : _) (gs' : _) (tr' : τ) :=
                  let im' := if !im.bobAccepted && bhIsBobAcceptSMResp q' r then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  (bhUnpackSmResp sq (bhPackSmResp q' r),
                    ({ σ with insts := σ.insts.set i { d with gs := some gs' },
                              instMeta := σ.instMeta.set i im' },
                     tracks.set i tr'))
                have hlhs :
                    Prod.fst <$>
                      ((fun z => (post z.1.1 z.1.2 z.2.1, z.2.2)) <$>
                        (((oracleHaltedLogged T sch (2 + 1) qep cfg q').run gs).run (tr₀, gLog))) =
                    (fun y : (_ × _) × τ => post y.1.1 y.1.2 y.2) <$>
                      ((fun z => (z.1, z.2.1)) <$>
                        (((oracleHaltedLogged T sch (2 + 1) qep cfg q').run gs).run (tr₀, gLog))) := by
                  simp [Functor.map_map]
                change Prod.fst <$>
                    ((fun z => (post z.1.1 z.1.2 z.2.1, z.2.2)) <$>
                      (((oracleHaltedLogged T sch (2 + 1) qep cfg q').run gs).run (tr₀, gLog))) = _
                rw [hlhs, oracleHaltedLogged_proj]
                simp [StateT.run_bind, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
                  bind_assoc, spqr, sch, cfg, tr₀, post]
          · simp [StateT.run_set, StateT.run_pure]

private theorem drvImplCoupled_agreeInv {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {badGlobal : List (BitVec 512) → Bool} (hBad : ValidBadLog badGlobal)
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrInv : τ → List (BitVec 512) → Prop} (hT : ValidSessionHaltTracker badGlobal T TrInv)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (t : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    AgreeInv (fun w => badGlobal w = false)
      (fun (σH : BHE2EDrvState S ℓ × List τ) gLog => ∀ tr ∈ σH.2, TrInv tr gLog)
      (drvImplCoupled T.init (fun sch cfg => oracleLoggedTracked T sch (2 + 1) qep cfg)
        P ki C K decT encT t)
      (drvImplCoupled T.init (fun sch cfg => oracleHaltedLogged T sch (2 + 1) qep cfg)
        P ki C K decT encT t) := by
  let good : List (BitVec 512) → Prop := fun w => badGlobal w = false
  let DrvInv : BHE2EDrvState S ℓ × List τ → List (BitVec 512) → Prop :=
    fun σH gLog => ∀ tr ∈ σH.2, TrInv tr gLog
  rcases t with n | ((kq | ctl) | ⟨i, sq⟩)
  · dsimp only [drvImplCoupled]
    exact liftProb2_agreeInv good DrvInv _
  · dsimp only [drvImplCoupled]
    refine AgreeInv.refl
      { pres_bad := fun ⟨σ, tracks⟩ gLog hbad z hz => ?_
        pres_inv := fun ⟨σ, tracks⟩ gLog hinv z hz => ?_ }
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
      cases h1 : (!bhDrvKiQueryOk P σ.toModelDriverBase kq)
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hz
        cases h2 : (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false)
        · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftProb2_run,
            StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply, support_bind, Set.mem_iUnion, exists_prop, support_pure,
            Set.mem_singleton_iff] at hz
          rcases hz with ⟨_, _, rfl⟩; exact hbad
        · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hbad
      · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hbad
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
      cases h1 : (!bhDrvKiQueryOk P σ.toModelDriverBase kq)
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hz
        cases h2 : (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false)
        · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftProb2_run,
            StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply, support_bind, Set.mem_iUnion, exists_prop, support_pure,
            Set.mem_singleton_iff] at hz
          rcases hz with ⟨_, _, rfl⟩; exact hinv
        · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hinv
      · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hinv
  · cases ctl with
    | startDR sid =>
      dsimp only [drvImplCoupled]
      refine AgreeInv.refl
        { pres_bad := fun ⟨σ, tracks⟩ gLog hbad z hz => ?_
          pres_inv := fun ⟨σ, tracks⟩ gLog hinv z hz => ?_ }
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, liftProb2_run, StateT.run_set,
          StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
          support_bind, Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨_, _, rfl⟩; exact hbad
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, liftProb2_run, StateT.run_set,
          StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
          support_bind, Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨p, hp, rfl⟩
        intro tr htr
        rcases bhE2ELocalStartSessionTracked_support T.init ki C K (some σ.b) σ tracks sid hp htr with
          hmem | ⟨k, rfl⟩
        · exact hinv tr hmem
        · exact hT.inv_init k gLog
  · dsimp only [drvImplCoupled]
    have hpres (ora : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512)
          (BitVec 256) Bytes → ConfigR (GhostState Bytes) (Plain ℓ) Bytes → QueryImpl _ _)
        (hstep : ∀ sch cfg q' gs tr₀ gLog z,
          z ∈ support (((ora sch cfg q').run gs).run (tr₀, gLog)) →
          (z.2.2 = gLog ∨ ∃ c, z.2.2 = gLog ++ [c]) ∧ (TrInv tr₀ gLog → TrInv z.2.1 z.2.2)) :
        PreservesInvBad good DrvInv (stepLocalSmCoupled T.init ora C K decT encT i sq) := by
      refine { pres_bad := fun ⟨σ, tracks⟩ gLog hbad z hz => ?_,
               pres_inv := fun ⟨σ, tracks⟩ gLog hinv z hz => ?_ }
      · dsimp only [stepLocalSmCoupled] at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
        cases hclean : bhE2EDrvInstClean σ i
        · simp only [hclean, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz; subst hz; exact hbad
        · simp only [hclean, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
          cases hinst : σ.insts[i]? with
          | none =>
            simp only [hinst, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hbad
          | some d =>
            cases him : σ.instMeta[i]? with
            | none =>
              simp only [hinst, him, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hbad
            | some im =>
              simp only [hinst, him] at hz
              cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d)
              · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hz
                cases hgs : d.gs with
                | none =>
                  simp only [hgs, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact hbad
                | some gs =>
                  simp only [hgs] at hz
                  cases hdec : bhDecodeSmWireQuery im d sq with
                  | none =>
                    simp only [hdec, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
                    subst hz; exact hbad
                  | some q' =>
                    simp only [hdec] at hz
                    rw [stepLocalSmCoupled_run_some, support_map] at hz
                    rcases hz with ⟨w, hw, rfl⟩
                    rcases (hstep _ _ q' gs _ gLog w hw).1 with heq | ⟨c, heq⟩
                    · dsimp only [good]; rw [heq]; exact hbad
                    · dsimp only [good]; rw [heq]
                      exact fun hg => hbad (hBad.snoc_false gLog c hg)
              · simp only [hcorr, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                  pure_bind, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact hbad
      · dsimp only [stepLocalSmCoupled] at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
        cases hclean : bhE2EDrvInstClean σ i
        · simp only [hclean, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hz; subst hz; exact hinv
        · simp only [hclean, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
          cases hinst : σ.insts[i]? with
          | none =>
            simp only [hinst, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hinv
          | some d =>
            cases him : σ.instMeta[i]? with
            | none =>
              simp only [hinst, him, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hinv
            | some im =>
              simp only [hinst, him] at hz
              cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d)
              · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hz
                cases hgs : d.gs with
                | none =>
                  simp only [hgs, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact hinv
                | some gs =>
                  simp only [hgs] at hz
                  cases hdec : bhDecodeSmWireQuery im d sq with
                  | none =>
                    simp only [hdec, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
                    subst hz; exact hinv
                  | some q' =>
                    simp only [hdec] at hz
                    rw [stepLocalSmCoupled_run_some, support_map] at hz
                    rcases hz with ⟨w, hw, rfl⟩
                    have htr₀ : TrInv ((tracks[i]?).getD (T.init default)) gLog := by
                      cases hget : tracks[i]? with
                      | none => simpa using hT.inv_init default gLog
                      | some tr => simpa using hinv tr (List.mem_of_getElem? hget)
                    obtain ⟨hg, htr'⟩ := hstep _ _ q' gs _ gLog w hw
                    intro t ht
                    rcases List.mem_or_eq_of_mem_set ht with hmem | rfl
                    · rcases hg with heq | ⟨c, heq⟩
                      · rw [heq]; exact hinv t hmem
                      · rw [heq]; exact hT.inv_mono c (hinv t hmem)
                    · exact htr' htr₀
              · simp only [hcorr, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                  pure_bind, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact hinv
    refine
      { pres₁ := hpres _ fun sch cfg q' gs tr₀ gLog z hz =>
          oracleLoggedTracked_step hT sch (2 + 1) qep cfg q' gs tr₀ gLog hz
        pres₂ := hpres _ fun sch cfg q' gs tr₀ gLog z hz =>
          oracleHaltedLogged_step hT sch (2 + 1) qep cfg q' gs tr₀ gLog hz
        agree := fun ⟨σ, tracks⟩ gLog hinv _ p => ?_ }
    dsimp only [stepLocalSmCoupled]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bhE2EDrvInstClean σ i
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases σ.insts[i]? with
      | none => simp only
      | some d =>
        cases σ.instMeta[i]? with
        | none => simp only
        | some im =>
          dsimp only
          cases (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases d.gs with
            | none => simp only
            | some gs =>
              dsimp only
              cases bhDecodeSmWireQuery im d sq with
              | none => simp only
              | some q' =>
                dsimp only
                rw [stepLocalSmCoupled_run_some, stepLocalSmCoupled_run_some,
                  prEvent_map_eq, prEvent_map_eq]
                have htr₀ : TrInv ((tracks[i]?).getD (T.init default)) gLog := by
                  cases hget : tracks[i]? with
                  | none => simpa using hT.inv_init default gLog
                  | some tr => simpa using hinv tr (List.mem_of_getElem? hget)
                exact oracleLogged_agree_halted hT _ (2 + 1) qep _ q' gs _ gLog htr₀ _
          · simp only [↓reduceIte]

/-- For any monotone-sticky `badGlobal` and valid per-session `SessionHaltTracker` `T`, good-log
outcomes `(val, gLog)` with `badGlobal gLog = false` in `cliE2EExpWithKiCoinLogged` occur with
probability at most that of `val` in `bhE2EExpWithKiSessionTracked T`. -/
theorem cliE2EExpWithKiCoinLogged_good_le_sessionTracked_pr {τ : Type} {ℓ : ℕ} {Pt : Type}
    {badGlobal : List (BitVec 512) → Bool} (hBad : ValidBadLog badGlobal)
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrInv : τ → List (BitVec 512) → Prop} (hT : ValidSessionHaltTracker badGlobal T TrInv)
    (secb : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (val : Bool) :
    Pr{let w ← cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT B}[
        w.1 = val ∧ badGlobal w.2 = false] ≤
      Pr{let b ← bhE2EExpWithKiSessionTracked T secb S P ki C K qep decT encT B}[b = val] := by
  let fin (b b' : Bool) (σ : BHE2EDrvState S ℓ) : ProbComp Bool :=
    if !allTestedSessionsFresh P σ.st then $ᵗ Bool else return (b' == b || bhE2EDrvWon σ b)
  let implL := drvImplCoupled T.init (fun sch cfg => oracleLoggedTracked T sch (2 + 1) qep cfg)
    P ki C K decT encT
  let implH := drvImplCoupled T.init (fun sch cfg => oracleHaltedLogged T sch (2 + 1) qep cfg)
    P ki C K decT encT
  let bodyL (b : Bool) :
      StateT (BHE2EDrvState S ℓ × List τ) (StateT (List (BitVec 512)) ProbComp) Bool := do
    let b' ← simulateQ implL B
    let σH ← get
    liftProb2 (fin b b' σH.1)
  let bodyH (b : Bool) :
      StateT (BHE2EDrvState S ℓ × List τ) (StateT (List (BitVec 512)) ProbComp) Bool := do
    let b' ← simulateQ implH B
    let σH ← get
    liftProb2 (fin b b' σH.1)
  let s₀ (b : Bool) : BHE2EDrvState S ℓ := { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
  have hLHS :
      cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT B =
        (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          (fun z => (z.1.1, z.2)) <$> (((bodyL b).run (s₀ b, [])).run [])) := by
    unfold cliE2EExpWithKiCoinLogged
    simp only [WriterT.run_bind, liftM_writer_run, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_apply, List.nil_append]
    congr 1; funext b
    have hsim := ProjectsToLogged.simulateQ implL
      (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
      (drvImplLogged_proj T P ki C K qep decT encT) B (s₀ b) [] []
    have hsim' :
        ((simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) B).run (s₀ b)).run =
          (fun z => ((z.1.1, z.1.2.1), z.2)) <$> (((simulateQ implL B).run (s₀ b, [])).run []) := by
      simpa [List.nil_append] using hsim.symm
    dsimp only [s₀] at hsim'
    rw [hsim']
    dsimp only [bodyL]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, liftProb2_run,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
    congr 1; funext z
    dsimp only [fin]
    cases allTestedSessionsFresh P z.1.2.1.st <;>
      simp [WriterT.run_pure, map_eq_bind_pure_comp,
        bind_assoc, List.append_nil]
  have hRHS :
      bhE2EExpWithKiSessionTracked T secb S P ki C K qep decT encT B =
        (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          (fun z => z.1.1) <$> (((bodyH b).run (s₀ b, [])).run [])) := by
    unfold bhE2EExpWithKiSessionTracked
    congr 1; funext b
    have hsim := ProjectsToHalted.simulateQ implH
      (bhE2EDrvImplWithSessionTracked T P ki C K qep decT encT)
      (drvImplHalted_proj T P ki C K qep decT encT) B (s₀ b, []) []
    rw [← hsim]
    dsimp only [bodyH, fin]
    simp [StateT.run_bind, StateT.run_get, liftProb2_run, map_eq_bind_pure_comp, bind_assoc]
  rw [hLHS, hRHS, prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  refine MeasureTheory.lintegral_mono fun b => ?_
  rw [prEvent_map_eq, prEvent_map_eq]
  have hAgree : AgreeInv (fun w => badGlobal w = false)
      (fun (σH : BHE2EDrvState S ℓ × List τ) gLog => ∀ tr ∈ σH.2, TrInv tr gLog)
      (bodyL b) (bodyH b) :=
    AgreeInv.bind
      (AgreeInv.simulateQ implL implH
        (drvImplCoupled_agreeInv hBad hT P ki C K qep decT encT) B)
      fun b' => AgreeInv.bind (AgreeInv.get _ _) fun σH => liftProb2_agreeInv _ _ (fin b b' σH.1)
  have heq := hAgree.agree (s₀ b, []) [] (fun _ h => nomatch h) hBad.nil_false
    (fun z => z.1.1 = val)
  dsimp only at heq ⊢
  rw [heq]
  exact prEvent_mono _ _ _ fun _ h => h.1

/-- `¬ (badGlobal w.2 = true)` variant matching `CliKemFailCoupling.cliPqAdvantage_le_of_e2eHalted`. -/
theorem cliE2EExpWithKiCoinLogged_good_not_true_le_sessionTracked_pr {τ : Type} {ℓ : ℕ} {Pt : Type}
    {badGlobal : List (BitVec 512) → Bool} (hBad : ValidBadLog badGlobal)
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ}
    {TrInv : τ → List (BitVec 512) → Prop} (hT : ValidSessionHaltTracker badGlobal T TrInv)
    (secb : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (val : Bool) :
    Pr{let w ← cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT B}[
        w.1 = val ∧ ¬ (badGlobal w.2 = true)] ≤
      Pr{let b ← bhE2EExpWithKiSessionTracked T secb S P ki C K qep decT encT B}[b = val] := by
  have hcongr :
      Pr{let w ← cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT B}[
          w.1 = val ∧ ¬ (badGlobal w.2 = true)] =
        Pr{let w ← cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT B}[
          w.1 = val ∧ badGlobal w.2 = false] :=
    prEvent_congr _ _ _ fun _ => by simp
  rw [hcongr]
  exact cliE2EExpWithKiCoinLogged_good_le_sessionTracked_pr hBad hT secb S P ki C K qep decT encT B val

end Computational.Proofs.LibsignalCli.MainHaltedOnline
