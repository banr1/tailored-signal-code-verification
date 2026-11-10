/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.UniformStartHop
public import Computational.Proofs.E2E.RefuseCorrB0Core
public import Computational.Proofs.E2E.SignedAdv
public import Computational.Specifications.Game.StatementPqOomFlag
public import Computational.Specifications.Session.StatementIdsModel
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Encaps1Total
import ProofLib.Lemmas

/-!
# Parametric `HaltedTracker` session core

Defines parametric online-halted SM R-game combinators (`HaltedTracker`, `gameRGenHalted`),
structure-preserving tracker homomorphisms (`HaltedTrackerHom`), and proves `Adversary.refuseCorrB0`
commutation and the halted uniform-start PRG hop (`boolBias_mixUGenHaltedWithSpqr_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSessionCore

open scoped ENNReal
open MeasureTheory (Measure)
open OracleComp OracleSpec

open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet (RootKey rootKdf)
open CryptoGames.Ratchet.LibsignalInst
  (configR1OnCurve ratchetKeyAdmissible libsignalSessionScheme libsignalSessionSchemeFromEpoch0Keys)
open CryptoGames.Ratchet.LibsignalSim (rootKdfAsPrg configEpoch0Distinguisher)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey IdentityKey Params Spqr)
open CryptoGames.LibsignalSM (LibAdv)
open CryptoGames.SM
  (ConfigR GameState Adversary AdversaryComp RecvResult spec initState samIfNec
   noBobSendInEpoch0 inWindow
   deliverR injectR corrR transmitQuery challQuery deliverQuery injectQuery corrQuery)
open CryptoGames.SM.Construction (boolBias_le_add_two_mul_boolDist)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E
  (Bytes liftStateT paramsIdsWithSpqr sessionSchemeU configRefuseEarlyBobCorr
   noBobCorrInEpoch0 noBobCorrWhileAliceBelowEpoch10)
open CryptoVerification.E2E.HeadlineU (libSessionU sample_prod_bindU)
open CryptoVerification.E2E.Relabel.GameEq (simulateQ_oracleSpec_query bind_congr_of_support)
open CryptoVerification.E2E.RefuseCorrB0
  (withNoCorrB0 RefuseState refuseTransmit refuseChall refuseDeliver refuseInject refuseCorr
   refuseCorrB0Impl ofGameState_record_epMgmt ofGameState_accept onDeliver_ofGameState_of_inTransit)
open CryptoVerification.E2E.Signed (prgAvg prgReal_avg prgIdeal_avg)

/-! ## Shallow online-halted definitions -/

abbrev paramsV1 (Z : Crypto) (K : MlKem) (idA idB : IdentityKey) : Params Bytes (BitVec 512) :=
  paramsIdsWithSpqr Z (spqrV1SessionUniformCoins Z.F K) idA idB

/-- Two-layer state monad threading `GameState St Msg C` over a per-session tracker `Tr`. -/
abbrev GenHaltedM (Tr St Msg C : Type) : Type → Type :=
  StateT (GameState St Msg C) (StateT Tr ProbComp)

@[simp] theorem liftStateT_run_state {σ τ α : Type}
    (x : StateT σ ProbComp α) (s : σ) (t : τ) :
    ((liftStateT (n := StateT τ ProbComp) x).run s).run t = (x.run s >>= fun a => pure (a, t)) := by
  change (StateT.lift (x.run s)).run t = _
  simp [StateT.run_lift, map_eq_bind_pure_comp]

@[simp] theorem stateT_lift_get_run {σ τ : Type} (s : σ) (t : τ) :
    ((StateT.lift get : StateT σ (StateT τ ProbComp) τ).run s).run t = pure ((t, s), t) := by
  simp [StateT.run_lift, StateT.run_get]

@[simp] theorem stateT_lift_set_run {σ τ : Type} (t' : τ) (s : σ) (t : τ) :
    ((StateT.lift (set t') : StateT σ (StateT τ ProbComp) PUnit).run s).run t =
      pure (((), s), t') := by
  simp [StateT.run_lift, StateT.run_set]

/-- Parametric per-session online halt tracker (`checkHalt`, `onSend`, `onAccept`). -/
structure HaltedTracker (Tr Coins C : Type) where
  checkHalt : Tr → Party → Coins → Option Tr
  onSend : Tr → Party → Coins → C → Tr
  onAccept : Tr → Party → C → Tr

def transmitRGenHalted {Tr Key St Msg Coins RCoins C : Type}
    [SampleableType Coins] (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) (GenHaltedM Tr St Msg C) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← (liftM (samIfNec r) : GenHaltedM Tr St Msg C (Coins × Bool))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let tr ← StateT.lift get
      match ht.checkHalt tr P coins with
      | some tr_h =>
        StateT.lift (set tr_h)
        return none
      | none =>
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        StateT.lift (set (ht.onSend tr P coins out.2))
        return some out.2

def challRGenHalted {Tr Key St Msg Coins RCoins C : Type}
    [SampleableType Coins] (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) (GenHaltedM Tr St Msg C) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← (liftM (samIfNec r) : GenHaltedM Tr St Msg C (Coins × Bool))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let tr ← StateT.lift get
      match ht.checkHalt tr P coins with
      | some tr_h =>
        StateT.lift (set tr_h)
        return none
      | none =>
        let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        StateT.lift (set (ht.onSend tr P coins out.2))
        return some out.2

def deliverRGenHalted {Tr Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType RCoins] (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) (GenHaltedM Tr St Msg C) :=
  fun ⟨Q, w⟩ => do
    let res ← liftStateT (deliverR sm cfg ⟨Q, w⟩)
    match res with
    | some (.accepted _ _ _) =>
      StateT.lift (modify fun tr => ht.onAccept tr Q w)
    | _ => pure ()
    return res

def oracleImplRGenHalted {Tr Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] [SampleableType RCoins] (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (spec St Msg Coins C) (GenHaltedM Tr St Msg C) :=
  transmitRGenHalted ht sm Δ qep cfg + challRGenHalted ht sm Δ qep cfg +
    deliverRGenHalted ht sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg)) (GenHaltedM Tr St Msg C)) +
    ((fun P => liftStateT (corrR cfg P)) : QueryImpl (Party →ₒ Option St) (GenHaltedM Tr St Msg C))

def runRGenHalted {Tr Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (initTr : Key → Tr) (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (b : Bool) (A : Adversary St Msg Coins C) :
    ProbComp ((Bool × GameState St Msg C) × Tr) := do
  let k ← ($ᵗ Key : ProbComp Key)
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (GenHaltedM Tr St Msg C) +
    oracleImplRGenHalted ht sm Δ qep cfg
  ((simulateQ impl A).run (initState sm.sendPart k b)).run (initTr k)

/-- Tracker-halted SM R-game returning `((b == b' || s.win), tr)`. -/
def gameRGenHalted {Tr Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]
    (initTr : Key → Tr) (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) : ProbComp (Bool × Tr) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((b', s), tr) ← runRGenHalted initTr ht sm Δ qep cfg b A
  return ((b == b' || s.win), tr)

theorem fst_gameRGenHalted_eq {Tr Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins] (initTr : Key → Tr) (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    Prod.fst <$> gameRGenHalted initTr ht sm Δ qep cfg A =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ((b', s), _) ← runRGenHalted initTr ht sm Δ qep cfg b A
        return (b == b' || s.win)) := by
  unfold gameRGenHalted
  rw [map_bind]
  congr 1; funext b
  rw [map_bind]
  rfl

/-- Online tracker-halted uniform-start PRG distinguisher on `(rk0, ck0)`. -/
def uniformStartDistinguisherGenHalted {Tr PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr PQC (List (BitVec 8))) (P : Params PQ PQC) (ℓ : ℕ)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (qep : ℕ)
    (A : Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((b', s), _) ←
    runRGenHalted (fun k => initTrRest k.2) ht
      (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep cfg b A
  return (b == b' || s.win)

/-- Online tracker-halted `eps0Event` in `libsignalSessionScheme`. -/
def eps0EventGenHalted {Tr PQ PQC Pt : Type} [Inhabited PQ] [SampleableType PQC]
    (initTr : (RootKey × BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr PQC (List (BitVec 8))) (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) : ProbComp Bool := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((_, s), _) ← runRGenHalted initTr ht (libsignalSessionScheme P ℓ encPt lam) 3 qep
    (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

/-- Online tracker-halted `epoch0Distinguisher` on `(rk0, ck0)`. -/
def epoch0DistinguisherGenHalted {Tr PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr PQC (List (BitVec 8))) (P : Params PQ PQC) (ℓ : ℕ)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (A : Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    PRGScheme.PRGAdversary (RootKey × BitVec 256) := fun rc => do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((_, s), _) ←
    runRGenHalted (fun k => initTrRest k.2) ht
      (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep
      (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

/-! ## Tracker homomorphisms and `mkStepDeliverTracker` -/

/-- Structure-preserving map `φ : Tr₁ → Tr₂` between two `HaltedTracker`s. -/
structure HaltedTrackerHom {Tr₁ Tr₂ Coins C : Type}
    (ht₁ : HaltedTracker Tr₁ Coins C) (ht₂ : HaltedTracker Tr₂ Coins C) (φ : Tr₁ → Tr₂) : Prop where
  checkHalt_map : ∀ tr P coins, (ht₁.checkHalt tr P coins).map φ = ht₂.checkHalt (φ tr) P coins
  onSend_map : ∀ tr P coins w, φ (ht₁.onSend tr P coins w) = ht₂.onSend (φ tr) P coins w
  onAccept_map : ∀ tr Q w, φ (ht₁.onAccept tr Q w) = ht₂.onAccept (φ tr) Q w

section Homomorphism

private theorem step_oracleImplRGenHalted_hom {Tr₁ Tr₂ Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    {ht₁ : HaltedTracker Tr₁ Coins C} {ht₂ : HaltedTracker Tr₂ Coins C} {φ : Tr₁ → Tr₂}
    (hφ : HaltedTrackerHom ht₁ ht₂ φ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (t : (unifSpec + spec St Msg Coins C).Domain) (s : GameState St Msg C) (tr : Tr₁) :
    Prod.map id φ <$>
      (((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (GenHaltedM Tr₁ St Msg C) +
          oracleImplRGenHalted ht₁ sm Δ qep cfg) t).run s).run tr) =
      (((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (GenHaltedM Tr₂ St Msg C) +
          oracleImplRGenHalted ht₂ sm Δ qep cfg) t).run s).run (φ tr)) := by
  rcases t with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change Prod.map id φ <$>
        (((StateT.lift (liftM (OracleSpec.query (spec := unifSpec) n)) :
            GenHaltedM Tr₁ St Msg C _).run s).run tr) =
      (((StateT.lift (liftM (OracleSpec.query (spec := unifSpec) n)) :
          GenHaltedM Tr₂ St Msg C _).run s).run (φ tr))
    simp [StateT.run_lift, StateT.run_monadLift, map_eq_bind_pure_comp]
  · simp only [QueryImpl.add_apply, oracleImplRGenHalted, transmitRGenHalted, StateT.run_bind,
      StateT.run_get, pure_bind]
    by_cases h1 : (!cfg.sendOK s P) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : s.win = true
      · simp [h2]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, map_eq_bind_pure_comp, bind_assoc, pure_bind]
        congr 1; funext cb
        cases s.epMgmt Δ qep P cb.2 with
        | none => simp
        | some s₁ =>
          simp only [StateT.run_bind, stateT_lift_get_run, pure_bind]
          have hchk := hφ.checkHalt_map tr P cb.1
          cases h₁ : ht₁.checkHalt tr P cb.1 <;> rw [h₁] at hchk
          · simp only [Option.map_none] at hchk
            rw [← hchk]
            simp [hφ.onSend_map]
          · simp only [Option.map_some] at hchk
            rw [← hchk]
            simp
  · simp only [QueryImpl.add_apply, oracleImplRGenHalted, challRGenHalted, StateT.run_bind,
      StateT.run_get, pure_bind]
    by_cases h1 : (!cfg.sendOK s P) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : s.win = true
      · simp [h2]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, map_eq_bind_pure_comp, bind_assoc, pure_bind]
        congr 1; funext cb
        cases s.epMgmt Δ qep P cb.2 with
        | none => simp
        | some s₁ =>
          dsimp only []
          by_cases hch : (!s₁.safeCh Δ P || !cfg.base.challAllowedIn (s₁.epoch P)) = true
          · simp [hch]
          · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_get_run,
              pure_bind]
            have hchk := hφ.checkHalt_map tr P cb.1
            cases h₁ : ht₁.checkHalt tr P cb.1 <;> rw [h₁] at hchk
            · simp only [Option.map_none] at hchk
              rw [← hchk]
              simp [hφ.onSend_map]
            · simp only [Option.map_some] at hchk
              rw [← hchk]
              simp
  · simp only [QueryImpl.add_apply, oracleImplRGenHalted, deliverRGenHalted, StateT.run_bind,
      liftStateT_run_state, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    congr 1; funext ⟨res, s'⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp [StateT.run_lift, StateT.run_modify, hφ.onAccept_map]
  · simp [QueryImpl.add_apply, oracleImplRGenHalted, liftStateT_run_state, map_eq_bind_pure_comp]
  · simp [QueryImpl.add_apply, oracleImplRGenHalted, liftStateT_run_state, map_eq_bind_pure_comp]

theorem simulateQ_oracleImplRGenHalted_hom {Tr₁ Tr₂ Key St Msg Coins RCoins C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    {ht₁ : HaltedTracker Tr₁ Coins C} {ht₂ : HaltedTracker Tr₂ Coins C} {φ : Tr₁ → Tr₂}
    (hφ : HaltedTrackerHom ht₁ ht₂ φ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (oa : AdversaryComp St Msg Coins C α) (s : GameState St Msg C) (tr : Tr₁) :
    Prod.map id φ <$>
      (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (GenHaltedM Tr₁ St Msg C) +
          oracleImplRGenHalted ht₁ sm Δ qep cfg) oa).run s).run tr) =
      (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (GenHaltedM Tr₂ St Msg C) +
          oracleImplRGenHalted ht₂ sm Δ qep cfg) oa).run s).run (φ tr)) := by
  induction oa using OracleComp.inductionOn generalizing s tr with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [← step_oracleImplRGenHalted_hom hφ sm Δ qep cfg t s tr]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, Prod.map_fst,
      Prod.map_snd, id_eq]
    congr 1; funext z
    simpa [map_eq_bind_pure_comp] using ih z.1.1 z.1.2 z.2

theorem runRGenHalted_hom_eq {Tr₁ Tr₂ Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    {initTr₁ : Key → Tr₁} {initTr₂ : Key → Tr₂}
    {ht₁ : HaltedTracker Tr₁ Coins C} {ht₂ : HaltedTracker Tr₂ Coins C} {φ : Tr₁ → Tr₂}
    (hinit : ∀ k, φ (initTr₁ k) = initTr₂ k) (hφ : HaltedTrackerHom ht₁ ht₂ φ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (b : Bool) (A : Adversary St Msg Coins C) :
    Prod.map id φ <$> runRGenHalted initTr₁ ht₁ sm Δ qep cfg b A =
      runRGenHalted initTr₂ ht₂ sm Δ qep cfg b A := by
  unfold runRGenHalted
  rw [map_bind]
  congr 1; funext k
  rw [← hinit k]
  exact simulateQ_oracleImplRGenHalted_hom hφ sm Δ qep cfg A (initState sm.sendPart k b) (initTr₁ k)

theorem fst_runRGenHalted_eq_of_hom {Tr₁ Tr₂ Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    {initTr₁ : Key → Tr₁} {initTr₂ : Key → Tr₂}
    {ht₁ : HaltedTracker Tr₁ Coins C} {ht₂ : HaltedTracker Tr₂ Coins C} {φ : Tr₁ → Tr₂}
    (hinit : ∀ k, φ (initTr₁ k) = initTr₂ k) (hφ : HaltedTrackerHom ht₁ ht₂ φ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (b : Bool) (A : Adversary St Msg Coins C) :
    Prod.fst <$> runRGenHalted initTr₁ ht₁ sm Δ qep cfg b A =
      Prod.fst <$> runRGenHalted initTr₂ ht₂ sm Δ qep cfg b A := by
  rw [← runRGenHalted_hom_eq hinit hφ sm Δ qep cfg b A, Functor.map_map]
  rfl

theorem fst_gameRGenHalted_eq_of_hom {Tr₁ Tr₂ Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    {initTr₁ : Key → Tr₁} {initTr₂ : Key → Tr₂}
    {ht₁ : HaltedTracker Tr₁ Coins C} {ht₂ : HaltedTracker Tr₂ Coins C} {φ : Tr₁ → Tr₂}
    (hinit : ∀ k, φ (initTr₁ k) = initTr₂ k) (hφ : HaltedTrackerHom ht₁ ht₂ φ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    Prod.fst <$> gameRGenHalted initTr₁ ht₁ sm Δ qep cfg A =
      Prod.fst <$> gameRGenHalted initTr₂ ht₂ sm Δ qep cfg A := by
  rw [fst_gameRGenHalted_eq, fst_gameRGenHalted_eq]
  congr 1; funext b
  have h := fst_runRGenHalted_eq_of_hom hinit hφ sm Δ qep cfg b A
  simpa [map_eq_bind_pure_comp, bind_assoc] using
    congrArg (fun m => m >>= fun bs => pure (b == bs.1 || bs.2.win)) h

theorem uniformStartDistinguisherGenHalted_eq_of_hom {Tr₁ Tr₂ PQ PQC : Type}
    [Inhabited PQ] [SampleableType PQC]
    {initTrRest₁ : (BitVec 256 × BitVec 256 × BitVec 256) → Tr₁}
    {initTrRest₂ : (BitVec 256 × BitVec 256 × BitVec 256) → Tr₂}
    {ht₁ : HaltedTracker Tr₁ PQC (List (BitVec 8))}
    {ht₂ : HaltedTracker Tr₂ PQC (List (BitVec 8))} {φ : Tr₁ → Tr₂}
    (hinit : ∀ rest, φ (initTrRest₁ rest) = initTrRest₂ rest) (hφ : HaltedTrackerHom ht₁ ht₂ φ)
    (P : Params PQ PQC) (ℓ : ℕ)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (qep : ℕ)
    (A : Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    uniformStartDistinguisherGenHalted initTrRest₁ ht₁ P ℓ cfg qep A =
      uniformStartDistinguisherGenHalted initTrRest₂ ht₂ P ℓ cfg qep A := by
  funext rc
  unfold uniformStartDistinguisherGenHalted
  congr 1; funext b
  have h := fst_runRGenHalted_eq_of_hom (fun k => hinit k.2) hφ
    (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep cfg b A
  simpa [map_eq_bind_pure_comp, bind_assoc] using
    congrArg (fun m => m >>= fun bs => pure (b == bs.1 || bs.2.win)) h

theorem eps0EventGenHalted_eq_of_hom {Tr₁ Tr₂ PQ PQC Pt : Type}
    [Inhabited PQ] [SampleableType PQC]
    {initTr₁ : (RootKey × BitVec 256 × BitVec 256 × BitVec 256) → Tr₁}
    {initTr₂ : (RootKey × BitVec 256 × BitVec 256 × BitVec 256) → Tr₂}
    {ht₁ : HaltedTracker Tr₁ PQC (List (BitVec 8))}
    {ht₂ : HaltedTracker Tr₂ PQC (List (BitVec 8))} {φ : Tr₁ → Tr₂}
    (hinit : ∀ k, φ (initTr₁ k) = initTr₂ k) (hφ : HaltedTrackerHom ht₁ ht₂ φ)
    (P : Params PQ PQC) (ℓ : ℕ) (encPt : Pt → List (BitVec 8)) (lam : Pt)
    (onImage : List (BitVec 8) → Bool) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    eps0EventGenHalted initTr₁ ht₁ P ℓ encPt lam onImage qep A =
      eps0EventGenHalted initTr₂ ht₂ P ℓ encPt lam onImage qep A := by
  unfold eps0EventGenHalted
  congr 1; funext b
  have h := fst_runRGenHalted_eq_of_hom hinit hφ (libsignalSessionScheme P ℓ encPt lam) 3 qep
    (configEpoch0Distinguisher onImage) b A
  simpa [map_eq_bind_pure_comp, bind_assoc] using
    congrArg (fun m => m >>= fun bs =>
      pure ((decide (0 < bs.2.maxAcc .A 0) || bs.2.win) && !(bs.2.corrs.contains (.B, 0)))) h

theorem epoch0DistinguisherGenHalted_eq_of_hom {Tr₁ Tr₂ PQ PQC : Type}
    [Inhabited PQ] [SampleableType PQC]
    {initTrRest₁ : (BitVec 256 × BitVec 256 × BitVec 256) → Tr₁}
    {initTrRest₂ : (BitVec 256 × BitVec 256 × BitVec 256) → Tr₂}
    {ht₁ : HaltedTracker Tr₁ PQC (List (BitVec 8))}
    {ht₂ : HaltedTracker Tr₂ PQC (List (BitVec 8))} {φ : Tr₁ → Tr₂}
    (hinit : ∀ rest, φ (initTrRest₁ rest) = initTrRest₂ rest) (hφ : HaltedTrackerHom ht₁ ht₂ φ)
    (P : Params PQ PQC) (ℓ : ℕ) (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (A : Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    epoch0DistinguisherGenHalted initTrRest₁ ht₁ P ℓ onImage qep A =
      epoch0DistinguisherGenHalted initTrRest₂ ht₂ P ℓ onImage qep A := by
  funext rc
  unfold epoch0DistinguisherGenHalted
  congr 1; funext b
  have h := fst_runRGenHalted_eq_of_hom (fun k => hinit k.2) hφ
    (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) 3 qep
    (configEpoch0Distinguisher onImage) b A
  simpa [map_eq_bind_pure_comp, bind_assoc] using
    congrArg (fun m => m >>= fun bs =>
      pure ((decide (0 < bs.2.maxAcc .A 0) || bs.2.win) && !(bs.2.corrs.contains (.B, 0)))) h

end Homomorphism

/-- Build a `HaltedTracker (T0 × List (C × Party)) (BitVec 512) C` from a per-send step `stepSend`,
halt predicate `candSome`, sticky latch `candLatch`, and chronological delivery step `stepDeliver`
(indexing `honestWires.reverse.findIdx?`). -/
def mkStepDeliverTracker {T0 C : Type} [DecidableEq C]
    (stepSend : T0 → Party → BitVec 512 → T0) (candSome : T0 → Bool)
    (candLatch : T0 → T0 → T0) (stepDeliver : T0 → Party → ℕ → T0) :
    HaltedTracker (T0 × List (C × Party)) (BitVec 512) C where
  checkHalt := fun ⟨tr, hw⟩ P coins =>
    let tr' := stepSend tr P coins
    if candSome tr' then some (candLatch tr tr', hw) else none
  onSend := fun ⟨tr, hw⟩ P coins w => (stepSend tr P coins, (w, P) :: hw)
  onAccept := fun ⟨tr, hw⟩ Q w =>
    match hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
    | some j => (stepDeliver tr Q j, hw)
    | none => (tr, hw)

section StepDeliverEq

theorem transmitRStepDeliver_eq_genHalted {T0 Key St Msg RCoins C : Type} [DecidableEq C]
    (stepSend : T0 → Party → BitVec 512 → T0) (candSome : T0 → Bool)
    (candLatch : T0 → T0 → T0) (stepDeliver : T0 → Party → ℕ → T0)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    ((fun ⟨P, m, r⟩ => do
      let s ← get
      if !(cfg.sendOK s P) then return none
      if s.win then return none
      let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
      match s.epMgmt Δ qep P bad with
      | none => return none
      | some s₁ =>
        let (tr, hw) ← StateT.lift get
        let tr' := stepSend tr P coins
        if candSome tr' then
          StateT.lift (set (candLatch tr tr', hw))
          return none
        else
          let out := sm.send (s₁.st P) m coins
          set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
          StateT.lift (set (tr', (out.2, P) :: hw))
          return some out.2) :
      QueryImpl ((Party × Msg × Option (BitVec 512)) →ₒ Option C)
        (GenHaltedM (T0 × List (C × Party)) St Msg C)) =
      transmitRGenHalted (mkStepDeliverTracker stepSend candSome candLatch stepDeliver)
        sm Δ qep cfg := by
  funext ⟨P, m, r⟩
  apply StateT.ext; intro s
  apply StateT.ext; intro ⟨tr, hw⟩
  unfold transmitRGenHalted mkStepDeliverTracker
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 : (!cfg.sendOK s P) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : s.win = true
    · simp [h2]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => rfl
      | some s₁ =>
        simp only [StateT.run_bind, stateT_lift_get_run, pure_bind]
        cases candSome (stepSend tr P coins) <;> simp

theorem challRStepDeliver_eq_genHalted {T0 Key St Msg RCoins C : Type} [DecidableEq C]
    (stepSend : T0 → Party → BitVec 512 → T0) (candSome : T0 → Bool)
    (candLatch : T0 → T0 → T0) (stepDeliver : T0 → Party → ℕ → T0)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    ((fun ⟨P, m₀, m₁, r⟩ => do
      let s ← get
      if !(cfg.sendOK s P) then return none
      if s.win then return none
      let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
      match s.epMgmt Δ qep P bad with
      | none => return none
      | some s₁ =>
        if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
        let (tr, hw) ← StateT.lift get
        let tr' := stepSend tr P coins
        if candSome tr' then
          StateT.lift (set (candLatch tr tr', hw))
          return none
        else
          let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
          let out := sm.send (s₁.st P) m coins
          set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
          StateT.lift (set (tr', (out.2, P) :: hw))
          return some out.2) :
      QueryImpl ((Party × Msg × Msg × Option (BitVec 512)) →ₒ Option C)
        (GenHaltedM (T0 × List (C × Party)) St Msg C)) =
      challRGenHalted (mkStepDeliverTracker stepSend candSome candLatch stepDeliver)
        sm Δ qep cfg := by
  funext ⟨P, m₀, m₁, r⟩
  apply StateT.ext; intro s
  apply StateT.ext; intro ⟨tr, hw⟩
  unfold challRGenHalted mkStepDeliverTracker
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 : (!cfg.sendOK s P) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : s.win = true
    · simp [h2]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => rfl
      | some s₁ =>
        dsimp only []
        by_cases hch : (!s₁.safeCh Δ P || !cfg.base.challAllowedIn (s₁.epoch P)) = true
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_get_run,
            pure_bind]
          cases candSome (stepSend tr P coins) <;> simp

theorem deliverRStepDeliver_eq_genHalted {T0 Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (stepSend : T0 → Party → BitVec 512 → T0) (candSome : T0 → Bool)
    (candLatch : T0 → T0 → T0) (stepDeliver : T0 → Party → ℕ → T0)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (cfg : ConfigR St Msg C) :
    ((fun ⟨Q, w⟩ => do
      let (_, hw) ← StateT.lift get
      let j? := hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
      let res ← liftStateT (deliverR sm cfg (Q, w))
      match res, j? with
      | some (.accepted _ _ _), some j =>
        StateT.lift (modify fun ⟨tr, hw'⟩ => (stepDeliver tr Q j, hw'))
      | _, _ => pure ()
      return res) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (GenHaltedM (T0 × List (C × Party)) St Msg C)) =
      deliverRGenHalted (mkStepDeliverTracker stepSend candSome candLatch stepDeliver) sm cfg := by
  funext ⟨Q, w⟩
  apply StateT.ext; intro s
  apply StateT.ext; intro ⟨tr, hw⟩
  unfold deliverRGenHalted mkStepDeliverTracker
  simp only [StateT.run_bind, stateT_lift_get_run, liftStateT_run_state, pure_bind, bind_assoc]
  congr 1; funext ⟨res, s'⟩
  cases res with
  | none => simp
  | some rr =>
    cases rr <;> simp only [StateT.run_pure]
    cases hidx : hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) <;>
      simp [hidx, StateT.run_lift, StateT.run_modify]

end StepDeliverEq

/-! ## `Adversary.refuseCorrB0` commutation on `gameRGenHalted` -/

section RefuseCoupling

variable {Tr Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
  [SampleableType Coins] [SampleableType RCoins]

private abbrev fullImplGGenHalted (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (unifSpec + spec St Msg Coins C) (GenHaltedM Tr St Msg C) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (GenHaltedM Tr St Msg C) +
    oracleImplRGenHalted ht sm Δ qep cfg

private theorem stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type} (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

private theorem transmitRGenHalted_refuse_eq
    (ht : HaltedTracker Tr Coins C) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (x : Party × Msg × Option Coins) (s : GameState St Msg C) (tr : Tr) :
    (((simulateQ (fullImplGGenHalted ht sm Δ qep cfg)
        ((refuseTransmit x).run (RefuseState.ofGameState s))).run s).run tr) =
      (fun z => (((z.1.1, RefuseState.ofGameState z.1.2), z.1.2), z.2)) <$>
        (((transmitRGenHalted ht sm Δ qep (withNoCorrB0 cfg) x).run s).run tr) := by
  rcases x with ⟨P, m, r⟩
  unfold refuseTransmit
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, simulateQ_bind,
    transmitQuery, simulateQ_oracleSpec_query, fullImplGGenHalted, QueryImpl.add_apply,
    oracleImplRGenHalted]
  rw [map_eq_bind_pure_comp]
  unfold transmitRGenHalted withNoCorrB0
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hok : cfg.sendOK s P = true
  · by_cases hwin : s.win = true
    · simp [hok, hwin]
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwin,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      congr 1; funext cb
      cases hep : s.epMgmt Δ qep P cb.2 with
      | none => simp
      | some s₁ =>
        simp only [StateT.run_bind, stateT_lift_get_run, pure_bind]
        cases ht.checkHalt tr P cb.1 with
        | some tr_h => simp
        | none =>
          have hrec := ofGameState_record_epMgmt hep (sm.send (s₁.st P) m cb.1).1 m
            (sm.send (s₁.st P) m cb.1).2 false
          simp [hrec]
  · simp [hok]

private theorem challRGenHalted_refuse_eq
    (ht : HaltedTracker Tr Coins C) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (x : Party × Msg × Msg × Option Coins) (s : GameState St Msg C) (tr : Tr) :
    (((simulateQ (fullImplGGenHalted ht sm Δ qep cfg)
        ((refuseChall x).run (RefuseState.ofGameState s))).run s).run tr) =
      (fun z => (((z.1.1, RefuseState.ofGameState z.1.2), z.1.2), z.2)) <$>
        (((challRGenHalted ht sm Δ qep (withNoCorrB0 cfg) x).run s).run tr) := by
  rcases x with ⟨P, m₀, m₁, r⟩
  unfold refuseChall
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, simulateQ_bind,
    challQuery, simulateQ_oracleSpec_query, fullImplGGenHalted, QueryImpl.add_apply,
    oracleImplRGenHalted]
  rw [map_eq_bind_pure_comp]
  unfold challRGenHalted withNoCorrB0
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hok : cfg.sendOK s P = true
  · by_cases hwin : s.win = true
    · simp [hok, hwin]
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwin,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      congr 1; funext cb
      cases hep : s.epMgmt Δ qep P cb.2 with
      | none => simp
      | some s₁ =>
        dsimp only []
        by_cases hch : (!s₁.safeCh Δ P || !cfg.base.challAllowedIn (s₁.epoch P)) = true
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_get_run,
            pure_bind]
          cases ht.checkHalt tr P cb.1 with
          | some tr_h => simp
          | none =>
            set msg := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
            have hrec := ofGameState_record_epMgmt hep (sm.send (s₁.st P) msg cb.1).1 msg
              (sm.send (s₁.st P) msg cb.1).2 true
            simp [hrec]
  · simp [hok]

private theorem deliverRGenHalted_refuse_eq
    (ht : HaltedTracker Tr Coins C) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (x : Party × C) (s : GameState St Msg C) (tr : Tr) :
    (((simulateQ (fullImplGGenHalted ht sm Δ qep cfg)
        ((refuseDeliver x).run (RefuseState.ofGameState s))).run s).run tr) =
      (fun z => (((z.1.1, RefuseState.ofGameState z.1.2), z.1.2), z.2)) <$>
        (((deliverRGenHalted ht sm (withNoCorrB0 cfg) x).run s).run tr) := by
  rcases x with ⟨P, c⟩
  unfold refuseDeliver
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, simulateQ_bind,
    deliverQuery, simulateQ_oracleSpec_query, fullImplGGenHalted, QueryImpl.add_apply,
    oracleImplRGenHalted]
  rw [map_eq_bind_pure_comp]
  unfold deliverRGenHalted deliverR withNoCorrB0
  simp only [StateT.run_bind, liftStateT_run_state, StateT.run_get, pure_bind, bind_assoc]
  cases hwin : s.win
  · cases htr : s.inTransit P.other c with
    | none => simp
    | some r =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind]
      congr 1; funext rc
      cases hrcv : sm.receive (s.st P) c rc with
      | none =>
        dsimp only []
        split_ifs <;> simp [simulateQ_pure]
      | some v =>
        rcases v with ⟨st', t', i', m'⟩
        dsimp only []
        have hdel := onDeliver_ofGameState_of_inTransit htr st'
        split_ifs <;> simp [hdel, simulateQ_pure, StateT.run_lift, StateT.run_modify]
  · simp

private theorem injectRGenHalted_refuse_eq
    (ht : HaltedTracker Tr Coins C) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (x : Party × C) (s : GameState St Msg C) (tr : Tr) :
    (((simulateQ (fullImplGGenHalted ht sm Δ qep cfg)
        ((refuseInject x).run (RefuseState.ofGameState s))).run s).run tr) =
      (fun z => (((z.1.1, RefuseState.ofGameState z.1.2), z.1.2), z.2)) <$>
        (((liftStateT (injectR sm Δ qep (withNoCorrB0 cfg) x) :
            GenHaltedM Tr St Msg C _).run s).run tr) := by
  rcases x with ⟨P, c⟩
  unfold refuseInject
  simp only [StateT.run_bind, stateT_lift_run, bind_assoc, pure_bind, simulateQ_bind,
    injectQuery, simulateQ_oracleSpec_query, fullImplGGenHalted, QueryImpl.add_apply,
    oracleImplRGenHalted]
  rw [map_eq_bind_pure_comp]
  unfold injectR withNoCorrB0
  simp only [StateT.run_bind, liftStateT_run_state, StateT.run_get, pure_bind, bind_assoc]
  by_cases hcond : (s.win || (s.inTransit P.other c).isSome || !s.safeInj Δ || !cfg.injOK c) = true
  · simp [hcond]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_assoc, pure_bind]
    congr 1; funext rc
    cases hrcv : sm.receive (s.st P) c rc with
    | none => simp [simulateQ_pure]
    | some v =>
      rcases v with ⟨st', t', i', m'⟩
      dsimp only []
      split_ifs <;> simp [ofGameState_accept, simulateQ_pure]

private theorem corrRGenHalted_refuse_eq
    (ht : HaltedTracker Tr Coins C) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (P : Party) (s : GameState St Msg C) (tr : Tr) :
    (((simulateQ (fullImplGGenHalted ht sm Δ qep cfg)
        ((refuseCorr P).run (RefuseState.ofGameState s))).run s).run tr) =
      (fun z => (((z.1.1, RefuseState.ofGameState z.1.2), z.1.2), z.2)) <$>
        (((liftStateT (corrR (withNoCorrB0 cfg) P) : GenHaltedM Tr St Msg C _).run s).run tr) := by
  rw [liftStateT_run_state]
  unfold refuseCorr corrR withNoCorrB0 noBobCorrInEpoch0 noBobCorrWhileAliceBelowEpoch10
  have hepB : (RefuseState.ofGameState s).epoch .B = s.epoch .B := rfl
  have hepA : (RefuseState.ofGameState s).epoch .A = s.epoch .A := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hepB, hepA]
  by_cases hB : ((P == .B && (s.epoch .B == 0)) || (P == .B && decide (s.epoch .A < 10))) = true
  · rcases Bool.or_eq_true_iff.mp hB with hB0 | hBW
    · simp [hB0]
    · simp [hBW]
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
      simulateQ_oracleSpec_query, fullImplGGenHalted, QueryImpl.add_apply, oracleImplRGenHalted,
      corrR, liftStateT_run_state, StateT.run_bind, StateT.run_get,
      pure_bind, map_eq_bind_pure_comp]
    by_cases hcond :
        (s.win || !s.corrAllowed P || (cfg.r1 && inWindow s P) || !cfg.corrOK s P) = true <;>
      { simp only [hcond, ↓reduceIte]; simp }

private theorem refuseCorrB0_genHalted_step_eq
    (ht : HaltedTracker Tr Coins C) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    (s : GameState St Msg C) (tr : Tr) :
    (((simulateQ (fullImplGGenHalted ht sm Δ qep cfg)
        ((refuseCorrB0Impl t).run (RefuseState.ofGameState s))).run s).run tr) =
      (fun z => (((z.1.1, RefuseState.ofGameState z.1.2), z.1.2), z.2)) <$>
        (((fullImplGGenHalted ht sm Δ qep (withNoCorrB0 cfg) t).run s).run tr) := by
  rcases t with n | ((((x | x) | x) | x) | P)
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, stateT_lift_run, simulateQ_bind,
      simulateQ_pure, simulateQ_oracleSpec_query, fullImplGGenHalted]
    change ((((StateT.lift (liftM (OracleSpec.query (spec := unifSpec) n)) :
          GenHaltedM Tr St Msg C _) >>=
        fun u => pure (u, RefuseState.ofGameState s)).run s).run tr) =
      (fun z => (((z.1.1, RefuseState.ofGameState z.1.2), z.1.2), z.2)) <$>
        (((StateT.lift (liftM (OracleSpec.query (spec := unifSpec) n)) :
          GenHaltedM Tr St Msg C _).run s).run tr)
    simp [StateT.run_lift, StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc]
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplGGenHalted, oracleImplRGenHalted]
    exact transmitRGenHalted_refuse_eq ht sm Δ qep cfg x s tr
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplGGenHalted, oracleImplRGenHalted]
    exact challRGenHalted_refuse_eq ht sm Δ qep cfg x s tr
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplGGenHalted, oracleImplRGenHalted]
    exact deliverRGenHalted_refuse_eq ht sm Δ qep cfg x s tr
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplGGenHalted, oracleImplRGenHalted]
    exact injectRGenHalted_refuse_eq ht sm Δ qep cfg x s tr
  · simp only [refuseCorrB0Impl, QueryImpl.add_apply, fullImplGGenHalted, oracleImplRGenHalted]
    exact corrRGenHalted_refuse_eq ht sm Δ qep cfg P s tr

private theorem simulateQ_refuseCorrB0_genHalted_run_eq
    (ht : HaltedTracker Tr Coins C) (sm : SMSchemeR Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    {α : Type} (oa : AdversaryComp St Msg Coins C α)
    (s : GameState St Msg C) (tr : Tr) :
    Prod.map (Prod.map Prod.fst id) id <$>
      (((simulateQ (fullImplGGenHalted ht sm Δ qep cfg)
        ((simulateQ refuseCorrB0Impl oa).run (RefuseState.ofGameState s))).run s).run tr) =
      (((simulateQ (fullImplGGenHalted ht sm Δ qep (withNoCorrB0 cfg)) oa).run s).run tr) := by
  induction oa using OracleComp.inductionOn generalizing s tr with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [refuseCorrB0_genHalted_step_eq ht sm Δ qep cfg t s tr, bind_map_left,
      map_eq_bind_pure_comp, bind_assoc]
    apply bind_congr_of_support
    intro z _
    dsimp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    rw [← ih z.1.1 z.1.2 z.2, map_eq_bind_pure_comp]

theorem runRGenHalted_withNoCorrB0_eq [SampleableType Key]
    (initTr : Key → Tr) (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (_hsendOK : cfg.sendOK = noBobSendInEpoch0 := by rfl)
    (b : Bool) (A : Adversary St Msg Coins C) :
    runRGenHalted initTr ht sm Δ qep (withNoCorrB0 cfg) b A =
      runRGenHalted initTr ht sm Δ qep cfg b A.refuseCorrB0 := by
  unfold runRGenHalted Adversary.refuseCorrB0
  congr 1; funext k
  dsimp only []
  have hinit : RefuseState.ofGameState (initState sm.sendPart k b) = {} := rfl
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, StateT.run_map, ← hinit]
  exact (simulateQ_refuseCorrB0_genHalted_run_eq ht sm Δ qep cfg A
    (initState sm.sendPart k b) (initTr k)).symm

/-- Running `A` in `withNoCorrB0 cfg` under `gameRGenHalted` equals running `A.refuseCorrB0` in
`cfg`. -/
theorem gameRGenHalted_withNoCorrB0_eq [SampleableType Key]
    (initTr : Key → Tr) (ht : HaltedTracker Tr Coins C)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (hsendOK : cfg.sendOK = noBobSendInEpoch0 := by rfl)
    (A : Adversary St Msg Coins C) :
    gameRGenHalted initTr ht sm Δ qep (withNoCorrB0 cfg) A =
      gameRGenHalted initTr ht sm Δ qep cfg A.refuseCorrB0 := by
  unfold gameRGenHalted
  congr 1; funext b
  rw [runRGenHalted_withNoCorrB0_eq initTr ht sm Δ qep cfg hsendOK b A]

end RefuseCoupling

/-! ## Halted uniform-start PRG hop -/

section UniformStartGenHalted

variable {Tr PQ PQC Pt : Type} [Inhabited PQ] [SampleableType PQC]

theorem evalDist_gameRGenHalted_libSessionR_eq_prgReal
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr PQC (List (BitVec 8))) (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (qep : ℕ)
    (A : Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    𝒟[Prod.fst <$> gameRGenHalted (fun k => initTrRest k.2) ht
        (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg A] =
      𝒟[(rootKdfAsPrg P.C.F (encPt lam)).prgRealExperiment
        (uniformStartDistinguisherGenHalted initTrRest ht P ℓ cfg qep A)] := by
  have horacle : ∀ rk0 ck0,
      oracleImplRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep cfg =
        oracleImplRGenHalted ht (libsignalSessionScheme P ℓ encPt lam) 3 qep cfg := by
    intro rk0 ck0
    unfold oracleImplRGenHalted transmitRGenHalted challRGenHalted deliverRGenHalted
      deliverR injectR corrR libsignalSessionSchemeFromEpoch0Keys libsignalSessionScheme
    rfl
  have hinit : ∀ (rk rk' : RootKey) (rest : BitVec 256 × BitVec 256 × BitVec 256) (b : Bool),
      initState (libsignalSessionSchemeFromEpoch0Keys P ℓ (rootKdf P.C.F rk (encPt lam)).1
          (rootKdf P.C.F rk (encPt lam)).2).sendPart (rk', rest) b =
        initState (libsignalSessionScheme P ℓ encPt lam).sendPart (rk, rest) b := by
    intro rk rk' rest b
    unfold initState SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libsignalSessionScheme
    rfl
  rw [fst_gameRGenHalted_eq]
  unfold PRGScheme.prgRealExperiment rootKdfAsPrg uniformStartDistinguisherGenHalted runRGenHalted
  simp only [bind_assoc, horacle]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ RootKey) ($ᵗ Bool)]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bindU]
  refine evalDist_bind_congr ($ᵗ RootKey) _ _ fun rk => ?_
  symm
  rw [sample_prod_bindU]
  simp only [hinit rk]
  exact OracleComp.evalDist_bind_const ($ᵗ RootKey) _

theorem evalDist_gameRGenHalted_libSessionU_eq_prgIdeal
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr PQC (List (BitVec 8))) (P : Params PQ PQC) (ℓ : ℕ)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8))) (qep : ℕ)
    (A : Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    𝒟[Prod.fst <$> gameRGenHalted (fun k => initTrRest k.2) ht (libSessionU P ℓ) 3 qep cfg A] =
      𝒟[PRGScheme.prgIdealExperiment
        (uniformStartDistinguisherGenHalted initTrRest ht P ℓ cfg qep A)] := by
  have horacle : ∀ rk0 ck0,
      oracleImplRGenHalted ht (libsignalSessionSchemeFromEpoch0Keys P ℓ rk0 ck0) 3 qep cfg =
        oracleImplRGenHalted ht (libSessionU P ℓ) 3 qep cfg := by
    intro rk0 ck0
    unfold oracleImplRGenHalted transmitRGenHalted challRGenHalted deliverRGenHalted
      deliverR injectR corrR libsignalSessionSchemeFromEpoch0Keys libSessionU
    rfl
  have hinit : ∀ (rc : RootKey × BitVec 256) (rk' : RootKey)
      (rest : BitVec 256 × BitVec 256 × BitVec 256) (b : Bool),
      initState (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2).sendPart (rk', rest) b =
        initState (libSessionU P ℓ).sendPart (rc, rest) b := by
    intro rc rk' rest b
    unfold initState SMSchemeR.sendPart libsignalSessionSchemeFromEpoch0Keys libSessionU
    rfl
  rw [fst_gameRGenHalted_eq]
  unfold PRGScheme.prgIdealExperiment uniformStartDistinguisherGenHalted runRGenHalted
  simp only [bind_assoc, horacle]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ (RootKey × BitVec 256)) ($ᵗ Bool)]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bindU]
  refine evalDist_bind_congr ($ᵗ (RootKey × BitVec 256)) _ _ fun rc => ?_
  symm
  rw [sample_prod_bindU]
  simp only [hinit rc]
  exact OracleComp.evalDist_bind_const ($ᵗ RootKey) _

/-- Halted U-mixture hop (`paramsIdsWithSpqr`): rewrites `configRefuseEarlyBobCorr` via
`Adversary.refuseCorrB0` and transitions from uniform start to KDF start via
`uniformStartDistinguisherGenHalted`. -/
theorem boolBias_mixUGenHaltedWithSpqr_le {Tr Pt α : Type}
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr (BitVec 512) Bytes)
    (Z : Crypto) (spqr : Spqr Bytes (BitVec 512)) {ℓ : ℕ}
    (encPt : Pt → Bytes) (lam : Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    (𝒟[oa >>= fun o =>
        Prod.fst <$> gameRGenHalted (fun k => initTrRest k.2) ht
          (sessionSchemeU (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= fun o =>
          Prod.fst <$> gameRGenHalted (fun k => initTrRest k.2) ht
            (libsignalSessionScheme (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ encPt lam) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
            (A o).refuseCorrB0]).boolBias
        + 2 * (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => uniformStartDistinguisherGenHalted initTrRest ht
            (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
            (A o).refuseCorrB0) := by
  have hU : 𝒟[oa >>= fun o =>
        Prod.fst <$> gameRGenHalted (fun k => initTrRest k.2) ht
          (sessionSchemeU (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)] =
      𝒟[PRGScheme.prgIdealExperiment
        (prgAvg oa fun o => uniformStartDistinguisherGenHalted initTrRest ht
          (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
          (A o).refuseCorrB0)] := by
    rw [prgIdeal_avg]
    refine evalDist_bind_congr _ _ _ fun o => ?_
    have hsm : sessionSchemeU (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ =
        libSessionU (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ := rfl
    have hcfg : (configRefuseEarlyBobCorr decT encT :
        ConfigR (GhostState Bytes) (Plain ℓ) Bytes) =
        withNoCorrB0 (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) := rfl
    rw [hsm, hcfg,
      gameRGenHalted_withNoCorrB0_eq _ ht _ 3 qep _ rfl (A o),
      evalDist_gameRGenHalted_libSessionU_eq_prgIdeal]
  have hR : 𝒟[oa >>= fun o =>
        Prod.fst <$> gameRGenHalted (fun k => initTrRest k.2) ht
          (libsignalSessionScheme (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ encPt lam) 3 qep
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
          (A o).refuseCorrB0] =
      𝒟[(rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment
        (prgAvg oa fun o => uniformStartDistinguisherGenHalted initTrRest ht
          (paramsIdsWithSpqr Z spqr (ida o) (idb o)) ℓ
          (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
          (A o).refuseCorrB0)] := by
    rw [prgReal_avg]
    exact evalDist_bind_congr _ _ _ fun o =>
      evalDist_gameRGenHalted_libSessionR_eq_prgReal initTrRest ht _ ℓ encPt lam _ qep _
  unfold PRGScheme.prgAdvantage
  rw [hU, hR, Measure.boolDist_comm 𝒟[(rootKdfAsPrg Z.F (encPt lam)).prgRealExperiment _]]
  exact boolBias_le_add_two_mul_boolDist _ _

theorem boolBias_mixUGenHalted_le_v1 {Tr Pt α : Type}
    (initTrRest : (BitVec 256 × BitVec 256 × BitVec 256) → Tr)
    (ht : HaltedTracker Tr (BitVec 512) Bytes)
    (Z : Crypto) (K : MlKem) {ℓ : ℕ}
    (encPt : Pt → Bytes) (lam : Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    (𝒟[oa >>= fun o =>
        Prod.fst <$> gameRGenHalted (fun k => initTrRest k.2) ht
          (sessionSchemeU (paramsV1 Z K (ida o) (idb o)) ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= fun o =>
          Prod.fst <$> gameRGenHalted (fun k => initTrRest k.2) ht
            (libsignalSessionScheme (paramsV1 Z K (ida o) (idb o)) ℓ encPt lam) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
            (A o).refuseCorrB0]).boolBias
        + 2 * (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prgAvg oa fun o => uniformStartDistinguisherGenHalted initTrRest ht
            (paramsV1 Z K (ida o) (idb o)) ℓ
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep
            (A o).refuseCorrB0) :=
  boolBias_mixUGenHaltedWithSpqr_le initTrRest ht Z (spqrV1SessionUniformCoins Z.F K) encPt lam
    encT decT qep oa ida idb A

end UniformStartGenHalted

end Computational.Proofs.E2E.HaltedSessionCore
