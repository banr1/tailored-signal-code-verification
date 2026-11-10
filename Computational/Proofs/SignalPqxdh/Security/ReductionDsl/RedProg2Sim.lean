/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.PqxdhTables
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndSigKem
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Potential
public import Computational.Proofs.GameHop.ReductionDsl.TwoStageBridge
import VCVio.EvalDist.Monad.Basic

/-!
# Simulation Lemmas for Two-Stage Reductions

Protocol specialization of `Computational.Proofs.GameHop.ReductionDsl.TwoStageBridge` onto
`PrimBaseSpec` (`pqPrimIface`).
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh.Security.ReductionDsl
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open OracleSpec OracleComp
open Computational.Proofs.GameHop.ReductionDsl

export TwoStageBridge (RedProg2State midOfStepUntilPause stepUntilPauseOfMid
  midOfStepUntilPause_stepUntilPauseOfMid)
namespace RedProg2State
export TwoStageBridge.RedProg2State (mapSt)
end RedProg2State

abbrev stepUntilPauseFuel {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {AOut PauseVal ChOut1 St : Type}
    (defaultAOut : AOut)
    (stepPre : (q : ιI) → St →
      OracleComp PrimBaseSpec ((GSpec.Range q × St) ⊕ (ChOut1 × (PauseVal × St))))
    (mx : OracleComp (unifSpec + GSpec) AOut) (fuel : Nat) (st : St) :
    OracleComp PrimBaseSpec (Option ChOut1 × RedProg2State GSpec AOut PauseVal St) :=
  TwoStageBridge.stepUntilPauseFuelGen
    (fun uq => embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)))
    defaultAOut stepPre mx fuel st

abbrev runWithFuelPrim {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (defaultVal : α)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (fuel : Nat) (st : St) :
    OracleComp PrimBaseSpec (α × St) :=
  TwoStageBridge.runWithFuelGen
    (fun uq => embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)))
    defaultVal step mx fuel st

theorem GRed2_run1_eq_stepUntilPauseFuel
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec pqSig G}
    {rIn aIn aOut ch rIn2 out : Ty pqSig}
    (R : TwoStageCostedReduction pqxdhOps pqPrimIface G C rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (dfltCh : ch.denote)
    (oa : OracleComp (unifSpec + G) α) (fuel : ℕ) (s : R.σ.denote) :
    R.run1 dflt oa fuel s =
      midOfStepUntilPause dfltCh <$>
        stepUntilPauseFuel dflt
          (fun t st => do
            match ← R.handlePre.eval (.cons st (.cons (C.qenc t) .nil)) with
            | .inl (v, s') => pure (.inl (C.rdec t v, s'))
            | .inr (c, p, s') => pure (.inr (c, (p, s'))))
          oa fuel s := by
  refine Eq.trans (TwoStageBridge.run1_eq_stepUntilPauseFuelGen R dflt dfltCh oa fuel s) ?_
  have hfwd : pqPrimIface.fwdU =
      fun uq => embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) := by
    funext uq; simp [pqPrimIface, embedUnif]; rfl
  unfold stepUntilPauseFuel
  rw [← hfwd]
  congr 1; congr 4
  funext t st; congr 1; funext x; rcases x with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl

theorem runFuel_pqPrimIface_eq_runWithFuelPrim
    {κ : Type} {G : OracleSpec.{0, 0} κ} {C : GameCodec pqSig G} {σ : Ty pqSig}
    (h : Comp pqxdhOps pqPrimIface [σ, C.Q] (.prod C.R σ))
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) (fuel : ℕ) (s : σ.denote) :
    runFuel (C := C) h dflt oa fuel s =
      runWithFuelPrim dflt
        (fun t st => do
          let p ← h.eval (.cons st (.cons (C.qenc t) .nil))
          return (C.rdec t p.1, p.2))
        oa fuel s := by
  have hfwd : pqPrimIface.fwdU =
      fun uq => embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) := by
    funext uq; simp [pqPrimIface, embedUnif]; rfl
  rw [runWithFuelPrim, ← hfwd]
  exact TwoStageBridge.runFuel_eq_runWithFuelGen h dflt oa fuel s

theorem HoldsOnLeaves.simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (impl : QueryImpl spec ProbComp) {P : α → Prop} {m : OracleComp spec α}
    (hm : HoldsOnLeaves P m) : HoldsOnLeaves P (_root_.simulateQ impl m) := by
  classical
  have he : (m >>= fun a => Pure.pure (a, decide (P a))) = (m >>= fun a => Pure.pure (a, true)) :=
    hm.bind_congr _ _ (fun a ha => by simp [ha])
  refine ⟨fun {β} F G hFG => ?_⟩
  let H : α × Bool → ProbComp β := fun p => if p.2 then G p.1 else F p.1
  have hF : F = fun a => H (a, decide (P a)) := by
    funext a; by_cases ha : P a <;> simp [H, ha, hFG a]
  have hG : G = fun a => H (a, true) := by funext a; simp [H]
  have he' := congrArg (fun x => _root_.simulateQ impl x >>= H) he
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind] at he'
  rw [hF, hG]; exact he'

theorem kemShCrExp_congr (P : Primitives) (A B : KemShCrAdv) (I : A.State → Prop)
    (F : A.State → B.State)
    (hCh : ∀ pk sk, B.choosePk pk sk = (fun x => (x.1, F x.2)) <$> A.choosePk pk sk)
    (hInv : ∀ pk sk, HoldsOnLeaves (fun x => I x.2) (A.choosePk pk sk))
    (hF : ∀ s, I s → ∀ ss ct, B.findCollision (F s) ss ct = A.findCollision s ss ct) :
    kemShCrExp P B = kemShCrExp P A := by
  unfold kemShCrExp
  refine bind_congr fun kp => ?_
  rcases kp with ⟨pk, sk⟩
  dsimp only
  rw [hCh, simulateQ_map, bind_map_left]
  refine ((hInv pk sk).simulateQ (primBaseImpl P)).bind_congr _ _ (fun x hx => ?_)
  refine bind_congr fun r => ?_
  rcases P.kemEncaps x.1 r with _ | ⟨ss, ct⟩
  · rfl
  · simp only [hF x.2 hx]

section Unfold
variable {ι : Type} {G : OracleSpec.{0, 0} ι}

theorem stepUntilPauseFuel_pure {AOut C P St : Type} (defaultAOut : AOut)
    (step : (q : ι) → St → OracleComp PrimBaseSpec ((G.Range q × St) ⊕ (C × (P × St))))
    (a : AOut) (fuel : Nat) (st : St) :
    stepUntilPauseFuel defaultAOut step (Pure.pure a) fuel st = Pure.pure (none, .done a st) := rfl

theorem stepUntilPauseFuel_inl {AOut C P St : Type} (defaultAOut : AOut)
    (step : (q : ι) → St → OracleComp PrimBaseSpec ((G.Range q × St) ⊕ (C × (P × St))))
    (uq : ℕ) (k : (unifSpec + G).Range (Sum.inl uq) → OracleComp (unifSpec + G) AOut)
    (fuel : Nat) (st : St) :
    stepUntilPauseFuel defaultAOut step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inl uq)) >>= k) fuel st =
      embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u =>
        stepUntilPauseFuel defaultAOut step (k u) fuel st :=
  TwoStageBridge.stepUntilPauseFuelGen_inl _ defaultAOut step uq k fuel st

theorem stepUntilPauseFuel_inr_zero {AOut C P St : Type} (defaultAOut : AOut)
    (step : (q : ι) → St → OracleComp PrimBaseSpec ((G.Range q × St) ⊕ (C × (P × St))))
    (gq : ι) (k : G.Range gq → OracleComp (unifSpec + G) AOut) (st : St) :
    stepUntilPauseFuel defaultAOut step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) 0 st =
      Pure.pure (none, .done defaultAOut st) :=
  TwoStageBridge.stepUntilPauseFuelGen_inr_zero _ defaultAOut step gq k st

theorem stepUntilPauseFuel_inr_succ {AOut C P St : Type} (defaultAOut : AOut)
    (step : (q : ι) → St → OracleComp PrimBaseSpec ((G.Range q × St) ⊕ (C × (P × St))))
    (gq : ι) (k : G.Range gq → OracleComp (unifSpec + G) AOut) (fuel : Nat) (st : St) :
    stepUntilPauseFuel defaultAOut step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) (fuel + 1) st =
      (step gq st >>= fun x => match x with
        | .inl (resp, s') => stepUntilPauseFuel defaultAOut step (k resp) fuel s'
        | .inr (c, (p, s')) => Pure.pure (some c, .paused gq p s' k)) :=
  TwoStageBridge.stepUntilPauseFuelGen_inr_succ _ defaultAOut step gq k fuel st

theorem runWithFuelPrim_pure {α St : Type} (defaultVal : α)
    (step : (q : ι) → St → OracleComp PrimBaseSpec (G.Range q × St)) (a : α) (fuel : Nat)
    (st : St) : runWithFuelPrim defaultVal step (Pure.pure a) fuel st = Pure.pure (a, st) := rfl

theorem runWithFuelPrim_inl {α St : Type} (defaultVal : α)
    (step : (q : ι) → St → OracleComp PrimBaseSpec (G.Range q × St))
    (uq : ℕ) (k : (unifSpec + G).Range (Sum.inl uq) → OracleComp (unifSpec + G) α)
    (fuel : Nat) (st : St) :
    runWithFuelPrim defaultVal step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inl uq)) >>= k) fuel st =
      embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u =>
        runWithFuelPrim defaultVal step (k u) fuel st :=
  TwoStageBridge.runWithFuelGen_inl _ defaultVal step uq k fuel st

theorem runWithFuelPrim_inr_zero {α St : Type} (defaultVal : α)
    (step : (q : ι) → St → OracleComp PrimBaseSpec (G.Range q × St))
    (gq : ι) (k : G.Range gq → OracleComp (unifSpec + G) α) (st : St) :
    runWithFuelPrim defaultVal step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) 0 st =
      Pure.pure (defaultVal, st) :=
  TwoStageBridge.runWithFuelGen_inr_zero _ defaultVal step gq k st

theorem runWithFuelPrim_inr_succ {α St : Type} (defaultVal : α)
    (step : (q : ι) → St → OracleComp PrimBaseSpec (G.Range q × St))
    (gq : ι) (k : G.Range gq → OracleComp (unifSpec + G) α) (fuel : Nat) (st : St) :
    runWithFuelPrim defaultVal step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) (fuel + 1) st =
      (step gq st >>= fun x => runWithFuelPrim defaultVal step (k x.1) fuel x.2) :=
  TwoStageBridge.runWithFuelGen_inr_succ _ defaultVal step gq k fuel st

end Unfold

def Mid.mapSt {κ : Type} {G : OracleSpec.{0, 0} κ} {α π π' σ σ' χ : Type}
    (g : π → π') (f : σ → σ') : Mid G α π σ χ → Mid G α π' σ' χ
  | .done a s => .done a (f s)
  | .paused t c p s k => .paused t c (g p) (f s) k

/-- Pre-pause step invariant: handled states satisfy `Inv (n + 1)` and paused results satisfy
    `PI n`. -/
def PreStepInvP {R C P St : Type} (Inv : Nat → St → Prop) (PI : Nat → C → P → St → Prop)
    (n : Nat) : (R × St) ⊕ (C × (P × St)) → Prop
  | .inl x => Inv (n + 1) x.2
  | .inr x => PI n x.1 x.2.1 x.2.2

def Stage1InvP {ι : Type} {G : OracleSpec.{0, 0} ι} {AOut C P St : Type}
    (Inv : Nat → St → Prop) (PI : Nat → C → P → St → Prop) (K : Nat) :
    Option C × RedProg2State G AOut P St → Prop
  | (c, .done _ s) => c = none ∧ Inv K s
  | (c, .paused _ p s k) => ∃ c' n r, c = some c' ∧ PI n c' p s ∧ n + 1 + r ≤ K ∧
      ∀ x, IsQueryBoundP (k x) (fun q : ℕ ⊕ ι => q.isRight = true) r

theorem stepUntilPauseFuel_map_boundedP {ι : Type} {G : OracleSpec.{0, 0} ι}
    {AOut C P P' St St' : Type}
    (defaultAOut : AOut) (g : P → P') (f : St → St') (Inv : Nat → St → Prop)
    (PI : Nat → C → P → St → Prop)
    (hMono : ∀ {n m st}, n ≤ m → Inv n st → Inv m st)
    (step : (q : ι) → St → OracleComp PrimBaseSpec ((G.Range q × St) ⊕ (C × (P × St))))
    (step' : (q : ι) → St' → OracleComp PrimBaseSpec ((G.Range q × St') ⊕ (C × (P' × St'))))
    (K : Nat)
    (hStepEq : ∀ n q st, n + 1 ≤ K → Inv n st →
      step' q (f st) = Sum.map (Prod.map id f) (Prod.map id (Prod.map g f)) <$> step q st)
    (hStepInv : ∀ n q st, Inv n st → HoldsOnLeaves (PreStepInvP Inv PI n) (step q st))
    (mx : OracleComp (unifSpec + G) AOut) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ι => q.isRight = true) rem)
    (fuel n : Nat) (st : St) (hInv : Inv n st) (hBound : n + rem ≤ K) :
    HoldsOnLeaves (Stage1InvP Inv PI K) (stepUntilPauseFuel defaultAOut step mx fuel st) ∧
      stepUntilPauseFuel defaultAOut step' mx fuel (f st) =
        Prod.map id (RedProg2State.mapSt g f) <$>
          stepUntilPauseFuel defaultAOut step mx fuel st := by
  induction mx using OracleComp.inductionOn generalizing rem n st fuel with
  | pure a =>
    rw [stepUntilPauseFuel_pure, stepUntilPauseFuel_pure]
    refine ⟨HoldsOnLeaves.pure ⟨rfl, hMono (by omega) hInv⟩, ?_⟩
    simp [RedProg2State.mapSt]
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · have hCont : ∀ u, IsQueryBoundP (k u) (fun q : ℕ ⊕ ι => q.isRight = true) rem := by
        intro u; simpa using hMx.2 u
      rw [stepUntilPauseFuel_inl, stepUntilPauseFuel_inl]
      refine ⟨HoldsOnLeaves.bind_const _ (fun u => (ih u rem (hCont u) fuel n st hInv hBound).1),
        ?_⟩
      rw [map_bind]
      congr 1; funext u
      exact (ih u rem (hCont u) fuel n st hInv hBound).2
    · have hPos : 0 < rem := hMx.1.resolve_left (by simp)
      have hCont : ∀ r, IsQueryBoundP (k r) (fun q : ℕ ⊕ ι => q.isRight = true) (rem - 1) := by
        intro r; simpa using hMx.2 r
      have hBound' : (n + 1) + (rem - 1) ≤ K := by omega
      have hInvK : Inv K st := hMono (by omega) hInv
      rcases fuel with _ | fuel
      · rw [stepUntilPauseFuel_inr_zero, stepUntilPauseFuel_inr_zero]
        refine ⟨HoldsOnLeaves.pure ⟨rfl, hInvK⟩, ?_⟩
        simp [RedProg2State.mapSt]
      have hLeaves := hStepInv n gq st hInv
      rw [stepUntilPauseFuel_inr_succ, stepUntilPauseFuel_inr_succ]
      refine ⟨HoldsOnLeaves.bind hLeaves (fun x hx => ?_), ?_⟩
      · rcases x with ⟨resp, s'⟩ | ⟨c, pv, s'⟩
        · exact (ih resp (rem - 1) (hCont resp) fuel (n + 1) s' hx hBound').1
        · exact HoldsOnLeaves.pure ⟨c, n, rem - 1, rfl, hx, by omega, hCont⟩
      · rw [hStepEq n gq st (by omega) hInv, bind_map_left, map_bind]
        refine hLeaves.bind_congr _ _ (fun x hx => ?_)
        rcases x with ⟨resp, s'⟩ | ⟨c, pv, s'⟩
        · exact (ih resp (rem - 1) (hCont resp) fuel (n + 1) s' hx hBound').2
        · simp [RedProg2State.mapSt]

theorem runWithFuelPrim_map_boundedP {ι : Type} {G : OracleSpec.{0, 0} ι} {α St St' : Type}
    (defaultVal : α) (f : St → St') (Inv : Nat → St → Prop)
    (hMono : ∀ {n m st}, n ≤ m → Inv n st → Inv m st)
    (step : (q : ι) → St → OracleComp PrimBaseSpec (G.Range q × St))
    (step' : (q : ι) → St' → OracleComp PrimBaseSpec (G.Range q × St'))
    (K : Nat)
    (hStepEq : ∀ n q st, n + 1 ≤ K → Inv n st → step' q (f st) = Prod.map id f <$> step q st)
    (hStepInv : ∀ n q st, Inv n st → HoldsOnLeaves (fun x => Inv (n + 1) x.2) (step q st))
    (mx : OracleComp (unifSpec + G) α) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ι => q.isRight = true) rem)
    (fuel n : Nat) (st : St) (hInv : Inv n st) (hBound : n + rem ≤ K) :
    HoldsOnLeaves (fun x => Inv K x.2) (runWithFuelPrim defaultVal step mx fuel st) ∧
      runWithFuelPrim defaultVal step' mx fuel (f st) =
        Prod.map id f <$> runWithFuelPrim defaultVal step mx fuel st := by
  induction mx using OracleComp.inductionOn generalizing rem n st fuel with
  | pure a =>
    rw [runWithFuelPrim_pure, runWithFuelPrim_pure]
    refine ⟨HoldsOnLeaves.pure (hMono (by omega) hInv), ?_⟩
    simp
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · have hCont : ∀ u, IsQueryBoundP (k u) (fun q : ℕ ⊕ ι => q.isRight = true) rem := by
        intro u; simpa using hMx.2 u
      rw [runWithFuelPrim_inl, runWithFuelPrim_inl]
      refine ⟨HoldsOnLeaves.bind_const _ (fun u => (ih u rem (hCont u) fuel n st hInv hBound).1),
        ?_⟩
      rw [map_bind]
      congr 1; funext u
      exact (ih u rem (hCont u) fuel n st hInv hBound).2
    · have hPos : 0 < rem := hMx.1.resolve_left (by simp)
      have hCont : ∀ r, IsQueryBoundP (k r) (fun q : ℕ ⊕ ι => q.isRight = true) (rem - 1) := by
        intro r; simpa using hMx.2 r
      have hBound' : (n + 1) + (rem - 1) ≤ K := by omega
      have hInvK : Inv K st := hMono (by omega) hInv
      rcases fuel with _ | fuel
      · rw [runWithFuelPrim_inr_zero, runWithFuelPrim_inr_zero]
        exact ⟨HoldsOnLeaves.pure hInvK, by simp⟩
      have hLeaves := hStepInv n gq st hInv
      rw [runWithFuelPrim_inr_succ, runWithFuelPrim_inr_succ]
      refine ⟨HoldsOnLeaves.bind hLeaves (fun x hx =>
        (ih x.1 (rem - 1) (hCont x.1) fuel (n + 1) x.2 hx hBound').1), ?_⟩
      rw [hStepEq n gq st (by omega) hInv, bind_map_left, map_bind]
      exact hLeaves.bind_congr _ _ (fun x hx =>
        (ih x.1 (rem - 1) (hCont x.1) fuel (n + 1) x.2 hx hBound').2)

def PreStepInv {R C P St : Type} (Inv : Nat → St → Prop) (n : Nat) :
    (R × St) ⊕ (C × (P × St)) → Prop :=
  PreStepInvP Inv (fun n _ _ s => Inv n s) n

def Stage1Inv {ι : Type} {G : OracleSpec.{0, 0} ι} {AOut C P St : Type} (Inv : Nat → St → Prop)
    (K : Nat) : Option C × RedProg2State G AOut P St → Prop
  | (_, .done _ s) => Inv K s
  | (_, .paused _ _ s c) => ∃ n r, Inv n s ∧ n + 1 + r ≤ K ∧
      ∀ x, IsQueryBoundP (c x) (fun q : ℕ ⊕ ι => q.isRight = true) r

theorem stepUntilPauseFuel_map_bounded {ι : Type} {G : OracleSpec.{0, 0} ι}
    {AOut C P P' St St' : Type}
    (defaultAOut : AOut) (g : P → P') (f : St → St') (Inv : Nat → St → Prop)
    (hMono : ∀ {n m st}, n ≤ m → Inv n st → Inv m st)
    (step : (q : ι) → St → OracleComp PrimBaseSpec ((G.Range q × St) ⊕ (C × (P × St))))
    (step' : (q : ι) → St' → OracleComp PrimBaseSpec ((G.Range q × St') ⊕ (C × (P' × St'))))
    (K : Nat)
    (hStepEq : ∀ q st, Inv K st →
      step' q (f st) = Sum.map (Prod.map id f) (Prod.map id (Prod.map g f)) <$> step q st)
    (hStepInv : ∀ n q st, Inv n st → HoldsOnLeaves (PreStepInv Inv n) (step q st))
    (mx : OracleComp (unifSpec + G) AOut) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ι => q.isRight = true) rem)
    (fuel n : Nat) (st : St) (hInv : Inv n st) (hBound : n + rem ≤ K) :
    HoldsOnLeaves (Stage1Inv Inv K) (stepUntilPauseFuel defaultAOut step mx fuel st) ∧
      stepUntilPauseFuel defaultAOut step' mx fuel (f st) =
        Prod.map id (RedProg2State.mapSt g f) <$>
          stepUntilPauseFuel defaultAOut step mx fuel st := by
  have hP := stepUntilPauseFuel_map_boundedP defaultAOut g f Inv (fun n _ _ s => Inv n s) hMono
    step step' K (fun n q st hle hI => hStepEq q st (hMono (by omega) hI)) hStepInv mx rem hMx
    fuel n st hInv hBound
  refine ⟨hP.1.mono fun x hx => ?_, hP.2⟩
  rcases x with ⟨_, ⟨_, _⟩ | ⟨_, _, _, _⟩⟩
  · exact hx.2
  · rcases hx with ⟨_, n', r', _, hI, hle, hk⟩
    exact ⟨n', r', hI, hle, hk⟩

theorem runWithFuelPrim_map_bounded {ι : Type} {G : OracleSpec.{0, 0} ι} {α St St' : Type}
    (defaultVal : α) (f : St → St') (Inv : Nat → St → Prop)
    (hMono : ∀ {n m st}, n ≤ m → Inv n st → Inv m st)
    (step : (q : ι) → St → OracleComp PrimBaseSpec (G.Range q × St))
    (step' : (q : ι) → St' → OracleComp PrimBaseSpec (G.Range q × St'))
    (K : Nat)
    (hStepEq : ∀ q st, Inv K st → step' q (f st) = Prod.map id f <$> step q st)
    (hStepInv : ∀ n q st, Inv n st → HoldsOnLeaves (fun x => Inv (n + 1) x.2) (step q st))
    (mx : OracleComp (unifSpec + G) α) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ι => q.isRight = true) rem)
    (fuel n : Nat) (st : St) (hInv : Inv n st) (hBound : n + rem ≤ K) :
    HoldsOnLeaves (fun x => Inv K x.2) (runWithFuelPrim defaultVal step mx fuel st) ∧
      runWithFuelPrim defaultVal step' mx fuel (f st) =
        Prod.map id f <$> runWithFuelPrim defaultVal step mx fuel st :=
  runWithFuelPrim_map_boundedP defaultVal f Inv hMono step step' K
    (fun _ q st hle hI => hStepEq q st (hMono (by omega) hI)) hStepInv mx rem hMx fuel n st hInv
    hBound

/-- Pre-pause step invariant fixing the paused challenger output to `φ` of the pause payload. -/
def PreStepInvC {R C P St : Type} (Inv : Nat → St → Prop) (φ : P → C) (n : Nat) :
    (R × St) ⊕ (C × (P × St)) → Prop :=
  PreStepInvP Inv (fun n c p s => c = φ p ∧ Inv n s) n

def Stage1InvC {ι : Type} {G : OracleSpec.{0, 0} ι} {AOut C P St : Type} (Inv : Nat → St → Prop)
    (φ : P → C) (K : Nat) : Option C × RedProg2State G AOut P St → Prop
  | (c, .done _ s) => c = none ∧ Inv K s
  | (c, .paused _ p s k) => c = some (φ p) ∧ ∃ n r, Inv n s ∧ n + 1 + r ≤ K ∧
      ∀ x, IsQueryBoundP (k x) (fun q : ℕ ⊕ ι => q.isRight = true) r

theorem stepUntilPauseFuel_map_boundedC {ι : Type} {G : OracleSpec.{0, 0} ι}
    {AOut C P P' St St' : Type}
    (defaultAOut : AOut) (g : P → P') (f : St → St') (Inv : Nat → St → Prop) (φ : P → C)
    (hMono : ∀ {n m st}, n ≤ m → Inv n st → Inv m st)
    (step : (q : ι) → St → OracleComp PrimBaseSpec ((G.Range q × St) ⊕ (C × (P × St))))
    (step' : (q : ι) → St' → OracleComp PrimBaseSpec ((G.Range q × St') ⊕ (C × (P' × St'))))
    (K : Nat)
    (hStepEq : ∀ n q st, n + 1 ≤ K → Inv n st →
      step' q (f st) = Sum.map (Prod.map id f) (Prod.map id (Prod.map g f)) <$> step q st)
    (hStepInv : ∀ n q st, Inv n st → HoldsOnLeaves (PreStepInvC Inv φ n) (step q st))
    (mx : OracleComp (unifSpec + G) AOut) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ι => q.isRight = true) rem)
    (fuel n : Nat) (st : St) (hInv : Inv n st) (hBound : n + rem ≤ K) :
    HoldsOnLeaves (Stage1InvC Inv φ K) (stepUntilPauseFuel defaultAOut step mx fuel st) ∧
      stepUntilPauseFuel defaultAOut step' mx fuel (f st) =
        Prod.map id (RedProg2State.mapSt g f) <$>
          stepUntilPauseFuel defaultAOut step mx fuel st := by
  have hP := stepUntilPauseFuel_map_boundedP defaultAOut g f Inv (fun n c p s => c = φ p ∧ Inv n s)
    hMono step step' K hStepEq hStepInv mx rem hMx fuel n st hInv hBound
  refine ⟨hP.1.mono fun x hx => ?_, hP.2⟩
  rcases x with ⟨_, ⟨_, _⟩ | ⟨_, _, _, _⟩⟩
  · exact hx
  · rcases hx with ⟨_, n', r', rfl, ⟨rfl, hI⟩, hle, hk⟩
    exact ⟨rfl, n', r', hI, hle, hk⟩

abbrev runWithFuelPrim_map_boundedC := @runWithFuelPrim_map_boundedP

theorem stepUntilPauseFuel_char {ι : Type} {Gs : OracleSpec.{0, 0} ι} {AOut C P St R : Type}
    (defaultAOut : AOut)
    (step : (q : ι) → St → OracleComp PrimBaseSpec ((Gs.Range q × St) ⊕ (C × (P × St))))
    (G : Option C × RedProg2State Gs AOut P St → R)
    (run : OracleComp (unifSpec + Gs) AOut → Nat → St → OracleComp PrimBaseSpec R)
    (hpure : ∀ a fuel s, run (Pure.pure a) fuel s = Pure.pure (G (none, .done a s)))
    (hunif : ∀ uq (k : (unifSpec + Gs).Range (Sum.inl uq) → OracleComp (unifSpec + Gs) AOut)
      fuel s, run (liftM (OracleSpec.query (spec := unifSpec + Gs) (Sum.inl uq)) >>= k) fuel s =
        embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u => run (k u) fuel s)
    (hzero : ∀ gq (k : Gs.Range gq → OracleComp (unifSpec + Gs) AOut) s,
      run (liftM (OracleSpec.query (spec := unifSpec + Gs) (Sum.inr gq)) >>= k) 0 s =
        Pure.pure (G (none, .done defaultAOut s)))
    (hsucc : ∀ gq (k : Gs.Range gq → OracleComp (unifSpec + Gs) AOut) fuel s,
      run (liftM (OracleSpec.query (spec := unifSpec + Gs) (Sum.inr gq)) >>= k) (fuel + 1) s =
        step gq s >>= fun x => match x with
          | .inl (resp, s') => run (k resp) fuel s'
          | .inr (c, (p, s')) => Pure.pure (G (some c, .paused gq p s' k)))
    (mx : OracleComp (unifSpec + Gs) AOut) (fuel : Nat) (st : St) :
    run mx fuel st = G <$> stepUntilPauseFuel defaultAOut step mx fuel st :=
  TwoStageBridge.stepUntilPauseFuelGen_char _ defaultAOut step G run hpure hunif hzero hsucc mx fuel st

theorem runWithFuelPrim_char {ι : Type} {Gs : OracleSpec.{0, 0} ι} {α St R : Type}
    (defaultVal : α) (step : (q : ι) → St → OracleComp PrimBaseSpec (Gs.Range q × St))
    (G : α × St → R)
    (run : OracleComp (unifSpec + Gs) α → Nat → St → OracleComp PrimBaseSpec R)
    (hpure : ∀ a fuel s, run (Pure.pure a) fuel s = Pure.pure (G (a, s)))
    (hunif : ∀ uq (k : (unifSpec + Gs).Range (Sum.inl uq) → OracleComp (unifSpec + Gs) α)
      fuel s, run (liftM (OracleSpec.query (spec := unifSpec + Gs) (Sum.inl uq)) >>= k) fuel s =
        embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u => run (k u) fuel s)
    (hzero : ∀ gq (k : Gs.Range gq → OracleComp (unifSpec + Gs) α) s,
      run (liftM (OracleSpec.query (spec := unifSpec + Gs) (Sum.inr gq)) >>= k) 0 s =
        Pure.pure (G (defaultVal, s)))
    (hsucc : ∀ gq (k : Gs.Range gq → OracleComp (unifSpec + Gs) α) fuel s,
      run (liftM (OracleSpec.query (spec := unifSpec + Gs) (Sum.inr gq)) >>= k) (fuel + 1) s =
        step gq s >>= fun x => run (k x.1) fuel x.2)
    (mx : OracleComp (unifSpec + Gs) α) (fuel : Nat) (st : St) :
    run mx fuel st = G <$> runWithFuelPrim defaultVal step mx fuel st :=
  TwoStageBridge.runWithFuelGen_char _ defaultVal step G run hpure hunif hzero hsucc mx fuel st

end SignalPqxdh.Security.ReductionDsl
