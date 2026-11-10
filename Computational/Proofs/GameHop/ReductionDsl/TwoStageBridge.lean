/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
public import Computational.Proofs.GameHop.StateSim

/-!
# Two-Stage `ReductionDsl` Simulation Bridges

Fueled two-stage and post-pause runners (`stepUntilPauseFuelGen`, `runWithFuelGen`), bridges from
`TwoStageCostedReduction.run1` and `ReductionDsl.runFuel`, recursion characterizations, and
two-stage experiment congruence (`twoStageExp_congr_of_support`).
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.ReductionDsl.TwoStageBridge

open OracleSpec OracleComp
open Computational.Proofs.GameHop.StateSim (AllSupport)
open _root_.ReductionDsl (Sig Ty Env Ops Iface Comp GameCodec Mid TwoStageCostedReduction runFuel)

section Runners

/-- Paused-or-done two-stage adversary state. -/
inductive RedProg2State {κ : Type} (GSpec : OracleSpec.{0, 0} κ) (AOut PauseVal St : Type) :
    Type where
  | done   (aOut : AOut) (st : St)
  | paused (q : κ) (pauseVal : PauseVal) (st : St)
      (cont : GSpec.Range q → OracleComp (unifSpec + GSpec) AOut)

/-- Stage-1 fueled runner parameterized by coin forwarding `fwdU`. -/
def stepUntilPauseFuelGen {ι κ : Type} {T : OracleSpec.{0, 0} ι} {GSpec : OracleSpec.{0, 0} κ}
    {AOut PauseVal ChOut1 St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    (defaultAOut : AOut)
    (stepPre : (q : κ) → St →
      OracleComp T ((GSpec.Range q × St) ⊕ (ChOut1 × (PauseVal × St))))
    (mx : OracleComp (unifSpec + GSpec) AOut) (fuel : ℕ) (st : St) :
    OracleComp T (Option ChOut1 × RedProg2State GSpec AOut PauseVal St) :=
  OracleComp.construct
    (C := fun _ => ℕ → St →
      OracleComp T (Option ChOut1 × RedProg2State GSpec AOut PauseVal St))
    (fun a _ s => pure (none, .done a s))
    (fun q cont r f s =>
      match q with
      | Sum.inl uq => do
        let u ← fwdU uq; r u f s
      | Sum.inr gq =>
        match f with
        | 0 => pure (none, .done defaultAOut s)
        | f' + 1 => do
          match ← stepPre gq s with
          | .inl (resp, s') => r resp f' s'
          | .inr (chOut1, (pVal, s')) => pure (some chOut1, .paused gq pVal s' cont))
    mx fuel st

/-- Stage-2 fueled runner parameterized by coin forwarding `fwdU`. -/
def runWithFuelGen {ι κ : Type} {T : OracleSpec.{0, 0} ι} {GSpec : OracleSpec.{0, 0} κ}
    {St α : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    (defaultVal : α)
    (step : (q : κ) → St → OracleComp T (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (fuel : ℕ) (st : St) :
    OracleComp T (α × St) :=
  OracleComp.construct
    (C := fun _ => ℕ → St → OracleComp T (α × St))
    (fun a _ s => pure (a, s))
    (fun q _ r f s =>
      match q with
      | Sum.inl uq => do
        let u ← fwdU uq; r u f s
      | Sum.inr gq =>
        match f with
        | 0 => pure (defaultVal, s)
        | f' + 1 => do let (resp, s') ← step gq s; r resp f' s')
    mx fuel st

def midOfStepUntilPause {κ : Type} {G : OracleSpec.{0, 0} κ} {α π σ χ : Type} (dfltCh : χ) :
    Option χ × RedProg2State G α π σ → Mid G α π σ χ
  | (_, .done a s) => .done a s
  | (c?, .paused t p s k) => .paused t (c?.getD dfltCh) p s k

def stepUntilPauseOfMid {κ : Type} {G : OracleSpec.{0, 0} κ} {α π σ χ : Type} :
    Mid G α π σ χ → Option χ × RedProg2State G α π σ
  | .done a s => (none, .done a s)
  | .paused t c p s k => (some c, .paused t p s k)

@[simp]
theorem midOfStepUntilPause_stepUntilPauseOfMid
    {κ : Type} {G : OracleSpec.{0, 0} κ} {α π σ χ : Type} (dfltCh : χ)
    (m : Mid G α π σ χ) :
    midOfStepUntilPause dfltCh (stepUntilPauseOfMid m) = m := by
  cases m <;> rfl

def RedProg2State.mapSt {κ : Type} {G : OracleSpec.{0, 0} κ} {AOut P P' St St' : Type}
    (g : P → P') (f : St → St') : RedProg2State G AOut P St → RedProg2State G AOut P' St'
  | .done a s => .done a (f s)
  | .paused q p s c => .paused q (g p) (f s) c

def midMapSt {κ : Type} {G : OracleSpec.{0, 0} κ} {α π π' σ σ' χ : Type}
    (g : π → π') (f : σ → σ') : Mid G α π σ χ → Mid G α π' σ' χ
  | .done a s => .done a (f s)
  | .paused t c p s k => .paused t c (g p) (f s) k

theorem run1_eq_stepUntilPauseFuelGen {S : Sig} {ι κ : Type}
    {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {O : Ops S} {I : Iface S T} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (dfltCh : ch.denote)
    (oa : OracleComp (unifSpec + G) α) (fuel : ℕ) (s : R.σ.denote) :
    R.run1 dflt oa fuel s =
      midOfStepUntilPause dfltCh <$>
        stepUntilPauseFuelGen I.fwdU dflt
          (fun t st => do
            match ← R.handlePre.eval (.cons st (.cons (C.qenc t) .nil)) with
            | .inl (v, s') => pure (.inl (C.rdec t v, s'))
            | .inr (c, p, s') => pure (.inr (c, (p, s'))))
          oa fuel s := by
  induction oa using OracleComp.inductionOn generalizing fuel s with
  | pure a => rfl
  | query_bind q k ih =>
    unfold TwoStageCostedReduction.run1 stepUntilPauseFuelGen
    rw [OracleComp.construct_query_bind, OracleComp.construct_query_bind]
    rcases q with uq | gq
    · dsimp only
      rw [map_bind]
      congr 1; funext u
      exact ih u fuel s
    · rcases fuel with _ | fuel
      · rfl
      · dsimp only
        rw [bind_assoc, map_bind]
        congr 1; funext res
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · exact ih (C.rdec gq v) fuel s'
        · rfl

theorem runFuel_eq_runWithFuelGen {S : Sig} {ι κ : Type}
    {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {O : Ops S} {I : Iface S T} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) (fuel : ℕ) (s : σ.denote) :
    runFuel (C := C) h dflt oa fuel s =
      runWithFuelGen I.fwdU dflt
        (fun t st => do
          let p ← h.eval (.cons st (.cons (C.qenc t) .nil))
          return (C.rdec t p.1, p.2))
        oa fuel s := by
  induction oa using OracleComp.inductionOn generalizing fuel s with
  | pure a => rfl
  | query_bind q k ih =>
    unfold runFuel runWithFuelGen
    rw [OracleComp.construct_query_bind, OracleComp.construct_query_bind]
    rcases q with uq | gq
    · dsimp only
      congr 1; funext u
      exact ih u fuel s
    · rcases fuel with _ | fuel
      · rfl
      · dsimp only
        rw [bind_assoc]
        congr 1; funext p
        rw [pure_bind]
        exact ih (C.rdec gq p.1) fuel p.2

end Runners

section UnfoldAndChar

variable {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}

theorem stepUntilPauseFuelGen_pure {AOut C P St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (defaultAOut : AOut)
    (step : (q : κ) → St → OracleComp T ((G.Range q × St) ⊕ (C × (P × St))))
    (a : AOut) (fuel : ℕ) (st : St) :
    stepUntilPauseFuelGen fwdU defaultAOut step (Pure.pure a) fuel st =
      Pure.pure (none, .done a st) := rfl

theorem stepUntilPauseFuelGen_inl {AOut C P St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (defaultAOut : AOut)
    (step : (q : κ) → St → OracleComp T ((G.Range q × St) ⊕ (C × (P × St))))
    (uq : ℕ) (k : (unifSpec + G).Range (Sum.inl uq) → OracleComp (unifSpec + G) AOut)
    (fuel : ℕ) (st : St) :
    stepUntilPauseFuelGen fwdU defaultAOut step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inl uq)) >>= k) fuel st =
      (fwdU uq >>= fun u => stepUntilPauseFuelGen fwdU defaultAOut step (k u) fuel st) := by
  unfold stepUntilPauseFuelGen
  rw [OracleComp.construct_query_bind]

theorem stepUntilPauseFuelGen_inr_zero {AOut C P St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (defaultAOut : AOut)
    (step : (q : κ) → St → OracleComp T ((G.Range q × St) ⊕ (C × (P × St))))
    (gq : κ) (k : G.Range gq → OracleComp (unifSpec + G) AOut) (st : St) :
    stepUntilPauseFuelGen fwdU defaultAOut step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) 0 st =
      Pure.pure (none, .done defaultAOut st) := by
  unfold stepUntilPauseFuelGen
  rw [OracleComp.construct_query_bind]

theorem stepUntilPauseFuelGen_inr_succ {AOut C P St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (defaultAOut : AOut)
    (step : (q : κ) → St → OracleComp T ((G.Range q × St) ⊕ (C × (P × St))))
    (gq : κ) (k : G.Range gq → OracleComp (unifSpec + G) AOut) (fuel : ℕ) (st : St) :
    stepUntilPauseFuelGen fwdU defaultAOut step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) (fuel + 1) st =
      (step gq st >>= fun x => match x with
        | .inl (resp, s') => stepUntilPauseFuelGen fwdU defaultAOut step (k resp) fuel s'
        | .inr (c, (p, s')) => Pure.pure (some c, .paused gq p s' k)) := by
  unfold stepUntilPauseFuelGen
  rw [OracleComp.construct_query_bind]
  dsimp only
  refine bind_congr fun x => ?_
  rcases x with ⟨a, b⟩ | ⟨c, p, s'⟩ <;> rfl

theorem runWithFuelGen_pure {α St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (defaultVal : α)
    (step : (q : κ) → St → OracleComp T (G.Range q × St)) (a : α) (fuel : ℕ)
    (st : St) :
    runWithFuelGen fwdU defaultVal step (Pure.pure a) fuel st = Pure.pure (a, st) := rfl

theorem runWithFuelGen_inl {α St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (defaultVal : α)
    (step : (q : κ) → St → OracleComp T (G.Range q × St))
    (uq : ℕ) (k : (unifSpec + G).Range (Sum.inl uq) → OracleComp (unifSpec + G) α)
    (fuel : ℕ) (st : St) :
    runWithFuelGen fwdU defaultVal step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inl uq)) >>= k) fuel st =
      (fwdU uq >>= fun u => runWithFuelGen fwdU defaultVal step (k u) fuel st) := by
  unfold runWithFuelGen
  rw [OracleComp.construct_query_bind]

theorem runWithFuelGen_inr_zero {α St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (defaultVal : α)
    (step : (q : κ) → St → OracleComp T (G.Range q × St))
    (gq : κ) (k : G.Range gq → OracleComp (unifSpec + G) α) (st : St) :
    runWithFuelGen fwdU defaultVal step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) 0 st =
      Pure.pure (defaultVal, st) := by
  unfold runWithFuelGen
  rw [OracleComp.construct_query_bind]

theorem runWithFuelGen_inr_succ {α St : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))) (defaultVal : α)
    (step : (q : κ) → St → OracleComp T (G.Range q × St))
    (gq : κ) (k : G.Range gq → OracleComp (unifSpec + G) α) (fuel : ℕ) (st : St) :
    runWithFuelGen fwdU defaultVal step
        (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) (fuel + 1) st =
      (step gq st >>= fun x => runWithFuelGen fwdU defaultVal step (k x.1) fuel x.2) := by
  unfold runWithFuelGen
  rw [OracleComp.construct_query_bind]

/-- Characterizes any stage-1 runner satisfying the defining recursion equations as
`M <$> stepUntilPauseFuelGen ...`. -/
theorem stepUntilPauseFuelGen_char {AOut C P St R : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    (defaultAOut : AOut)
    (step : (q : κ) → St → OracleComp T ((G.Range q × St) ⊕ (C × (P × St))))
    (M : Option C × RedProg2State G AOut P St → R)
    (run : OracleComp (unifSpec + G) AOut → ℕ → St → OracleComp T R)
    (hpure : ∀ a fuel s, run (Pure.pure a) fuel s = Pure.pure (M (none, .done a s)))
    (hunif : ∀ uq (k : (unifSpec + G).Range (Sum.inl uq) → OracleComp (unifSpec + G) AOut)
      fuel s, run (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inl uq)) >>= k) fuel s =
        (fwdU uq >>= fun u => run (k u) fuel s))
    (hzero : ∀ gq (k : G.Range gq → OracleComp (unifSpec + G) AOut) s,
      run (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) 0 s =
        Pure.pure (M (none, .done defaultAOut s)))
    (hsucc : ∀ gq (k : G.Range gq → OracleComp (unifSpec + G) AOut) fuel s,
      run (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) (fuel + 1) s =
        (step gq s >>= fun x => match x with
          | .inl (resp, s') => run (k resp) fuel s'
          | .inr (c, (p, s')) => Pure.pure (M (some c, .paused gq p s' k))))
    (mx : OracleComp (unifSpec + G) AOut) (fuel : ℕ) (st : St) :
    run mx fuel st = M <$> stepUntilPauseFuelGen fwdU defaultAOut step mx fuel st := by
  induction mx using OracleComp.inductionOn generalizing fuel st with
  | pure a =>
    rw [hpure, stepUntilPauseFuelGen_pure, map_pure]
  | query_bind q k ih =>
    rcases q with uq | gq
    · rw [hunif, stepUntilPauseFuelGen_inl, map_bind]
      exact congrArg _ (funext fun u => ih u fuel st)
    · rcases fuel with _ | fuel
      · rw [hzero, stepUntilPauseFuelGen_inr_zero, map_pure]
      · rw [hsucc, stepUntilPauseFuelGen_inr_succ, map_bind]
        refine congrArg _ (funext fun x => ?_)
        rcases x with ⟨resp, s'⟩ | ⟨c, p, s'⟩
        · exact ih resp fuel s'
        · simp

/-- Characterizes any stage-2 runner satisfying the defining recursion equations as
`M <$> runWithFuelGen ...`. -/
theorem runWithFuelGen_char {α St R : Type}
    (fwdU : (n : ℕ) → OracleComp T (Fin (n + 1)))
    (defaultVal : α)
    (step : (q : κ) → St → OracleComp T (G.Range q × St))
    (M : α × St → R)
    (run : OracleComp (unifSpec + G) α → ℕ → St → OracleComp T R)
    (hpure : ∀ a fuel s, run (Pure.pure a) fuel s = Pure.pure (M (a, s)))
    (hunif : ∀ uq (k : (unifSpec + G).Range (Sum.inl uq) → OracleComp (unifSpec + G) α)
      fuel s, run (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inl uq)) >>= k) fuel s =
        (fwdU uq >>= fun u => run (k u) fuel s))
    (hzero : ∀ gq (k : G.Range gq → OracleComp (unifSpec + G) α) s,
      run (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) 0 s =
        Pure.pure (M (defaultVal, s)))
    (hsucc : ∀ gq (k : G.Range gq → OracleComp (unifSpec + G) α) fuel s,
      run (liftM (OracleSpec.query (spec := unifSpec + G) (Sum.inr gq)) >>= k) (fuel + 1) s =
        (step gq s >>= fun x => run (k x.1) fuel x.2))
    (mx : OracleComp (unifSpec + G) α) (fuel : ℕ) (st : St) :
    run mx fuel st = M <$> runWithFuelGen fwdU defaultVal step mx fuel st := by
  induction mx using OracleComp.inductionOn generalizing fuel st with
  | pure a =>
    rw [hpure, runWithFuelGen_pure, map_pure]
  | query_bind q k ih =>
    rcases q with uq | gq
    · rw [hunif, runWithFuelGen_inl, map_bind]
      exact congrArg _ (funext fun u => ih u fuel st)
    · rcases fuel with _ | fuel
      · rw [hzero, runWithFuelGen_inr_zero, map_pure]
      · rw [hsucc, runWithFuelGen_inr_succ, map_bind]
        exact congrArg _ (funext fun x => ih x.1 fuel x.2)

/-- Congruence for two-stage experiments related by a stage-1 state map `F` under a leaf invariant
`Inv`. -/
theorem twoStageExp_congr_of_support {ι' : Type} {S : OracleSpec.{0, 0} ι'}
    {Ch StA StB Out : Type}
    (impl : QueryImpl T (OracleComp S))
    (stage1A : OracleComp T (Ch × StA))
    (stage1B : OracleComp T (Ch × StB))
    (Inv : StA → Prop) (F : StA → StB)
    (midA : Ch → StA → OracleComp S Out)
    (midB : Ch → StB → OracleComp S Out)
    (h1 : stage1B = Prod.map id F <$> stage1A)
    (hInv : AllSupport (fun x => Inv x.2) (simulateQ impl stage1A))
    (h2 : ∀ ch s, Inv s → midB ch (F s) = midA ch s) :
    (simulateQ impl stage1B >>= fun x => midB x.1 x.2) =
      (simulateQ impl stage1A >>= fun x => midA x.1 x.2) := by
  rw [h1, simulateQ_map, bind_map_left]
  exact hInv.bind_congr _ _ fun ⟨ch, s⟩ hs => h2 ch s hs

end UnfoldAndChar

end Computational.Proofs.GameHop.ReductionDsl.TwoStageBridge
