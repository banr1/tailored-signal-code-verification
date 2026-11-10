/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` Latched-`dh1` Oracle Wrapper

Defines `pqxdhAuthAdvLatchedStageImpl1Key` and equates `authKoskExpAtStage1Key` with simulation
under the latched-state wrapper.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security

/-- Stage-parameterized one-key `Auth` oracle wrapper updating `latchedDh1` at `.corruptIK`. -/
def pqxdhAuthAdvLatchedStageImpl1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthAdvLatchedState S) ProbComp)
  | .corruptIK u => StateT.mk (fun s => do
    let latched' :=
      latchDh1ForPrincipal S P u.val s.adv.hyb.base s.adv.advRoLog s.adv.respRecs s.latchedDh1
    let (resp, adv') ← (pqxdhAuthAdvStageImpl1Key stage S P (.corruptIK u)).run s.adv
    return (resp, { adv := adv', latchedDh1 := latched' }))
  | q => StateT.mk (fun s => do
    let (resp, adv') ← (pqxdhAuthAdvStageImpl1Key stage S P q).run s.adv
    return (resp, { s with adv := adv' }))

theorem map_adv_pqxdhAuthAdvLatchedStageImpl1Key (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S) :
    Prod.map id AuthAdvLatchedState.adv <$>
        ((pqxdhAuthAdvLatchedStageImpl1Key stage S P q).run s) =
      (pqxdhAuthAdvStageImpl1Key stage S P q).run s.adv := by
  cases q <;> simp [pqxdhAuthAdvLatchedStageImpl1Key, StateT.run_mk, Prod.map]

theorem map_adv_fullAuthAdvLatchedStageImpl1Key (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) (q : (unifSpec + authSpec S).Domain) (s : AuthAdvLatchedState S) :
    Prod.map id AuthAdvLatchedState.adv <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthAdvLatchedState S) ProbComp) +
        pqxdhAuthAdvLatchedStageImpl1Key stage S P) q).run s =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvCutoffState S) ProbComp) +
      pqxdhAuthAdvStageImpl1Key stage S P) q).run s.adv := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr gq => exact map_adv_pqxdhAuthAdvLatchedStageImpl1Key stage S P gq s

theorem simulateQ_map_adv_fullAuthAdvLatchedStageImpl1Key (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) {α : Type} (oa : OracleComp (unifSpec + authSpec S) α)
    (s : AuthAdvLatchedState S) :
    let fullLatched := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvLatchedState S) ProbComp) + pqxdhAuthAdvLatchedStageImpl1Key stage S P
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvCutoffState S) ProbComp) + pqxdhAuthAdvStageImpl1Key stage S P
    Prod.map id AuthAdvLatchedState.adv <$> ((simulateQ fullLatched oa).run s) =
      (simulateQ fullAdv oa).run s.adv :=
  _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    AuthAdvLatchedState.adv
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthAdvLatchedState S) ProbComp) + pqxdhAuthAdvLatchedStageImpl1Key stage S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthAdvCutoffState S) ProbComp) + pqxdhAuthAdvStageImpl1Key stage S P)
    (map_adv_fullAuthAdvLatchedStageImpl1Key stage S P)
    oa s

theorem authKoskExpAtStage_eq_advLatchedStage1Key (stage : AuthHybridStage) (S : Setup)
    (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage1Key stage S P A =
    (do
      let secb ← $ᵗ Bool
      let initSt := AuthAdvLatchedState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthAdvLatchedState S) ProbComp) +
        pqxdhAuthAdvLatchedStageImpl1Key stage S P
      let (b', finalSt) ← (simulateQ impl A.run).run initSt
      finalizeAuthKosk S P secb b' finalSt.hyb) := by
  rw [authKoskExpAtStage_eq_advStage1Key stage S P A]
  congr 1; funext secb
  have hsim := congrArg
    (· >>= fun (p : Bool × AuthAdvCutoffState S) => finalizeAuthKosk S P secb p.1 p.2.hyb)
    (simulateQ_map_adv_fullAuthAdvLatchedStageImpl1Key stage S P A.run
      (AuthAdvLatchedState.empty S secb))
  dsimp only [AuthAdvLatchedState.adv_empty] at hsim
  rw [← hsim, map_eq_bind_pure_comp]
  simp [bind_assoc, Prod.map, AuthAdvLatchedState.hyb]

end Proofs.SignalPqxdh.Security
