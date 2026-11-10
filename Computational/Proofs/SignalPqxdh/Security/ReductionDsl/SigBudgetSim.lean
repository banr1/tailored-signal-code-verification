/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake
import VCVio.EvalDist.Monad.Basic

/-!
# Bounded State Simulation of `runWithSigBudgetPrim`

Lifts shallow `SigStepResultPrim` handlers into stateful `pqxdhEufCmaIface` steps carrying the
signing budget in the state (`sigLiftStep`), and proves bounded state simulation under a per-query
invariant (`runWithIfaceStep_sig_map_state_bounded`).
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh.Security.ReductionDsl
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open OracleSpec OracleComp

def runWithSigStep {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp (PrimBaseSpec + sigOracleSpec) (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    OracleComp (PrimBaseSpec + sigOracleSpec) (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp (PrimBaseSpec + sigOracleSpec) (α × St))
    (fun x st => Pure.pure (x, st))
    (fun q _ r st => match q with
      | Sum.inl uq => do
          let u ← liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec)
            (Sum.inl (Sum.inl uq)))
          r u st
      | Sum.inr gq => do
          let p ← step gq st
          r p.1 p.2)
    mx st

theorem runWithIfaceStep_pqSigIface_eq_runWithSigStep
    {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp (PrimBaseSpec + sigOracleSpec) (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    runWithIfaceStep pqxdhEufCmaIface step mx st = runWithSigStep step mx st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind q k ih =>
    rcases q with uq | gq
    · change (pqxdhEufCmaIface.fwdU uq >>= fun u => runWithIfaceStep pqxdhEufCmaIface step (k u) st) =
        (liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inl (Sum.inl uq))) >>=
          fun u => runWithSigStep step (k u) st)
      congr 1; funext u; exact ih u st
    · change (step gq st >>= fun p => runWithIfaceStep pqxdhEufCmaIface step (k p.1) p.2) =
        (step gq st >>= fun p => runWithSigStep step (k p.1) p.2)
      congr 1; funext p; exact ih p.1 p.2

theorem HoldsOnLeaves.embedPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {m : OracleComp PrimBaseSpec α} (hm : HoldsOnLeaves P m) :
    HoldsOnLeaves P (embedPrim (spec := spec) m) := by
  classical
  have he : (m >>= fun a => Pure.pure (a, decide (P a))) = (m >>= fun a => Pure.pure (a, true)) :=
    hm.bind_congr _ _ (fun a ha => by simp [ha])
  refine ⟨fun {β} F G hFG => ?_⟩
  let H : α × Bool → OracleComp (PrimBaseSpec + spec) β := fun p => if p.2 then G p.1 else F p.1
  have hF : F = fun a => H (a, decide (P a)) := by
    funext a; by_cases ha : P a <;> simp [H, ha, hFG a]
  have hG : G = fun a => H (a, true) := by funext a; simp [H]
  have he' := congrArg (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := spec) x >>= H) he
  simp only [embedPrim_bind, embedPrim_pure, bind_assoc, pure_bind] at he'
  rw [hF, hG]; exact he'

def SigResInv {St R : Type} (I : St → Prop) : SigStepResultPrim St R → Prop
  | .done _ st' => I st'
  | .signTwo _ k1 fb => I fb.2 ∧ ∀ pq s1 s2, I ((k1 pq s1).2 s2).2

def sigLiftK {St R St' : Type} (f : St × Nat → St') (b : Nat) :
    SigStepResultPrim St R → OracleComp (PrimBaseSpec + sigOracleSpec) (R × St')
  | .done res st' => Pure.pure (res, f (st', b))
  | .signTwo msg1 k1 fb =>
    match b with
    | 0 => Pure.pure (fb.1, f (fb.2, 0))
    | b' + 1 => do
      let sig1 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg1))
      let pq ← _root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) sampleKemKeyGenPrim
      let (msg2, k2) := k1 pq sig1
      let sig2 ← query (spec := PrimBaseSpec + sigOracleSpec) (Sum.inr (SigQuery.sign msg2))
      let p := k2 sig2
      Pure.pure (p.1, f (p.2, b'))

/-- Stateful `pqxdhEufCmaIface` step lifting a shallow `SigStepResultPrim` handler with budget `b`. -/
def sigLiftStep {St R St' : Type} (f : St × Nat → St')
    (step : St → OracleComp PrimBaseSpec (SigStepResultPrim St R)) (st : St) (b : Nat) :
    OracleComp (PrimBaseSpec + sigOracleSpec) (R × St') :=
  _root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) (step st) >>= sigLiftK f b

theorem runWithSigStep_map_state_bounded {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {St St' Obs α : Type} (f : St × Nat → St') (obs : St → Obs) (obs' : St' → Obs)
    (hObs : ∀ st b, obs' (f (st, b)) = obs st)
    (Inv : Nat → St → Prop) (hMono : ∀ {n m st}, n ≤ m → Inv n st → Inv m st)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (step' : (q : ιI) → St' → OracleComp (PrimBaseSpec + sigOracleSpec) (GSpec.Range q × St'))
    (K : Nat)
    (hStepEq : ∀ q st b, Inv K st → step' q (f (st, b)) = sigLiftStep f (step q) st b)
    (hStepInv : ∀ n q st, Inv n st → HoldsOnLeaves (SigResInv (Inv (n + 1))) (step q st))
    (mx : OracleComp (unifSpec + GSpec) α) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => q.isRight = true) rem)
    (n : Nat) (st : St) (b : Nat) (hInv : Inv n st) (hBound : n + rem ≤ K) :
    Prod.map id obs' <$> runWithSigStep step' mx (f (st, b)) =
      Prod.map id obs <$> runWithSigBudgetPrim step mx st b := by
  induction mx using OracleComp.inductionOn generalizing rem n st b with
  | pure a =>
    change Prod.map id obs' <$> (Pure.pure (a, f (st, b)) : OracleComp _ _) =
      Prod.map id obs <$> (Pure.pure (a, st) : OracleComp _ _)
    simp [hObs]
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · have hCont : ∀ u, IsQueryBoundP (k u) (fun q : ℕ ⊕ ιI => q.isRight = true) rem := by
        intro u; simpa using hMx.2 u
      change Prod.map id obs' <$>
          (liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec)
            (Sum.inl (Sum.inl uq))) >>=
            fun u => runWithSigStep step' (k u) (f (st, b))) =
        Prod.map id obs <$>
          (liftM (OracleSpec.query (spec := PrimBaseSpec + sigOracleSpec)
            (Sum.inl (Sum.inl uq))) >>=
            fun u => runWithSigBudgetPrim step (k u) st b)
      rw [map_bind, map_bind]
      exact congrArg _ (funext fun u => ih u rem (hCont u) n st b hInv hBound)
    · have hPos : 0 < rem := hMx.1.resolve_left (by simp)
      have hCont : ∀ r, IsQueryBoundP (k r) (fun q : ℕ ⊕ ιI => q.isRight = true) (rem - 1) := by
        intro r; simpa using hMx.2 r
      have hBound' : (n + 1) + (rem - 1) ≤ K := by omega
      have hInvK : Inv K st := hMono (by omega) hInv
      have hIH : ∀ r st'' b'', Inv (n + 1) st'' →
          Prod.map id obs' <$> runWithSigStep step' (k r) (f (st'', b'')) =
            Prod.map id obs <$> runWithSigBudgetPrim step (k r) st'' b'' :=
        fun r st'' b'' h => ih r (rem - 1) (hCont r) (n + 1) st'' b'' h hBound'
      change Prod.map id obs' <$>
          (step' gq (f (st, b)) >>= fun x => runWithSigStep step' (k x.1) x.2) =
        Prod.map id obs <$>
          (_root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec) (step gq st) >>= fun sr =>
            match sr with
            | .done res st' => runWithSigBudgetPrim step (k res) st' b
            | .signTwo msg1 k1 fallback =>
              match b with
              | 0 => runWithSigBudgetPrim step (k fallback.1) fallback.2 0
              | b' + 1 => do
                let sig1 ← query (spec := PrimBaseSpec + sigOracleSpec)
                  (Sum.inr (SigQuery.sign msg1))
                let pq ← _root_.SignalPqxdh.Security.embedPrim (spec := sigOracleSpec)
                  sampleKemKeyGenPrim
                let (msg2, k2) := k1 pq sig1
                let sig2 ← query (spec := PrimBaseSpec + sigOracleSpec)
                  (Sum.inr (SigQuery.sign msg2))
                let p := k2 sig2
                runWithSigBudgetPrim step (k p.1) p.2 b')
      rw [hStepEq gq st b hInvK, sigLiftStep, bind_assoc, map_bind, map_bind]
      refine (HoldsOnLeaves.embedPrim (hStepInv n gq st hInv)).bind_congr _ _ (fun sr hsr => ?_)
      rcases sr with ⟨res, st'⟩ | ⟨msg1, k1, fb⟩
      · simp only [sigLiftK, pure_bind]
        exact hIH res st' b hsr
      · obtain ⟨hfb, hk⟩ := hsr
        rcases b with _ | b'
        · simp only [sigLiftK, pure_bind]
          exact hIH fb.1 fb.2 0 hfb
        · simp only [sigLiftK, bind_assoc, map_bind]
          refine congrArg _ (funext fun sig1 => ?_)
          refine congrArg _ (funext fun pq => ?_)
          have hk2 := hk pq sig1
          rcases hkp : k1 pq sig1 with ⟨msg2, k2⟩
          rw [hkp] at hk2
          simp only [pure_bind]
          refine congrArg _ (funext fun sig2 => ?_)
          exact hIH _ _ b' (hk2 sig2)

theorem runWithIfaceStep_sig_map_state_bounded {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {St St' Obs α : Type} (f : St × Nat → St') (obs : St → Obs) (obs' : St' → Obs)
    (hObs : ∀ st b, obs' (f (st, b)) = obs st)
    (Inv : Nat → St → Prop) (hMono : ∀ {n m st}, n ≤ m → Inv n st → Inv m st)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (SigStepResultPrim St (GSpec.Range q)))
    (step' : (q : ιI) → St' → OracleComp (PrimBaseSpec + sigOracleSpec) (GSpec.Range q × St'))
    (K : Nat)
    (hStepEq : ∀ q st b, Inv K st → step' q (f (st, b)) = sigLiftStep f (step q) st b)
    (hStepInv : ∀ n q st, Inv n st → HoldsOnLeaves (SigResInv (Inv (n + 1))) (step q st))
    (mx : OracleComp (unifSpec + GSpec) α) (rem : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => q.isRight = true) rem)
    (n : Nat) (st : St) (b : Nat) (hInv : Inv n st) (hBound : n + rem ≤ K) :
    Prod.map id obs' <$> runWithIfaceStep pqxdhEufCmaIface step' mx (f (st, b)) =
      Prod.map id obs <$> runWithSigBudgetPrim step mx st b := by
  rw [runWithIfaceStep_pqSigIface_eq_runWithSigStep]
  exact runWithSigStep_map_state_bounded f obs obs' hObs Inv hMono step step' K hStepEq hStepInv
    mx rem hMx n st b hInv hBound

abbrev embedPrim_mapML := @embedPrim_mapMPrim
abbrev embedPrim_consumeFirstML := @embedPrim_consumeFirstMPrim
abbrev sigLiftK₀ := @sigLiftK
abbrev sigLiftStep₀ := @sigLiftStep

theorem GRed_eval_pqSigIface {κ : Type} {G : OracleSpec κ} {C : GameCodec pqSig G}
    {rIn aIn aOut out : Ty pqSig} (R : CostedReduction pqxdhOps pqxdhEufCmaIface G C rIn aIn aOut out)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote) :
    R.eval A x =
      (do
        let p ← R.init.eval (.cons x .nil)
        let y ← runWithIfaceStep pqxdhEufCmaIface
          (fun q st => do
            let p ← R.handle.eval (.cons st (.cons (C.qenc q) .nil))
            return (C.rdec q p.1, p.2))
          (A p.1) p.2
        R.finish.eval (.cons y.2 (.cons y.1 .nil))) := by
  unfold CostedReduction.eval CostedReduction.impl
  refine bind_congr fun ⟨a, s⟩ => ?_
  dsimp only
  rw [simulateQ_handlerImpl_eq_runWithIfaceStep]

end SignalPqxdh.Security.ReductionDsl
