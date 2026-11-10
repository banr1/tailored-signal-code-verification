/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhIkInv
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpkInv
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Hop 4 (`G3 → G3.5`): `G3` with an Adversary `advRoLog`

Extends `keyIndExpG3` with a log `advRoLog` of adversary `.roQuery` inputs, proves its projections
onto `keyIndExpG3` and `runKeyIndFgSim`, and defines the `secb`-branch runs and state erasure.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security

export _root_.SignalPqxdh.Security.RoKem (extractDh1 extractDh3 spkBundleFlatIdx)

def badKeyIndFgAny4 {S : Setup} (P : Primitives) (maxLen : ℕ)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  badKeyIndFgAny P maxLen st advRoLog ||
  ((List.range S.N_send_tot).any (fun sIdx =>
    (List.range S.N_id).any (fun kIdx =>
      badKeyIndFgDh2At P maxLen sIdx kIdx st advRoLog))) ||
  ((List.range S.N_send_opk_tot).any (fun sIdx =>
    (List.range S.N_opk_tot).any (fun oIdx =>
      badKeyIndFgDh4At P maxLen sIdx oIdx st advRoLog)))

theorem probExpect_add_le_fg {α : Type} (mx : ProbComp α) (f g h : α → ℝ≥0∞)
    (hle : ∀ x, f x ≤ g x + h x) :
    probExpect mx f ≤ probExpect mx g + probExpect mx h := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  unfold probExpect
  calc ∫⁻ a, f a ∂𝒟[mx]
      ≤ ∫⁻ a, (g a + h a) ∂𝒟[mx] := MeasureTheory.lintegral_mono hle
    _ = (∫⁻ a, g a ∂𝒟[mx]) + (∫⁻ a, h a ∂𝒟[mx]) :=
        MeasureTheory.lintegral_add_left Measurable.of_discrete _

/-! ## Extended `G3` simulation with `advRoLog` -/

/-- Extended `KeyInd` state pairing `KeyIndShCrState S` with the adversary RO log `advRoLog`. -/
structure KeyIndAdvCutoffState (S : Setup) where
  shCr     : KeyIndShCrState S
  advRoLog : List Bytes := []

def KeyIndAdvCutoffState.toFg {S : Setup} (hst : KeyIndAdvCutoffState S) :
    KeyIndFgCutoffState S :=
  { base := hst.shCr.base, advRoLog := hst.advRoLog }

def liftKeyIndAdvShCr {S : Setup} {α : Type}
    (m : StateT (KeyIndShCrState S) ProbComp α) :
    StateT (KeyIndAdvCutoffState S) ProbComp α :=
  StateT.mk fun hst => do
    let (r, shCr') ← m.run hst.shCr
    return (r, { hst with shCr := shCr' })

/-- `G3` oracle implementation appending adversary `.roQuery` inputs to `advRoLog`. -/
def pqxdhKeyIndAdvG3Impl (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndAdvCutoffState S) ProbComp)
  | .roQuery sec =>
    StateT.mk fun hst => do
      let (r, shCr') ← (pqxdhKeyIndShCrImpl false S P (.roQuery sec)).run hst.shCr
      return (r, { shCr := shCr', advRoLog := sec :: hst.advRoLog })
  | q => liftKeyIndAdvShCr (pqxdhKeyIndShCrImpl false S P q)

theorem liftKeyIndAdvShCr_shCr {S : Setup} {α : Type}
    (m : StateT (KeyIndShCrState S) ProbComp α) (hst : KeyIndAdvCutoffState S) :
    Prod.map id KeyIndAdvCutoffState.shCr <$> ((liftKeyIndAdvShCr m).run hst) =
      m.run hst.shCr := by
  simp [liftKeyIndAdvShCr, StateT.run_mk, Prod.map]

theorem pqxdhKeyIndAdvG3Impl_shCr {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndAdvCutoffState S) :
    Prod.map id KeyIndAdvCutoffState.shCr <$> ((pqxdhKeyIndAdvG3Impl S P q).run hst) =
      (pqxdhKeyIndShCrImpl false S P q).run hst.shCr := by
  cases q with
  | roQuery sec =>
    simp [pqxdhKeyIndAdvG3Impl, StateT.run_mk, Prod.map]
  | initPrin u => exact liftKeyIndAdvShCr_shCr _ hst
  | corruptIK u => exact liftKeyIndAdvShCr_shCr _ hst
  | genSPK u j => exact liftKeyIndAdvShCr_shCr _ hst
  | genOPK u j k => exact liftKeyIndAdvShCr_shCr _ hst
  | initiateOPK u i bundle => exact liftKeyIndAdvShCr_shCr _ hst
  | initiateNoOPK u i bundle => exact liftKeyIndAdvShCr_shCr _ hst
  | acceptOPK u j k hdr => exact liftKeyIndAdvShCr_shCr _ hst
  | acceptNoOPK u j l hdr => exact liftKeyIndAdvShCr_shCr _ hst
  | testSession sid => exact liftKeyIndAdvShCr_shCr _ hst
  | revealSessionKey sid => exact liftKeyIndAdvShCr_shCr _ hst
  | revealDhSecrets => exact liftKeyIndAdvShCr_shCr _ hst
  | registerKey sk => exact liftKeyIndAdvShCr_shCr _ hst
  | revealSpkSk u j => exact liftKeyIndAdvShCr_shCr _ hst

theorem simulateQ_pqxdhKeyIndAdvG3Impl_shCr {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndAdvCutoffState S) :
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl S P
    let fullShCr := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyIndShCrImpl false S P
    Prod.map id KeyIndAdvCutoffState.shCr <$> ((simulateQ fullAdv oa).run hst) =
      (simulateQ fullShCr oa).run hst.shCr := by
  intro fullAdv fullShCr
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure, Prod.map]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullAdv, fullShCr]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, map_bind]
      congr 1; funext u
      exact ih u hst
    | inr gq =>
      dsimp only [fullAdv, fullShCr]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr, map_bind]
      rw [← pqxdhKeyIndAdvG3Impl_shCr P gq hst, bind_map_left]
      congr 1; funext y
      exact ih y.1 y.2

/-- Run the `G3` simulation recording `advRoLog` alongside `KeyIndShCrState S`. -/
noncomputable def runKeyIndAdvG3Sim (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp (Bool × Bool × KeyIndAdvCutoffState S) := do
  let secb ← $ᵗ Bool
  let initSt : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

theorem runKeyIndAdvG3Sim_shCr (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    Prod.map id (Prod.map id KeyIndAdvCutoffState.shCr) <$> runKeyIndAdvG3Sim S P A =
      runKeyIndShCrSim S P A := by
  unfold runKeyIndAdvG3Sim runKeyIndShCrSim
  rw [map_bind]
  congr 1; funext secb
  dsimp only
  have hSim := simulateQ_pqxdhKeyIndAdvG3Impl_shCr P A.run
    { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] }
  dsimp only at hSim
  rw [← hSim, bind_map_left]
  simp [Prod.map, map_eq_bind_pure_comp, bind_assoc]

noncomputable def finalizeKeyIndG3 (S : Setup) (P : Primitives)
    (secb b' : Bool) (finalHst : KeyIndShCrState S) : ProbComp Bool :=
  let finalSt := finalHst.base
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.sessions r)
  if (((!allTestedClean || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt) ||
      hasKemPkCollisionKeyInd finalSt) ||
     hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs then
    $ᵗ Bool
  else
    pure (b' == secb)

noncomputable def finalizeKeyIndG3Post (S : Setup) (P : Primitives)
    (b' : Bool) (finalHst : KeyIndShCrState S) : ProbComp Bool :=
  let finalSt := finalHst.base
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.sessions r)
  if (((!allTestedClean || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt) ||
      hasKemPkCollisionKeyInd finalSt) ||
     hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs then
    $ᵗ Bool
  else
    pure b'

theorem evalDist_uniformBool_beq_fg (b : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun z => pure (b == z)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  cases b
  · simpa using ProbComp.evalDist_bind_not_uniformBool (fun z => (pure z : ProbComp Bool))
  · simp

theorem evalDist_finalizeKeyIndG3_eq_post_beq (S : Setup) (P : Primitives)
    (secb b' : Bool) (finalHst : KeyIndShCrState S) :
    𝒟[finalizeKeyIndG3 S P secb b' finalHst] =
    𝒟[finalizeKeyIndG3Post S P b' finalHst >>= fun z => pure (secb == z)] := by
  unfold finalizeKeyIndG3 finalizeKeyIndG3Post
  dsimp only
  split_ifs with hbad
  · exact (evalDist_uniformBool_beq_fg secb).symm
  · simp [Bool.beq_comm]

theorem keyIndExpG3_eq_advG3Sim (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyIndExpG3 S P A = (do
      let (secb, b', finalHst) ← runKeyIndAdvG3Sim S P A
      finalizeKeyIndG3 S P secb b' finalHst.shCr) := by
  unfold keyIndExpG3 finalizeKeyIndG3
  rw [← runKeyIndAdvG3Sim_shCr S P A, bind_map_left]
  rfl

/-! ## Projection to `runKeyIndFgSim` -/

theorem liftKeyIndAdvShCr_toFg {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndAdvCutoffState S) :
    Prod.map id KeyIndAdvCutoffState.toFg <$>
      ((liftKeyIndAdvShCr (pqxdhKeyIndShCrImpl false S P q)).run hst) =
      (do
        let (r, base') ← (pqxdhKeyIndImpl true S P q).run hst.shCr.base
        pure (r, { base := base', advRoLog := hst.advRoLog })) := by
  have hBase := map_base_pqxdhKeyIndShCrImpl_false S P q hst.shCr
  rw [← hBase]
  simp [liftKeyIndAdvShCr, StateT.run_mk, Prod.map, KeyIndAdvCutoffState.toFg,
    map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndAdvG3Impl_toFg {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndAdvCutoffState S) :
    Prod.map id KeyIndAdvCutoffState.toFg <$> ((pqxdhKeyIndAdvG3Impl S P q).run hst) =
      (pqxdhKeyIndFgImpl S P q).run hst.toFg := by
  cases q with
  | roQuery sec =>
    have hBase := map_base_pqxdhKeyIndShCrImpl_false S P (.roQuery sec) hst.shCr
    dsimp only [pqxdhKeyIndAdvG3Impl, pqxdhKeyIndFgImpl, KeyIndAdvCutoffState.toFg]
    rw [StateT.run_mk, StateT.run_mk, ← hBase]
    simp [Prod.map, KeyIndAdvCutoffState.toFg, map_eq_bind_pure_comp, bind_assoc]
  | initPrin u => exact liftKeyIndAdvShCr_toFg P (.initPrin u) hst
  | corruptIK u => exact liftKeyIndAdvShCr_toFg P (.corruptIK u) hst
  | genSPK u j => exact liftKeyIndAdvShCr_toFg P (.genSPK u j) hst
  | genOPK u j k => exact liftKeyIndAdvShCr_toFg P (.genOPK u j k) hst
  | initiateOPK u i bundle => exact liftKeyIndAdvShCr_toFg P (.initiateOPK u i bundle) hst
  | initiateNoOPK u i bundle => exact liftKeyIndAdvShCr_toFg P (.initiateNoOPK u i bundle) hst
  | acceptOPK u j k hdr => exact liftKeyIndAdvShCr_toFg P (.acceptOPK u j k hdr) hst
  | acceptNoOPK u j l hdr => exact liftKeyIndAdvShCr_toFg P (.acceptNoOPK u j l hdr) hst
  | testSession sid => exact liftKeyIndAdvShCr_toFg P (.testSession sid) hst
  | revealSessionKey sid => exact liftKeyIndAdvShCr_toFg P (.revealSessionKey sid) hst
  | revealDhSecrets => exact liftKeyIndAdvShCr_toFg P .revealDhSecrets hst
  | registerKey sk => exact liftKeyIndAdvShCr_toFg P (.registerKey sk) hst
  | revealSpkSk u j => exact liftKeyIndAdvShCr_toFg P (.revealSpkSk u j) hst

theorem simulateQ_pqxdhKeyIndAdvG3Impl_toFg {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndAdvCutoffState S) :
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl S P
    let fullFg := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyIndFgImpl S P
    Prod.map id KeyIndAdvCutoffState.toFg <$> ((simulateQ fullAdv oa).run hst) =
      (simulateQ fullFg oa).run hst.toFg := by
  intro fullAdv fullFg
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure, Prod.map]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullAdv, fullFg]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, map_bind]
      congr 1; funext u
      exact ih u hst
    | inr gq =>
      dsimp only [fullAdv, fullFg]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr, map_bind]
      rw [← pqxdhKeyIndAdvG3Impl_toFg P gq hst, bind_map_left]
      congr 1; funext y
      exact ih y.1 y.2

theorem runKeyIndAdvG3Sim_toFg (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    Prod.map id (Prod.map id KeyIndAdvCutoffState.toFg) <$> runKeyIndAdvG3Sim S P A =
      runKeyIndFgSim S P A := by
  unfold runKeyIndAdvG3Sim runKeyIndFgSim
    _root_.Proofs.SignalPqxdh.Security.FgGapDh.KeyIndFgCutoffState.empty
  rw [map_bind]
  congr 1; funext secb
  dsimp only
  have hSim := simulateQ_pqxdhKeyIndAdvG3Impl_toFg P A.run
    { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] }
  dsimp only [KeyIndAdvCutoffState.toFg] at hSim
  rw [← hSim, bind_map_left]
  simp [Prod.map, KeyIndAdvCutoffState.toFg, map_eq_bind_pure_comp, bind_assoc]

theorem badKeyIndFgAny_runKeyIndAdvG3Sim_eq_runKeyIndFgSim
    (S : Setup) (P : Primitives) (maxLen : ℕ) (A : KeyIndAdversary S) :
    (runKeyIndAdvG3Sim S P A >>= fun x =>
      pure (badKeyIndFgAny4 P maxLen x.2.2.shCr.base x.2.2.advRoLog)) =
    (runKeyIndFgSim S P A >>= fun x =>
      pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)) := by
  rw [← runKeyIndAdvG3Sim_toFg S P A, bind_map_left]
  rfl

/-! ## Branch runs and test-session implementation -/

/-- Branch execution of `pqxdhKeyIndAdvG3Impl` starting from `KeyIndState.empty S secb` and
    applying `finalizeKeyIndG3Post`. -/
noncomputable def keyIndAdvG3Branch (secb : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp Bool := do
  let initSt : KeyIndAdvCutoffState S :=
    { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  finalizeKeyIndG3Post S P b' finalHst.shCr

def withSecbBase {S : Setup} (b : Bool) (st : KeyIndState S) : KeyIndState S :=
  { st with secb := b }

def withSecbShCr {S : Setup} (b : Bool) (hst : KeyIndShCrState S) : KeyIndShCrState S :=
  { hst with base := withSecbBase b hst.base }

def withSecbAdv {S : Setup} (b : Bool) (hst : KeyIndAdvCutoffState S) : KeyIndAdvCutoffState S :=
  { hst with shCr := withSecbShCr b hst.shCr }

@[simp] theorem isFreshKeyIndSession_withSecbBase {S : Setup} (b : Bool)
    (st : KeyIndState S) (sid : SessionId S) :
    isKeyIndSessionTestable (withSecbBase b st) sid = isKeyIndSessionTestable st sid := rfl

@[simp] theorem finalizeKeyIndG3_withSecbShCr {S : Setup} (P : Primitives) (b secb b' : Bool)
    (hst : KeyIndShCrState S) :
    finalizeKeyIndG3 S P secb b' (withSecbShCr b hst) = finalizeKeyIndG3 S P secb b' hst := rfl

@[simp] theorem badKeyIndFgAny_withSecbBase {S : Setup} (P : Primitives) (maxLen : ℕ) (b : Bool)
    (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgAny4 P maxLen (withSecbBase b st) advRoLog =
      badKeyIndFgAny4 P maxLen st advRoLog := rfl

def runKeyIndTestSession (testReal : Bool) (S : Setup) (sid : SessionId S) :
    StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if !isKeyIndSessionTestable st sid then
    return .noneResp
  match st.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    let sessions' := st.sessions.map (fun s =>
      if s.sid == sid then { s with tested := true } else s)
    set { st with sessions := sessions' }
    return .drKeyResp (if testReal then e.drKeyReal else e.drKeyRand)
  | none =>
    match st.respSessions.find? (fun r => r.sid == sid) with
    | none => return .noneResp
    | some r =>
      let resp' := st.respSessions.map (fun x =>
        if x.sid == sid then { x with tested := true } else x)
      set { st with respSessions := resp' }
      return .drKeyResp (if testReal then r.drKeyReal else r.drKeyRand)

def pqxdhKeyIndAdvTestImpl (testReal : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndAdvCutoffState S) ProbComp)
  | .testSession sid =>
    liftKeyIndAdvShCr (liftKeyIndShCrBase (runKeyIndTestSession testReal S sid))
  | q => pqxdhKeyIndAdvG3Impl S P q

theorem runKeyIndTestSession_withSecbBase (testReal b : Bool) (S : Setup)
    (sid : SessionId S) (st : KeyIndState S) :
    (runKeyIndTestSession testReal S sid).run (withSecbBase b st) =
      Prod.map id (withSecbBase b) <$> (runKeyIndTestSession testReal S sid).run st := by
  have hFresh : isKeyIndSessionTestable (withSecbBase b st) sid = isKeyIndSessionTestable st sid := rfl
  unfold runKeyIndTestSession
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hFresh]
  unfold withSecbBase
  dsimp only
  by_cases h : (!isKeyIndSessionTestable st sid) = true
  · simp [h, StateT.run_pure, Prod.map]
  · simp only [h]
    cases st.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only
      simp [StateT.run_set, Prod.map]
    | none =>
      dsimp only
      cases st.respSessions.find? (fun r => r.sid == sid) with
      | none => simp [StateT.run_pure, Prod.map]
      | some r =>
        dsimp only
        simp [StateT.run_set, Prod.map]

theorem finishKeyIndBase_withSecbBase (b : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (uEntry : PrincipalEntry)
    (ekASk ss kemCt : Bytes) (st : KeyIndState S) :
    finishKeyIndBase S P sid bundle uEntry ekASk ss kemCt (withSecbBase b st) =
      Prod.map id (Option.map (withSecbBase b)) <$>
        finishKeyIndBase S P sid bundle uEntry ekASk ss kemCt st := by
  unfold finishKeyIndBase withSecbBase
  dsimp only
  simp only [map_bind]
  congr 1; funext ⟨drKeyReal, roCache'⟩
  cases keyIndPartnerRandKey? P st.respSessions _ <;>
    simp [Prod.map, map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndImpl_withSecbBase_of_ne_testSession (b : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hNe : ∀ sid, q ≠ .testSession sid)
    (hNeInit1 : ∀ u i bundle, q ≠ .initiateOPK u i bundle)
    (hNeInit2 : ∀ u i bundle, q ≠ .initiateNoOPK u i bundle)
    (st : KeyIndState S) :
    (pqxdhKeyIndImpl true S P q).run (withSecbBase b st) =
      Prod.map id (withSecbBase b) <$> (pqxdhKeyIndImpl true S P q).run st := by
  cases q with
  | testSession sid => exact False.elim (hNe sid rfl)
  | initiateOPK u i bundle => exact False.elim (hNeInit1 u i bundle rfl)
  | initiateNoOPK u i bundle => exact False.elim (hNeInit2 u i bundle rfl)
  | initPrin u =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp [StateT.run_pure, StateT.run_set, StateT.run_monadLift,
      Prod.map, map_eq_bind_pure_comp, bind_assoc]
  | corruptIK u =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]
  | genSPK u j =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, Prod.map]
    · cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some p =>
        simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
          Prod.map, map_eq_bind_pure_comp, bind_assoc]
  | genOPK u j k =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, Prod.map]
    · simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
        Prod.map, map_eq_bind_pure_comp, bind_assoc]
  | acceptOPK k j o hdr =>
    unfold pqxdhKeyIndImpl recordKeyIndResp withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, Prod.map]
    · simp [StateT.run_pure, Prod.map]
    · simp [StateT.run_pure, Prod.map]
    · cases st.principals.find? (fun (idx, _) => idx == k.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some kp =>
        cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => simp [StateT.run_pure, Prod.map]
        | some bp =>
          cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none => simp [StateT.run_pure, Prod.map]
          | some op =>
            dsimp only
            split_ifs
            · simp [StateT.run_pure, Prod.map]
            · cases Model.acceptKeys P _ with
              | none => simp [StateT.run_pure, Prod.map]
              | some _ =>
                cases P.kemDecaps bp.2.pqspkSk hdr.kemCt with
                | none => simp [StateT.run_pure, Prod.map]
                | some ss =>
                  dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self]
                  simp only [bind_assoc, pure_bind, StateT.run_set, StateT.run_get, map_bind]
                  congr 1; funext ⟨drKey, roCache'⟩
                  cases st.sessions.find? (fun s => keyIndPartner P s _) <;>
                    cases findHonestPrincipal P st.principals hdr.ikAPk <;>
                    simp [StateT.run_bind, StateT.run_pure, StateT.run_set, StateT.run_monadLift,
                      Prod.map, map_eq_bind_pure_comp, bind_assoc]
  | acceptNoOPK k j l hdr =>
    unfold pqxdhKeyIndImpl recordKeyIndResp withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp [StateT.run_pure, Prod.map]
    · simp [StateT.run_pure, Prod.map]
    · simp [StateT.run_pure, Prod.map]
    · cases st.principals.find? (fun (idx, _) => idx == k.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some kp =>
        cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => simp [StateT.run_pure, Prod.map]
        | some bp =>
          dsimp only
          cases Model.acceptKeys P _ with
          | none => simp [StateT.run_pure, Prod.map]
          | some _ =>
            cases P.kemDecaps bp.2.pqspkSk hdr.kemCt with
            | none => simp [StateT.run_pure, Prod.map]
            | some ss =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self]
              simp only [bind_assoc, pure_bind, StateT.run_set, StateT.run_get, map_bind]
              congr 1; funext ⟨drKey, roCache'⟩
              cases st.sessions.find? (fun s => keyIndPartner P s _) <;>
                cases findHonestPrincipal P st.principals hdr.ikAPk <;>
                simp [StateT.run_bind, StateT.run_pure, StateT.run_set, StateT.run_monadLift,
                  Prod.map, map_eq_bind_pure_comp, bind_assoc]
  | revealSessionKey sid =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only
      split_ifs <;> simp [StateT.run_pure, StateT.run_set, Prod.map]
    | none =>
      dsimp only
      cases st.respSessions.find? (fun r => r.sid == sid) with
      | none => simp [StateT.run_pure, Prod.map]
      | some r =>
        dsimp only
        split_ifs <;> simp [StateT.run_pure, StateT.run_set, Prod.map]
  | roQuery sec =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
      StateT.run_pure, Prod.map, map_eq_bind_pure_comp, bind_assoc]
  | revealDhSecrets =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp [StateT.run_pure, Prod.map]
  | registerKey sk =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases registerAdvKey P st.advKeys sk <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]
  | revealSpkSk u j =>
    unfold pqxdhKeyIndImpl withSecbBase
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;>
      simp [StateT.run_pure, StateT.run_set, Prod.map]

theorem liftShCrBase_withSecbShCr {S : Setup} {α : Type} (b : Bool)
    (m : StateT (KeyIndState S) ProbComp α) (hst : KeyIndShCrState S)
    (hm : m.run (withSecbBase b hst.base) = Prod.map id (withSecbBase b) <$> m.run hst.base) :
    (liftShCrBase m).run (withSecbShCr b hst) =
      Prod.map id (withSecbShCr b) <$> (liftShCrBase m).run hst := by
  change (do let (a, base') ← m.run (withSecbBase b hst.base); pure (a,
    { withSecbShCr b hst with base := base' })) =
    Prod.map id (withSecbShCr b) <$> (do let (a, base') ← m.run hst.base; pure (a,
      { hst with base := base' }))
  rw [hm, bind_map_left, map_bind]
  rfl

theorem applyShCrFinish_withSecbShCr {S : Setup} {Resp : Type} (b : Bool)
    (sid : SessionId S) (pqspkPk ss kemCt : Bytes) (hst : KeyIndShCrState S)
    (out : Resp × Option (KeyIndState S)) :
    applyShCrFinish sid pqspkPk ss kemCt (withSecbShCr b hst)
      (Prod.map id (Option.map (withSecbBase b)) out) =
      Prod.map id (withSecbShCr b) (applyShCrFinish sid pqspkPk ss kemCt hst out) := by
  rcases out with ⟨resp, none | base'⟩ <;> rfl

theorem runKeyIndShCrInitiate_false_withSecbShCr (b : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (hst : KeyIndShCrState S) :
    (runKeyIndShCrInitiate false S P sid u bundle).run (withSecbShCr b hst) =
      Prod.map id (withSecbShCr b) <$>
        (runKeyIndShCrInitiate false S P sid u bundle).run hst := by
  unfold runKeyIndShCrInitiate runShCrInitiate2
  have hPre : preCheckKeyInd S P sid u bundle (withSecbShCr b hst).base =
      preCheckKeyInd S P sid u bundle hst.base := rfl
  have h2 : (withSecbShCr b hst).base.principals = hst.base.principals := rfl
  simp only [StateT.run, hPre, h2]
  cases preCheckKeyInd S P sid u bundle hst.base with
  | none => simp [Prod.map]
  | some uEntry =>
    dsimp only [Option.map]
    simp only [map_bind]
    congr 1; funext ekASk; congr 1; funext kemCoins
    split_ifs
    · simp [Prod.map]
    · cases h5 : P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp [withSecbShCr, Prod.map]
      | some kp =>
        have hFin := finishKeyIndBase_withSecbBase b S P sid bundle uEntry ekASk kp.1 kp.2 hst.base
        change applyShCrFinish sid bundle.pqspkB kp.1 kp.2 (withSecbShCr b hst) <$>
          finishKeyIndBase S P sid bundle uEntry ekASk kp.1 kp.2 (withSecbBase b hst.base) = _
        rw [hFin, Functor.map_map, Functor.map_map]
        congr 1; funext out
        exact applyShCrFinish_withSecbShCr b sid bundle.pqspkB kp.1 kp.2 hst out

theorem recordAcceptKemGeneric_withSecbShCr (b : Bool) (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr) (out : KeyIndResponse)
    (hst : KeyIndShCrState S) :
    (recordAcceptKemGeneric P KeyIndState.spkBundles isNoneKeyIndResp k j hdr out).run
      (withSecbShCr b hst) =
      Prod.map id (withSecbShCr b) <$>
        (recordAcceptKemGeneric P KeyIndState.spkBundles isNoneKeyIndResp k j hdr out).run hst := by
  unfold recordAcceptKemGeneric
  have h1 : (withSecbShCr b hst).base.spkBundles = hst.base.spkBundles := rfl
  simp only [StateT.run, h1]
  split_ifs
  · simp [Prod.map]
  · cases h2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => simp [Prod.map]
    | some bp =>
      rcases bp with ⟨idx, bEntry⟩
      dsimp only
      cases h3 : P.kemDecaps bEntry.pqspkSk hdr.kemCt <;> simp [withSecbShCr]

theorem pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession (b : Bool) (S : Setup) (P :
  Primitives)
    (q : KeyIndQuery S) (hNe : ∀ sid, q ≠ .testSession sid) (hst : KeyIndShCrState S) :
    (pqxdhKeyIndShCrImpl false S P q).run (withSecbShCr b hst) =
      Prod.map id (withSecbShCr b) <$> (pqxdhKeyIndShCrImpl false S P q).run hst := by
  cases q with
  | testSession sid => exact False.elim (hNe sid rfl)
  | genSPK u j =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.genSPK u j)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.genSPK u j)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)
  | initiateOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrImpl]
    split_ifs
    · simp [StateT.run_pure, Prod.map]
    · exact runKeyIndShCrInitiate_false_withSecbShCr b S P (.sendOPK u i) u bundle hst
  | initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyIndShCrImpl]
    split_ifs
    · simp [StateT.run_pure, Prod.map]
    · exact runKeyIndShCrInitiate_false_withSecbShCr b S P (.sendNoOPK u i) u bundle hst
  | acceptOPK k j o hdr =>
    unfold pqxdhKeyIndShCrImpl runShCrAcceptGeneric
    simp only [StateT.run_bind, map_bind]
    rw [liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.acceptOPK k j o hdr)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.acceptOPK k j o hdr)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base),
      bind_map_left]
    congr 1; funext y
    exact recordAcceptKemGeneric_withSecbShCr b S P k j hdr y.1 y.2
  | acceptNoOPK k j l hdr =>
    unfold pqxdhKeyIndShCrImpl runShCrAcceptGeneric
    simp only [StateT.run_bind, map_bind]
    rw [liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.acceptNoOPK k j l hdr)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.acceptNoOPK k j l hdr)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base),
      bind_map_left]
    congr 1; funext y
    exact recordAcceptKemGeneric_withSecbShCr b S P k j hdr y.1 y.2
  | initPrin u =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.initPrin u)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.initPrin u)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)
  | corruptIK u =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.corruptIK u)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.corruptIK u)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)
  | genOPK u j o =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.genOPK u j o)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.genOPK u j o)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)
  | revealSessionKey sid =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.revealSessionKey sid)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.revealSessionKey sid)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)
  | roQuery sec =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.roQuery sec)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.roQuery sec)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)
  | revealDhSecrets =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P .revealDhSecrets) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P .revealDhSecrets
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)
  | registerKey sk =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.registerKey sk)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.registerKey sk)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)
  | revealSpkSk u j =>
    exact liftShCrBase_withSecbShCr b (pqxdhKeyIndImpl true S P (.revealSpkSk u j)) hst
      (pqxdhKeyIndImpl_withSecbBase_of_ne_testSession b S P (.revealSpkSk u j)
        (by intro _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ _ _ h; cases h) hst.base)

theorem liftKeyIndAdvShCr_withSecbAdv {S : Setup} (b : Bool)
    (m : StateT (KeyIndShCrState S) ProbComp KeyIndResponse) (hst : KeyIndAdvCutoffState S)
    (hm : m.run (withSecbShCr b hst.shCr) = Prod.map id (withSecbShCr b) <$> m.run hst.shCr) :
    (liftKeyIndAdvShCr m).run (withSecbAdv b hst) =
      Prod.map id (withSecbAdv b) <$> (liftKeyIndAdvShCr m).run hst := by
  simp [liftKeyIndAdvShCr, StateT.run_mk, withSecbAdv, hm, Prod.map,
    map_eq_bind_pure_comp, bind_assoc]

theorem pqxdhKeyIndAdvG3Impl_withSecbAdv_eq_testImpl (b : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndAdvCutoffState S) :
    (pqxdhKeyIndAdvG3Impl S P q).run (withSecbAdv b hst) =
      Prod.map id (withSecbAdv b) <$> (pqxdhKeyIndAdvTestImpl b S P q).run hst := by
  cases q with
  | testSession sid =>
    have hTest : (pqxdhKeyIndShCrImpl false S P (.testSession sid)).run (withSecbShCr b hst.shCr) =
        Prod.map id (withSecbShCr b) <$>
          (liftKeyIndShCrBase (runKeyIndTestSession b S sid)).run hst.shCr := by
      change (liftShCrBase (pqxdhKeyIndImpl true S P (.testSession sid))).run (withSecbShCr b
        hst.shCr) =
        Prod.map id (withSecbShCr b) <$> (liftShCrBase (runKeyIndTestSession b S sid)).run hst.shCr
      rw [← liftShCrBase_withSecbShCr b (runKeyIndTestSession b S sid) hst.shCr
        (runKeyIndTestSession_withSecbBase b b S sid hst.shCr.base)]
      rfl
    change (do let (r, shCr') ← (pqxdhKeyIndShCrImpl false S P (.testSession sid)).run (withSecbShCr
      b hst.shCr)
               pure (r, { withSecbAdv b hst with shCr := shCr' })) =
      Prod.map id (withSecbAdv b) <$>
        (do let (r, shCr') ← (liftKeyIndShCrBase (runKeyIndTestSession b S sid)).run hst.shCr
            pure (r, { hst with shCr := shCr' }))
    rw [hTest, bind_map_left, map_bind]
    rfl
  | roQuery sec =>
    dsimp only [pqxdhKeyIndAdvG3Impl, pqxdhKeyIndAdvTestImpl]
    have hShCr := pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.roQuery sec)
      (by intro _ h; cases h) hst.shCr
    simp [StateT.run_mk, withSecbAdv, hShCr, Prod.map, map_eq_bind_pure_comp, bind_assoc]
  | initPrin u =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.initPrin u)) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.initPrin u)
        (by intro _ h; cases h) hst.shCr)
  | corruptIK u =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.corruptIK u)) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.corruptIK u)
        (by intro _ h; cases h) hst.shCr)
  | genSPK u j =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.genSPK u j)) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.genSPK u j)
        (by intro _ h; cases h) hst.shCr)
  | genOPK u j k =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.genOPK u j k)) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.genOPK u j k)
        (by intro _ h; cases h) hst.shCr)
  | initiateOPK u i bundle =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.initiateOPK u i bundle))
      hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.initiateOPK u i bundle)
        (by intro _ h; cases h) hst.shCr)
  | initiateNoOPK u i bundle =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.initiateNoOPK u i
      bundle)) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.initiateNoOPK u i bundle)
        (by intro _ h; cases h) hst.shCr)
  | acceptOPK u j k hdr =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.acceptOPK u j k hdr)) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.acceptOPK u j k hdr)
        (by intro _ h; cases h) hst.shCr)
  | acceptNoOPK u j l hdr =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.acceptNoOPK u j l hdr))
      hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.acceptNoOPK u j l hdr)
        (by intro _ h; cases h) hst.shCr)
  | revealSessionKey sid =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.revealSessionKey sid))
      hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.revealSessionKey sid)
        (by intro _ h; cases h) hst.shCr)
  | revealDhSecrets =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P .revealDhSecrets) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P .revealDhSecrets
        (by intro _ h; cases h) hst.shCr)
  | registerKey sk =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.registerKey sk)) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.registerKey sk)
        (by intro _ h; cases h) hst.shCr)
  | revealSpkSk u j =>
    exact liftKeyIndAdvShCr_withSecbAdv b (pqxdhKeyIndShCrImpl false S P (.revealSpkSk u j)) hst
      (pqxdhKeyIndShCrImpl_false_withSecbShCr_of_ne_testSession b S P (.revealSpkSk u j)
        (by intro _ h; cases h) hst.shCr)

theorem simulateQ_pqxdhKeyIndAdvG3Impl_withSecbAdv {S : Setup} {α : Type} (b : Bool) (P :
  Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndAdvCutoffState S) :
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvG3Impl S P
    let fullTest := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndAdvCutoffState S) ProbComp) + pqxdhKeyIndAdvTestImpl b S P
    ((simulateQ fullAdv oa).run (withSecbAdv b hst)) =
      Prod.map id (withSecbAdv b) <$> ((simulateQ fullTest oa).run hst) := by
  intro fullAdv fullTest
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure, Prod.map]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullAdv, fullTest]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, map_bind]
      congr 1; funext u
      exact ih u hst
    | inr gq =>
      dsimp only [fullAdv, fullTest]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr,
        pqxdhKeyIndAdvG3Impl_withSecbAdv_eq_testImpl b S P gq hst,
        bind_map_left, map_bind]
      congr 1; funext y
      exact ih y.1 y.2

def eraseSessionKeys {S : Setup} (s : KeyIndInitiatorEntry S) : KeyIndInitiatorEntry S :=
  { s with drKeyReal := default, drKeyRand := default }

def eraseRespKeys {S : Setup} (r : KeyIndRespEntry S) : KeyIndRespEntry S :=
  { r with drKeyReal := default, drKeyRand := default }

def eraseStateKeysAndCache {S : Setup} (st : KeyIndState S) : KeyIndState S :=
  { st with
    secb         := true
    sessions     := st.sessions.map eraseSessionKeys
    respSessions := st.respSessions.map eraseRespKeys
    roCache      := [] }

def eraseShCrKeysAndCache {S : Setup} (hst : KeyIndShCrState S) : KeyIndShCrState S :=
  { hst with base := eraseStateKeysAndCache hst.base }

def isKeyIndG3Abort {S : Setup} (P : Primitives) (finalHst : KeyIndShCrState S) : Bool :=
  let finalSt := finalHst.base
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles
        finalSt.sessions r)
  (((!allTestedClean || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt) ||
    hasKemPkCollisionKeyInd finalSt) ||
   hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs

@[simp]
theorem finalizeKeyIndG3_eq_if_isKeyIndG3Abort (S : Setup) (P : Primitives)
    (secb b' : Bool) (finalHst : KeyIndShCrState S) :
    finalizeKeyIndG3 S P secb b' finalHst =
      if isKeyIndG3Abort P finalHst then $ᵗ Bool else pure (b' == secb) := rfl

theorem finalizeKeyIndG3_of_isKeyIndG3Abort (S : Setup) (P : Primitives)
    (secb b' : Bool) (finalHst : KeyIndShCrState S)
    (hAbort : isKeyIndG3Abort P finalHst = true) :
    finalizeKeyIndG3 S P secb b' finalHst = $ᵗ Bool := by
  rw [finalizeKeyIndG3_eq_if_isKeyIndG3Abort]
  simp [hAbort]

@[simp]
theorem keyIndPartner_eraseSessionKeys {S : Setup} (P : Primitives)
    (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    keyIndPartner P (eraseSessionKeys s) r = keyIndPartner P s r := rfl

@[simp]
theorem keyIndPartner_eraseRespKeys {S : Setup} (P : Primitives)
    (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    keyIndPartner P s (eraseRespKeys r) = keyIndPartner P s r := rfl

@[simp]
theorem isSessionStillFreshKeyInd_eraseSessionKeys {S : Setup} (P : Primitives) (useRo : Bool)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (s : KeyIndInitiatorEntry S) :
    keyIndInitCorruptionClause P useRo principals spkBundles (eraseSessionKeys s) =
      keyIndInitCorruptionClause P useRo principals spkBundles s := rfl

@[simp]
theorem isKeyIndInitStillFresh_erase {S : Setup} (P : Primitives) (useRo : Bool)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (respSessions : List (KeyIndRespEntry S))
    (s : KeyIndInitiatorEntry S) :
    isKeyIndInitStillFresh P useRo principals spkBundles (respSessions.map eraseRespKeys)
      (eraseSessionKeys s) =
      isKeyIndInitStillFresh P useRo principals spkBundles respSessions s := by
  unfold isKeyIndInitStillFresh
  rw [isSessionStillFreshKeyInd_eraseSessionKeys, List.all_map]
  rfl

theorem find_map_eraseSessionKeys {S : Setup} (P : Primitives)
    (sessions : List (KeyIndInitiatorEntry S)) (r : KeyIndRespEntry S) :
    (sessions.map eraseSessionKeys).find? (fun s => keyIndPartner P s (eraseRespKeys r)) =
      (sessions.find? (fun s => keyIndPartner P s r)).map eraseSessionKeys := by
  induction sessions with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.find?_cons, keyIndPartner_eraseSessionKeys,
      keyIndPartner_eraseRespKeys]
    cases keyIndPartner P s r
    · exact ih
    · rfl

@[simp]
theorem isKeyIndRespStillFresh_erase {S : Setup} (P : Primitives) (useRo : Bool)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (sessions : List (KeyIndInitiatorEntry S))
    (r : KeyIndRespEntry S) :
    isKeyIndRespStillFresh P useRo principals spkBundles (sessions.map eraseSessionKeys)
      (eraseRespKeys r) =
      isKeyIndRespStillFresh P useRo principals spkBundles sessions r := by
  unfold isKeyIndRespStillFresh
  rw [List.any_map, List.all_map]
  rfl

@[simp]
theorem allHonestEcPksKeyInd_eraseStateKeysAndCache {S : Setup} (P : Primitives) (st : KeyIndState
  S) :
    allHonestEcPksKeyInd P (eraseStateKeysAndCache st) = allHonestEcPksKeyInd P st := by
  unfold allHonestEcPksKeyInd eraseStateKeysAndCache HasKeyIndState.toKeyIndState
    instHasKeyIndStateKeyIndState
  dsimp only
  rw [List.map_map]
  rfl

@[simp]
theorem allInitDh2sKeyInd_eraseStateKeysAndCache {S : Setup} (P : Primitives) (st : KeyIndState S) :
    allInitDh2sKeyInd P (eraseStateKeysAndCache st) = allInitDh2sKeyInd P st := by
  unfold allInitDh2sKeyInd eraseStateKeysAndCache HasKeyIndState.toKeyIndState
    instHasKeyIndStateKeyIndState
  dsimp only
  rw [List.map_map]
  rfl

@[simp]
theorem hasEcPkCollisionKeyInd_eraseStateKeysAndCache {S : Setup} (P : Primitives) (st : KeyIndState
  S) :
    hasEcPkCollisionKeyInd P (eraseStateKeysAndCache st) = hasEcPkCollisionKeyInd P st := by
  unfold hasEcPkCollisionKeyInd
  rw [allHonestEcPksKeyInd_eraseStateKeysAndCache, allInitDh2sKeyInd_eraseStateKeysAndCache]

@[simp]
theorem hasBadSigKeyInd_eraseStateKeysAndCache {S : Setup} (st : KeyIndState S) :
    hasBadSigKeyInd (eraseStateKeysAndCache st) = hasBadSigKeyInd st := by
  unfold hasBadSigKeyInd eraseStateKeysAndCache HasKeyIndState.toKeyIndState
    instHasKeyIndStateKeyIndState
  dsimp only
  rw [List.any_map]
  rfl

@[simp]
theorem hasKemPkCollisionKeyInd_eraseStateKeysAndCache {S : Setup} (st : KeyIndState S) :
    hasKemPkCollisionKeyInd (eraseStateKeysAndCache st) = hasKemPkCollisionKeyInd st := rfl

@[simp]
theorem isKeyIndG3Abort_eraseShCrKeysAndCache {S : Setup} (P : Primitives)
    (finalHst : KeyIndShCrState S) :
    isKeyIndG3Abort P (eraseShCrKeysAndCache finalHst) = isKeyIndG3Abort P finalHst := by
  unfold isKeyIndG3Abort eraseShCrKeysAndCache
  dsimp only
  rw [hasEcPkCollisionKeyInd_eraseStateKeysAndCache,
      hasBadSigKeyInd_eraseStateKeysAndCache,
      hasKemPkCollisionKeyInd_eraseStateKeysAndCache]
  congr 4
  unfold eraseStateKeysAndCache
  dsimp only
  rw [List.all_map, List.all_map]
  have h1 : ((fun s => !s.tested || isKeyIndInitStillFresh P true finalHst.base.principals
        finalHst.base.spkBundles (List.map eraseRespKeys finalHst.base.respSessions) s) ∘
          eraseSessionKeys) =
      (fun s => !s.tested || isKeyIndInitStillFresh P true finalHst.base.principals
        finalHst.base.spkBundles finalHst.base.respSessions s) := by
    funext s
    dsimp only [Function.comp_apply]
    rw [isKeyIndInitStillFresh_erase]
    rfl
  have h2 : ((fun r => !r.tested || isKeyIndRespStillFresh P true finalHst.base.principals
        finalHst.base.spkBundles (List.map eraseSessionKeys finalHst.base.sessions) r) ∘
          eraseRespKeys) =
      (fun r => !r.tested || isKeyIndRespStillFresh P true finalHst.base.principals
        finalHst.base.spkBundles finalHst.base.sessions r) := by
    funext r
    dsimp only [Function.comp_apply]
    rw [isKeyIndRespStillFresh_erase]
    rfl
  rw [h1, h2]

@[simp]
theorem finalizeKeyIndG3_eraseShCrKeysAndCache (S : Setup) (P : Primitives)
    (secb b' : Bool) (finalHst : KeyIndShCrState S) :
    finalizeKeyIndG3 S P secb b' (eraseShCrKeysAndCache finalHst) =
      finalizeKeyIndG3 S P secb b' finalHst := by
  rw [finalizeKeyIndG3_eq_if_isKeyIndG3Abort, finalizeKeyIndG3_eq_if_isKeyIndG3Abort,
      isKeyIndG3Abort_eraseShCrKeysAndCache]

@[simp]
theorem badKeyIndFgDh1At_eraseStateKeysAndCache {S : Setup} (P : Primitives)
    (maxLen uIdx bIdx : ℕ) (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgDh1At P maxLen uIdx bIdx (eraseStateKeysAndCache st) advRoLog =
      badKeyIndFgDh1At P maxLen uIdx bIdx st advRoLog := by
  unfold badKeyIndFgDh1At eraseStateKeysAndCache
  dsimp only
  simp only [← List.map_take, List.any_map]
  rfl

theorem find_slot_eraseSessionKeys {S : Setup}
    (sessions : List (KeyIndInitiatorEntry S)) (sIdx : ℕ) :
    (sessions.map eraseSessionKeys).find? (fun s => FgGapDh.initSessionSlotIdx s.sid == sIdx) =
      (sessions.find? (fun s => FgGapDh.initSessionSlotIdx s.sid == sIdx)).map eraseSessionKeys :=
        by
  induction sessions with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.find?_cons]
    have hSid : (eraseSessionKeys s).sid = s.sid := rfl
    rw [hSid]
    cases FgGapDh.initSessionSlotIdx s.sid == sIdx
    · exact ih
    · rfl

@[simp]
theorem badKeyIndFgDh3At_eraseStateKeysAndCache {S : Setup} (P : Primitives)
    (maxLen sIdx bIdx : ℕ) (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgDh3At P maxLen sIdx bIdx (eraseStateKeysAndCache st) advRoLog =
      badKeyIndFgDh3At P maxLen sIdx bIdx st advRoLog := by
  unfold badKeyIndFgDh3At eraseStateKeysAndCache
  dsimp only
  rw [find_slot_eraseSessionKeys]
  cases st.sessions.find? (fun s => FgGapDh.initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s =>
    simp only [Option.map_some]
    cases st.spkBundles.find? (fun (k, _) => FgGapDh.spkBundleFlatIdxVal S k == bIdx) with
    | none => rfl
    | some bp => rcases bp with ⟨_, bEntry⟩; rfl

@[simp]
theorem badKeyIndFgAny_eraseStateKeysAndCache {S : Setup} (P : Primitives)
    (maxLen : ℕ) (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgAny P maxLen (eraseStateKeysAndCache st) advRoLog =
      badKeyIndFgAny P maxLen st advRoLog := by
  unfold badKeyIndFgAny
  simp only [badKeyIndFgDh1At_eraseStateKeysAndCache, badKeyIndFgDh3At_eraseStateKeysAndCache]

@[simp]
theorem badKeyIndFgDh2At_eraseStateKeysAndCache {S : Setup} (P : Primitives)
    (maxLen sIdx kIdx : ℕ) (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgDh2At P maxLen sIdx kIdx (eraseStateKeysAndCache st) advRoLog =
      badKeyIndFgDh2At P maxLen sIdx kIdx st advRoLog := by
  unfold badKeyIndFgDh2At eraseStateKeysAndCache
  dsimp only
  rw [find_slot_eraseSessionKeys]
  cases st.sessions.find? (fun s => FgGapDh.initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s =>
    simp only [Option.map_some]
    cases st.principals.find? (fun (u, _) => u == kIdx) with
    | none => rfl
    | some up => rcases up with ⟨_, kEntry⟩; rfl

@[simp]
theorem badKeyIndFgDh4At_eraseStateKeysAndCache {S : Setup} (P : Primitives)
    (maxLen sIdx oIdx : ℕ) (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgDh4At P maxLen sIdx oIdx (eraseStateKeysAndCache st) advRoLog =
      badKeyIndFgDh4At P maxLen sIdx oIdx st advRoLog := by
  unfold badKeyIndFgDh4At eraseStateKeysAndCache
  dsimp only
  rw [find_slot_eraseSessionKeys]
  cases st.sessions.find? (fun s => FgGapDh.initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s =>
    simp only [Option.map_some]
    cases st.opkEntries.find? (fun (k, _) => opkSlotFlatIdx S k == oIdx) with
    | none => rfl
    | some op => rcases op with ⟨_, oEntry⟩; rfl

@[simp]
theorem badKeyIndFgAny4_eraseStateKeysAndCache {S : Setup} (P : Primitives)
    (maxLen : ℕ) (st : KeyIndState S) (advRoLog : List Bytes) :
    badKeyIndFgAny4 P maxLen (eraseStateKeysAndCache st) advRoLog =
      badKeyIndFgAny4 P maxLen st advRoLog := by
  unfold badKeyIndFgAny4
  simp only [badKeyIndFgAny_eraseStateKeysAndCache, badKeyIndFgDh2At_eraseStateKeysAndCache,
    badKeyIndFgDh4At_eraseStateKeysAndCache]

end Proofs.SignalPqxdh.Security
