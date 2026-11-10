/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.RoKemHop
public import Computational.Proofs.SignalPqxdh.Security.SigHop1Key
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# One-Key `KeyInd` Hop `G2 -> G3` (`KemShCr`) and Combined `G0 -> G3` Bound

**Checked by Lean.** Lifts the semi-honest KEM collision-resistance hop (`G2 → G3`) to the
one-key random-oracle handshake game `pqxdhKeyIndImpl1KeyRo`, and combines it with the one-key
`G0 → G2` bound to obtain `keyInd1Key_hop_G0_G3_le`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ProbabilityTheory ENNReal
open scoped BigOperators
open SignalPqxdh SignalPqxdh.Security
open SignalPqxdh.Security.RoKem

namespace Proofs.SignalPqxdh.Security

/-! ## One-key `KeyIndShCrState` implementations -/

/-- One-key `KeyIndShCrState` oracle implementation delegating `.initPrin` to `pqxdhKeyIndImpl1KeyRo`
    and all other queries to `pqxdhKeyIndShCrImpl`. -/
def pqxdhKeyInd1KeyShCrImpl (checkG2 : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) ProbComp)
  | .initPrin u => liftKeyIndShCrBase (pqxdhKeyIndImpl1KeyRo S P (.initPrin u))
  | q           => pqxdhKeyIndShCrImpl checkG2 S P q

def pqxdhKeyInd1KeyShCrCachedImpl (checkG2 : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) ProbComp)
  | .initPrin u => liftKeyIndShCrBase (pqxdhKeyIndImpl1KeyRo S P (.initPrin u))
  | q           => pqxdhKeyIndShCrCachedImpl checkG2 S P q

theorem pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) :
    ∀ y ∈ support ((pqxdhKeyIndImpl1KeyRo S P (.initPrin u)).run st),
      y.2.spkBundles = st.spkBundles := by
  intro y hy
  unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal at hy
  dsimp only at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  revert hy
  cases st.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    intro hy
    simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; rfl
  | false =>
    intro hy
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨_, _, rfl⟩
    rfl

theorem pqxdhKeyIndImpl1KeyRo_initPrin_commutes_cache (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) :
    CommutesRel (cacheKeyIndAdvKeys S P) st
      (pqxdhKeyIndImpl1KeyRo S P (.initPrin u))
      (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) := by
  unfold CommutesRel pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal
  dsimp only [cacheKeyIndAdvKeys]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases st.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    simp [Prod.map, cacheKeyIndAdvKeys]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, map_bind]
    refine bind_congr (fun secIKA0 => ?_)
    simp [Prod.map, cacheKeyIndAdvKeys]

theorem pqxdhKeyIndImpl1KeyRo_initPrin_validKeyIndEcC (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) (hV : ValidKeyIndEcC S P st) :
    ∀ y ∈ support ((pqxdhKeyIndImpl1KeyRo S P (.initPrin u)).run st),
      ValidKeyIndEcC S P y.2 := by
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hAdv, hR⟩
  intro y hy
  unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal at hy
  dsimp only at hy
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
  revert hy
  cases hFresh : st.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    intro hy
    simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hAdv, hR⟩
  | false =>
    intro hy
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨secIKA0, _, rfl⟩
    exact ⟨⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hVSess⟩, hAdv, hR⟩

theorem pqxdhKeyInd1KeyShCrCachedImpl_false_commutes_cache (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    CommutesRel (cacheShCrAdvKeys S P) hst
      (pqxdhKeyInd1KeyShCrCachedImpl false S P q)
      (pqxdhKeyInd1KeyShCrImpl false S P q) := by
  cases q with
  | initPrin u =>
    exact CommutesRel.liftKeyIndShCrBase_cache S P hst _ _
      (pqxdhKeyIndImpl1KeyRo_initPrin_commutes_cache S P u hst.base)
  | genSPK u j => exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.genSPK u j) hst
  | initiateOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.initiateOPK u i bundle) hst
  | initiateNoOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.initiateNoOPK u i bundle) hst
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.acceptOPK k j o hdr) hst
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.acceptNoOPK k j l hdr) hst
  | corruptIK u => exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.corruptIK u) hst
  | genOPK u j o => exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.genOPK u j o) hst
  | testSession sid =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.testSession sid) hst
  | revealSessionKey sid =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.revealSessionKey sid) hst
  | roQuery secrets =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.roQuery secrets) hst
  | revealDhSecrets =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P .revealDhSecrets hst
  | registerKey sk =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.registerKey sk) hst
  | revealSpkSk u j =>
    exact pqxdhKeyIndShCrCachedImpl_false_commutes_cache S P (.revealSpkSk u j) hst

/-! ## Per-step `KemShCr` reduction obligations -/

noncomputable def tryPauseKeyInd1KeyQuery (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) : Option (PausedShCrKem S (KeyIndState S)) :=
  match gq, cont with
  | .initiateOPK u i bundle, cont =>
    if bundle.opkB?.isNone then none
    else tryPause2 P KeyIndState.principals (pqxdhKeyInd1KeyShCrCachedImpl true S P)
      (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
      (finishKeyIndBase S P (.sendOPK u i) bundle) sIdx cont hst
  | .initiateNoOPK u i bundle, cont =>
    if bundle.opkB?.isSome then none
    else tryPause2 P KeyIndState.principals (pqxdhKeyInd1KeyShCrCachedImpl true S P)
      (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
      (finishKeyIndBase S P (.sendNoOPK u i) bundle) sIdx cont hst
  | _, _ => none

noncomputable def shcrChoosePkKeyInd1KeyAt (S : Setup) (P : Primitives)
    (bIdx sIdx : Nat) (A : KeyIndAdversary S) :
    Bytes → Bytes → ProbComp (Bytes × (Bytes → Bytes → ProbComp Bytes)) :=
  shcrChoosePkGenericAt P ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    (pqxdhKeyInd1KeyShCrCachedImpl true S P) (tryPauseKeyInd1KeyQuery S P) bIdx sIdx A.run

noncomputable def runKeyInd1KeyShCrSim (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ProbComp (Bool × Bool × KeyIndShCrState S) := do
  let secb ← $ᵗ Bool
  let initSt : KeyIndShCrState S := { base := KeyIndState.empty S secb }
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrImpl false S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

noncomputable def badKemShCrProbKeyInd1KeyAt (S : Setup) (P : Primitives)
    (idx : Nat) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeyShCrSim S P A >>= fun (_, _, finalHst) =>
    pure (hasBadKemShCrRecordsAt S P idx finalHst.initKemRecs finalHst.recvKemRecs)] {true}).toReal

theorem pqxdhKeyInd1KeyShCrCachedImpl_clearFalse (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst),
      clearShCrTarget x.2 = x.2 := by
  cases q with
  | initPrin u =>
    exact liftShCrBase_clearFalse (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) hst hClear
  | genSPK u j => exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.genSPK u j) hst hClear
  | initiateOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.initiateOPK u i bundle) hst hClear
  | initiateNoOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.initiateNoOPK u i bundle) hst hClear
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.acceptOPK k j o hdr) hst hClear
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.acceptNoOPK k j l hdr) hst hClear
  | corruptIK u => exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.corruptIK u) hst hClear
  | genOPK u j o => exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.genOPK u j o) hst hClear
  | testSession sid => exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.testSession sid) hst hClear
  | roQuery secrets => exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.roQuery secrets) hst hClear
  | revealDhSecrets => exact pqxdhKeyIndShCrCachedImpl_clearFalse S P .revealDhSecrets hst hClear
  | revealSessionKey sid =>
    exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.revealSessionKey sid) hst hClear
  | registerKey sk => exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.registerKey sk) hst hClear
  | revealSpkSk u j => exact pqxdhKeyIndShCrCachedImpl_clearFalse S P (.revealSpkSk u j) hst hClear

theorem pqxdhKeyInd1KeyShCrCachedImpl_afterGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst)
    (hGen : hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk, (pqxdhKeyInd1KeyShCrCachedImpl true S P q).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst) ∧
    (∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst),
      hasGeneratedTargetBundle S bIdx x.2.base.spkBundles) := by
  cases q with
  | initPrin u =>
    exact liftShCrBase_afterGen KeyIndState.spkBundles
      (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) bIdx hst
      (pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles S P u hst.base) hGen
  | genSPK u j =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.genSPK u j) hst hClear hGen
  | initiateOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.initiateOPK u i bundle) hst hClear hGen
  | initiateNoOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.initiateNoOPK u i bundle) hst hClear hGen
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.acceptOPK k j o hdr) hst hClear hGen
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.acceptNoOPK k j l hdr) hst hClear hGen
  | corruptIK u =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.corruptIK u) hst hClear hGen
  | genOPK u j o =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.genOPK u j o) hst hClear hGen
  | testSession sid =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.testSession sid) hst hClear hGen
  | roQuery secrets =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.roQuery secrets) hst hClear hGen
  | revealDhSecrets =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx .revealDhSecrets hst hClear hGen
  | revealSessionKey sid =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.revealSessionKey sid) hst hClear hGen
  | registerKey sk =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.registerKey sk) hst hClear hGen
  | revealSpkSk u j =>
    exact pqxdhKeyIndShCrCachedImpl_afterGen S P bIdx (.revealSpkSk u j) hst hClear hGen

theorem pqxdhKeyInd1KeyShCrCachedImpl_beforeGen (S : Setup) (P : Primitives) (bIdx : Nat)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hClear : clearShCrTarget hst = hst)
    (hNotGen : ¬ hasGeneratedTargetBundle S bIdx hst.base.spkBundles) :
    (∀ pk sk, (pqxdhKeyInd1KeyShCrCachedImpl true S P q).run (setShCrTarget hst bIdx pk sk) =
      Prod.map id (fun s' => setShCrTarget s' bIdx pk sk) <$>
        (pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst) ∨
    ((∀ obs : (keyIndSpec S).Range q × KeyIndShCrState S → ProbComp Bool,
      𝒟[sampleKemKeyGen P >>= fun pair =>
        (pqxdhKeyInd1KeyShCrCachedImpl true S P q).run (setShCrTarget hst bIdx pair.1 pair.2) >>=
          fun x => obs (x.1, clearShCrTarget x.2)] =
      𝒟[(pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst >>= obs]) ∧
     (∀ pk sk,
       ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl true S P q).run (setShCrTarget hst bIdx pk sk)),
      x.2 = setShCrTarget (clearShCrTarget x.2) bIdx pk sk ∧
      hasGeneratedTargetBundle S bIdx (clearShCrTarget x.2).base.spkBundles)) := by
  cases q with
  | initPrin u =>
    left
    exact liftShCrBase_setShCrTarget (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) hst bIdx
  | genSPK u j =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.genSPK u j) hst hClear hNotGen
  | initiateOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.initiateOPK u i bundle) hst hClear hNotGen
  | initiateNoOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.initiateNoOPK u i bundle) hst hClear hNotGen
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.acceptOPK k j o hdr) hst hClear hNotGen
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.acceptNoOPK k j l hdr) hst hClear hNotGen
  | corruptIK u =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.corruptIK u) hst hClear hNotGen
  | genOPK u j o =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.genOPK u j o) hst hClear hNotGen
  | testSession sid =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.testSession sid) hst hClear hNotGen
  | roQuery secrets =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.roQuery secrets) hst hClear hNotGen
  | revealDhSecrets =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx .revealDhSecrets hst hClear hNotGen
  | revealSessionKey sid =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.revealSessionKey sid) hst hClear hNotGen
  | registerKey sk =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.registerKey sk) hst hClear hNotGen
  | revealSpkSk u j =>
    exact pqxdhKeyIndShCrCachedImpl_beforeGen S P bIdx (.revealSpkSk u j) hst hClear hNotGen

theorem pqxdhKeyInd1KeyShCrCachedImpl_validStep (S : Setup) (P : Primitives)
    (bIdx : Nat) (pk sk : Bytes) (q : KeyIndQuery S) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecv KeyIndState.spkBundles bIdx pk sk hst) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl true S P q).run hst),
      ValidTargetRecv KeyIndState.spkBundles bIdx pk sk x.2 := by
  cases q with
  | initPrin u =>
    exact liftShCrBase_validStep KeyIndState.spkBundles
      (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) bIdx pk sk hst
      (pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles S P u hst.base) hV
  | genSPK u j => exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.genSPK u j) hst hV
  | initiateOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.initiateOPK u i bundle) hst hV
  | initiateNoOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.initiateNoOPK u i bundle) hst hV
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.acceptOPK k j o hdr) hst hV
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.acceptNoOPK k j l hdr) hst hV
  | corruptIK u => exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.corruptIK u) hst hV
  | genOPK u j o => exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.genOPK u j o) hst hV
  | testSession sid =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.testSession sid) hst hV
  | roQuery secrets =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.roQuery secrets) hst hV
  | revealDhSecrets =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk .revealDhSecrets hst hV
  | revealSessionKey sid =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.revealSessionKey sid) hst hV
  | registerKey skAdv =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.registerKey skAdv) hst hV
  | revealSpkSk u j =>
    exact pqxdhKeyIndShCrCachedImpl_validStep S P bIdx pk sk (.revealSpkSk u j) hst hV

theorem pqxdhKeyInd1KeyShCrCachedImpl_sendStep (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl true S P q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  cases q with
  | initPrin u => exact liftShCrBase_sendStep (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) hst
  | genSPK u j => exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.genSPK u j) hst
  | initiateOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.initiateOPK u i bundle) hst
  | initiateNoOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.initiateNoOPK u i bundle) hst
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.acceptOPK k j o hdr) hst
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.acceptNoOPK k j l hdr) hst
  | corruptIK u => exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.corruptIK u) hst
  | genOPK u j o => exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.genOPK u j o) hst
  | testSession sid => exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.testSession sid) hst
  | roQuery secrets => exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.roQuery secrets) hst
  | revealDhSecrets => exact pqxdhKeyIndShCrCachedImpl_sendStep S P .revealDhSecrets hst
  | revealSessionKey sid => exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.revealSessionKey sid) hst
  | registerKey sk => exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.registerKey sk) hst
  | revealSpkSk u j => exact pqxdhKeyIndShCrCachedImpl_sendStep S P (.revealSpkSk u j) hst

theorem pqxdhKeyInd1KeyShCrCachedImpl_pauseNone (S : Setup) (P : Primitives) (sIdx : Nat)
    (gq : KeyIndQuery S) (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (hLe : hst.sendCount ≤ sIdx)
    (hNone : tryPauseKeyInd1KeyQuery S P sIdx gq cont hst = none) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl true S P gq).run hst),
      x.2.sendCount ≤ sIdx := by
  cases gq with
  | initPrin u =>
    exact liftShCrBase_pauseNone (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) sIdx hst hLe
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyInd1KeyQuery] at hNone
    dsimp only [pqxdhKeyInd1KeyShCrCachedImpl, pqxdhKeyIndShCrCachedImpl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate2_pauseNone P KeyIndState.principals
        (pqxdhKeyInd1KeyShCrCachedImpl true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyInd1KeyQuery] at hNone
    dsimp only [pqxdhKeyInd1KeyShCrCachedImpl, pqxdhKeyIndShCrCachedImpl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hNone
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate2_pauseNone P KeyIndState.principals
        (pqxdhKeyInd1KeyShCrCachedImpl true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  | genSPK u j =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.genSPK u j) cont hst hLe rfl
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.acceptOPK k j o hdr) cont hst hLe rfl
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.acceptNoOPK k j l hdr) cont hst hLe rfl
  | corruptIK u =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.corruptIK u) cont hst hLe rfl
  | genOPK u j o =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.genOPK u j o) cont hst hLe rfl
  | testSession sid =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.testSession sid) cont hst hLe rfl
  | roQuery secrets =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.roQuery secrets) cont hst hLe rfl
  | revealDhSecrets =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx .revealDhSecrets cont hst hLe rfl
  | revealSessionKey sid =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.revealSessionKey sid) cont hst hLe rfl
  | registerKey sk =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.registerKey sk) cont hst hLe rfl
  | revealSpkSk u j =>
    exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx (.revealSpkSk u j) cont hst hLe rfl

theorem pqxdhKeyInd1KeyShCrCachedImpl_pauseSome (S : Setup) (P : Primitives)
    (bIdx sIdx : Nat) (pk sk : Bytes)
    (gq : KeyIndQuery S) (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (paused : PausedShCrKem S (KeyIndState S))
    (hV : ValidTargetRecv KeyIndState.spkBundles bIdx pk sk hst)
    (hSome : tryPauseKeyInd1KeyQuery S P sIdx gq cont hst = some paused) :
    ∃ (noneOut : (keyIndSpec S).Range gq)
      (postKem : Bytes → Bytes → ProbComp ((keyIndSpec S).Range gq × KeyIndShCrState S)),
      (∀ ss ct, paused.resume ss ct =
        (postKem ss ct >>= fun y =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (KeyIndShCrState S) ProbComp) +
              pqxdhKeyInd1KeyShCrCachedImpl true S P) (cont y.1)).run y.2)) ∧
      (∀ obs : (keyIndSpec S).Range gq × KeyIndShCrState S → ProbComp Bool,
        𝒟[(pqxdhKeyInd1KeyShCrCachedImpl true S P gq).run hst >>= obs] =
        𝒟[sampleCoins32 >>= fun r =>
          match P.kemEncaps paused.bundle.pqspkB r with
          | none => obs (noneOut, { hst with sendCount := sIdx + 1 })
          | some (ss, ct) => postKem ss ct >>= obs]) ∧
      (∀ ss ct, ∀ y ∈ support (postKem ss ct),
        ValidTargetRecv KeyIndState.spkBundles bIdx pk sk y.2 ∧
        sIdx < y.2.sendCount ∧
        (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
          (i.sendIdx = sIdx ∧
           i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))) := by
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyInd1KeyQuery] at hSome
    rw [show pqxdhKeyInd1KeyShCrCachedImpl true S P (.initiateOPK u i bundle) =
      (if bundle.opkB?.isNone then pure .noneResp
       else runKeyIndShCrInitiate true S P (.sendOPK u i) u bundle) from rfl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate2_pauseSome P KeyIndState.principals KeyIndState.spkBundles
        (pqxdhKeyInd1KeyShCrCachedImpl true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle)
        bIdx sIdx pk sk cont hst paused
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendOPK u i) bundle uInfo ekASk ss kemCt hst.base out hout)
        hV hSome
    · rw [hopk] at hSome; simp at hSome
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyInd1KeyQuery] at hSome
    rw [show pqxdhKeyInd1KeyShCrCachedImpl true S P (.initiateNoOPK u i bundle) =
      (if bundle.opkB?.isSome then pure .noneResp
       else runKeyIndShCrInitiate true S P (.sendNoOPK u i) u bundle) from rfl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate2_pauseSome P KeyIndState.principals KeyIndState.spkBundles
        (pqxdhKeyInd1KeyShCrCachedImpl true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle)
        bIdx sIdx pk sk cont hst paused
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendNoOPK u i) bundle uInfo ekASk ss kemCt hst.base out hout)
        hV hSome
    · rw [hopk] at hSome; simp at hSome
  | genSPK u j => cases hSome
  | acceptOPK k j o hdr => cases hSome
  | acceptNoOPK k j l hdr => cases hSome
  | initPrin u => cases hSome
  | corruptIK u => cases hSome
  | genOPK u j o => cases hSome
  | testSession sid => cases hSome
  | roQuery secrets => cases hSome
  | revealDhSecrets => cases hSome
  | revealSessionKey sid => cases hSome
  | registerKey sk => cases hSome
  | revealSpkSk u j => cases hSome

theorem badKemShCrProbKeyInd1KeyAt_le_kemShCrProb (S : Setup) (P : Primitives)
    (idx : Nat) (A : KeyIndAdversary S) :
    badKemShCrProbKeyInd1KeyAt S P idx A ≤
      (𝒟[kemShCrExpProb P
          (shcrChoosePkKeyInd1KeyAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A)]
        {true}).toReal := by
  unfold badKemShCrProbKeyInd1KeyAt shcrChoosePkKeyInd1KeyAt
  have hEq :
      (runKeyInd1KeyShCrSim S P A >>= fun (_, _, finalHst) =>
        pure (hasBadKemShCrRecordsAt S P idx finalHst.initKemRecs finalHst.recvKemRecs)) =
      (($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndShCrState S) ProbComp) +
            pqxdhKeyInd1KeyShCrCachedImpl false S P) A.run).run { base := b0 } >>= fun x =>
        pure (hasBadKemShCrRecordsAt S P idx x.2.initKemRecs x.2.recvKemRecs)) := by
    unfold runKeyInd1KeyShCrSim
    simp only [bind_assoc, pure_bind]
    refine bind_congr (fun secb => ?_)
    have hSim := CommutesRel.simulateQ_add_unif (cacheShCrAdvKeys S P)
      (pqxdhKeyInd1KeyShCrCachedImpl false S P) (pqxdhKeyInd1KeyShCrImpl false S P)
      (pqxdhKeyInd1KeyShCrCachedImpl_false_commutes_cache S P)
      A.run { base := KeyIndState.empty S secb }
    unfold CommutesRel at hSim
    have hInit : cacheShCrAdvKeys S P { base := KeyIndState.empty S secb } =
        { base := KeyIndState.empty S secb } := rfl
    rw [hInit] at hSim
    rw [hSim, bind_map_left]
    rfl
  rw [hEq]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  exact badKemShCrProbGenericAt_le_kemShCr P
    ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    KeyIndState.spkBundles
    (pqxdhKeyInd1KeyShCrCachedImpl false S P)
    (pqxdhKeyInd1KeyShCrCachedImpl true S P)
    (tryPauseKeyInd1KeyQuery S P)
    idx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨secb, _, rfl⟩
      rfl)
    (pqxdhKeyInd1KeyShCrCachedImpl_clearFalse S P)
    (pqxdhKeyInd1KeyShCrCachedImpl_afterGen S P (idx / S.N_send_tot))
    (pqxdhKeyInd1KeyShCrCachedImpl_beforeGen S P (idx / S.N_send_tot))
    (pqxdhKeyInd1KeyShCrCachedImpl_validStep S P (idx / S.N_send_tot))
    (pqxdhKeyInd1KeyShCrCachedImpl_sendStep S P)
    (pqxdhKeyInd1KeyShCrCachedImpl_pauseNone S P (idx % S.N_send_tot))
    (pqxdhKeyInd1KeyShCrCachedImpl_pauseSome S P (idx / S.N_send_tot) (idx % S.N_send_tot))
    A.run

/-! ## Base-state projection and `G2_5` / `G3` hybrids -/

theorem map_base_pqxdhKeyInd1KeyShCrImpl_false (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    (Prod.map id ShCrState.base <$>
      (pqxdhKeyInd1KeyShCrImpl false S P q).run hst) =
      (pqxdhKeyIndImpl1KeyRo S P q).run hst.base := by
  cases q with
  | initPrin u =>
    exact map_base_liftShCrBase (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) hst
  | genSPK u j => exact map_base_pqxdhKeyIndShCrImpl_false S P (.genSPK u j) hst
  | initiateOPK u i bundle =>
    exact map_base_pqxdhKeyIndShCrImpl_false S P (.initiateOPK u i bundle) hst
  | initiateNoOPK u i bundle =>
    exact map_base_pqxdhKeyIndShCrImpl_false S P (.initiateNoOPK u i bundle) hst
  | acceptOPK k j o hdr =>
    exact map_base_pqxdhKeyIndShCrImpl_false S P (.acceptOPK k j o hdr) hst
  | acceptNoOPK k j l hdr =>
    exact map_base_pqxdhKeyIndShCrImpl_false S P (.acceptNoOPK k j l hdr) hst
  | corruptIK u => exact map_base_pqxdhKeyIndShCrImpl_false S P (.corruptIK u) hst
  | genOPK u j o => exact map_base_pqxdhKeyIndShCrImpl_false S P (.genOPK u j o) hst
  | testSession sid => exact map_base_pqxdhKeyIndShCrImpl_false S P (.testSession sid) hst
  | roQuery bytes => exact map_base_pqxdhKeyIndShCrImpl_false S P (.roQuery bytes) hst
  | revealDhSecrets => exact map_base_pqxdhKeyIndShCrImpl_false S P .revealDhSecrets hst
  | revealSessionKey sid =>
    exact map_base_pqxdhKeyIndShCrImpl_false S P (.revealSessionKey sid) hst
  | registerKey sk => exact map_base_pqxdhKeyIndShCrImpl_false S P (.registerKey sk) hst
  | revealSpkSk u j => exact map_base_pqxdhKeyIndShCrImpl_false S P (.revealSpkSk u j) hst

theorem map_base_fullKeyInd1KeyShCrImpl_false (S : Setup) (P : Primitives)
    (q : (unifSpec + keyIndSpec S).Domain) (hst : KeyIndShCrState S) :
    (Prod.map id ShCrState.base <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrImpl false S P) q).run hst) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P) q).run hst.base := by
  cases q with
  | inl uq =>
    simp [QueryImpl.liftTarget, StateT.run_monadLift]
  | inr kq =>
    exact map_base_pqxdhKeyInd1KeyShCrImpl_false S P kq hst

noncomputable def badKemShCrProbKeyInd1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeyShCrSim S P A >>= fun (_, _, finalHst) =>
    pure (hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)] {true}).toReal

noncomputable abbrev keyInd1KeyExpG2_5 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  _root_.SignalPqxdh.Security.keyInd1KeyExpG2_1 S P A

noncomputable abbrev keyInd1KeyAdvG2_5 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  _root_.SignalPqxdh.Security.keyInd1KeyAdvG2_1 S P A

noncomputable def keyInd1KeyExpG2_5ShCr (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalHst) ← runKeyInd1KeyShCrSim S P A
  let finalSt := finalHst.base
  if ((!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
      hasBadSigKeyInd finalSt) ||
     hasKemPkCollisionKeyInd finalSt then
    $ᵗ Bool
  else
    return (b' == secb)

noncomputable def keyInd1KeyAdvG2_5ShCr (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyInd1KeyExpG2_5ShCr S P A].boolBias).toReal

/-- One-key `G3` hybrid game adding `hasBadKemShCrRecords` to the `G2_5` abort condition. -/
noncomputable def keyInd1KeyExpG3 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let (secb, b', finalHst) ← runKeyInd1KeyShCrSim S P A
  let finalSt := finalHst.base
  if (((!keyInd1KeyAllTestedClean P finalSt || hasEcPkCollisionKeyInd P finalSt) ||
       hasBadSigKeyInd finalSt) ||
      hasKemPkCollisionKeyInd finalSt) ||
     hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs then
    $ᵗ Bool
  else
    return (b' == secb)

noncomputable def keyInd1KeyAdvG3 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyInd1KeyExpG3 S P A].boolBias).toReal

theorem keyInd1Key_hop_badKemShCr_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyInd1KeyAdvG2_5ShCr S P A - keyInd1KeyAdvG3 S P A| ≤ badKemShCrProbKeyInd1Key S P A := by
  unfold keyInd1KeyAdvG2_5ShCr keyInd1KeyAdvG3 keyInd1KeyExpG2_5ShCr keyInd1KeyExpG3
    badKemShCrProbKeyInd1Key
  exact abs_sub_boolBias_abort_or_le (runKeyInd1KeyShCrSim S P A)
    (fun (_, _, finalHst) =>
      ((!keyInd1KeyAllTestedClean P finalHst.base || hasEcPkCollisionKeyInd P finalHst.base) ||
       hasBadSigKeyInd finalHst.base) ||
      hasKemPkCollisionKeyInd finalHst.base)
    (fun (_, _, finalHst) => hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)
    (fun (secb, b', _) => pure (b' == secb))

theorem badKemShCrProbKeyInd1Key_le_sum (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    badKemShCrProbKeyInd1Key S P A ≤
      ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        badKemShCrProbKeyInd1KeyAt S P idx A := by
  unfold badKemShCrProbKeyInd1Key badKemShCrProbKeyInd1KeyAt hasBadKemShCrRecords
  exact toReal_any_range_le_sum (runKeyInd1KeyShCrSim S P A) (S.N_spk_tot * S.N_send_tot)
    (fun idx (_, _, finalHst) =>
      hasBadKemShCrRecordsAt S P idx finalHst.initKemRecs finalHst.recvKemRecs)

theorem keyInd1KeyExpG2_5ShCr_eq (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyInd1KeyExpG2_5ShCr S P A = keyInd1KeyExpG2_5 S P A := by
  unfold keyInd1KeyExpG2_5ShCr keyInd1KeyExpG2_5 _root_.SignalPqxdh.Security.keyInd1KeyExpG2_1
    runKeyInd1KeyShCrSim runKeyInd1KeySim
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro secb
  have hsim := map_proj_simulateQ ShCrState.base
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrImpl false S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P)
    (map_base_fullKeyInd1KeyShCrImpl_false S P)
    A.run { base := KeyIndState.empty S secb }
  rw [← hsim, bind_map_left]
  rfl

theorem keyInd1KeyAdvG2_5_eq_ShCr (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyInd1KeyAdvG2_5 S P A = keyInd1KeyAdvG2_5ShCr S P A := by
  unfold keyInd1KeyAdvG2_5 _root_.SignalPqxdh.Security.keyInd1KeyAdvG2_1 keyInd1KeyAdvG2_5ShCr
  rw [keyInd1KeyExpG2_5ShCr_eq]

/-! ## Black-box `KemShCr` equivalence and hop bounds -/

theorem pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs (embedTarget : Bool)
    (S : Setup) (P : Primitives)
    (gq : KeyIndQuery S) (hst : KeyIndShCrState S) (hV : ValidKeyIndEcC S P hst.base) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl embedTarget S P gq).run hst),
      ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
  cases gq with
  | initPrin u =>
    intro x hx
    dsimp only [pqxdhKeyInd1KeyShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨pqxdhKeyIndImpl1KeyRo_initPrin_validKeyIndEcC S P u hst.base hV z hz, by simp⟩
  | genSPK u j =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P (.genSPK u j) hst hV
  | initiateOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.initiateOPK u i bundle) hst hV
  | initiateNoOPK u i bundle =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.initiateNoOPK u i bundle) hst hV
  | acceptOPK k j o hdr =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.acceptOPK k j o hdr) hst hV
  | acceptNoOPK k j l hdr =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.acceptNoOPK k j l hdr) hst hV
  | corruptIK u =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.corruptIK u) hst hV
  | genOPK u j o =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.genOPK u j o) hst hV
  | testSession sid =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.testSession sid) hst hV
  | revealSessionKey sid =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.revealSessionKey sid) hst hV
  | roQuery secrets =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.roQuery secrets) hst hV
  | revealDhSecrets =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      .revealDhSecrets hst hV
  | registerKey sk =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.registerKey sk) hst hV
  | revealSpkSk u j =>
    exact pqxdhKeyIndShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P
      (.revealSpkSk u j) hst hV

theorem simulateQ_pqxdhKeyIndImpl1KeyRoPrim_initPrin (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) :
    simulateQ (primBaseImpl P) ((pqxdhKeyIndImpl1KeyRoPrim S (.initPrin u)).run st) =
      (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)).run st := by
  unfold pqxdhKeyIndImpl1KeyRoPrim pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases st.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    simp [StateT.run_pure]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      simulateQ_bind, simulateQ_embedUnif, simulateQ_pure]
    refine bind_congr (fun secIKA0 => ?_)
    rw [simulateQ_primQ_x25519Base, pure_bind]

theorem simulateQ_pqxdhKeyIndShCrPrimImpl1Key (embedTarget : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (gq : KeyIndQuery S) (hst : KeyIndShCrState S)
    (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) ((pqxdhKeyIndShCrPrimImpl1Key embedTarget S gq).run hst) =
      (pqxdhKeyInd1KeyShCrCachedImpl embedTarget S P gq).run hst := by
  cases gq with
  | initPrin u =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImpl1KeyRoPrim_initPrin S P u hst.base)
  | genSPK u j => exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.genSPK u j) hst hV
  | initiateOPK u i bundle =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.initiateOPK u i bundle) hst hV
  | initiateNoOPK u i bundle =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.initiateNoOPK u i bundle) hst hV
  | acceptOPK k j o hdr =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.acceptOPK k j o hdr) hst hV
  | acceptNoOPK k j l hdr =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.acceptNoOPK k j l hdr) hst hV
  | corruptIK u => exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.corruptIK u) hst hV
  | genOPK u j o =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.genOPK u j o) hst hV
  | testSession sid =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.testSession sid) hst hV
  | revealSessionKey sid =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.revealSessionKey sid) hst hV
  | roQuery secrets =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.roQuery secrets) hst hV
  | revealDhSecrets =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP .revealDhSecrets hst hV
  | registerKey sk =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.registerKey sk) hst hV
  | revealSpkSk u j =>
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP (.revealSpkSk u j) hst hV

noncomputable def PausedShCrData.toPaused1Key {S : Setup} (P : Primitives)
    (d : PausedShCrData S) : PausedShCrKem S (KeyIndState S) where
  bundle := d.bundle
  resume := fun ss kemCt =>
    postKem2 d.sid d.bundle d.uEntry (finishKeyIndBase S P d.sid d.bundle) d.hst ss kemCt >>=
      fun y =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndShCrState S) ProbComp) +
            pqxdhKeyInd1KeyShCrCachedImpl true S P) (d.cont y.1)).run y.2

@[simp] theorem PausedShCrData.toPaused1Key_bundle {S : Setup} (P : Primitives)
    (d : PausedShCrData S) : (PausedShCrData.toPaused1Key P d).bundle = d.bundle := rfl

theorem map_toPaused1Key_tryPauseKeyIndQueryData (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) :
    (tryPauseKeyIndQueryData S P sIdx gq cont hst).map (PausedShCrData.toPaused1Key P) =
      tryPauseKeyInd1KeyQuery S P sIdx gq cont hst := by
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryData, tryPauseKeyInd1KeyQuery, tryPause2]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckKeyInd S P (.sendOPK u i) u bundle hst.base with
      | none => rfl
      | some uEntry =>
        dsimp only
        split_ifs <;> rfl
    · rfl
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryData, tryPauseKeyInd1KeyQuery, tryPause2]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckKeyInd S P (.sendNoOPK u i) u bundle hst.base with
      | none => rfl
      | some uEntry =>
        dsimp only
        split_ifs <;> rfl
    · rfl
  | _ => rfl

theorem simulateQ_runWithFuelKeyInd1KeyShCrPrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ)
    (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    simulateQ (primBaseImpl P) (runWithFuelKeyInd1KeyShCrPrim S oa hst fuel) =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrCachedImpl true S P) oa).run hst := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b =>
    simp [runWithFuelKeyInd1KeyShCrPrim]
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      simp only [runWithFuelKeyInd1KeyShCrPrim, OracleComp.construct_query_bind,
        simulateQ_bind, simulateQ_embedUnif, StateT.run_bind,
        QueryImpl.simulateQ_add_query_left, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self,
        bind_assoc, pure_bind]
      exact bind_congr (fun u => ih u hst fuel hV (h_cont u))
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          simp only [runWithFuelKeyInd1KeyShCrPrim, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_pqxdhKeyIndShCrPrimImpl1Key true S P hP gq hst hV,
            StateT.run_bind, QueryImpl.simulateQ_add_query_right]
          refine bind_congr_of_support ((pqxdhKeyInd1KeyShCrCachedImpl true S P gq).run hst) _ _
            (fun x hx => ?_)
          have hVx :=
            (pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs true S P gq hst hV x hx).1
          exact ih x.1 x.2 f hVx (h_cont x.1)

theorem simulateQ_pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs
    (embedTarget : Bool) (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ)
    (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrCachedImpl embedTarget S P
    ∀ x ∈ support ((simulateQ fullImpl oa).run hst),
      ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel := by
  intro fullImpl
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hV, Nat.le_add_right _ _⟩
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      dsimp only [fullImpl]
      intro x hx
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx⟩
      exact ih u hst fuel hV (h_cont u) x hx
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          dsimp only [fullImpl]
          intro x hx
          rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨y, hy, hx⟩
          have ⟨hVy, hRecy⟩ :=
            pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P gq hst hV y hy
          have ⟨hVx, hRecx⟩ := ih y.1 y.2 f hVy (h_cont y.1) x hx
          exact ⟨hVx, by omega⟩

theorem simulateQ_stepUntilShCrFuelKeyInd1KeyPrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx : ℕ)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : ℕ)
    (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    (Sum.map id (PausedShCrData.toPaused1Key P) <$>
      simulateQ (primBaseImpl P) (stepUntilShCrFuelKeyInd1KeyPrim S sIdx oa hst fuel) =
      stepUntilShCr (pqxdhKeyInd1KeyShCrCachedImpl true S P) (tryPauseKeyInd1KeyQuery S P sIdx) oa hst) ∧
    (∀ res ∈ support (simulateQ (primBaseImpl P) (stepUntilShCrFuelKeyInd1KeyPrim S sIdx oa hst fuel)),
      match res with
      | Sum.inl done => done.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel
      | Sum.inr d    => ValidPausedShCrData S P (hst.recvKemRecs.length + fuel) d) := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b' =>
    refine ⟨?_, ?_⟩
    · simp [stepUntilShCrFuelKeyInd1KeyPrim, stepUntilShCr]
    · intro res hres
      simp only [stepUntilShCrFuelKeyInd1KeyPrim, OracleComp.construct_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hres
      subst hres
      exact Nat.le_add_right _ _
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      refine ⟨?_, ?_⟩
      · rw [stepUntilShCr_query_inl]
        simp only [stepUntilShCrFuelKeyInd1KeyPrim, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, map_bind]
        exact bind_congr (fun u => (ih u hst fuel hV (h_cont u)).1)
      · intro res hres
        simp only [stepUntilShCrFuelKeyInd1KeyPrim, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, MonadAttach.mem_support_bind] at hres
        rcases hres with ⟨u, _, hres⟩
        exact (ih u hst fuel hV (h_cont u)).2 res hres
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exfalso; exact h_abs rfl
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          have h_try := simulateQ_tryPauseKeyIndQueryPrim S P sIdx gq oa hst hV
          have h_map := map_toPaused1Key_tryPauseKeyIndQueryData S P sIdx gq oa hst
          refine ⟨?_, ?_⟩
          · rw [stepUntilShCr_query_inr]
            simp only [stepUntilShCrFuelKeyInd1KeyPrim, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind, ← h_map]
            cases h_d : tryPauseKeyIndQueryData S P sIdx gq oa hst with
            | some d =>
              simp [simulateQ_pure]
            | none =>
              simp only [Option.map_none, simulateQ_bind,
                simulateQ_pqxdhKeyIndShCrPrimImpl1Key true S P hP gq hst hV, map_bind]
              refine bind_congr_of_support ((pqxdhKeyInd1KeyShCrCachedImpl true S P gq).run hst) _ _
                (fun x hx => ?_)
              have hVx :=
                (pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs true S P gq hst hV x hx).1
              exact (ih x.1 x.2 f hVx (h_cont x.1)).1
          · intro res hres
            simp only [stepUntilShCrFuelKeyInd1KeyPrim, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind] at hres
            cases h_d : tryPauseKeyIndQueryData S P sIdx gq oa hst with
            | some d =>
              rw [h_d] at hres
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hres
              subst hres
              rcases tryPauseKeyIndQueryData_some_props S P sIdx gq oa hst d h_d with
                ⟨h_hst, h_sid, h_fresh, h_cb⟩
              refine ⟨h_hst ▸ hV, h_sid, h_fresh, f, ?_, h_cb f h_cont⟩
              rw [h_hst]; omega
            | none =>
              rw [h_d] at hres
              simp only [simulateQ_bind, simulateQ_pqxdhKeyIndShCrPrimImpl1Key true S P hP gq hst hV,
                MonadAttach.mem_support_bind] at hres
              rcases hres with ⟨x, hx, hres⟩
              have ⟨hVx, hRecx⟩ :=
                pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs true S P gq hst hV x hx
              have h_ih := (ih x.1 x.2 f hVx (h_cont x.1)).2 res hres
              cases res with
              | inl done => omega
              | inr d =>
                rcases h_ih with ⟨hVd, hSid, hFresh, f', hf', hCont⟩
                exact ⟨hVd, hSid, hFresh, f', by omega, hCont⟩

theorem simulateQ_resumePausedKeyInd1KeyPrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (N : ℕ) (d : PausedShCrData S) (ss kemCt : Bytes)
    (hValid : ValidPausedShCrData S P N d) :
    simulateQ (primBaseImpl P) (resumePausedKeyInd1KeyPrim S N d ss kemCt) =
      (PausedShCrData.toPaused1Key P d).resume ss kemCt ∧
    (∀ z ∈ support ((PausedShCrData.toPaused1Key P d).resume ss kemCt),
      z.2.recvKemRecs.length ≤ N) := by
  rcases hValid with ⟨hVd, hSid, hFresh, f, hf_le, hCont⟩
  have hf_N : f ≤ N := by omega
  have hEq : simulateQ (primBaseImpl P) (resumePausedKeyInd1KeyPrim S N d ss kemCt) =
      (PausedShCrData.toPaused1Key P d).resume ss kemCt := by
    unfold resumePausedKeyInd1KeyPrim PausedShCrData.toPaused1Key
    dsimp only
    rw [simulateQ_bind, simulateQ_postKemKeyIndPrim S P d.sid d.bundle d.uEntry d.hst ss kemCt hVd]
    refine bind_congr_of_support
      (postKem2 d.sid d.bundle d.uEntry (finishKeyIndBase S P d.sid d.bundle) d.hst ss kemCt) _ _
      (fun y hy => ?_)
    have hVy :=
      (postKem2_validKeyIndEc_and_recvKemRecs S P d.sid hSid d.bundle d.uEntry d.hst ss kemCt hVd
        hFresh y hy).1
    exact simulateQ_runWithFuelKeyInd1KeyShCrPrim S P hP (d.cont y.1) y.2 N hVy
      ((hCont y.1).mono hf_N)
  refine ⟨hEq, fun z hz => ?_⟩
  unfold PausedShCrData.toPaused1Key at hz
  dsimp only at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨y, hy, hz⟩
  have ⟨hVy, hRecy⟩ :=
    postKem2_validKeyIndEc_and_recvKemRecs S P d.sid hSid d.bundle d.uEntry d.hst ss kemCt hVd
      hFresh y hy
  have ⟨_, hRecz⟩ :=
    simulateQ_pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs true S P (d.cont y.1) y.2 f
      hVy (hCont y.1) z hz
  rw [hRecy] at hRecz
  omega

def shcrReductionKeyInd1KeyAt (S : Setup) (b : QueryBudget) (idx : ℕ)
    (A : KeyIndAdversary S) : KemShCrAdv where
  State := ShCrFinishState S
  choosePk := choosePkKeyInd1KeyPrimAt S b (idx / S.N_send_tot) (idx % S.N_send_tot) A
  findCollision := findCollisionKeyInd1KeyPrim S b
  q_prim := primQueryBudget S b

theorem kemShCrExp_shcrReductionKeyInd1KeyAt_eq (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (idx : ℕ) (A : KeyIndAdversary S) (hA : QueryBounded A b) :
    kemShCrExp P (shcrReductionKeyInd1KeyAt S b idx A) =
      kemShCrExpProb P
        (shcrChoosePkKeyInd1KeyAt S P (idx / S.N_send_tot) (idx % S.N_send_tot) A) := by
  unfold kemShCrExp shcrReductionKeyInd1KeyAt kemShCrExpProb shcrChoosePkKeyInd1KeyAt
    shcrChoosePkGenericAt choosePkKeyInd1KeyPrimAt findCollisionKeyInd1KeyPrim
  dsimp only
  congr 1; ext ⟨pk, sk⟩
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_embedUnif, bind_assoc, pure_bind]
  refine bind_congr (fun secb => ?_)
  let initSt : KeyIndShCrState S := {
    base        := KeyIndState.empty S secb
    targetBIdx? := some (idx / S.N_send_tot)
    targetPk    := pk
    targetSk    := sk
  }
  have hV0 : ValidKeyIndEcC S P initSt.base :=
    ⟨validEcLists_nil S, (fun _ h => False.elim (List.not_mem_nil h)), validKeyIndResp_empty S secb⟩
  have ⟨hSimStep, hSupStep⟩ :=
    simulateQ_stepUntilShCrFuelKeyInd1KeyPrim S P hP (idx % S.N_send_tot) A.run initSt b.q_total hV0
      hA.2.2.2.1
  have h_rec0 : initSt.recvKemRecs.length + b.q_total = b.q_total := by
    change ([] : List RecvKemRecord).length + b.q_total = b.q_total
    simp
  rw [← hSimStep, bind_map_left]
  refine bind_congr_of_support
    (simulateQ (primBaseImpl P)
      (stepUntilShCrFuelKeyInd1KeyPrim S (idx % S.N_send_tot) A.run initSt b.q_total))
    _ _ (fun res hres => ?_)
  have hValidRes := hSupStep res hres
  rw [h_rec0] at hValidRes
  cases res with
  | inl done =>
    dsimp only [Sum.map, Sum.elim, Function.comp_def, id] at hValidRes ⊢
    congr 1; ext r
    cases hEnc : P.kemEncaps pk r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩
      dsimp only
      rw [pure_bind,
          simulateQ_extractCollidingKemCtPrim b.q_total P pk sk pk ct ss done.2.recvKemRecs
            hValidRes,
          pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc
  | inr d =>
    simp only [Sum.map, Sum.elim, Function.comp_def,
      PausedShCrData.toPaused1Key_bundle] at hValidRes ⊢
    congr 1; ext r
    cases hEnc : P.kemEncaps d.bundle.pqspkB r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩
      dsimp only
      rcases simulateQ_resumePausedKeyInd1KeyPrim S P hP b.q_total d ss ct hValidRes with
        ⟨hSimRes, hSupRes⟩
      rw [simulateQ_bind, hSimRes, bind_assoc, bind_assoc]
      refine bind_congr_of_support ((PausedShCrData.toPaused1Key P d).resume ss ct) _ _
        (fun z hz => ?_)
      rw [simulateQ_extractCollidingKemCtPrim b.q_total P pk sk d.bundle.pqspkB ct ss
            z.2.recvKemRecs (hSupRes z hz),
          pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc

theorem mul_kemShCr_shcrReductionKeyInd1Key_eq_sum (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) * KemShCrReal P (shcrReductionKeyInd1Key S b A) =
      ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        KemShCrReal P (shcrReductionKeyInd1KeyAt S b idx A.1) := by
  have hSwap :
      𝒟[kemShCrExp P (shcrReductionKeyInd1Key S b A)] =
      𝒟[sampleIndexRange (S.N_spk_tot * S.N_send_tot) >>= fun idx =>
        kemShCrExp P (shcrReductionKeyInd1KeyAt S b idx A.1)] := by
    unfold kemShCrExp shcrReductionKeyInd1Key shcrReductionKeyInd1KeyCore shcrReductionKeyInd1KeyAt
    dsimp only
    simp only [simulateQ_bind, simulateQ_embedUnif, bind_assoc]
    rw [OracleComp.evalDist_bind_bind_swap]
  unfold KemShCrReal KemShCr
  rw [hSwap]
  exact mul_toReal_sampleIndexRange_bind_eq_sum (S.N_spk_tot * S.N_send_tot)
    (fun idx => kemShCrExp P (shcrReductionKeyInd1KeyAt S b idx A.1))

theorem badKemShCrProbKeyInd1Key_le_kemShCr (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    badKemShCrProbKeyInd1Key S P A.1 ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd1Key S b A) := by
  calc badKemShCrProbKeyInd1Key S P A.1
      ≤ ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
          badKemShCrProbKeyInd1KeyAt S P idx A.1 :=
        badKemShCrProbKeyInd1Key_le_sum S P A.1
    _ ≤ ∑ idx ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
          KemShCrReal P (shcrReductionKeyInd1KeyAt S b idx A.1) := by
        refine Finset.sum_le_sum (fun idx _ => ?_)
        unfold KemShCrReal KemShCr
        rw [kemShCrExp_shcrReductionKeyInd1KeyAt_eq S P hP b idx A.1 A.2]
        exact badKemShCrProbKeyInd1KeyAt_le_kemShCrProb S P idx A.1
    _ = ((S.N_spk_tot * S.N_send_tot : ℕ) : ℝ) * KemShCrReal P (shcrReductionKeyInd1Key S b A) :=
        (mul_kemShCr_shcrReductionKeyInd1Key_eq_sum S P b A).symm
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd1Key S b A) := by
        push_cast; ring

/-- Bounds `|keyInd1KeyAdvG2 - keyInd1KeyAdvG3|` via `shcrReductionKeyInd1Key` and the PQSPK
    public-key collision bound. -/
theorem keyInd1Key_hop_G2_G3_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG2 S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd1Key S b A) +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have h1 : |keyInd1KeyAdvG2 S P A.1 - keyInd1KeyAdvG2_5 S P A.1| ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 :=
    keyInd1Key_hop_G2_G2_1_le S P hP A.1
  have h2 : |keyInd1KeyAdvG2_5 S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd1Key S b A) := by
    rw [keyInd1KeyAdvG2_5_eq_ShCr S P A.1]
    exact (keyInd1Key_hop_badKemShCr_le_prob S P A.1).trans
      (badKemShCrProbKeyInd1Key_le_kemShCr S P hP b A)
  have htri := abs_sub_le (keyInd1KeyAdvG2 S P A.1) (keyInd1KeyAdvG2_5 S P A.1)
    (keyInd1KeyAdvG3 S P A.1)
  set_option exponentiation.threshold 512 in
  linarith

/-- Bounds `|KeyInd1KeyRoAdvantageReal - keyInd1KeyAdvG3|` via `sigReductionKeyInd1Key` and
    `shcrReductionKeyInd1Key`. -/
theorem keyInd1Key_hop_G0_G3_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |KeyInd1KeyRoAdvantageReal S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
      (S.N_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1Key S b A) +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd1Key S b A) +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have h0_eq : keyInd1KeyAdvG0 S P A.1 = KeyInd1KeyRoAdvantageReal S P A.1 :=
    keyInd1KeyAdvG0_eq S P A.1
  have h02 := keyInd1Key_hop_G0_G2_le S b P hP A
  have h23 := keyInd1Key_hop_G2_G3_le S P hP b A
  rw [h0_eq] at h02
  have htri := abs_sub_le (KeyInd1KeyRoAdvantageReal S P A.1) (keyInd1KeyAdvG2 S P A.1)
    (keyInd1KeyAdvG3 S P A.1)
  set_option exponentiation.threshold 512 in
  linarith

end Proofs.SignalPqxdh.Security

namespace SignalPqxdh.Security

export _root_.Proofs.SignalPqxdh.Security (
  pqxdhKeyInd1KeyShCrImpl
  pqxdhKeyInd1KeyShCrCachedImpl
  runKeyInd1KeyShCrSim
  badKemShCrProbKeyInd1KeyAt
  badKemShCrProbKeyInd1Key
  keyInd1KeyExpG2_5ShCr
  keyInd1KeyAdvG2_5ShCr
  keyInd1KeyExpG3
  keyInd1KeyAdvG3
  keyInd1Key_hop_G2_G3_le
  keyInd1Key_hop_G0_G3_le
)

end SignalPqxdh.Security

namespace SignalPqxdh

export _root_.Proofs.SignalPqxdh.Security (
  pqxdhKeyInd1KeyShCrImpl
  pqxdhKeyInd1KeyShCrCachedImpl
  runKeyInd1KeyShCrSim
  badKemShCrProbKeyInd1KeyAt
  badKemShCrProbKeyInd1Key
  keyInd1KeyExpG2_5ShCr
  keyInd1KeyAdvG2_5ShCr
  keyInd1KeyExpG3
  keyInd1KeyAdvG3
  keyInd1Key_hop_G2_G3_le
  keyInd1Key_hop_G0_G3_le
)

end SignalPqxdh
