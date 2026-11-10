/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyCoupling -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Creation-Order One-Key `KeyInd` Hop `G2 -> G3` (`KemShCr`) and `G0 -> G3` Combiner

Proves the creation-order `KemShCr` union bound `keyInd1Key_hop_G2_1_G3_active_le` on
`badKemShCrProbKeyInd1Key` via `shcrReductionKeyInd1KeyActive` and combines the `G0 -> G3` active
hops into `KI1KeyActiveHopG0G3Stmt`.
-/


set_option autoImplicit false

open scoped ENNReal BigOperators
open MeasureTheory (measure_ne_top)
open OracleSpec OracleComp
open SignalPqxdh (Setup Bytes Primitives PrincipalEntry SpkBundleEntry PreKeyBundleInput
  HandshakeHdr SessionId KeyIndQuery KeyIndResponse KeyIndState KeyIndAdversary keyIndSpec
  QueryBudget BoundedAdv QueryBounded isGameQuery sampleScalar32 sampleCoins32 sampleRandom64
  sampleKemKeyGen isKeyIndOnlineQuery pqxdhKeyIndImpl pqxdhKeyIndImpl1KeyRo activeIdCount
  activeSpkCount activeSendCount activeDhCount CryptoWellFormedPrimitivesδ
  KeyInd1KeyRoAdvantageReal GapSigEufCmaAdv GapSigEufCma GapSigEufCmaReal KemShCrAdv KemShCr
  KemShCrReal kemShCrExp primBaseImpl)
open SignalPqxdh.Security (keyInd1KeyAdvG0 keyInd1KeyAdvG0_eq keyInd1KeyAdvG0_1 keyInd1KeyAdvG2
  keyInd1KeyAdvG2_1 toReal_bind_bool_mono_of_support toReal_any_range_le_sum simulateQ_embedUnif
  KeyIndShCrState PausedShCrData ShCrFinishState embedUnif liftShCrBasePrim genSpkTargetKeyIndPrim
  postKemKeyIndPrim pqxdhKeyIndImplPrim pqxdhKeyIndShCrPrimImpl pqxdhKeyIndImpl1KeyRoPrim
  tryPauseKeyIndQueryPrim extractCollidingKemCtPrim pqxdhKeyIndCachedImpl CommutesRel
  ValidKeyIndEcC validEcLists_nil validKeyIndResp_empty validSpkBundles_cons
  simulateQ_pqxdhKeyIndImplPrim validKeyIndEc_lengths_le validKeyIndResp_length_le)
open SignalPqxdh.Security.RoKem (sampleIndexRange isNoneKeyIndResp ShCrState applyShCrFinish)
open Proofs.SignalPqxdh.Security (keyInd1KeyAdvG3 keyInd1KeyAdvG2_5 keyInd1KeyAdvG2_5ShCr
  keyInd1KeyAdvG2_5_eq_ShCr keyInd1Key_hop_badKemShCr_le_prob
  pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles pqxdhKeyIndImpl1KeyRo_initPrin_validKeyIndEcC
  simulateQ_run_query_inl simulateQ_run_query_inr bind_congr_of_support
  InitKemRecord RecvKemRecord isKemShCrPair hasBadKemShCrRecords hasBadKemShCrRecordsAt
  badKemShCrProbKeyInd1Key runKeyInd1KeyShCrSim pqxdhKeyInd1KeyShCrImpl
  pqxdhKeyInd1KeyShCrCachedImpl pqxdhKeyInd1KeyShCrCachedImpl_false_commutes_cache
  pqxdhKeyInd1KeyShCrCachedImpl_clearFalse pqxdhKeyInd1KeyShCrCachedImpl_sendStep
  pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs
  pqxdhKeyIndShCrCachedImpl pqxdhKeyIndShCrCachedImpl_pauseNone
  pqxdhKeyIndCachedImpl_preserves_spkBundles cacheShCrAdvKeys clearShCrTarget clearShCrTarget_idem
  clearShCrTarget_eq_iff setShCrTarget liftShCrBase liftShCrBase_setShCrTarget
  liftShCrBase_preserves_bundles liftKeyIndShCrBase genSpkBaseGeneric genSpkTargetGeneric
  mkSpkBundlePair mem_support_genSpkBaseGeneric mem_support_genSpkTargetGeneric
  recordAcceptKemGeneric mem_support_recordAcceptKemGeneric runShCrAcceptGeneric
  runShCrAcceptGeneric_setShCrTarget runShCrAcceptGeneric_preserves_bundles checkBundleSigs
  runShCrInitiate2 postKem2 tryPause2 mem_support_runShCrInitiate2 runShCrInitiate2_setShCrTarget
  runShCrInitiate2_preserves_bundles runShCrInitiate2_pauseNone applyShCrFinish_bundles
  applyShCrFinish_send preCheckKeyInd finishKeyIndBase finishKeyIndBase_spkBundles
  extractCollidingKemCt extractCollidingKemCt_wins_of_mem_recvRecs PausedShCrKem stepUntilShCr
  stepUntilShCr_query_inl stepUntilShCr_query_inr shcrChoosePkGenericAt kemShCrExpProb
  kemShCrWin_pure_eq_of_cwf simulateQ_liftShCrBasePrim simulateQ_pqxdhKeyIndImpl1KeyRoPrim_initPrin
  simulateQ_genSpkTargetKeyIndPrim simulateQ_pqxdhKeyIndShCrPrimImpl
  simulateQ_extractCollidingKemCtPrim simulateQ_tryPauseKeyIndQueryPrim simulateQ_postKemKeyIndPrim
  tryPauseKeyIndQueryData tryPauseKeyIndQueryData_some_props ValidPausedShCrData
  postKem2_validKeyIndEc_and_recvKemRecs mul_toReal_sampleIndexRange_bind_eq_sum)
open Proofs.SignalPqxdh.Security.FgGapDh1Key (validSpkBundles_length_le)
open Proofs.SignalPqxdh.Security.PqxdhDelta (KI1KeyActiveHopG0G3Stmt)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (
  sigReductionKeyInd1KeyActive runKeyIndShCrActiveGenSPKPrim pqxdhKeyIndShCrActivePrimImpl1Key
  runWithFuelKeyInd1KeyActiveShCrPrim stepUntilShCrFuelKeyInd1KeyActivePrim
  resumePausedKeyInd1KeyActivePrim choosePkKeyInd1KeyActivePrimAt
  findCollisionKeyInd1KeyActivePrim shcrReductionKeyInd1KeyActiveAt
  shcrReductionKeyInd1KeyActiveCore shcrReductionKeyInd1KeyActive)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShcrHop

public section
/-! ## Creation-order `KemShCr` coupling (`G2_1 -> G3`) -/

private noncomputable def runShCrActiveGenSPK (embedTarget : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (KeyIndShCrState S) ProbComp KeyIndResponse := fun hst =>
  if !embedTarget then
    (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles := bs })
      KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst
  else
    match hst.targetBIdx? with
    | none =>
      (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles := bs })
        KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst
    | some spkOrd =>
      if hst.base.spkBundles.length == spkOrd then
        (genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
          (fun st bs => { st with spkBundles := bs })
          KeyIndResponse.noneResp KeyIndResponse.bundleResp u j).run hst
      else
        (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
          (fun st bs => { st with spkBundles := bs })
          KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst

private noncomputable def pqxdhKeyInd1KeyActiveShCrCachedImpl (embedTarget : Bool)
    (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) ProbComp)
  | .initPrin u => liftKeyIndShCrBase (pqxdhKeyIndImpl1KeyRo S P (.initPrin u))
  | .genSPK u j => runShCrActiveGenSPK embedTarget S P u j
  | q_other     => pqxdhKeyIndShCrCachedImpl embedTarget S P q_other

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_false_eq (S : Setup) (P : Primitives) :
    pqxdhKeyInd1KeyActiveShCrCachedImpl false S P = pqxdhKeyInd1KeyShCrCachedImpl false S P := by
  funext q; cases q <;> rfl

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_eq_of_ne_genSPK (embedTarget : Bool)
    (S : Setup) (P : Primitives) (q : KeyIndQuery S) (hNotGen : ∀ u j, q ≠ .genSPK u j) :
    pqxdhKeyInd1KeyActiveShCrCachedImpl embedTarget S P q =
      pqxdhKeyInd1KeyShCrCachedImpl embedTarget S P q := by
  cases q <;> first | rfl | exact False.elim (hNotGen _ _ rfl)

private noncomputable def tryPauseKeyInd1KeyActiveQuery (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) : Option (PausedShCrKem S (KeyIndState S)) :=
  match gq, cont with
  | .initiateOPK u i bundle, cont =>
    if bundle.opkB?.isNone then none
    else tryPause2 P KeyIndState.principals (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P)
      (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
      (finishKeyIndBase S P (.sendOPK u i) bundle) sIdx cont hst
  | .initiateNoOPK u i bundle, cont =>
    if bundle.opkB?.isSome then none
    else tryPause2 P KeyIndState.principals (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P)
      (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
      (finishKeyIndBase S P (.sendNoOPK u i) bundle) sIdx cont hst
  | _, _ => none

private noncomputable def shcrChoosePkKeyInd1KeyActiveAt (S : Setup) (P : Primitives)
    (spkOrd sIdx : Nat) (A : KeyIndAdversary S) :
    Bytes → Bytes → ProbComp (Bytes × (Bytes → Bytes → ProbComp Bytes)) :=
  shcrChoosePkGenericAt P ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb))
    (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P)
    (tryPauseKeyInd1KeyActiveQuery S P) spkOrd sIdx A.run

private def hasBadKemShCrActiveAt {S : Setup} (P : Primitives) (spkOrd sIdx : Nat)
    (hst : KeyIndShCrState S) : Bool :=
  match hst.base.spkBundles.reverse[spkOrd]? with
  | none => false
  | some (_, bEntry) =>
    hst.initKemRecs.any (fun i =>
      (i.sendIdx == sIdx) &&
      hst.recvKemRecs.any (fun r =>
        (r.pqspkPk == bEntry.pqspkPk) && (r.pqspkSk == bEntry.pqspkSk) &&
        isKemShCrPair P i r))

private noncomputable def badKemShCrActiveProbKeyInd1KeyAt (S : Setup) (P : Primitives)
    (spkOrd sIdx : Nat) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyInd1KeyShCrSim S P A >>= fun (_, _, finalHst) =>
    pure (hasBadKemShCrActiveAt P spkOrd sIdx finalHst)] {true}).toReal

private theorem runShCrActiveGenSPK_true_run (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndShCrState S) :
    (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P (.genSPK u j)).run hst =
      match hst.targetBIdx? with
      | none => (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
          (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
          KeyIndResponse.bundleResp u j)).run hst
      | some spkOrd =>
          if hst.base.spkBundles.length == spkOrd then
            (genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
              (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
              KeyIndResponse.bundleResp u j).run hst
          else
            (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
              (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
              KeyIndResponse.bundleResp u j)).run hst := rfl

private theorem runShCrActiveGenSPK_true_run_raw (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndShCrState S) :
    (runShCrActiveGenSPK true S P u j).run hst =
      (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P (.genSPK u j)).run hst := rfl

private theorem runShCrActiveGenSPK_setShCrTarget (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndShCrState S) (spkOrd : Nat) (pk sk : Bytes) :
    (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P (.genSPK u j)).run
      (setShCrTarget hst spkOrd pk sk) =
      if hst.base.spkBundles.length == spkOrd then
        (genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
          (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
          KeyIndResponse.bundleResp u j).run (setShCrTarget hst spkOrd pk sk)
      else
        (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
          (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
          KeyIndResponse.bundleResp u j)).run (setShCrTarget hst spkOrd pk sk) := rfl

private def SpkBundlesNoGenStep (bs bs' : List ((Nat × Nat) × SpkBundleEntry)) : Prop :=
  bs' = bs ∨
  ∃ u j : Nat, bs' = bs.map (fun (idx, b) =>
    if idx == (u, j) then (idx, { b with revealed := true }) else (idx, b))

private theorem pqxdhKeyInd1KeyShCrCachedImpl_false_spkBundles_step
    (S : Setup) (P : Primitives) (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst),
      (SpkBundlesNoGenStep hst.base.spkBundles x.2.base.spkBundles ∨
        ∃ e, x.2.base.spkBundles = e :: hst.base.spkBundles) ∧
      ((∀ u j, q ≠ .genSPK u j) →
        SpkBundlesNoGenStep hst.base.spkBundles x.2.base.spkBundles) := by
  have hEqOf : ∀ {x : (keyIndSpec S).Range q × KeyIndShCrState S},
      x.2.base.spkBundles = hst.base.spkBundles →
      (SpkBundlesNoGenStep hst.base.spkBundles x.2.base.spkBundles ∨
        ∃ e, x.2.base.spkBundles = e :: hst.base.spkBundles) ∧
      ((∀ u j, q ≠ .genSPK u j) →
        SpkBundlesNoGenStep hst.base.spkBundles x.2.base.spkBundles) :=
    fun heq => ⟨Or.inl (Or.inl heq), fun _ => Or.inl heq⟩
  cases q
  case initPrin u =>
    exact fun x hx => hEqOf (liftShCrBase_preserves_bundles KeyIndState.spkBundles
      (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) hst
      (pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles S P u hst.base) x hx)
  case genSPK u j =>
    intro x hx
    change x ∈ support ((liftShCrBase (genSpkBaseGeneric P KeyIndState.principals
      KeyIndState.spkBundles (fun st bs => { st with spkBundles := bs })
      KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst) at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases mem_support_genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
      KeyIndResponse.bundleResp u j hst.base y hy with rfl | ⟨_, _, _, _, _, _, _, rfl⟩
    · exact ⟨Or.inl (Or.inl rfl), fun h => False.elim (h u j rfl)⟩
    · exact ⟨Or.inr ⟨_, rfl⟩, fun h => False.elim (h u j rfl)⟩
  case revealSpkSk u j =>
    intro x hx
    have ⟨y, hy, hxy⟩ :
        ∃ y ∈ support ((pqxdhKeyIndImpl true S P (.revealSpkSk u j)).run hst.base),
          x = (y.1, { hst with base := y.2 }) := by
      change x ∈ support ((liftShCrBase (pqxdhKeyIndImpl true S P (.revealSpkSk u j))).run hst) at hx
      simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff] at hx
      exact hx
    subst hxy; unfold pqxdhKeyIndImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    cases hfind : hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      rw [hfind] at hy
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hEqOf rfl
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; rw [hfind] at hy; dsimp only at hy
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨Or.inl (Or.inr ⟨u.val, j.val, rfl⟩), fun _ => Or.inr ⟨u.val, j.val, rfl⟩⟩
  case initiateOPK u i bundle =>
    intro x hx; dsimp only [pqxdhKeyInd1KeyShCrCachedImpl, pqxdhKeyIndShCrCachedImpl] at hx
    cases hopk : bundle.opkB?.isNone
    · simp only [hopk, Bool.false_eq_true, ↓reduceIte] at hx
      exact hEqOf (runShCrInitiate2_preserves_bundles P KeyIndState.principals
        KeyIndState.spkBundles KeyIndResponse.noneResp (preCheckKeyInd S P (.sendOPK u i) u bundle)
        (.sendOPK u i) bundle (finishKeyIndBase S P (.sendOPK u i) bundle) hst
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendOPK u i) bundle uInfo ekASk ss kemCt hst.base out
            hout) x hx)
    · simp only [hopk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hEqOf rfl
  case initiateNoOPK u i bundle =>
    intro x hx; dsimp only [pqxdhKeyInd1KeyShCrCachedImpl, pqxdhKeyIndShCrCachedImpl] at hx
    cases hopk : bundle.opkB?.isSome
    · simp only [hopk, Bool.false_eq_true, ↓reduceIte] at hx
      exact hEqOf (runShCrInitiate2_preserves_bundles P KeyIndState.principals
        KeyIndState.spkBundles KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) hst
        (fun uInfo ekASk ss kemCt out hout =>
          finishKeyIndBase_spkBundles S P (.sendNoOPK u i) bundle uInfo ekASk ss kemCt hst.base out
            hout) x hx)
    · simp only [hopk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hEqOf rfl
  case acceptOPK k j o hdr =>
    exact fun x hx => hEqOf (runShCrAcceptGeneric_preserves_bundles P KeyIndState.spkBundles
      isNoneKeyIndResp (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.acceptOPK k j o hdr) hst.base
        (by intro _ _; simp) (by intro _ _; simp)) x hx)
  case acceptNoOPK k j l hdr =>
    exact fun x hx => hEqOf (runShCrAcceptGeneric_preserves_bundles P KeyIndState.spkBundles
      isNoneKeyIndResp (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P (.acceptNoOPK k j l hdr) hst.base
        (by intro _ _; simp) (by intro _ _; simp)) x hx)
  all_goals
    exact fun x hx => hEqOf (liftShCrBase_preserves_bundles KeyIndState.spkBundles _ hst
      (pqxdhKeyIndCachedImpl_preserves_spkBundles S P _ hst.base
        (by intro _ _; simp) (by intro _ _; simp)) x hx)

private theorem pqxdhKeyInd1KeyShCrCachedImpl_false_spkBundles_len_mono
    (S : Setup) (P : Primitives) (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst),
      hst.base.spkBundles.length ≤ x.2.base.spkBundles.length := by
  intro x hx
  rcases (pqxdhKeyInd1KeyShCrCachedImpl_false_spkBundles_step S P q hst x hx).1 with
    (heq | ⟨_, _, heq⟩) | ⟨_, heq⟩ <;> simp [heq]

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_nonGenSPK_setShCrTarget
    (S : Setup) (P : Primitives) (spkOrd : Nat) (q : KeyIndQuery S)
    (hNotGen : ∀ u j, q ≠ .genSPK u j) (hst : KeyIndShCrState S) (pk sk : Bytes) :
    (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P q).run (setShCrTarget hst spkOrd pk sk) =
      Prod.map id (fun s' => setShCrTarget s' spkOrd pk sk) <$>
        (pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst := by
  cases q
  case initPrin u =>
    exact liftShCrBase_setShCrTarget (pqxdhKeyIndImpl1KeyRo S P (.initPrin u)) hst spkOrd pk sk
  case genSPK u j => exact False.elim (hNotGen u j rfl)
  case initiateOPK u i bundle =>
    dsimp only [pqxdhKeyInd1KeyActiveShCrCachedImpl, pqxdhKeyInd1KeyShCrCachedImpl,
      pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isNone
    · exact runShCrInitiate2_setShCrTarget P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) hst spkOrd pk sk
    · simp [Prod.map, setShCrTarget]
  case initiateNoOPK u i bundle =>
    dsimp only [pqxdhKeyInd1KeyActiveShCrCachedImpl, pqxdhKeyInd1KeyShCrCachedImpl,
      pqxdhKeyIndShCrCachedImpl]
    cases bundle.opkB?.isSome
    · exact runShCrInitiate2_setShCrTarget P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) hst spkOrd pk sk
    · simp [Prod.map, setShCrTarget]
  case acceptOPK k j o hdr =>
    exact runShCrAcceptGeneric_setShCrTarget P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptOPK k j o hdr)) k j hdr hst spkOrd pk sk
  case acceptNoOPK k j l hdr =>
    exact runShCrAcceptGeneric_setShCrTarget P KeyIndState.spkBundles isNoneKeyIndResp
      (pqxdhKeyIndCachedImpl true S P (.acceptNoOPK k j l hdr)) k j hdr hst spkOrd pk sk
  all_goals exact liftShCrBase_setShCrTarget (pqxdhKeyIndCachedImpl true S P _) hst spkOrd pk sk

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_afterGen (S : Setup) (P : Primitives)
    (spkOrd : Nat) (q : KeyIndQuery S) (hst : KeyIndShCrState S)
    (hGen : spkOrd < hst.base.spkBundles.length) :
    (∀ pk sk, (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P q).run
      (setShCrTarget hst spkOrd pk sk) =
      Prod.map id (fun s' => setShCrTarget s' spkOrd pk sk) <$>
        (pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst) ∧
    (∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst),
      spkOrd < x.2.base.spkBundles.length) := by
  refine ⟨?_, fun x hx =>
    Nat.lt_of_lt_of_le hGen (pqxdhKeyInd1KeyShCrCachedImpl_false_spkBundles_len_mono S P q hst x hx)⟩
  by_cases hG : ∃ u j, q = .genSPK u j
  · rcases hG with ⟨u, j, rfl⟩
    intro pk sk
    have hne : (hst.base.spkBundles.length == spkOrd) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hGen)
    rw [runShCrActiveGenSPK_setShCrTarget]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact liftShCrBase_setShCrTarget _ hst spkOrd pk sk
  · exact pqxdhKeyInd1KeyActiveShCrCachedImpl_nonGenSPK_setShCrTarget S P spkOrd q
      (fun u j h => hG ⟨u, j, h⟩) hst

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_beforeGen (S : Setup) (P : Primitives)
    (spkOrd : Nat) (q : KeyIndQuery S) (hst : KeyIndShCrState S)
    (hClear : clearShCrTarget hst = hst) :
    (∀ pk sk, (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P q).run
      (setShCrTarget hst spkOrd pk sk) =
      Prod.map id (fun s' => setShCrTarget s' spkOrd pk sk) <$>
        (pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst) ∨
    ((∀ obs : (keyIndSpec S).Range q × KeyIndShCrState S → ProbComp Bool,
      𝒟[sampleKemKeyGen P >>= fun pair =>
        (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P q).run
          (setShCrTarget hst spkOrd pair.1 pair.2) >>=
          fun x => obs (x.1, clearShCrTarget x.2)] =
      𝒟[(pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst >>= obs]) ∧
     (∀ pk sk,
       ∀ x ∈ support ((pqxdhKeyInd1KeyActiveShCrCachedImpl true S P q).run
         (setShCrTarget hst spkOrd pk sk)),
       x.2 = setShCrTarget (clearShCrTarget x.2) spkOrd pk sk ∧
       spkOrd < (clearShCrTarget x.2).base.spkBundles.length)) := by
  by_cases hG : ∃ u j, q = .genSPK u j
  · rcases hG with ⟨u, j, rfl⟩
    cases hlen : (hst.base.spkBundles.length == spkOrd)
    · left
      intro pk sk
      rw [runShCrActiveGenSPK_setShCrTarget]
      simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      exact liftShCrBase_setShCrTarget _ hst spkOrd pk sk
    · cases hany : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · cases hfind : hst.base.principals.find? (fun (idx, _) => idx == u.val)
        · left
          intro pk sk
          rw [runShCrActiveGenSPK_setShCrTarget]
          simp only [hlen, ↓reduceIte]
          change (genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
              (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
              KeyIndResponse.bundleResp u j).run (setShCrTarget hst spkOrd pk sk) =
            Prod.map id (fun s' => setShCrTarget s' spkOrd pk sk) <$>
              (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
                (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
                KeyIndResponse.bundleResp u j)).run hst
          unfold genSpkTargetGeneric liftShCrBase genSpkBaseGeneric
          dsimp only [setShCrTarget]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          unfold StateT.run
          dsimp only
          rw [hany, hfind]
          simp [Prod.map]
        · rename_i pair
          rcases pair with ⟨_, uEntry⟩
          right
          have hClearSet : ∀ (b' : KeyIndState S) (pk sk : Bytes),
              clearShCrTarget ({ setShCrTarget hst spkOrd pk sk with base := b' } :
                KeyIndShCrState S) = { hst with base := b' } := by
            intro b' pk sk
            rw [clearShCrTarget_eq_iff] at hClear
            cases hst
            dsimp only at hClear
            rcases hClear with ⟨rfl, rfl, rfl⟩
            rfl
          constructor
          · intro obs
            have hTarget : ∀ pair : Bytes × Bytes,
                (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P (.genSPK u j)).run
                  (setShCrTarget hst spkOrd pair.1 pair.2) =
                (sampleScalar32 >>= fun spkSk =>
                 sampleRandom64 >>= fun rSpk =>
                 sampleRandom64 >>= fun rPq =>
                 let (bEntry, bundleOut) :=
                   mkSpkBundlePair P j.val uEntry spkSk rSpk pair.1 pair.2 rPq
                 pure (KeyIndResponse.bundleResp bundleOut,
                   { setShCrTarget hst spkOrd pair.1 pair.2 with
                     base := { hst.base with
                       spkBundles := ((u.val, j.val), bEntry) :: hst.base.spkBundles } })) := by
              intro pair
              rw [runShCrActiveGenSPK_setShCrTarget]
              simp only [hlen, ↓reduceIte]
              unfold genSpkTargetGeneric StateT.run
              dsimp only [setShCrTarget]
              rw [hany, hfind]
              rfl
            have hBase :
                (pqxdhKeyInd1KeyShCrCachedImpl false S P (.genSPK u j)).run hst =
                (sampleScalar32 >>= fun spkSk =>
                 sampleRandom64 >>= fun rSpk =>
                 sampleKemKeyGen P >>= fun pair =>
                 sampleRandom64 >>= fun rPq =>
                 let (bEntry, bundleOut) :=
                   mkSpkBundlePair P j.val uEntry spkSk rSpk pair.1 pair.2 rPq
                 pure (KeyIndResponse.bundleResp bundleOut,
                   { hst with
                     base := { hst.base with
                       spkBundles := ((u.val, j.val), bEntry) :: hst.base.spkBundles } })) := by
              change (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals
                KeyIndState.spkBundles (fun st bs => { st with spkBundles := bs })
                KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst = _
              unfold liftShCrBase genSpkBaseGeneric StateT.run
              dsimp only
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hany, Bool.false_eq_true,
                ↓reduceIte, hfind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                StateT.run_pure, bind_assoc]
            simp only [hTarget, hBase, bind_assoc, pure_bind]
            rw [OracleComp.evalDist_bind_bind_swap (sampleKemKeyGen P) sampleScalar32]
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spkSk _ => ?_)
            rw [OracleComp.evalDist_bind_bind_swap (sampleKemKeyGen P) sampleRandom64]
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rSpk _ => ?_)
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemPair _ => ?_)
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rPq _ => ?_)
            rw [hClearSet]
          · intro pk sk x hx
            rw [runShCrActiveGenSPK_setShCrTarget] at hx
            simp only [hlen, ↓reduceIte] at hx
            unfold genSpkTargetGeneric StateT.run at hx
            dsimp only [setShCrTarget] at hx
            rw [hany, hfind] at hx
            simp only [Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
              support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨spkSk, _, rSpk, _, rPq, _, rfl⟩
            refine ⟨rfl, ?_⟩
            dsimp only [clearShCrTarget]
            have hEqLen : hst.base.spkBundles.length = spkOrd := beq_iff_eq.mp hlen
            simp [hEqLen]
      · left
        intro pk sk
        rw [runShCrActiveGenSPK_setShCrTarget]
        simp only [hlen, ↓reduceIte]
        change (genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
            (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
            KeyIndResponse.bundleResp u j).run (setShCrTarget hst spkOrd pk sk) =
          Prod.map id (fun s' => setShCrTarget s' spkOrd pk sk) <$>
            (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
              (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
              KeyIndResponse.bundleResp u j)).run hst
        unfold genSpkTargetGeneric liftShCrBase genSpkBaseGeneric
        dsimp only [setShCrTarget]
        simp only [StateT.run_bind, StateT.run_get, pure_bind]
        unfold StateT.run
        dsimp only
        rw [hany]
        simp [Prod.map]
  · left
    exact pqxdhKeyInd1KeyActiveShCrCachedImpl_nonGenSPK_setShCrTarget S P spkOrd q
      (fun u j h => hG ⟨u, j, h⟩) hst

private theorem simulateQ_shCrActive_true_eq_false_of_gt {S : Setup} {α : Type}
    (P : Primitives) (spkOrd : Nat)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndShCrState S)
    (hClear : clearShCrTarget hst = hst)
    (hGen : spkOrd < hst.base.spkBundles.length)
    (pk sk : Bytes) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyActiveShCrCachedImpl true S P
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrCachedImpl false S P
    Prod.map id clearShCrTarget <$>
      (simulateQ fullTrue oa).run (setShCrTarget hst spkOrd pk sk) =
      (simulateQ fullFalse oa).run hst := by
  intro fullTrue fullFalse
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp [StateT.run_pure, Prod.map, hClear]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullTrue, fullFalse]
      simp_rw [simulateQ_run_query_inl, map_bind]
      refine bind_congr (fun u => ih u hst hClear hGen)
    | inr gq =>
      dsimp only [fullTrue, fullFalse]
      simp_rw [simulateQ_run_query_inr]
      rcases pqxdhKeyInd1KeyActiveShCrCachedImpl_afterGen S P spkOrd gq hst hGen with
        ⟨hStep, hMono⟩
      rw [hStep pk sk, bind_map_left, map_bind]
      refine bind_congr_of_support ((pqxdhKeyInd1KeyShCrCachedImpl false S P gq).run hst) _ _
        (fun x hx => ?_)
      exact ih x.1 x.2 (pqxdhKeyInd1KeyShCrCachedImpl_clearFalse S P gq hst hClear x hx)
        (hMono x hx)

private theorem evalDist_simulateQ_embedTargetActive_eq {S : Setup} {α : Type}
    (P : Primitives) (spkOrd : Nat)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndShCrState S)
    (hClear : clearShCrTarget hst = hst)
    (obs : α × KeyIndShCrState S → ProbComp Bool) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyActiveShCrCachedImpl true S P
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrCachedImpl false S P
    𝒟[sampleKemKeyGen P >>= fun pair =>
      (simulateQ fullTrue oa).run (setShCrTarget hst spkOrd pair.1 pair.2) >>= fun x =>
      obs (x.1, clearShCrTarget x.2)] =
    𝒟[(simulateQ fullFalse oa).run hst >>= obs] := by
  intro fullTrue fullFalse
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    calc 𝒟[sampleKemKeyGen P >>= fun pair =>
          (simulateQ fullTrue (pure a)).run (setShCrTarget hst spkOrd pair.1 pair.2) >>= fun x =>
          obs (x.1, clearShCrTarget x.2)]
        = 𝒟[sampleKemKeyGen P >>= fun _ => obs (a, hst)] := by
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun _ _ => ?_)
          simp [StateT.run_pure, hClear]
      _ = 𝒟[(simulateQ fullFalse (pure a)).run hst >>= obs] := by
          rw [OracleComp.evalDist_bind_const]
          simp [StateT.run_pure]
  | query_bind q oa ih =>
    by_cases hGen : spkOrd < hst.base.spkBundles.length
    · calc 𝒟[sampleKemKeyGen P >>= fun pair =>
            (simulateQ fullTrue (liftM (OracleSpec.query q) >>= oa)).run
              (setShCrTarget hst spkOrd pair.1 pair.2) >>= fun x =>
            obs (x.1, clearShCrTarget x.2)]
          = 𝒟[sampleKemKeyGen P >>= fun _ =>
              (simulateQ fullFalse (liftM (OracleSpec.query q) >>= oa)).run hst >>= obs] := by
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨pk, sk⟩ _ => ?_)
            have hsim := simulateQ_shCrActive_true_eq_false_of_gt P spkOrd
              (liftM (OracleSpec.query q) >>= oa) hst hClear hGen pk sk
            dsimp only at hsim
            rw [← hsim, bind_map_left]
            rfl
        _ = 𝒟[(simulateQ fullFalse (liftM (OracleSpec.query q) >>= oa)).run hst >>= obs] :=
            OracleComp.evalDist_bind_const _ _
    · cases q with
      | inl uq =>
        dsimp only [fullTrue, fullFalse]
        simp_rw [simulateQ_run_query_inl, bind_assoc]
        rw [OracleComp.evalDist_bind_bind_swap]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ih u hst hClear)
      | inr gq =>
        dsimp only [fullTrue, fullFalse]
        simp_rw [simulateQ_run_query_inr, bind_assoc]
        rcases pqxdhKeyInd1KeyActiveShCrCachedImpl_beforeGen S P spkOrd gq hst hClear with
          hLeft | ⟨hDist, hSupp⟩
        · calc 𝒟[sampleKemKeyGen P >>= fun pair =>
                (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P gq).run
                  (setShCrTarget hst spkOrd pair.1 pair.2) >>= fun x =>
                (simulateQ fullTrue (oa x.1)).run x.2 >>= fun y =>
                obs (y.1, clearShCrTarget y.2)]
              = 𝒟[sampleKemKeyGen P >>= fun pair =>
                  (pqxdhKeyInd1KeyShCrCachedImpl false S P gq).run hst >>= fun x =>
                  (simulateQ fullTrue (oa x.1)).run
                    (setShCrTarget x.2 spkOrd pair.1 pair.2) >>= fun y =>
                  obs (y.1, clearShCrTarget y.2)] := by
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨pk, sk⟩ _ => ?_)
                rw [hLeft pk sk, bind_map_left]
                rfl
            _ = 𝒟[(pqxdhKeyInd1KeyShCrCachedImpl false S P gq).run hst >>= fun x =>
                  (simulateQ fullFalse (oa x.1)).run x.2 >>= obs] := by
                rw [OracleComp.evalDist_bind_bind_swap]
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
                exact ih x.1 x.2 (pqxdhKeyInd1KeyShCrCachedImpl_clearFalse S P gq hst hClear x hx)
        · calc 𝒟[sampleKemKeyGen P >>= fun pair =>
                (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P gq).run
                  (setShCrTarget hst spkOrd pair.1 pair.2) >>= fun x =>
                (simulateQ fullTrue (oa x.1)).run x.2 >>= fun y =>
                obs (y.1, clearShCrTarget y.2)]
              = 𝒟[sampleKemKeyGen P >>= fun pair =>
                  (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P gq).run
                    (setShCrTarget hst spkOrd pair.1 pair.2) >>= fun x =>
                  (simulateQ fullFalse (oa x.1)).run (clearShCrTarget x.2) >>= obs] := by
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨pk, sk⟩ _ => ?_)
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
                rcases hSupp pk sk x hx with ⟨hx_set, hx_gen⟩
                have hsim := simulateQ_shCrActive_true_eq_false_of_gt P spkOrd
                  (oa x.1) (clearShCrTarget x.2) (clearShCrTarget_idem x.2) hx_gen pk sk
                dsimp only at hsim
                rw [← hx_set] at hsim
                rw [← hsim, bind_map_left]
                rfl
            _ = 𝒟[(pqxdhKeyInd1KeyShCrCachedImpl false S P gq).run hst >>= fun x =>
                  (simulateQ fullFalse (oa x.1)).run x.2 >>= obs] :=
                hDist (fun x => (simulateQ fullFalse (oa x.1)).run x.2 >>= obs)

private def ValidTargetRecvActive {S : Setup} (spkOrd : Nat) (pk sk : Bytes)
    (hst : KeyIndShCrState S) : Prop :=
  hst.targetBIdx? = some spkOrd ∧ hst.targetPk = pk ∧ hst.targetSk = sk ∧
  ∀ p, hst.base.spkBundles.reverse[spkOrd]? = some p →
    p.2.pqspkPk = pk ∧ p.2.pqspkSk = sk

private theorem validTargetRecvActive_of_same_bundles {S : Setup} (spkOrd : Nat) (pk sk : Bytes)
    {hst hst' : KeyIndShCrState S} (hV : ValidTargetRecvActive spkOrd pk sk hst)
    (hBIdx : hst'.targetBIdx? = hst.targetBIdx?) (hPk : hst'.targetPk = hst.targetPk)
    (hSk : hst'.targetSk = hst.targetSk) (hB : hst'.base.spkBundles = hst.base.spkBundles) :
    ValidTargetRecvActive spkOrd pk sk hst' := by
  refine ⟨hBIdx.trans hV.1, hPk.trans hV.2.1, hSk.trans hV.2.2.1, ?_⟩
  rw [hB]; exact hV.2.2.2

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_validStep (S : Setup) (P : Primitives)
    (spkOrd : Nat) (pk sk : Bytes) (q : KeyIndQuery S) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecvActive spkOrd pk sk hst) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyActiveShCrCachedImpl true S P q).run hst),
      ValidTargetRecvActive spkOrd pk sk x.2 := by
  by_cases hG : ∃ u j, q = .genSPK u j
  · rcases hG with ⟨u, j, rfl⟩
    intro x hx
    rw [runShCrActiveGenSPK_true_run, hV.1] at hx
    dsimp only at hx
    cases hlen : (hst.base.spkBundles.length == spkOrd)
    · rw [hlen] at hx
      change x ∈ support ((liftShCrBase (genSpkBaseGeneric P KeyIndState.principals
        KeyIndState.spkBundles (fun st bs => { st with spkBundles := bs })
        KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst) at hx
      simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨y, hy, rfl⟩
      rcases mem_support_genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
        KeyIndResponse.bundleResp u j hst.base y hy with
        rfl | ⟨_, _, _, _, _, _, _, rfl⟩
      · exact hV
      · refine ⟨hV.1, hV.2.1, hV.2.2.1, fun p hp => ?_⟩
        dsimp only at hp
        rw [List.reverse_cons] at hp
        have hne : hst.base.spkBundles.length ≠ spkOrd := beq_eq_false_iff_ne.mp hlen
        by_cases hlt : spkOrd < hst.base.spkBundles.length
        · rw [List.getElem?_append_left (by simp [hlt])] at hp
          exact hV.2.2.2 p hp
        · rw [List.getElem?_eq_none (by simp; omega)] at hp
          cases hp
    · rw [hlen] at hx
      change x ∈ support ((genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
        KeyIndResponse.bundleResp u j).run hst) at hx
      rcases mem_support_genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
        KeyIndResponse.bundleResp u j hst x hx with
        rfl | ⟨uEntry, spkSk, rSpk, rPq, _, rfl⟩
      · exact hV
      · refine ⟨hV.1, hV.2.1, hV.2.2.1, fun p hp => ?_⟩
        dsimp only at hp
        have hEqLen : hst.base.spkBundles.length = spkOrd := beq_iff_eq.mp hlen
        rw [List.reverse_cons, List.getElem?_append_right (by simp [hEqLen])] at hp
        simp only [List.length_reverse, hEqLen, Nat.sub_self, List.getElem?_cons_zero,
          Option.some.injEq] at hp
        subst hp
        simp [mkSpkBundlePair, hV.2.1, hV.2.2.1]
  · intro x hx
    have hNotGen : ∀ u j, q ≠ .genSPK u j := fun u j h => hG ⟨u, j, h⟩
    have hEqHst : hst = setShCrTarget (clearShCrTarget hst) spkOrd pk sk := by
      rcases hV with ⟨hbIdx, hPk, hSk, _⟩
      cases hst
      dsimp only at hbIdx hPk hSk
      subst hbIdx hPk hSk
      rfl
    rw [hEqHst, pqxdhKeyInd1KeyActiveShCrCachedImpl_nonGenSPK_setShCrTarget S P spkOrd q hNotGen
      (clearShCrTarget hst) pk sk, support_map, Set.mem_image] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hStep := (pqxdhKeyInd1KeyShCrCachedImpl_false_spkBundles_step S P q
      (clearShCrTarget hst) y hy).2 hNotGen
    have hBaseClear : (clearShCrTarget hst).base = hst.base := rfl
    rw [hBaseClear] at hStep
    rcases hStep with hSame | ⟨u0, j0, hMap⟩
    · exact validTargetRecvActive_of_same_bundles spkOrd pk sk hV hV.1.symm hV.2.1.symm
        hV.2.2.1.symm hSame
    · refine ⟨rfl, rfl, rfl, fun p hp => ?_⟩
      dsimp only [Prod.map, id, setShCrTarget] at hp
      rw [hMap, ← List.map_reverse, List.getElem?_map] at hp
      cases hprev : hst.base.spkBundles.reverse[spkOrd]? with
      | none => rw [hprev] at hp; cases hp
      | some p0 =>
        rw [hprev, Option.map_some, Option.some.injEq] at hp
        rcases p0 with ⟨idx0, b0⟩
        have h0 := hV.2.2.2 (idx0, b0) hprev
        subst hp
        dsimp only
        cases (idx0 == (u0, j0)) <;> exact h0

private theorem runShCrActiveGenSPK_preserves_send (embedTarget : Bool) (S : Setup)
    (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndShCrState S) :
    ∀ x ∈ support ((runShCrActiveGenSPK embedTarget S P u j).run hst),
      x.2.sendCount = hst.sendCount ∧ x.2.initKemRecs = hst.initKemRecs := by
  intro x hx
  have hBase : ∀ z ∈ support ((liftShCrBase (genSpkBaseGeneric P KeyIndState.principals
      KeyIndState.spkBundles (fun st bs => { st with spkBundles := bs })
      KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst),
      z.2.sendCount = hst.sendCount ∧ z.2.initKemRecs = hst.initKemRecs := by
    intro z hz
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact ⟨rfl, rfl⟩
  have hTarget : ∀ z ∈ support ((genSpkTargetGeneric P KeyIndState.principals
      KeyIndState.spkBundles (fun st bs => { st with spkBundles := bs })
      KeyIndResponse.noneResp KeyIndResponse.bundleResp u j).run hst),
      z.2.sendCount = hst.sendCount ∧ z.2.initKemRecs = hst.initKemRecs := by
    intro z hz
    rcases mem_support_genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
      (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
      KeyIndResponse.bundleResp u j hst z hz with rfl | ⟨_, _, _, _, _, rfl⟩ <;>
      exact ⟨rfl, rfl⟩
  cases embedTarget
  · exact hBase x hx
  · rw [runShCrActiveGenSPK_true_run_raw, runShCrActiveGenSPK_true_run] at hx
    cases htb : hst.targetBIdx? with
    | none =>
      rw [htb] at hx
      exact hBase x hx
    | some spkOrd =>
      rw [htb] at hx
      dsimp only at hx
      split_ifs at hx
      · exact hTarget x hx
      · exact hBase x hx

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_sendStep (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyActiveShCrCachedImpl true S P q).run hst),
      hst.sendCount ≤ x.2.sendCount ∧ (∀ i ∈ x.2.initKemRecs, i ∈ hst.initKemRecs ∨
        (i.sendIdx = hst.sendCount ∧ hst.sendCount < x.2.sendCount)) := by
  by_cases hG : ∃ u j, q = .genSPK u j
  · rcases hG with ⟨u, j, rfl⟩; intro x hx
    rcases runShCrActiveGenSPK_preserves_send true S P u j hst x hx with ⟨hS, hI⟩
    exact ⟨by omega, fun i hi => Or.inl (hI ▸ hi)⟩
  · rw [pqxdhKeyInd1KeyActiveShCrCachedImpl_eq_of_ne_genSPK true S P q (fun u j h => hG ⟨u, j, h⟩)]
    exact pqxdhKeyInd1KeyShCrCachedImpl_sendStep S P q hst

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_pauseNone (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (hLe : hst.sendCount ≤ sIdx)
    (hNone : tryPauseKeyInd1KeyActiveQuery S P sIdx gq cont hst = none) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyActiveShCrCachedImpl true S P gq).run hst),
      x.2.sendCount ≤ sIdx := by
  cases gq
  case initPrin u =>
    intro x hx; dsimp only [pqxdhKeyInd1KeyActiveShCrCachedImpl, liftKeyIndShCrBase] at hx
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨_, _, rfl⟩; exact hLe
  case genSPK u j =>
    exact fun x hx => (runShCrActiveGenSPK_preserves_send true S P u j hst x hx).1 ▸ hLe
  case initiateOPK u i bundle =>
    dsimp only [tryPauseKeyInd1KeyActiveQuery] at hNone
    dsimp only [pqxdhKeyInd1KeyActiveShCrCachedImpl, pqxdhKeyIndShCrCachedImpl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hNone; simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate2_pauseNone P KeyIndState.principals
        (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendOPK u i) u bundle) (.sendOPK u i) bundle
        (finishKeyIndBase S P (.sendOPK u i) bundle) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  case initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyInd1KeyActiveQuery] at hNone
    dsimp only [pqxdhKeyInd1KeyActiveShCrCachedImpl, pqxdhKeyIndShCrCachedImpl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hNone; simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
      exact runShCrInitiate2_pauseNone P KeyIndState.principals
        (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P) KeyIndResponse.noneResp
        (preCheckKeyInd S P (.sendNoOPK u i) u bundle) (.sendNoOPK u i) bundle
        (finishKeyIndBase S P (.sendNoOPK u i) bundle) sIdx cont hst hLe hNone
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro x hx; subst hx; exact hLe
  all_goals exact pqxdhKeyIndShCrCachedImpl_pauseNone S P sIdx _ cont hst hLe rfl

private theorem runShCrInitiate2_pauseSome_active {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (spkOrd sIdx : Nat) (pk sk : Bytes)
    (cont : KeyIndResponse → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (paused : PausedShCrKem S (KeyIndState S))
    (hV : ValidTargetRecvActive spkOrd pk sk hst)
    (hSome : tryPause2 P KeyIndState.principals (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P)
      (preCheckKeyInd S P sid u bundle) sid bundle (finishKeyIndBase S P sid bundle)
      sIdx cont hst = some paused) :
    ∃ (noneOut : KeyIndResponse)
      (postKem : Bytes → Bytes → ProbComp (KeyIndResponse × KeyIndShCrState S)),
      (∀ ss ct, paused.resume ss ct =
        (postKem ss ct >>= fun y =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (KeyIndShCrState S) ProbComp) +
              pqxdhKeyInd1KeyActiveShCrCachedImpl true S P) (cont y.1)).run y.2)) ∧
      (∀ obs : KeyIndResponse × KeyIndShCrState S → ProbComp Bool,
        𝒟[(runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
            (preCheckKeyInd S P sid u bundle) sid bundle
            (finishKeyIndBase S P sid bundle)).run hst >>= obs] =
        𝒟[sampleCoins32 >>= fun r =>
          match P.kemEncaps paused.bundle.pqspkB r with
          | none => obs (noneOut, { hst with sendCount := sIdx + 1 })
          | some (ss, ct) => postKem ss ct >>= obs]) ∧
      (∀ ss ct, ∀ y ∈ support (postKem ss ct),
        ValidTargetRecvActive spkOrd pk sk y.2 ∧
        sIdx < y.2.sendCount ∧
        (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
          (i.sendIdx = sIdx ∧
           i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))) := by
  unfold tryPause2 at hSome
  cases hpre : preCheckKeyInd S P sid u bundle hst.base with
  | none => rw [hpre] at hSome; cases hSome
  | some uInfo =>
    rw [hpre] at hSome
    dsimp only at hSome
    cases hsig : checkBundleSigs P hst.base.principals bundle
    · rw [hsig] at hSome; simp at hSome
    · rw [hsig] at hSome
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSome
      cases hcnt : (hst.sendCount == sIdx)
      · rw [hcnt] at hSome; simp at hSome
      · rw [hcnt] at hSome
        simp only [↓reduceIte, Option.some.injEq] at hSome
        subst hSome
        have hsIdx : hst.sendCount = sIdx := beq_iff_eq.mp hcnt
        refine ⟨KeyIndResponse.noneResp,
          postKem2 sid bundle uInfo (finishKeyIndBase S P sid bundle) hst, ?_, ?_, ?_⟩
        · intro ss ct; rfl
        · intro obs
          unfold runShCrInitiate2 StateT.run postKem2
          dsimp only
          rw [hpre]
          dsimp only
          simp only [hsig, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
          rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 sampleCoins32]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
          cases P.kemEncaps bundle.pqspkB r with
          | none =>
            simp only [pure_bind, hsIdx]
            exact OracleComp.evalDist_bind_const _ _
          | some kemPair =>
            rcases kemPair with ⟨ss, ct⟩
            simp only [bind_map_left]
        · intro ss ct y hy
          unfold postKem2 at hy
          simp only [MonadAttach.mem_support_bind, support_map, Set.mem_image] at hy
          rcases hy with ⟨ekASk, _, out, hout, rfl⟩
          have hB := applyShCrFinish_bundles KeyIndState.spkBundles sid bundle.pqspkB ss ct hst out
            (finishKeyIndBase_spkBundles S P sid bundle uInfo ekASk ss ct hst.base out hout)
          have hVy : ValidTargetRecvActive spkOrd pk sk
              (applyShCrFinish sid bundle.pqspkB ss ct hst out).2 := by
            rcases out with ⟨_, none | _⟩ <;>
              exact validTargetRecvActive_of_same_bundles spkOrd pk sk hV rfl rfl rfl hB
          rcases applyShCrFinish_send sid bundle.pqspkB ss ct hst out with ⟨hSend, hInit⟩
          refine ⟨hVy, by omega, fun i hi => ?_⟩
          rcases hInit i hi with hi_old | ⟨hi_idx, hi_pk, hi_ct, hi_ss⟩
          · exact Or.inl hi_old
          · exact Or.inr ⟨hi_idx.trans hsIdx, hi_pk, hi_ct, hi_ss⟩

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_pauseSome (S : Setup) (P : Primitives)
    (spkOrd sIdx : Nat) (pk sk : Bytes)
    (gq : KeyIndQuery S) (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (paused : PausedShCrKem S (KeyIndState S))
    (hV : ValidTargetRecvActive spkOrd pk sk hst)
    (hSome : tryPauseKeyInd1KeyActiveQuery S P sIdx gq cont hst = some paused) :
    ∃ (noneOut : (keyIndSpec S).Range gq)
      (postKem : Bytes → Bytes → ProbComp ((keyIndSpec S).Range gq × KeyIndShCrState S)),
      (∀ ss ct, paused.resume ss ct =
        (postKem ss ct >>= fun y =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (KeyIndShCrState S) ProbComp) +
              pqxdhKeyInd1KeyActiveShCrCachedImpl true S P) (cont y.1)).run y.2)) ∧
      (∀ obs : (keyIndSpec S).Range gq × KeyIndShCrState S → ProbComp Bool,
        𝒟[(pqxdhKeyInd1KeyActiveShCrCachedImpl true S P gq).run hst >>= obs] =
        𝒟[sampleCoins32 >>= fun r =>
          match P.kemEncaps paused.bundle.pqspkB r with
          | none => obs (noneOut, { hst with sendCount := sIdx + 1 })
          | some (ss, ct) => postKem ss ct >>= obs]) ∧
      (∀ ss ct, ∀ y ∈ support (postKem ss ct),
        ValidTargetRecvActive spkOrd pk sk y.2 ∧
        sIdx < y.2.sendCount ∧
        (∀ i ∈ y.2.initKemRecs, i ∈ hst.initKemRecs ∨
          (i.sendIdx = sIdx ∧
           i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss))) := by
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyInd1KeyActiveQuery] at hSome
    dsimp only [pqxdhKeyInd1KeyActiveShCrCachedImpl, pqxdhKeyIndShCrCachedImpl]
    cases hopk : bundle.opkB?.isNone
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate2_pauseSome_active P (.sendOPK u i) u bundle spkOrd sIdx pk sk cont hst
        paused hV hSome
    · rw [hopk] at hSome; simp at hSome
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyInd1KeyActiveQuery] at hSome
    dsimp only [pqxdhKeyInd1KeyActiveShCrCachedImpl, pqxdhKeyIndShCrCachedImpl]
    cases hopk : bundle.opkB?.isSome
    · rw [hopk] at hSome
      simp only [Bool.false_eq_true, ↓reduceIte] at hSome ⊢
      exact runShCrInitiate2_pauseSome_active P (.sendNoOPK u i) u bundle spkOrd sIdx pk sk cont
        hst paused hV hSome
    · rw [hopk] at hSome; simp at hSome
  | _ => cases hSome

private theorem hasBadKemShCrActiveAt_eq_false_of_forall_ne {S : Setup} (P : Primitives)
    (spkOrd sIdx : Nat) (hst : KeyIndShCrState S)
    (hne : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ sIdx) :
    hasBadKemShCrActiveAt P spkOrd sIdx hst = false := by
  unfold hasBadKemShCrActiveAt
  cases hst.base.spkBundles.reverse[spkOrd]? with
  | none => rfl
  | some p =>
    rcases p with ⟨_, bEntry⟩
    rw [List.any_eq_false]
    intro i hi htrue
    simp only [Bool.and_eq_true, beq_iff_eq] at htrue
    exact hne i hi htrue.1

private theorem simulateQ_post_sIdx_active_invariant {S : Setup} {α : Type} (P : Primitives)
    (spkOrd sIdx : Nat) (pk sk : Bytes)
    (P_rec : InitKemRecord S → Prop)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecvActive spkOrd pk sk hst)
    (hLt : sIdx < hst.sendCount)
    (hRec : ∀ i ∈ hst.initKemRecs, i.sendIdx = sIdx → P_rec i) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyActiveShCrCachedImpl true S P
    ∀ x ∈ support ((simulateQ fullTrue oa).run hst),
      ValidTargetRecvActive spkOrd pk sk x.2 ∧
      sIdx < x.2.sendCount ∧
      (∀ i ∈ x.2.initKemRecs, i.sendIdx = sIdx → P_rec i) := by
  intro fullTrue
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    intro x hx
    change x ∈ support (pure (a, hst)) at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hV, hLt, hRec⟩
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      intro x hx
      dsimp only [fullTrue] at hx
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx⟩
      exact ih u hst hV hLt hRec x hx
    | inr gq =>
      intro x hx
      dsimp only [fullTrue] at hx
      rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨y, hy, hx⟩
      have hVy := pqxdhKeyInd1KeyActiveShCrCachedImpl_validStep S P spkOrd pk sk gq hst hV y hy
      rcases pqxdhKeyInd1KeyActiveShCrCachedImpl_sendStep S P gq hst y hy with ⟨hLe, hInit⟩
      have hLty : sIdx < y.2.sendCount := Nat.lt_of_lt_of_le hLt hLe
      have hRecy : ∀ i ∈ y.2.initKemRecs, i.sendIdx = sIdx → P_rec i := by
        intro i hi his
        rcases hInit i hi with hi_old | ⟨_, _⟩
        · exact hRec i hi_old his
        · omega
      exact ih y.1 y.2 hVy hLty hRecy x hx

private theorem evalDist_simulateQ_badKemActive_eq_zero_of_gt {S : Setup} {α : Type}
    (P : Primitives) (spkOrd sIdx : Nat) (pk sk : Bytes)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecvActive spkOrd pk sk hst)
    (hLt : sIdx < hst.sendCount)
    (hNe : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ sIdx) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyActiveShCrCachedImpl true S P
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)] {true} = 0 := by
  intro fullTrue
  have hPost := simulateQ_post_sIdx_active_invariant P spkOrd sIdx pk sk (fun _ => False)
    oa hst hV hLt (fun i hi heq => hNe i hi heq)
  have h_congr :
      𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
        pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)] =
      𝒟[(simulateQ fullTrue oa).run hst >>= fun _ => (pure false : ProbComp Bool)] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
    rw [hasBadKemShCrActiveAt_eq_false_of_forall_ne P spkOrd sIdx x.2
      (fun i hi heq => (hPost x hx).2.2 i hi heq)]
  rw [h_congr, OracleComp.evalDist_bind_const]
  simp [evalDist_pure]

private theorem evalDist_simulateQ_badKemActive_le_win_of_gt {S : Setup} {α : Type}
    (P : Primitives) (spkOrd sIdx : Nat) (pk sk chosenPk ct ss : Bytes)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecvActive spkOrd pk sk hst)
    (hLt : sIdx < hst.sendCount)
    (hRec : ∀ i ∈ hst.initKemRecs, i.sendIdx = sIdx →
      i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) :
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyActiveShCrCachedImpl true S P
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)] {true} ≤
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      let ct' := extractCollidingKemCt P pk sk chosenPk ct ss x.2.recvKemRecs
      pure (decide (P.kemDecaps sk ct' = some ss) && decide (ct' ≠ ct ∨ chosenPk ≠ pk))] {true} := by
  intro fullTrue
  have hPost := simulateQ_post_sIdx_active_invariant P spkOrd sIdx pk sk
    (fun i => i.pqspkPk = chosenPk ∧ i.kemCt = ct ∧ i.kemSs = ss) oa hst hV hLt hRec
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun x hx => ?_)
  rcases hPost x hx with ⟨hVx, _, hRecx⟩
  cases hbad : hasBadKemShCrActiveAt P spkOrd sIdx x.2
  · simp [evalDist_pure]
  · unfold hasBadKemShCrActiveAt at hbad
    cases hrev : x.2.base.spkBundles.reverse[spkOrd]? with
    | none => rw [hrev] at hbad; cases hbad
    | some p =>
      rw [hrev] at hbad
      rcases p with ⟨kj, bEntry⟩
      rcases hVx.2.2.2 (kj, bEntry) hrev with ⟨hBpk, hBsk⟩
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hbad
      rcases hbad with ⟨i, hi_mem, hi_idx, r, hr_mem, ⟨hr_pk, hr_sk⟩, hpair⟩
      rcases hRecx i hi_mem hi_idx with ⟨hi_pk, hi_ct, hi_ss⟩
      have hwin := extractCollidingKemCt_wins_of_mem_recvRecs P pk sk chosenPk ct ss
        x.2.recvKemRecs i r hr_mem (hr_sk.trans hBsk) (hr_pk.trans hBpk) hi_pk hi_ct hi_ss hpair
      simp only [hwin, le_rfl]

private theorem evalDist_stepUntilShCrActive_le {S : Setup} (P : Primitives)
    (spkOrd sIdx : Nat) (pk sk : Bytes)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) (hst : KeyIndShCrState S)
    (hV : ValidTargetRecvActive spkOrd pk sk hst)
    (hLe : hst.sendCount ≤ sIdx)
    (hInitLt : ∀ i ∈ hst.initKemRecs, i.sendIdx < hst.sendCount) :
    let implTrue := pqxdhKeyInd1KeyActiveShCrCachedImpl true S P
    let fullTrue := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + implTrue
    𝒟[(simulateQ fullTrue oa).run hst >>= fun x =>
      pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)] {true} ≤
    𝒟[stepUntilShCr implTrue (tryPauseKeyInd1KeyActiveQuery S P sIdx) oa hst >>= fun res =>
      let chosenPk := match res with
        | Sum.inl _      => pk
        | Sum.inr paused => paused.bundle.pqspkB
      sampleCoins32 >>= fun r =>
      match P.kemEncaps chosenPk r with
      | none => pure false
      | some (ss, ct) =>
        (match res with
         | Sum.inl done   => pure done
         | Sum.inr paused => paused.resume ss ct) >>= fun x =>
        let ct' := extractCollidingKemCt P pk sk chosenPk ct ss x.2.recvKemRecs
        pure (decide (P.kemDecaps sk ct' = some ss) && decide (ct' ≠ ct ∨ chosenPk ≠ pk))] {true} := by
  intro implTrue fullTrue
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure b' =>
    have hne : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ sIdx := by
      intro i hi; have := hInitLt i hi; omega
    have h_lhs :
        ((simulateQ fullTrue (pure b')).run hst >>= fun x =>
          pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)) = pure false := by
      simp [StateT.run_pure, hasBadKemShCrActiveAt_eq_false_of_forall_ne P spkOrd sIdx hst hne]
    rw [h_lhs]
    simp [evalDist_pure]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullTrue]
      rw [simulateQ_run_query_inl, stepUntilShCr_query_inl, bind_assoc, bind_assoc]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
        (fun u _ => ih u hst hV hLe hInitLt)
    | inr gq =>
      dsimp only [fullTrue]
      rw [simulateQ_run_query_inr, stepUntilShCr_query_inr, bind_assoc]
      cases hPause : tryPauseKeyInd1KeyActiveQuery S P sIdx gq oa hst with
      | none =>
        dsimp only
        rw [bind_assoc]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
          (fun x hx => ?_)
        have hVx := pqxdhKeyInd1KeyActiveShCrCachedImpl_validStep S P spkOrd pk sk gq hst hV x hx
        have hLex := pqxdhKeyInd1KeyActiveShCrCachedImpl_pauseNone S P sIdx gq oa hst hLe hPause x hx
        rcases pqxdhKeyInd1KeyActiveShCrCachedImpl_sendStep S P gq hst x hx with ⟨hSendLe, hInit⟩
        have hInitLtx : ∀ i ∈ x.2.initKemRecs, i.sendIdx < x.2.sendCount := by
          intro i hi
          rcases hInit i hi with hi_old | ⟨_, _⟩
          · exact Nat.lt_of_lt_of_le (hInitLt i hi_old) hSendLe
          · omega
        exact ih x.1 x.2 hVx hLex hInitLtx
      | some paused =>
        rcases pqxdhKeyInd1KeyActiveShCrCachedImpl_pauseSome S P spkOrd sIdx pk sk gq oa hst paused
          hV hPause with ⟨noneOut, postKem, hResume, hDist, hPostSupp⟩
        dsimp only
        rw [pure_bind, hDist (fun x => (simulateQ fullTrue (oa x.1)).run x.2 >>= fun y =>
          pure (hasBadKemShCrActiveAt P spkOrd sIdx y.2))]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
          (fun r _ => ?_)
        cases P.kemEncaps paused.bundle.pqspkB r with
        | none =>
          have hV_next : ValidTargetRecvActive spkOrd pk sk
              { hst with sendCount := sIdx + 1 } := hV
          have hNe : ∀ i ∈ hst.initKemRecs, i.sendIdx ≠ sIdx := by
            intro i hi; have := hInitLt i hi; omega
          have hZero := evalDist_simulateQ_badKemActive_eq_zero_of_gt P spkOrd sIdx pk sk
            (oa noneOut) { hst with sendCount := sIdx + 1 } hV_next (Nat.lt_succ_self _) hNe
          dsimp only at hZero
          rw [hZero]
          simp [evalDist_pure]
        | some kemPair =>
          rcases kemPair with ⟨ss, ct⟩
          dsimp only
          rw [hResume ss ct, bind_assoc]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
            (fun y hy => ?_)
          rcases hPostSupp ss ct y hy with ⟨hVy, hLty, hInity⟩
          have hRecy : ∀ i ∈ y.2.initKemRecs, i.sendIdx = sIdx →
              i.pqspkPk = paused.bundle.pqspkB ∧ i.kemCt = ct ∧ i.kemSs = ss := by
            intro i hi his
            rcases hInity i hi with hi_old | ⟨_, hpk, hct, hss⟩
            · have := hInitLt i hi_old; omega
            · exact ⟨hpk, hct, hss⟩
          exact evalDist_simulateQ_badKemActive_le_win_of_gt P spkOrd sIdx pk sk
            paused.bundle.pqspkB ct ss (oa y.1) y.2 hVy hLty hRecy

private theorem badKemShCrActiveProbGenericAt_le_kemShCr {S : Setup} (P : Primitives)
    (initBaseComp : ProbComp (KeyIndState S)) (spkOrd sIdx : Nat)
    (hInitBundles : ∀ b0 ∈ support initBaseComp, b0.spkBundles = [])
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) :
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrCachedImpl false S P
    𝒟[initBaseComp >>= fun b0 =>
      (simulateQ fullFalse oa).run { base := b0 } >>= fun x =>
      pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)] {true} ≤
    𝒟[kemShCrExpProb P (shcrChoosePkGenericAt P initBaseComp
      (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P)
      (tryPauseKeyInd1KeyActiveQuery S P) spkOrd sIdx oa)] {true} := by
  intro fullFalse
  have h_embed :
      𝒟[initBaseComp >>= fun b0 =>
        (simulateQ fullFalse oa).run { base := b0 } >>= fun x =>
        pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)] =
      𝒟[initBaseComp >>= fun b0 =>
        sampleKemKeyGen P >>= fun pair =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndShCrState S) ProbComp) +
            pqxdhKeyInd1KeyActiveShCrCachedImpl true S P) oa).run
          (setShCrTarget { base := b0 } spkOrd pair.1 pair.2) >>= fun x =>
        pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)] := by
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun b0 _ => ?_)
    exact (evalDist_simulateQ_embedTargetActive_eq P spkOrd oa { base := b0 } rfl
      (fun x => pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2))).symm
  rw [h_embed, OracleComp.evalDist_bind_bind_swap]
  unfold kemShCrExpProb shcrChoosePkGenericAt
  simp only [bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun pksk _ => ?_)
  rcases pksk with ⟨pk, sk⟩
  dsimp only
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun b0 hb0 => ?_)
  have hV0 : ValidTargetRecvActive spkOrd pk sk
      (setShCrTarget ({ base := b0 } : KeyIndShCrState S) spkOrd pk sk) := by
    refine ⟨rfl, rfl, rfl, fun p hp => ?_⟩
    simp [setShCrTarget, hInitBundles b0 hb0] at hp
  have hInit0 : ∀ i ∈ (setShCrTarget ({ base := b0 } : KeyIndShCrState S) spkOrd pk sk).initKemRecs,
      i.sendIdx < (setShCrTarget ({ base := b0 } : KeyIndShCrState S) spkOrd pk sk).sendCount := by
    intro i hi; simp [setShCrTarget] at hi
  have hStep := evalDist_stepUntilShCrActive_le P spkOrd sIdx pk sk oa
    (setShCrTarget ({ base := b0 } : KeyIndShCrState S) spkOrd pk sk)
    hV0 (Nat.zero_le _) hInit0
  dsimp only at hStep
  refine le_trans hStep ?_
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun res _ => ?_)
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun r _ => ?_)
  cases res with
  | inl done =>
    dsimp only
    cases P.kemEncaps pk r with
    | none => exact le_rfl
    | some kemPair =>
      rcases kemPair with ⟨ss, ct⟩
      dsimp only
      rw [pure_bind, pure_bind]
  | inr paused =>
    dsimp only
    cases P.kemEncaps paused.bundle.pqspkB r with
    | none => exact le_rfl
    | some kemPair =>
      rcases kemPair with ⟨ss, ct⟩
      dsimp only
      rw [bind_assoc]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
        (fun x _ => ?_)
      rw [pure_bind]

private theorem badKemShCrActiveProbKeyInd1KeyAt_le_kemShCrProb (S : Setup) (P : Primitives)
    (spkOrd sIdx : Nat) (A : KeyIndAdversary S) :
    badKemShCrActiveProbKeyInd1KeyAt S P spkOrd sIdx A ≤
      (𝒟[kemShCrExpProb P (shcrChoosePkKeyInd1KeyActiveAt S P spkOrd sIdx A)] {true}).toReal := by
  unfold badKemShCrActiveProbKeyInd1KeyAt shcrChoosePkKeyInd1KeyActiveAt
  have hEq :
      (runKeyInd1KeyShCrSim S P A >>= fun (_, _, finalHst) =>
        pure (hasBadKemShCrActiveAt P spkOrd sIdx finalHst)) =
      (($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb)) >>= fun b0 =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndShCrState S) ProbComp) +
            pqxdhKeyInd1KeyShCrCachedImpl false S P) A.run).run { base := b0 } >>= fun x =>
        pure (hasBadKemShCrActiveAt P spkOrd sIdx x.2)) := by
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
  exact badKemShCrActiveProbGenericAt_le_kemShCr P
    ($ᵗ Bool >>= fun secb => pure (KeyIndState.empty S secb)) spkOrd sIdx
    (by
      intro b0 hb0
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb0
      rcases hb0 with ⟨_, _, rfl⟩
      rfl)
    A.run

/-! ## `PrimBaseSpec` equivalence and active `KemShCr` union bound -/

private theorem pqxdhKeyInd1KeyActiveShCrCachedImpl_validKeyIndEc_and_recvKemRecs
    (embedTarget : Bool) (S : Setup) (P : Primitives) (gq : KeyIndQuery S)
    (hst : KeyIndShCrState S) (hV : ValidKeyIndEcC S P hst.base) :
    ∀ x ∈ support ((pqxdhKeyInd1KeyActiveShCrCachedImpl embedTarget S P gq).run hst),
      ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
  by_cases hG : ∃ u j, gq = .genSPK u j
  · rcases hG with ⟨u, j, rfl⟩
    have hBase : ∀ x ∈ support ((liftShCrBase (genSpkBaseGeneric P KeyIndState.principals
        KeyIndState.spkBundles (fun st bs => { st with spkBundles := bs })
        KeyIndResponse.noneResp KeyIndResponse.bundleResp u j)).run hst),
        ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 :=
      pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs false S P (.genSPK u j) hst hV
    have hTarget : ∀ x ∈ support ((genSpkTargetGeneric P KeyIndState.principals
        KeyIndState.spkBundles (fun st bs => { st with spkBundles := bs })
        KeyIndResponse.noneResp KeyIndResponse.bundleResp u j).run hst),
        ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + 1 := by
      intro x hx
      rcases mem_support_genSpkTargetGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
        KeyIndResponse.bundleResp u j hst x hx with rfl | ⟨_, _, _, _, hFresh, rfl⟩
      · exact ⟨hV, by simp⟩
      · exact ⟨⟨⟨hV.1.1, (validSpkBundles_cons S u j _ hst.base.spkBundles hV.1.2.1 hFresh).1,
          hV.1.2.2.1, hV.1.2.2.2⟩, hV.2⟩, by simp⟩
    cases embedTarget
    · exact hBase
    · intro x hx; rw [runShCrActiveGenSPK_true_run] at hx
      cases htb : hst.targetBIdx? with
      | none => rw [htb] at hx; exact hBase x hx
      | some spkOrd =>
        rw [htb] at hx; dsimp only at hx; split_ifs at hx
        · exact hTarget x hx
        · exact hBase x hx
  · rw [pqxdhKeyInd1KeyActiveShCrCachedImpl_eq_of_ne_genSPK embedTarget S P gq
      (fun u j h => hG ⟨u, j, h⟩)]
    exact pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs embedTarget S P gq hst hV

private theorem simulateQ_runKeyIndShCrActiveGenSPKPrim (embedTarget : Bool) (S : Setup)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hst : KeyIndShCrState S) (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) ((runKeyIndShCrActiveGenSPKPrim embedTarget S u j).run hst) =
      (runShCrActiveGenSPK embedTarget S P u j).run hst := by
  rcases validKeyIndEc_lengths_le S P hst.base hV.1 with ⟨hPrin, hSpk, hOpk, hSess⟩
  dsimp only [runKeyIndShCrActiveGenSPKPrim, runShCrActiveGenSPK, StateT.run]
  have hBase : simulateQ (primBaseImpl P)
      ((liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run hst) =
      (liftShCrBase (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
        (fun st bs => { st with spkBundles := bs }) KeyIndResponse.noneResp
        KeyIndResponse.bundleResp u j)).run hst := by
    rw [simulateQ_liftShCrBasePrim P _ _ hst (simulateQ_pqxdhKeyIndImplPrim true S P hP
      (.genSPK u j) hst.base hPrin hSpk hOpk hSess
      (validKeyIndResp_length_le S hst.base hV.2.2) hV.2.1)]; rfl
  split_ifs
  · exact hBase
  · cases hst.targetBIdx? with
    | none => exact hBase
    | some spkOrd =>
      dsimp only; split_ifs
      · exact simulateQ_genSpkTargetKeyIndPrim S P u j hst
      · exact hBase

private theorem simulateQ_pqxdhKeyIndShCrActivePrimImpl1Key (embedTarget : Bool) (S : Setup)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (gq : KeyIndQuery S)
    (hst : KeyIndShCrState S) (hV : ValidKeyIndEcC S P hst.base) :
    simulateQ (primBaseImpl P) ((pqxdhKeyIndShCrActivePrimImpl1Key embedTarget S gq).run hst) =
      (pqxdhKeyInd1KeyActiveShCrCachedImpl embedTarget S P gq).run hst := by
  cases gq
  case initPrin u =>
    exact simulateQ_liftShCrBasePrim P _ _ hst
      (simulateQ_pqxdhKeyIndImpl1KeyRoPrim_initPrin S P u hst.base)
  case genSPK u j => exact simulateQ_runKeyIndShCrActiveGenSPKPrim embedTarget S P hP u j hst hV
  all_goals
    dsimp only [pqxdhKeyIndShCrActivePrimImpl1Key, pqxdhKeyInd1KeyActiveShCrCachedImpl]
    exact simulateQ_pqxdhKeyIndShCrPrimImpl embedTarget S P hP _ hst hV

private noncomputable def toPaused1KeyActive {S : Setup} (P : Primitives)
    (d : PausedShCrData S) : PausedShCrKem S (KeyIndState S) where
  bundle := d.bundle
  resume := fun ss kemCt =>
    postKem2 d.sid d.bundle d.uEntry (finishKeyIndBase S P d.sid d.bundle) d.hst ss kemCt >>=
      fun y => (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) +
          pqxdhKeyInd1KeyActiveShCrCachedImpl true S P) (d.cont y.1)).run y.2

private theorem toPaused1KeyActive_bundle {S : Setup} (P : Primitives)
    (d : PausedShCrData S) : (toPaused1KeyActive P d).bundle = d.bundle := rfl

private theorem map_toPaused1KeyActive_tryPauseKeyIndQueryData (S : Setup) (P : Primitives)
    (sIdx : Nat) (gq : KeyIndQuery S)
    (cont : (keyIndSpec S).Range gq → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) :
    (tryPauseKeyIndQueryData S P sIdx gq cont hst).map (toPaused1KeyActive P) =
      tryPauseKeyInd1KeyActiveQuery S P sIdx gq cont hst := by
  cases gq with
  | initiateOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryData, tryPauseKeyInd1KeyActiveQuery, tryPause2]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckKeyInd S P (.sendOPK u i) u bundle hst.base with
      | none => rfl
      | some uEntry => dsimp only; split_ifs <;> rfl
    · rfl
  | initiateNoOPK u i bundle =>
    dsimp only [tryPauseKeyIndQueryData, tryPauseKeyInd1KeyActiveQuery, tryPause2]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases preCheckKeyInd S P (.sendNoOPK u i) u bundle hst.base with
      | none => rfl
      | some uEntry => dsimp only; split_ifs <;> rfl
    · rfl
  | _ => rfl

private theorem simulateQ_runWithFuelKeyInd1KeyActiveShCrPrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : Nat) (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    simulateQ (primBaseImpl P) (runWithFuelKeyInd1KeyActiveShCrPrim S oa hst fuel) =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) +
          pqxdhKeyInd1KeyActiveShCrCachedImpl true S P) oa).run hst := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b => simp [runWithFuelKeyInd1KeyActiveShCrPrim]
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      simp only [runWithFuelKeyInd1KeyActiveShCrPrim, OracleComp.construct_query_bind,
        simulateQ_bind, simulateQ_embedUnif, StateT.run_bind,
        QueryImpl.simulateQ_add_query_left, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr (fun u => ih u hst fuel hV (h_cont u))
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exact False.elim (h_abs rfl)
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          simp only [runWithFuelKeyInd1KeyActiveShCrPrim, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_pqxdhKeyIndShCrActivePrimImpl1Key true S P hP gq hst hV,
            StateT.run_bind, QueryImpl.simulateQ_add_query_right]
          refine bind_congr_of_support
            ((pqxdhKeyInd1KeyActiveShCrCachedImpl true S P gq).run hst) _ _ (fun x hx => ?_)
          exact ih x.1 x.2 f
            (pqxdhKeyInd1KeyActiveShCrCachedImpl_validKeyIndEc_and_recvKemRecs
              true S P gq hst hV x hx).1 (h_cont x.1)

private theorem simulateQ_pqxdhKeyInd1KeyActiveShCrCachedImpl_validKeyIndEc_and_recvKemRecs
    (embedTarget : Bool) (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) (hst : KeyIndShCrState S) (fuel : Nat)
    (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) +
          pqxdhKeyInd1KeyActiveShCrCachedImpl embedTarget S P
    ∀ x ∈ support ((simulateQ fullImpl oa).run hst),
      ValidKeyIndEcC S P x.2.base ∧ x.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel := by
  intro fullImpl
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨hV, Nat.le_add_right _ _⟩
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      dsimp only [fullImpl]; intro x hx
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx⟩
      exact ih u hst fuel hV (h_cont u) x hx
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exact False.elim (h_abs rfl)
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          dsimp only [fullImpl]; intro x hx
          rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
          rcases hx with ⟨y, hy, hx⟩
          have ⟨hVy, hRecy⟩ :=
            pqxdhKeyInd1KeyActiveShCrCachedImpl_validKeyIndEc_and_recvKemRecs
              embedTarget S P gq hst hV y hy
          have ⟨hVx, hRecx⟩ := ih y.1 y.2 f hVy (h_cont y.1) x hx
          exact ⟨hVx, by omega⟩

private theorem simulateQ_stepUntilShCrFuelKeyInd1KeyActivePrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx : Nat)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) (hst : KeyIndShCrState S) (fuel : Nat)
    (hV : ValidKeyIndEcC S P hst.base)
    (hb : IsQueryBoundP oa (fun q => isGameQuery q = true) fuel) :
    (Sum.map id (toPaused1KeyActive P) <$>
      simulateQ (primBaseImpl P) (stepUntilShCrFuelKeyInd1KeyActivePrim S sIdx oa hst fuel) =
      stepUntilShCr (pqxdhKeyInd1KeyActiveShCrCachedImpl true S P)
        (tryPauseKeyInd1KeyActiveQuery S P sIdx) oa hst) ∧
    (∀ res ∈ support (simulateQ (primBaseImpl P)
        (stepUntilShCrFuelKeyInd1KeyActivePrim S sIdx oa hst fuel)),
      match res with
      | Sum.inl done => done.2.recvKemRecs.length ≤ hst.recvKemRecs.length + fuel
      | Sum.inr d    => ValidPausedShCrData S P (hst.recvKemRecs.length + fuel) d) := by
  induction oa using OracleComp.inductionOn generalizing hst fuel with
  | pure b' =>
    refine ⟨by simp [stepUntilShCrFuelKeyInd1KeyActivePrim, stepUntilShCr], fun res hres => ?_⟩
    simp only [stepUntilShCrFuelKeyInd1KeyActivePrim, OracleComp.construct_pure, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hres
    subst hres; exact Nat.le_add_right _ _
  | query_bind q oa ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    cases q with
    | inl uq =>
      rcases hb with ⟨_, h_cont⟩
      simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at h_cont
      refine ⟨?_, fun res hres => ?_⟩
      · rw [stepUntilShCr_query_inl]
        simp only [stepUntilShCrFuelKeyInd1KeyActivePrim, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, map_bind]
        exact bind_congr (fun u => (ih u hst fuel hV (h_cont u)).1)
      · simp only [stepUntilShCrFuelKeyInd1KeyActivePrim, OracleComp.construct_query_bind,
          simulateQ_bind, simulateQ_embedUnif, MonadAttach.mem_support_bind] at hres
        rcases hres with ⟨u, _, hres⟩
        exact (ih u hst fuel hV (h_cont u)).2 res hres
    | inr gq =>
      rcases hb with ⟨h_abs | h_pos, h_cont⟩
      · exact False.elim (h_abs rfl)
      · cases fuel with
        | zero => omega
        | succ f =>
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          have h_try := simulateQ_tryPauseKeyIndQueryPrim S P sIdx gq oa hst hV
          have h_map := map_toPaused1KeyActive_tryPauseKeyIndQueryData S P sIdx gq oa hst
          refine ⟨?_, fun res hres => ?_⟩
          · rw [stepUntilShCr_query_inr]
            simp only [stepUntilShCrFuelKeyInd1KeyActivePrim, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind, ← h_map]
            cases h_d : tryPauseKeyIndQueryData S P sIdx gq oa hst with
            | some d => simp [simulateQ_pure]
            | none =>
              simp only [Option.map_none, simulateQ_bind,
                simulateQ_pqxdhKeyIndShCrActivePrimImpl1Key true S P hP gq hst hV, map_bind]
              refine bind_congr_of_support
                ((pqxdhKeyInd1KeyActiveShCrCachedImpl true S P gq).run hst) _ _ (fun x hx => ?_)
              exact (ih x.1 x.2 f
                (pqxdhKeyInd1KeyActiveShCrCachedImpl_validKeyIndEc_and_recvKemRecs
                  true S P gq hst hV x hx).1 (h_cont x.1)).1
          · simp only [stepUntilShCrFuelKeyInd1KeyActivePrim, OracleComp.construct_query_bind,
              simulateQ_bind, h_try, pure_bind] at hres
            cases h_d : tryPauseKeyIndQueryData S P sIdx gq oa hst with
            | some d =>
              rw [h_d] at hres
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hres
              subst hres
              rcases tryPauseKeyIndQueryData_some_props S P sIdx gq oa hst d h_d with
                ⟨h_hst, h_sid, h_fresh, h_cb⟩
              exact ⟨h_hst ▸ hV, h_sid, h_fresh, f, by rw [h_hst]; omega, h_cb f h_cont⟩
            | none =>
              rw [h_d] at hres
              simp only [simulateQ_bind,
                simulateQ_pqxdhKeyIndShCrActivePrimImpl1Key true S P hP gq hst hV,
                MonadAttach.mem_support_bind] at hres
              rcases hres with ⟨x, hx, hres⟩
              have ⟨hVx, hRecx⟩ :=
                pqxdhKeyInd1KeyActiveShCrCachedImpl_validKeyIndEc_and_recvKemRecs
                  true S P gq hst hV x hx
              have h_ih := (ih x.1 x.2 f hVx (h_cont x.1)).2 res hres
              cases res with
              | inl done => omega
              | inr d =>
                rcases h_ih with ⟨hVd, hSid, hFresh, f', hf', hCont⟩
                exact ⟨hVd, hSid, hFresh, f', by omega, hCont⟩

private theorem simulateQ_resumePausedKeyInd1KeyActivePrim (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (N : Nat) (d : PausedShCrData S) (ss kemCt : Bytes)
    (hValid : ValidPausedShCrData S P N d) :
    simulateQ (primBaseImpl P) (resumePausedKeyInd1KeyActivePrim S N d ss kemCt) =
      (toPaused1KeyActive P d).resume ss kemCt ∧
    (∀ z ∈ support ((toPaused1KeyActive P d).resume ss kemCt), z.2.recvKemRecs.length ≤ N) := by
  rcases hValid with ⟨hVd, hSid, hFresh, f, hf_le, hCont⟩
  have hf_N : f ≤ N := by omega
  refine ⟨?_, fun z hz => ?_⟩
  · unfold resumePausedKeyInd1KeyActivePrim toPaused1KeyActive; dsimp only
    rw [simulateQ_bind, simulateQ_postKemKeyIndPrim S P d.sid d.bundle d.uEntry d.hst ss kemCt hVd]
    refine bind_congr_of_support
      (postKem2 d.sid d.bundle d.uEntry (finishKeyIndBase S P d.sid d.bundle) d.hst ss kemCt) _ _
      (fun y hy => ?_)
    have hVy := (postKem2_validKeyIndEc_and_recvKemRecs S P d.sid hSid d.bundle d.uEntry d.hst
      ss kemCt hVd hFresh y hy).1
    exact simulateQ_runWithFuelKeyInd1KeyActiveShCrPrim S P hP (d.cont y.1) y.2 N hVy
      ((hCont y.1).mono hf_N)
  · unfold toPaused1KeyActive at hz; dsimp only at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨y, hy, hz⟩
    have ⟨hVy, hRecy⟩ := postKem2_validKeyIndEc_and_recvKemRecs S P d.sid hSid d.bundle d.uEntry
      d.hst ss kemCt hVd hFresh y hy
    have ⟨_, hRecz⟩ := simulateQ_pqxdhKeyInd1KeyActiveShCrCachedImpl_validKeyIndEc_and_recvKemRecs
      true S P (d.cont y.1) y.2 f hVy (hCont y.1) z hz
    rw [hRecy] at hRecz; omega

private theorem kemShCrExp_shcrReductionKeyInd1KeyActiveAt_eq (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget) (spkOrd sIdx : Nat)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    kemShCrExp P (shcrReductionKeyInd1KeyActiveAt (some spkOrd) sIdx S b A) =
      kemShCrExpProb P (shcrChoosePkKeyInd1KeyActiveAt S P spkOrd sIdx A.1) := by
  unfold kemShCrExp shcrReductionKeyInd1KeyActiveAt kemShCrExpProb shcrChoosePkKeyInd1KeyActiveAt
    shcrChoosePkGenericAt choosePkKeyInd1KeyActivePrimAt findCollisionKeyInd1KeyActivePrim
  dsimp only
  congr 1; ext ⟨pk, sk⟩
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_embedUnif, bind_assoc, pure_bind]
  refine bind_congr (fun secb => ?_)
  let initSt : KeyIndShCrState S :=
    { base := KeyIndState.empty S secb, targetBIdx? := some spkOrd, targetPk := pk, targetSk := sk }
  have hV0 : ValidKeyIndEcC S P initSt.base :=
    ⟨validEcLists_nil S, (fun _ h => False.elim (List.not_mem_nil h)), validKeyIndResp_empty S secb⟩
  have ⟨hSimStep, hSupStep⟩ := simulateQ_stepUntilShCrFuelKeyInd1KeyActivePrim S P hP sIdx
    A.1.run initSt b.q_total hV0 A.2.2.2.2.1
  have h_rec0 : initSt.recvKemRecs.length + b.q_total = b.q_total := by
    change ([] : List RecvKemRecord).length + b.q_total = b.q_total; simp
  rw [← hSimStep, bind_map_left]
  refine bind_congr_of_support
    (simulateQ (primBaseImpl P)
      (stepUntilShCrFuelKeyInd1KeyActivePrim S sIdx A.1.run initSt b.q_total))
    _ _ (fun res hres => ?_)
  have hValidRes := hSupStep res hres; rw [h_rec0] at hValidRes
  cases res with
  | inl done =>
    dsimp only [Sum.map, Sum.elim, Function.comp_def, id] at hValidRes ⊢
    congr 1; ext r
    cases hEnc : P.kemEncaps pk r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩; dsimp only
      rw [pure_bind, simulateQ_extractCollidingKemCtPrim b.q_total P pk sk pk ct ss
        done.2.recvKemRecs hValidRes, pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc
  | inr d =>
    dsimp only [Sum.map, Sum.elim, Function.comp_def] at hValidRes ⊢
    simp only [toPaused1KeyActive_bundle]
    congr 1; ext r
    cases hEnc : P.kemEncaps d.bundle.pqspkB r with
    | none => rfl
    | some sc =>
      rcases sc with ⟨ss, ct⟩; dsimp only
      rcases simulateQ_resumePausedKeyInd1KeyActivePrim S P hP b.q_total d ss ct hValidRes with
        ⟨hSimRes, hSupRes⟩
      rw [simulateQ_bind, hSimRes, bind_assoc, bind_assoc]
      refine bind_congr_of_support ((toPaused1KeyActive P d).resume ss ct) _ _ (fun z hz => ?_)
      rw [simulateQ_extractCollidingKemCtPrim b.q_total P pk sk d.bundle.pqspkB ct ss
        z.2.recvKemRecs (hSupRes z hz), pure_bind]
      exact kemShCrWin_pure_eq_of_cwf P hP hEnc

private theorem sum_range_mul_div_mod (n m : Nat) (hm : 0 < m) (f : Nat → Nat → ℝ) :
    (∑ idx ∈ Finset.range (n * m), f (idx / m) (idx % m)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f i j := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1; refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj_lt : j < m := Finset.mem_range.mp hj
    rw [Nat.add_comm (k * m) j, Nat.add_mul_div_right j k hm, Nat.div_eq_of_lt hj_lt,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj_lt]

/-- Double-sum decomposition of `shcrReductionKeyInd1KeyActive` into per-target
    `shcrReductionKeyInd1KeyActiveAt (some spkOrd) sIdx` reductions over active SPK and send
    creation ordinals. -/
theorem sum_kemShCr_shcrReductionKeyInd1KeyActiveAt_eq (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (∑ spkOrd ∈ Finset.range (activeSpkCount S b.q_on),
      ∑ sIdx ∈ Finset.range (activeSendCount S b.q_on),
        KemShCrReal P (shcrReductionKeyInd1KeyActiveAt (some spkOrd) sIdx S b A)) =
    ((activeSpkCount S b.q_on * activeSendCount S b.q_on : Nat) : ℝ) *
      KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) := by
  let n_spk := activeSpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  by_cases h0 : n_spk * n_send = 0
  · rcases Nat.mul_eq_zero.mp h0 with h | h <;> simp [n_spk, n_send, h]
  · have hm : 0 < n_send := Nat.pos_of_ne_zero (right_ne_zero_of_mul h0)
    have hSwap :
        𝒟[kemShCrExp P (shcrReductionKeyInd1KeyActive S b A)] =
        𝒟[sampleIndexRange (n_spk * n_send) >>= fun idx =>
          kemShCrExp P
            (shcrReductionKeyInd1KeyActiveAt (some (idx / n_send)) (idx % n_send) S b A)] := by
      unfold kemShCrExp shcrReductionKeyInd1KeyActive shcrReductionKeyInd1KeyActiveCore
        shcrReductionKeyInd1KeyActiveAt
      dsimp only
      simp only [n_spk, n_send] at h0
      simp only [h0, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif, bind_assoc]
      rw [OracleComp.evalDist_bind_bind_swap]
    have hMul :
        ((n_spk * n_send : Nat) : ℝ) * KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) =
        ∑ idx ∈ Finset.range (n_spk * n_send),
          KemShCrReal P
            (shcrReductionKeyInd1KeyActiveAt (some (idx / n_send)) (idx % n_send) S b A) := by
      unfold KemShCrReal KemShCr
      rw [hSwap]
      exact mul_toReal_sampleIndexRange_bind_eq_sum (n_spk * n_send)
        (fun idx => kemShCrExp P
          (shcrReductionKeyInd1KeyActiveAt (some (idx / n_send)) (idx % n_send) S b A))
    rw [hMul]
    exact (sum_range_mul_div_mod (activeSpkCount S b.q_on) (activeSendCount S b.q_on) hm _).symm

private def ShCrOnlineInv {S : Setup} (P : Primitives) (hst : KeyIndShCrState S) : Prop :=
  ValidKeyIndEcC S P hst.base ∧
  (∀ i ∈ hst.initKemRecs, i.sendIdx < hst.sendCount) ∧
  (∀ r ∈ hst.recvKemRecs, ∃ p ∈ hst.base.spkBundles,
    r.pqspkPk = p.2.pqspkPk ∧ r.pqspkSk = p.2.pqspkSk)

private theorem spkBundles_mem_of_step {bs bs' : List ((Nat × Nat) × SpkBundleEntry)}
    (hStep : SpkBundlesNoGenStep bs bs' ∨ ∃ e, bs' = e :: bs) :
    ∀ p ∈ bs, ∃ p' ∈ bs', p'.2.pqspkPk = p.2.pqspkPk ∧ p'.2.pqspkSk = p.2.pqspkSk := by
  intro p hp
  rcases hStep with (rfl | ⟨u, j, rfl⟩) | ⟨e, rfl⟩
  · exact ⟨p, hp, rfl, rfl⟩
  · refine ⟨_, List.mem_map_of_mem hp, ?_⟩
    rcases p with ⟨idx, b⟩; dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩
  · exact ⟨p, List.mem_cons_of_mem e hp, rfl, rfl⟩

private theorem pqxdhKeyInd1KeyShCrCachedImpl_false_onlineStep (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndShCrState S) (hInv : ShCrOnlineInv P hst) :
    let d := if isKeyIndOnlineQuery (.inr q) then 1 else 0
    ∀ x ∈ support ((pqxdhKeyInd1KeyShCrCachedImpl false S P q).run hst),
      ShCrOnlineInv P x.2 ∧
      x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + d ∧
      x.2.sendCount ≤ hst.sendCount + d := by
  intro d x hx
  rcases hInv with ⟨hV, hInitLt, hRecv⟩
  have hVx :=
    (pqxdhKeyInd1KeyShCrCachedImpl_validKeyIndEc_and_recvKemRecs false S P q hst hV x hx).1
  have hBStepFull := pqxdhKeyInd1KeyShCrCachedImpl_false_spkBundles_step S P q hst x hx
  have hBMono := spkBundles_mem_of_step hBStepFull.1
  have hBLen : x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + d := by
    by_cases hOn : isKeyIndOnlineQuery (.inr q)
    · have hd : d = 1 := by simp [d, hOn]
      rcases hBStepFull.1 with (heq | ⟨_, _, heq⟩) | ⟨_, heq⟩ <;> simp [heq, hd]
    · have hNoGen : ∀ u j, q ≠ .genSPK u j := by
        rintro u j rfl; exact hOn trivial
      rcases hBStepFull.2 hNoGen with heq | ⟨_, _, heq⟩ <;> simp [heq]
  suffices hMid : x.2.sendCount ≤ hst.sendCount + d ∧
      (∀ i ∈ x.2.initKemRecs, i.sendIdx < x.2.sendCount) ∧
      (∀ r ∈ x.2.recvKemRecs, r ∈ hst.recvKemRecs ∨
        ∃ p ∈ x.2.base.spkBundles, r.pqspkPk = p.2.pqspkPk ∧ r.pqspkSk = p.2.pqspkSk) by
    refine ⟨⟨hVx, hMid.2.1, fun r hr => ?_⟩, hBLen, hMid.1⟩
    rcases hMid.2.2 r hr with hr_old | hnew
    · rcases hRecv r hr_old with ⟨p, hp, hpk, hsk⟩
      rcases hBMono p hp with ⟨p', hp', hpk', hsk'⟩
      exact ⟨p', hp', hpk.trans hpk'.symm, hsk.trans hsk'.symm⟩
    · exact hnew
  have hLiftBase : ∀ {R : Type} (m : StateT (KeyIndState S) ProbComp R)
      (w : R × KeyIndShCrState S) (_ : w ∈ support ((liftShCrBase m).run hst)),
      w.2.sendCount ≤ hst.sendCount + d ∧
      (∀ i ∈ w.2.initKemRecs, i.sendIdx < w.2.sendCount) ∧
      (∀ r ∈ w.2.recvKemRecs, r ∈ hst.recvKemRecs ∨
        ∃ p ∈ w.2.base.spkBundles, r.pqspkPk = p.2.pqspkPk ∧ r.pqspkSk = p.2.pqspkSk) := by
    intro R m w hw
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hw
    rcases hw with ⟨_, _, rfl⟩
    exact ⟨Nat.le_add_right _ _, hInitLt, fun r hr => Or.inl hr⟩
  have hInitCase : ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
      (hd1 : d = 1) (w : KeyIndResponse × KeyIndShCrState S)
      (_ : w ∈ support ((runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
        (preCheckKeyInd S P sid u bundle) sid bundle (finishKeyIndBase S P sid bundle)).run hst)),
      w.2.sendCount ≤ hst.sendCount + d ∧
      (∀ i ∈ w.2.initKemRecs, i.sendIdx < w.2.sendCount) ∧
      (∀ r ∈ w.2.recvKemRecs, r ∈ hst.recvKemRecs ∨
        ∃ p ∈ w.2.base.spkBundles, r.pqspkPk = p.2.pqspkPk ∧ r.pqspkSk = p.2.pqspkSk) := by
    intro sid u bundle hd1 w hw
    rcases mem_support_runShCrInitiate2 P KeyIndState.principals KeyIndResponse.noneResp
      (preCheckKeyInd S P sid u bundle) sid bundle (finishKeyIndBase S P sid bundle) hst w hw with
      ⟨rfl, _⟩ | ⟨_, _, _, rfl | ⟨_, ss, kemCt, out, _, rfl⟩⟩
    · exact ⟨Nat.le_add_right _ _, hInitLt, fun r hr => Or.inl hr⟩
    · exact ⟨by dsimp only; omega, fun i hi => Nat.lt_succ_of_lt (hInitLt i hi),
        fun r hr => Or.inl hr⟩
    · rcases applyShCrFinish_send sid bundle.pqspkB ss kemCt hst out with ⟨hS, hI⟩
      have hR : (applyShCrFinish sid bundle.pqspkB ss kemCt hst out).2.recvKemRecs =
          hst.recvKemRecs := by unfold applyShCrFinish; cases out.2 <;> rfl
      refine ⟨by omega, fun i hi => ?_, fun r hr => Or.inl (hR ▸ hr)⟩
      rcases hI i hi with hi0 | ⟨hidx, _⟩
      · have := hInitLt i hi0; omega
      · omega
  have hAcceptCase : ∀ (baseAccept : StateT (KeyIndState S) ProbComp KeyIndResponse)
      (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
      (w : KeyIndResponse × KeyIndShCrState S)
      (_ : w ∈ support ((runShCrAcceptGeneric P KeyIndState.spkBundles isNoneKeyIndResp
        baseAccept k j hdr).run hst)),
      w.2.sendCount ≤ hst.sendCount + d ∧
      (∀ i ∈ w.2.initKemRecs, i.sendIdx < w.2.sendCount) ∧
      (∀ r ∈ w.2.recvKemRecs, r ∈ hst.recvKemRecs ∨
        ∃ p ∈ w.2.base.spkBundles, r.pqspkPk = p.2.pqspkPk ∧ r.pqspkSk = p.2.pqspkSk) := by
    intro baseAccept k j hdr w hw
    simp only [runShCrAcceptGeneric, StateT.run_bind, MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨y, hy, hw⟩
    simp only [liftShCrBase, StateT.run, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hy
    rcases hy with ⟨z, _, rfl⟩
    rcases mem_support_recordAcceptKemGeneric P KeyIndState.spkBundles isNoneKeyIndResp k j hdr
      z.1 { hst with base := z.2 } w hw with rfl | ⟨idxPair, bEntry, _, hfind, _, rfl⟩
    · exact ⟨Nat.le_add_right _ _, hInitLt, fun r hr => Or.inl hr⟩
    · refine ⟨Nat.le_add_right _ _, hInitLt, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr_old
      · exact Or.inr ⟨(idxPair, bEntry), List.mem_of_find?_eq_some hfind, rfl, rfl⟩
      · exact Or.inl hr_old
  revert hx
  cases q
  case initPrin u => exact hLiftBase _ x
  case genSPK u j => exact hLiftBase _ x
  case initiateOPK u i bundle =>
    intro hx; dsimp only [pqxdhKeyInd1KeyShCrCachedImpl, pqxdhKeyIndShCrCachedImpl] at hx
    cases hopk : bundle.opkB?.isNone
    · simp only [hopk, Bool.false_eq_true, ↓reduceIte] at hx
      exact hInitCase (.sendOPK u i) u bundle rfl x hx
    · simp only [hopk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨Nat.le_add_right _ _, hInitLt, fun r hr => Or.inl hr⟩
  case initiateNoOPK u i bundle =>
    intro hx; dsimp only [pqxdhKeyInd1KeyShCrCachedImpl, pqxdhKeyIndShCrCachedImpl] at hx
    cases hopk : bundle.opkB?.isSome
    · simp only [hopk, Bool.false_eq_true, ↓reduceIte] at hx
      exact hInitCase (.sendNoOPK u i) u bundle rfl x hx
    · simp only [hopk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨Nat.le_add_right _ _, hInitLt, fun r hr => Or.inl hr⟩
  case acceptOPK k j o hdr => exact hAcceptCase _ k j hdr x
  case acceptNoOPK k j l hdr => exact hAcceptCase _ k j hdr x
  all_goals exact hLiftBase _ x

private theorem simulateQ_false_onlineInv {α : Type} (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndShCrState S) (n : Nat)
    (hInv : ShCrOnlineInv P hst) (hOn : oa.IsQueryBoundP isKeyIndOnlineQuery n) :
    let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrCachedImpl false S P
    ∀ x ∈ support ((simulateQ fullFalse oa).run hst),
      ShCrOnlineInv P x.2 ∧
      x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + n ∧
      x.2.sendCount ≤ hst.sendCount + n := by
  intro fullFalse
  induction oa using OracleComp.inductionOn generalizing hst n with
  | pure a =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨hInv, Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  | query_bind t k ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hOn
    rcases hOn with ⟨hCan, hCont⟩
    cases t with
    | inl uq =>
      intro x hx; dsimp only [fullFalse] at hx
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx⟩
      have hFalse : ¬ isKeyIndOnlineQuery (S := S) (.inl uq) := id
      have hContU := hCont u; simp only [hFalse, ↓reduceIte] at hContU
      exact ih u hst n hInv hContU x hx
    | inr gq =>
      intro x hx; dsimp only [fullFalse] at hx
      rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨y, hy, hx⟩
      rcases pqxdhKeyInd1KeyShCrCachedImpl_false_onlineStep S P gq hst hInv y hy with
        ⟨hInvy, hBy, hSy⟩
      by_cases hq : isKeyIndOnlineQuery (.inr gq)
      · have hn : 0 < n := hCan.resolve_left (not_not.mpr hq)
        have hContY := hCont y.1; simp only [hq, ↓reduceIte] at hBy hSy hContY
        rcases ih y.1 y.2 (n - 1) hInvy hContY x hx with ⟨hInvx, hBx, hSx⟩
        exact ⟨hInvx, by omega, by omega⟩
      · have hContY := hCont y.1; simp only [hq, ↓reduceIte] at hBy hSy hContY
        rcases ih y.1 y.2 n hInvy hContY x hx with ⟨hInvx, hBx, hSx⟩
        exact ⟨hInvx, by omega, by omega⟩

private theorem hasBadKemShCrRecords_imp_active_any (S : Setup) (P : Primitives) (q_on : Nat)
    (hst : KeyIndShCrState S) (hInv : ShCrOnlineInv P hst)
    (hBLen : hst.base.spkBundles.length ≤ q_on) (hSLen : hst.sendCount ≤ q_on)
    (hBad : hasBadKemShCrRecords S P hst.initKemRecs hst.recvKemRecs = true) :
    let n_spk := activeSpkCount S q_on
    let n_send := activeSendCount S q_on
    (List.range (n_spk * n_send)).any (fun idx =>
      hasBadKemShCrActiveAt P (idx / n_send) (idx % n_send) hst) = true := by
  intro n_spk n_send
  rcases hInv with ⟨hV, hInitLt, hRecv⟩
  have hBStat : hst.base.spkBundles.length ≤ S.N_spk_tot :=
    validSpkBundles_length_le S hV.1.2.1
  unfold hasBadKemShCrRecords hasBadKemShCrRecordsAt at hBad
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hBad
  rcases hBad with ⟨idx_stat, hlt_stat, i, hi_mem, hi_mod, r, hr_mem, _, hpair⟩
  have hSendPos : 0 < S.N_send_tot :=
    Nat.pos_of_ne_zero (fun h => by simp [h] at hlt_stat)
  have hi_stat : i.sendIdx < S.N_send_tot := hi_mod ▸ Nat.mod_lt idx_stat hSendPos
  have hi_on : i.sendIdx < q_on := Nat.lt_of_lt_of_le (hInitLt i hi_mem) hSLen
  have hi_act : i.sendIdx < n_send := Nat.lt_min.mpr ⟨hi_on, hi_stat⟩
  have hm : 0 < n_send := Nat.lt_of_le_of_lt (Nat.zero_le _) hi_act
  rcases hRecv r hr_mem with ⟨p, hp, hr_pk, hr_sk⟩
  have hp_rev : p ∈ hst.base.spkBundles.reverse := List.mem_reverse.mpr hp
  rcases List.mem_iff_getElem.mp hp_rev with ⟨spkOrd, hOrd, hGet⟩
  have hOrd_len : spkOrd < hst.base.spkBundles.length := by simpa using hOrd
  have hOrd_act : spkOrd < n_spk :=
    Nat.lt_min.mpr ⟨Nat.lt_of_lt_of_le hOrd_len hBLen, Nat.lt_of_lt_of_le hOrd_len hBStat⟩
  have hIdxLt : spkOrd * n_send + i.sendIdx < n_spk * n_send := by
    have hMulLe : (spkOrd + 1) * n_send ≤ n_spk * n_send :=
      Nat.mul_le_mul_right n_send hOrd_act
    rw [Nat.add_one_mul] at hMulLe
    omega
  rw [List.any_eq_true]
  refine ⟨spkOrd * n_send + i.sendIdx, List.mem_range.mpr hIdxLt, ?_⟩
  rw [Nat.add_comm (spkOrd * n_send) i.sendIdx, Nat.add_mul_div_right i.sendIdx spkOrd hm,
    Nat.div_eq_of_lt hi_act, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi_act]
  unfold hasBadKemShCrActiveAt
  rw [List.getElem?_eq_getElem hOrd, hGet]
  rcases p with ⟨kj, bEntry⟩; dsimp only at hr_pk hr_sk ⊢
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨i, hi_mem, rfl, r, hr_mem, ⟨hr_pk, hr_sk⟩, hpair⟩

private theorem badKemShCrProbKeyInd1Key_le_active_sum (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    badKemShCrProbKeyInd1Key S P A.1 ≤
      ∑ spkOrd ∈ Finset.range (activeSpkCount S b.q_on),
        ∑ sIdx ∈ Finset.range (activeSendCount S b.q_on),
          badKemShCrActiveProbKeyInd1KeyAt S P spkOrd sIdx A.1 := by
  let n_spk := activeSpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let fullFalse := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndShCrState S) ProbComp) + pqxdhKeyInd1KeyShCrCachedImpl false S P
  let cachedRun : ProbComp (Bool × Bool × KeyIndShCrState S) :=
    $ᵗ Bool >>= fun secb =>
      (simulateQ fullFalse A.1.run).run { base := KeyIndState.empty S secb } >>=
        fun (b', finalHst) => pure (secb, b', finalHst)
  have hRunEq : ∀ (f : KeyIndShCrState S → Bool)
      (_ : ∀ h, f (cacheShCrAdvKeys S P h) = f h),
      (runKeyInd1KeyShCrSim S P A.1 >>= fun w => pure (f w.2.2)) =
      (cachedRun >>= fun w => pure (f w.2.2)) := by
    intro f hf
    unfold runKeyInd1KeyShCrSim cachedRun
    simp only [bind_assoc, pure_bind]
    refine bind_congr (fun secb => ?_)
    have hSim := CommutesRel.simulateQ_add_unif (cacheShCrAdvKeys S P)
      (pqxdhKeyInd1KeyShCrCachedImpl false S P) (pqxdhKeyInd1KeyShCrImpl false S P)
      (pqxdhKeyInd1KeyShCrCachedImpl_false_commutes_cache S P)
      A.1.run { base := KeyIndState.empty S secb }
    unfold CommutesRel at hSim
    have hInit : cacheShCrAdvKeys S P { base := KeyIndState.empty S secb } =
        { base := KeyIndState.empty S secb } := rfl
    rw [hInit] at hSim; rw [hSim, bind_map_left]
    exact bind_congr (fun x => by dsimp only [Prod.map, id]; rw [hf])
  have hLeAny : badKemShCrProbKeyInd1Key S P A.1 ≤
      (𝒟[runKeyInd1KeyShCrSim S P A.1 >>= fun (_, _, finalHst) =>
        pure ((List.range (n_spk * n_send)).any (fun idx =>
          hasBadKemShCrActiveAt P (idx / n_send) (idx % n_send) finalHst))] {true}).toReal := by
    unfold badKemShCrProbKeyInd1Key
    have hL : (runKeyInd1KeyShCrSim S P A.1 >>= fun (_, _, finalHst) =>
        pure (hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)) =
        (cachedRun >>= fun w =>
          pure (hasBadKemShCrRecords S P w.2.2.initKemRecs w.2.2.recvKemRecs)) :=
      hRunEq (fun finalHst => hasBadKemShCrRecords S P finalHst.initKemRecs finalHst.recvKemRecs)
        (fun _ => rfl)
    have hR : (runKeyInd1KeyShCrSim S P A.1 >>= fun (_, _, finalHst) =>
        pure ((List.range (n_spk * n_send)).any (fun idx =>
          hasBadKemShCrActiveAt P (idx / n_send) (idx % n_send) finalHst))) =
        (cachedRun >>= fun w =>
          pure ((List.range (n_spk * n_send)).any (fun idx =>
            hasBadKemShCrActiveAt P (idx / n_send) (idx % n_send) w.2.2))) :=
      hRunEq (fun finalHst => (List.range (n_spk * n_send)).any (fun idx =>
        hasBadKemShCrActiveAt P (idx / n_send) (idx % n_send) finalHst)) (fun _ => rfl)
    rw [hL, hR]
    refine toReal_bind_bool_mono_of_support cachedRun _ _ (fun w hw hBad => ?_)
    simp only [cachedRun, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hw
    rcases hw with ⟨secb, _, ⟨b', finalHst⟩, hx, rfl⟩
    have hInv0 : ShCrOnlineInv P ({ base := KeyIndState.empty S secb } : KeyIndShCrState S) :=
      ⟨⟨validEcLists_nil S, (fun _ h => False.elim (List.not_mem_nil h)),
        validKeyIndResp_empty S secb⟩,
       (fun _ h => False.elim (List.not_mem_nil h)),
       (fun _ h => False.elim (List.not_mem_nil h))⟩
    rcases simulateQ_false_onlineInv S P A.1.run { base := KeyIndState.empty S secb } b.q_on
      hInv0 A.2.2.2.2.2 (b', finalHst) hx with ⟨hInvF, hBF, hSF⟩
    exact hasBadKemShCrRecords_imp_active_any S P b.q_on finalHst hInvF
      (by simpa [KeyIndState.empty] using hBF) (by simpa using hSF) hBad
  have hSumFlat :
      (𝒟[runKeyInd1KeyShCrSim S P A.1 >>= fun (_, _, finalHst) =>
        pure ((List.range (n_spk * n_send)).any (fun idx =>
          hasBadKemShCrActiveAt P (idx / n_send) (idx % n_send) finalHst))] {true}).toReal ≤
      ∑ idx ∈ Finset.range (n_spk * n_send),
        badKemShCrActiveProbKeyInd1KeyAt S P (idx / n_send) (idx % n_send) A.1 :=
    toReal_any_range_le_sum (runKeyInd1KeyShCrSim S P A.1) (n_spk * n_send)
      (fun idx (_, _, finalHst) =>
        hasBadKemShCrActiveAt P (idx / n_send) (idx % n_send) finalHst)
  refine le_trans (le_trans hLeAny hSumFlat) ?_
  by_cases hm : 0 < n_send
  · exact le_of_eq (sum_range_mul_div_mod n_spk n_send hm
      (fun spkOrd sIdx => badKemShCrActiveProbKeyInd1KeyAt S P spkOrd sIdx A.1))
  · have hz : n_send = 0 := Nat.eq_zero_of_not_pos hm
    simp [n_spk, n_send, hz]

/-- Active creation-order union bound on `badKemShCrProbKeyInd1Key` via
    `shcrReductionKeyInd1KeyActive`. -/
theorem badKemShCrProbKeyInd1Key_le_kemShCr_active (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    badKemShCrProbKeyInd1Key S P A.1 ≤
      ((activeSpkCount S b.q_on * activeSendCount S b.q_on : Nat) : ℝ) *
        KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) := by
  calc badKemShCrProbKeyInd1Key S P A.1
      ≤ ∑ spkOrd ∈ Finset.range (activeSpkCount S b.q_on),
          ∑ sIdx ∈ Finset.range (activeSendCount S b.q_on),
            badKemShCrActiveProbKeyInd1KeyAt S P spkOrd sIdx A.1 :=
        badKemShCrProbKeyInd1Key_le_active_sum S P b A
    _ ≤ ∑ spkOrd ∈ Finset.range (activeSpkCount S b.q_on),
          ∑ sIdx ∈ Finset.range (activeSendCount S b.q_on),
            KemShCrReal P (shcrReductionKeyInd1KeyActiveAt (some spkOrd) sIdx S b A) := by
        refine Finset.sum_le_sum (fun spkOrd _ => Finset.sum_le_sum (fun sIdx _ => ?_))
        unfold KemShCrReal KemShCr
        rw [kemShCrExp_shcrReductionKeyInd1KeyActiveAt_eq S P hP b spkOrd sIdx A]
        exact badKemShCrActiveProbKeyInd1KeyAt_le_kemShCrProb S P spkOrd sIdx A.1
    _ = ((activeSpkCount S b.q_on * activeSendCount S b.q_on : Nat) : ℝ) *
          KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) :=
        sum_kemShCr_shcrReductionKeyInd1KeyActiveAt_eq S P b A

/-- Active creation-order Hop `G2_1 -> G3` bound via `shcrReductionKeyInd1KeyActive`. -/
theorem keyInd1Key_hop_G2_1_G3_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG2_1 S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
      ((activeSpkCount S b.q_on * activeSendCount S b.q_on : Nat) : ℝ) *
        KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) := by
  change |keyInd1KeyAdvG2_5 S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤ _
  rw [keyInd1KeyAdvG2_5_eq_ShCr S P A.1]
  exact (keyInd1Key_hop_badKemShCr_le_prob S P A.1).trans
    (badKemShCrProbKeyInd1Key_le_kemShCr_active S P hP b A)

theorem keyInd1Key_hop_G2_G3_active_of_G2_1 (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b)
    (hG2_G2_1 : |keyInd1KeyAdvG2 S P A.1 - keyInd1KeyAdvG2_1 S P A.1| ≤
      ((activeSpkCount S b.q_on * (activeSpkCount S b.q_on - 1) : Nat) : ℝ) / (2 : ℝ) ^ 256) :
    |keyInd1KeyAdvG2 S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
      (activeSpkCount S b.q_on : ℝ) * (activeSendCount S b.q_on : ℝ) *
        KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) +
      ((activeSpkCount S b.q_on * (activeSpkCount S b.q_on - 1) : Nat) : ℝ) / (2 : ℝ) ^ 256 := by
  have h2 := keyInd1Key_hop_G2_1_G3_active_le S P hP b A
  have hCast : ((activeSpkCount S b.q_on * activeSendCount S b.q_on : Nat) : ℝ) *
      KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) =
      (activeSpkCount S b.q_on : ℝ) * (activeSendCount S b.q_on : ℝ) *
        KemShCrReal P (shcrReductionKeyInd1KeyActive S b A) := by push_cast; ring
  rw [hCast] at h2
  have htri := abs_sub_le (keyInd1KeyAdvG2 S P A.1) (keyInd1KeyAdvG2_1 S P A.1)
    (keyInd1KeyAdvG3 S P A.1)
  set_option exponentiation.threshold 512 in
  linarith

/-! ## `KI1KeyActiveHopG0G3Stmt` combiners -/

theorem ki1KeyActiveHopG0G3_of_parts (S : Setup)
    (sigShallow sigDsl : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapSigEufCmaAdv)
    (shcrShallow shcrDsl : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → KemShCrAdv)
    (hG0G2 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        let n_id := activeIdCount S b.q_on
        let n_send := activeSendCount S b.q_on
        let n_dh := activeDhCount S b.q_on
        |keyInd1KeyAdvG0 S P A.1 - keyInd1KeyAdvG2 S P A.1| ≤
          (n_id : ℝ) * GapSigEufCmaReal P P.isValidDhTriple (sigShallow b A) +
          ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251)
    (hG2G3 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        let n_spk := activeSpkCount S b.q_on
        let n_send := activeSendCount S b.q_on
        |keyInd1KeyAdvG2 S P A.1 - keyInd1KeyAdvG3 S P A.1| ≤
          (n_spk : ℝ) * (n_send : ℝ) * KemShCrReal P (shcrShallow b A) +
          ((n_spk * (n_spk - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256)
    (hSigEq : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        GapSigEufCmaReal P P.isValidDhTriple (sigDsl b A) =
          GapSigEufCmaReal P P.isValidDhTriple (sigShallow b A))
    (hShcrEq : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        KemShCrReal P (shcrDsl b A) = KemShCrReal P (shcrShallow b A)) :
    KI1KeyActiveHopG0G3Stmt S sigDsl shcrDsl := by
  intro P hP b A
  dsimp only
  have h0_eq : keyInd1KeyAdvG0 S P A.1 = KeyInd1KeyRoAdvantageReal S P A.1 :=
    keyInd1KeyAdvG0_eq S P A.1
  have h02 := hG0G2 P hP b A
  have h23 := hG2G3 P hP b A
  dsimp only at h02 h23
  rw [h0_eq] at h02
  rw [hSigEq P hP b A, hShcrEq P hP b A]
  have htri := abs_sub_le (KeyInd1KeyRoAdvantageReal S P A.1) (keyInd1KeyAdvG2 S P A.1)
    (keyInd1KeyAdvG3 S P A.1)
  set_option exponentiation.threshold 512 in
  linarith

/-- Assembles `KI1KeyActiveHopG0G3Stmt` for `pqxdhKeyInd1KeyActiveCostedSims S` from the active
    collision bounds, the `G0_1 -> G2` signature hop, and the DSL advantage equalities. -/
theorem ki1KeyActiveHopG0G3_of_active_hops (S : Setup)
    (hG0_G0_1 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        let n_dh := activeDhCount S b.q_on
        let n_send := activeSendCount S b.q_on
        |keyInd1KeyAdvG0 S P A.1 - keyInd1KeyAdvG0_1 S P A.1| ≤
          ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : Nat) : ℝ) / (2 : ℝ) ^ 251)
    (hG0_1_G2 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        |keyInd1KeyAdvG0_1 S P A.1 - keyInd1KeyAdvG2 S P A.1| ≤
          (activeIdCount S b.q_on : ℝ) *
            GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A))
    (hG2_G2_1 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        let n_spk := activeSpkCount S b.q_on
        |keyInd1KeyAdvG2 S P A.1 - keyInd1KeyAdvG2_1 S P A.1| ≤
          ((n_spk * (n_spk - 1) : Nat) : ℝ) / (2 : ℝ) ^ 256)
    (hSigEq : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        GapSigEufCmaReal P P.isValidDhTriple ((pqxdhKeyInd1KeyActiveCostedSims S).eval.sig b A) =
          GapSigEufCmaReal P P.isValidDhTriple (sigReductionKeyInd1KeyActive S b A))
    (hShcrEq : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
        KemShCrReal P ((pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr b A) =
          KemShCrReal P (shcrReductionKeyInd1KeyActive S b A)) :
    KI1KeyActiveHopG0G3Stmt S (pqxdhKeyInd1KeyActiveCostedSims S).eval.sig
      (pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr := by
  refine ki1KeyActiveHopG0G3_of_parts S
    (sigReductionKeyInd1KeyActive S) (pqxdhKeyInd1KeyActiveCostedSims S).eval.sig
    (shcrReductionKeyInd1KeyActive S) (pqxdhKeyInd1KeyActiveCostedSims S).eval.shcr
    (fun P hP b A => ?_)
    (fun P hP b A => keyInd1Key_hop_G2_G3_active_of_G2_1 S P hP b A (hG2_G2_1 P hP b A))
    hSigEq hShcrEq
  dsimp only
  have h1 := hG0_G0_1 P hP b A
  have h2 := hG0_1_G2 P hP b A
  dsimp only at h1 h2
  have htri := abs_sub_le (keyInd1KeyAdvG0 S P A.1) (keyInd1KeyAdvG0_1 S P A.1)
    (keyInd1KeyAdvG2 S P A.1)
  set_option exponentiation.threshold 512 in
  linarith

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShcrHop
