/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.KeyInd1RealReds
public import Computational.Proofs.LibsignalCli.PrefixCouplingWithCore
import Computational.Proofs.LibsignalCli.PrefixCouplingWith
import ProofLib.BV.WidthNorm
import VCVio.EvalDist.Monad.Basic

/-!
# The model interface `Σ_model^H` and Lemma 3

**Checked by Lean.** Relates the generic composed game at `modelIface P ki C K qep decT encT` to
the model-state E2E experiment `bhE2EExpWithKi true` on `modelAdvRun A`, transfers query bounds
through `modelAdvRun`, and proves model security (`model_secure`, Lemma 3) for any handshake `ki`
admitting lazy session-key sampling.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E.Prefix CryptoVerification.E2E.Signed ReductionDsl

namespace CryptoVerification.E2E

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}

/-! ## Flattening two state layers -/

theorem flattenImpl_run_run {ι : Type} {spec : OracleSpec ι} {M : Type → Type} [Monad M]
    {D K : Type} (get : D → K) (set : D → K → D) (impl : QueryImpl spec (StateT D M))
    (q : spec.Domain) (d : D) (k : K) :
    ((flattenImpl get set impl q).run d).run k =
      (fun p => (p, get p.2)) <$> (impl q).run (set d k) := rfl

theorem run_run_simulateQ_flattenImpl {ι : Type} {spec : OracleSpec ι} {M : Type → Type} [Monad M]
    [LawfulMonad M] {D K α : Type} (get : D → K) (set : D → K → D)
    (hset : ∀ d, set d (get d) = d) (impl : QueryImpl spec (StateT D M))
    (oa : OracleComp spec α) (d : D) :
    ((simulateQ (flattenImpl get set impl) oa).run d).run (get d) =
      (fun p : α × D => ((p.1, p.2), get p.2)) <$> (simulateQ impl oa).run d := by
  induction oa using OracleComp.inductionOn generalizing d with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    rw [flattenImpl_run_run, hset, bind_map_left]
    exact bind_congr fun p => ih p.1 p.2

/-! ## Model interface and query bounds -/

/-- Query index map underlying `modelReassoc`. -/
def modelReassocQuery :
    (composedSpec S ℓ (GhostState Bytes)).Domain →
      (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain
  | .inl (.inl (.inl n)) => .inl n
  | .inl (.inl (.inr kq)) => .inr (.inl (.inl kq))
  | .inl (.inr cq) => .inr (.inl (.inr cq))
  | .inr dq => .inr (.inr dq)

theorem isQueryBoundP_modelReassoc
    (p : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop) [DecidablePred p]
    (t : (composedSpec S ℓ (GhostState Bytes)).Domain) :
    (modelReassoc (S := S) (ℓ := ℓ) t).IsQueryBoundP p
      (if p (modelReassocQuery t) then 1 else 0) := by
  rcases t with ((n | kq) | cq) | dq <;>
    simp only [modelReassoc, modelReassocQuery] <;>
    exact (isQueryBoundP_query_iff p _ _).mpr fun h => by simp [h]

/-- Transfers `IsQueryBoundP` along `modelReassocQuery` to `modelAdvRun A`. -/
theorem IsQueryBoundP.modelAdvRun
    {p : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop} [DecidablePred p]
    {A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool} {n : ℕ}
    (h : A.IsQueryBoundP (fun t => p (modelReassocQuery t)) n) :
    (modelAdvRun A).IsQueryBoundP p n :=
  OracleComp.IsQueryBoundP.simulateQ_of_step h
    (fun t ht => by simpa [ht] using isQueryBoundP_modelReassoc p t)
    (fun t ht => by simpa [ht] using isQueryBoundP_modelReassoc p t)

/-- Predicate selecting `startDR` control queries of `composedSpec`. -/
def modelIsStartQuery (t : (composedSpec S ℓ (GhostState Bytes)).Domain) : Prop :=
  bhClassifyTarget (S := S) (ℓ := ℓ) (PQC := BitVec 512) (fun _ => false) (fun _ => true)
    (fun _ => false) (modelReassocQuery t) = true

instance : DecidablePred (modelIsStartQuery (S := S) (ℓ := ℓ)) := fun t => by
  unfold modelIsStartQuery; infer_instance

/-- Predicate selecting all non-coin game queries of `composedSpec`. -/
def modelIsGameQuery (t : (composedSpec S ℓ (GhostState Bytes)).Domain) : Prop :=
  isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512)) (modelReassocQuery t)

instance : DecidablePred (modelIsGameQuery (S := S) (ℓ := ℓ)) := fun t => by
  unfold modelIsGameQuery; infer_instance

@[simp] theorem modelIsGameQuery_unif (n : ℕ) :
    ¬ modelIsGameQuery (S := S) (ℓ := ℓ) (.inl (.inl (.inl n))) := by
  simp [modelIsGameQuery, modelReassocQuery, isGameQuery]

/-- `composedExp` at `modelIface` equals `bhE2EExpWithKi true` on `modelAdvRun A`. -/
theorem composedExp_modelIface (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool) :
    composedExp (modelIface (ℓ := ℓ) P ki C K qep decT encT) A =
      bhE2EExpWithKi true S P ki C K ℓ qep decT encT (modelAdvRun A) := by
  unfold composedExp bhE2EExpWithKi modelAdvRun
  refine bind_congr fun b => ?_
  show (do
      let x ← ((simulateQ (flattenImpl (fun d : BHE2EDrvState S ℓ => d.st)
        (fun d st => { d with st := st }) (bhE2EDrvImplWith P ki C K qep decT encT) ∘ₛ
          modelReassoc) A).run { b := b, st := SignalPqxdh.KeyIndState.empty S true }).run
        (SignalPqxdh.KeyIndState.empty S true)
      if !allTestedSessionsFresh P x.2 then $ᵗ Bool else return (x.1.1 == b || bhE2EDrvWon x.1.2 b)) = _
  rw [QueryImpl.simulateQ_compose]
  have h := run_run_simulateQ_flattenImpl (fun d : BHE2EDrvState S ℓ => d.st)
    (fun d st => { d with st := st }) (fun _ => rfl) (bhE2EDrvImplWith P ki C K qep decT encT)
    (simulateQ modelReassoc A) { b := b, st := SignalPqxdh.KeyIndState.empty S true }
  erw [h]
  rw [bind_map_left]

/-! ## Lemma 3 -/

/-- Bounds `ComposedAdvantage (modelIface ... ki) A` by twice the `KeyInd` advantage of
`bhKindRedWith` plus the prefix-hybrid `SM.gameR` bias sum when `ki` admits lazy session-key
sampling. -/
theorem model_secure (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart qTot : ℕ) (A : OracleComp (composedSpec S ℓ (GhostState Bytes)) Bool)
    (hLazyEq : ∀ k < qStart, ∀ b_k,
      𝒟[Prefix1Key.bhPrefixLazyFullExpWith S ki P C K ℓ qep decT encT k b_k (modelAdvRun A)] =
        𝒟[Prefix1Key.bhPrefixExactFullExpWith S ki P C K ℓ qep decT encT k b_k (modelAdvRun A)])
    (hQStart : A.IsQueryBoundP modelIsStartQuery qStart)
    (hQTot : A.IsQueryBoundP modelIsGameQuery qTot) :
    ComposedAdvantage (modelIface (ℓ := ℓ) P ki C K qep decT encT) A ≤
      2 * KeyIndAdvantageForHandshake S P ki
            ⟨(bhKindRedWith (S := S) (ℓ := ℓ) P ki C K qep decT encT).eval
              (fun _ => modelAdvRun A) ()⟩ +
        ∑ k ∈ Finset.range qStart,
          ⨆ flip : Bool,
            𝒟[stageOneAsProbComp
                ((Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval1
                  (fun _ => modelAdvRun A) () qTot false) >>=
              fun o =>
                SM.gameR
                  (sessionSchemeFixedSpk
                    (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                    ℓ o.1.spkCoins)
                  (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                  ((Prefix1Key.bhPrefixRedWith S ℓ P ki C K qep decT encT k).eval2
                    o.2 flip qTot false)].boolBias := by
  unfold ComposedAdvantage
  rw [composedExp_modelIface]
  refine (boolBias_bhE2EExpWithKi_true_le S P ki C K ℓ qep decT encT (modelAdvRun A)).trans ?_
  gcongr
  have hExpEq : bhE2EExpWithKi false S P ki C K ℓ qep decT encT (modelAdvRun A) =
      Prefix1Key.bhE2EExpWithKi S ki false P C K ℓ qep decT encT (modelAdvRun A) := rfl
  rw [hExpEq]
  exact Prefix1Key.boolBias_bhE2EExpWithKi_false_le_sum_prefix_steps_of_lazyEq S ki P C K ℓ qep
    decT encT qStart qTot (modelAdvRun A) hLazyEq (IsQueryBoundP.modelAdvRun hQStart)
    (IsQueryBoundP.modelAdvRun hQTot)

end CryptoVerification.E2E
