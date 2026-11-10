/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.LibsignalCli.MainHaltedDefs
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
import Computational.Proofs.LibsignalCli.MainHaltedKeyInd
import Computational.Proofs.LibsignalCli.MainHaltedLazy1Key
import Computational.Proofs.LibsignalCli.MainHaltedPrefix
import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness
import Computational.Proofs.E2E.Dsl.CompositionHaltedReds
import Computational.Proofs.ReductionDsl.Soundness
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure

/-!
# Halted Multi-Session Composition Bound

Proves `exists_haltedCompositionRedsBound`, bridging the cost-bounded halted reduction family
witness `redsHalted` with the `KeyInd` coupling, lazy-vs-exact 1-key prefix equivalence, and
prefix hybrid telescope on `bhE2EExpWithKiSessionTracked`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.MainHaltedCompBound

open scoped ENNReal BigOperators
open OracleComp OracleSpec
open _root_.ReductionDsl (isGameQuery)
open CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey ShaCompress)
open CryptoGames.Ratchet.LibsignalInst (X25519RealizesDh dummyKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (BHModelInst Bytes CompositionCostedReductionFamily
  CompositionCostedReductionFamilyBounded MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds PEParams
  SampledSessionKey UnreachedPqxdhPrimitives bhTargetGameSpec configRefuseEarlyBobCorr
  keyIndReductionBudget modelPrims paramsIdsWithSpqr sessionSchemeFixedSpk stageOneAsProbComp)
open Computational.Proofs.LibsignalCli.MainHaltedDefs (TargetAdvPerInstanceBounded
  kemFailCoreTracker)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker
  bhClassifyTarget bhE2EDrvImplWithSessionTracked bhE2EExpWithKiSessionTracked
  bhE2EStepLocalSmSessionTracked bhPrefixRedWithSessionTracked gameRSessionTracked
  oracleImplRSessionTracked)
open Computational.Proofs.LibsignalCli.MainHaltedKeyInd (bhE2EDrvImplWithTracked
  bhE2EExpWithKiTracked bhE2EStepLocalSmTracked bhKindRedWithTracked
  boolBias_bhE2EExpWithKiTracked_1KeyReal_true_le)
open Computational.Proofs.LibsignalCli.MainHaltedLazy1Key
  (evalDist_bhPrefixLazyFullExpWithSessionTracked_1KeyReal_eq_bhPrefixExactFullExpWithSessionTracked)
open Computational.Proofs.LibsignalCli.MainHaltedPrefix
  (boolBias_bhE2EExpWithKiSessionTracked_false_le_sum_prefix_steps_of_lazyEq)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (initKemTrack)
open Computational.Proofs.E2E.Dsl.CompositionHaltedReds (kemFailSessionTracker kindRealExp_eq
  makesAtMostQueries prefixEval_eq redsHalted redsHalted_familyBounded)

/-! ## Tracker, query-budget, and shallow driver bridges -/

private theorem kemFailCoreTracker_eq_kemFailSessionTracker {ℓ : ℕ}
    (F : ShaCompress) (K : MlKem) :
    kemFailCoreTracker (St := GhostState Bytes) (Msg := Plain ℓ) (C := Bytes) F K =
      kemFailSessionTracker (ℓ := ℓ) F K := by
  unfold kemFailCoreTracker kemFailSessionTracker initKemTrack
  congr 1
  funext _ Q w res st
  have hpred :
      (fun wp : Bytes × Party => @BEq.beq Bytes instBEqOfDecidableEq wp.1 w && wp.2 == Q.other) =
      (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other) := by
    funext wp
    by_cases h : wp.1 = w
    · subst h; simp
    · have h1 : @BEq.beq Bytes instBEqOfDecidableEq wp.1 w = false := decide_eq_false h
      have h2 : (wp.1 == w) = false := beq_false_of_ne h
      rw [h1, h2]
  rw [hpred]
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted _ _ _ =>
      cases List.findIdx? (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other) st.2.reverse <;>
        rfl

private theorem isQueryBoundP_or_add_local {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p₁ p₂ p : ι → Prop} [DecidablePred p₁] [DecidablePred p₂] [DecidablePred p]
    (hsplit : ∀ t, p t → p₁ t ∨ p₂ t) {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h₁ : oa.IsQueryBoundP p₁ n₁) (h₂ : oa.IsQueryBoundP p₂ n₂) :
    oa.IsQueryBoundP p (n₁ + n₂) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂ ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp : p t
      · rcases hsplit t hp with hp1 | hp2
        · exact Or.inr (by have := h₁.1.resolve_left (not_not.mpr hp1); omega)
        · exact Or.inr (by have := h₂.1.resolve_left (not_not.mpr hp2); omega)
      · exact Or.inl hp
    · have k₁ := h₁.2 u
      have k₂ := h₂.2 u
      by_cases hp : p t
      · rcases hsplit t hp with hp1 | hp2
        · have _hpos := h₁.1.resolve_left (not_not.mpr hp1)
          simp only [hp1, ite_true] at k₁
          have k₂' : (mx u).IsQueryBoundP p₂ n₂ := k₂.mono (by split <;> omega)
          have := ih u k₁ k₂'
          simp only [hp, ite_true]
          exact this.mono (by omega)
        · have _hpos := h₂.1.resolve_left (not_not.mpr hp2)
          simp only [hp2, ite_true] at k₂
          have k₁' : (mx u).IsQueryBoundP p₁ n₁ := k₁.mono (by split <;> omega)
          have := ih u k₁' k₂
          simp only [hp, ite_true]
          exact this.mono (by omega)
      · simp only [hp, ite_false]
        exact (ih u (k₁.mono (by split <;> omega)) (k₂.mono (by split <;> omega))).mono le_rfl

private theorem isGameQuery_bound_of_targetAdvPerInstanceBounded {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool}
    {b : SignalPqxdh.QueryBudget} {qStart : ℕ} {qs : ℕ → ℕ}
    (hB : TargetAdvPerInstanceBounded B_A b qStart qs) :
    B_A.IsQueryBoundP (isGameQuery (G := bhTargetGameSpec S ℓ (BitVec 512)))
      (b.q_total + qStart + ∑ k ∈ Finset.range qStart, qs k) := by
  rcases hB with ⟨_, _, _, hTot, _, _, hStart, hDr, _⟩
  refine isQueryBoundP_or_add_local
    (p₁ := fun q =>
      bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true ∨
      bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    (p₂ := fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
    (fun q hq => by
      rcases q with n | ((kq | cq) | ⟨i, sq⟩)
      · exact absurd hq (by simp [isGameQuery])
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl)
    (isQueryBoundP_or_add_local (fun q hq => hq) hTot hStart) hDr

private theorem bhE2EStepLocalSmSessionTracked_eq_tracked_comp
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    bhE2EStepLocalSmSessionTracked (S := S) T C K qep decT encT =
      bhE2EStepLocalSmTracked T.init
        (fun d => oracleImplRSessionTracked T
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
            d.idA d.idB) ℓ d.spkCoins)
          (2 + 1) qep (configRefuseEarlyBobCorr decT encT)) := by
  funext σH i q
  unfold bhE2EStepLocalSmSessionTracked bhE2EStepLocalSmTracked
  rcases σH with ⟨σ, tracks⟩
  dsimp only
  split_ifs with hClean
  · rfl
  · cases σ.insts[i]? <;> cases σ.instMeta[i]? <;> rfl

private theorem bhE2EDrvImplWithSessionTracked_eq_tracked
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    bhE2EDrvImplWithSessionTracked T P ki C K qep decT encT =
      bhE2EDrvImplWithTracked T.init
        (fun d => oracleImplRSessionTracked T
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
            d.idA d.idB) ℓ d.spkCoins)
          (2 + 1) qep (configRefuseEarlyBobCorr decT encT))
        P ki C K := by
  funext q; ext σH
  unfold bhE2EDrvImplWithSessionTracked bhE2EDrvImplWithTracked
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · rfl
  · cases kq <;> rfl
  · rfl
  · simp only [StateT.run_bind, StateT.run_get, pure_bind,
      bhE2EStepLocalSmSessionTracked_eq_tracked_comp]

private theorem bhE2EExpWithKiSessionTracked_eq_tracked
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (secb : Bool) (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhE2EExpWithKiSessionTracked T secb S P ki C K qep decT encT B =
      bhE2EExpWithKiTracked T.init
        (fun d => oracleImplRSessionTracked T
          (sessionSchemeFixedSpk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K)
            d.idA d.idB) ℓ d.spkCoins)
          (2 + 1) qep (configRefuseEarlyBobCorr decT encT))
        secb P ki C K B := by
  unfold bhE2EExpWithKiSessionTracked bhE2EExpWithKiTracked
  rw [bhE2EDrvImplWithSessionTracked_eq_tracked]

/-! ## Shallow session-tracked advantage telescope -/

private theorem boolBias_bhE2EExpWithKiSessionTracked_1KeyReal_true_le_sum
    {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : TargetAdvPerInstanceBounded B_A b qStart qs) :
    let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qTot := b.q_total + qStart + qDR
    let smImpl := fun d : BHModelInst S ℓ =>
      oracleImplRSessionTracked T
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
    𝒟[bhE2EExpWithKiSessionTracked T true S P ki C K qep decT encT B_A].boolBias ≤
      2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P
            ⟨(bhKindRedWithTracked T.init smImpl P ki C K).eval (fun _ => B_A) ()⟩ +
        ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          𝒟[stageOneAsProbComp
              ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1
                (fun _ => B_A) () qTot false) >>=
            fun o =>
              Prod.fst <$> gameRSessionTracked T
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                  ℓ o.1.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2
                  o.2 flip qTot false)].boolBias := by
  intro ki qDR qTot smImpl
  have hHop1 :
      𝒟[bhE2EExpWithKiSessionTracked T true S P ki C K qep decT encT B_A].boolBias ≤
        2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P
              ⟨(bhKindRedWithTracked T.init smImpl P ki C K).eval (fun _ => B_A) ()⟩ +
          𝒟[bhE2EExpWithKiSessionTracked T false S P ki C K qep decT encT B_A].boolBias := by
    rw [bhE2EExpWithKiSessionTracked_eq_tracked T true,
      bhE2EExpWithKiSessionTracked_eq_tracked T false]
    exact boolBias_bhE2EExpWithKiTracked_1KeyReal_true_le T.init smImpl P C K B_A
  have hStart :
      B_A.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
        qStart := hB.2.2.2.2.2.2.1
  have hHop2 :
      𝒟[bhE2EExpWithKiSessionTracked T false S P ki C K qep decT encT B_A].boolBias ≤
        ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          𝒟[stageOneAsProbComp
              ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval1
                (fun _ => B_A) () qTot false) >>=
            fun o =>
              Prod.fst <$> gameRSessionTracked T
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                  ℓ o.1.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                ((bhPrefixRedWithSessionTracked T P ki C K qep decT encT k).eval2
                  o.2 flip qTot false)].boolBias :=
    boolBias_bhE2EExpWithKiSessionTracked_false_le_sum_prefix_steps_of_lazyEq
      T S ki P C K qep decT encT qStart qTot B_A
      (fun k _ b_k =>
        evalDist_bhPrefixLazyFullExpWithSessionTracked_1KeyReal_eq_bhPrefixExactFullExpWithSessionTracked
          T S P C K qep decT encT k b_k B_A)
      hStart
      (isGameQuery_bound_of_targetAdvPerInstanceBounded hB)
  exact hHop1.trans (add_le_add le_rfl hHop2)

/-! ## Halted composition reductions bound -/

private theorem exists_haltedCompositionRedsBound_of_witness
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (T : ∀ (F : ShaCompress) (_K : MlKem),
        SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey
          (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack F Bytes))
    (hTrEq : ∀ (F : ShaCompress) (K : MlKem),
        kemFailCoreTracker (St := GhostState Bytes) (Msg := Plain ℓ) (C := Bytes) F K = T F K)
    (redsHalted : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S (Pt := Pt) ℓ P C K qep decT encT)
    (redsHalted_familyBounded : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamilyBounded P C K qep decT encT
          (redsHalted P C K qep decT encT))
    (makesAtMostQueries : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
        (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
        (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
        TargetAdvPerInstanceBounded B_A b qStart qs →
        let qDR := ∑ k ∈ Finset.range qStart, qs k
        let qInst := Finset.sup (Finset.range qStart) qs
        let qTot := b.q_total + qStart + qDR
        let Re := redsHalted P C K qep decT encT b qStart qDR qInst
        SignalPqxdh.QueryBounded
            (⟨Re.kindRed.eval (fun _ => B_A) ()⟩ : SignalPqxdh.KeyIndAdversary S)
            (keyIndReductionBudget S qStart b) ∧
          (∀ k < qStart,
            ∀ o ∈ support
              (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
            ∀ flip,
              CryptoGames.SM.MakesAtMostQueries
                ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)))
    (kindRealExp_eq : ∀ (P : SignalPqxdh.Primitives)
        (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        SignalPqxdh.WellFormedPrimitivesδ P →
        ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
          (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
        TargetAdvPerInstanceBounded B_A b qStart qs →
        SignalPqxdh.pqxdhKeyInd1KeyRealExp S P
            ⟨(redsHalted P C K qep decT encT b qStart
                (∑ k ∈ Finset.range qStart, qs k)
                (Finset.sup (Finset.range qStart) qs)).kindRed.eval (fun _ => B_A) ()⟩ =
          SignalPqxdh.pqxdhKeyInd1KeyRealExp S P
            ⟨(bhKindRedWithTracked (T C.F K).init
              (fun d : BHModelInst S ℓ =>
                oracleImplRSessionTracked (T C.F K)
                  (sessionSchemeFixedSpk
                    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                    ℓ d.spkCoins)
                  (2 + 1) qep (configRefuseEarlyBobCorr decT encT))
              P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K).eval (fun _ => B_A) ()⟩)
    (prefixEval_eq : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        SignalPqxdh.WellFormedPrimitivesδ P →
        ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
          (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool),
        TargetAdvPerInstanceBounded B_A b qStart qs →
        ∀ {k : ℕ}, k < qStart → ∀ (flip : Bool),
        let qDR := ∑ j ∈ Finset.range qStart, qs j
        let qInst := Finset.sup (Finset.range qStart) qs
        let qTot := b.q_total + qStart + qDR
        let Re := redsHalted P C K qep decT encT b qStart qDR qInst
        (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>= fun o =>
            Prod.fst <$> gameRSessionTracked (T C.F K)
              (sessionSchemeFixedSpk
                (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.1 o.1.2.1)
                ℓ o.1.2.2)
              (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
              ((Re.prefixRed k).eval2 o.2 flip qTot false)) =
          (stageOneAsProbComp
              ((bhPrefixRedWithSessionTracked (T C.F K)
                  P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT k).eval1
                (fun _ => B_A) () qTot false) >>=
            fun o =>
              Prod.fst <$> gameRSessionTracked (T C.F K)
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) o.1.idA o.1.idB)
                  ℓ o.1.spkCoins)
                (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                ((bhPrefixRedWithSessionTracked (T C.F K)
                    P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT k).eval2
                  o.2 flip qTot false))) :
    ∃ (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT),
      (∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamilyBounded P C K qep decT encT (reds P C K qep decT encT)) ∧
      ∀ (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
        (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Wp.Q.K)
        (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X Wp))
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
        (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (_hDh : Dh.Commutes) (_hX : X25519RealizesDh Wp.C Dh encPt encT)
        (_hdec : ∀ T, decT (encT T) = some T)
        (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
        (_hD : ∀ k x, Wp.C.D k (Wp.C.E k x) = x)
        (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
        (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
        (_hB : TargetAdvPerInstanceBounded B_A b qStart qs),
        let P := modelPrims X Wp
        let spqr := spqrV1SessionUniformCoins Wp.C.F Wp.Q.K
        let qDR := ∑ k ∈ Finset.range qStart, qs k
        let qInst := Finset.sup (Finset.range qStart) qs
        let qTot := b.q_total + qStart + qDR
        let Re := reds P Wp.C Wp.Q.K qep decT encT b qStart qDR qInst
        let b_ki := keyIndReductionBudget S qStart b
        let advK : SignalPqxdh.KeyIndAdversary S := ⟨Re.kindRed.eval (fun _ => B_A) ()⟩
        let exp_H :=
          bhE2EExpWithKiSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K) true S P
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) Wp.C Wp.Q.K qep decT encT B_A
        SignalPqxdh.QueryBounded advK b_ki ∧
        (∀ k < qStart,
          ∀ o ∈ support (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
          ∀ flip,
          CryptoGames.SM.MakesAtMostQueries ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
        𝒟[exp_H].boolBias ≤
          2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P advK +
            ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
              𝒟[stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
                fun o =>
                  Prod.fst <$> gameRSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K)
                    (sessionSchemeFixedSpk (paramsIdsWithSpqr Wp.C spqr o.1.1 o.1.2.1) ℓ o.1.2.2)
                    (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                    ((Re.prefixRed k).eval2 o.2 flip qTot false)].boolBias := by
  refine ⟨redsHalted, redsHalted_familyBounded, ?_⟩
  intro X Wp _hK_tot hP _Dh _encPt encT decT qep _hℓ _hDh _hX _hdec _hdum _hz _hD
    b qStart qs B_A hB
  dsimp only
  obtain ⟨hQ_ki, hQ_sm⟩ := makesAtMostQueries (modelPrims X Wp) Wp.C Wp.Q.K qep
    decT encT b qStart qs B_A hB
  refine ⟨hQ_ki, hQ_sm, ?_⟩
  rw [hTrEq Wp.C.F Wp.Q.K]
  have hShallow := boolBias_bhE2EExpWithKiSessionTracked_1KeyReal_true_le_sum
    (T Wp.C.F Wp.Q.K)
    (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT b qStart qs B_A hB
  dsimp only at hShallow
  have hKindAdvEq :
      SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X Wp)
          ⟨(redsHalted (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT b qStart
              (∑ k ∈ Finset.range qStart, qs k)
              (Finset.sup (Finset.range qStart) qs)).kindRed.eval (fun _ => B_A) ()⟩ =
        SignalPqxdh.KeyInd1KeyRealAdvantage S (modelPrims X Wp)
          ⟨(bhKindRedWithTracked (T Wp.C.F Wp.Q.K).init
            (fun d => oracleImplRSessionTracked (T Wp.C.F Wp.Q.K)
              (sessionSchemeFixedSpk
                (paramsIdsWithSpqr Wp.C (spqrV1SessionUniformCoins Wp.C.F Wp.Q.K) d.idA d.idB)
                ℓ d.spkCoins)
              (2 + 1) qep (configRefuseEarlyBobCorr decT encT))
            (modelPrims X Wp) (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S (modelPrims X Wp))
            Wp.C Wp.Q.K).eval (fun _ => B_A) ()⟩ :=
    congrArg (fun x => 𝒟[x].boolBias)
      (kindRealExp_eq (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT
        hP.toWellFormedPrimitivesδ b qStart qs B_A hB)
  rw [← hKindAdvEq] at hShallow
  refine hShallow.trans (add_le_add le_rfl (Finset.sum_le_sum fun k hk => iSup_mono fun flip => ?_))
  apply le_of_eq
  congr 1
  congr 1
  exact (prefixEval_eq (modelPrims X Wp) Wp.C Wp.Q.K qep decT encT
    hP.toWellFormedPrimitivesδ b qStart qs B_A hB (Finset.mem_range.mp hk) flip).symm

/-- Cost-bounded halted composition reduction family `reds` satisfying `QueryBounded` and Stage-2
`MakesAtMostQueries` on any `TargetAdvPerInstanceBounded` target adversary `B_A`, telescoping
`𝒟[bhE2EExpWithKiSessionTracked (kemFailCoreTracker ...) true].boolBias` into `KeyInd` and
per-session prefix mixture terms. -/
theorem exists_haltedCompositionRedsBound
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    ∃ (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT),
      (∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamilyBounded P C K qep decT encT (reds P C K qep decT encT)) ∧
      ∀ (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
        (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Wp.Q.K)
        (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X Wp))
        (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
        (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (_hDh : Dh.Commutes) (_hX : X25519RealizesDh Wp.C Dh encPt encT)
        (_hdec : ∀ T, decT (encT T) = some T)
        (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
        (_hD : ∀ k x, Wp.C.D k (Wp.C.E k x) = x)
        (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
        (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
        (_hB : TargetAdvPerInstanceBounded B_A b qStart qs),
        let P := modelPrims X Wp
        let spqr := spqrV1SessionUniformCoins Wp.C.F Wp.Q.K
        let qDR := ∑ k ∈ Finset.range qStart, qs k
        let qInst := Finset.sup (Finset.range qStart) qs
        let qTot := b.q_total + qStart + qDR
        let Re := reds P Wp.C Wp.Q.K qep decT encT b qStart qDR qInst
        let b_ki := keyIndReductionBudget S qStart b
        let advK : SignalPqxdh.KeyIndAdversary S := ⟨Re.kindRed.eval (fun _ => B_A) ()⟩
        let exp_H :=
          bhE2EExpWithKiSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K) true S P
            (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) Wp.C Wp.Q.K qep decT encT B_A
        SignalPqxdh.QueryBounded advK b_ki ∧
        (∀ k < qStart,
          ∀ o ∈ support (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
          ∀ flip,
          CryptoGames.SM.MakesAtMostQueries ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
        𝒟[exp_H].boolBias ≤
          2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P advK +
            ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
              𝒟[stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false) >>=
                fun o =>
                  Prod.fst <$> gameRSessionTracked (kemFailCoreTracker Wp.C.F Wp.Q.K)
                    (sessionSchemeFixedSpk (paramsIdsWithSpqr Wp.C spqr o.1.1 o.1.2.1) ℓ o.1.2.2)
                    (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
                    ((Re.prefixRed k).eval2 o.2 flip qTot false)].boolBias := by
  exact exists_haltedCompositionRedsBound_of_witness (Pt := Pt) S ℓ
    (fun F K => kemFailSessionTracker (ℓ := ℓ) F K)
    (fun F K => kemFailCoreTracker_eq_kemFailSessionTracker F K)
    (redsHalted (Pt := Pt) S ℓ)
    (redsHalted_familyBounded (Pt := Pt) S ℓ)
    (makesAtMostQueries (Pt := Pt) S ℓ)
    (kindRealExp_eq (Pt := Pt) S ℓ)
    (prefixEval_eq (Pt := Pt) S ℓ)

end Computational.Proofs.LibsignalCli.MainHaltedCompBound
