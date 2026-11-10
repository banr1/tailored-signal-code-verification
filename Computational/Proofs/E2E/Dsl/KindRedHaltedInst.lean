/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.KindRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedEval -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedStartSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp -- proof-setup: allow-public-import

/-!
# Halted Multi-Session Handshake Reduction Instantiation

Connects `kindRedHalted` and `OneStageAtomicSimSpec` to `HaltedSimInv` and the handshake
subprograms from `HaltedStartSessionSim`, proving `GRedBounded`, `SignalPqxdh.QueryBounded`,
and `.eval` agreement with `bhKindRedWithTracked`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.KindRedHaltedInst

open scoped BigOperators
open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Env Expr Comp CostedReduction
  UniformSamplerTag AtomicBaseUnif E2EKeyIndTag bits
  atomicSig atomicE2EOps e2eKeyIndTargetIface
  BV256 FinT sidT sidV keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc smQT smQenc smRT GhostStT)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState maxForwardJumps)
open CryptoVerification.LibsignalSession (GRedBounded)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes BHE2EDrvState BHModelInst SampledSessionKey
  bhTargetGameSpec e2eTargetGameCodec bhTargetQenc bhTargetRdec bhClassifyTarget
  bhLiftP bhDrvKiQueryOk bhNoOpkRespPromoted bhE2EMirror bhE2EGuard bhE2EFinishStartSpk bhE2EDrvWon
  bhE2ECostBudget keyIndReductionBudget
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
  (SessionHaltTracker oracleImplRSessionTracked bhE2EStepLocalSmSessionTracked)
open Computational.Proofs.LibsignalCli.MainHaltedKeyInd (bhKindRedWithTracked)
open Computational.Proofs.E2E.Dsl.M3Interfaces
  (DrvMirrorBounded drvMetaAligned_mirror)
open Computational.Proofs.E2E.Dsl.KindRedHalted
  (HaltedKindSubprograms drvKindHaltedTy drvKindHaltedEnc
   mkAtomicTestSessionE mkAtomicRevealSpkSkE eval_mkAtomicTestSessionE eval_mkAtomicRevealSpkSkE
   kindStartStepHaltedC kindRedHalted
   haltedKindEndpointCost haltedKindStepCost haltedKindSizeBound
   kindRedHalted_size_le_budget kindRedHalted_gRedBounded
   sidOfV_sidV keyIndQdec_keyIndQenc
   kindHandleHalted_eval_ki kindHandleHalted_eval_ctl kindHandleHalted_eval_sm
   kindRedHalted_queryBounded
   bhE2EFinishStartSpkTracked bhKindHandleWithHalted bhKindRedWithHalted)
open Computational.Proofs.E2E.Dsl.KindRedHaltedEval
  (OneStageAtomicSimSpec oneStage_eval_eq
   packAtomicSmRespEnc atomicKindRespEnc
   atomicKeyIndTargetIface_liftP_eq_bhLiftP mem_support_of_bhLiftP)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness
  (kemFailSessionTracker HaltedTargetAdvPerInstanceBounded ValidSimTrackInv HaltedSimInv
   e2ePerStepWeightedFactor e2eFreshScanInnerFactor
   params_bits_le_budget totalCost_le_bhE2ECostBudget_of_step_endpoint
   haltedLinearStep_le_weightedFactor
   bhKindRedWithHalted_eq_bhKindRedWithTracked
   finishStartSpkTracked_preserves stepLocalSmSessionTracked_preserves)

/-! ## `KeyInd` mirroring invariant preservation -/

theorem kiSkip_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH)
    (hKiNext : qKiDone + 1 ≤ b.q_total) :
    HaltedSimInv TrackInv C K b qStart qDR (qKiDone + 1) qStartDone qDrDone σH where
  ki_le := hKiNext
  start_le := hInv.start_le
  dr_le := hInv.dr_le
  mirror := hInv.mirror.mono (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
    (Nat.le_succ _) (Nat.le_succ _) (le_refl _)
  metaAligned := hInv.metaAligned
  sessions := hInv.sessions
  kiReach := hInv.kiReach.mono (Nat.le_succ _)
  tracks_len := hInv.tracks_len
  tracks_inv := hInv.tracks_inv

theorem kiMirror_preserves {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {TrackInv : ℕ → τ → Prop} {C : Crypto} {K : MlKem}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qKiDone qStartDone qDrDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List τ}
    (hInv : HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH)
    (hKiNext : qKiDone + 1 ≤ b.q_total)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    HaltedSimInv TrackInv C K b qStart qDR (qKiDone + 1) qStartDone qDrDone
      (bhE2EMirror σH.1 kq kr, σH.2) := by
  rcases σH with ⟨σ, tracks⟩
  have hInstsEq : (bhE2EMirror σ kq kr).insts = σ.insts := by
    cases kq <;> cases kr <;> rfl
  have hStEq : (bhE2EMirror σ kq kr).st = σ.st := by
    cases kq <;> cases kr <;> rfl
  exact {
    ki_le := hKiNext
    start_le := hInv.start_le
    dr_le := hInv.dr_le
    mirror := DrvMirrorBounded.mirror hInv.mirror kq kr
    metaAligned := drvMetaAligned_mirror hInv.metaAligned kq kr
    sessions := fun d hd gs0 hgs0 => by
      rw [hInstsEq] at hd
      exact hInv.sessions d hd gs0 hgs0
    kiReach := hStEq ▸ hInv.kiReach.mono (Nat.le_succ _)
    tracks_len := by dsimp only; rw [hInstsEq]; exact hInv.tracks_len
    tracks_inv := hInv.tracks_inv
  }

/-! ## Verified subprogram bundle and boundedness -/

/-- Semantic evaluation and budget hypotheses for a `HaltedKindSubprograms` bundle against tracker `T`. -/
structure ValidHaltedKindSubprograms
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH)
    (TrackInv : ℕ → SessH → Prop)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) : Prop where
  track_valid : ValidSimTrackInv T TrackInv
  endpointCost_le :
    haltedKindEndpointCost subs qStart ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b
  stepCost_le :
    haltedKindStepCost subs b qStart qInst qep ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ
  sizeBound_le :
    ∀ qDR : ℕ, ∃ C₀ C₁, C₀ ≤ 2 ^ 22 ∧ C₁ ≤ 2 ^ 11 ∧
      haltedKindSizeBound subs b qStart qInst qep ≤
        C₀ + C₁ * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ)
  initKindC_eval :
    ∀ {Γ} (ρ : Env Γ),
      (subs.initKindC (Γ := Γ)).eval ρ =
        (e2eKeyIndTargetIface S ℓ Pt).liftP
          ((fun b0 : Bool => subs.drvEnc ({ b := b0 } : BHE2EDrvState S ℓ)) <$>
            ($ᵗ Bool : ProbComp Bool))
  kiQueryOkE_eval :
    SignalPqxdh.WellFormedPrimitivesδ P →
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
        (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
        (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S),
        σE.eval ρ = subs.drvEnc σH.1 →
        kqE.eval ρ = keyIndQenc kq →
        (subs.kiQueryOkE b qStart σE kqE).eval ρ =
          (bhDrvKiQueryOk P σH.1.toModelDriverBase kq &&
            !(match kq with | .corruptIK u => bhNoOpkRespPromoted σH.1.instMeta u | _ => false))
  mirrorE_eval :
    ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (krE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)))
      (ρ : Env Γ) (σ : BHE2EDrvState S ℓ)
      (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse),
      σE.eval ρ = subs.drvEnc σ →
      kqE.eval ρ = keyIndQenc kq →
      krE.eval ρ = keyIndRenc kr →
      (subs.mirrorE σE kqE krE).eval ρ = subs.drvEnc (bhE2EMirror σ kq kr)
  prepStartSpkE_eval :
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
        (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
        (ρ : Env Γ) (sid : SignalPqxdh.SessionId S),
        σE.eval ρ = subs.drvEnc σH.1 →
        sidE.eval ρ = sidV sid →
        (subs.prepStartSpkE b qStart σE sidE).eval ρ =
          (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj)
  finishStartSpkHaltedC_eval :
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      ∀ {Γ} (bmE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .bool))
        (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvKindHaltedTy subs))
        (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
        (kr1E kr2E : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt)))
        (acE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (BV256 (ℓ := ℓ) (Pt := Pt)))
        (ρ : Env Γ) (sid : SignalPqxdh.SessionId S)
        (kr1 kr2 : SignalPqxdh.KeyIndResponse),
        σHE.eval ρ = drvKindHaltedEnc subs σH →
        sidE.eval ρ = sidV sid →
        kr1E.eval ρ = keyIndRenc kr1 →
        kr2E.eval ρ = keyIndRenc kr2 →
        (subs.finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE).eval ρ =
          let fin := bhE2EFinishStartSpkTracked T.init C K (bmE.eval ρ) σH sid kr1 kr2 (acE.eval ρ)
          pure (fin.1, drvKindHaltedEnc subs fin.2)
  haltedStepLocalSmC_eval :
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      qDrDone + 1 ≤ qDR →
      ∀ {Γ} (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvKindHaltedTy subs))
        (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
        (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
        (ρ : Env Γ) (i : ℕ)
        (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
        σHE.eval ρ = drvKindHaltedEnc subs σH →
        idxE.eval ρ = i →
        sqE.eval ρ = smQenc sq →
        (subs.haltedStepLocalSmC b qStart qInst qep σHE idxE sqE).eval ρ =
          (e2eKeyIndTargetIface S ℓ Pt).liftP
            ((fun out => (packAtomicSmRespEnc out.1, drvKindHaltedEnc subs out.2)) <$>
              bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)
  finishKindE_eval :
    ∀ {qDR qKiDone qStartDone qDrDone : ℕ} {σH : BHE2EDrvState S ℓ × List SessH},
      HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
      ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
        (bOutE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
        (ρ : Env Γ),
        σE.eval ρ = subs.drvEnc σH.1 →
        (subs.finishKindE qStart σE bOutE).eval ρ =
          (bOutE.eval ρ == σH.1.b || bhE2EDrvWon σH.1 σH.1.b)

theorem kindRedHalted_gRedBounded_of_valid
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep : ℕ}
    (hValid : ValidHaltedKindSubprograms subs T TrackInv b qStart qInst qep) :
    let qTot := b.q_total + qStart + qDR
    GRedBounded (kindRedHalted subs b qStart qInst qep)
      (fun _ => 1) (fun _ => 0) qTot (2 * qTot) (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  dsimp only
  rcases hValid.sizeBound_le qDR with ⟨C₀, C₁, hC₀, hC₁, hSz⟩
  exact kindRedHalted_gRedBounded subs b qStart qInst qep (b.q_total + qStart + qDR)
    (bhE2ECostBudget S b qStart qDR qInst qep ℓ)
    (totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ
      (b.q_total + qStart + qDR) _ _ (le_refl _) hValid.endpointCost_le hValid.stepCost_le)
    (kindRedHalted_size_le_budget subs b qStart qInst qep
      (bhE2ECostBudget S b qStart qDR qInst qep ℓ) C₀ C₁ hC₀ hC₁ hSz)

theorem kindRedHalted_queryBounded_of_inst_gen
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    SignalPqxdh.QueryBounded
      (⟨(kindRedHalted subs b qStart qInst qep).eval
        (fun _ => B_A) ()⟩ : SignalPqxdh.KeyIndAdversary S)
      (keyIndReductionBudget S qStart b) :=
  Computational.Proofs.E2E.Dsl.KindRedHalted.kindRedHalted_queryBounded_inst
    subs b qStart (∑ k ∈ Finset.range qStart, qs k) qInst qep B_A hB.toKindTargetAdvBounded

theorem kindRedHalted_queryBounded_of_inst
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qep : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    SignalPqxdh.QueryBounded
      (⟨(kindRedHalted subs b qStart (∑ k ∈ Finset.range qStart, qs k) qep).eval
        (fun _ => B_A) ()⟩ : SignalPqxdh.KeyIndAdversary S)
      (keyIndReductionBudget S qStart b) :=
  kindRedHalted_queryBounded_of_inst_gen subs b qStart (∑ k ∈ Finset.range qStart, qs k) qep qs
    B_A hB

/-! ## `OneStageAtomicSimSpec` instantiation and `.eval` equivalence -/

private theorem atomicKeyIndLiftP_map {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α β : Type}
    (f : α → β) (p : ProbComp α) :
    (e2eKeyIndTargetIface S ℓ Pt).liftP (f <$> p) =
      f <$> (e2eKeyIndTargetIface S ℓ Pt).liftP p := by
  simp [atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP]

private def kiNoOpkPromoted {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) : SignalPqxdh.KeyIndQuery S → Bool
  | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u
  | _ => false

private theorem eval_query_keyInd {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (qE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (kq : SignalPqxdh.KeyIndQuery S)
    (hq : qE.eval ρ = keyIndQenc kq) :
    (Comp.query (O := atomicE2EOps ℓ P C K decT encT)
      (I := e2eKeyIndTargetIface S ℓ Pt) E2EKeyIndTag.keyInd qE).eval ρ =
      keyIndRenc <$>
        (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
          OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _) := by
  dsimp only [Comp.eval, e2eKeyIndTargetIface]
  rw [hq, keyIndQdec_keyIndQenc]

private theorem comp_eval_bind_sample_bv256 {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {b : Ty (atomicSig ℓ Pt)}
    (c2 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt)
      (BV256 (ℓ := ℓ) (Pt := Pt) :: Γ) b)
    (ρ : Env Γ) :
    (Comp.bind (.sample (I := e2eKeyIndTargetIface S ℓ Pt)
      (UniformSamplerTag.base AtomicBaseUnif.bv256) .unit) c2).eval ρ =
      (bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
        fun bv => c2.eval (.cons bv ρ)) := by
  dsimp only [Comp.eval, e2eKeyIndTargetIface, _root_.ReductionDsl.atomicBaseSamplers,
    _root_.ReductionDsl.unifSamplers]
  rw [atomicKeyIndTargetIface_liftP_eq_bhLiftP]
  rfl

private theorem comp_eval_bind {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (c1 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ a)
    (c2 : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) (a :: Γ) b)
    (ρ : Env Γ) :
    (Comp.bind c1 c2).eval ρ = (c1.eval ρ >>= fun x => c2.eval (.cons x ρ)) := rfl

private theorem comp_eval_ret {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicE2EOps ℓ P C K decT encT) Γ a) (ρ : Env Γ) :
    (Comp.ret (I := e2eKeyIndTargetIface S ℓ Pt) e).eval ρ = pure (e.eval ρ) := rfl

private theorem comp_eval_caseOpt {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt a))
    (cN : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ b)
    (cS : Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) (a :: Γ) b)
    (ρ : Env Γ) :
    (Comp.caseOpt e cN cS).eval ρ =
      match e.eval ρ with
      | none => cN.eval ρ
      | some x => cS.eval (.cons x ρ) := by
  dsimp only [Comp.eval]
  cases e.eval ρ <;> rfl

@[expose] def kindRedHalted_oneStageSimSpec
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep : ℕ}
    (hValid : ValidHaltedKindSubprograms subs T TrackInv b qStart qInst qep)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) :
    OneStageAtomicSimSpec S Pt ℓ (atomicE2EOps ℓ P C K decT encT) b qStart qDR
      (BHE2EDrvState S ℓ × List SessH) where
  R := kindRedHalted subs b qStart qInst qep
  handleRef := bhKindHandleWithHalted T.init
    (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K
  R_ref := bhKindRedWithHalted T.init
    (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K
  drvEnc := drvKindHaltedEnc subs
  Inv := HaltedSimInv TrackInv C K b qStart qDR
  impl_eq := rfl
  init_eq := by
    dsimp only [kindRedHalted, bhKindRedWithHalted, Comp.eval]
    rw [hValid.initKindC_eval, atomicKeyIndLiftP_map, bind_map_left]
    simp only [atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP,
      simulateQ_bind, simulateQ_pure, map_bind, map_pure, bind_assoc, pure_bind,
      Expr.eval, Expr.v0, Env.get, Prod.map, id_eq, drvKindHaltedEnc, List.map_nil]
  init_inv us hus := by
    dsimp only [bhKindRedWithHalted] at hus
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hus
    rcases hus with ⟨drvH, hdrvH, rfl⟩
    have hdrvP := mem_support_of_bhLiftP _ hdrvH
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hdrvP
    rcases hdrvP with ⟨secb, -, rfl⟩
    exact HaltedSimInv.empty TrackInv C K b qStart qDR secb
  step_eq {qKiDone qStartDone qDrDone σH} hInv t hBud := by
    dsimp only [kindRedHalted]
    rcases t with (kq | ctl) | ⟨i, sq⟩
    · clear hBud
      rw [kindHandleHalted_eval_ki]
      have hRhsEq :
          bhKindHandleWithHalted T.init
            (bhE2EStepLocalSmSessionTracked T C K qep decT encT) P C K σH
            (bhTargetQenc (.inl (.inl kq))) =
          if (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted σH.1 kq) = true then
            do
              let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
                OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
              pure ((.inl (.inl kr) : CryptoVerification.E2E.BHTargetResp ℓ),
                (bhE2EMirror σH.1 kq kr, σH.2))
          else
            pure ((.inl (.inl .noneResp) : CryptoVerification.E2E.BHTargetResp ℓ), σH) := by
        cases kq <;> rfl
      rw [hRhsEq]
      let ρ_ki : Env [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
          Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
          (.cons (drvKindHaltedEnc subs σH) (.cons (.inl (.inl (keyIndQenc kq))) .nil)))
      have hokE : (subs.kiQueryOkE b qStart (.fst .v2) .v0).eval ρ_ki =
          (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted σH.1 kq) := by
        rw [hValid.kiQueryOkE_eval hP hInv (.fst .v2) .v0 ρ_ki kq
          (by simp [ρ_ki, Expr.eval, Expr.v2, drvKindHaltedEnc])
          (by simp [ρ_ki, Expr.eval, Expr.v0])]
        cases kq <;> rfl
      dsimp only [ρ_ki] at hokE
      rw [hokE]
      cases hok : (bhDrvKiQueryOk P σH.1.toModelDriverBase kq && !kiNoOpkPromoted σH.1 kq)
      · simp [Prod.map, atomicKindRespEnc, keyIndRenc, drvKindHaltedEnc]
      · simp only [↓reduceIte]
        have hq := eval_query_keyInd (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          .v0 ρ_ki kq (by simp [ρ_ki, Expr.eval, Expr.v0])
        dsimp only [ρ_ki] at hq
        rw [hq]
        simp only [bind_map_left, map_bind, map_pure]
        refine bind_congr fun kr => ?_
        have hm := hValid.mirrorE_eval (.fst .v3) .v1 .v0 (.cons (keyIndRenc kr) ρ_ki) σH.1 kq kr
          (by simp [ρ_ki, Expr.eval, Expr.v3, drvKindHaltedEnc])
          (by simp [ρ_ki, Expr.eval, Expr.v1])
          (by simp [ρ_ki, Expr.eval, Expr.v0])
        dsimp only [ρ_ki] at hm
        rw [hm]
        rfl
    · clear hBud
      cases ctl with | startDR sid =>
      rw [kindHandleHalted_eval_ctl]
      dsimp only [bhKindHandleWithHalted, bhTargetQenc]
      let Γ_ctl : List (Ty (atomicSig ℓ Pt)) :=
        [sidT (ℓ := ℓ) (Pt := Pt) S,
          Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
          drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
      let ρ_ctl : Env Γ_ctl :=
        .cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons (drvKindHaltedEnc subs σH) (.cons (.inl (.inr (sidV sid))) .nil)))
      dsimp only [kindStartStepHaltedC]
      rw [comp_eval_bind, comp_eval_ret]
      have hpair : (Expr.pair (O := atomicE2EOps ℓ P C K decT encT) .v2 .v0).eval ρ_ctl =
          (drvKindHaltedEnc subs σH, sidV sid) := rfl
      dsimp only [ρ_ctl] at hpair
      rw [hpair, pure_bind, comp_eval_caseOpt]
      let Γ1 := Ty.prod (drvKindHaltedTy subs) (sidT (ℓ := ℓ) (Pt := Pt) S) :: Γ_ctl
      let ρ1 : Env Γ1 := .cons (drvKindHaltedEnc subs σH, sidV sid) ρ_ctl
      have hprep := hValid.prepStartSpkE_eval hInv (.fst (.fst .v0)) (.snd .v0) ρ1 sid
        (by simp [ρ1, Expr.eval, Expr.v0, drvKindHaltedEnc])
        (by simp [ρ1, Expr.eval, Expr.v0])
      dsimp only [ρ1, ρ_ctl] at hprep
      rw [hprep]
      rcases hguard : bhE2EGuard σH.1 sid with _ | ⟨_, _, u, j⟩
      · dsimp only [Option.map]
        rw [comp_eval_ret]
        simp [Expr.eval, Expr.v0, Prod.map, atomicKindRespEnc]
      · dsimp only [Option.map]
        let Γ2 := Ty.prod (_root_.ReductionDsl.FinT (ℓ := ℓ) (Pt := Pt) S.N_id)
          (_root_.ReductionDsl.FinT (ℓ := ℓ) (Pt := Pt) S.N_recv) :: Γ1
        let ρ2 : Env Γ2 := .cons (u, j) ρ1
        rw [comp_eval_bind]
        have htsQ : (mkAtomicTestSessionE (O := atomicE2EOps ℓ P C K decT encT) (.snd .v1)).eval ρ2 =
            keyIndQenc (.testSession sid) := by
          simp [ρ2, ρ1, Expr.eval, Expr.v1, sidOfV_sidV]
        have hq1 := eval_query_keyInd (mkAtomicTestSessionE (.snd .v1)) ρ2 (.testSession sid) htsQ
        dsimp only [ρ2, ρ1, ρ_ctl] at hq1
        rw [hq1]
        simp only [bind_map_left, map_bind, bind_assoc]
        refine bind_congr fun ts => ?_
        let Γ3 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ2
        let ρ3 : Env Γ3 := .cons (keyIndRenc ts) ρ2
        rw [comp_eval_bind]
        have hskQ : (mkAtomicRevealSpkSkE (O := atomicE2EOps ℓ P C K decT encT) .v1).eval ρ3 =
            keyIndQenc (.revealSpkSk u j) := by
          simp [ρ3, ρ2, Expr.eval, Expr.v1]
        have hq2 := eval_query_keyInd (mkAtomicRevealSpkSkE .v1) ρ3 (.revealSpkSk u j) hskQ
        dsimp only [ρ3, ρ2, ρ1, ρ_ctl] at hq2
        rw [hq2]
        simp only [bind_map_left, bind_assoc]
        refine bind_congr fun sk => ?_
        let Γ4 := keyIndRT (ℓ := ℓ) (Pt := Pt) :: Γ3
        let ρ4 : Env Γ4 := .cons (keyIndRenc sk) ρ3
        have hsmp := comp_eval_bind_sample_bv256
          (subs.finishStartSpkHaltedC b qStart (.some (subs.drvBitE (.fst (.fst .v4))))
            (.fst .v4) (.snd .v4) .v2 .v1 .v0) ρ4
        refine (congrArg (fun m => m >>= fun v =>
          pure ((.inl (.inr v.1) : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2)) hsmp).trans ?_
        dsimp only [ρ4, ρ3, ρ2, ρ1, ρ_ctl]
        rw [bind_assoc]
        refine bind_congr fun bv => ?_
        let Γ5 := BV256 (ℓ := ℓ) (Pt := Pt) :: Γ4
        let ρ5 : Env Γ5 := .cons bv ρ4
        have hfin := hValid.finishStartSpkHaltedC_eval hInv
          (.some (subs.drvBitE (.fst (.fst .v4)))) (.fst .v4) (.snd .v4) .v2 .v1 .v0
          ρ5 sid ts sk
          (by simp [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4])
          (by simp [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4])
          (by simp [ρ5, ρ4, ρ3, Expr.eval, Expr.v2])
          (by simp [ρ5, ρ4, Expr.eval, Expr.v1])
        have hbit : (Expr.some (subs.drvBitE (.fst (.fst .v4)))).eval ρ5 = some σH.1.b := by
          dsimp only [Expr.eval]
          rw [subs.drvBitE_eval (.fst (.fst .v4)) ρ5 σH.1
            (by simp [ρ5, ρ4, ρ3, ρ2, ρ1, Expr.eval, Expr.v4, drvKindHaltedEnc])]
        have hbvE : (Expr.v0 : Expr (atomicE2EOps ℓ P C K decT encT) Γ5 _).eval ρ5 = bv := rfl
        dsimp only at hfin
        rw [hbit, hbvE] at hfin
        dsimp only [ρ5, ρ4, ρ3, ρ2, ρ1, ρ_ctl] at hfin
        rw [hfin]
        simp [Prod.map, atomicKindRespEnc]
    · rw [kindHandleHalted_eval_sm]
      dsimp only [bhKindHandleWithHalted, bhTargetQenc]
      let ρ_sm : Env [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)),
          drvKindHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q] :=
        .cons (i, smQenc sq) (.cons (drvKindHaltedEnc subs σH) (.cons (.inr (i, smQenc sq)) .nil))
      rw [hValid.haltedStepLocalSmC_eval hInv hBud .v1 (.fst .v0) (.snd .v0) ρ_sm i sq rfl rfl rfl]
      rw [atomicKeyIndLiftP_map, bind_map_left]
      simp [atomicKeyIndTargetIface_liftP_eq_bhLiftP, bhLiftP, Prod.map, atomicKindRespEnc]
  step_inv {qKiDone qStartDone qDrDone σH} hInv t hBud rs hrs := by
    rcases t with (kq | ctl) | ⟨i, sq⟩
    · dsimp only [bhKindHandleWithHalted, bhTargetQenc, KindRedHaltedEval.StepNextInv] at hrs ⊢
      split_ifs at hrs with hok
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrs
        rcases hrs with ⟨kr, -, rfl⟩
        exact kiMirror_preserves hInv hBud kq kr
      · simp only [support_pure, Set.mem_singleton_iff] at hrs
        subst hrs
        exact kiSkip_preserves hInv hBud
    · cases ctl with | startDR sid =>
      dsimp only [bhKindHandleWithHalted, bhTargetQenc, KindRedHaltedEval.StepNextInv] at hrs ⊢
      rcases hguard : (bhE2EGuard σH.1 sid).map (fun (_, _, uj) => uj) with _ | ⟨u, j⟩
      · rw [hguard] at hrs
        simp only [support_pure, Set.mem_singleton_iff] at hrs
        subst hrs
        exact {
          ki_le := hInv.ki_le
          start_le := hBud
          dr_le := hInv.dr_le
          mirror := hInv.mirror.mono (le_refl _) (le_refl _) (le_refl _)
            (le_refl _) (le_refl _) (Nat.le_succ _)
          metaAligned := hInv.metaAligned
          sessions := hInv.sessions
          kiReach := hInv.kiReach
          tracks_len := hInv.tracks_len
          tracks_inv := hInv.tracks_inv
        }
      · rw [hguard] at hrs
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrs
        rcases hrs with ⟨ts, -, sk, -, bv, -, rfl⟩
        exact (finishStartSpkTracked_preserves hValid.track_valid C K (some σH.1.b)
          hInv hBud sid ts sk bv).1
    · dsimp only [bhKindHandleWithHalted, bhTargetQenc, KindRedHaltedEval.StepNextInv] at hrs ⊢
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrs
      rcases hrs with ⟨⟨sr, σH'⟩, h1, rfl⟩
      have hsm := mem_support_of_bhLiftP _ h1
      exact (stepLocalSmSessionTracked_preserves hValid.track_valid C K qep decT encT
        hInv hBud i sq hsm).1
  finish_eq {_ _ _ σ_out} hInv b_out := by
    dsimp only [kindRedHalted, bhKindRedWithHalted, Comp.eval]
    let ρ_f : Env [drvKindHaltedTy subs, .bool] :=
      .cons (drvKindHaltedEnc subs σ_out) (.cons b_out .nil)
    rw [hValid.finishKindE_eval hInv (.fst .v0) .v1 ρ_f
      (by simp [ρ_f, Expr.eval, Expr.v0, drvKindHaltedEnc])]
    rfl

/-- Evaluation equivalence between `kindRedHalted` and `bhKindRedWithTracked` for any `KeyInd` handler `ki`. -/
theorem kindEval_eq_of_valid
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop}
    {b : SignalPqxdh.QueryBudget} {qStart qInst qep : ℕ} {qs : ℕ → ℕ}
    (hValid : ValidHaltedKindSubprograms subs T TrackInv b qStart qInst qep)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    let smImpl := fun d : BHModelInst S ℓ =>
      oracleImplRSessionTracked T
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB) ℓ d.spkCoins)
        (2 + 1) qep (configRefuseEarlyBobCorr decT encT)
    (kindRedHalted subs b qStart qInst qep).eval (fun _ => B_A) () =
      (bhKindRedWithTracked T.init smImpl P ki C K).eval (fun _ => B_A) () := by
  dsimp only
  have hSim := oneStage_eval_eq
    (kindRedHalted_oneStageSimSpec (qDR := ∑ k ∈ Finset.range qStart, qs k) hValid hP) B_A
    hB.toOneStageTargetBounded
  dsimp only [kindRedHalted_oneStageSimSpec] at hSim
  rwa [bhKindRedWithHalted_eq_bhKindRedWithTracked T P ki C K qep decT encT] at hSim

/-! ## Handshake subprogram wiring -/

/-- Per-session halted Double Ratchet step contract over `e2eKeyIndTargetIface`. -/
structure HaltedLocalSmKindStep
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop) where
  stepC : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)) →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT)
        (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
  stepCost : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ℕ
  stepSize : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ℕ
  stepC_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (stepC b qStart qInst qep σHE idxE sqE).cost ≤
      σHE.cost + idxE.cost + sqE.cost + stepCost b qStart qInst qep
  stepC_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (stepC b qStart qInst qep σHE idxE sqE).size ≤
      σHE.size + idxE.size + sqE.size + stepSize b qStart qInst qep
  stepC_queries : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
    (w : (e2eKeyIndTargetIface S ℓ Pt).Tag → ℕ),
    (stepC b qStart qInst qep σHE idxE sqE).queries w (fun _ => 0) = 0
  stepCost_bound : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ),
    stepCost b qStart qInst qep ≤
      650 * b.q_total + 800 * qInst + 10 * ℓ + 4 * Nat.log 2 qep + 19000000
  stepSize_bound : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ),
    stepSize b qStart qInst qep ≤
      500000 + 500 * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ)
  stepC_eval : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ)
    {qKiDone qStartDone qDrDone : ℕ}
    {σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)},
    HaltedSimInv TrackInv C K b qStart qDR qKiDone qStartDone qDrDone σH →
    qDrDone + 1 ≤ qDR →
    ∀ {Γ}
      (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
        (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
      (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
      (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
      (ρ : Env Γ) (i : ℕ)
      (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
      σHE.eval ρ = (HaltedStartSessionSim.drvEnc σH.1, σH.2.map HaltedStartSessionSim.sessHEnc) →
      idxE.eval ρ = i →
      sqE.eval ρ = smQenc sq →
      (stepC b qStart qInst qep σHE idxE sqE).eval ρ =
        (e2eKeyIndTargetIface S ℓ Pt).liftP
          ((fun out => (packAtomicSmRespEnc out.1,
            (HaltedStartSessionSim.drvEnc out.2.1, out.2.2.map HaltedStartSessionSim.sessHEnc))) <$>
            bhE2EStepLocalSmSessionTracked (kemFailSessionTracker C.F K) C K qep decT encT σH i sq)

@[expose] def mkKindSubprogramsHalted
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (smStep : HaltedLocalSmKindStep S ℓ Pt P C K decT encT TrackInv) :
    HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT (KemFailSessionTrack C.F Bytes) where
  drvTy := HaltedStartSessionSim.drvTy S ℓ Pt
  sessHTy := HaltedStartSessionSim.sessHTy ℓ Pt
  drvEnc := HaltedStartSessionSim.drvEnc
  sessHEnc := HaltedStartSessionSim.sessHEnc
  initKindC := fun {_} => HaltedStartSessionSim.initKindC
  initKindCost := HaltedStartSessionSim.initKindCost
  initKindSize := HaltedStartSessionSim.initKindSize
  initKindC_cost := fun {_} => HaltedStartSessionSim.initKindC_cost
  initKindC_size := fun {_} => HaltedStartSessionSim.initKindC_size
  initKindC_queries := fun {_} w => HaltedStartSessionSim.initKindC_queries w
  drvBitE := fun {_} σE => HaltedStartSessionSim.drvBitE σE
  drvBitCost := HaltedStartSessionSim.drvBitCost
  drvBitSize := HaltedStartSessionSim.drvBitSize
  drvBitE_cost := fun {_} σE => HaltedStartSessionSim.drvBitE_cost σE
  drvBitE_size := fun {_} σE => HaltedStartSessionSim.drvBitE_size σE
  drvBitE_eval := fun {_} σE ρ σ hσ => HaltedStartSessionSim.drvBitE_eval σE ρ σ hσ
  kiQueryOkE := fun b qStart {_} σE kqE => HaltedStartSessionSim.kiQueryOkE b qStart σE kqE
  kiQueryOkCost := HaltedStartSessionSim.kiQueryOkCost
  kiQueryOkSize := HaltedStartSessionSim.kiQueryOkSize
  kiQueryOkE_cost := fun b qStart {_} σE kqE =>
    HaltedStartSessionSim.kiQueryOkE_cost b qStart σE kqE
  kiQueryOkE_size := fun b qStart {_} σE kqE =>
    HaltedStartSessionSim.kiQueryOkE_size b qStart σE kqE
  mirrorE := fun {_} σE kqE krE => HaltedStartSessionSim.mirrorE σE kqE krE
  mirrorCost := HaltedStartSessionSim.mirrorCost
  mirrorSize := HaltedStartSessionSim.mirrorSize
  mirrorE_cost := fun {_} σE kqE krE => HaltedStartSessionSim.mirrorE_cost σE kqE krE
  mirrorE_size := fun {_} σE kqE krE => HaltedStartSessionSim.mirrorE_size σE kqE krE
  prepStartSpkE := fun b qStart {_} σE sidE => HaltedStartSessionSim.prepStartSpkE b qStart σE sidE
  prepStartSpkCost := HaltedStartSessionSim.prepStartSpkCost
  prepStartSpkSize := HaltedStartSessionSim.prepStartSpkSize
  prepStartSpkE_cost := fun b qStart {_} σE sidE =>
    HaltedStartSessionSim.prepStartSpkE_cost b qStart σE sidE
  prepStartSpkE_size := fun b qStart {_} σE sidE =>
    HaltedStartSessionSim.prepStartSpkE_size b qStart σE sidE
  finishStartSpkHaltedC := fun b qStart {_} bmE σHE sidE kr1E kr2E acE =>
    HaltedStartSessionSim.finishStartSpkHaltedC b qStart bmE σHE sidE kr1E kr2E acE
  finishStartSpkHaltedCost := HaltedStartSessionSim.finishStartSpkHaltedCost
  finishStartSpkHaltedSize := HaltedStartSessionSim.finishStartSpkHaltedSize
  finishStartSpkHaltedC_cost := fun b qStart {_} bmE σHE sidE kr1E kr2E acE =>
    HaltedStartSessionSim.finishStartSpkHaltedC_cost b qStart bmE σHE sidE kr1E kr2E acE
  finishStartSpkHaltedC_size := fun b qStart {_} bmE σHE sidE kr1E kr2E acE =>
    HaltedStartSessionSim.finishStartSpkHaltedC_size b qStart bmE σHE sidE kr1E kr2E acE
  finishStartSpkHaltedC_queries := fun b qStart {_} bmE σHE sidE kr1E kr2E acE w =>
    HaltedStartSessionSim.finishStartSpkHaltedC_queries b qStart bmE σHE sidE kr1E kr2E acE w
  haltedStepLocalSmC := fun b qStart qInst qep {_} σHE idxE sqE =>
    smStep.stepC b qStart qInst qep σHE idxE sqE
  haltedStepLocalSmCost := smStep.stepCost
  haltedStepLocalSmSize := smStep.stepSize
  haltedStepLocalSmC_cost := fun b qStart qInst qep {_} σHE idxE sqE =>
    smStep.stepC_cost b qStart qInst qep σHE idxE sqE
  haltedStepLocalSmC_size := fun b qStart qInst qep {_} σHE idxE sqE =>
    smStep.stepC_size b qStart qInst qep σHE idxE sqE
  haltedStepLocalSmC_queries := fun b qStart qInst qep {_} σHE idxE sqE w =>
    smStep.stepC_queries b qStart qInst qep σHE idxE sqE w
  finishKindE := fun qStart {_} σE bOutE => HaltedStartSessionSim.finishKindE qStart σE bOutE
  finishKindCost := HaltedStartSessionSim.finishKindCost
  finishKindSize := HaltedStartSessionSim.finishKindSize
  finishKindE_cost := fun qStart {_} σE bOutE =>
    HaltedStartSessionSim.finishKindE_cost qStart σE bOutE
  finishKindE_size := fun qStart {_} σE bOutE =>
    HaltedStartSessionSim.finishKindE_size qStart σE bOutE

theorem mkKindSubprogramsHalted_valid
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (hTrack : ValidSimTrackInv (kemFailSessionTracker (ℓ := ℓ) C.F K) TrackInv)
    (smStep : HaltedLocalSmKindStep S ℓ Pt P C K decT encT TrackInv)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    (hEnd : haltedKindEndpointCost (mkKindSubprogramsHalted smStep) qStart ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b)
    (hStep : haltedKindStepCost (mkKindSubprogramsHalted smStep) b qStart qInst qep ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ) :
    ValidHaltedKindSubprograms (mkKindSubprogramsHalted smStep)
      (kemFailSessionTracker (ℓ := ℓ) C.F K) TrackInv b qStart qInst qep where
  track_valid := hTrack
  endpointCost_le := hEnd
  stepCost_le := hStep
  sizeBound_le := fun qDR => by
    refine ⟨510000, 530, by omega, by omega, ?_⟩
    have hsm := smStep.stepSize_bound b qStart qDR qInst qep
    obtain ⟨hbTot, hbSt, -⟩ := params_bits_le_budget S b qStart qDR qInst qep ℓ
    dsimp only [haltedKindSizeBound, mkKindSubprogramsHalted,
      HaltedStartSessionSim.initKindSize, HaltedStartSessionSim.finishKindSize,
      HaltedStartSessionSim.kiQueryOkSize, HaltedStartSessionSim.mirrorSize,
      HaltedStartSessionSim.prepStartSpkSize, HaltedStartSessionSim.drvBitSize,
      HaltedStartSessionSim.finishStartSpkHaltedSize]
    omega
  initKindC_eval := fun {_} ρ => HaltedStartSessionSim.initKindC_eval ρ
  kiQueryOkE_eval := fun hP {_ _ _ _ _} hInv {_} σE kqE ρ kq hσ hkq => by
    have h := HaltedStartSessionSim.kiQueryOkE_eval b qStart hP σE kqE ρ hσ hkq hInv.mirror_full
    cases kq <;> exact h
  mirrorE_eval := fun {_} σE kqE krE ρ σ kq kr hσ hkq hkr =>
    HaltedStartSessionSim.mirrorE_eval σE kqE krE ρ σ kq kr hσ hkq hkr
  prepStartSpkE_eval := fun {_ _ _ _ _} hInv {_} σE sidE ρ sid hσ hsid =>
    HaltedStartSessionSim.prepStartSpkE_eval b qStart σE sidE ρ _ sid hσ hsid hInv.mirror_full
  finishStartSpkHaltedC_eval := fun {_ _ _ _ σH} hInv {_} bmE σHE sidE kr1E kr2E acE
      ρ sid kr1 kr2 hσH hsid hkr1 hkr2 => by
    have hTracks : σH.2.length ≤ qStart := hInv.tracks_len ▸ hInv.mirror_full.insts_le
    refine Eq.trans (HaltedStartSessionSim.finishStartSpkHaltedC_eval b qStart
      bmE σHE sidE kr1E kr2E acE ρ σH sid kr1 kr2 hσH hsid hkr1 hkr2 hTracks hInv.mirror_full) ?_
    dsimp only [bhE2EFinishStartSpkTracked, drvKindHaltedEnc, mkKindSubprogramsHalted,
      kemFailSessionTracker, Computational.Proofs.E2E.Dsl.CompositionHaltedWitness.initKemTrack]
    rcases bhE2EFinishStartSpk C K (bmE.eval ρ) σH.1 sid kr1 kr2 (acE.eval ρ)
      with ⟨_ | idx, σ'⟩ <;> cases kr1 <;> rfl
  haltedStepLocalSmC_eval := fun {qDR _ _ _ _} hInv hDrNext {_} σHE idxE sqE ρ i sq hσH hidx hsq =>
    smStep.stepC_eval b qStart qDR qInst qep hInv hDrNext σHE idxE sqE ρ i sq hσH hidx hsq
  finishKindE_eval := fun {_ _ _ _ _} hInv {_} σE bOutE ρ hσ =>
    HaltedStartSessionSim.finishKindE_eval qStart σE bOutE ρ hσ hInv.mirror_full.insts_le

/-! ## Clamped handshake subprograms -/

section ClampedHandshake

open Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp (SmEpochBounded)
open Computational.Proofs.E2E.Dsl.M3Interfaces (DrvMetaAligned DrvSessionsBounded)

structure HaltedLocalSmKindStepInst
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop) where
  stepC : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)) →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eKeyIndTargetIface S ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT)
        (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
  stepCost : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ℕ
  stepSize : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ℕ
  stepC_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (stepC b qStart qInst qep σHE idxE sqE).cost ≤
      σHE.cost + idxE.cost + sqE.cost + stepCost b qStart qInst qep
  stepC_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (stepC b qStart qInst qep σHE idxE sqE).size ≤
      σHE.size + idxE.size + sqE.size + stepSize b qStart qInst qep
  stepC_queries : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
    (w : (e2eKeyIndTargetIface S ℓ Pt).Tag → ℕ),
    (stepC b qStart qInst qep σHE idxE sqE).queries w (fun _ => 0) = 0
  stepCost_bound : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ),
    stepCost b qStart qInst qep ≤
      650 * b.q_total + 800 * qInst + 10 * ℓ + 4 * Nat.log 2 qep + 19000000
  stepSize_bound : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ),
    stepSize b qStart qInst qep ≤
      500000 + 500 * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ)
  stepC_eval : ∀ (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ)
    {σH : BHE2EDrvState S ℓ × List (KemFailSessionTrack C.F Bytes)},
    σH.1.insts.length ≤ min qStart (min b.q_total S.N_send_tot) →
    DrvMetaAligned σH.1 →
    σH.1.corrPrins.length ≤ b.q_total →
    σH.1.revealedSpks.length ≤ b.q_total →
    σH.1.prins.length ≤ b.q_total →
    DrvSessionsBounded C K qInst σH.1 →
    (∀ d ∈ σH.1.insts, ∀ gs ∈ d.gs, SmEpochBounded qInst gs) →
    σH.2.length ≤ min qStart (min b.q_total S.N_send_tot) →
    (∀ st ∈ σH.2, TrackInv qInst st) →
    ∀ {Γ}
      (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
        (.prod (HaltedStartSessionSim.drvTy S ℓ Pt) (.list (HaltedStartSessionSim.sessHTy ℓ Pt))))
      (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
      (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
      (ρ : Env Γ) (i : ℕ)
      (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
      σHE.eval ρ = (HaltedStartSessionSim.drvEnc σH.1, σH.2.map HaltedStartSessionSim.sessHEnc) →
      idxE.eval ρ = i →
      sqE.eval ρ = smQenc sq →
      (stepC b qStart qInst qep σHE idxE sqE).eval ρ =
        (e2eKeyIndTargetIface S ℓ Pt).liftP
          ((fun out => (packAtomicSmRespEnc out.1,
            (HaltedStartSessionSim.drvEnc out.2.1, out.2.2.map HaltedStartSessionSim.sessHEnc))) <$>
            bhE2EStepLocalSmSessionTracked (kemFailSessionTracker C.F K) C K qep decT encT σH i sq)

/-- `b₀`-clamped `HaltedKindSubprograms` bundle satisfying `bhE2ECostBudget` unconditionally. -/
@[expose] def mkKindSubprogramsHaltedClamped
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (smStep : HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT TrackInv)
    (b₀ : SignalPqxdh.QueryBudget) :
    HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT (KemFailSessionTrack C.F Bytes) where
  drvTy := HaltedStartSessionSim.drvTy S ℓ Pt
  sessHTy := HaltedStartSessionSim.sessHTy ℓ Pt
  drvEnc := HaltedStartSessionSim.drvEnc
  sessHEnc := HaltedStartSessionSim.sessHEnc
  initKindC := fun {_} => HaltedStartSessionSim.initKindC
  initKindCost := HaltedStartSessionSim.initKindCost
  initKindSize := HaltedStartSessionSim.initKindSize
  initKindC_cost := fun {_} => HaltedStartSessionSim.initKindC_cost
  initKindC_size := fun {_} => HaltedStartSessionSim.initKindC_size
  initKindC_queries := fun {_} w => HaltedStartSessionSim.initKindC_queries w
  drvBitE := fun {_} σE => HaltedStartSessionSim.drvBitE σE
  drvBitCost := HaltedStartSessionSim.drvBitCost
  drvBitSize := HaltedStartSessionSim.drvBitSize
  drvBitE_cost := fun {_} σE => HaltedStartSessionSim.drvBitE_cost σE
  drvBitE_size := fun {_} σE => HaltedStartSessionSim.drvBitE_size σE
  drvBitE_eval := fun {_} σE ρ σ hσ => HaltedStartSessionSim.drvBitE_eval σE ρ σ hσ
  kiQueryOkE := fun _b qSt {_} σE kqE => HaltedStartSessionSim.kiQueryOkClampedE b₀ qSt σE kqE
  kiQueryOkCost := fun _b qSt => HaltedStartSessionSim.kiQueryOkClampedCost S b₀ qSt
  kiQueryOkSize := fun _b _qSt => HaltedStartSessionSim.kiQueryOkClampedSize b₀
  kiQueryOkE_cost := fun _b qSt {_} σE kqE =>
    HaltedStartSessionSim.kiQueryOkClampedE_cost b₀ qSt σE kqE
  kiQueryOkE_size := fun _b qSt {_} σE kqE =>
    HaltedStartSessionSim.kiQueryOkClampedE_size b₀ qSt σE kqE
  mirrorE := fun {_} σE kqE krE => HaltedStartSessionSim.mirrorClampedE b₀ σE kqE krE
  mirrorCost := HaltedStartSessionSim.mirrorClampedCost b₀
  mirrorSize := HaltedStartSessionSim.mirrorClampedSize b₀
  mirrorE_cost := fun {_} σE kqE krE => HaltedStartSessionSim.mirrorClampedE_cost b₀ σE kqE krE
  mirrorE_size := fun {_} σE kqE krE => HaltedStartSessionSim.mirrorClampedE_size b₀ σE kqE krE
  prepStartSpkE := fun _b qSt {_} σE sidE => HaltedStartSessionSim.prepStartSpkClampedE b₀ qSt σE sidE
  prepStartSpkCost := fun _b qSt => HaltedStartSessionSim.prepStartSpkClampedCost S b₀ qSt
  prepStartSpkSize := fun _b _qSt => HaltedStartSessionSim.prepStartSpkClampedSize b₀
  prepStartSpkE_cost := fun _b qSt {_} σE sidE =>
    HaltedStartSessionSim.prepStartSpkClampedE_cost b₀ qSt σE sidE
  prepStartSpkE_size := fun _b qSt {_} σE sidE =>
    HaltedStartSessionSim.prepStartSpkClampedE_size b₀ qSt σE sidE
  finishStartSpkHaltedC := fun _b qSt {_} bmE σHE sidE kr1E kr2E acE =>
    HaltedStartSessionSim.finishStartSpkHaltedClampedC b₀ qSt bmE σHE sidE kr1E kr2E acE
  finishStartSpkHaltedCost := fun _b qSt =>
    HaltedStartSessionSim.finishStartSpkHaltedClampedCost S b₀ qSt
  finishStartSpkHaltedSize := fun _b _qSt => HaltedStartSessionSim.finishStartSpkHaltedClampedSize b₀
  finishStartSpkHaltedC_cost := fun _b qSt {_} bmE σHE sidE kr1E kr2E acE =>
    HaltedStartSessionSim.finishStartSpkHaltedClampedC_cost b₀ qSt bmE σHE sidE kr1E kr2E acE
  finishStartSpkHaltedC_size := fun _b qSt {_} bmE σHE sidE kr1E kr2E acE =>
    HaltedStartSessionSim.finishStartSpkHaltedClampedC_size b₀ qSt bmE σHE sidE kr1E kr2E acE
  finishStartSpkHaltedC_queries := fun _b qSt {_} bmE σHE sidE kr1E kr2E acE w =>
    HaltedStartSessionSim.finishStartSpkHaltedClampedC_queries b₀ qSt bmE σHE sidE kr1E kr2E acE w
  haltedStepLocalSmC := fun b qSt qInst qep {_} σHE idxE sqE =>
    smStep.stepC b qSt qInst qep σHE idxE sqE
  haltedStepLocalSmCost := smStep.stepCost
  haltedStepLocalSmSize := smStep.stepSize
  haltedStepLocalSmC_cost := fun b qSt qInst qep {_} σHE idxE sqE =>
    smStep.stepC_cost b qSt qInst qep σHE idxE sqE
  haltedStepLocalSmC_size := fun b qSt qInst qep {_} σHE idxE sqE =>
    smStep.stepC_size b qSt qInst qep σHE idxE sqE
  haltedStepLocalSmC_queries := fun b qSt qInst qep {_} σHE idxE sqE w =>
    smStep.stepC_queries b qSt qInst qep σHE idxE sqE w
  finishKindE := fun qSt {_} σE bOutE => HaltedStartSessionSim.finishKindClampedE b₀ qSt σE bOutE
  finishKindCost := HaltedStartSessionSim.finishKindClampedCost S b₀
  finishKindSize := fun _qSt => HaltedStartSessionSim.finishKindClampedSize b₀
  finishKindE_cost := fun qSt {_} σE bOutE =>
    HaltedStartSessionSim.finishKindClampedE_cost b₀ qSt σE bOutE
  finishKindE_size := fun qSt {_} σE bOutE =>
    HaltedStartSessionSim.finishKindClampedE_size b₀ qSt σE bOutE

theorem mkKindSubprogramsHaltedClamped_endpointCost_le
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (smStep : HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT TrackInv)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    haltedKindEndpointCost (mkKindSubprogramsHaltedClamped smStep b) qStart ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ +
        2 ^ 13 * min qStart (min b.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b := by
  have hw : haltedKindEndpointCost (mkKindSubprogramsHaltedClamped smStep b) qStart ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
    apply haltedLinearStep_le_weightedFactor
    dsimp only [haltedKindEndpointCost, mkKindSubprogramsHaltedClamped,
      HaltedStartSessionSim.initKindCost, HaltedStartSessionSim.finishKindClampedCost,
      FreshnessSim.finishKindCost, FreshnessSim.drvWonCost]
    omega
  omega

theorem mkKindSubprogramsHaltedClamped_stepCost_le
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (smStep : HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT TrackInv)
    (b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) :
    haltedKindStepCost (mkKindSubprogramsHaltedClamped smStep b) b qStart qInst qep ≤
      2 ^ 10 * e2ePerStepWeightedFactor S b qStart qInst qep ℓ := by
  apply haltedLinearStep_le_weightedFactor
  have hsm := smStep.stepCost_bound b qStart qInst qep
  dsimp only [haltedKindStepCost, mkKindSubprogramsHaltedClamped,
    HaltedStartSessionSim.kiQueryOkClampedCost, HaltedStartSessionSim.mirrorClampedCost,
    HaltedStartSessionSim.prepStartSpkClampedCost, HaltedStartSessionSim.drvBitCost,
    HaltedStartSessionSim.finishStartSpkHaltedClampedCost]
  omega

theorem mkKindSubprogramsHaltedClamped_sizeBound_le
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (smStep : HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT TrackInv)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    haltedKindSizeBound (mkKindSubprogramsHaltedClamped smStep b) b qStart qInst qep ≤
      510000 + 530 * bits (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  have hsm := smStep.stepSize_bound b qStart qDR qInst qep
  obtain ⟨hbTot, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    params_bits_le_budget S b qStart qDR qInst qep ℓ
  dsimp only [haltedKindSizeBound, mkKindSubprogramsHaltedClamped,
    HaltedStartSessionSim.initKindSize, HaltedStartSessionSim.finishKindClampedSize,
    HaltedStartSessionSim.kiQueryOkClampedSize, HaltedStartSessionSim.mirrorClampedSize,
    HaltedStartSessionSim.prepStartSpkClampedSize, HaltedStartSessionSim.drvBitSize,
    HaltedStartSessionSim.finishStartSpkHaltedClampedSize]
  omega

/-- Unconditional `GRedBounded` under `bhE2ECostBudget` for `kindRedHalted` with `mkKindSubprogramsHaltedClamped`. -/
theorem kindRedHalted_clamped_gRedBounded
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (smStep : HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT TrackInv)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    let qTot := b.q_total + qStart + qDR
    GRedBounded (kindRedHalted (mkKindSubprogramsHaltedClamped smStep b) b qStart qInst qep)
      (fun _ => 1) (fun _ => 0) qTot (2 * qTot) (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  dsimp only
  exact kindRedHalted_gRedBounded (mkKindSubprogramsHaltedClamped smStep b) b qStart qInst qep
    (b.q_total + qStart + qDR) (bhE2ECostBudget S b qStart qDR qInst qep ℓ)
    (totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ
      (b.q_total + qStart + qDR) _ _ (le_refl _)
      (mkKindSubprogramsHaltedClamped_endpointCost_le smStep b qStart qInst qep)
      (mkKindSubprogramsHaltedClamped_stepCost_le smStep b qStart qInst qep))
    (kindRedHalted_size_le_budget (mkKindSubprogramsHaltedClamped smStep b) b qStart qInst qep
      (bhE2ECostBudget S b qStart qDR qInst qep ℓ) 510000 530 (by omega) (by omega)
      (mkKindSubprogramsHaltedClamped_sizeBound_le smStep b qStart qDR qInst qep))

end ClampedHandshake

end Computational.Proofs.E2E.Dsl.KindRedHaltedInst
