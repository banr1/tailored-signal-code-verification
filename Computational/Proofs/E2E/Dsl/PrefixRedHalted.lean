/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1 -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Halted Multi-Session Two-Stage Prefix Reductions

Constructs the parametric halted two-stage prefix reduction `prefixRedHalted` over
`ReductionDsl.atomicE2EOps` alongside its shallow reference reduction `bhPrefixRedWithHalted`.
Establishes static query bounds, symbolic step-cost and syntax-size bounds, `GRed2Bounded`, and
Stage-2 per-instance `SM.MakesAtMostQueries`.
-/

public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.PrefixRedHalted

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp Mid CostedReduction
  TwoStageCostedReduction runFuel bits reductionSizeBudget OpsSizeHonest SampSizeHonest
  AllGameQueriesFit supportWhen atomicSig atomicE2EOps atomicE2EOps_sizeHonest
  atomicBaseSamplers_sizeHonest e2eKeyIndTargetIface e2eSessionTargetIface prefixCtxT
  keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec sidT sidV sidOfV
  smQT smQenc smRT smRdec GhostStT BV256 UniformSamplerTag AtomicUnifBase)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (GameState MakesAtMostQueries gameR)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSession (GRedBounded GRedCostByKind GRed2CostByKind)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes BHE2EDrvState BHE2ESmResp BHTargetQuery BHTargetResp
  BHPrefixCtx bhTargetGameSpec e2eTargetGameCodec bhTargetQenc bhTargetRdec bhFwdU bhLiftP
  BhShallowTwoStageRed bhShallowRunFuel bhShallowStepPreNonCtl bhShallowStepPreCtl
  bhShallowStepPostLocal bhShallowCheckExtSm bhShallowCommitExtSm bhShallowFinishPrefix
  bhIdKeyOf bhPackSmResp compositionLocalStart GRed2Bounded CompositionCostedReductions
  CompositionCostedReductionFamily CompositionCostedReductionsBounded
  CompositionCostedReductionFamilyBounded bhE2ECostBudget bhE2ECostBudgetByKind
  bhQueryKind bhKindCounts stageOneAsProbComp isSmTargetQuery
  bhClassifyTarget bhClassifyTargetOnly runFuel_queryBound_of_step_le
  isQueryBoundP_paused_of_mem_support_simulateQ_eval1)
open CryptoVerification.E2E.Costed (costedFits_iff_fits costedOpsSizeHonest_of_opsSizeHonest
  costedSampSizeHonest_of_sampSizeHonest gRedBounded_of_bounds)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (size_le_budget_of_log_cost bits_mono
  bits_pos bits_mul_le bits_add_le_two_mul_bits_add bits_succ_le)

/-- General `GRed2Bounded` constructor for unit-input boolean-output two-stage reductions. -/
theorem gRed2Bounded_of_bounds_general {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C0 : GameCodec S0 G} {ch : Ty S0}
    (R : TwoStageCostedReduction O I G C0 .unit .unit .bool ch .bool .bool)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ) (dflt : Bool)
    (hCost : R.totalCost q ≤ costBudget)
    (hSize : R.size ≤ reductionSizeBudget + 2 ^ 12 * bits costBudget)
    (hStage1Q : R.init.queries wTag wSamp + R.handlePre.queries wTag wSamp +
      R.chDone.queries wTag wSamp = 0)
    (hQueries : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GRed2Bounded R wTag wSamp q qOut costBudget dflt := by
  refine ⟨hCost, hSize, hStage1Q, hQueries,
    costedOpsSizeHonest_of_opsSizeHonest hO,
    costedSampSizeHonest_of_sampSizeHonest hS, ?_⟩
  intro B _hAdv A hA x _hx _widthB cm hcm
  have h1 := TwoStageCostedReduction.fits_eval1_when R hO hS B B 0
    (fun _ => trivial) A hA q 0 x trivial dflt cm hcm
  refine ⟨?_, fun _ _ _ _ => trivial⟩
  rw [costedFits_iff_fits]
  refine Ty.fits_mono ?_ _ _ h1.1
  have hnq : R.nq q ≤ R.totalCost q :=
    CryptoVerification.E2E.Costed.TwoStageCostedReduction.nq_le_totalCost R q
  have hnqB : R.nq q * B ≤ costBudget * B :=
    Nat.mul_le_mul_right B (le_trans hnq hCost)
  have hW : _widthB = 2 * (costBudget + q + 1) * (B + 1) := rfl
  rw [hW]
  nlinarith

theorem gRed2Bounded_atomic_of_bounds {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (R : TwoStageCostedReduction (atomicE2EOps ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool (prefixCtxT (ℓ := ℓ) (Pt := Pt)) .bool .bool)
    (q qOut costBudget : ℕ) (dflt : Bool)
    (hCost : R.totalCost q ≤ costBudget)
    (hSize : R.size ≤ reductionSizeBudget + 2 ^ 12 * bits costBudget)
    (hStage1Q : R.init.queries (fun _ => 1) (fun _ => 0) +
      R.handlePre.queries (fun _ => 1) (fun _ => 0) +
      R.chDone.queries (fun _ => 1) (fun _ => 0) = 0)
    (hQueries : R.totalQueries (fun _ => 1) (fun _ => 0) q ≤ qOut) :
    GRed2Bounded R (fun _ => 1) (fun _ => 0) q qOut costBudget dflt :=
  gRed2Bounded_of_bounds_general R (fun _ => 1) (fun _ => 0) q qOut costBudget dflt
    hCost hSize hStage1Q hQueries
    (atomicE2EOps_sizeHonest ℓ P C K decT encT)
    (atomicBaseSamplers_sizeHonest ℓ Pt)

/-- Assemble `CompositionCostedReductionsBounded` from component cost, size, and query bounds. -/
theorem compositionBounded_of_bounds {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (R : CompositionCostedReductions S ℓ P C K qep decT encT)
    (hKindCost : let qDR := ∑ k ∈ Finset.range qStart, qs k
      R.kindRed.totalCost (b.q_total + qStart + qDR) ≤
        bhE2ECostBudget S b qStart qDR (Finset.sup (Finset.range qStart) qs) qep ℓ)
    (hKindSize : let qDR := ∑ k ∈ Finset.range qStart, qs k
      R.kindRed.size ≤ reductionSizeBudget +
        2 ^ 12 * bits (bhE2ECostBudget S b qStart qDR (Finset.sup (Finset.range qStart) qs) qep ℓ))
    (hKindQ : let qTot := b.q_total + qStart + ∑ k ∈ Finset.range qStart, qs k
      R.kindRed.totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ 2 * qTot)
    (hPrefCost : let qDR := ∑ k ∈ Finset.range qStart, qs k
      ∀ k < qStart, (R.prefixRed k).totalCost (b.q_total + qStart + qDR) ≤
        bhE2ECostBudget S b qStart qDR (Finset.sup (Finset.range qStart) qs) qep ℓ)
    (hPrefSize : let qDR := ∑ k ∈ Finset.range qStart, qs k
      ∀ k < qStart, (R.prefixRed k).size ≤ reductionSizeBudget +
        2 ^ 12 * bits (bhE2ECostBudget S b qStart qDR (Finset.sup (Finset.range qStart) qs) qep ℓ))
    (hPrefQ1 : ∀ k < qStart,
      (R.prefixRed k).init.queries (fun _ => 1) (fun _ => 0) +
        (R.prefixRed k).handlePre.queries (fun _ => 1) (fun _ => 0) +
        (R.prefixRed k).chDone.queries (fun _ => 1) (fun _ => 0) = 0)
    (hPrefQ2 : let qTot := b.q_total + qStart + ∑ k ∈ Finset.range qStart, qs k
      ∀ k < qStart, (R.prefixRed k).totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ qTot)
    (hKindCostByKind : let qDR := ∑ k ∈ Finset.range qStart, qs k
      R.kindRed.CostBoundedByKind bhQueryKind (bhKindCounts b qStart qDR)
        (bhE2ECostBudgetByKind S b qStart qDR (Finset.sup (Finset.range qStart) qs) qep ℓ))
    (hKindQSum : let qSum := (List.ofFn (bhKindCounts b qStart (∑ k ∈ Finset.range qStart, qs k))).sum
      R.kindRed.totalQueries (fun _ => 1) (fun _ => 0) qSum ≤ 2 * qSum)
    (hPrefCostByKind : let qDR := ∑ k ∈ Finset.range qStart, qs k
      ∀ k < qStart, (R.prefixRed k).CostBoundedByKind bhQueryKind (bhKindCounts b qStart qDR)
        (bhE2ECostBudgetByKind S b qStart qDR (Finset.sup (Finset.range qStart) qs) qep ℓ))
    (hPrefQ2Sum : let qSum := (List.ofFn (bhKindCounts b qStart (∑ k ∈ Finset.range qStart, qs k))).sum
      ∀ k < qStart, (R.prefixRed k).totalQueries (fun _ => 1) (fun _ => 0) qSum ≤ qSum) :
    CompositionCostedReductionsBounded P C K qep decT encT b qStart qs R := by
  refine ⟨⟨?_, fun k hk => ?_⟩,
    ⟨⟨hKindCostByKind, hKindQSum⟩,
      fun k hk => ⟨hPrefCostByKind k hk, hPrefQ1 k hk, hPrefQ2Sum k hk⟩⟩⟩
  · exact gRedBounded_of_bounds R.kindRed (fun _ => 1) (fun _ => 0) _ _ _
      hKindCost hKindSize hKindQ
      (atomicE2EOps_sizeHonest ℓ P C K decT encT)
      (atomicBaseSamplers_sizeHonest ℓ Pt)
  · exact gRed2Bounded_atomic_of_bounds (R.prefixRed k) _ _ _ false
      (hPrefCost k hk) (hPrefSize k hk) (hPrefQ1 k hk) (hPrefQ2 k hk)

section ShallowHalted

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {SessH : Type}

@[expose] def bhShallowStepPreNonCtlHalted
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (σH : BHE2EDrvState S ℓ × List SessH) (q : BHTargetQuery S ℓ (BitVec 512)) :
    ProbComp (BHTargetResp ℓ × (BHE2EDrvState S ℓ × List SessH)) := do
  match q with
  | .inl (.inl kq) =>
    let (r, σ') ← bhShallowStepPreNonCtl P ki C K qep decT encT σH.1 (.inl (.inl kq))
    return (r, (σ', σH.2))
  | .inl (.inr _) => return (.inl (.inr none), σH)
  | .inr (i, sq) =>
    let (sr, σH') ← stepLocalSmH σH i sq
    return (.inr sr, σH')

@[expose] def bhShallowStepPreCtlHalted
    (localStartH : Bool → (BHE2EDrvState S ℓ × List SessH) → SignalPqxdh.SessionId S →
      ProbComp (Option ℕ × (BHE2EDrvState S ℓ × List SessH)))
    (k : ℕ) (σH : BHE2EDrvState S ℓ × List SessH) (sid : SignalPqxdh.SessionId S) :
    ProbComp ((Option ℕ × (BHE2EDrvState S ℓ × List SessH)) ⊕
      (BHPrefixCtx × (Option ℕ × (BHE2EDrvState S ℓ × List SessH)))) := do
  let (idx?, (σ', logs')) ← localStartH true σH sid
  if k < σ'.insts.length then
    let ctx : BHPrefixCtx := match σ'.insts[k]? with
      | some d => { idA := d.idA, idB := d.idB, spkCoins := d.spkCoins }
      | none => { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }
    let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
    return .inr (ctx, (idx?, ({ σ' with insts := insts', paused := true }, logs')))
  else return .inl (idx?, (σ', logs'))

@[expose] def bhShallowStepPostLocalHalted
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (localStartH : Bool → (BHE2EDrvState S ℓ × List SessH) → SignalPqxdh.SessionId S →
      ProbComp (Option ℕ × (BHE2EDrvState S ℓ × List SessH)))
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (σH : BHE2EDrvState S ℓ × List SessH) (q : BHTargetQuery S ℓ (BitVec 512)) :
    ProbComp (BHTargetResp ℓ × (BHE2EDrvState S ℓ × List SessH)) := do
  match q with
  | .inl (.inl kq) =>
    let (r, σ') ← bhShallowStepPostLocal P ki C K qep decT encT σH.1 (.inl (.inl kq))
    return (r, (σ', σH.2))
  | .inl (.inr sid) =>
    let (idx?, σH1) ← localStartH false σH sid
    return (.inl (.inr idx?), σH1)
  | .inr (i, sq) =>
    let (sr, σH') ← stepLocalSmH σH i sq
    return (.inr sr, σH')

@[expose] def bhPrefixHandlePreWithHalted (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (localStartH : Bool → (BHE2EDrvState S ℓ × List SessH) → SignalPqxdh.SessionId S →
      ProbComp (Option ℕ × (BHE2EDrvState S ℓ × List SessH)))
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (k : ℕ) (σH : BHE2EDrvState S ℓ × List SessH) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      ((BHTargetResp ℓ × (BHE2EDrvState S ℓ × List SessH)) ⊕
        (BHPrefixCtx × (Option ℕ × (BHE2EDrvState S ℓ × List SessH)))) :=
  match q with
  | .inl (.inl kq) => do
    let res ← bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreNonCtlHalted P ki C K qep decT encT stepLocalSmH σH (.inl (.inl kq)))
    return .inl res
  | .inl (.inr sid) => do
    let res ← bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreCtlHalted localStartH k σH sid)
    match res with
    | .inl ans => return .inl (.inl (.inr ans.1), ans.2)
    | .inr ctxAndDrv => return .inr ctxAndDrv
  | .inr iSq => do
    let res ← bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreNonCtlHalted P ki C K qep decT encT stepLocalSmH σH (.inr iSq))
    return .inl res

@[expose] def bhPrefixHandlePostWithHalted (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (localStartH : Bool → (BHE2EDrvState S ℓ × List SessH) → SignalPqxdh.SessionId S →
      ProbComp (Option ℕ × (BHE2EDrvState S ℓ × List SessH)))
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (k : ℕ) (σH : BHE2EDrvState S ℓ × List SessH) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (BHTargetResp ℓ × (BHE2EDrvState S ℓ × List SessH)) :=
  match q with
  | .inl kiOrCtl =>
    bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPostLocalHalted P ki C K qep decT encT localStartH stepLocalSmH σH (.inl kiOrCtl))
  | .inr (i, sq) =>
    match bhShallowCheckExtSm k σH.1 i sq with
    | .inl _ =>
      bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (bhShallowStepPostLocalHalted P ki C K qep decT encT localStartH stepLocalSmH σH (.inr (i, sq)))
    | .inr sq' => do
      let r ← (liftM
        ((unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).query
          (.inr sq')) :
        OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) _)
      let (resp, σ1) := bhShallowCommitExtSm k σH.1 sq' (bhPackSmResp sq' r)
      return (resp, (σ1, σH.2))

/-- Shallow two-stage halted prefix reference reduction maintaining per-session halted state `List SessH` alongside `BHE2EDrvState S ℓ`. -/
@[expose] def bhPrefixRedWithHalted (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (localStartH : Bool → (BHE2EDrvState S ℓ × List SessH) → SignalPqxdh.SessionId S →
      ProbComp (Option ℕ × (BHE2EDrvState S ℓ × List SessH)))
    (stepLocalSmH : BHE2EDrvState S ℓ × List SessH → ℕ →
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain →
      ProbComp (BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List SessH)))
    (k : ℕ) :
    BhShallowTwoStageRed (bhTargetGameSpec S ℓ (BitVec 512))
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (BHTargetQuery S ℓ (BitVec 512)) (BHTargetResp ℓ)
      Unit Unit Bool BHPrefixCtx Bool Bool (BHE2EDrvState S ℓ × List SessH) (Option ℕ) where
  qenc := bhTargetQenc
  rdec := bhTargetRdec
  init _ := pure ((), ({}, []))
  handlePre := bhPrefixHandlePreWithHalted S ℓ P ki C K qep decT encT localStartH stepLocalSmH k
  chDone _ _ := pure { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }
  resume σH p flip := pure (.inl (.inr p), ({ σH.1 with b := flip }, σH.2))
  handlePost := bhPrefixHandlePostWithHalted S ℓ P ki C K qep decT encT localStartH stepLocalSmH k
  finish σH b' flip :=
    bhLiftP (G := CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowFinishPrefix P σH.1 b' flip)

end ShallowHalted

section AtomicProgram

/-- Atomic `ReductionDsl` subprogram interface over `atomicE2EOps` and `e2eSessionTargetIface` used to assemble `prefixRedHalted`. -/
structure HaltedPrefixSubprograms (S : SignalPqxdh.Setup) {Pt : Type} (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (SessH : Type) where
  drvTy : Ty (atomicSig ℓ Pt)
  sessHTy : Ty (atomicSig ℓ Pt)
  drvEnc : BHE2EDrvState S ℓ → drvTy.denote
  sessHEnc : SessH → sessHTy.denote

  emptyDrvStateE : ∀ {Γ}, Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy
  emptyDrvStateCost : ℕ
  emptyDrvStateSize : ℕ
  emptyDrvStateE_cost : ∀ {Γ} (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool),
    (emptyDrvStateE bE).cost ≤ bE.cost + emptyDrvStateCost
  emptyDrvStateE_size : ∀ {Γ} (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool),
    (emptyDrvStateE bE).size ≤ bE.size + emptyDrvStateSize
  emptyDrvStateE_eval : ∀ {Γ} (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) (ρ : Env Γ),
    (emptyDrvStateE bE).eval ρ = drvEnc { b := bE.eval ρ }

  drvSetBitE : ∀ {Γ}, Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy
  drvSetBitCost : ℕ
  drvSetBitSize : ℕ
  drvSetBitE_cost : ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool),
    (drvSetBitE σE bE).cost ≤ σE.cost + bE.cost + drvSetBitCost
  drvSetBitE_size : ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool),
    (drvSetBitE σE bE).size ≤ σE.size + bE.size + drvSetBitSize
  drvSetBitE_eval : ∀ {Γ} (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (bE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool) (ρ : Env Γ) (σ : BHE2EDrvState S ℓ),
    σE.eval ρ = drvEnc σ →
    (drvSetBitE σE bE).eval ρ = drvEnc { σ with b := bE.eval ρ }

  defaultPrefixCtxE : ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (prefixCtxT (ℓ := ℓ) (Pt := Pt))
  defaultPrefixCtxCost : ℕ
  defaultPrefixCtxSize : ℕ
  defaultPrefixCtxE_cost : ∀ {Γ}, (defaultPrefixCtxE (Γ := Γ)).cost ≤ defaultPrefixCtxCost
  defaultPrefixCtxE_size : ∀ {Γ}, (defaultPrefixCtxE (Γ := Γ)).size ≤ defaultPrefixCtxSize
  defaultPrefixCtxE_eval : ∀ {Γ} (ρ : Env Γ),
    (defaultPrefixCtxE (Γ := Γ)).eval ρ = (bhIdKeyOf [], (bhIdKeyOf [], 0))

  kiStepC : SignalPqxdh.QueryBudget → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S) →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (e2eTargetGameCodec S ℓ Pt).R drvTy)
  kiStepCost : SignalPqxdh.QueryBudget → ℕ
  kiStepSize : SignalPqxdh.QueryBudget → ℕ
  kiStepC_cost : ∀ (b : SignalPqxdh.QueryBudget) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)),
    (kiStepC b σE kqE).cost ≤ σE.cost + kqE.cost + kiStepCost b
  kiStepC_size : ∀ (b : SignalPqxdh.QueryBudget) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)),
    (kiStepC b σE kqE).size ≤ σE.size + kqE.size + kiStepSize b
  kiStepC_queries : ∀ (b : SignalPqxdh.QueryBudget) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ),
    (kiStepC b σE kqE).queries w (fun _ => 0) = 0

  localStartHaltedC : SignalPqxdh.QueryBudget → ℕ → Bool → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S) →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (.opt .nat) (.prod drvTy (.list sessHTy)))
  localStartHaltedCost : SignalPqxdh.QueryBudget → ℕ → ℕ
  localStartHaltedSize : SignalPqxdh.QueryBudget → ℕ → ℕ
  localStartHaltedC_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)),
    (localStartHaltedC b qStart bm σHE sidE).cost ≤
      σHE.cost + sidE.cost + localStartHaltedCost b qStart
  localStartHaltedC_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S)),
    (localStartHaltedC b qStart bm σHE sidE).size ≤
      σHE.size + sidE.size + localStartHaltedSize b qStart
  localStartHaltedC_queries : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (bm : Bool) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (sidE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sidT (ℓ := ℓ) (Pt := Pt) S))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ),
    (localStartHaltedC b qStart bm σHE sidE).queries w (fun _ => 0) = 0

  promoteSlotKC : ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.sum (.prod (.opt .nat) drvTy)
        (.prod (prefixCtxT (ℓ := ℓ) (Pt := Pt)) (.prod (.opt .nat) drvTy)))
  promoteSlotKCost : ℕ → ℕ
  promoteSlotKSize : ℕ → ℕ
  promoteSlotKC_cost : ∀ (qStart : ℕ) {Γ}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy),
    (promoteSlotKC qStart kE idxOptE σE).cost ≤
      kE.cost + idxOptE.cost + σE.cost + promoteSlotKCost qStart
  promoteSlotKC_size : ∀ (qStart : ℕ) {Γ}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy),
    (promoteSlotKC qStart kE idxOptE σE).size ≤
      kE.size + idxOptE.size + σE.size + promoteSlotKSize qStart
  promoteSlotKC_queries : ∀ (qStart : ℕ) {Γ}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ),
    (promoteSlotKC qStart kE idxOptE σE).queries w (fun _ => 0) = 0

  extSmStepC : SignalPqxdh.QueryBudget → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)) →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) drvTy)
  extSmStepCost : SignalPqxdh.QueryBudget → ℕ → ℕ
  extSmStepSize : SignalPqxdh.QueryBudget → ℕ → ℕ
  extSmStepC_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (extSmStepC b qStart kE σE sqE).cost ≤
      kE.cost + σE.cost + sqE.cost + extSmStepCost b qStart
  extSmStepC_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (extSmStepC b qStart kE σE sqE).size ≤
      kE.size + σE.size + sqE.size + extSmStepSize b qStart
  extSmStepC_queries_one : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (kE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (extSmStepC b qStart kE σE sqE).queries (fun _ => 1) (fun _ => 0) ≤ 1

  haltedStepLocalSmC : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)) →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)) →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod drvTy (.list sessHTy)))
  haltedStepLocalSmCost : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ℕ
  haltedStepLocalSmSize : SignalPqxdh.QueryBudget → ℕ → ℕ → ℕ → ℕ
  haltedStepLocalSmC_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (haltedStepLocalSmC b qStart qDR qep σHE idxE sqE).cost ≤
      σHE.cost + idxE.cost + sqE.cost + haltedStepLocalSmCost b qStart qDR qep
  haltedStepLocalSmC_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt))),
    (haltedStepLocalSmC b qStart qDR qep σHE idxE sqE).size ≤
      σHE.size + idxE.size + sqE.size + haltedStepLocalSmSize b qStart qDR qep
  haltedStepLocalSmC_queries : ∀ (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {Γ}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (.prod drvTy (.list sessHTy)))
    (idxE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .nat)
    (sqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (smQT (ℓ := ℓ) (Pt := Pt)))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ),
    (haltedStepLocalSmC b qStart qDR qep σHE idxE sqE).queries w (fun _ => 0) = 0

  finishPrefixC : SignalPqxdh.QueryBudget → ℕ → ∀ {Γ},
    Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool →
    Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool →
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ .bool
  finishPrefixCost : SignalPqxdh.QueryBudget → ℕ → ℕ
  finishPrefixSize : SignalPqxdh.QueryBudget → ℕ → ℕ
  finishPrefixC_cost : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool),
    (finishPrefixC b qStart σE bOutE flipE).cost ≤
      σE.cost + bOutE.cost + flipE.cost + finishPrefixCost b qStart
  finishPrefixC_size : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool),
    (finishPrefixC b qStart σE bOutE flipE).size ≤
      σE.size + bOutE.size + flipE.size + finishPrefixSize b qStart
  finishPrefixC_queries : ∀ (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ drvTy)
    (bOutE flipE : Expr (atomicE2EOps ℓ P C K decT encT) Γ .bool)
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ),
    (finishPrefixC b qStart σE bOutE flipE).queries w (fun _ => 0) = 0

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}

abbrev drvHaltedTy (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH) :
    Ty (atomicSig ℓ Pt) :=
  .prod subs.drvTy (.list subs.sessHTy)

@[expose] def drvHaltedEnc (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (σH : BHE2EDrvState S ℓ × List SessH) : (drvHaltedTy subs).denote :=
  (subs.drvEnc σH.1, σH.2.map subs.sessHEnc)

@[expose] def prefixKiStepHaltedC (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) Γ
      (.prod (e2eTargetGameCodec S ℓ Pt).R (drvHaltedTy subs)) :=
  .bind (.ret (.pair σHE kqE))
    (.bind (subs.kiStepC b (.fst (.fst .v0)) (.snd .v0))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.fst .v1))))))

/-- Stage-1 handler of `prefixRedHalted`, promoting pre-`k` sessions and pausing once slot `k` is promoted. -/
@[expose] def prefixHandlePreHalted (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt)
      [drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
      (.sum (.prod (e2eTargetGameCodec S ℓ Pt).R (drvHaltedTy subs))
        (.prod (prefixCtxT (ℓ := ℓ) (Pt := Pt)) (.prod (.opt .nat) (drvHaltedTy subs)))) :=
  .caseSum .v1
    (.caseSum .v0
      (.bind (prefixKiStepHaltedC subs b .v2 .v0)
        (.ret (.inl .v0)))
      (.bind (subs.localStartHaltedC b qStart true .v2 .v0)
        (.bind
          (subs.promoteSlotKC qStart (.nat k) (.fst .v0) (.fst (.snd .v0)))
          (.caseSum .v0
            (.ret
              (.inl
                (.pair (.inl (.inr (.fst .v0)))
                  (.pair (.snd .v0) (.snd (.snd .v2))))))
            (.ret
              (.inr
                (.pair (.fst .v0)
                  (.pair (.fst (.snd .v0))
                    (.pair (.snd (.snd .v0)) (.snd (.snd .v2)))))))))))
    (.bind
      (subs.haltedStepLocalSmC b qStart qDR qep .v1 (.fst .v0) (.snd .v0))
      (.ret (.inl (.pair (.inr (.fst .v0)) (.snd .v0)))))

/-- Stage-2 handler of `prefixRedHalted`, routing session `k` externally and simulating sessions `i ≠ k` locally. -/
@[expose] def prefixHandlePostHalted (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt)
      [drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
      (.prod (e2eTargetGameCodec S ℓ Pt).R (drvHaltedTy subs)) :=
  .caseSum .v1
    (.caseSum .v0
      (prefixKiStepHaltedC subs b .v2 .v0)
      (.bind (subs.localStartHaltedC b qStart false .v2 .v0)
        (.ret (.pair (.inl (.inr (.fst .v0))) (.snd .v0)))))
    (.ite (.eqN (.fst .v0) (.nat k))
      (.bind (subs.extSmStepC b qStart (.nat k) (.fst .v1) (.snd .v0))
        (.ret (.pair (.inr (.fst .v0)) (.pair (.snd .v0) (.snd .v2)))))
      (.bind (subs.haltedStepLocalSmC b qStart qDR qep .v1 (.fst .v0) (.snd .v0))
        (.ret (.pair (.inr (.fst .v0)) (.snd .v0)))))

/-- Two-stage halted per-session prefix reduction over `atomicE2EOps` and `e2eSessionTargetIface`. -/
@[expose, reducible] def prefixRedHalted
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    TwoStageCostedReduction (atomicE2EOps ℓ P C K decT encT)
      (e2eSessionTargetIface ℓ Pt)
      (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
      .unit .unit .bool (prefixCtxT (ℓ := ℓ) (Pt := Pt)) .bool .bool where
  σ := drvHaltedTy subs
  π := .opt .nat
  init := .ret (.pair .unit (.pair (subs.emptyDrvStateE (.bool false)) .nil))
  handlePre := prefixHandlePreHalted subs b qStart qDR qep k
  chDone := .ret subs.defaultPrefixCtxE
  resume := .ret (.pair (.inl (.inr .v1)) (.pair (subs.drvSetBitE (.fst .v0) .v2) (.snd .v0)))
  handlePost := prefixHandlePostHalted subs b qStart qDR qep k
  finish := subs.finishPrefixC b qStart (.fst .v0) .v1 .v2

theorem prefixKiStepHaltedC_queries
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (prefixKiStepHaltedC subs b σHE kqE).queries w (fun _ => 0) = 0 := by
  simp [prefixKiStepHaltedC, Comp.queries, subs.kiStepC_queries]

theorem prefixHandlePreHalted_queries
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (w : (e2eSessionTargetIface ℓ Pt).Tag → ℕ) :
    (prefixHandlePreHalted subs b qStart qDR qep k).queries w (fun _ => 0) = 0 := by
  simp [prefixHandlePreHalted, Comp.queries, prefixKiStepHaltedC_queries,
    subs.localStartHaltedC_queries, subs.promoteSlotKC_queries, subs.haltedStepLocalSmC_queries]

theorem prefixHandlePostHalted_queries_le
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    (prefixHandlePostHalted subs b qStart qDR qep k).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
  have hext := subs.extSmStepC_queries_one b qStart
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) (.nat k) (.fst .v1) (.snd .v0)
  dsimp only [Expr.v0, Expr.v1] at hext
  simp only [prefixHandlePostHalted, Comp.queries, prefixKiStepHaltedC_queries,
    subs.localStartHaltedC_queries, subs.haltedStepLocalSmC_queries, Expr.v0, Expr.v1]
  omega

theorem prefixRedHalted_stage1Queries
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ) :
    (prefixRedHalted subs b qStart qDR qep k).init.queries (fun _ => 1) (fun _ => 0) +
      (prefixRedHalted subs b qStart qDR qep k).handlePre.queries (fun _ => 1) (fun _ => 0) +
      (prefixRedHalted subs b qStart qDR qep k).chDone.queries (fun _ => 1) (fun _ => 0) = 0 := by
  simp [prefixRedHalted, Comp.queries, prefixHandlePreHalted_queries]

theorem prefixRedHalted_totalQueries_le
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k qTot : ℕ) :
    (prefixRedHalted subs b qStart qDR qep k).totalQueries (fun _ => 1) (fun _ => 0) qTot ≤ qTot := by
  have hpre := prefixHandlePreHalted_queries subs b qStart qDR qep k (fun _ => 1)
  have hpost := prefixHandlePostHalted_queries_le subs b qStart qDR qep k
  have hfin := subs.finishPrefixC_queries b qStart
    (Γ := [drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2 (fun _ => 1)
  dsimp only [TwoStageCostedReduction.totalQueries, prefixRedHalted]
  have hinit :
      (Comp.ret (.pair .unit (.pair (subs.emptyDrvStateE (.bool false)) .nil)) :
        Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt) [.unit]
          (.prod .unit (drvHaltedTy subs))).queries (fun _ => 1) (fun _ => 0) = 0 := by
    simp [Comp.queries]
  have hch :
      (Comp.ret subs.defaultPrefixCtxE :
        Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt)
          [drvHaltedTy subs, .bool] (prefixCtxT (ℓ := ℓ) (Pt := Pt))).queries
        (fun _ => 1) (fun _ => 0) = 0 := by
    simp [Comp.queries]
  have hres :
      (Comp.ret (.pair (.inl (.inr .v1)) (.pair (subs.drvSetBitE (.fst .v0) .v2) (.snd .v0))) :
        Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt)
          [drvHaltedTy subs, .opt .nat, .bool]
          (.prod (e2eTargetGameCodec S ℓ Pt).R (drvHaltedTy subs))).queries
        (fun _ => 1) (fun _ => 0) = 0 := by
    simp [Comp.queries]
  rw [hinit, hpre, hch, hres, hfin]
  simp only [Nat.zero_max, Nat.zero_add, Nat.add_zero]
  exact Nat.le_trans (Nat.mul_le_mul_left qTot hpost) (by simp)

theorem prefixKiStepHaltedC_cost
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (prefixKiStepHaltedC subs b σHE kqE).cost ≤
      σHE.cost + kqE.cost + subs.kiStepCost b + 24 := by
  have hk := subs.kiStepC_cost b
    (Γ := Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ)
    (.fst (.fst .v0)) (.snd .v0)
  dsimp only [prefixKiStepHaltedC, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hk ⊢
  omega

theorem prefixKiStepHaltedC_size
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σHE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvHaltedTy subs))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S)) :
    (prefixKiStepHaltedC subs b σHE kqE).size ≤
      σHE.size + kqE.size + subs.kiStepSize b + 24 := by
  have hk := subs.kiStepC_size b
    (Γ := Ty.prod (drvHaltedTy subs) (keyIndQT (ℓ := ℓ) (Pt := Pt) S) :: Γ)
    (.fst (.fst .v0)) (.snd .v0)
  dsimp only [prefixKiStepHaltedC, Comp.size, Expr.size, Expr.v0, Expr.v1] at hk ⊢
  omega

/-- Endpoint leaf step-cost upper bound for `prefixRedHalted`. -/
@[expose] def haltedPrefixEndpointCost
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) : ℕ :=
  subs.emptyDrvStateCost + subs.defaultPrefixCtxCost + subs.drvSetBitCost +
    subs.finishPrefixCost b qStart + 60

/-- Per-query leaf step-cost upper bound for `prefixRedHalted` at `k < qStart`. -/
@[expose] def haltedPrefixStepCost
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  subs.kiStepCost b +
    subs.localStartHaltedCost b qStart +
    subs.promoteSlotKCost qStart +
    subs.extSmStepCost b qStart +
    subs.haltedStepLocalSmCost b qStart qDR qep +
    2 * qStart + 180

theorem prefixHandlePreHalted_cost_le
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixHandlePreHalted subs b qStart qDR qep k).cost + 64 ≤
      haltedPrefixStepCost subs b qStart qDR qep := by
  have hbits : bits k ≤ qStart := le_trans (CryptoVerification.E2E.Costed.bits_le_self_add_one k) hk
  have hki := prefixKiStepHaltedC_cost subs b
    (Γ := [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hloc := subs.localStartHaltedC_cost b qStart true
    (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hprom := subs.promoteSlotKC_cost qStart
    (Γ := [Ty.prod (.opt .nat) (drvHaltedTy subs), sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q])
    (.nat k) (.fst .v0) (.fst (.snd .v0))
  have hsm := subs.haltedStepLocalSmC_cost b qStart qDR qep
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePreHalted, haltedPrefixStepCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

theorem prefixHandlePostHalted_cost_le
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixHandlePostHalted subs b qStart qDR qep k).cost + 64 ≤
      haltedPrefixStepCost subs b qStart qDR qep := by
  have hbits : bits k ≤ qStart := le_trans (CryptoVerification.E2E.Costed.bits_le_self_add_one k) hk
  have hki := prefixKiStepHaltedC_cost subs b
    (Γ := [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hloc := subs.localStartHaltedC_cost b qStart false
    (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hext := subs.extSmStepC_cost b qStart
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) (.nat k) (.fst .v1) (.snd .v0)
  have hsm := subs.haltedStepLocalSmC_cost b qStart qDR qep
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [prefixHandlePostHalted, haltedPrefixStepCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

theorem prefixRedHalted_totalCost_le_leaf
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixRedHalted subs b qStart qDR qep k).totalCost qTot ≤
      haltedPrefixEndpointCost subs b qStart +
        qTot * haltedPrefixStepCost subs b qStart qDR qep := by
  have hempty := subs.emptyDrvStateE_cost (Γ := [.unit]) (.bool false)
  have hch := subs.defaultPrefixCtxE_cost (Γ := [drvHaltedTy subs, .bool])
  have hres := subs.drvSetBitE_cost (Γ := [drvHaltedTy subs, .opt .nat, .bool]) (.fst .v0) .v2
  have hfin := subs.finishPrefixC_cost b qStart
    (Γ := [drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2
  have hpre := prefixHandlePreHalted_cost_le subs b qStart qDR qep hk
  have hpost := prefixHandlePostHalted_cost_le subs b qStart qDR qep hk
  have hcc : (e2eTargetGameCodec S ℓ Pt).codecCost ≤ 64 := by
    dsimp [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec]; omega
  have hstep :
      max 1 (max (prefixHandlePreHalted subs b qStart qDR qep k).cost
          (prefixHandlePostHalted subs b qStart qDR qep k).cost +
          (e2eTargetGameCodec S ℓ Pt).codecCost) ≤
        haltedPrefixStepCost subs b qStart qDR qep := by
    have hpos : 1 ≤ haltedPrefixStepCost subs b qStart qDR qep := by
      unfold haltedPrefixStepCost; omega
    omega
  have hmul :
      qTot * max 1 (max (prefixHandlePreHalted subs b qStart qDR qep k).cost
          (prefixHandlePostHalted subs b qStart qDR qep k).cost +
          (e2eTargetGameCodec S ℓ Pt).codecCost) ≤
        qTot * haltedPrefixStepCost subs b qStart qDR qep :=
    Nat.mul_le_mul_left qTot hstep
  rw [TwoStageCostedReduction.totalCost]
  have hu : (e2eSessionTargetIface ℓ Pt).uCost = 1 := rfl
  rw [hu]
  dsimp only [prefixRedHalted, haltedPrefixEndpointCost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2] at hempty hch hres hfin hmul ⊢
  omega

/-- Leaf syntax-size upper bound for `prefixRedHalted` at `k < qStart`. -/
@[expose] def haltedPrefixSizeBound
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) : ℕ :=
  subs.emptyDrvStateSize +
    subs.defaultPrefixCtxSize +
    subs.drvSetBitSize +
    subs.finishPrefixSize b qStart +
    2 * subs.kiStepSize b +
    2 * subs.localStartHaltedSize b qStart +
    subs.promoteSlotKSize qStart +
    subs.extSmStepSize b qStart +
    2 * subs.haltedStepLocalSmSize b qStart qDR qep +
    3 * bits qStart + 200

theorem prefixRedHalted_size_le_leaf
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep : ℕ) {k : ℕ} (hk : k < qStart) :
    (prefixRedHalted subs b qStart qDR qep k).size ≤
      haltedPrefixSizeBound subs b qStart qDR qep := by
  have hbk : bits k ≤ bits qStart := bits_mono (Nat.le_of_lt hk)
  have hempty := subs.emptyDrvStateE_size (Γ := [.unit]) (.bool false)
  have hch := subs.defaultPrefixCtxE_size (Γ := [drvHaltedTy subs, .bool])
  have hres := subs.drvSetBitE_size (Γ := [drvHaltedTy subs, .opt .nat, .bool]) (.fst .v0) .v2
  have hfin := subs.finishPrefixC_size b qStart
    (Γ := [drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2
  have hki := prefixKiStepHaltedC_size subs b
    (Γ := [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hlocT := subs.localStartHaltedC_size b qStart true
    (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hlocF := subs.localStartHaltedC_size b qStart false
    (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0
  have hprom := subs.promoteSlotKC_size qStart
    (Γ := [Ty.prod (.opt .nat) (drvHaltedTy subs), sidT (ℓ := ℓ) (Pt := Pt) S,
      Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
      drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q])
    (.nat k) (.fst .v0) (.fst (.snd .v0))
  have hext := subs.extSmStepC_size b qStart
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) (.nat k) (.fst .v1) (.snd .v0)
  have hsm := subs.haltedStepLocalSmC_size b qStart qDR qep
    (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
      (e2eTargetGameCodec S ℓ Pt).Q]) .v1 (.fst .v0) (.snd .v0)
  dsimp only [TwoStageCostedReduction.size, prefixRedHalted, prefixHandlePreHalted,
    prefixHandlePostHalted, haltedPrefixSizeBound, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2] at *
  omega

theorem prefixRedHalted_size_le_budget
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep costBudget C₀ C₁ : ℕ)
    {k : ℕ} (hk : k < qStart)
    (h₀ : C₀ ≤ 2 ^ 22) (h₁ : C₁ ≤ 2 ^ 11)
    (hLeaf : haltedPrefixSizeBound subs b qStart qDR qep ≤ C₀ + C₁ * bits costBudget) :
    (prefixRedHalted subs b qStart qDR qep k).size ≤
      reductionSizeBudget + 2 ^ 12 * bits costBudget :=
  size_le_budget_of_log_cost h₀ h₁
    (le_trans (prefixRedHalted_size_le_leaf subs b qStart qDR qep hk) hLeaf)

/-- `GRed2Bounded` certificate for `prefixRedHalted` under `costBudget`. -/
theorem prefixRedHalted_gRed2Bounded
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot costBudget : ℕ)
    {k : ℕ} (hk : k < qStart)
    (hCost :
      haltedPrefixEndpointCost subs b qStart +
        qTot * haltedPrefixStepCost subs b qStart qDR qep ≤ costBudget)
    (hSize :
      (prefixRedHalted subs b qStart qDR qep k).size ≤
        reductionSizeBudget + 2 ^ 12 * bits costBudget) :
    GRed2Bounded (prefixRedHalted subs b qStart qDR qep k)
      (fun _ => 1) (fun _ => 0) qTot qTot costBudget false :=
  gRed2Bounded_atomic_of_bounds (prefixRedHalted subs b qStart qDR qep k)
    qTot qTot costBudget false
    (le_trans (prefixRedHalted_totalCost_le_leaf subs b qStart qDR qep qTot hk) hCost)
    hSize
    (prefixRedHalted_stage1Queries subs b qStart qDR qep k)
    (prefixRedHalted_totalQueries_le subs b qStart qDR qep k qTot)

private theorem isQueryBoundP_sessionTargetIface_fwdU (n : ℕ) :
    ((e2eSessionTargetIface ℓ Pt).fwdU n).IsQueryBoundP (isSmTargetQuery ℓ) 0 :=
  (isQueryBoundP_query_iff
    (spec := unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (isSmTargetQuery ℓ) (Sum.inl n) 0).2 (by simp [isSmTargetQuery])

private theorem hw_sessionTargetIface :
    ∀ (g : (e2eSessionTargetIface ℓ Pt).Tag) (x : ((e2eSessionTargetIface ℓ Pt).dom g).denote),
      isSmTargetQuery ℓ ((e2eSessionTargetIface ℓ Pt).enc g x) → 1 ≤ (fun _ => 1) g :=
  fun _ _ _ => le_rfl

theorem prefixHandlePreHalted_eval_ki
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (drvHaltedTy subs).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    (prefixHandlePreHalted subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl kq))) .nil)) =
      ((prefixKiStepHaltedC subs b
          (Γ := [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
            Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
            drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0).eval
        (.cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
          (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))) >>=
        fun v => pure (.inl v)) := rfl

theorem prefixHandlePreHalted_eval_ctl
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (drvHaltedTy subs).denote) (sid : SignalPqxdh.SessionId S) :
    (prefixHandlePreHalted subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inr (.startDR sid)))) .nil)) =
      ((subs.localStartHaltedC b qStart true
          (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
            Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
            drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0).eval
        (.cons (sidV sid) (.cons (Sum.inr (sidV sid))
          (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))) >>= fun x =>
        (subs.promoteSlotKC qStart
          (Γ := [Ty.prod (.opt .nat) (drvHaltedTy subs), sidT (ℓ := ℓ) (Pt := Pt) S,
            Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
            drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q])
          (.nat k) (.fst .v0) (.fst (.snd .v0))).eval
          (.cons x (.cons (sidV sid) (.cons (Sum.inr (sidV sid))
            (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil))))) >>= fun v =>
        match v with
        | .inl ans => pure (.inl ((.inl (.inr ans.1), (ans.2, x.2.2))))
        | .inr pause => pure (.inr (pause.1, (pause.2.1, (pause.2.2, x.2.2))))) := by
  dsimp only [prefixHandlePreHalted, e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec,
    Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get]
  refine bind_congr fun x => bind_congr fun v => ?_
  cases v <;> rfl

theorem prefixHandlePreHalted_eval_sm
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (drvHaltedTy subs).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (prefixHandlePreHalted subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inr (i, sq))) .nil)) =
      ((subs.haltedStepLocalSmC b qStart qDR qep
          (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
            (e2eTargetGameCodec S ℓ Pt).Q]) .v1 (.fst .v0) (.snd .v0)).eval
        (.cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))) >>=
        fun v => pure (.inl (.inr v.1, v.2))) := rfl

theorem prefixHandlePostHalted_eval_ki
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (drvHaltedTy subs).denote) (kq : SignalPqxdh.KeyIndQuery S) :
    (prefixHandlePostHalted subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inl kq))) .nil)) =
      (prefixKiStepHaltedC subs b
          (Γ := [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
            Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
            drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0).eval
        (.cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
          (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))) := rfl

theorem prefixHandlePostHalted_eval_ctl
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (drvHaltedTy subs).denote) (sid : SignalPqxdh.SessionId S) :
    (prefixHandlePostHalted subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inl (.inr (.startDR sid)))) .nil)) =
      ((subs.localStartHaltedC b qStart false
          (Γ := [sidT (ℓ := ℓ) (Pt := Pt) S,
            Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
            drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]) .v2 .v0).eval
        (.cons (sidV sid) (.cons (Sum.inr (sidV sid))
          (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))) >>=
        fun v => pure (.inl (.inr v.1), v.2)) := rfl

theorem prefixHandlePostHalted_eval_sm
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (drvHaltedTy subs).denote) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (prefixHandlePostHalted subs b qStart qDR qep k).eval
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inr (i, sq))) .nil)) =
      (if decide (i = k) = true then
        (subs.extSmStepC b qStart
            (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
              (e2eTargetGameCodec S ℓ Pt).Q]) (.nat k) (.fst .v1) (.snd .v0)).eval
          (.cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))) >>=
          fun v => pure (.inr v.1, (v.2, s.2))
       else
        (subs.haltedStepLocalSmC b qStart qDR qep
            (Γ := [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
              (e2eTargetGameCodec S ℓ Pt).Q]) .v1 (.fst .v0) (.snd .v0)).eval
          (.cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))) >>=
          fun v => pure (.inr v.1, v.2)) := rfl

theorem isQueryBoundP_prefixHandlePostHalted_eval
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep k : ℕ)
    (s : (drvHaltedTy subs).denote)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    ((prefixHandlePostHalted subs b qStart qDR qep k).eval
      (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil))).IsQueryBoundP
      (isSmTargetQuery ℓ)
      (if bhClassifyTargetOnly (fun _ => false) (fun _ => false) (fun i => i == k) t then 1 else 0) := by
  have hU := isQueryBoundP_sessionTargetIface_fwdU (ℓ := ℓ) (Pt := Pt)
  have hw := hw_sessionTargetIface (ℓ := ℓ) (Pt := Pt)
  rcases t with (kq | cq) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    rw [prefixHandlePostHalted_eval_ki]
    let Γ_ki : List (Ty (atomicSig ℓ Pt)) :=
      [keyIndQT (ℓ := ℓ) (Pt := Pt) S,
        Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
        drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
    let ρ_ki : Env Γ_ki :=
      .cons (keyIndQenc kq) (.cons (Sum.inl (keyIndQenc kq))
        (.cons s (.cons (Sum.inl (Sum.inl (keyIndQenc kq))) .nil)))
    have hq := prefixKiStepHaltedC_queries subs b (Γ := Γ_ki) .v2 .v0 (fun _ => 1)
    exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (prefixKiStepHaltedC subs b (Γ := Γ_ki) .v2 .v0) ρ_ki).mono (by rw [hq])
  · rcases cq with ⟨sid⟩
    simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte]
    rw [prefixHandlePostHalted_eval_ctl]
    let Γ_ctl : List (Ty (atomicSig ℓ Pt)) :=
      [sidT (ℓ := ℓ) (Pt := Pt) S,
        Ty.sum (keyIndQT (ℓ := ℓ) (Pt := Pt) S) (sidT (ℓ := ℓ) (Pt := Pt) S),
        drvHaltedTy subs, (e2eTargetGameCodec S ℓ Pt).Q]
    let ρ_ctl : Env Γ_ctl :=
      .cons (sidV sid) (.cons (Sum.inr (sidV sid))
        (.cons s (.cons (Sum.inl (Sum.inr (sidV sid))) .nil)))
    have hq := subs.localStartHaltedC_queries b qStart false (Γ := Γ_ctl) .v2 .v0 (fun _ => 1)
    have hc := (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (subs.localStartHaltedC b qStart false (Γ := Γ_ctl) .v2 .v0) ρ_ctl).mono (by rw [hq])
    exact (isQueryBoundP_bind hc (fun v _ =>
      isQueryBoundP_pure (isSmTargetQuery ℓ)
        ((Sum.inl (Sum.inr v.1) : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2) 0)).mono (by omega)
  · simp only [bhClassifyTargetOnly]
    by_cases hp : (i == k) = true
    · simp only [hp, ↓reduceIte]
      have hpost := prefixHandlePostHalted_queries_le subs b qStart qDR qep k
      exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
        (prefixHandlePostHalted subs b qStart qDR qep k)
        (.cons s (.cons ((e2eTargetGameCodec S ℓ Pt).qenc (.inr (i, sq))) .nil))).mono hpost
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hne : i ≠ k := fun heq => hp (beq_iff_eq.mpr heq)
      have hdec : decide (i = k) = false := decide_eq_false hne
      rw [prefixHandlePostHalted_eval_sm, hdec]
      simp only [Bool.false_eq_true, ↓reduceIte]
      let Γ_sm : List (Ty (atomicSig ℓ Pt)) :=
        [Ty.prod .nat (smQT (ℓ := ℓ) (Pt := Pt)), drvHaltedTy subs,
          (e2eTargetGameCodec S ℓ Pt).Q]
      let ρ_sm : Env Γ_sm :=
        .cons (i, smQenc sq) (.cons s (.cons (Sum.inr (i, smQenc sq)) .nil))
      have hq := subs.haltedStepLocalSmC_queries b qStart qDR qep
        (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0) (fun _ => 1)
      have hc := (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
        (subs.haltedStepLocalSmC b qStart qDR qep (Γ := Γ_sm) .v1 (.fst .v0) (.snd .v0))
        ρ_sm).mono (by rw [hq])
      exact (isQueryBoundP_bind hc (fun v _ =>
        isQueryBoundP_pure (isSmTargetQuery ℓ)
          ((Sum.inr v.1 : (e2eTargetGameCodec S ℓ Pt).R.denote), v.2) 0)).mono (by omega)

/-- Stage 2 of `prefixRedHalted` makes at most `qsK` queries to `SM.spec` whenever `B_A` makes at most `qsK` queries to session `k`. -/
theorem prefixRedHalted_makesAtMostQueries
    (subs : HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep qTot k qsK : ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hInst : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      qsK)
    (o : (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote ×
      Mid (bhTargetGameSpec S ℓ (BitVec 512)) Bool
        (Option ℕ) (drvHaltedTy subs).denote (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote)
    (ho : o ∈ support (stageOneAsProbComp
      ((prefixRedHalted subs b qStart qDR qep k).eval1 (fun _ => B_A) () qTot false)))
    (flip : Bool) :
    MakesAtMostQueries
      ((prefixRedHalted subs b qStart qDR qep k).eval2 o.2 flip qTot false) qsK := by
  have hU := isQueryBoundP_sessionTargetIface_fwdU (ℓ := ℓ) (Pt := Pt)
  have hw := hw_sessionTargetIface (ℓ := ℓ) (Pt := Pt)
  have hfin : ∀ (s_out : (drvHaltedTy subs).denote) (b_out : Bool),
      ((prefixRedHalted subs b qStart qDR qep k).finish.eval
        (.cons s_out (.cons b_out (.cons flip .nil)))).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    intro s_out b_out
    have hq := subs.finishPrefixC_queries b qStart
      (Γ := [drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2 (fun _ => 1)
    exact (Comp.queryBound_eval (isSmTargetQuery ℓ) (fun _ => 1) (fun _ => 0) hw hU
      (subs.finishPrefixC b qStart (Γ := [drvHaltedTy subs, .bool, .bool]) (.fst .v0) .v1 .v2)
      (.cons s_out (.cons b_out (.cons flip .nil)))).mono (by rw [hq])
  have hgoal :
      ((prefixRedHalted subs b qStart qDR qep k).eval2 o.2 flip qTot false).IsQueryBoundP
        (isSmTargetQuery ℓ) qsK →
      MakesAtMostQueries
        ((prefixRedHalted subs b qStart qDR qep k).eval2 o.2 flip qTot false) qsK := by
    intro hqb
    unfold MakesAtMostQueries IsQueryBoundP at hqb ⊢
    convert hqb using 1 <;>
      (funext x qb; rcases x with _ | _ <;> simp [isSmTargetQuery])
  apply hgoal
  rcases o with ⟨c0, m⟩
  dsimp only
  cases m with
  | done b_out s_out =>
    dsimp only [TwoStageCostedReduction.eval2]
    rw [pure_bind]
    exact (hfin s_out b_out).mono (Nat.zero_le _)
  | paused t c p s_p cont =>
    have hcont : ∀ v,
        (cont v).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
          qsK :=
      isQueryBoundP_paused_of_mem_support_simulateQ_eval1
        (prefixRedHalted subs b qStart qDR qep k) _
        (fun _ => B_A) () qTot false qsK (fun _ => hInst)
        c0 t c p s_p cont ho
    let s₁ : (drvHaltedTy subs).denote :=
      ((subs.drvSetBitE (Γ := [drvHaltedTy subs, .opt .nat, .bool]) (.fst .v0) .v2).eval
        (.cons s_p (.cons p (.cons flip .nil))), s_p.2)
    have hres_eval :
        (prefixRedHalted subs b qStart qDR qep k).resume.eval
          (.cons s_p (.cons p (.cons flip .nil))) =
        pure ((Sum.inl (Sum.inr p) : (e2eTargetGameCodec S ℓ Pt).R.denote), s₁) := rfl
    have hfuel := runFuel_queryBound_of_step_le
      (C_codec := e2eTargetGameCodec S ℓ Pt)
      (prefixHandlePostHalted subs b qStart qDR qep k)
      hU
      (fun t' s' =>
        isQueryBoundP_prefixHandlePostHalted_eval subs b qStart qDR qep k s' t')
      false
      (q := qsK)
      (by
        have hc0 := hcont ((e2eTargetGameCodec S ℓ Pt).rdec t (.inl (.inr p)))
        unfold IsQueryBoundP at hc0 ⊢
        convert hc0 using 1 <;>
          (funext x qb; rcases x with _ | _ <;> simp [bhClassifyTarget]))
      qTot s₁
    dsimp only [TwoStageCostedReduction.eval2]
    rw [hres_eval, pure_bind]
    exact (isQueryBoundP_bind hfuel (fun x _ => hfin x.2 x.1)).mono (by omega)

end AtomicProgram

end Computational.Proofs.E2E.Dsl.PrefixRedHalted
