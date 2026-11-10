/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop2
public import Computational.Proofs.E2E.SpkHop1D
public import Computational.Proofs.ReductionDsl.SpkHop2Red
public import Computational.Proofs.ReductionDsl.SpkLeakRedU
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.E2E.SpkCostedEval
import Computational.Proofs.E2E.SpkHop1InitBridge
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
public import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg
public import Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg
public import Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedTier2Prog
public import Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog
public import Computational.Specifications.Session.StatementSpkModel

/-!
# Leaked-signed-pre-key Double Ratchet session reductions and terminal hybrid bound

**Checked by Lean.** Every theorem in this file depends only on
(`propext`, `Classical.choice`, `Quot.sound`).

Proves the length side conditions at `paramsIdsWithSpqr`, the `configRefuseEarlyBobCorr` config
rewrite (`DEV-LS33`, `DEV-LS34`), the costed SPK reduction bundle `mkSpkCostedReds` with its
size/cost/evaluation bridges, and the terminal Hop-2 hybrid bound `evalDist_hop2PrfRedK_last_le`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.HeadlineSpk

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CryptoGames.MACScheme HMAC CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq
  CryptoVerification.E2E.SpkHop1 CryptoVerification.E2E.SpkHop2
open CryptoGames.CKA (DHFun)

/-! ## Side conditions at `paramsIds` -/

theorem addrsE_length (uuidParse : UuidParser) (s r : Party) (a : List (BitVec 8))
    (h : serializedPartyAddresses uuidParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : serviceIdParse uuidParse (utf8 (partyAddressName s)) <;>
    cases hr : serviceIdParse uuidParse (utf8 (partyAddressName r)) <;> simp_all [addrBytes]
  subst h
  simp

theorem lengthsOk_paramsIdsWithSpqr {PQC : Type} (C : Crypto) (spqr : Spqr Bytes PQC)
    (idA idB : IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 2 ^ 31)
    (hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29) :
    LengthsOk (paramsIdsWithSpqr C spqr idA idB) ℓ := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro st rq st' salt msg h
    exact hLspqr st rq st' salt msg h
  · intro a h
    rw [addrsE_length _ _ _ a h]; decide
  · intro a h
    rw [addrsE_length _ _ _ a h]; decide

@[simp] theorem configSpkS_eq_configR1OnCurveSpk {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) {St Msg : Type} :
    (configRefuseEarlyBobCorr decT encT : SM.ConfigR St Msg Bytes) =
      configR1OnCurveSpk (ratchetKeyAdmissible protoSignalCodec decT encT) := rfl

/-! ## Costed SPK reduction bundle -/

set_option linter.unusedSectionVars false

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

/-- Hop-3 uniform-scalar wrapper `spkLeakRedU` expressed over `ReductionDsl.atomicPureOps ℓ Pt`. -/
def spkLeakRedUAtomicProg (ℓ : ℕ := 0) : SpkLeakRedUProg Pt ℓ where
  σ := .unit
  init :=
    .bind (.sample (ReductionDsl.UniformSamplerTag.base ReductionDsl.AtomicBaseUnif.bv256) .unit)
      (.ret (.pair (.var .zero) .unit))
  handle :=
    .bind (.query () (.var (.succ .zero)))
      (.ret (.pair (.var .zero) .unit))
  finish := .ret (.var (.succ .zero))

@[simp] private theorem spkEnv_get_zero {S : ReductionDsl.Sig} {Γ : List (ReductionDsl.Ty S)}
    {t : ReductionDsl.Ty S} (x : t.denote) (ρ : ReductionDsl.Env Γ) :
    (ReductionDsl.Env.cons x ρ).get ReductionDsl.Var.zero = x := rfl

@[simp] private theorem spkEnv_get_succ {S : ReductionDsl.Sig} {Γ : List (ReductionDsl.Ty S)}
    {t u : ReductionDsl.Ty S} (x : u.denote) (ρ : ReductionDsl.Env Γ)
    (v : ReductionDsl.Var Γ t) :
    (ReductionDsl.Env.cons x ρ).get (ReductionDsl.Var.succ v) = ρ.get v := rfl

private theorem spkSimulateQ_run_StateT_of_step {κ : Type} {spec : OracleSpec κ} {m : Type → Type}
    [Monad m] [LawfulMonad m] {σ α : Type}
    {impl : QueryImpl spec (StateT σ m)} {qi : QueryImpl spec m}
    (hstep : ∀ t s, (impl t).run s = (fun x => (x, s)) <$> qi t)
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run s = (fun x => (x, s)) <$> simulateQ qi oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind]
    change ((impl t).run s >>= fun p => (simulateQ impl (mx p.1)).run p.2) =
      (fun x => (x, s)) <$> (qi t >>= fun u => simulateQ qi (mx u))
    rw [hstep, bind_map_left, map_bind]
    exact bind_congr fun u => ih u s

@[simp] private theorem spkSimulateQ_query_id {κ : Type} {spec : OracleSpec κ} {α : Type}
    (oa : OracleComp spec α) :
    simulateQ (fun t => (liftM (spec.query t) : OracleComp spec (spec.Range t))) oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind]
    exact bind_congr ih

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem spkLeakRedUAtomicProg_impl (ℓ : ℕ) :
    (spkLeakRedUAtomicProg (Pt := Pt) ℓ).impl =
      fun t => StateT.lift (liftM ((unifSpec + MACScheme.prfSpec Pt (BitVec 256)).query t)) := by
  funext t
  rcases t with n | q
  all_goals (apply StateT.ext; intro s; change Unit at s; cases s)
  · simp only [ReductionDsl.CostedReduction.impl, ReductionDsl.handlerImpl, spkLeakRedUAtomicProg,
      ReductionDsl.extractPtPrfBaseIface, ReductionDsl.atomicPrfIface, OracleSpec.query]
    rfl
  · simp only [ReductionDsl.CostedReduction.impl, ReductionDsl.handlerImpl, spkLeakRedUAtomicProg,
      ReductionDsl.extractPtPrfCodec, ReductionDsl.atomicPrfCodec,
      ReductionDsl.extractPtPrfBaseIface, ReductionDsl.atomicPrfIface,
      ReductionDsl.Comp.eval, ReductionDsl.Expr.eval, spkEnv_get_zero, spkEnv_get_succ,
      StateT.run_lift, map_eq_bind_pure_comp, OracleSpec.query]
    rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem spkLeakRedUAtomicProg_impl_run (ℓ : ℕ)
    (t : (unifSpec + MACScheme.prfSpec Pt (BitVec 256)).Domain)
    (s : (spkLeakRedUAtomicProg (Pt := Pt) ℓ).σ.denote) :
    ((spkLeakRedUAtomicProg (Pt := Pt) ℓ).impl t).run s =
      (fun u => (u, s)) <$> liftM ((unifSpec + MACScheme.prfSpec Pt (BitVec 256)).query t) := by
  rw [spkLeakRedUAtomicProg_impl]
  simp [StateT.run_lift, map_eq_bind_pure_comp]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType PQC] in
theorem spkLeakRedUAtomicProg_eval (ℓ : ℕ) (D : SpkLeakRed Pt ℓ PQC) (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) :
    evalSpkLeakRedU (spkLeakRedUAtomicProg (Pt := Pt) ℓ)
        (fun x => D P Dh encPt encT decT qep x A) =
      spkLeakRedU D P Dh encPt encT decT qep A := by
  simp only [evalSpkLeakRedU, ReductionDsl.CostedReduction.eval, spkLeakRedU,
    spkSimulateQ_run_StateT_of_step (spkLeakRedUAtomicProg_impl_run (Pt := Pt) ℓ)]
  simp [spkLeakRedUAtomicProg, ReductionDsl.extractPtPrfBaseIface, ReductionDsl.atomicPrfIface,
    ReductionDsl.atomicBaseSamplers, ReductionDsl.unifSamplers, ReductionDsl.AtomicBaseUnif.sort,
    ReductionDsl.Comp.eval, ReductionDsl.Expr.eval, bind_map_left]
  rfl

private theorem spkRatchetCostBudget_lower (q qep : ℕ) :
    16777216 * (q + 1) ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget maxForwardJumps
  have hq : q + 1 ≤ (q + 1) ^ 2 := by nlinarith
  have hm : 25000 ≤ q + 25000 + ReductionDsl.bits qep := by omega
  nlinarith

private theorem spkHopBudget_lower (q qep ℓ : ℕ) :
    12800000 * (q + 1) ≤ spkHopBudget q qep ℓ := by
  unfold spkHopBudget
  refine le_min ?_ ?_
  · unfold spkTier1Budget maxForwardJumps
    omega
  · unfold spkTier2Budget maxForwardJumps
    have h1 : 12800000 ≤
        64 * (ℓ + 512) + 64 * ReductionDsl.bits (q + 1) +
          64 * ReductionDsl.bits qep + 2 ^ 9 * 25000 := by omega
    calc 12800000 * (q + 1)
      _ = (q + 1) * 12800000 := Nat.mul_comm _ _
      _ ≤ (q + 1) * (64 * (ℓ + 512) + 64 * ReductionDsl.bits (q + 1) +
            64 * ReductionDsl.bits qep + 2 ^ 9 * 25000) := Nat.mul_le_mul_left (q + 1) h1

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem spkLeakRedUAtomicProg_gRedBounded (ℓ q qep : ℕ) :
    GRedBounded (spkLeakRedUAtomicProg (Pt := Pt) ℓ) (fun _ => 1) (fun _ => 0)
      (q + 1) (q + 1) (ratchetCostBudget q qep) := by
  refine Costed.gRedBounded_of_bounds (spkLeakRedUAtomicProg (Pt := Pt) ℓ)
    (fun _ => 1) (fun _ => 0) (q + 1) (q + 1) (ratchetCostBudget q qep) ?_ ?_ ?_
    (ReductionDsl.atomicPureOps_sizeHonest ℓ Pt)
    (ReductionDsl.atomicBaseSamplers_sizeHonest ℓ Pt)
  · have hbud := spkRatchetCostBudget_lower q qep
    have hmax11 : max 1 11 = 11 := rfl
    simp only [ReductionDsl.CostedReduction.totalCost, spkLeakRedUAtomicProg,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
      ReductionDsl.extractPtPrfBaseIface, ReductionDsl.atomicPrfIface,
      ReductionDsl.extractPtPrfCodec, ReductionDsl.atomicPrfCodec,
      ReductionDsl.atomicBaseSamplers, ReductionDsl.unifSamplers,
      ReductionDsl.AtomicBaseUnif.cost, Nat.reduceAdd, hmax11]
    omega
  · simp only [ReductionDsl.CostedReduction.size, spkLeakRedUAtomicProg,
      ReductionDsl.Comp.size, ReductionDsl.Expr.size, ReductionDsl.reductionSizeBudget]
    omega
  · simp only [ReductionDsl.CostedReduction.totalQueries, spkLeakRedUAtomicProg,
      ReductionDsl.Comp.queries]
    omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem spkLeakRedUAtomicProg_gRedBounded_tight (ℓ q : ℕ) :
    GRedBounded (spkLeakRedUAtomicProg (Pt := Pt) ℓ) (fun _ => 1) (fun _ => 0)
      (q + 1) (q + 1) (spkLeakRedUBudget q) := by
  refine Costed.gRedBounded_of_bounds (spkLeakRedUAtomicProg (Pt := Pt) ℓ)
    (fun _ => 1) (fun _ => 0) (q + 1) (q + 1) (spkLeakRedUBudget q) ?_ ?_ ?_
    (ReductionDsl.atomicPureOps_sizeHonest ℓ Pt)
    (ReductionDsl.atomicBaseSamplers_sizeHonest ℓ Pt)
  · have hmax11 : max 1 11 = 11 := rfl
    simp only [ReductionDsl.CostedReduction.totalCost, spkLeakRedUAtomicProg,
      spkLeakRedUBudget,
      ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
      ReductionDsl.extractPtPrfBaseIface, ReductionDsl.atomicPrfIface,
      ReductionDsl.extractPtPrfCodec, ReductionDsl.atomicPrfCodec,
      ReductionDsl.atomicBaseSamplers, ReductionDsl.unifSamplers,
      ReductionDsl.AtomicBaseUnif.cost, Nat.reduceAdd, hmax11]
    omega
  · simp only [ReductionDsl.CostedReduction.size, spkLeakRedUAtomicProg,
      ReductionDsl.Comp.size, ReductionDsl.Expr.size, ReductionDsl.reductionSizeBudget]
    omega
  · simp only [ReductionDsl.CostedReduction.totalQueries, spkLeakRedUAtomicProg,
      ReductionDsl.Comp.queries]
    omega

def mkSpkCostedRedsOf {ℓ : ℕ} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (spkLeak : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam)
    (hop2Prg : (k : ℕ) → SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam)
    (hop2Prf : (k : ℕ) → SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam) :
    SpkCostedReds Pt ℓ C K Dh encPt encT decT lam where
  spkLeakRed := spkLeak
  spkLeakRedU := spkLeakRedUAtomicProg ℓ
  hop2PrgRedK := hop2Prg
  hop2PrfRedK := hop2Prf

def spkCostedRedsBoundedWitness (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt := 0) :
    SpkCostedReds Pt ℓ C K Dh encPt encT decT lam where
  spkLeakRed := {
    σ := .unit
    init := .ret (.pair .unit .unit)
    handle := .ret (.pair (.pair .none (.pair .none .none)) .unit)
    finish := .ret (.bool false)
  }
  spkLeakRedU := spkLeakRedUAtomicProg ℓ
  hop2PrgRedK _ := {
    σ := .unit
    init := .ret (.pair .unit .unit)
    handle := .ret (.pair (.pair .none (.pair .none .none)) .unit)
    finish := .ret (.bool false)
  }
  hop2PrfRedK _ := {
    σ := .unit
    init := .ret (.pair .unit .unit)
    handle := .ret (.pair (.pair .none (.pair .none .none)) .unit)
    finish := .ret (.bool false)
  }

theorem spkCostedRedsBoundedWitness_bounds (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ) :
    spkCostedBounds q qep (spkCostedRedsBoundedWitness (Pt := Pt) ℓ C K Dh encPt encT decT lam) := by
  have hbud := spkHopBudget_lower q qep ℓ
  have hmax24 : max 1 24 = 24 := rfl
  have hOps := ReductionDsl.atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam
  have hSamp := ReductionDsl.atomicSamplers_sizeHonest ℓ Pt
  refine ⟨?_, spkLeakRedUAtomicProg_gRedBounded_tight ℓ q, fun k _ => ?_, fun k _ => ?_⟩
  · refine Costed.gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q (q + 1)
      (spkHopBudget q qep ℓ) ?_ ?_ ?_ hOps hSamp
    · simp only [ReductionDsl.CostedReduction.totalCost, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
        ReductionDsl.extractPtPrfIface, ReductionDsl.atomicPrfIface,
        ReductionDsl.e2eSessionCodec, Nat.reduceAdd, hmax24]; omega
    · simp only [ReductionDsl.CostedReduction.size, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.size, ReductionDsl.Expr.size, ReductionDsl.reductionSizeBudget]; omega
    · simp only [ReductionDsl.CostedReduction.totalQueries, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.queries]; omega
  · refine Costed.gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0
      (spkHopBudget q qep ℓ) ?_ ?_ ?_ hOps hSamp
    · simp only [ReductionDsl.CostedReduction.totalCost, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
        ReductionDsl.coinOnlyIface, ReductionDsl.e2eSessionCodec,
        Nat.reduceAdd, hmax24]; omega
    · simp only [ReductionDsl.CostedReduction.size, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.size, ReductionDsl.Expr.size, ReductionDsl.reductionSizeBudget]; omega
    · simp only [ReductionDsl.CostedReduction.totalQueries, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.queries]; omega
  · refine Costed.gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q
      (spkHopBudget q qep ℓ) ?_ ?_ ?_ hOps hSamp
    · simp only [ReductionDsl.CostedReduction.totalCost, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.cost, ReductionDsl.Expr.cost,
        ReductionDsl.extractPtPrfIface, ReductionDsl.atomicPrfIface,
        ReductionDsl.e2eSessionCodec, Nat.reduceAdd, hmax24]; omega
    · simp only [ReductionDsl.CostedReduction.size, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.size, ReductionDsl.Expr.size, ReductionDsl.reductionSizeBudget]; omega
    · simp only [ReductionDsl.CostedReduction.totalQueries, spkCostedRedsBoundedWitness,
        ReductionDsl.Comp.queries]; omega

private theorem isGameQuery_of_makesAtMostQueries {ℓ q : ℕ}
    {A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes}
    (hq : SM.MakesAtMostQueries A q) :
    A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)) q :=
  hq.of_imp (fun t ht => by cases t <;> simp_all [ReductionDsl.isGameQuery])

theorem mkSpkCostedRedsOf_evalSpkLeakRedU
    (P : Params Bytes (BitVec 512)) (ℓ : ℕ) {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) {lam : Pt}
    (spkLeak : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam)
    (hop2Prg : (k : ℕ) → SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam)
    (hop2Prf : (k : ℕ) → SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam)
    (qep : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (heval : ∀ x, evalSpkLeakRed spkLeak x A = spkLeakRed P Dh encPt encT decT qep x A) :
    evalSpkLeakRedU (mkSpkCostedRedsOf spkLeak hop2Prg hop2Prf).spkLeakRedU
        (fun x => evalSpkLeakRed (mkSpkCostedRedsOf spkLeak hop2Prg hop2Prf).spkLeakRed x A) =
      spkLeakRedU spkLeakRed P Dh encPt encT decT qep A := by
  have heq : (fun x => evalSpkLeakRed spkLeak x A) =
      (fun x => spkLeakRed P Dh encPt encT decT qep x A) := funext heval
  dsimp only [mkSpkCostedRedsOf]
  rw [heq]
  exact spkLeakRedUAtomicProg_eval ℓ spkLeakRed P Dh encPt encT decT qep A

private theorem spk_ite_pos {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  split_ifs
  rfl

private theorem spk_ite_neg {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by
  split_ifs
  rfl

/-- Canonical `SpkCostedReds` bundle over `atomicSessionOps`, selecting Tier-1 witnesses when
`spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ` and Tier-2 witnesses otherwise. -/
def mkSpkCostedReds (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ) :
    SpkCostedReds Pt ℓ C K Dh encPt encT decT lam where
  spkLeakRed :=
    if spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ then
      Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg.spkLeakRed
        C K Dh encPt encT decT idA idB lam ℓ q qep
    else
      Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedTier2Prog.spkLeakRedTier2
        C K Dh encPt encT decT idA idB lam ℓ q qep
  spkLeakRedU := spkLeakRedUAtomicProg ℓ
  hop2PrgRedK k :=
    if spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ then
      Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2PrgRedK
        C K Dh encPt encT decT idA idB lam ℓ q qep k
    else
      Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog.hop2PrgRedKTier2
        C K Dh encPt encT decT idA idB lam ℓ q qep k
  hop2PrfRedK k :=
    if spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ then
      Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2PrfRedK
        C K Dh encPt encT decT idA idB lam ℓ q qep k
    else
      Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog.hop2PrfRedKTier2
        C K Dh encPt encT decT idA idB lam ℓ q qep k

theorem mkSpkCostedReds_bounds (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (hqep : qep ≤ q + 10) :
    spkCostedBounds q qep
      (mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep) := by
  dsimp only [spkCostedBounds, mkSpkCostedReds]
  by_cases h : spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ
  · have hbud : spkHopBudget q qep ℓ = spkTier1Budget q qep := Nat.min_eq_left h
    rw [spk_ite_pos h, hbud]
    refine ⟨Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg.spkLeakRed_gRedBounded_tier1
        C K Dh encPt encT decT idA idB lam ℓ q qep hqep,
      spkLeakRedUAtomicProg_gRedBounded_tight ℓ q,
      fun k _ => ?_, fun k _ => ?_⟩
    · rw [spk_ite_pos h]
      exact Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2PrgRedK_gRedBounded_tier1
        C K Dh encPt encT decT idA idB lam ℓ q qep k hqep
    · rw [spk_ite_pos h]
      exact Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2PrfRedK_gRedBounded_tier1
        C K Dh encPt encT decT idA idB lam ℓ q qep k hqep
  · have hbud : spkHopBudget q qep ℓ = spkTier2Budget q qep ℓ :=
      Nat.min_eq_right (Nat.le_of_not_le h)
    rw [spk_ite_neg h, hbud]
    refine ⟨Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedTier2Prog.spkLeakRedTier2_gRedBounded
        C K Dh encPt encT decT idA idB lam ℓ q qep hqep,
      spkLeakRedUAtomicProg_gRedBounded_tight ℓ q,
      fun k _ => ?_, fun k _ => ?_⟩
    · rw [spk_ite_neg h]
      exact Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog.hop2PrgRedKTier2_gRedBounded
        C K Dh encPt encT decT idA idB lam ℓ q qep k hqep
    · rw [spk_ite_neg h]
      exact Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog.hop2PrfRedKTier2_gRedBounded
        C K Dh encPt encT decT idA idB lam ℓ q qep k hqep

theorem mkSpkCostedReds_evalSpkLeakRed
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkLeakRed
        (mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRed s A =
      spkLeakRed
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep s A := by
  dsimp only [mkSpkCostedReds]
  by_cases h : spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ
  · rw [spk_ite_pos h]
    exact Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedRInProg.spkLeakRed_eval
      C K Dh encPt encT decT idA idB lam ℓ q qep s A hq hℓ
  · rw [spk_ite_neg h]
    exact Computational.Proofs.Game.PromotedCostedReds.SpkLeakRedTier2Prog.spkLeakRedTier2_eval
      C K Dh encPt encT decT idA idB lam ℓ q qep s A hq hℓ

theorem mkSpkCostedReds_evalSpkLeakRedU
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkLeakRedU
        (mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRedU
        (fun x =>
          evalSpkLeakRed
            (mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRed
            x A) =
      spkLeakRedU spkLeakRed
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        Dh encPt encT decT qep A := by
  have heq :
      (fun x =>
        evalSpkLeakRed
          (mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep).spkLeakRed
          x A) =
      (fun x =>
        spkLeakRed
          (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
          Dh encPt encT decT qep x A) :=
    funext fun x => mkSpkCostedReds_evalSpkLeakRed ℓ C K idA idB Dh encPt encT decT lam q qep x A hq hℓ
  dsimp only [mkSpkCostedReds] at heq ⊢
  rw [heq]
  exact spkLeakRedUAtomicProg_eval ℓ spkLeakRed
    (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
    Dh encPt encT decT qep A

theorem mkSpkCostedReds_evalHop2PrgRedK_of_dec
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hq : SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
        ((mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrgRedK k)
        s A =
      hop2PrgRedK
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encPt encT decT qep s k A := by
  dsimp only [mkSpkCostedReds]
  by_cases h : spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ
  · rw [spk_ite_pos h]
    exact Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2PrgRedK_eval
      C K Dh encPt encT decT idA idB lam ℓ q qep k s A hk hq hℓ
  · rw [spk_ite_neg h]
    exact Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog.hop2PrgRedKTier2_eval_of_dec
      C K Dh encPt encT decT idA idB lam ℓ q qep k s A hdec hk hq hℓ

theorem mkSpkCostedReds_evalHop2PrfRedK_of_dec
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hq : SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
        ((mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrfRedK k)
        s A =
      hop2PrfRedK
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT qep s k A := by
  dsimp only [mkSpkCostedReds]
  by_cases h : spkTier1Budget q qep ≤ spkTier2Budget q qep ℓ
  · rw [spk_ite_pos h]
    exact Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg.hop2PrfRedK_eval
      C K Dh encPt encT decT idA idB lam ℓ q qep k s A hk hq hℓ
  · rw [spk_ite_neg h]
    exact Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog.hop2PrfRedKTier2_eval_of_dec
      C K Dh encPt encT decT idA idB lam ℓ q qep k s A hdec hk hq hℓ

theorem mkSpkCostedReds_evalHop2PrgRedK
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hq : SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrgHybrid
        ((mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrgRedK k)
        s A =
      hop2PrgRedK
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encPt encT decT qep s k A :=
  mkSpkCostedReds_evalHop2PrgRedK_of_dec ℓ C K idA idB Dh encPt encT decT lam q qep s k A hdec hk hq hℓ

theorem mkSpkCostedReds_evalHop2PrfRedK
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (q qep : ℕ)
    (s : BitVec 256) (k : ℕ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hdec : ∀ T, decT (encT T) = some T)
    (hk : k < spkSwapHybridCount) (hq : SM.MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    evalSpkSwapPrfHybrid
        ((mkSpkCostedReds (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam q qep).hop2PrfRedK k)
        s A =
      hop2PrfRedK
        (paramsIdsWithSpqr C (LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ Dh encT decT qep s k A :=
  mkSpkCostedReds_evalHop2PrfRedK_of_dec ℓ C K idA idB Dh encPt encT decT lam q qep s k A hdec hk hq hℓ

/-! ## Terminal Hop-2 hybrid bound (`k = 8`) -/

section Hop2Last

open CryptoGames.CKA CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF MACScheme LibsignalAead

set_option linter.unusedSectionVars false

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

attribute [local simp] simulateQ_lazyImpl_evalQuery simulateQ_lazyImpl_hop2Unif

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem dh_eq_of_hker (Dh : DHFun (BitVec 256) Pt) (s : BitVec 256)
    (hDh : Dh.Commutes)
    (hker : ∀ (x : BitVec 256) (P P' : Pt), Dh.dh x P = Dh.dh x P' ↔ Dh.dh s P = Dh.dh s P')
    (b rc a : BitVec 256) (T : Pt) (h : Dh.dh b T = Dh.dh b (Dh.dh a Dh.base)) :
    Dh.dh rc T = Dh.dh a (Dh.dh rc Dh.base) := by
  rw [← hDh rc a, hker rc, ← hker b]
  exact h

theorem senderRatchetKey_ne_spk_of_dh_ne (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (a s : BitVec 256) (T : Pt) (k : PublicKey) (hencT : encT T = k)
    (hne : Dh.dh a T ≠ Dh.dh a (Dh.dh s Dh.base)) :
    k ≠ (KeyPair.generate P.C s).publicKey := by
  have hspk : (KeyPair.generate P.C s).publicKey = encT (Dh.dh s Dh.base) :=
    keyPair_generate_publicKey hX s
  intro heq
  have hT : some T = some (Dh.dh s Dh.base) := by
    rw [← hdec T, hencT, heq, hspk, hdec]
  exact hne (Option.some.inj hT ▸ rfl)

omit [Zero Pt] [SampleableType Pt] in
theorem hop2LastActiveAt_of_B_noop {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {s : BitVec 256} {k_A : ℕ}
    {st st_next : Hop2State Pt ℓ} {tbl tbl_next : List (Pt × BitVec 256)}
    (h : Hop2LastActiveAt P Dh s k_A st tbl) (hbad : st_next.2.bad = false)
    (hstA : st_next.1.st .A = st.1.st .A) (hpB : (st_next.1.st .B).party = .B)
    (hidx : st_next.2.idx = st.2.idx) (hcoins : st_next.2.coins = st.2.coins)
    (hmade : st_next.2.made = st.2.made)
    (hlazy : ∀ t Q, t % 2 = 1 → st_next.2.lazy.lookup (t, Q) = st.2.lazy.lookup (t, Q))
    (htbl_lt : k_A < 4 → tbl_next = tbl)
    (htbl_fresh : tbl_next.lookup (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)) = none) :
    Hop2LastActiveAt P Dh s k_A st_next tbl_next where
  hkA := h.hkA
  bad_false := hbad
  party_A := hstA ▸ h.party_A
  party_B := hpB
  rem_A := hstA ▸ h.rem_A
  loc_A := hstA ▸ h.loc_A
  chains_len_A := hstA ▸ h.chains_len_A
  epochs_len_A := hstA ▸ h.epochs_len_A
  pos_tail_A := hstA ▸ h.pos_tail_A
  no_spk_A := hstA ▸ h.no_spk_A
  idx_A := (congrFun hidx .A).trans h.idx_A
  lazy_odd := fun t Q hodd => (hlazy t Q hodd).trans (h.lazy_odd t Q hodd)
  tbl_empty_lt := fun hk => (htbl_lt hk).trans (h.tbl_empty_lt hk)
  tbl_fresh := by rw [congrFun hcoins .A]; exact htbl_fresh
  made_gt := fun t ht Q => hmade ▸ h.made_gt t ht Q
  made_odd := fun Q ck hck => by
    rw [congrFun hcoins .A]
    exact h.made_odd Q ck (hmade ▸ hck)
  bob_state := h.bob_state.of_eq (congrFun hidx .B) hmade hcoins

omit [Zero Pt] [SampleableType Pt] in
theorem hop2LastActiveAt_of_B_offChain {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {s : BitVec 256} {k_A : ℕ}
    {st st_next : Hop2State Pt ℓ} {tbl tbl_next : List (Pt × BitVec 256)}
    (h : Hop2LastActiveAt P Dh s k_A st tbl) (rc : BitVec 256) (hbad : st_next.2.bad = false)
    (hstA : st_next.1.st .A = st.1.st .A) (hpB : (st_next.1.st .B).party = .B)
    (hidx : st_next.2.idx = (hop2Commit st.2 .B (some ⟨none, rc, none⟩)).idx)
    (hcoins : st_next.2.coins = (hop2Commit st.2 .B (some ⟨none, rc, none⟩)).coins)
    (hmade : st_next.2.made = (hop2Commit st.2 .B (some ⟨none, rc, none⟩)).made)
    (hlazy : ∀ t Q, t % 2 = 1 → st_next.2.lazy.lookup (t, Q) = st.2.lazy.lookup (t, Q))
    (htbl_lt : k_A < 4 → tbl_next = tbl)
    (htbl_fresh : tbl_next.lookup (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)) = none) :
    Hop2LastActiveAt P Dh s k_A st_next tbl_next where
  hkA := h.hkA
  bad_false := hbad
  party_A := hstA ▸ h.party_A
  party_B := hpB
  rem_A := hstA ▸ h.rem_A
  loc_A := hstA ▸ h.loc_A
  chains_len_A := hstA ▸ h.chains_len_A
  epochs_len_A := hstA ▸ h.epochs_len_A
  pos_tail_A := hstA ▸ h.pos_tail_A
  no_spk_A := hstA ▸ h.no_spk_A
  idx_A := by
    rw [hidx]; dsimp [hop2Commit]
    rw [Function.update_of_ne (by decide)]
    exact h.idx_A
  lazy_odd := fun t Q hodd => (hlazy t Q hodd).trans (h.lazy_odd t Q hodd)
  tbl_empty_lt := fun hk => (htbl_lt hk).trans (h.tbl_empty_lt hk)
  tbl_fresh := by
    rw [hcoins]; dsimp [hop2Commit]
    rw [Function.update_of_ne (by decide)]
    exact htbl_fresh
  made_gt := fun t ht Q => by
    rw [hmade]; dsimp [hop2Commit]
    exact h.made_gt t ht Q
  made_odd := fun Q ck hck => by
    rw [hcoins]; dsimp [hop2Commit]
    rw [Function.update_of_ne (by decide)]
    rw [hmade] at hck; dsimp [hop2Commit] at hck
    exact h.made_odd Q ck hck
  bob_state := .offChain (by rw [hidx]; dsimp [hop2Commit]; rw [Function.update_self])

omit [Zero Pt] [SampleableType Pt] in
theorem hop2LastActiveAt_of_B_atNext {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {s : BitVec 256} {k_A : ℕ}
    {st st_next : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)}
    (h : Hop2LastActiveAt P Dh s k_A st tbl) (hklt : k_A < 4) (rc ckS : BitVec 256) (Q' : Pt)
    (hQ'_eq : Q' = Dh.dh (st.2.coins .A) (Dh.dh rc Dh.base))
    (hQ'_ne : Q' ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base))
    (hmade_odd_none : ∀ Q, st.2.made.lookup (2 * k_A + 1, Q) = none) (hbad : st_next.2.bad = false)
    (hstA : st_next.1.st .A = st.1.st .A) (hpB : (st_next.1.st .B).party = .B)
    (hidx : st_next.2.idx =
      (hop2Commit st.2 .B (some ⟨some (2 * k_A + 2), rc, some ((2 * k_A + 1, Q'), ckS)⟩)).idx)
    (hcoins : st_next.2.coins =
      (hop2Commit st.2 .B (some ⟨some (2 * k_A + 2), rc, some ((2 * k_A + 1, Q'), ckS)⟩)).coins)
    (hmade : st_next.2.made =
      (hop2Commit st.2 .B (some ⟨some (2 * k_A + 2), rc, some ((2 * k_A + 1, Q'), ckS)⟩)).made)
    (hlazy : ∀ t Q, t % 2 = 1 → st_next.2.lazy.lookup (t, Q) = st.2.lazy.lookup (t, Q)) :
    Hop2LastActiveAt P Dh s k_A st_next tbl where
  hkA := h.hkA
  bad_false := hbad
  party_A := hstA ▸ h.party_A
  party_B := hpB
  rem_A := hstA ▸ h.rem_A
  loc_A := hstA ▸ h.loc_A
  chains_len_A := hstA ▸ h.chains_len_A
  epochs_len_A := hstA ▸ h.epochs_len_A
  pos_tail_A := hstA ▸ h.pos_tail_A
  no_spk_A := hstA ▸ h.no_spk_A
  idx_A := by
    rw [hidx]; dsimp [hop2Commit]
    rw [Function.update_of_ne (by decide)]
    exact h.idx_A
  lazy_odd := fun t Q hodd => (hlazy t Q hodd).trans (h.lazy_odd t Q hodd)
  tbl_empty_lt := h.tbl_empty_lt
  tbl_fresh := by
    rw [hcoins]; dsimp [hop2Commit]
    rw [Function.update_of_ne (by decide)]
    exact h.tbl_fresh
  made_gt := fun t ht Q => by
    rw [hmade]; dsimp [hop2Commit]
    have hne : (t, Q) ≠ (2 * k_A + 1, Q') := by
      intro heq
      rcases Prod.mk.inj heq with ⟨rfl, _⟩
      omega
    have hbeq : ((t, Q) == (2 * k_A + 1, Q')) = false := beq_eq_false_iff_ne.mpr hne
    simp [List.lookup, hbeq, h.made_gt t ht Q]
  made_odd := fun Q ck hck => by
    rw [hcoins]; dsimp [hop2Commit]
    rw [Function.update_of_ne (by decide)]
    rw [hmade] at hck; dsimp [hop2Commit] at hck
    by_cases hQ : Q = Q'
    · subst hQ; exact hQ'_ne
    · have hne : (2 * k_A + 1, Q) ≠ (2 * k_A + 1, Q') := fun heq => hQ (Prod.mk.inj heq).2
      have hbeq : ((2 * k_A + 1, Q) == (2 * k_A + 1, Q')) = false := beq_eq_false_iff_ne.mpr hne
      simp [List.lookup, hbeq, hmade_odd_none Q] at hck
  bob_state := .atNext hklt
    (by rw [hidx]; dsimp [hop2Commit]; rw [Function.update_self]) (fun Q ck hck => by
      rw [hcoins]; dsimp [hop2Commit]
      rw [Function.update_of_ne (by decide), Function.update_self]
      rw [hmade] at hck; dsimp [hop2Commit] at hck
      by_cases hQ : Q = Q'
      · subst hQ; exact hQ'_eq
      · have hne : (2 * k_A + 1, Q) ≠ (2 * k_A + 1, Q') := fun heq => hQ (Prod.mk.inj heq).2
        have hbeq : ((2 * k_A + 1, Q) == (2 * k_A + 1, Q')) = false := beq_eq_false_iff_ne.mpr hne
        simp [List.lookup, hbeq, hmade_odd_none Q] at hck)

omit [Zero Pt] [SampleableType Pt] in
theorem hop2BobState_even_idx {Dh : DHFun (BitVec 256) Pt} {k_A : ℕ} {aux : Hop2Aux Pt}
    (hkA : k_A ≤ 4) (h : Hop2BobState Dh k_A aux) :
    aux.idx .B = none ∨ ∃ t, aux.idx .B = some t ∧ t % 2 = 0 ∧ t ≤ 8 := by
  rcases h with ⟨h1⟩ | ⟨h1, _, _⟩ | ⟨hk, h1, _⟩
  · exact Or.inl h1
  · exact Or.inr ⟨2 * k_A, h1, by omega, by omega⟩
  · exact Or.inr ⟨2 * k_A + 2, h1, by omega, by omega⟩

omit [SampleableType Pt] in
theorem hop2Recv_B_support_active {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (r : Ratchet.RootKey) (c_chall : BitVec 256) (hDh : Dh.Commutes)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (k_A : ℕ) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hact : Hop2LastActiveAt P Dh s k_A st tbl) (c : Bytes) (rc : BitVec 256)
    (hrc : Dh.dh (st.2.coins .A) (Dh.dh rc Dh.base) ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base))
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s .B c (st.1.st .B) post)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .B) c rc).run st)).run tbl)) :
    Hop2LastActiveAt P Dh s k_A (post z.1.1 z.1.2).2 z.2 := by
  have hbadB : hop2BadAt P s (st.1.st .B) c = false :=
    hop2BadAt_eq_false_of_party_B P s (st.1.st .B) c hact.party_B
  unfold hop2Recv at hz
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    rw [htry] at hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rw [hpost.on_none]; exact hact
  | ok msg =>
    rw [htry] at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hact.party_B] at hz
    cases hidxB : st.2.idx .B with
    | none =>
      rw [hidxB] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      dsimp only []
      cases hrec_u : (sessionSchemeU P ℓ).receive (st.1.st .B) c rc with
      | none =>
        dsimp only [Option.map]
        rw [hpost.on_none]; exact hact
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        dsimp only [Option.map]
        have hp := hpost.on_some st' t' i' m' none st
        have hbad_next : (post (some ((st', t', i', m'), none)) st).2.2.bad = false := by
          rw [hp.1, hact.bad_false, hbadB]; rfl
        have hpe :=
          (sessionSchemeU_receive_party_epochs P (st.1.st .B) c rc st' t' i' m' hrec_u).1.trans
          hact.party_B
        rcases hp.2.2 with ⟨hst_eq, hidx_eq, hcoins_eq, hmade_eq⟩ | ⟨hst_upd, hidx_eq, hcoins_eq,
          hmade_eq⟩
        · exact hop2LastActiveAt_of_B_noop hact hbad_next (congrFun hst_eq .A)
            ((congrArg GhostState.party (congrFun hst_eq .B)).trans hact.party_B)
            hidx_eq hcoins_eq hmade_eq (fun _ _ _ => congrArg (List.lookup _) hp.2.1)
            (fun _ => rfl) hact.tbl_fresh
        · exact hop2LastActiveAt_of_B_noop hact hbad_next
            (by rw [hst_upd, Function.update_of_ne (by decide)])
            (by rw [hst_upd, Function.update_self]; exact hpe)
            hidx_eq hcoins_eq hmade_eq (fun _ _ _ => congrArg (List.lookup _) hp.2.1)
            (fun _ => rfl) hact.tbl_fresh
    | some t =>
      rw [hidxB] at hz
      dsimp only [] at hz
      split_ifs at hz with hfind
      · unfold hop2DH at hz
        cases hdec : decT msg.senderRatchetKey with
        | none =>
          rw [hdec] at hz
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; rw [hpost.on_none]; exact hact
        | some T =>
          rw [hdec] at hz
          dsimp only [] at hz
          by_cases hT : T = 0 ∨ encT T ≠ msg.senderRatchetKey
          · simp only [hT, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz; rw [hpost.on_none]; exact hact
          · simp only [hT, ↓reduceIte] at hz
            cases hsc : (st.1.st .B).session.senderChain with
            | none =>
              rw [hsc] at hz
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; rw [hpost.on_none]; exact hact
            | some sc =>
              rw [hsc] at hz
              simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hz
              rcases hz with ⟨⟨⟨r1, st1⟩, tbl1⟩, hz1, hz2⟩
              have heven_t : some t = none ∨ ∃ t', some t = some t' ∧ t' % 2 = 0 ∧ t' ≤ 8 := by
                have := hop2BobState_even_idx hact.hkA hact.bob_state
                rwa [hidxB] at this
              have h1 := hop2RecvHalf_even_support P r c_chall (some t)
                (st.1.st .B).session.rootKey msg.senderRatchetKey sc.ratchetKey.privateKey
                (Dh.dh (st.2.coins .B) T) st tbl heven_t _ hz1
              rcases h1 with ⟨hst1, hbad1, hidx1, hcoins1, hmade1, hlazy1, htbl1, hr1⟩
              rw [htbl1] at hz2
              cases r1 with
              | none =>
                simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hz2
                subst hz2; rw [hpost.on_none]
                exact hop2LastActiveAt_of_B_noop hact (hbad1.trans hact.bad_false)
                  (congrFun (congrArg SM.GameState.st hst1) .A)
                  (hst1 ▸ hact.party_B) hidx1 hcoins1 hmade1 hlazy1 (fun _ => rfl) hact.tbl_fresh
              | some p1 =>
                rcases p1 with ⟨idx1, rkM, ckR⟩
                simp only [stateT_lift_run_hop2, StateT.run_bind, bind_assoc, pure_bind,
                  simulateQ_bind, MonadAttach.mem_support_bind] at hz2
                rcases hz2 with ⟨⟨r2, tbl_mid⟩, hz_send, hz3⟩
                have hs := hop2SendHalf_support r c_chall idx1 rkM msg.senderRatchetKey
                  (KeyPair.generate P.C rc).privateKey (Dh.dh rc T) tbl (r2, tbl_mid) hz_send
                rcases hr1 idx1 rkM ckR rfl with rfl | ⟨t', ht_eq, hmade_t, rfl⟩
                ·
                  rcases hs.1 rfl with ⟨htbl_mid, hs_some⟩
                  rw [htbl_mid] at hz3
                  cases r2 with
                  | none =>
                    simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hz3
                    subst hz3; rw [hpost.on_none]
                    exact hop2LastActiveAt_of_B_noop hact (hbad1.trans hact.bad_false)
                      (congrFun (congrArg SM.GameState.st hst1) .A)
                      (hst1 ▸ hact.party_B) hidx1 hcoins1 hmade1 hlazy1 (fun _ => rfl)
                        hact.tbl_fresh
                  | some p2 =>
                    rcases p2 with ⟨idx2, rk2, ckS, pend⟩
                    rcases hs_some idx2 rk2 ckS pend rfl with ⟨rfl, rfl⟩
                    dsimp only [] at hz3
                    rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr
                      (P.expectedAddrs (st.1.st .B).party) msg .whisper rc _ with ⟨r_tr, s_out⟩
                    rw [htr] at hz3
                    cases r_tr with
                    | error _ =>
                      simp only [StateT.run_pure, simulateQ_pure, support_pure,
                        Set.mem_singleton_iff] at hz3
                      subst hz3; rw [hpost.on_none]
                      exact hop2LastActiveAt_of_B_noop hact (hbad1.trans hact.bad_false)
                        (congrFun (congrArg SM.GameState.st hst1) .A)
                        (hst1 ▸ hact.party_B) hidx1 hcoins1 hmade1 hlazy1 (fun _ => rfl)
                          hact.tbl_fresh
                    | ok m_plain =>
                      simp only [StateT.run_pure, simulateQ_pure, support_pure,
                        Set.mem_singleton_iff] at hz3
                      subst hz3; dsimp only []
                      set st' : GhostState Bytes :=
                        { (st.1.st .B) with
                          session := s_out
                          epoch := (st.1.st .B).epoch + 1
                          chainEpochs := ((st.1.st .B).chainEpochs ++ [(st.1.st .B).epoch + 1]).drop
                            (((st.1.st .B).chainEpochs.length + 1) - s_out.receiverChains.length) }
                      have hp := hpost.on_some st' ((st.1.st .B).epoch + 1) (msg.counter.toNat + 1)
                        (padOrTruncatePlain ℓ m_plain) (some ⟨none, rc, none⟩) st1
                      have hbad_next : (post (some ((st', (st.1.st .B).epoch +
                        1, msg.counter.toNat + 1,
                          padOrTruncatePlain ℓ m_plain), some ⟨none, rc, none⟩)) st1).2.2.bad = false := by
                        rw [hp.1, hbad1, hact.bad_false, hbadB]; rfl
                      rcases hp.2.2 with ⟨hst_eq, hidx_eq, hcoins_eq, hmade_eq⟩ |
                        ⟨hst_upd, hidx_eq, hcoins_eq, hmade_eq⟩
                      · exact hop2LastActiveAt_of_B_noop hact hbad_next
                          ((congrFun hst_eq .A).trans (congrFun (congrArg SM.GameState.st hst1) .A))
                          ((congrArg GhostState.party (congrFun hst_eq .B)).trans (hst1 ▸
                            hact.party_B))
                          (hidx_eq.trans hidx1) (hcoins_eq.trans hcoins1) (hmade_eq.trans hmade1)
                          (fun t0 Q0 h0 => (congrArg (List.lookup (t0,
                            Q0)) hp.2.1).trans (hlazy1 t0 Q0 h0))
                          (fun _ => rfl) hact.tbl_fresh
                      · exact hop2LastActiveAt_of_B_offChain hact rc hbad_next
                          (by rw [hst_upd, Function.update_of_ne (by decide), hst1])
                          (by rw [hst_upd, Function.update_self]; exact hact.party_B)
                          (by rw [hidx_eq]; dsimp [hop2Commit]; rw [hidx1])
                          (by rw [hcoins_eq]; dsimp [hop2Commit]; rw [hcoins1])
                          (by rw [hmade_eq]; dsimp [hop2Commit]; rw [hmade1])
                          (fun t0 Q0 h0 => (congrArg (List.lookup (t0,
                            Q0)) hp.2.1).trans (hlazy1 t0 Q0 h0))
                          (fun _ => rfl) hact.tbl_fresh
                ·
                  injection ht_eq with hteq; subst hteq
                  rcases hact.bob_state with ⟨hb_none⟩ | ⟨hb_even, hmade_odd_none,
                    hmade_even⟩ | ⟨_, hb_next, _⟩
                  · rw [hidxB] at hb_none; cases hb_none
                  · rw [hidxB] at hb_even
                    injection hb_even with hbeven; subst hbeven
                    have hQB_eq : Dh.dh (st.2.coins .B) T =
                        Dh.dh (st.2.coins .B) (Dh.dh (st.2.coins .A) Dh.base) :=
                      hmade_even _ ckR hmade_t
                    have hQ'_eq : Dh.dh rc T = Dh.dh (st.2.coins .A) (Dh.dh rc Dh.base) :=
                      dh_eq_of_hker Dh s hDh hker (st.2.coins .B) rc (st.2.coins .A) T hQB_eq
                    have hQ'_ne : Dh.dh rc T ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base) :=
                      hQ'_eq ▸ hrc
                    by_cases hklt : k_A < 4
                    · have hjle : 2 * k_A + 1 ≤ 8 := by omega
                      rcases hs.2.1 (2 * k_A + 1) rfl hjle with ⟨htbl_mid, hs_some⟩
                      rw [htbl_mid] at hz3
                      cases r2 with
                      | none =>
                        simp only [StateT.run_pure, simulateQ_pure, support_pure,
                          Set.mem_singleton_iff] at hz3
                        subst hz3; rw [hpost.on_none]
                        exact hop2LastActiveAt_of_B_noop hact (hbad1.trans hact.bad_false)
                          (congrFun (congrArg SM.GameState.st hst1) .A)
                          (hst1 ▸ hact.party_B) hidx1 hcoins1 hmade1 hlazy1 (fun _ => rfl)
                            hact.tbl_fresh
                      | some p2 =>
                        rcases p2 with ⟨idx2, rk2, ckS, pend⟩
                        rcases hs_some idx2 rk2 ckS pend rfl with ⟨rfl, ck', rfl⟩
                        dsimp only [] at hz3
                        rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr
                          (P.expectedAddrs (st.1.st .B).party) msg .whisper rc _ with ⟨r_tr, s_out⟩
                        rw [htr] at hz3
                        cases r_tr with
                        | error _ =>
                          simp only [StateT.run_pure, simulateQ_pure, support_pure,
                            Set.mem_singleton_iff] at hz3
                          subst hz3; rw [hpost.on_none]
                          exact hop2LastActiveAt_of_B_noop hact (hbad1.trans hact.bad_false)
                            (congrFun (congrArg SM.GameState.st hst1) .A)
                            (hst1 ▸ hact.party_B) hidx1 hcoins1 hmade1 hlazy1 (fun _ => rfl)
                              hact.tbl_fresh
                        | ok m_plain =>
                          simp only [StateT.run_pure, simulateQ_pure, support_pure,
                            Set.mem_singleton_iff] at hz3
                          subst hz3; dsimp only []
                          set st' : GhostState Bytes :=
                            { (st.1.st .B) with
                              session := s_out
                              epoch := (st.1.st .B).epoch + 1
                              chainEpochs :=
                                ((st.1.st .B).chainEpochs ++ [(st.1.st .B).epoch + 1]).drop
                                (((st.1.st .B).chainEpochs.length +
                                  1) - s_out.receiverChains.length) }
                          set u_comm : Option (Hop2Upd Pt) :=
                            some ⟨some (2 * k_A + 2), rc, some ((2 * k_A + 1, Dh.dh rc T), ck')⟩
                          have hp :=
                            hpost.on_some st' ((st.1.st .B).epoch + 1) (msg.counter.toNat + 1)
                            (padOrTruncatePlain ℓ m_plain) u_comm st1
                          have hbad_next : (post (some ((st', (st.1.st .B).epoch +
                            1, msg.counter.toNat + 1,
                              padOrTruncatePlain ℓ m_plain), u_comm)) st1).2.2.bad = false := by
                            rw [hp.1, hbad1, hact.bad_false, hbadB]; rfl
                          rcases hp.2.2 with ⟨hst_eq, hidx_eq, hcoins_eq, hmade_eq⟩ |
                            ⟨hst_upd, hidx_eq, hcoins_eq, hmade_eq⟩
                          · exact hop2LastActiveAt_of_B_noop hact hbad_next
                              ((congrFun hst_eq .A).trans (congrFun (congrArg SM.GameState.st hst1)
                                .A))
                              ((congrArg GhostState.party (congrFun hst_eq .B)).trans (hst1 ▸
                                hact.party_B))
                              (hidx_eq.trans hidx1) (hcoins_eq.trans hcoins1) (hmade_eq.trans
                                hmade1)
                              (fun t0 Q0 h0 => (congrArg (List.lookup (t0,
                                Q0)) hp.2.1).trans (hlazy1 t0 Q0 h0))
                              (fun _ => rfl) hact.tbl_fresh
                          · exact hop2LastActiveAt_of_B_atNext hact hklt rc ck' (Dh.dh rc T) hQ'_eq
                              hQ'_ne
                              hmade_odd_none hbad_next
                              (by rw [hst_upd, Function.update_of_ne (by decide), hst1])
                              (by rw [hst_upd, Function.update_self]; exact hact.party_B)
                              (by rw [hidx_eq]; dsimp [hop2Commit, u_comm]; rw [hidx1])
                              (by rw [hcoins_eq]; dsimp [hop2Commit, u_comm]; rw [hcoins1])
                              (by rw [hmade_eq]; dsimp [hop2Commit, u_comm]; rw [hmade1])
                              (fun t0 Q0 h0 => (congrArg (List.lookup (t0,
                                Q0)) hp.2.1).trans (hlazy1 t0 Q0 h0))
                    ·
                      have hjgt : 8 < 2 * k_A + 1 := by
                        have := hact.hkA; omega
                      rcases hs.2.2 (2 * k_A + 1) rfl hjgt with ⟨htbl_mid, hs_some⟩
                      have htbl_fresh_mid : tbl_mid.lookup (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base))
                        = none :=
                        htbl_mid _ hQ'_ne hact.tbl_fresh
                      have htbl_lt_mid : k_A < 4 → tbl_mid = tbl := fun hlt => (hklt hlt).elim
                      cases r2 with
                      | none =>
                        simp only [StateT.run_pure, simulateQ_pure, support_pure,
                          Set.mem_singleton_iff] at hz3
                        subst hz3; rw [hpost.on_none]
                        exact hop2LastActiveAt_of_B_noop hact (hbad1.trans hact.bad_false)
                          (congrFun (congrArg SM.GameState.st hst1) .A)
                          (hst1 ▸ hact.party_B) hidx1 hcoins1 hmade1 hlazy1 htbl_lt_mid
                            htbl_fresh_mid
                      | some p2 =>
                        rcases p2 with ⟨idx2, rk2, ckS, pend⟩
                        rcases hs_some idx2 rk2 ckS pend rfl with ⟨rfl, rfl⟩
                        dsimp only [] at hz3
                        rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr
                          (P.expectedAddrs (st.1.st .B).party) msg .whisper rc _ with ⟨r_tr, s_out⟩
                        rw [htr] at hz3
                        cases r_tr with
                        | error _ =>
                          simp only [StateT.run_pure, simulateQ_pure, support_pure,
                            Set.mem_singleton_iff] at hz3
                          subst hz3; rw [hpost.on_none]
                          exact hop2LastActiveAt_of_B_noop hact (hbad1.trans hact.bad_false)
                            (congrFun (congrArg SM.GameState.st hst1) .A)
                            (hst1 ▸ hact.party_B) hidx1 hcoins1 hmade1 hlazy1 htbl_lt_mid
                              htbl_fresh_mid
                        | ok m_plain =>
                          simp only [StateT.run_pure, simulateQ_pure, support_pure,
                            Set.mem_singleton_iff] at hz3
                          subst hz3; dsimp only []
                          set st' : GhostState Bytes :=
                            { (st.1.st .B) with
                              session := s_out
                              epoch := (st.1.st .B).epoch + 1
                              chainEpochs :=
                                ((st.1.st .B).chainEpochs ++ [(st.1.st .B).epoch + 1]).drop
                                (((st.1.st .B).chainEpochs.length +
                                  1) - s_out.receiverChains.length) }
                          have hp :=
                            hpost.on_some st' ((st.1.st .B).epoch + 1) (msg.counter.toNat + 1)
                            (padOrTruncatePlain ℓ m_plain) (some ⟨none, rc, none⟩) st1
                          have hbad_next : (post (some ((st', (st.1.st .B).epoch +
                            1, msg.counter.toNat + 1,
                              padOrTruncatePlain ℓ m_plain), some ⟨none, rc, none⟩)) st1).2.2.bad =
                                false := by
                            rw [hp.1, hbad1, hact.bad_false, hbadB]; rfl
                          rcases hp.2.2 with ⟨hst_eq, hidx_eq, hcoins_eq, hmade_eq⟩ |
                            ⟨hst_upd, hidx_eq, hcoins_eq, hmade_eq⟩
                          · exact hop2LastActiveAt_of_B_noop hact hbad_next
                              ((congrFun hst_eq .A).trans (congrFun (congrArg SM.GameState.st hst1)
                                .A))
                              ((congrArg GhostState.party (congrFun hst_eq .B)).trans (hst1 ▸
                                hact.party_B))
                              (hidx_eq.trans hidx1) (hcoins_eq.trans hcoins1) (hmade_eq.trans
                                hmade1)
                              (fun t0 Q0 h0 => (congrArg (List.lookup (t0,
                                Q0)) hp.2.1).trans (hlazy1 t0 Q0 h0))
                              htbl_lt_mid htbl_fresh_mid
                          · exact hop2LastActiveAt_of_B_offChain hact rc hbad_next
                              (by rw [hst_upd, Function.update_of_ne (by decide), hst1])
                              (by rw [hst_upd, Function.update_self]; exact hact.party_B)
                              (by rw [hidx_eq]; dsimp [hop2Commit]; rw [hidx1])
                              (by rw [hcoins_eq]; dsimp [hop2Commit]; rw [hcoins1])
                              (by rw [hmade_eq]; dsimp [hop2Commit]; rw [hmade1])
                              (fun t0 Q0 h0 => (congrArg (List.lookup (t0,
                                Q0)) hp.2.1).trans (hlazy1 t0 Q0 h0))
                              htbl_lt_mid htbl_fresh_mid
                  ·
                    rw [hidxB] at hb_next
                    injection hb_next with hbnext; subst hbnext
                    have hnone_made :=
                      hact.made_gt (2 * k_A + 2) (le_refl _) (Dh.dh (st.2.coins .B) T)
                    rw [hnone_made] at hmade_t
                    cases hmade_t
      ·
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        dsimp only []
        cases hrec_u : (sessionSchemeU P ℓ).receive (st.1.st .B) c rc with
        | none =>
          dsimp only [Option.map]
          rw [hpost.on_none]; exact hact
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          dsimp only [Option.map]
          have hp := hpost.on_some st' t' i' m' none st
          have hbad_next : (post (some ((st', t', i', m'), none)) st).2.2.bad = false := by
            rw [hp.1, hact.bad_false, hbadB]; rfl
          have hpe :=
            (sessionSchemeU_receive_party_epochs P (st.1.st .B) c rc st' t' i' m' hrec_u).1.trans
            hact.party_B
          rcases hp.2.2 with ⟨hst_eq, hidx_eq, hcoins_eq, hmade_eq⟩ | ⟨hst_upd, hidx_eq,
            hcoins_eq, hmade_eq⟩
          · exact hop2LastActiveAt_of_B_noop hact hbad_next (congrFun hst_eq .A)
              ((congrArg GhostState.party (congrFun hst_eq .B)).trans hact.party_B)
              hidx_eq hcoins_eq hmade_eq (fun _ _ _ => congrArg (List.lookup _) hp.2.1)
              (fun _ => rfl) hact.tbl_fresh
          · exact hop2LastActiveAt_of_B_noop hact hbad_next
              (by rw [hst_upd, Function.update_of_ne (by decide)])
              (by rw [hst_upd, Function.update_self]; exact hpe)
              hidx_eq hcoins_eq hmade_eq (fun _ _ _ => congrArg (List.lookup _) hp.2.1)
              (fun _ => rfl) hact.tbl_fresh

omit [SampleableType Pt] in
theorem evalDist_runHop2_recvWithPost_B_le {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (r : Ratchet.RootKey) (c_chall : BitVec 256) (hDh : Dh.Commutes)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (k_A : ℕ) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hact : Hop2LastActiveAt P Dh s k_A st tbl) (c : Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s .B c (st.1.st .B) post) (k : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (hts : TransShort st.1)
    (hpts : ∀ o st2, TransShort st2.1 → TransShort (post o st2).2.1)
    (M : ℝ≥0∞) (ih : ∀ a st' tbl', Hop2LastInv P Dh s st' tbl' → TransShort st'.1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k a) st' tbl'] {true} ≤ M) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .B) c rc).run st
        return post res.1 res.2)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k z.1.1) z.1.2 z.2)] {true} ≤
      hop2CollUnit Dh + M := by
  have hpull :
      (do
        let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
          let rc ← hop2Unif (Pt := Pt)
          let res ← (hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .B) c rc).run st
          return post res.1 res.2)).run tbl
        runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k z.1.1) z.1.2 z.2) =
      (do
        let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .B) c rc).run st)).run tbl
        runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k (post z.1.1 z.1.2).1)
          (post z.1.1 z.1.2).2 z.2) := by
    simp [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif, bind_assoc]
  rw [hpull]
  refine (bind_apply_le_add_of_bad ($ᵗ BitVec 256)
    _ (fun rc => decide (Dh.dh (st.2.coins .A) (Dh.dh rc Dh.base) =
      Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)))
    M (fun rc hbadF => ?_)).trans
    (add_le_add_left (dh_coll_prob_le_hop2CollUnit Dh (st.2.coins .A) (Dh.dh s Dh.base)) M)
  have hrc : Dh.dh (st.2.coins .A) (Dh.dh rc Dh.base) ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base) :=
    of_decide_eq_false hbadF
  refine bind_le_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
  exact ih (post z.1.1 z.1.2).1 (post z.1.1 z.1.2).2 z.2 (Or.inr ⟨k_A,
    hop2Recv_B_support_active P Dh encT decT s r c_chall hDh hker k_A st tbl hact c rc hrc post
      hpost z hz⟩)
    (hpts _ _ (by
      rw [(SpkHop1.hop2Recv_support_done P Dh encT decT _ _ c rc st tbl z hz).1]; exact hts))

omit [Zero Pt] [SampleableType Pt] in
theorem hop2LastActiveAt_of_A_noop {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {s : BitVec 256} {k_A : ℕ}
    {st st_next : Hop2State Pt ℓ} {tbl tbl_next : List (Pt × BitVec 256)}
    (h : Hop2LastActiveAt P Dh s k_A st tbl) (hbad : st_next.2.bad = false)
    (hst : st_next.1.st = st.1.st) (hidx : st_next.2.idx = st.2.idx)
    (hcoins : st_next.2.coins = st.2.coins) (hmade : st_next.2.made = st.2.made)
    (hlazy : st_next.2.lazy = st.2.lazy) (htbl_lt : k_A < 4 → tbl_next = tbl)
    (htbl_fresh : tbl_next.lookup (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)) = none) :
    Hop2LastActiveAt P Dh s k_A st_next tbl_next :=
  hop2LastActiveAt_of_B_noop h hbad (congrFun hst .A)
    ((congrArg GhostState.party (congrFun hst .B)).trans h.party_B)
    hidx hcoins hmade (fun _ _ _ => congrArg (List.lookup _) hlazy) htbl_lt htbl_fresh

omit [Zero Pt] [SampleableType Pt] in
theorem hop2LastActiveAt_of_A_existing {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {s : BitVec 256} {k_A : ℕ}
    {st st_next : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)}
    (h : Hop2LastActiveAt P Dh s k_A st tbl) (st' : GhostState Bytes) (hbad : st_next.2.bad = false)
    (hst : st_next.1.st = Function.update st.1.st .A st') (hpA : st'.party = .A)
    (hremA : st'.session.remoteIdentity = (st.1.st .A).session.remoteIdentity)
    (hlocA : st'.session.localIdentity = (st.1.st .A).session.localIdentity)
    (hlenA : st'.session.receiverChains.length = (st.1.st .A).session.receiverChains.length)
    (hepA : st'.chainEpochs = (st.1.st .A).chainEpochs)
    (hnoA : NoKeyInChains (KeyPair.generate P.C s).publicKey st'.session.receiverChains)
    (hidx : st_next.2.idx = st.2.idx) (hcoins : st_next.2.coins = st.2.coins)
    (hmade : st_next.2.made = st.2.made) (hlazy : st_next.2.lazy = st.2.lazy) :
    Hop2LastActiveAt P Dh s k_A st_next tbl where
  hkA := h.hkA
  bad_false := hbad
  party_A := by rw [hst, Function.update_self]; exact hpA
  party_B := by rw [hst, Function.update_of_ne (by decide)]; exact h.party_B
  rem_A := by rw [hst, Function.update_self, hremA]; exact h.rem_A
  loc_A := by rw [hst, Function.update_self, hlocA]; exact h.loc_A
  chains_len_A := by rw [hst, Function.update_self, hlenA]; exact h.chains_len_A
  epochs_len_A := by rw [hst, Function.update_self, hepA]; exact h.epochs_len_A
  pos_tail_A := by rw [hst, Function.update_self, hepA]; exact h.pos_tail_A
  no_spk_A := by rw [hst, Function.update_self]; exact hnoA
  idx_A := (congrFun hidx .A).trans h.idx_A
  lazy_odd := fun t Q hodd => hlazy ▸ h.lazy_odd t Q hodd
  tbl_empty_lt := h.tbl_empty_lt
  tbl_fresh := by rw [congrFun hcoins .A]; exact h.tbl_fresh
  made_gt := fun t ht Q => hmade ▸ h.made_gt t ht Q
  made_odd := fun Q ck hck => by
    rw [congrFun hcoins .A]
    exact h.made_odd Q ck (hmade ▸ hck)
  bob_state := h.bob_state.of_eq (congrFun hidx .B) hmade hcoins

omit [Zero Pt] [SampleableType Pt] in
theorem hop2LastActiveAt_of_A_step_lt {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {s : BitVec 256} {k_A : ℕ}
    {st st_next : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)}
    (h : Hop2LastActiveAt P Dh s k_A st tbl) (hDh : Dh.Commutes)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (hklt : k_A < 4) (T : Pt) (ckR rc ckS : BitVec 256)
    (hmade_t : st.2.made.lookup (2 * k_A + 1, Dh.dh (st.2.coins .A) T) = some ckR)
    (st' : GhostState Bytes) (hbad : st_next.2.bad = false)
    (hst : st_next.1.st = Function.update st.1.st .A st') (hpA : st'.party = .A)
    (hremA : st'.session.remoteIdentity = (st.1.st .A).session.remoteIdentity)
    (hlocA : st'.session.localIdentity = (st.1.st .A).session.localIdentity)
    (hlenA : st'.session.receiverChains.length = (k_A + 1) + 1)
    (hep_lenA : st'.chainEpochs.length = (k_A + 1) + 1)
    (hpos_tailA : ∀ e ∈ st'.chainEpochs.tail, 0 < e)
    (hnoA : NoKeyInChains (KeyPair.generate P.C s).publicKey st'.session.receiverChains)
    (hidx : st_next.2.idx =
      (hop2Commit st.2 .A (some ⟨some (2 * k_A + 3), rc, some ((2 * k_A +
        2, Dh.dh rc T), ckS)⟩)).idx)
    (hcoins : st_next.2.coins =
      (hop2Commit st.2 .A (some ⟨some (2 * k_A + 3), rc, some ((2 * k_A +
        2, Dh.dh rc T), ckS)⟩)).coins)
    (hmade : st_next.2.made =
      (hop2Commit st.2 .A (some ⟨some (2 * k_A + 3), rc, some ((2 * k_A +
        2, Dh.dh rc T), ckS)⟩)).made)
    (hlazy : st_next.2.lazy = st.2.lazy) :
    Hop2LastActiveAt P Dh s (k_A + 1) st_next tbl where
  hkA := by omega
  bad_false := hbad
  party_A := by rw [hst, Function.update_self]; exact hpA
  party_B := by rw [hst, Function.update_of_ne (by decide)]; exact h.party_B
  rem_A := by rw [hst, Function.update_self, hremA]; exact h.rem_A
  loc_A := by rw [hst, Function.update_self, hlocA]; exact h.loc_A
  chains_len_A := by rw [hst, Function.update_self]; exact hlenA
  epochs_len_A := by rw [hst, Function.update_self]; exact hep_lenA
  pos_tail_A := by rw [hst, Function.update_self]; exact hpos_tailA
  no_spk_A := by rw [hst, Function.update_self]; exact hnoA
  idx_A := by
    rw [hidx]; dsimp [hop2Commit]
    rw [Function.update_self]
    exact congrArg some (by omega)
  lazy_odd := fun t Q hodd => hlazy ▸ h.lazy_odd t Q hodd
  tbl_empty_lt := fun _ => h.tbl_empty_lt hklt
  tbl_fresh := by rw [h.tbl_empty_lt hklt]; rfl
  made_gt := fun t ht Q => by
    rw [hmade]; dsimp [hop2Commit]
    have hne : (t, Q) ≠ (2 * k_A + 2, Dh.dh rc T) := by
      intro heq
      rcases Prod.mk.inj heq with ⟨rfl, _⟩
      omega
    have hbeq : ((t, Q) == (2 * k_A + 2, Dh.dh rc T)) = false := beq_eq_false_iff_ne.mpr hne
    simp [List.lookup, hbeq, h.made_gt t (by omega) Q]
  made_odd := fun Q ck hck => by
    rw [hmade] at hck; dsimp [hop2Commit] at hck
    have hne : (2 * (k_A + 1) + 1, Q) ≠ (2 * k_A + 2, Dh.dh rc T) := by
      intro heq
      rcases Prod.mk.inj heq with ⟨h1, _⟩
      omega
    have hbeq : ((2 * (k_A + 1) + 1, Q) == (2 * k_A + 2, Dh.dh rc T)) = false :=
      beq_eq_false_iff_ne.mpr hne
    simp [List.lookup, hbeq, h.made_gt (2 * (k_A + 1) + 1) (by omega) Q] at hck
  bob_state := by
    rcases h.bob_state with ⟨hb_none⟩ | ⟨_, hmade_odd_none, _⟩ | ⟨_, hb_next, hmade_odd_eq⟩
    · exact .offChain (by
        rw [hidx]; dsimp [hop2Commit]
        rw [Function.update_of_ne (by decide)]
        exact hb_none)
    · have := hmade_odd_none (Dh.dh (st.2.coins .A) T)
      rw [this] at hmade_t; cases hmade_t
    · refine .atEven ?_ ?_ ?_
      · rw [hidx]; dsimp [hop2Commit]
        rw [Function.update_of_ne (by decide)]
        exact hb_next
      · intro Q
        rw [hmade]; dsimp [hop2Commit]
        have hne : (2 * (k_A + 1) + 1, Q) ≠ (2 * k_A + 2, Dh.dh rc T) := by
          intro heq
          rcases Prod.mk.inj heq with ⟨h1, _⟩
          omega
        have hbeq : ((2 * (k_A + 1) + 1, Q) == (2 * k_A + 2, Dh.dh rc T)) = false :=
          beq_eq_false_iff_ne.mpr hne
        simp [List.lookup, hbeq, h.made_gt (2 * (k_A + 1) + 1) (by omega) Q]
      · intro Q ck hck
        rw [hcoins]; dsimp [hop2Commit]
        rw [Function.update_of_ne (by decide), Function.update_self]
        rw [hmade] at hck; dsimp [hop2Commit] at hck
        have hQA_eq : Dh.dh (st.2.coins .A) T =
            Dh.dh (st.2.coins .A) (Dh.dh (st.2.coins .B) Dh.base) :=
          hmade_odd_eq _ ckR hmade_t
        have hQ'_eq : Dh.dh rc T = Dh.dh (st.2.coins .B) (Dh.dh rc Dh.base) :=
          dh_eq_of_hker Dh s hDh hker (st.2.coins .A) rc (st.2.coins .B) T hQA_eq
        by_cases hQ : Q = Dh.dh rc T
        · subst hQ; exact hQ'_eq
        · have hne : (2 * (k_A + 1), Q) ≠ (2 * k_A + 2, Dh.dh rc T) := fun heq =>
            hQ (Prod.mk.inj heq).2
          have hbeq : ((2 * (k_A + 1), Q) == (2 * k_A + 2, Dh.dh rc T)) = false :=
            beq_eq_false_iff_ne.mpr hne
          simp [List.lookup, hbeq, h.made_gt (2 * (k_A + 1)) (by omega) Q] at hck

omit [Zero Pt] [SampleableType Pt] in
theorem hop2LastActiveAt_of_A_step_four_done {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {s : BitVec 256}
    {st st_next : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)}
    (h : Hop2LastActiveAt P Dh s 4 st tbl) (st' : GhostState Bytes) (hbad : st_next.2.bad = false)
    (hst : st_next.1.st = Function.update st.1.st .A st') (hpA : st'.party = .A)
    (hposA : ∀ e ∈ st'.chainEpochs, 0 < e) :
    Hop2LastDone P s st_next where
  bad_false := hbad
  party_A := by rw [hst, Function.update_self]; exact hpA
  party_B := by rw [hst, Function.update_of_ne (by decide)]; exact h.party_B
  pos_epochs_A := by rw [hst, Function.update_self]; exact hposA

theorem hop2OffChainOut_step_four_inv {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (s : BitVec 256) (st : Hop2State Pt ℓ) (tbl tbl2 : List (Pt × BitVec 256))
    (hact : Hop2LastActiveAt P Dh s 4 st tbl)
    (c : Bytes) (msg : SignalMessage) (T : Pt) (sc : SenderChain) (rc u : BitVec 256)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind : ((st.1.st .A).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true)
    (henc : encT T = msg.senderRatchetKey)
    (hQA : Dh.dh (st.2.coins .A) T ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base))
    (htbl2 : tbl2.lookup (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)) = none)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s .A c (st.1.st .A) post) :
    Hop2LastInv P Dh s
      (withLazy st.2.lazy (post (hop2OffChainOut P ℓ (st.1.st .A) msg sc rc u) st).2) tbl2 := by
  have hne_spk : msg.senderRatchetKey ≠ (KeyPair.generate P.C s).publicKey :=
    senderRatchetKey_ne_spk_of_dh_ne P Dh encPt encT decT hX hdec (st.2.coins .A) s T
      msg.senderRatchetKey henc hQA
  have hbadA : hop2BadAt P s (st.1.st .A) c = false :=
    hop2BadAt_eq_false_of_senderRatchetKey_ne P s (st.1.st .A) c msg htry hne_spk
  dsimp only [hop2OffChainOut]
  cases hcc : rootCreateChain P.C (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
    msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
  | error _ =>
    dsimp only []
    rw [hpost.on_none, withLazy_self]
    exact Or.inr ⟨4,
      hop2LastActiveAt_of_A_noop hact hact.bad_false rfl rfl rfl rfl rfl (by omega) htbl2⟩
  | ok p2 =>
    rcases p2 with ⟨rk2, ck2⟩
    dsimp only []
    rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr
      (P.expectedAddrs (st.1.st .A).party) msg .whisper rc _ with ⟨r_tr, s_out⟩
    cases r_tr with
    | error _ =>
      dsimp only []
      rw [hpost.on_none, withLazy_self]
      exact Or.inr ⟨4,
        hop2LastActiveAt_of_A_noop hact hact.bad_false rfl rfl rfl rfl rfl (by omega) htbl2⟩
    | ok m_plain =>
      dsimp only []
      set st' : GhostState Bytes :=
        { (st.1.st .A) with
          session := s_out
          epoch := (st.1.st .A).epoch + 1
          chainEpochs := ((st.1.st .A).chainEpochs ++ [(st.1.st .A).epoch + 1]).drop
            (((st.1.st .A).chainEpochs.length + 1) - s_out.receiverChains.length) }
      have hp := hpost.on_some st' ((st.1.st .A).epoch + 1) (msg.counter.toNat + 1)
        (padOrTruncatePlain ℓ m_plain) (some ⟨none, rc, none⟩) st
      have hbad_next : (withLazy st.2.lazy (post (some ((st', (st.1.st .A).epoch + 1,
          msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain), some ⟨none, rc, none⟩)) st).2).2.bad =
            false := by
        change (post _ st).2.2.bad = false
        rw [hp.1, hact.bad_false, hbadA]; rfl
      rcases hp.2.2 with ⟨hst_eq, hidx_eq, hcoins_eq, hmade_eq⟩ |
        ⟨hst_upd, hidx_eq, hcoins_eq, hmade_eq⟩
      · exact Or.inr ⟨4,
          hop2LastActiveAt_of_A_noop hact hbad_next hst_eq hidx_eq hcoins_eq hmade_eq rfl
          (by omega) htbl2⟩
      · have hnone_find : (st.1.st .A).session.receiverChains.findIdx?
            (·.senderRatchetKey == msg.senderRatchetKey) = none :=
          Option.isNone_iff_eq_none.mp hfind
        have hstep_pr := tryDecryptFromRecord_stepped_props P (st.1.st .A) msg rc
          (if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1)
          rk2 (Ratchet.rootExpand P.C.F (keyToBytes32 u)).2
          (some ⟨KeyPair.generate P.C rc, ⟨ck2.key, 0⟩⟩)
          m_plain s_out hnone_find htr
        have hlen5 : s_out.receiverChains.length = 5 :=
          hstep_pr.2.2.1.trans (evictReceiverChains_append_length_four _ _ hact.chains_len_A)
        have hpos_epochs : ∀ e ∈ st'.chainEpochs, 0 < e := by
          dsimp only [st']
          rw [hlen5]
          exact chainEpochs_step_four (st.1.st .A).chainEpochs ((st.1.st .A).epoch + 1)
            hact.epochs_len_A hact.pos_tail_A (by omega)
        exact Or.inl (hop2LastActiveAt_of_A_step_four_done hact st' hbad_next hst_upd hact.party_A
          hpos_epochs)

theorem sessionSchemeU_receive_existing_props {ℓ : ℕ} (P : Params Bytes PQC)
    (stA : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (msg : SignalMessage)
    (k : PublicKey) (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg) (hfind : (stA.session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone = false)
    (hepochs : stA.chainEpochs.length = stA.session.receiverChains.length)
    (hno : NoKeyInChains k stA.session.receiverChains)
    (hrec : (sessionSchemeU P ℓ).receive stA c rc = some (st', t', i', m')) :
    st'.party = stA.party ∧
    st'.session.remoteIdentity = stA.session.remoteIdentity ∧
    st'.session.localIdentity = stA.session.localIdentity ∧
    st'.session.receiverChains.length = stA.session.receiverChains.length ∧
    st'.chainEpochs = stA.chainEpochs ∧
    NoKeyInChains k st'.session.receiverChains := by
  unfold sessionSchemeU Params.receive at hrec
  simp only [Option.map_eq_some_iff] at hrec
  rcases hrec with ⟨⟨g1, t1, i1, m1⟩, hy, htuple⟩
  rcases Prod.mk.inj htuple with ⟨rfl, _⟩
  rw [htry] at hy; dsimp only [] at hy
  rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs stA.party)
    msg .whisper rc stA.session with ⟨r_tr, s_out⟩
  rw [htr] at hy
  cases r_tr with
  | error _ => cases hy
  | ok m_plain =>
    dsimp only [] at hy
    injection hy with hy'
    rcases Prod.mk.inj hy' with ⟨rfl, _⟩
    cases hf : stA.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
    | none => rw [hf] at hfind; cases hfind
    | some idx =>
      have hex := tryDecryptFromRecord_existing_props P stA msg rc idx m_plain s_out hf htr
      refine ⟨rfl, hex.1, hex.2.1, hex.2.2.1, ?_, hex.2.2.2 k hno⟩
      simp [hepochs, hex.2.2.1]

set_option maxHeartbeats 800000 in
theorem hop2Recv_A_none_support_inv {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hDh : Dh.Commutes) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (r : Ratchet.RootKey) (c_chall : BitVec 256)
    (k_A : ℕ) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hact : Hop2LastActiveAt P Dh s k_A st tbl) (c : Bytes) (rc : BitVec 256)
    (hkey : hop2LazyKey P Dh encT decT (hop2HybLast r c_chall) (st.1.st .A) c st = none)
    (hnot_four_spk : ¬ (k_A = 4 ∧ ∃ msg T sc,
      SignalMessage.tryFrom P.codec c = .ok msg ∧
      ((st.1.st .A).session.receiverChains.findIdx?
        (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true ∧
      decT msg.senderRatchetKey = some T ∧
      ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
      (st.1.st .A).session.senderChain = some sc ∧
      Dh.dh (st.2.coins .A) T = Dh.dh (st.2.coins .A) (Dh.dh s Dh.base) ∧
      Dh.dh (st.2.coins .A) T ≠ 0))
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s .A c (st.1.st .A) post)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .A) c rc).run
        (withLazy [] st))).run tbl)) :
    Hop2LastInv P Dh s (withLazy st.2.lazy (post z.1.1 st).2) z.2 := by
  have hz_orig := hz
  unfold hop2Recv at hz
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    rw [htry] at hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; dsimp only []
    rw [hpost.on_none, withLazy_self]
    exact Or.inr ⟨k_A, hact⟩
  | ok msg =>
    rw [htry] at hz
    have hidxA_wl : (withLazy [] st).2.idx (st.1.st .A).party = some (2 * k_A + 1) := by
      dsimp [withLazy]; rw [hact.party_A, hact.idx_A]
    have hcoinsA_wl : (withLazy [] st).2.coins (st.1.st .A).party = st.2.coins .A := by
      dsimp [withLazy]; rw [hact.party_A]
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hidxA_wl, hcoinsA_wl] at hz
    cases hfind : ((st.1.st .A).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg.senderRatchetKey)).isNone with
    | false =>
      rw [hfind] at hz; simp only [Bool.false_eq_true, ↓reduceIte] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; dsimp only []
      cases hrec_u : (sessionSchemeU P ℓ).receive (st.1.st .A) c rc with
      | none =>
        dsimp only [Option.map]
        rw [hpost.on_none, withLazy_self]
        exact Or.inr ⟨k_A, hact⟩
      | some val =>
        rcases val with ⟨st', t', i', m'⟩
        dsimp only [Option.map]
        have hne_spk : msg.senderRatchetKey ≠ (KeyPair.generate P.C s).publicKey := by
          intro heq
          rw [heq, findIdx?_eq_none_of_noKeyInChains _ _ hact.no_spk_A] at hfind
          cases hfind
        have hbadA : hop2BadAt P s (st.1.st .A) c = false :=
          hop2BadAt_eq_false_of_senderRatchetKey_ne P s (st.1.st .A) c msg htry hne_spk
        have hp := hpost.on_some st' t' i' m' none st
        have hbad_next : (withLazy st.2.lazy
            (post (some ((st', t', i', m'), none)) st).2).2.bad = false := by
          change (post _ st).2.2.bad = false
          rw [hp.1, hact.bad_false, hbadA]; rfl
        have hex := sessionSchemeU_receive_existing_props P (st.1.st .A) c rc msg
          (KeyPair.generate P.C s).publicKey st' t' i' m' htry hfind
          (hact.epochs_len_A.trans hact.chains_len_A.symm) hact.no_spk_A hrec_u
        rcases hp.2.2 with ⟨hst_eq, hidx_eq, hcoins_eq, hmade_eq⟩ |
          ⟨hst_upd, hidx_eq, hcoins_eq, hmade_eq⟩
        · exact Or.inr ⟨k_A, hop2LastActiveAt_of_A_noop hact hbad_next hst_eq hidx_eq
            hcoins_eq hmade_eq rfl (fun _ => rfl) hact.tbl_fresh⟩
        · exact Or.inr ⟨k_A, hop2LastActiveAt_of_A_existing hact st' hbad_next hst_upd
            (hex.1.trans hact.party_A) hex.2.1 hex.2.2.1 hex.2.2.2.1 hex.2.2.2.2.1
            hex.2.2.2.2.2 hidx_eq hcoins_eq hmade_eq rfl⟩
    | true =>
      rw [hfind] at hz; simp only [↓reduceIte] at hz
      unfold hop2DH at hz
      cases hdecT : decT msg.senderRatchetKey with
      | none =>
        rw [hdecT] at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; dsimp only []
        rw [hpost.on_none, withLazy_self]
        exact Or.inr ⟨k_A, hact⟩
      | some T =>
        rw [hdecT] at hz; dsimp only [] at hz
        by_cases hT : T = 0 ∨ encT T ≠ msg.senderRatchetKey
        · simp only [hT, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; dsimp only []
          rw [hpost.on_none, withLazy_self]
          exact Or.inr ⟨k_A, hact⟩
        · simp only [hT, ↓reduceIte] at hz
          have henc : encT T = msg.senderRatchetKey := Decidable.of_not_not (not_or.mp hT).2
          cases hsc : (st.1.st .A).session.senderChain with
          | none =>
            rw [hsc] at hz
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; dsimp only []
            rw [hpost.on_none, withLazy_self]
            exact Or.inr ⟨k_A, hact⟩
          | some sc =>
            rw [hsc] at hz; dsimp only [] at hz
            by_cases hklt : k_A < 4
            · by_cases hQ0 : Dh.dh (st.2.coins .A) T = 0
              · unfold hop2RecvHalf at hz
                simp only [hQ0, ↓reduceIte, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; dsimp only []
                rw [hpost.on_none, withLazy_self]
                exact Or.inr ⟨k_A, hact⟩
              · have htle : 2 * k_A + 1 ≤ (hop2HybLast (Pt := Pt) r c_chall).k := by
                  change 2 * k_A + 1 ≤ 8; omega
                have hmade_some : ∃ ckR, st.2.made.lookup (2 * k_A +
                  1, Dh.dh (st.2.coins .A) T) = some ckR := by
                  unfold hop2LazyKey at hkey
                  rw [htry, hact.party_A, hact.idx_A] at hkey; dsimp only [] at hkey
                  rw [hfind] at hkey; simp only [↓reduceIte] at hkey
                  rw [hdecT] at hkey; dsimp only [] at hkey
                  simp only [hT, ↓reduceIte, hsc, hQ0, htle] at hkey
                  cases hm : st.2.made.lookup (2 * k_A + 1, Dh.dh (st.2.coins .A) T) with
                  | none => rw [hm] at hkey; cases hkey
                  | some ckR => exact ⟨ckR, rfl⟩
                rcases hmade_some with ⟨ckR, hmade_t⟩
                have hmade_wl : (withLazy [] st).2.made.lookup (2 * k_A +
                  1, Dh.dh (st.2.coins .A) T) = some ckR :=
                  hmade_t
                unfold hop2RecvHalf at hz
                simp only [hQ0, ↓reduceIte, htle, StateT.run_bind, StateT.run_get, pure_bind,
                  hmade_wl, StateT.run_pure, stateT_lift_run_hop2, bind_assoc,
                  simulateQ_bind, MonadAttach.mem_support_bind] at hz
                rcases hz with ⟨⟨r2, tbl_out⟩, hz2, hz3⟩
                have hs := hop2SendHalf_support (P := P) r c_chall (some (2 * k_A + 1 + 1)) 0
                  msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey (Dh.dh rc T) tbl (r2,
                    tbl_out) hz2
                have hQA_ne : Dh.dh (st.2.coins .A) T ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base) :=
                  hact.made_odd (Dh.dh (st.2.coins .A) T) ckR hmade_t
                have hne_spk : msg.senderRatchetKey ≠ (KeyPair.generate P.C s).publicKey :=
                  senderRatchetKey_ne_spk_of_dh_ne P Dh encPt encT decT hX hdec (st.2.coins .A) s T
                    msg.senderRatchetKey henc hQA_ne
                have hbadA : hop2BadAt P s (st.1.st .A) c = false :=
                  hop2BadAt_eq_false_of_senderRatchetKey_ne P s (st.1.st .A) c msg htry hne_spk
                have hjle : 2 * k_A + 1 + 1 ≤ 8 := by omega
                rcases hs.2.1 (2 * k_A + 1 + 1) rfl hjle with ⟨htbl_out, hs_some⟩
                subst htbl_out
                cases r2 with
                | none =>
                  simp only [StateT.run_pure, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hz3
                  subst hz3; dsimp only []
                  rw [hpost.on_none, withLazy_self]
                  exact Or.inr ⟨k_A, hact⟩
                | some p2 =>
                  rcases p2 with ⟨idx2, rk2, ckS, pend⟩
                  rcases hs_some idx2 rk2 ckS pend rfl with ⟨rfl, ck', rfl⟩
                  dsimp only [] at hz3
                  rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr
                    (P.expectedAddrs (st.1.st .A).party) msg .whisper rc _ with ⟨r_tr, s_out⟩
                  rw [htr] at hz3
                  cases r_tr with
                  | error _ =>
                    simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hz3
                    subst hz3; dsimp only []
                    rw [hpost.on_none, withLazy_self]
                    exact Or.inr ⟨k_A, hact⟩
                  | ok m_plain =>
                    simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hz3
                    subst hz3; dsimp only []
                    set st' : GhostState Bytes :=
                      { (st.1.st .A) with
                        session := s_out
                        epoch := (st.1.st .A).epoch + 1
                        chainEpochs := ((st.1.st .A).chainEpochs ++ [(st.1.st .A).epoch + 1]).drop
                          (((st.1.st .A).chainEpochs.length + 1) - s_out.receiverChains.length) }
                    set u_comm : Option (Hop2Upd Pt) :=
                      some ⟨some (2 * k_A + 1 + 1 + 1), rc, some ((2 * k_A + 1 +
                        1, Dh.dh rc T), ck')⟩
                    have hp := hpost.on_some st' ((st.1.st .A).epoch + 1) (msg.counter.toNat + 1)
                      (padOrTruncatePlain ℓ m_plain) u_comm st
                    have hbad_next : (withLazy st.2.lazy (post (some ((st', (st.1.st .A).epoch + 1,
                        msg.counter.toNat + 1, padOrTruncatePlain ℓ m_plain), u_comm)) st).2).2.bad =
                          false := by
                      change (post _ st).2.2.bad = false
                      rw [hp.1, hact.bad_false, hbadA]; rfl
                    rcases hp.2.2 with ⟨hst_eq, hidx_eq, hcoins_eq, hmade_eq⟩ |
                      ⟨hst_upd, hidx_eq, hcoins_eq, hmade_eq⟩
                    · exact Or.inr ⟨k_A, hop2LastActiveAt_of_A_noop hact hbad_next hst_eq hidx_eq
                        hcoins_eq hmade_eq rfl (fun _ => rfl) hact.tbl_fresh⟩
                    · have hnone_find : (st.1.st .A).session.receiverChains.findIdx?
                          (·.senderRatchetKey == msg.senderRatchetKey) = none :=
                        Option.isNone_iff_eq_none.mp hfind
                      have hstep_pr := tryDecryptFromRecord_stepped_props P (st.1.st .A) msg rc
                        (if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1)
                        rk2 ckR
                        (some ⟨KeyPair.generate P.C rc, ⟨ckS, 0⟩⟩)
                        m_plain s_out hnone_find htr
                      have hlen_succ : s_out.receiverChains.length = (k_A + 1) + 1 :=
                        hstep_pr.2.2.1.trans (evictReceiverChains_append_length_lt _ _ k_A
                          hact.chains_len_A hklt)
                      have hep_props : st'.chainEpochs.length = (k_A + 1) + 1 ∧
                          ∀ e ∈ st'.chainEpochs.tail, 0 < e := by
                        dsimp only [st']
                        rw [hlen_succ]
                        exact chainEpochs_step_lt (st.1.st .A).chainEpochs ((st.1.st .A).epoch + 1)
                          k_A hact.epochs_len_A hact.pos_tail_A (by omega)
                      have hno_chains : NoKeyInChains (KeyPair.generate P.C s).publicKey
                        s_out.receiverChains :=
                        hstep_pr.2.2.2 _ hact.no_spk_A hne_spk
                      exact Or.inr ⟨k_A +
                        1, hop2LastActiveAt_of_A_step_lt hact hDh hker hklt T ckR rc ck'
                        hmade_t st' hbad_next hst_upd hact.party_A hstep_pr.1 hstep_pr.2.1
                        hlen_succ hep_props.1 hep_props.2 hno_chains hidx_eq hcoins_eq hmade_eq rfl⟩
            · have hk4 : k_A = 4 := by have := hact.hkA; omega
              by_cases hQ0 : Dh.dh (st.2.coins .A) T = 0
              · unfold hop2RecvHalf at hz
                simp only [hQ0, ↓reduceIte, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; dsimp only []
                rw [hpost.on_none, withLazy_self]
                exact Or.inr ⟨k_A, hact⟩
              · have hQA_ne : Dh.dh (st.2.coins .A) T ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base) :=
                  by
                  intro hQA_eq
                  exact hnot_four_spk ⟨hk4, msg, T, sc, htry, hfind, hdecT, hT, hsc, hQA_eq, hQ0⟩
                have hidx9 : st.2.idx (st.1.st .A).party = some 9 := by
                  rw [hact.party_A, hact.idx_A, hk4]
                have hcoinsA : st.2.coins (st.1.st .A).party = st.2.coins .A := by
                  rw [hact.party_A]
                have hrun9 := hop2Recv_run_at_nine P Dh encT decT r c_chall
                  (st.1.st .A) c rc st msg T sc hidx9 htry hfind hdecT hT hsc
                  (hcoinsA ▸ hQ0)
                rw [hcoinsA] at hrun9
                rw [hrun9] at hz_orig
                simp only [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind,
                  simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion,
                  support_pure, Set.mem_singleton_iff, Function.comp_apply] at hz_orig
                rcases hz_orig with ⟨⟨u, tbl2⟩, hu, hz_eq⟩
                subst hz_eq; dsimp only []
                have htbl2 : tbl2.lookup (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)) = none :=
                  evalQuery_support_lookup_eq_none (Dh.dh (st.2.coins .A) T) _ tbl hQA_ne
                    hact.tbl_fresh (u, tbl2) hu
                exact hop2OffChainOut_step_four_inv P Dh encPt encT decT hX hdec s st tbl tbl2
                  (hk4 ▸ hact) c msg T sc rc u htry hfind henc hQA_ne htbl2 post hpost

omit [SampleableType Pt] in
theorem hop2LazyKey_some_props {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (h : Hop2Hyb Pt) (s : BitVec 256) (k_A : ℕ) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hact : Hop2LastActiveAt P Dh s k_A st tbl)
    (c : Bytes) (tq : ℕ × Pt) (msg : SignalMessage) (sc : SenderChain)
    (hkey : hop2LazyKey P Dh encT decT h (st.1.st .A) c st = some (tq, msg, sc)) :
    SignalMessage.tryFrom P.codec c = .ok msg ∧
    (st.1.st .A).session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) =
      none ∧
    st.2.lazy.lookup tq = none := by
  unfold hop2LazyKey at hkey
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hkey; cases hkey
  | ok msg' =>
    rw [htry, hact.party_A, hact.idx_A] at hkey; dsimp only [] at hkey
    cases hfind : ((st.1.st .A).session.receiverChains.findIdx?
      (·.senderRatchetKey == msg'.senderRatchetKey)).isNone with
    | false =>
      rw [hfind] at hkey; simp only [Bool.false_eq_true, ↓reduceIte] at hkey; cases hkey
    | true =>
      rw [hfind] at hkey; simp only [↓reduceIte] at hkey
      cases hdecT : decT msg'.senderRatchetKey with
      | none => rw [hdecT] at hkey; cases hkey
      | some T =>
        rw [hdecT] at hkey; dsimp only [] at hkey
        by_cases hT : T = 0 ∨ encT T ≠ msg'.senderRatchetKey
        · simp only [hT, ↓reduceIte] at hkey; cases hkey
        · simp only [hT, ↓reduceIte] at hkey
          cases hsc : (st.1.st .A).session.senderChain with
          | none => rw [hsc] at hkey; cases hkey
          | some sc' =>
            rw [hsc] at hkey; dsimp only [] at hkey
            by_cases hQ0 : Dh.dh (st.2.coins .A) T = 0
            · simp only [hQ0, ↓reduceIte] at hkey; cases hkey
            · simp only [hQ0, ↓reduceIte] at hkey
              by_cases htle : 2 * k_A + 1 ≤ h.k
              · simp only [htle, ↓reduceIte] at hkey
                cases hm : st.2.made.lookup (2 * k_A + 1, Dh.dh (st.2.coins .A) T) with
                | some _ => rw [hm] at hkey; cases hkey
                | none =>
                  rw [hm] at hkey
                  injection hkey with htuple
                  rcases Prod.mk.inj htuple with ⟨rfl, hrest⟩
                  rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
                  exact ⟨rfl, Option.isNone_iff_eq_none.mp hfind,
                    hact.lazy_odd (2 * k_A + 1) (Dh.dh (st.2.coins .A) T) (by omega)⟩
              · simp only [htle, ↓reduceIte] at hkey; cases hkey

set_option maxHeartbeats 400000 in
theorem evalDist_runHop2_recvWithPost_A_le {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hDh : Dh.Commutes) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (r : Ratchet.RootKey) (c_chall : BitVec 256)
    (k_A : ℕ) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hact : Hop2LastActiveAt P Dh s k_A st tbl) (c : Bytes)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s .A c (st.1.st .A) post) (k : Option (SM.RecvResult (CBC.Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (hc : ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → c.length < 2 ^ 32)
    (hts : TransShort st.1)
    (hpts : ∀ o st2, TransShort st2.1 → TransShort (post o st2).2.1)
    (M : ℝ≥0∞) (ih : ∀ a st' tbl', Hop2LastInv P Dh s st' tbl' → TransShort st'.1 →
      𝒟[runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k a) st' tbl'] {true} ≤ M) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT (hop2HybLast r c_chall) (st.1.st .A) c rc).run st
        return post res.1 res.2)).run tbl
      runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k z.1.1) z.1.2 z.2)] {true} ≤
      hop2FreshUnit P.C.F + M := by
  have hrun := runHop2_recvWithPost P Dh encT decT qep s (hop2HybLast r c_chall) .A c
    st.2.lazy st tbl post hpost k
  rw [withLazy_self] at hrun
  rw [hrun]
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun rc _ => ?_
  cases hkey : hop2LazyKey P Dh encT decT (hop2HybLast r c_chall) (st.1.st .A) c st with
  | some val =>
    rcases val with ⟨tq, msg, sc⟩
    dsimp only []
    have hprops := hop2LazyKey_some_props P Dh encT decT (hop2HybLast r c_chall) s k_A st tbl hact
      c tq msg sc hkey
    rw [hprops.2.2]
    dsimp only []
    set bad : BitVec 256 → Bool :=
      fun u => testSpk P (st.1.st .A).session.pqRatchetState c ((Ratchet.expandPRG P.C.F).gen u).2
    set g : BitVec 256 → ProbComp Bool :=
      fun u => runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k (some .rejected))
        (withLazy ((tq, u) :: st.2.lazy) st) tbl
    refine (bind_apply_le_add_of_eq_on_good ($ᵗ BitVec 256) _ g bad (fun u hbadF => ?_)).trans ?_
    · have hout : hop2OffChainOut (Pt := Pt) P ℓ (st.1.st .A) msg sc rc u = none :=
        hop2OffChainOut_eq_none_of_testSpk_false P ℓ (st.1.st .A) c msg sc rc u
          hact.party_A hact.rem_A hact.loc_A hprops.1 hprops.2.1 hbadF
      dsimp only [g]
      rw [hout, hpost.on_none]
    · refine add_le_add
        (testSpk_expandPRG_le_hop2FreshUnit P (st.1.st .A).session.pqRatchetState c hc) ?_
      have hcons := evalDist_runHop2_lazy_cons_fresh P Dh encT decT qep s (hop2HybLast r c_chall)
        (k (some .rejected)) st tbl st.2.lazy tq hprops.2.2
      have hcons_true : 𝒟[($ᵗ BitVec 256) >>= g] {true} =
          𝒟[runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k (some .rejected)) st tbl] {true}
            := by
        simpa only [g,
          withLazy_self] using congrArg (fun d => (d : MeasureTheory.Measure Bool) {true}) hcons
      rw [hcons_true]
      exact ih (some .rejected) st tbl (Or.inr ⟨k_A, hact⟩) hts
  | none =>
    dsimp only []
    by_cases hfour : k_A = 4 ∧ ∃ msg T sc,
      SignalMessage.tryFrom P.codec c = .ok msg ∧
      ((st.1.st .A).session.receiverChains.findIdx?
        (·.senderRatchetKey == msg.senderRatchetKey)).isNone = true ∧
      decT msg.senderRatchetKey = some T ∧
      ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
      (st.1.st .A).session.senderChain = some sc ∧
      Dh.dh (st.2.coins .A) T = Dh.dh (st.2.coins .A) (Dh.dh s Dh.base) ∧
      Dh.dh (st.2.coins .A) T ≠ 0
    · rcases hfour with ⟨hk4, msg, T, sc, htry, hfind, hdecT, hT, hsc, hQA_eq, hQ0⟩
      have hidx9 : st.2.idx (st.1.st .A).party = some 9 := by
        rw [hact.party_A, hact.idx_A, hk4]
      have hcoinsA : st.2.coins (st.1.st .A).party = st.2.coins .A := by
        rw [hact.party_A]
      have hrun9 := hop2Recv_run_at_nine P Dh encT decT r c_chall
        (st.1.st .A) c rc st msg T sc hidx9 htry hfind hdecT hT hsc
        (hcoinsA ▸ hQ0)
      rw [hcoinsA, hQA_eq] at hrun9
      rw [hrun9]
      have hstep : (SpkHop1.lazyStep (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base))).run tbl =
          (fun u => (u, (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base), u) :: tbl)) <$>
            ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
        unfold SpkHop1.lazyStep
        simp [StateT.run_bind, StateT.run_get, hact.tbl_fresh,
          StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]
      have heval : ((simulateQ (lazyImpl (Pt := Pt))
          ((fun u => (hop2OffChainOut (Pt := Pt) P ℓ (st.1.st .A) msg sc rc u, withLazy [] st)) <$>
            evalQuery (Input := Pt) (Tag :=
              BitVec 256) (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)))).run tbl) =
          (fun u => ((hop2OffChainOut (Pt := Pt) P ℓ (st.1.st .A) msg sc rc u, withLazy [] st),
            (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base), u) :: tbl)) <$>
            ($ᵗ BitVec 256 : ProbComp (BitVec 256)) := by
        simp [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_evalQuery,
          hstep, StateT.run_pure, simulateQ_pure, bind_assoc, pure_bind, Function.comp_apply]
      rw [heval]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      set bad : BitVec 256 → Bool :=
        fun u => testSpk P (st.1.st .A).session.pqRatchetState c ((Ratchet.expandPRG P.C.F).gen u).2
      set g : BitVec 256 → ProbComp Bool :=
        fun u => runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k (some .rejected)) st
          ((Dh.dh (st.2.coins .A) (Dh.dh s Dh.base), u) :: tbl)
      refine (bind_apply_le_add_of_eq_on_good ($ᵗ BitVec 256) _ g bad (fun u hbadF => ?_)).trans ?_
      · have hnone_find : (st.1.st .A).session.receiverChains.findIdx?
            (·.senderRatchetKey == msg.senderRatchetKey) = none :=
          Option.isNone_iff_eq_none.mp hfind
        have hout : hop2OffChainOut (Pt := Pt) P ℓ (st.1.st .A) msg sc rc u = none :=
          hop2OffChainOut_eq_none_of_testSpk_false P ℓ (st.1.st .A) c msg sc rc u
            hact.party_A hact.rem_A hact.loc_A htry hnone_find hbadF
        dsimp only [g]
        rw [hout, hpost.on_none, withLazy_self]
      · refine add_le_add
          (testSpk_expandPRG_le_hop2FreshUnit P (st.1.st .A).session.pqRatchetState c hc) ?_
        have hcons := evalDist_runHop2_tbl_cons_fresh P Dh encT decT qep s (hop2HybLast r c_chall)
          (k (some .rejected)) st tbl (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)) hact.tbl_fresh
        have hcons_true : 𝒟[($ᵗ BitVec 256) >>= g] {true} =
            𝒟[runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) (k (some .rejected)) st tbl]
              {true} :=
          congrArg (fun d => (d : MeasureTheory.Measure Bool) {true}) hcons
        rw [hcons_true]
        exact ih (some .rejected) st tbl (Or.inr ⟨k_A, hact⟩) hts
    · refine (bind_le_of_support _ _ (measurableSet_singleton _) fun z hz => ?_).trans le_add_self
      exact ih (post z.1.1 st).1 (withLazy st.2.lazy (post z.1.1 st).2) z.2
        (hop2Recv_A_none_support_inv P Dh encPt encT decT hX hdec hDh s hker r c_chall k_A st tbl
          hact c rc hkey hfour post hpost z hz)
        (hpts z.1.1 st hts)

private theorem mul_sub_one_add {q : ℕ} (hq0 : 0 < q) (U : ℝ≥0∞) :
    U + ((q - 1 : ℕ) : ℝ≥0∞) * U = (q : ℝ≥0∞) * U := by
  have hq_eq : q = (q - 1) + 1 := by omega
  conv_rhs => rw [hq_eq, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

theorem hop2DeliverPost_transShort {ℓ : ℕ} (P : Params Bytes PQC) (s : BitVec 256)
    (Q : Party) (c : Bytes) (g₀ : GhostState Bytes) (r : SM.Record (CBC.Plain ℓ) Bytes)
    (o : Hop2Out Pt ℓ) (st2 : Hop2State Pt ℓ) (h : TransShort st2.1) :
    TransShort (hop2DeliverPost P s Q c g₀ r o st2).2.1 := by
  rcases o with _ | ⟨⟨st', t', i', m'⟩, u⟩
  · exact h
  · exact transShort_accept h Q st' r.pos

theorem hop2InjectPost_transShort {ℓ : ℕ} (P : Params Bytes PQC) (qep : ℕ) (s : BitVec 256)
    (Q : Party) (c : Bytes) (g₀ : GhostState Bytes)
    (o : Hop2Out Pt ℓ) (st2 : Hop2State Pt ℓ) (h : TransShort st2.1) :
    TransShort (hop2InjectPost P qep s Q c g₀ o st2).2.1 := by
  rcases o with _ | ⟨⟨st', t', i', m'⟩, u⟩
  · exact h
  · simp only [hop2InjectPost]
    split_ifs
    · exact h
    · exact transShort_accept h Q st' _
    · exact h

set_option maxHeartbeats 600000 in
theorem evalDist_runHop2_le_of_makesAtMostQueries {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hDh : Dh.Commutes) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (r : Ratchet.RootKey) (c_chall : BitVec 256)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (hcodec : P.codec = protoSignalCodec) (hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ)
    (rem : ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) (hinv : Hop2LastInv P Dh s st tbl)
    (hts : TransShort st.1) :
    𝒟[runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) oa st tbl] {true} ≤
      (rem : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh) := by
  induction oa using OracleComp.inductionOn generalizing rem st tbl with
  | pure b =>
    rcases hinv with hdone | ⟨k_A, hact⟩
    · rw [evalDist_runHop2_eq_zero_of_done P Dh encT decT qep s (hop2HybLast r c_chall)
        (pure b) st tbl hdone]
      exact zero_le
    · rw [runHop2_pure, hact.bad_false]
      simp
  | query_bind t k ih =>
    rcases hinv with hdone | ⟨k_A, hact⟩
    · rw [evalDist_runHop2_eq_zero_of_done P Dh encT decT qep s (hop2HybLast r c_chall)
        _ st tbl hdone]
      exact zero_le
    · rw [SM.MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
      rw [runHop2_bind_query]
      rcases t with n | ((((⟨Q, m, r_c⟩ | ⟨Q, m₀, m₁, r_c⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
      · rw [runHop2_unif]
        exact bind_le_of_support _ _ (measurableSet_singleton _) fun u _ =>
          ih u rem (by simpa [SM.MakesAtMostQueries] using hq.2 u) st tbl (Or.inr ⟨k_A, hact⟩) hts
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        rw [runHop2_hop2Lift']
        refine (bind_le_of_support _ _ (measurableSet_singleton _) fun res hres => ?_).trans
          ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        exact ih res.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 res.1)
          (res.2, st.2) tbl (Or.inr ⟨k_A,
            hact.of_stSendStep (transmitR_support_stSendStep P decT encT qep (Q, m,
              r_c) st.1 res hres)⟩)
          (transmitR_support_transShort P hrt _ qep st.1 (Q, m, r_c) hts res hres)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        rw [runHop2_hop2Lift']
        refine (bind_le_of_support _ _ (measurableSet_singleton _) fun res hres => ?_).trans
          ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        exact ih res.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 res.1)
          (res.2, st.2) tbl (Or.inr ⟨k_A,
            hact.of_stSendStep (challR_support_stSendStep P decT encT qep (Q, m₀, m₁,
              r_c) st.1 res hres)⟩)
          (challR_support_transShort P hrt _ qep st.1 (Q, m₀, m₁, r_c) hts res hres)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        by_cases hwin : st.1.win = true
        · have hstep : (hop2Deliver P Dh encT decT s (hop2HybLast r c_chall) (Q, c)).run st =
              pure (none, st) := by
            unfold hop2Deliver
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
              StateT.run_pure]
          simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
          exact (ih none (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 none)
            st tbl (Or.inr ⟨k_A, hact⟩) hts).trans ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
          cases hin : st.1.inTransit Q.other c with
          | none =>
            have hstep : (hop2Deliver P Dh encT decT s (hop2HybLast r c_chall) (Q, c)).run st =
                pure (none, st) := by
              unfold hop2Deliver
              simp only [StateT.run_bind, StateT.run_get, pure_bind, hwinF, Bool.false_eq_true,
                ↓reduceIte, hin, StateT.run_pure]
            simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
            exact (ih none (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 none)
              st tbl (Or.inr ⟨k_A, hact⟩) hts).trans ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
          | some r_tr =>
            rw [hop2Deliver_run_eq_post P Dh encT decT s (hop2HybLast r c_chall) Q c st r_tr hwinF
              hin]
            cases Q with
            | A =>
              refine (evalDist_runHop2_recvWithPost_A_le P Dh encPt encT decT qep hX hdec hDh s hker
                r c_chall k_A st tbl hact c _
                (hop2DeliverPost_isHop2Post P s .A c (st.1.st .A) r_tr) k
                (fun _ _ => ct_length_lt_of_inTransit hts _ c r_tr hin) hts
                (hop2DeliverPost_transShort P s .A c (st.1.st .A) r_tr)
                (((rem - 1 : ℕ) : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh))
                (fun a st' tbl' hinv' hts' =>
                  ih a (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 a) st' tbl'
                    hinv' hts')).trans ?_
              have hle : hop2FreshUnit P.C.F ≤ hop2FreshUnit P.C.F + hop2CollUnit Dh := le_self_add
              exact (add_le_add_left hle _).trans_eq (mul_sub_one_add hq0 _)
            | B =>
              refine (evalDist_runHop2_recvWithPost_B_le P Dh encT decT qep s r c_chall hDh hker
                k_A st tbl hact c _
                (hop2DeliverPost_isHop2Post P s .B c (st.1.st .B) r_tr) k hts
                (hop2DeliverPost_transShort P s .B c (st.1.st .B) r_tr)
                (((rem - 1 : ℕ) : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh))
                (fun a st' tbl' hinv' hts' =>
                  ih a (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 a) st' tbl'
                    hinv' hts')).trans ?_
              have hle : hop2CollUnit Dh ≤ hop2FreshUnit P.C.F + hop2CollUnit Dh := le_add_self
              exact (add_le_add_left hle _).trans_eq (mul_sub_one_add hq0 _)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
        · have hstep : (hop2Inject P Dh encT decT qep s (hop2HybLast r c_chall) (Q, c)).run st =
              pure (none, st) := by
            unfold hop2Inject
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte, StateT.run_pure]
          simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
          exact (ih none (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 none)
            st tbl (Or.inr ⟨k_A, hact⟩) hts).trans ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
          have hadm : ratchetKeyAdmissible protoSignalCodec decT encT c = true := by
            revert hgF
            cases ratchetKeyAdmissible protoSignalCodec decT encT c <;> simp
          have hc32 : ∀ msg, SignalMessage.tryFrom P.codec c = .ok msg → c.length < 2 ^ 32 :=
            fun msg htry => ratchetKeyAdmissible_length_lt_of_tryFrom protoSignalCodec decT encT c msg
              hadm (by rw [← hcodec]; exact htry)
          rw [hop2Inject_run_eq_post P Dh encT decT qep s (hop2HybLast r c_chall) Q c st hgF]
          cases Q with
          | A =>
            refine (evalDist_runHop2_recvWithPost_A_le P Dh encPt encT decT qep hX hdec hDh s hker
              r c_chall k_A st tbl hact c _
              (hop2InjectPost_isHop2Post (Pt := Pt) (ℓ := ℓ) P qep s .A c (st.1.st .A)) k
              hc32 hts (hop2InjectPost_transShort (Pt := Pt) P qep s .A c (st.1.st .A))
              (((rem - 1 : ℕ) : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh))
              (fun a st' tbl' hinv' hts' =>
                ih a (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 a) st' tbl'
                  hinv' hts')).trans ?_
            have hle : hop2FreshUnit P.C.F ≤ hop2FreshUnit P.C.F + hop2CollUnit Dh := le_self_add
            exact (add_le_add_left hle _).trans_eq (mul_sub_one_add hq0 _)
          | B =>
            refine (evalDist_runHop2_recvWithPost_B_le P Dh encT decT qep s r c_chall hDh hker
              k_A st tbl hact c _
              (hop2InjectPost_isHop2Post (Pt := Pt) (ℓ := ℓ) P qep s .B c (st.1.st .B)) k
              hts (hop2InjectPost_transShort (Pt := Pt) P qep s .B c (st.1.st .B))
              (((rem - 1 : ℕ) : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh))
              (fun a st' tbl' hinv' hts' =>
                ih a (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 a) st' tbl'
                  hinv' hts')).trans ?_
            have hle : hop2CollUnit Dh ≤ hop2FreshUnit P.C.F + hop2CollUnit Dh := le_add_self
            exact (add_le_add_left hle _).trans_eq (mul_sub_one_add hq0 _)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        rw [runHop2_hop2Lift']
        refine (bind_le_of_support _ _ (measurableSet_singleton _) fun res hres => ?_).trans
          ((le_add_self).trans_eq (mul_sub_one_add hq0 _))
        exact ih res.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 res.1)
          (res.2, st.2) tbl (Or.inr ⟨k_A,
            hact.of_stSendStep (corrR_support_stSendStep P decT encT Q st.1 res hres)⟩)
          (corrR_support_transShort _ st.1 Q hts res hres)

theorem hop2LastActiveAt_init {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (s : BitVec 256) (b : Bool) (ck0 x alice pqr ck1 : BitVec 256)
    (hx_ne : Dh.dh s (Dh.dh x Dh.base) ≠ Dh.dh s (Dh.dh s Dh.base)) :
    let I0 := Dh.dh x (Dh.dh alice Dh.base)
    let spk := (KeyPair.generate P.C x).publicKey
    let sessA := ((SessionState.new currentVersion P.idA P.idB 0
      (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
      (KeyPair.generate P.C alice) ⟨ck1, 0⟩
    let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
    let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
    let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
      { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
    let aux0 : Hop2Aux Pt :=
      { made := [((0, I0), ck1)]
        idx := fun Q => match Q with | .A => some 1 | .B => some 0
        coins := fun Q => match Q with | .A => alice | .B => x }
    Hop2LastActiveAt P Dh s 0 (initSt, aux0) [] where
  hkA := by decide
  bad_false := rfl
  party_A := rfl
  party_B := rfl
  rem_A := rfl
  loc_A := rfl
  chains_len_A := rfl
  epochs_len_A := rfl
  pos_tail_A := by simp
  no_spk_A := by
    intro ch hch
    rcases List.mem_singleton.mp hch with rfl
    exact senderRatchetKey_ne_spk_of_dh_ne P Dh encPt encT decT hX hdec s s (Dh.dh x Dh.base)
      (KeyPair.generate P.C x).publicKey (keyPair_generate_publicKey hX x).symm hx_ne
  idx_A := rfl
  lazy_odd := fun _ _ _ => rfl
  tbl_empty_lt := fun _ => rfl
  tbl_fresh := rfl
  made_gt := fun t ht Q => by
    have hne : (t, Q) ≠ (0, Dh.dh x (Dh.dh alice Dh.base)) := by
      intro heq
      rcases Prod.mk.inj heq with ⟨rfl, _⟩
      omega
    simp [List.lookup, beq_eq_false_iff_ne.mpr hne]
  made_odd := fun Q ck hck => by
    have hne : (2 * 0 + 1, Q) ≠ (0, Dh.dh x (Dh.dh alice Dh.base)) := by
      intro heq
      rcases Prod.mk.inj heq with ⟨h1, _⟩
      omega
    simp [List.lookup, beq_eq_false_iff_ne.mpr hne] at hck
  bob_state := .atEven rfl
    (fun Q => by
      have hne : (2 * 0 + 1, Q) ≠ (0, Dh.dh x (Dh.dh alice Dh.base)) := by
        intro heq
        rcases Prod.mk.inj heq with ⟨h1, _⟩
        omega
      simp [List.lookup, beq_eq_false_iff_ne.mpr hne])
    (fun Q ck hck => by
      by_cases hQ : Q = Dh.dh x (Dh.dh alice Dh.base)
      · exact hQ
      · have hne : (0, Q) ≠ (0, Dh.dh x (Dh.dh alice Dh.base)) := fun heq =>
          hQ (Prod.mk.inj heq).2
        have hbeq : ((0, Q) == (0, Dh.dh x (Dh.dh alice Dh.base))) = false :=
          beq_eq_false_iff_ne.mpr hne
        simp [List.lookup, hbeq] at hck)

private theorem stateT_run'_lift_bind {S α β : Type} (p : ProbComp α)
    (f : α → StateT S ProbComp β) (s : S) :
    (do let x ← (StateT.lift p : StateT S ProbComp α); f x).run' s =
      (do let x ← p; (f x).run' s) := by
  change (Prod.fst <$> (do let x ← (StateT.lift p : StateT S ProbComp α); f x).run s) =
    (do let x ← p; Prod.fst <$> (f x).run s)
  rw [StateT.run_bind, stateT_lift_probComp_run]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]

/-- Terminal Hop-2 bound (`k = 8`): in the `b = true` random-function branch of `hop2PrfRedK`,
the probability of `bad = true` is at most
`spkSwapSpuriousStepTerm P.C.F q + spkSwapCreationPointHitTerm Dh q`. -/
theorem evalDist_hop2PrfRedK_last_le {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hDh : Dh.Commutes) (s : BitVec 256)
    (hker : ∀ (x : BitVec 256) (P₁ P₂ : Pt), Dh.dh x P₁ = Dh.dh x P₂ ↔ Dh.dh s P₁ = Dh.dh s P₂)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    𝒟[(extractPRF P.C.F encPt).branch true
        (hop2PrfRedK P ℓ Dh encT decT qep s (spkSwapHybridCount - 1) A)] {true} ≤
      spkSwapSpuriousStepTerm P.C.F q + spkSwapCreationPointHitTerm Dh q := by
  rw [evalDist_branch_true_eq_lazyImpl]
  have hunfold :
      (simulateQ (lazyImpl (Pt := Pt))
        (hop2PrfRedK P ℓ Dh encT decT qep s (spkSwapHybridCount - 1) A)).run' [] =
      (do
        let r ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let c_chall ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ck0 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let x ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let alice ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let pqr ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let u1 ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
        let I0 := Dh.dh x (Dh.dh alice Dh.base)
        let spk := (KeyPair.generate P.C x).publicKey
        let sessA := ((SessionState.new currentVersion P.idA P.idB 0
          (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
          (KeyPair.generate P.C alice) ⟨u1, 0⟩
        let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
        let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
        let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
          { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
        let aux0 : Hop2Aux Pt :=
          { made := [((0, I0), u1)]
            idx := fun Q => match Q with | .A => some 1 | .B => some 0
            coins := fun Q => match Q with | .A => alice | .B => x }
        runHop2 P Dh encT decT qep s (hop2HybLast r c_chall) A (initSt, aux0) []) := by
    unfold hop2PrfRedK
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun r => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun c_chall => ?_
    unfold hop2Game
    rw [simulateQ_bind, simulateQ_lazyImpl_liftM, stateT_run'_lift_bind]
    refine bind_congr fun b => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun ck0 => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun x => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun alice => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun pqr => ?_
    rw [simulateQ_bind, simulateQ_lazyImpl_hop2Unif, stateT_run'_lift_bind]
    refine bind_congr fun u1 => ?_
    rfl
  rw [hunfold]
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun r _ => ?_
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun c_chall _ => ?_
  refine bind_le_of_support ($ᵗ Bool) _ (measurableSet_singleton _) fun b _ => ?_
  refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun ck0 _ => ?_
  refine (bind_apply_le_add_of_bad ($ᵗ BitVec 256) _
    (fun x => decide (Dh.dh s (Dh.dh x Dh.base) = Dh.dh s (Dh.dh s Dh.base)))
    ((q : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh)) (fun x hbadF => ?_)).trans ?_
  · have hx_ne : Dh.dh s (Dh.dh x Dh.base) ≠ Dh.dh s (Dh.dh s Dh.base) :=
      of_decide_eq_false hbadF
    refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun alice _ => ?_
    refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun pqr _ => ?_
    refine bind_le_of_support ($ᵗ BitVec 256) _ (measurableSet_singleton _) fun u1 _ => ?_
    exact evalDist_runHop2_le_of_makesAtMostQueries P Dh encPt encT decT qep hX hdec hDh s hker
      r c_chall A hcodec
      ⟨hcodec ▸ signalRoundTripShort_proto, hL, hcodec ▸ signalEncodeFits32_proto⟩ q hq _ []
      (Or.inr ⟨0, hop2LastActiveAt_init P Dh encPt encT decT hX hdec s b ck0 x alice pqr u1 hx_ne⟩)
      (by intro r hr; simp at hr)
  · calc 𝒟[($ᵗ BitVec 256) >>= fun x =>
          pure (decide (Dh.dh s (Dh.dh x Dh.base) = Dh.dh s (Dh.dh s Dh.base)))] {true} +
        (q : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh)
      _ ≤ hop2CollUnit Dh + (q : ℝ≥0∞) * (hop2FreshUnit P.C.F + hop2CollUnit Dh) :=
        add_le_add_left (dh_coll_prob_le_hop2CollUnit Dh s (Dh.dh s Dh.base)) _
      _ = spkSwapSpuriousStepTerm P.C.F q + spkSwapCreationPointHitTerm Dh q := by
        rw [hop2FreshTerm_eq_mul_unit, hop2CollTerm_eq_mul_unit, Nat.cast_add, Nat.cast_one,
          mul_add, add_mul, one_mul]
        ac_rfl

end Hop2Last

end CryptoVerification.E2E.HeadlineSpk
