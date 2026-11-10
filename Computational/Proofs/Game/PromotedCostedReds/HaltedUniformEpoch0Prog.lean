/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Step -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Tracker-Halted Promoted `CostedReduction` for `uniformStart`

Constructs `uniformStartRedHalted`, the `KemFailSessionTrack`-halted `CostedReduction` witness
for `uniformStartDistinguisherTrackHalted` over `atomicSessionOps` and `coinOnlyIface`. Proves
`GRedBounded` bounds and exact evaluation agreement with `KemFailTrackBridge.runRTrackHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Iface Expr Comp CostedReduction bits
  reductionSizeBudget bind_congr_of_mem_support'
  atomicSessionOps coinOnlyIface e2eSessionCodec BV256)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet (RootKey)
open CryptoGames.Ratchet.LibsignalInst (libsignalSessionSchemeFromEpoch0Keys ratchetKeyAdmissible
  configR1OnCurve)
open CryptoGames.Ratchet.LibsignalSim (kemTrackEnc)
open CryptoGames.SM (GameState Adversary initState spec MakesAtMostQueries
  orE boolEq letE_eval orE_eval boolEq_eval)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey GhostState)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState stepKemFailSend
  stepKemFailDeliver)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes liftStateT paramsIdsWithSpqr paramsV1 sessionSchemeFixedSpk)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables (e2eOps)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsTy e2eGsEnc e2eGsB e2eGsWin)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest
  atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims liftTy
  liftVal liftExpr liftExpr_cost liftExpr_eval pullEnv renExpr renExpr_cost renExpr_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (eval_eq_simulateQ_of_enc
  isQueryBoundP_of_makesAtMostQueries liftVal_smQenc e2eSessionCodec_rdec_liftVal_smRenc
  liftExpr_size_le renExpr_size bits_succ_le session_cost_le_ratchetCostBudget
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness (KemTrackDeliverInv
  KemTrackDeliverInv.mono)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono size_le_budget_of_log_cost)
open Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Init (KemFailSessionTrack
  initKemFailSessionTrack libsignalSessionPqrOf transmitRSessionTrackHalted
  challRSessionTrackHalted deliverRSessionTrackHalted oracleImplRSessionTrackHalted
  runRSessionTrackHalted uniformStartDistinguisherTrackHalted
  oracleImplRSessionTrackHalted_epoch0Keys_eq_fixedSpk
  kemSessionTrackT sessionHaltedStTy kemSessionTrackEnc sessionHaltedEnc
  initEpoch0GsTrackC initEpoch0GsTrackC_queries_zero initEpoch0GsTrackC_cost
  initEpoch0GsTrackC_size_le epoch0TrackInitImpl initEpoch0GsTrackC_eval epoch0TrackInitImpl_inv
  oracleImplRSessionTrackHalted_preserves_b oracleImplRSessionTrackHalted_inv)
open Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Step (r1OracleStepTrackC
  r1OracleStepTrackC_queries_zero r1OracleStepTrackC_cost r1OracleStepTrackC_size_le
  r1OracleStepTrackC_eval)

export Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Init
  (uniformStartDistinguisherTrackHalted kemSessionTrackT sessionHaltedStTy
   kemSessionTrackEnc sessionHaltedEnc)

/-! ## Helpers -/

section Helpers

@[expose] def finRen {S : Sig} {s t u v : Ty S} : Var [s, u] v → Var [s, t, u] v
  | .zero => .zero
  | .succ .zero => .succ (.succ .zero)

@[expose] def uniformStartHaltedFinishE (C : Crypto) (K : MlKem) {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (ℓ : ℕ) :
    Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [sessionHaltedStTy ℓ Pt, .bool] .bool :=
  .letE (.fst .v0)
    (renExpr finRen
      (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT) (Γ := [e2eGsTy ℓ, .bool])
          (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0))))

theorem cost_uniformStartHaltedFinishE_le (C : Crypto) (K : MlKem) {Pt : Type}
    [DecidableEq Pt] [Zero Pt] (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (ℓ : ℕ) :
    (uniformStartHaltedFinishE C K Dh encPt encT decT lam ℓ).cost ≤ 500 := by
  let finE2E := orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT) (Γ := [e2eGsTy ℓ, .bool])
    (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0)
  have h := liftExpr_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) finE2E
  dsimp only [uniformStartHaltedFinishE, finE2E] at h ⊢
  simp only [renExpr_cost, orE, boolEq, e2eGsB, e2eGsWin, Expr.v0, Expr.v1, Expr.cost] at h ⊢
  omega

theorem size_uniformStartHaltedFinishE_le (C : Crypto) (K : MlKem) {Pt : Type}
    [DecidableEq Pt] [Zero Pt] (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (ℓ : ℕ) :
    (uniformStartHaltedFinishE C K Dh encPt encT decT lam ℓ).size ≤ 500 := by
  let finE2E := orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT) (Γ := [e2eGsTy ℓ, .bool])
    (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0)
  have h := liftExpr_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) finE2E
  dsimp only [uniformStartHaltedFinishE, finE2E] at h ⊢
  simp only [renExpr_size, orE, boolEq, e2eGsB, e2eGsWin, Expr.v0, Expr.v1, Expr.size] at h ⊢
  omega

theorem eval_uniformStartHaltedFinishE (C : Crypto) (K : MlKem) {Pt : Type}
    [DecidableEq Pt] [Zero Pt] (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (ℓ : ℕ)
    (s : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (ts : KemFailSessionTrack C.F Bytes) (b' : Bool) :
    (uniformStartHaltedFinishE C K Dh encPt encT decT lam ℓ).eval
      (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (s, ts)) (.cons b' .nil)) =
      (s.b == b' || s.win) := by
  unfold uniformStartHaltedFinishE
  rw [letE_eval, renExpr_eval]
  have hpull :
      pullEnv (finRen (u := .bool))
        (.cons ((Expr.fst (Expr.v0 (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam))).eval
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (s, ts)) (Env.cons (t := .bool) b' .nil)))
          (.cons (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt) (s, ts)) (.cons b' .nil))) =
      .cons (liftVal (Pt := Pt) (e2eGsEnc s)) (.cons b' .nil) := rfl
  rw [hpull]
  have hev := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT) (Γ := [e2eGsTy ℓ, .bool])
      (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0))
    (.cons (e2eGsEnc s) (.cons b' .nil))
  change (liftExpr (orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT)
      (Γ := [e2eGsTy ℓ, .bool]) (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0))).eval
      (.cons (liftVal (Pt := Pt) (e2eGsEnc s)) (.cons b' .nil)) = _ at hev
  rw [hev]
  simp [orE_eval, boolEq_eval, e2eGsB, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Expr.v1, liftVal]

@[expose] def flatSt2 {S₁ S₂ : Type} {m : Type → Type} [Functor m] {α : Type}
    (c : StateT S₁ (StateT S₂ m) α) : StateT (S₁ × S₂) m α :=
  fun ⟨s₁, s₂⟩ => (fun ⟨⟨a, s₁'⟩, s₂'⟩ => (a, (s₁', s₂'))) <$> ((c.run s₁).run s₂)

theorem simulateQ_run_flatSt2 {ι : Type} {ospec : OracleSpec.{0, 0} ι} {S₁ S₂ α : Type}
    (impl : QueryImpl ospec (StateT S₁ (StateT S₂ ProbComp)))
    (oa : OracleComp ospec α) (s₁ : S₁) (s₂ : S₂) :
    ((simulateQ impl oa).run s₁).run s₂ =
      (fun ⟨a, ⟨s₁', s₂'⟩⟩ => ((a, s₁'), s₂')) <$>
        (simulateQ (fun q => flatSt2 (impl q)) oa).run (s₁, s₂) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      LawfulFunctor.id_map, StateT.run_bind]
    rw [show (flatSt2 (impl q)).run (s₁, s₂) =
        (fun ⟨⟨a, s₁'⟩, s₂'⟩ => (a, (s₁', s₂'))) <$> (((impl q).run s₁).run s₂) from rfl]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine OracleComp.bind_congr' rfl fun ⟨⟨u, s₁'⟩, s₂'⟩ => ?_
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih u s₁' s₂'

end Helpers

/-! ## Tracker-halted reduction and bounds -/

section Reduction

variable (C : Crypto) (K : MlKem) {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt) (ℓ q qep : ℕ)

@[expose] def uniformStartRedHaltedReal :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) (.prod BV256 BV256) .unit .bool .bool where
  σ := sessionHaltedStTy ℓ Pt
  init := initEpoch0GsTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
  handle := r1OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep
  finish := .ret (uniformStartHaltedFinishE C K Dh encPt encT decT lam ℓ)

/-- Tracker-halted `CostedReduction` witness for `uniformStartDistinguisherTrackHalted`. -/
@[expose] def uniformStartRedHalted :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) (.prod BV256 BV256) .unit .bool .bool :=
  if ℓ < 10 ^ 6 then
    uniformStartRedHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep
  else
    dummyBoolSessionRed (coinOnlyIface ℓ Pt) (.prod BV256 BV256)

abbrev uniformStartDistinguisherProgHalted :=
  uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep

private theorem q_add_eleven_le_ratchetCostBudget (q' qep' : ℕ) :
    q' + 11 ≤ ratchetCostBudget q' qep' := by
  have h := session_cost_le_ratchetCostBudget q' qep' 100 (400 * q') 0 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem uniformStartRedHalted_totalQueries_zero :
    (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  unfold uniformStartRedHalted
  split_ifs with hℓ
  · simp [uniformStartRedHaltedReal, CostedReduction.totalQueries, initEpoch0GsTrackC_queries_zero,
      r1OracleStepTrackC_queries_zero, Comp.queries]
  · exact dummyBoolSessionRed_totalQueries _ _ _ _ _

theorem uniformStartRedHalted_totalCost_le {qep' : ℕ} (hqep : qep ≤ qep') :
    (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold uniformStartRedHalted
  split_ifs with hℓ
  · have hinit := initEpoch0GsTrackC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
    have hstep := r1OracleStepTrackC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep
    have hfin := cost_uniformStartHaltedFinishE_le C K Dh encPt encT decT lam ℓ
    have hb3 : bits (2 + 1) = 2 := by decide
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1 ((uniformStartRedHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost + 16) ≤
          175100000 + 15000 * q + 64 * bits qep' := by
      dsimp only [uniformStartRedHaltedReal]
      omega
    have hmul :
        q * max 1
          ((uniformStartRedHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost + 16) ≤
          q * (175100000 + 15000 * q + 64 * bits qep') :=
      Nat.mul_le_mul_left q hhandle
    have hfin_le :
        (uniformStartRedHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤ 1000 := by
      dsimp only [uniformStartRedHaltedReal, Comp.cost]
      omega
    have htot :
        (uniformStartRedHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          3100000 + q * (175100000 + 15000 * q + 64 * bits qep') + 1000 := by
      dsimp only [uniformStartRedHaltedReal, CostedReduction.totalCost, coinOnlyIface,
        e2eSessionCodec] at hmul hfin_le ⊢
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 3100000 1000 175100000 15000 64
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

theorem uniformStartRedHalted_size_le_of_clamp {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  unfold uniformStartRedHalted
  split_ifs with hℓ
  · have hinit := initEpoch0GsTrackC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
    have hstep := r1OracleStepTrackC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep
    have hfin := size_uniformStartHaltedFinishE_le C K Dh encPt encT decT lam ℓ
    have hb3 : bits (2 + 1) = 2 := by decide
    have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
    have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbq1 : bits (q + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
    have hsz :
        (uniformStartRedHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
          1660000 + 191 * bits (ratchetCostBudget q qep') := by
      dsimp only [uniformStartRedHaltedReal, CostedReduction.size, Comp.size]
      omega
    exact size_le_budget_of_log_cost (by decide) (by decide) hsz
  · exact (dummyBoolSessionRed_size_le (coinOnlyIface ℓ Pt) (.prod BV256 BV256)).trans
      (Nat.le_add_right _ _)

theorem uniformStartRedHalted_size_le {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact uniformStartRedHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep (by omega)

theorem uniformStartRedHalted_gRedBounded_of_clamp {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (uniformStartRedHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (uniformStartRedHalted_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep_B)
    (Nat.le_of_eq (uniformStartRedHalted_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem uniformStartRedHalted_gRedBounded_of_le {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (uniformStartRedHalted_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (uniformStartRedHalted_size_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep_q)
    (Nat.le_of_eq (uniformStartRedHalted_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem uniformStartRedHalted_gRedBounded (hqep : qep ≤ q + 10) :
    GRedBounded (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep) :=
  uniformStartRedHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep
    hqep (Nat.le_refl qep)

theorem uniformStartRedHalted_gRedBounded_succ (hqep : qep ≤ q + 10) :
    GRedBounded (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q (qep + 1)) :=
  uniformStartRedHalted_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep
    hqep (Nat.le_succ qep)

/-! ## Evaluation agreement -/

theorem uniformStartRedHalted_eval
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (rc : RootKey × BitVec 256) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) rc =
      uniformStartDistinguisherTrackHalted (paramsV1 C K idA idB) K ℓ
        (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep A rc := by
  unfold uniformStartRedHalted; simp only [hℓ, ↓reduceIte]
  set cfg := configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)
  set sm := libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2
  have hSmEq := oracleImplRSessionTrackHalted_epoch0Keys_eq_fixedSpk C K idA idB ℓ 3 qep rc 0 cfg
  let M2 := StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (KemFailSessionTrack C.F Bytes) ProbComp)
  let impl2 : QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) M2 :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget M2 +
      oracleImplRSessionTrackHalted C.F K sm 3 qep cfg
  let so : QueryImpl (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes) ProbComp) :=
    fun qy => flatSt2 (impl2 qy)
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes × KemFailSessionTrack C.F Bytes → Prop :=
    fun m s => m ≤ q ∧ SmReachBounded C K (q - m) s.1 ∧
      KemTrackDeliverInv C.F K (q - m) (kemTrackEnc s.2.1) ∧ s.2.2.length ≤ q - m
  have hsim := eval_eq_simulateQ_of_enc
    (uniformStartRedHaltedReal C K Dh encPt encT decT idA idB lam ℓ q qep)
    (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt)) Inv (epoch0TrackInitImpl C K idA idB ℓ) so
    (fun s b' => pure (s.1.b == b' || s.1.win))
    q rc (initEpoch0GsTrackC_eval idA idB rc)
    (fun r hr => by simpa [Inv, Nat.sub_self] using epoch0TrackInitImpl_inv C K idA idB ℓ rc hr)
    (fun n ⟨s₁, s₂⟩ => by
      dsimp only [coinOnlyIface, Iface.fwdU]
      change ((fun ⟨⟨a, s₁'⟩, s₂'⟩ => (a, (s₁', s₂'))) <$>
          (((StateT.lift (StateT.lift
            (liftM (OracleSpec.query (spec := unifSpec) n)))).run s₁).run s₂)) = _
      simp [StateT.run_lift, -bind_pure_comp, map_eq_bind_pure_comp, Function.comp_def])
    (fun m sq s hs => by
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (r1OracleStepTrackC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
              (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep).eval
              (.cons (sessionHaltedEnc s) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id (sessionHaltedEnc (ℓ := ℓ) (Pt := Pt)) <$> (so (.inr sq)).run s
        have hstepEv := r1OracleStepTrackC_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) q (2 + 1) qep
          idA idB 0 s.1 s.2.1 s.2.2 sq (hs.2.1.mono (by omega)) (hs.2.2.1.mono (by omega))
          (hs.2.2.2.trans (by omega))
        rw [show (so (.inr sq)).run s =
            (fun ⟨⟨a, s₁'⟩, s₂'⟩ => (a, (s₁', s₂'))) <$>
              (((oracleImplRSessionTrackHalted C.F K sm 3 qep cfg sq).run s.1).run (s.2.1, s.2.2))
            from rfl, hstepEv, ← hSmEq]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine OracleComp.bind_congr' rfl fun ⟨⟨ans, s'⟩, ts'⟩ => congrArg pure ?_
        exact Prod.ext (e2eSessionCodec_rdec_liftVal_smRenc (Pt := Pt) sq ans) rfl
      · intro r hr
        rw [show (so (.inr sq)).run s =
            (fun ⟨⟨a, s₁'⟩, s₂'⟩ => (a, (s₁', s₂'))) <$>
              (((oracleImplRSessionTrackHalted C.F K sm 3 qep cfg sq).run s.1).run (s.2.1, s.2.2))
            from rfl, hSmEq] at hr
        simp only [support_map, Set.mem_image] at hr
        obtain ⟨w, hw, rfl⟩ := hr
        have hinv := oracleImplRSessionTrackHalted_inv C K idA idB ℓ 3 qep (q - (m + 1)) 0 cfg sq
          s.1 s.2.1 s.2.2 hs.2.1 hs.2.2.1 hs.2.2.2 hw
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact ⟨by omega, heq ▸ hinv.1, heq ▸ hinv.2.1, heq ▸ hinv.2.2⟩)
    (fun s b' _ => by
      dsimp only [uniformStartRedHaltedReal, Comp.eval]
      rw [eval_uniformStartHaltedFinishE C K Dh encPt encT decT lam ℓ s.1 s.2 b'])
    (fun {m n} s hmn hn => ⟨by omega, hn.2.1.mono (by omega), hn.2.2.1.mono (by omega), by omega⟩)
    (fun _ => A) (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  unfold uniformStartDistinguisherTrackHalted runRSessionTrackHalted epoch0TrackInitImpl
  simp only [bind_assoc, pure_bind]
  refine OracleComp.bind_congr' rfl fun b => OracleComp.bind_congr' rfl fun k => ?_
  have hb_pres : ∀ {α : Type}
      (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
      (s : GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (ts : KemFailSessionTrack C.F Bytes)
      (r : (α × GameState (GhostState Bytes) (Plain ℓ) Bytes) × KemFailSessionTrack C.F Bytes),
      r ∈ support (((simulateQ impl2 oa).run s).run ts) → r.1.2.b = s.b := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro s ts r hr0
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
    | query_bind qy mx ih =>
      intro s ts r hr0
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        LawfulFunctor.id_map, StateT.run_bind, mem_support_bind_iff] at hr0
      obtain ⟨⟨⟨u, s'⟩, ts'⟩, hst, hr0⟩ := hr0
      have hs' : s'.b = s.b := by
        rcases qy with n | sq
        · change ((u, s'), ts') ∈ support
            (((StateT.lift (StateT.lift (QueryImpl.ofLift unifSpec ProbComp n))).run s).run ts)
            at hst
          simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hst
          obtain ⟨_, -, heq⟩ := hst
          cases heq; rfl
        · dsimp only [impl2, HAdd.hAdd, QueryImpl.add] at hst
          exact oracleImplRSessionTrackHalted_preserves_b C.F K sm 3 qep cfg sq s ts hst
      exact (ih u s' ts' r hr0).trans hs'
  let s₀ := initState sm.sendPart k b
  let ts₀ := initKemFailSessionTrack C.F Bytes (libsignalSessionPqrOf k)
  have h_rhs :
      (do
        let ((b', s₁), _) ← ((simulateQ impl2 A).run s₀).run ts₀
        pure (b == b' || s₁.win)) =
      (do
        let ((b', s₁), _) ← ((simulateQ impl2 A).run s₀).run ts₀
        pure (s₁.b == b' || s₁.win)) :=
    bind_congr_of_mem_support' _ fun ⟨⟨b', s₁⟩, ts₁⟩ hr => by
      have hbEq : s₁.b = b := hb_pres A s₀ ts₀ ((b', s₁), ts₁) hr
      dsimp only; rw [hbEq]
  change (do
      let (b', s₁) ← (simulateQ so A).run (s₀, ts₀)
      pure (s₁.1.b == b' || s₁.1.win)) =
    (do
      let ((b', s₁), _) ← ((simulateQ impl2 A).run s₀).run ts₀
      pure (b == b' || s₁.win))
  rw [h_rhs, simulateQ_run_flatSt2]
  simp only [so, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

@[expose] def refToBridgeTrack {F : ShaCompress} (t : KemFailTrackState F) :
    Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailTrackState F :=
  ⟨t.e, t.auth, t.c, t.st, t.sentB, t.sendCtr, t.cand⟩

private theorem refToBridgeTrack_stepSend {F : ShaCompress} (tr : KemFailTrackState F)
    (P : Party) (r : BitVec 512) :
    refToBridgeTrack (stepKemFailSend F K tr P r) =
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend F K
        (refToBridgeTrack tr) P r := by
  have hp : CryptoGames.LibsignalSM.Proofs.Refinement.kemBraidParty P =
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.kemBraidParty P := by
    cases P <;> rfl
  rcases tr with ⟨e, auth, c, st, sentB, sendCtr, cand⟩
  unfold stepKemFailSend
    Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailSend
  rw [hp]; dsimp only [refToBridgeTrack]
  rcases (st P).send K (CryptoVerification.LibsignalSpqrV1.coinBytes r) with _ | ⟨out, _⟩ <;>
    cases cand <;> rcases c with _ | s | _ <;> cases st P <;> rfl

private theorem refToBridgeTrack_stepDeliver {F : ShaCompress} (tr : KemFailTrackState F)
    (Q : Party) (j : ℕ) :
    refToBridgeTrack (stepKemFailDeliver F K tr Q j) =
      Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailDeliver F K
        (refToBridgeTrack tr) Q j := by
  rcases tr with ⟨e, auth, c, st, sentB, sendCtr, cand⟩
  unfold stepKemFailDeliver
    Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.stepKemFailDeliver
  dsimp only [refToBridgeTrack]
  rcases sentB[j]? with _ | ⟨m, _⟩
  · rfl
  · dsimp only
    rcases CryptoVerification.LibsignalSpqrV1.States.recv K (st Q) m with _ | out
    · rfl
    · dsimp only
      by_cases hm : m = CryptoVerification.SpqrV1Sync.Braid.noneMsg (e + 1#64) <;>
        cases c <;> simp [hm]

theorem uniformStartRedHalted_eval_bridge
    (A : Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (rc : RootKey × BitVec 256) (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (uniformStartRedHalted C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) rc =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ((b', s), _) ←
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.runRTrackHalted
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf
            C.F K (libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2) 3 qep
            (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) b A
        return (b == b' || s.win)) := by
  rw [uniformStartRedHalted_eval C K Dh encPt encT decT idA idB lam ℓ q qep A rc hA hℓ]
  unfold uniformStartDistinguisherTrackHalted runRSessionTrackHalted
    Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.runRTrackHalted
  simp only [bind_assoc]
  refine OracleComp.bind_congr' rfl fun b => OracleComp.bind_congr' rfl fun k => ?_
  set sm := libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2
  set cfg := configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)
  let MBridge := StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.KemFailSessionTrack
        C.F Bytes) ProbComp)
  let MRef := StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (KemFailSessionTrack C.F Bytes) ProbComp)
  have hLiftStateT : ∀ {σ τ α : Type} (x : StateT σ ProbComp α) (s : σ) (t : τ),
      ((liftStateT x : StateT σ (StateT τ ProbComp) α).run s).run t =
        (x.run s >>= fun a => pure (a, t)) := fun _ _ _ => rfl
  have hsim : ∀ {α : Type}
      (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
      (s : GameState (GhostState Bytes) (Plain ℓ) Bytes) (ts : KemFailSessionTrack C.F Bytes),
      (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget MBridge +
          Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted
            C.F K sm 3 qep cfg) oa).run s).run (refToBridgeTrack ts.1, ts.2)) =
      Prod.map id (Prod.map refToBridgeTrack id) <$>
        (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget MRef +
            oracleImplRSessionTrackHalted C.F K sm 3 qep cfg) oa).run s).run ts) := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a => intro s ts; simp [Prod.map]
    | query_bind qy cont ih =>
      intro s ts
      have h1 : (((((QueryImpl.ofLift unifSpec ProbComp).liftTarget MBridge +
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted
              C.F K sm 3 qep cfg) qy).run s).run (refToBridgeTrack ts.1, ts.2)) =
          Prod.map id (Prod.map refToBridgeTrack id) <$>
            (((((QueryImpl.ofLift unifSpec ProbComp).liftTarget MRef +
                oracleImplRSessionTrackHalted C.F K sm 3 qep cfg) qy).run s).run ts) := by
        rcases qy with n | (((⟨P, m, r⟩ | ⟨P, m0, m1, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
        · dsimp only [MBridge, MRef, HAdd.hAdd, QueryImpl.add, QueryImpl.liftTarget]
          simp [Prod.map, -bind_pure_comp, map_eq_bind_pure_comp, Function.comp_def]
        · dsimp only [HAdd.hAdd, QueryImpl.add, oracleImplRSessionTrackHalted,
            transmitRSessionTrackHalted,
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted,
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.transmitRTrackHalted,
            liftM, monadLift, MonadLift.monadLift]
          cases h1 : cfg.sendOK s P
          · simp [h1, Prod.map]
          · cases h2 : s.win
            · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                StateT.run_get, StateT.run_lift, bind_assoc, map_bind, pure_bind]
              refine OracleComp.bind_congr' rfl fun ⟨coins, bad⟩ => ?_
              cases s.epMgmt 3 qep P bad with
              | none => simp [Prod.map]
              | some s1 =>
                simp only [StateT.run_bind, StateT.run_lift, StateT.run_get,
                  bind_assoc, pure_bind, ← refToBridgeTrack_stepSend (K := K) ts.1 P coins]
                have hc : (refToBridgeTrack (stepKemFailSend C.F K ts.1 P coins)).cand.isSome =
                    (stepKemFailSend C.F K ts.1 P coins).cand.isSome := rfl
                rw [hc]; split_ifs <;> simp [refToBridgeTrack, Prod.map]
            · simp [h1, h2, Prod.map]
        · dsimp only [HAdd.hAdd, QueryImpl.add, oracleImplRSessionTrackHalted,
            challRSessionTrackHalted,
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted,
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.challRTrackHalted,
            liftM, monadLift, MonadLift.monadLift]
          cases h1 : cfg.sendOK s P
          · simp [h1, Prod.map]
          · cases h2 : s.win
            · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                StateT.run_get, StateT.run_lift, bind_assoc, map_bind, pure_bind]
              refine OracleComp.bind_congr' rfl fun ⟨coins, bad⟩ => ?_
              cases s.epMgmt 3 qep P bad with
              | none => simp [Prod.map]
              | some s1 =>
                cases hs1 : s1.safeCh 3 P
                · simp [hs1, Prod.map]
                · cases hca : cfg.base.challAllowedIn (s1.epoch P)
                  · simp [hs1, hca, Prod.map]
                  · simp only [hs1, hca, Bool.not_true, Bool.or_self, Bool.false_eq_true,
                      ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_get,
                      bind_assoc, pure_bind,
                      ← refToBridgeTrack_stepSend (K := K) ts.1 P coins]
                    have hc : (refToBridgeTrack (stepKemFailSend C.F K ts.1 P coins)).cand.isSome =
                        (stepKemFailSend C.F K ts.1 P coins).cand.isSome := rfl
                    rw [hc]; split_ifs <;> simp [refToBridgeTrack, Prod.map]
            · simp [h1, h2, Prod.map]
        · dsimp only [HAdd.hAdd, QueryImpl.add, oracleImplRSessionTrackHalted,
            deliverRSessionTrackHalted,
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted,
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.deliverRTrackHalted]
          simp only [StateT.run_bind, StateT.run_lift, StateT.run_get,
            hLiftStateT, bind_assoc, map_bind, pure_bind]
          refine OracleComp.bind_congr' rfl fun ⟨res, s'⟩ => ?_
          rcases res with _ | (_ | ⟨_, _, _⟩)
          · simp [Prod.map]
          · simp [Prod.map]
          · dsimp only
            cases List.findIdx?
                (fun (wp : List (BitVec 8) × Party) =>
                  @BEq.beq (List (BitVec 8)) instBEqOfDecidableEq wp.1 w && wp.2 == Q.other)
                ts.2.reverse with
            | none => simp [Prod.map]
            | some j =>
              simp [StateT.run_modify, Prod.map, ← refToBridgeTrack_stepDeliver (K := K) ts.1 Q j]
        · dsimp only [HAdd.hAdd, QueryImpl.add, oracleImplRSessionTrackHalted,
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted]
          rw [hLiftStateT, hLiftStateT]
          simp [Prod.map, -bind_pure_comp, map_eq_bind_pure_comp, Function.comp_def]
        · dsimp only [HAdd.hAdd, QueryImpl.add, oracleImplRSessionTrackHalted,
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted]
          rw [hLiftStateT, hLiftStateT]
          simp [Prod.map, -bind_pure_comp, map_eq_bind_pure_comp, Function.comp_def]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        StateT.run_bind, h1, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine OracleComp.bind_congr' rfl fun ⟨⟨u, s'⟩, ts'⟩ => ?_
      simpa only [Prod.map, id_eq, map_eq_bind_pure_comp, Function.comp_def] using ih u s' ts'
  have hInit : (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.initKemFailTrack
      C.F (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf k),
      ([] : List (Bytes × Party))) =
    (refToBridgeTrack (initKemFailSessionTrack C.F Bytes (libsignalSessionPqrOf k)).1,
      (initKemFailSessionTrack C.F Bytes (libsignalSessionPqrOf k)).2) := rfl
  change (do
      let ((b', s), _) ←
        (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget MRef +
            oracleImplRSessionTrackHalted C.F K sm 3 qep cfg) A).run (initState sm.sendPart k b)).run
          (initKemFailSessionTrack C.F Bytes (libsignalSessionPqrOf k)))
      pure (b == b' || s.win)) =
    (do
      let ((b', s), _) ←
        (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget MBridge +
            Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.oracleImplRTrackHalted
              C.F K sm 3 qep cfg) A).run (initState sm.sendPart k b)).run
          (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.initKemFailTrack
            C.F (Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge.libsignalSessionPqrOf k),
            ([] : List (Bytes × Party))))
      pure (b == b' || s.win))
  rw [hInit, hsim A]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact OracleComp.bind_congr' rfl fun ⟨⟨b', s⟩, _⟩ => rfl

end Reduction

end Computational.Proofs.Game.PromotedCostedReds.HaltedUniformEpoch0Prog
