/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.HaltedSpkDefs
public import Computational.Proofs.E2E.SpkHop1

/-!
# Tracker-Halted Hop-2 Core Combinators

Defines `runHop2Track` — the `lazyImpl` evaluator for `hop2ImplTrackHalted` — and proves `withLazy`
congruence, `prfReal` unfolding, `patchGamePartyIdx` commutation, and absorbing-state reductions.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.HaltedSpkHop2Core

open scoped BigOperators ENNReal
open OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack
  challRTrackHalted initKemFailTrack transmitRTrackHalted)
open Computational.Proofs.E2E.HaltedSpkDefs (challRTrackHalted_mapSt_eq challRTrackHalted_support
  hop2DeliverTrackHalted hop2DeliverTrackHalted_run hop2GameTrackHalted hop2ImplTrackHalted
  hop2LiftTrackHalted hop2PrfRedKTrackHalted liftHop2NoTrackM transmitRTrackHalted_mapSt_eq
  transmitRTrackHalted_support updateKemFailOnDeliver)
open CryptoGames (MACScheme Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (GhostState KeyPair LengthsOk Params PublicKey
  SessionState SignalMessage currentVersion)
open CryptoGames.MACScheme (evalQuery prfSpec)
open CryptoGames.Ratchet (RootKey expandPRG extractPRF)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible)
open CryptoGames.SM (Adversary GameState MakesAtMostQueries RecvResult corrR spec)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E (Bytes Hop2Aux Hop2Comp Hop2Hyb Hop2M Hop2Out configRefuseEarlyBobCorr
  hop2Deliver hop2Inject hop2Lift hop2Recv hop2Unif sessionSchemeU)
open CryptoVerification.E2E.SpkHop1 (Hop2Absorbed Hop2LastDone Hop2State IsHop2Post LookupEq
  bind_eq_of_support bind_le_of_support challR_support_stSendStep challR_support_win_true
  corrR_support_stSendStep corrR_support_win_true evalDist_lazyImpl_cons_fresh
  evalDist_lazyStep_discard hop2DeliverPost hop2DeliverPost_isHop2Post hop2Deliver_run_eq_post
  hop2Deliver_run_withLazy hop2InjectPost hop2InjectPost_isHop2Post hop2Inject_run_eq_post
  hop2Inject_run_withLazy hop2LazyKey hop2OffChainOut
  hop2RecvWithPost_support_bad_true hop2RecvWithPost_support_done hop2RecvWithPost_withLazy
  lazyImpl lazyStep patchGamePartyIdx patchGamePartyIdx_epMgmt patchGamePartyIdx_noBobEpoch0
  patchGamePartyIdx_record patchPartyIdx pureStepHyb pureStepImpl send_patchPartyIdx_eq
  simulateQ_lazyImpl_evalQuery simulateQ_lazyImpl_hop2Impl_pureStep simulateQ_lazyImpl_hop2Unif
  simulateQ_lazyImpl_liftM simulateQ_pureStepImpl_liftM stateT_lift_probComp_run
  stateT_lift_run_hop2 transmitR_support_stSendStep transmitR_support_win_true withLazy
  withLazy_self)
open CryptoVerification.LibsignalSpqrV1 (MlKem)

section Core

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-! ## `runHop2Track` evaluator -/

/-- Run an adversary computation `oa` in `hop2ImplTrackHalted` under `lazyImpl` starting from
game/hook state `st`, session tracker `tr`, and PRF table `tbl`, returning `st'.2.bad`. -/
def runHop2Track {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) : ProbComp Bool :=
  (simulateQ (lazyImpl (Pt := Pt)) (do
    let ((_, st'), _) ←
      ((simulateQ (hop2ImplTrackHalted P K Dh encT decT qep s h) oa).run st).run tr
    return st'.2.bad)).run' tbl

omit [SampleableType Pt] in
@[simp] theorem runHop2Track_pure {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (a : β) (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    runHop2Track P K Dh encT decT qep s h (pure a) st tr tbl = pure st.2.bad := rfl

omit [SampleableType Pt] in
theorem runHop2Track_bind_query {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (k : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range t →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    runHop2Track P K Dh encT decT qep s h
      (liftM (OracleSpec.query (spec := unifSpec +
          spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) t) >>= k)
      st tr tbl =
      (do
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          (((hop2ImplTrackHalted P K Dh encT decT qep s h t).run st).run tr)).run tbl
        runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) := by
  unfold runHop2Track
  simp only [StateT.run'_eq, simulateQ_bind, simulateQ_pure, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, StateT.run_bind, StateT.run_pure,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rfl

omit [SampleableType Pt] in
theorem runHop2Track_unif {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (u : unifSpec.Domain)
    (k : unifSpec.Range u →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        (((hop2ImplTrackHalted P K Dh encT decT qep s h (.inl u)).run st).run tr)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) =
    (do
      let a ← (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _)
      runHop2Track P K Dh encT decT qep s h (k a) st tr tbl) := by
  simp [hop2ImplTrackHalted, lazyImpl, QueryImpl.add_apply_inl, StateT.run_lift,
    StateT.run_monadLift, monadLift_self, map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType Pt] in
theorem runHop2Track_hop2LiftTrackHalted {ℓ : ℕ} {α β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (KemFailSessionTrack P.C.F Bytes) ProbComp) α)
    (k : α → OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ)
    (tr : KemFailSessionTrack P.C.F Bytes) (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        (((hop2LiftTrackHalted m).run (withLazy l st)).run tr)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) =
    (do
      let r ← (m.run st.1).run tr
      runHop2Track P K Dh encT decT qep s h (k r.1.1) (withLazy l (r.1.2, st.2)) r.2 tbl) := by
  simp [hop2LiftTrackHalted, withLazy]

omit [SampleableType Pt] in
theorem runHop2Track_hop2LiftTrackHalted' {ℓ : ℕ} {α β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (m : StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (StateT (KemFailSessionTrack P.C.F Bytes) ProbComp) α)
    (k : α → OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        (((hop2LiftTrackHalted m).run st).run tr)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) =
    (do
      let r ← (m.run st.1).run tr
      runHop2Track P K Dh encT decT qep s h (k r.1.1) (r.1.2, st.2) r.2 tbl) := by
  simp [hop2LiftTrackHalted]

omit [SampleableType Pt] in
theorem runHop2Track_deliver {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (x : Party × Bytes)
    (k : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        (((hop2DeliverTrackHalted P K Dh encT decT s h x).run st).run tr)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) =
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) ((hop2Deliver P Dh encT decT s h x).run st)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1) z.1.2
        (updateKemFailOnDeliver P.C.F K tr x z.1.1) z.2) := by
  rw [hop2DeliverTrackHalted_run]
  simp [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind]

omit [SampleableType Pt] in
theorem runHop2Track_noTrack {ℓ : ℕ} {α β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (m : Hop2M Pt ℓ α)
    (k : α → OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        (((liftHop2NoTrackM m).run st).run tr)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) =
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (m.run st)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1) z.1.2 tr z.2) := by
  simp [liftHop2NoTrackM, StateT.run_lift, map_eq_bind_pure_comp, simulateQ_bind,
    StateT.run_bind, bind_assoc]

omit [SampleableType Pt] in
theorem runHop2Track_corr {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (Q : Party)
    (k : Option (GhostState Bytes) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        (((liftHop2NoTrackM (hop2Lift (corrR (configRefuseEarlyBobCorr decT encT) Q))).run st).run tr)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) =
    (do
      let r ← (corrR (configRefuseEarlyBobCorr decT encT) Q).run st.1
      runHop2Track P K Dh encT decT qep s h (k r.1) (r.2, st.2) tr tbl) := by
  rw [runHop2Track_noTrack]
  simp [hop2Lift]

/-! ## `withLazy` congruence and `prfReal` unfolding -/

omit [SampleableType Pt] in
theorem simulateQ_hop2ImplTrackHalted_withLazy_congr {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    {l₁ l₂ : List ((ℕ × Pt) × BitVec 256)} (hlook : LookupEq l₁ l₂) :
    (do let ((_, st'), _) ←
          ((simulateQ (hop2ImplTrackHalted P K Dh encT decT qep s h) oa).run (withLazy l₁ st)).run tr
        return st'.2.bad) =
    (do let ((_, st'), _) ←
          ((simulateQ (hop2ImplTrackHalted P K Dh encT decT qep s h) oa).run (withLazy l₂ st)).run tr
        return st'.2.bad) := by
  induction oa using OracleComp.inductionOn generalizing st tr l₁ l₂ with
  | pure a =>
    simp [StateT.run_pure, withLazy]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    rcases t with u | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · simp only [hop2ImplTrackHalted, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        bind_assoc, pure_bind]
      refine bind_congr fun a => ih a st tr hlook
    · simp only [hop2ImplTrackHalted, hop2LiftTrackHalted, StateT.run_mk, withLazy, bind_assoc,
        pure_bind]
      refine bind_congr fun r => ih r.1.1 (r.1.2, st.2) r.2 hlook
    · simp only [hop2ImplTrackHalted, hop2LiftTrackHalted, StateT.run_mk, withLazy, bind_assoc,
        pure_bind]
      refine bind_congr fun r => ih r.1.1 (r.1.2, st.2) r.2 hlook
    · dsimp only [hop2ImplTrackHalted]
      rw [hop2DeliverTrackHalted_run, hop2DeliverTrackHalted_run]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      by_cases hwin : st.1.win = true
      · have hw1 : (withLazy l₁ st).1.win = true := hwin
        have hw2 : (withLazy l₂ st).1.win = true := hwin
        unfold hop2Deliver
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hw1, hw2, ↓reduceIte,
          StateT.run_pure, pure_bind]
        exact ih none st (updateKemFailOnDeliver P.C.F K tr (Q, c) none) hlook
      · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
        cases hin : st.1.inTransit Q.other c with
        | none =>
          have hw1 : (withLazy l₁ st).1.win = false := hwinF
          have hw2 : (withLazy l₂ st).1.win = false := hwinF
          have hi1 : (withLazy l₁ st).1.inTransit Q.other c = none := hin
          have hi2 : (withLazy l₂ st).1.inTransit Q.other c = none := hin
          unfold hop2Deliver
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hw1, hw2, Bool.false_eq_true,
            ↓reduceIte, hi1, hi2, StateT.run_pure, pure_bind]
          exact ih none st (updateKemFailOnDeliver P.C.F K tr (Q, c) none) hlook
        | some r =>
          rw [hop2Deliver_run_withLazy P Dh encT decT s h Q c l₁ st r hwinF hin,
              hop2Deliver_run_withLazy P Dh encT decT s h Q c l₂ st r hwinF hin]
          simp only [bind_assoc]
          refine bind_congr fun rc => ?_
          cases hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
          | none =>
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            refine bind_congr fun res => ih _ _ _ hlook
          | some val =>
            rcases val with ⟨tq, msg, sc⟩
            dsimp only []
            rw [hlook tq]
            cases l₂.lookup tq with
            | some u =>
              simp only [pure_bind]
              exact ih _ _ _ hlook
            | none =>
              simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
              refine bind_congr fun u => ih _ _ _ (hlook.cons tq u)
    · dsimp only [hop2ImplTrackHalted]
      simp only [liftHop2NoTrackM, StateT.run_mk, StateT.run_lift,
        bind_assoc, pure_bind]
      by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
      · have hg1 : ((withLazy l₁ st).1.win || ((withLazy l₁ st).1.inTransit Q.other c).isSome ||
            !((withLazy l₁ st).1.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg
        have hg2 : ((withLazy l₂ st).1.win || ((withLazy l₂ st).1.inTransit Q.other c).isSome ||
            !((withLazy l₂ st).1.safeInj 3) ||
              !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg
        unfold hop2Inject
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hg1, hg2, ↓reduceIte,
          StateT.run_pure, pure_bind]
        exact ih none st tr hlook
      · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
        rw [hop2Inject_run_withLazy P Dh encT decT qep s h Q c l₁ st hgF,
            hop2Inject_run_withLazy P Dh encT decT qep s h Q c l₂ st hgF]
        simp only [bind_assoc]
        refine bind_congr fun rc => ?_
        cases hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
        | none =>
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
          refine bind_congr fun res => ih _ _ tr hlook
        | some val =>
          rcases val with ⟨tq, msg, sc⟩
          dsimp only []
          rw [hlook tq]
          cases l₂.lookup tq with
          | some u =>
            simp only [pure_bind]
            exact ih _ _ tr hlook
          | none =>
            simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
            refine bind_congr fun u => ih _ _ tr (hlook.cons tq u)
    · simp only [hop2ImplTrackHalted, liftHop2NoTrackM, hop2Lift, StateT.run_mk, StateT.run_lift,
        withLazy, bind_assoc, pure_bind]
      refine bind_congr fun r => ih r.1 (r.2, st.2) tr hlook

omit [SampleableType Pt] in
theorem runHop2Track_withLazy_congr {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256))
    {l₁ l₂ : List ((ℕ × Pt) × BitVec 256)} (hlook : LookupEq l₁ l₂) :
    runHop2Track P K Dh encT decT qep s h oa (withLazy l₁ st) tr tbl =
      runHop2Track P K Dh encT decT qep s h oa (withLazy l₂ st) tr tbl := by
  unfold runHop2Track
  rw [simulateQ_hop2ImplTrackHalted_withLazy_congr P K Dh encT decT qep s h oa st tr hlook]

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_tbl_cons_fresh {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (I : Pt) (hfresh : tbl.lookup I = none) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
        runHop2Track P K Dh encT decT qep s h oa st tr ((I, u) :: tbl)] =
      𝒟[runHop2Track P K Dh encT decT qep s h oa st tr tbl] :=
  evalDist_lazyImpl_cons_fresh _ I tbl hfresh

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_tbl_discard {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (I : Pt) :
    𝒟[(do
      let (_, tbl') ← (lazyStep I).run tbl
      runHop2Track P K Dh encT decT qep s h oa st tr tbl')] =
      𝒟[runHop2Track P K Dh encT decT qep s h oa st tr tbl] := by
  simpa [runHop2Track, StateT.run'_eq, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc] using
    evalDist_lazyStep_discard I (do
      let ((_, fin), _) ←
        ((simulateQ (hop2ImplTrackHalted P K Dh encT decT qep s h) oa).run st).run tr
      return fin.2.bad) tbl

omit [SampleableType Pt] in
theorem runHop2Track_recvWithPost {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (Q : Party) (c : Bytes)
    (l : List ((ℕ × Pt) × BitVec 256)) (st : Hop2State Pt ℓ)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256))
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s Q c (st.1.st Q) post)
    (k : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
        let rc ← hop2Unif (Pt := Pt)
        let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l st)
        return post res.1 res.2)).run tbl
      runHop2Track P K Dh encT decT qep s h (k z.1.1) z.1.2 (tr_next z.1.1) z.2) =
    (do
      let rc ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      match hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
      | none =>
        let z ← (simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy [] st))).run tbl
        let p := post z.1.1 st
        runHop2Track P K Dh encT decT qep s h (k p.1) (withLazy l p.2) (tr_next p.1) z.2
      | some (tq, msg, sc) =>
        match l.lookup tq with
        | some u =>
          let p := post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st
          runHop2Track P K Dh encT decT qep s h (k p.1) (withLazy l p.2) (tr_next p.1) tbl
        | none =>
          let u ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          let p := post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st
          runHop2Track P K Dh encT decT qep s h (k p.1) (withLazy ((tq, u) :: l) p.2)
            (tr_next p.1) tbl) := by
  have h1 : (do
      let rc ← hop2Unif (Pt := Pt)
      let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l st)
      return post res.1 res.2) =
    (do
      let rc ← hop2Unif (Pt := Pt)
      match hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
      | none =>
        (fun r => ((post r.1 st).1, withLazy l (post r.1 st).2)) <$>
          (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy [] st)
      | some (tq, msg, sc) =>
        match l.lookup tq with
        | some u =>
          pure ((post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st).1,
            withLazy l (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st).2)
        | none =>
          (fun u => ((post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st).1,
            withLazy ((tq, u) :: l) (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u) st).2)) <$>
            hop2Unif (Pt := Pt)) := by
    refine bind_congr fun rc => ?_
    exact hop2RecvWithPost_withLazy P Dh encT decT s h Q c (st.1.st Q) post hpost rc l st
  rw [h1]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif, stateT_lift_probComp_run,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr fun rc => ?_
  cases hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
  | none =>
    simp [simulateQ_bind]
  | some val =>
    rcases val with ⟨tq, msg, sc⟩
    dsimp only []
    cases l.lookup tq with
    | some u =>
      simp [StateT.run_pure]
    | none =>
      simp [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
        StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_recvWithPost_cons_fresh {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (Q : Party) (c : Bytes)
    (st : Hop2State Pt ℓ)
    (tr_next : Option (RecvResult (Plain ℓ)) → KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256))
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (RecvResult (Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s Q c (st.1.st Q) post)
    (k : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (l : List ((ℕ × Pt) × BitVec 256)) (tq : ℕ × Pt) (hfresh : l.lookup tq = none)
    (ih : ∀ a st' tr' tbl' l', l'.lookup tq = none →
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
          runHop2Track P K Dh encT decT qep s h (k a) (withLazy ((tq, u) :: l') st') tr' tbl'] =
        𝒟[runHop2Track P K Dh encT decT qep s h (k a) (withLazy l' st') tr' tbl']) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
        do
          let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
            let rc ← hop2Unif (Pt := Pt)
            let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run
              (withLazy ((tq, u) :: l) st)
            return post res.1 res.2)).run tbl
          runHop2Track P K Dh encT decT qep s h (k z.1.1) z.1.2 (tr_next z.1.1) z.2] =
    𝒟[do
        let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
          let rc ← hop2Unif (Pt := Pt)
          let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l st)
          return post res.1 res.2)).run tbl
        runHop2Track P K Dh encT decT qep s h (k z.1.1) z.1.2 (tr_next z.1.1) z.2] := by
  have hl1 : ∀ u, (do
        let z ← (simulateQ (lazyImpl (Pt := Pt)) (do
          let rc ← hop2Unif (Pt := Pt)
          let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run
            (withLazy ((tq, u) :: l) st)
          return post res.1 res.2)).run tbl
        runHop2Track P K Dh encT decT qep s h (k z.1.1) z.1.2 (tr_next z.1.1) z.2) = _ :=
    fun u => runHop2Track_recvWithPost P K Dh encT decT qep s h Q c ((tq, u) :: l) st tr_next tbl
      post hpost k
  simp_rw [hl1, runHop2Track_recvWithPost P K Dh encT decT qep s h Q c l st tr_next tbl post hpost k]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun rc => ?_
  cases hop2LazyKey P Dh encT decT h (st.1.st Q) c st with
  | none =>
    dsimp only []
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
    refine evalDist_bind_congr _ _ _ fun z => ?_
    exact ih (post z.1.1 st).1 (post z.1.1 st).2 (tr_next (post z.1.1 st).1) z.2 l hfresh
  | some val =>
    rcases val with ⟨tq', msg, sc⟩
    dsimp only [List.lookup]
    by_cases heq : (tq' == tq) = true
    · have htq : tq' = tq := eq_of_beq heq
      subst htq
      simp only [heq, hfresh]
    · have hne : (tq' == tq) = false := Bool.eq_false_iff.mpr heq
      have hne_val : tq' ≠ tq := beq_eq_false_iff_ne.mp hne
      simp only [hne]
      cases hlook' : l.lookup tq' with
      | some u' =>
        dsimp only []
        exact ih _ _ _ tbl l hfresh
      | none =>
        dsimp only []
        rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
        refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun u' => ?_
        have hswap : ∀ u,
            runHop2Track P K Dh encT decT qep s h
              (k (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).1)
              (withLazy ((tq', u') :: (tq, u) :: l)
                (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).2)
              (tr_next (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).1) tbl =
            runHop2Track P K Dh encT decT qep s h
              (k (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).1)
              (withLazy ((tq, u) :: (tq', u') :: l)
                (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).2)
              (tr_next (post (hop2OffChainOut P ℓ (st.1.st Q) msg sc rc u') st).1) tbl :=
          fun u => runHop2Track_withLazy_congr P K Dh encT decT qep s h _ _ _ tbl
            (LookupEq.swap_cons tq' tq u' u l hne_val)
        simp_rw [hswap]
        have hfresh' : (((tq', u') :: l).lookup tq) = none := by
          have hne_symm : (tq == tq') = false := beq_eq_false_iff_ne.mpr hne_val.symm
          simp [List.lookup, hne_symm, hfresh]
        exact ih _ _ _ tbl ((tq', u') :: l) hfresh'

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_lazy_cons_fresh {ℓ : ℕ} {β : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) β)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (l : List ((ℕ × Pt) × BitVec 256)) (tq : ℕ × Pt)
    (hfresh : l.lookup tq = none) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun u =>
        runHop2Track P K Dh encT decT qep s h oa (withLazy ((tq, u) :: l) st) tr tbl] =
      𝒟[runHop2Track P K Dh encT decT qep s h oa (withLazy l st) tr tbl] := by
  induction oa using OracleComp.inductionOn generalizing st tr tbl l with
  | pure a =>
    simp only [runHop2Track_pure, withLazy, OracleComp.evalDist_bind_const ($ᵗ BitVec 256)]
  | query_bind t k ih =>
    simp_rw [runHop2Track_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · simp_rw [runHop2Track_unif]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine evalDist_bind_congr _ _ _ fun a => ih a st tr tbl l hfresh
    · dsimp only [hop2ImplTrackHalted]
      simp_rw [runHop2Track_hop2LiftTrackHalted]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine evalDist_bind_congr _ _ _ fun r => ih r.1.1 (r.1.2, st.2) r.2 tbl l hfresh
    · dsimp only [hop2ImplTrackHalted]
      simp_rw [runHop2Track_hop2LiftTrackHalted]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine evalDist_bind_congr _ _ _ fun r => ih r.1.1 (r.1.2, st.2) r.2 tbl l hfresh
    · dsimp only [hop2ImplTrackHalted]
      have hdel_L : (fun u =>
          do
            let z ← (simulateQ (lazyImpl (Pt := Pt))
              (((hop2DeliverTrackHalted P K Dh encT decT s h (Q, c)).run
                (withLazy ((tq, u) :: l) st)).run tr)).run tbl
            runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) =
          (fun u =>
          do
            let z ← (simulateQ (lazyImpl (Pt := Pt))
              ((hop2Deliver P Dh encT decT s h (Q, c)).run (withLazy ((tq, u) :: l) st))).run tbl
            runHop2Track P K Dh encT decT qep s h (k z.1.1) z.1.2
              (updateKemFailOnDeliver P.C.F K tr (Q, c) z.1.1) z.2) :=
        funext fun u =>
          runHop2Track_deliver P K Dh encT decT qep s h (Q, c) k (withLazy ((tq, u) :: l) st) tr tbl
      have hdel_R := runHop2Track_deliver P K Dh encT decT qep s h (Q, c) k (withLazy l st) tr tbl
      erw [hdel_L, hdel_R]
      by_cases hwin : st.1.win = true
      · have hstep : ∀ l',
            (hop2Deliver P Dh encT decT s h (Q, c)).run (withLazy l' st) =
            pure (none, withLazy l' st) := by
          intro l'
          have hw : (withLazy l' st).1.win = true := hwin
          unfold hop2Deliver
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hw, ↓reduceIte, StateT.run_pure]
        simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
        exact ih none st _ tbl l hfresh
      · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
        cases hin : st.1.inTransit Q.other c with
        | none =>
          have hstep : ∀ l',
              (hop2Deliver P Dh encT decT s h (Q, c)).run (withLazy l' st) =
              pure (none, withLazy l' st) := by
            intro l'
            have hw : (withLazy l' st).1.win = false := hwinF
            have hi : (withLazy l' st).1.inTransit Q.other c = none := hin
            unfold hop2Deliver
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hw, Bool.false_eq_true,
              ↓reduceIte, hi, StateT.run_pure]
          simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
          exact ih none st _ tbl l hfresh
        | some r =>
          have hstep : ∀ l',
              (hop2Deliver P Dh encT decT s h (Q, c)).run (withLazy l' st) =
              (do
                let rc ← hop2Unif (Pt := Pt)
                let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l' st)
                return hop2DeliverPost P s Q c (st.1.st Q) r res.1 res.2) :=
            fun l' => hop2Deliver_run_eq_post P Dh encT decT s h Q c (withLazy l' st) r hwinF hin
          simp_rw [hstep]
          exact evalDist_runHop2Track_recvWithPost_cons_fresh P K Dh encT decT qep s h Q c st
            (updateKemFailOnDeliver P.C.F K tr (Q, c)) tbl _
            (hop2DeliverPost_isHop2Post P s Q c (st.1.st Q) r) k l tq hfresh ih
    · dsimp only [hop2ImplTrackHalted]
      simp_rw [runHop2Track_noTrack]
      by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
      · have hstep : ∀ l',
            (hop2Inject P Dh encT decT qep s h (Q, c)).run (withLazy l' st) =
            pure (none, withLazy l' st) := by
          intro l'
          have hgl : ((withLazy l' st).1.win || ((withLazy l' st).1.inTransit Q.other c).isSome ||
              !((withLazy l' st).1.safeInj 3) ||
                !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg
          unfold hop2Inject
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hgl, ↓reduceIte, StateT.run_pure]
        simp only [hstep, simulateQ_pure, StateT.run_pure, pure_bind]
        exact ih none st tr tbl l hfresh
      · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
        have hstep : ∀ l',
            (hop2Inject P Dh encT decT qep s h (Q, c)).run (withLazy l' st) =
            (do
              let rc ← hop2Unif (Pt := Pt)
              let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run (withLazy l' st)
              return hop2InjectPost P qep s Q c (st.1.st Q) res.1 res.2) :=
          fun l' => hop2Inject_run_eq_post P Dh encT decT qep s h Q c (withLazy l' st) hgF
        simp_rw [hstep]
        exact evalDist_runHop2Track_recvWithPost_cons_fresh P K Dh encT decT qep s h Q c st
          (fun _ => tr) tbl _
          (hop2InjectPost_isHop2Post (Pt := Pt) (ℓ := ℓ) P qep s Q c (st.1.st Q)) k l tq hfresh ih
    · dsimp only [hop2ImplTrackHalted]
      have hcorr_L : (fun u =>
          do
            let z ← (simulateQ (lazyImpl (Pt := Pt))
              (((liftHop2NoTrackM (hop2Lift (corrR (configRefuseEarlyBobCorr decT encT) y_corr))).run
                (withLazy ((tq, u) :: l) st)).run tr)).run tbl
            runHop2Track P K Dh encT decT qep s h (k z.1.1.1) z.1.1.2 z.1.2 z.2) =
          (fun u =>
          do
            let r ← (corrR (configRefuseEarlyBobCorr decT encT) y_corr).run st.1
            runHop2Track P K Dh encT decT qep s h (k r.1) (withLazy ((tq, u) :: l) (r.2, st.2)) tr tbl) :=
        funext fun u =>
          runHop2Track_corr P K Dh encT decT qep s h y_corr k (withLazy ((tq, u) :: l) st) tr tbl
      have hcorr_R := runHop2Track_corr P K Dh encT decT qep s h y_corr k (withLazy l st) tr tbl
      erw [hcorr_L, hcorr_R]
      rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256)]
      refine evalDist_bind_congr _ _ _ fun r => ih r.1 (r.2, st.2) tr tbl l hfresh

omit [SampleableType Pt] in
theorem simulateQ_lazyImpl_hop2ImplTrackHalted_pureStep {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (k' : ℕ) (rc : RootKey × BitVec 256) (f : Pt → BitVec 256)
    (t : (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt))
      (((hop2ImplTrackHalted P K Dh encT decT qep s (pureStepHyb k' rc f) t).run st).run tr)).run tbl =
      (·, tbl) <$> simulateQ (pureStepImpl f)
        (((hop2ImplTrackHalted P K Dh encT decT qep s (pureStepHyb k' rc f) t).run st).run tr) := by
  rcases t with u | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
  · simp [hop2ImplTrackHalted, lazyImpl, pureStepImpl, StateT.run_lift, StateT.run_monadLift,
      monadLift_self, StateT.run_pure, bind_assoc, pure_bind, map_eq_bind_pure_comp,
      Function.comp_apply]
  · simp [hop2ImplTrackHalted, hop2LiftTrackHalted, StateT.run_bind, simulateQ_bind,
      simulateQ_lazyImpl_liftM, simulateQ_pureStepImpl_liftM, StateT.run_pure,
      map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  · simp [hop2ImplTrackHalted, hop2LiftTrackHalted, StateT.run_bind, simulateQ_bind,
      simulateQ_lazyImpl_liftM, simulateQ_pureStepImpl_liftM, StateT.run_pure,
      map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  · dsimp only [hop2ImplTrackHalted]
    rw [hop2DeliverTrackHalted_run]
    have hp := simulateQ_lazyImpl_hop2Impl_pureStep P Dh encT decT qep s k' rc f
      (.inr (.inl (.inl (.inr (Q, c))))) st tbl
    dsimp only [ CryptoVerification.E2E.hop2Impl ] at hp
    simp only [map_eq_bind_pure_comp, simulateQ_bind, StateT.run_bind, simulateQ_pure,
      StateT.run_pure, Function.comp_apply, bind_assoc, pure_bind] at hp ⊢
    rw [hp]
    simp [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  · dsimp only [hop2ImplTrackHalted, liftHop2NoTrackM]
    have hp := simulateQ_lazyImpl_hop2Impl_pureStep P Dh encT decT qep s k' rc f
      (.inr (.inl (.inr (Q, c)))) st tbl
    dsimp only [ CryptoVerification.E2E.hop2Impl ] at hp
    simp only [StateT.run_mk, StateT.run_lift, map_eq_bind_pure_comp, simulateQ_bind,
      StateT.run_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply, bind_assoc,
      pure_bind] at hp ⊢
    rw [hp]
    simp [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  · simp [hop2ImplTrackHalted, liftHop2NoTrackM, hop2Lift, StateT.run_lift, StateT.run_bind,
      simulateQ_bind, simulateQ_lazyImpl_liftM, simulateQ_pureStepImpl_liftM, StateT.run_pure,
      map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]

omit [SampleableType Pt] in
theorem simulateQ_prfReal_hop2ImplTrackHalted_run {ℓ : ℕ} {α : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (k' : ℕ) (rc : RootKey × BitVec 256) (f : Pt → BitVec 256)
    (m : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) :
    (simulateQ (lazyImpl (Pt := Pt))
      (((simulateQ (hop2ImplTrackHalted P K Dh encT decT qep s (pureStepHyb k' rc f)) m).run st).run tr)).run tbl =
      (·, tbl) <$> simulateQ (pureStepImpl f)
        (((simulateQ (hop2ImplTrackHalted P K Dh encT decT qep s (pureStepHyb k' rc f)) m).run st).run tr) := by
  induction m using OracleComp.inductionOn generalizing st tr tbl with
  | pure a => simp [StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      StateT.run_bind,
      simulateQ_lazyImpl_hop2ImplTrackHalted_pureStep P K Dh encT decT qep s k' rc f t st tr tbl,
      map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    refine bind_congr fun z => ?_
    simpa only [map_eq_bind_pure_comp, Function.comp_apply, id_eq] using ih z.1.1 z.1.2 z.2 tbl

omit [SampleableType Pt] in
theorem simulateQ_prfReal_hop2ImplTrackHalted_eq_runHop2Track {ℓ : ℕ} {α : Type}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (k' : ℕ) (rc : RootKey × BitVec 256) (f : Pt → BitVec 256)
    (m : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes) :
    (do
        let ((_, fin), _) ← simulateQ (pureStepImpl f)
          (((simulateQ (hop2ImplTrackHalted P K Dh encT decT qep s (pureStepHyb k' rc f)) m).run st).run tr)
        return fin.2.bad : ProbComp Bool) =
      runHop2Track P K Dh encT decT qep s (pureStepHyb k' rc f) m st tr [] := by
  unfold runHop2Track
  rw [StateT.run'_eq, simulateQ_bind, StateT.run_bind,
    simulateQ_prfReal_hop2ImplTrackHalted_run P K Dh encT decT qep s k' rc f m st tr []]
  simp [StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]

/-! ## `patchGamePartyIdx` commutation and absorbing states -/

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitRTrackHalted_patchGamePartyIdx {ℓ : ℕ} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (m : ℕ) (rk : RootKey) (idx : Party → Option ℕ)
    (s : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (y : Party × Plain ℓ × Option (BitVec 512)) :
    (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) y).run (patchGamePartyIdx m rk idx s)).run tr) =
      Prod.map (Prod.map id (patchGamePartyIdx m rk idx)) id <$>
        (((transmitRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) y).run s).run tr) := by
  refine transmitRTrackHalted_mapSt_eq P.C.F K (sessionSchemeU P ℓ) (sessionSchemeU P ℓ) 3 qep
    (configRefuseEarlyBobCorr decT encT) (configRefuseEarlyBobCorr decT encT)
    (patchGamePartyIdx m rk idx) y s tr
    (patchGamePartyIdx_noBobEpoch0 m rk idx s y.1) rfl
    (patchGamePartyIdx_epMgmt m rk idx s 3 qep y.1) ?_
  intro _ bad s₁ coins _
  have hst1 : (patchGamePartyIdx m rk idx s₁).st y.1 =
      patchPartyIdx m rk (idx y.1) (s₁.st y.1) := rfl
  have hep1 : (patchGamePartyIdx m rk idx s₁).epoch y.1 = s₁.epoch y.1 := rfl
  have hidx1 : (patchGamePartyIdx m rk idx s₁).idx y.1 = s₁.idx y.1 := rfl
  dsimp only []
  rw [hst1, hep1, hidx1]
  simp only [sessionSchemeU, send_patchPartyIdx_eq]
  exact ⟨trivial, patchGamePartyIdx_record m rk idx s₁ 3 y.1 (P.send (s₁.st y.1) y.2.1.toList coins).1
    _ false⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challRTrackHalted_patchGamePartyIdx {ℓ : ℕ} (P : Params Bytes (BitVec 512)) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (m : ℕ) (rk : RootKey) (idx : Party → Option ℕ)
    (s : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (tr : KemFailSessionTrack P.C.F Bytes)
    (y : Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) :
    (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
        (configRefuseEarlyBobCorr decT encT) y).run (patchGamePartyIdx m rk idx s)).run tr) =
      Prod.map (Prod.map id (patchGamePartyIdx m rk idx)) id <$>
        (((challRTrackHalted P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) y).run s).run tr) := by
  refine challRTrackHalted_mapSt_eq P.C.F K (sessionSchemeU P ℓ) (sessionSchemeU P ℓ) 3 qep
    (configRefuseEarlyBobCorr decT encT) (configRefuseEarlyBobCorr decT encT)
    (patchGamePartyIdx m rk idx) y s tr
    (patchGamePartyIdx_noBobEpoch0 m rk idx s y.1) rfl rfl
    (patchGamePartyIdx_epMgmt m rk idx s 3 qep y.1)
    (fun _ _ _ _ => ⟨rfl, rfl, rfl⟩) ?_
  intro _ bad s₁ msg coins _
  have hst1 : (patchGamePartyIdx m rk idx s₁).st y.1 =
      patchPartyIdx m rk (idx y.1) (s₁.st y.1) := rfl
  have hep1 : (patchGamePartyIdx m rk idx s₁).epoch y.1 = s₁.epoch y.1 := rfl
  have hidx1 : (patchGamePartyIdx m rk idx s₁).idx y.1 = s₁.idx y.1 := rfl
  dsimp only []
  rw [hst1, hep1, hidx1]
  simp only [sessionSchemeU, send_patchPartyIdx_eq]
  exact ⟨trivial, patchGamePartyIdx_record m rk idx s₁ 3 y.1 (P.send (s₁.st y.1) msg.toList coins).1
    _ true⟩

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_eq_zero_of_done {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (hdone : Hop2LastDone P s st) :
    𝒟[runHop2Track P K Dh encT decT qep s h oa st tr tbl] {true} = 0 := by
  refine le_antisymm ?_ zero_le
  induction oa using OracleComp.inductionOn generalizing st tr tbl with
  | pure a =>
    rw [runHop2Track_pure, hdone.bad_false]
    simp
  | query_bind t k ih =>
    rw [runHop2Track_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2Track_unif]
      exact bind_le_of_support _ _ (measurableSet_singleton _) fun a _ => ih a st tr tbl hdone
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_hop2LiftTrackHalted']
      refine bind_le_of_support _ _ (measurableSet_singleton _) fun r hr => ?_
      rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) y_tr st.1 tr hr with heq | hmem
      · rw [heq]; exact ih none st r.2 tbl hdone
      · exact ih r.1.1 (r.1.2, st.2) r.2 tbl
          (hdone.of_stSendStep (transmitR_support_stSendStep P decT encT qep y_tr st.1 r.1 hmem))
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_hop2LiftTrackHalted']
      refine bind_le_of_support _ _ (measurableSet_singleton _) fun r hr => ?_
      rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) y_ch st.1 tr hr with heq | hmem
      · rw [heq]; exact ih none st r.2 tbl hdone
      · exact ih r.1.1 (r.1.2, st.2) r.2 tbl
          (hdone.of_stSendStep (challR_support_stSendStep P decT encT qep y_ch st.1 r.1 hmem))
    · dsimp only [hop2ImplTrackHalted]
      erw [runHop2Track_deliver P K Dh encT decT qep s h (Q, c) k st tr tbl]
      refine bind_le_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      by_cases hwin : st.1.win = true
      · unfold hop2Deliver at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ih none st _ tbl hdone
      · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
        cases hin : st.1.inTransit Q.other c with
        | none =>
          unfold hop2Deliver at hz
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hwinF, Bool.false_eq_true,
            ↓reduceIte, hin, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; exact ih none st _ tbl hdone
        | some r =>
          rw [hop2Deliver_run_eq_post P Dh encT decT s h Q c st r hwinF hin] at hz
          exact ih z.1.1 z.1.2 _ z.2 (hop2RecvWithPost_support_done P Dh encT decT s h Q c st tbl _
            (hop2DeliverPost_isHop2Post P s Q c (st.1.st Q) r) hdone z hz)
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_noTrack]
      refine bind_le_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
      · unfold hop2Inject at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ih none st tr tbl hdone
      · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
        rw [hop2Inject_run_eq_post P Dh encT decT qep s h Q c st hgF] at hz
        exact ih z.1.1 z.1.2 tr z.2 (hop2RecvWithPost_support_done P Dh encT decT s h Q c st tbl _
          (hop2InjectPost_isHop2Post P qep s Q c (st.1.st Q)) hdone z hz)
    · dsimp only [hop2ImplTrackHalted]
      erw [runHop2Track_corr P K Dh encT decT qep s h y_corr k st tr tbl]
      exact bind_le_of_support _ _ (measurableSet_singleton _) fun r hr =>
        ih r.1 (r.2, st.2) tr tbl (hdone.of_stSendStep
          (corrR_support_stSendStep P decT encT y_corr st.1 r hr))

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_eq_one_of_bad_true {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (hbad : st.2.bad = true) :
    𝒟[runHop2Track P K Dh encT decT qep s h oa st tr tbl] {true} = 1 := by
  induction oa using OracleComp.inductionOn generalizing st tr tbl with
  | pure a =>
    rw [runHop2Track_pure, hbad]
    simp
  | query_bind t k ih =>
    rw [runHop2Track_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2Track_unif]
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun a _ => ih a st tr tbl hbad
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_hop2LiftTrackHalted']
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r _ =>
        ih r.1.1 (r.1.2, st.2) r.2 tbl hbad
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_hop2LiftTrackHalted']
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r _ =>
        ih r.1.1 (r.1.2, st.2) r.2 tbl hbad
    · dsimp only [hop2ImplTrackHalted]
      erw [runHop2Track_deliver P K Dh encT decT qep s h (Q, c) k st tr tbl]
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      by_cases hwin : st.1.win = true
      · unfold hop2Deliver at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ih none st _ tbl hbad
      · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
        cases hin : st.1.inTransit Q.other c with
        | none =>
          unfold hop2Deliver at hz
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hwinF, Bool.false_eq_true,
            ↓reduceIte, hin, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; exact ih none st _ tbl hbad
        | some r =>
          rw [hop2Deliver_run_eq_post P Dh encT decT s h Q c st r hwinF hin] at hz
          exact ih z.1.1 z.1.2 _ z.2 (hop2RecvWithPost_support_bad_true P Dh encT decT s h Q c
            st tbl _ (hop2DeliverPost_isHop2Post P s Q c (st.1.st Q) r) hbad z hz)
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_noTrack]
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
      · unfold hop2Inject at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ih none st tr tbl hbad
      · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
        rw [hop2Inject_run_eq_post P Dh encT decT qep s h Q c st hgF] at hz
        exact ih z.1.1 z.1.2 tr z.2 (hop2RecvWithPost_support_bad_true P Dh encT decT s h Q c
          st tbl _ (hop2InjectPost_isHop2Post P qep s Q c (st.1.st Q)) hbad z hz)
    · dsimp only [hop2ImplTrackHalted]
      erw [runHop2Track_corr P K Dh encT decT qep s h y_corr k st tr tbl]
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r _ =>
        ih r.1 (r.2, st.2) tr tbl hbad

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_eq_of_win_true {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (hwin : st.1.win = true) :
    𝒟[runHop2Track P K Dh encT decT qep s h oa st tr tbl] {true} =
      𝒟[(pure st.2.bad : ProbComp Bool)] {true} := by
  induction oa using OracleComp.inductionOn generalizing st tr tbl with
  | pure a =>
    rw [runHop2Track_pure]
  | query_bind t k ih =>
    rw [runHop2Track_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2Track_unif]
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun a _ => ih a st tr tbl hwin
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_hop2LiftTrackHalted']
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr => ?_
      rcases transmitRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) y_tr st.1 tr hr with heq | hmem
      · rw [heq]; exact ih none st r.2 tbl hwin
      · exact ih r.1.1 (r.1.2, st.2) r.2 tbl
          (transmitR_support_win_true P decT encT qep y_tr st.1 hwin r.1 hmem)
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_hop2LiftTrackHalted']
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr => ?_
      rcases challRTrackHalted_support P.C.F K (sessionSchemeU P ℓ) 3 qep
          (configRefuseEarlyBobCorr decT encT) y_ch st.1 tr hr with heq | hmem
      · rw [heq]; exact ih none st r.2 tbl hwin
      · exact ih r.1.1 (r.1.2, st.2) r.2 tbl
          (challR_support_win_true P decT encT qep y_ch st.1 hwin r.1 hmem)
    · dsimp only [hop2ImplTrackHalted]
      erw [runHop2Track_deliver P K Dh encT decT qep s h (Q, c) k st tr tbl]
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      unfold hop2Deliver at hz
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ih none st _ tbl hwin
    · dsimp only [hop2ImplTrackHalted]
      rw [runHop2Track_noTrack]
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      unfold hop2Inject at hz
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.true_or, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ih none st tr tbl hwin
    · dsimp only [hop2ImplTrackHalted]
      erw [runHop2Track_corr P K Dh encT decT qep s h y_corr k st tr tbl]
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr =>
        ih r.1 (r.2, st.2) tr tbl (corrR_support_win_true decT encT y_corr st.1 hwin r hr)

omit [SampleableType Pt] in
theorem evalDist_runHop2Track_of_absorbed {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool)
    (st : Hop2State Pt ℓ) (tr : KemFailSessionTrack P.C.F Bytes)
    (tbl : List (Pt × BitVec 256)) (habs : Hop2Absorbed st) :
    𝒟[runHop2Track P K Dh encT decT qep s h oa st tr tbl] {true} =
      𝒟[(pure st.2.bad : ProbComp Bool)] {true} := by
  rcases habs with hbad | hwin | ⟨hpA, hpB, hpos⟩
  · rw [evalDist_runHop2Track_eq_one_of_bad_true P K Dh encT decT qep s h oa st tr tbl hbad, hbad]
    simp
  · exact evalDist_runHop2Track_eq_of_win_true P K Dh encT decT qep s h oa st tr tbl hwin
  · cases hbad : st.2.bad with
    | true =>
      rw [evalDist_runHop2Track_eq_one_of_bad_true P K Dh encT decT qep s h oa st tr tbl hbad]
      simp
    | false =>
      rw [evalDist_runHop2Track_eq_zero_of_done P K Dh encT decT qep s h oa st tr tbl
        ⟨hbad, hpA, hpB, hpos⟩]
      simp

end Core

end Computational.Proofs.E2E.HaltedSpkHop2Core
