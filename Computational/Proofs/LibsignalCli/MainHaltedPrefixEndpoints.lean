/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
import Computational.Proofs.CryptoGames.FSAEAD.CellForgery
import Computational.Proofs.GameHop.GlobalHybrid
import VCVio.EvalDist.Monad.Basic

/-!
# Session-Tracked Prefix Hybrid Endpoint Identities

**Checked by Lean.** Proves the `k = 0` and `k = qStart` endpoint identities for
`bhPrefixHybExpWithSessionTracked` and equates the `secb = false` boolean bias of
`bhE2EExpWithKiSessionTracked` with the `boolDist` between the two endpoints.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec

namespace Computational.Proofs.LibsignalCli.MainHaltedPrefixEndpoints

open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.CellForgery (run_simulateQ_query_bind)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.SM (ConfigR GameState corrR samIfNec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (BHE2EDrvState BHE2ESmResp Bytes SampledSessionKey
  allTestedSessionsFresh bhDrvKiQueryOk bhE2EDrvInstClean bhE2EDrvWon bhE2EFinishStartSpk
  bhE2EGuard bhE2EInstIkACorr bhE2EMirror bhIsBobRecvSMQuery bhNoOpkRespPromoted bhTargetGameSpec
  deliverRM epMgmt_b injectRM liftStateT prob_bind_congr_of_support)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (ModelDriverKeyBitGen
  SessionHaltTracker
  bhClassifyTarget bhClassifyTargetOnly bhComposedPostObs bhComposedPostObsSessionTracked
  bhE2EDrvImplGenWithSessionTracked bhE2EDrvImplPrefixWithSessionTracked
  bhE2EDrvImplPrefixWithSessionTracked_run_eq_gen bhE2EDrvImplWithSessionTracked
  bhE2EExpWithKiSessionTracked bhE2ELocalStartGenWithSessionTracked bhE2ELocalStartSessionTracked
  bhE2EStepLocalSmSessionTracked bhE2EStepLocalSmSessionTracked_eq_filter bhFilterSmQuery
  bhFinishStartSpkGen bhMkKeyBitConst bhMkPrefixExact_false_eq_bhMkPrefixHyb
  bhMkPrefixExact_true_eq_bhMkPrefixHyb_succ bhMkPrefixHyb bhModeExpWithSessionTracked
  bhPrefixExactFullExpWithSessionTracked bhPrefixHybExpWithSessionTracked challRSessionTracked
  deliverRSessionTracked oracleImplRSessionTracked smSchemeTrackState stateT_run_lift
  stateT_run_liftM transmitRSessionTracked)

theorem bhPrefixExactFullExpWithSessionTracked_true_eq {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhPrefixExactFullExpWithSessionTracked T S ki P C K qep decT encT k true B =
      bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT (k + 1) B := by
  unfold bhPrefixExactFullExpWithSessionTracked bhPrefixHybExpWithSessionTracked
  rw [bhMkPrefixExact_true_eq_bhMkPrefixHyb_succ]

theorem bhPrefixExactFullExpWithSessionTracked_false_eq {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhPrefixExactFullExpWithSessionTracked T S ki P C K qep decT encT k false B =
      bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT k B := by
  unfold bhPrefixExactFullExpWithSessionTracked bhPrefixHybExpWithSessionTracked
  rw [bhMkPrefixExact_false_eq_bhMkPrefixHyb]

theorem bhE2ELocalStartGenWithSessionTracked_const_eq {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (initTrack : SampledSessionKey → τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (b : Bool)
    (σH : BHE2EDrvState S ℓ × List τ) (sid : SignalPqxdh.SessionId S) :
    bhE2ELocalStartGenWithSessionTracked initTrack ki C K (bhMkKeyBitConst b) σH sid =
      bhE2ELocalStartSessionTracked initTrack ki C K (some b) σH sid := by
  rcases σH with ⟨σ, tracks⟩
  dsimp only [bhE2ELocalStartGenWithSessionTracked, bhE2ELocalStartSessionTracked]
  cases hG : bhE2EGuard σ sid with
  | none => rfl
  | some val =>
    rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
    dsimp only
    simp only [bhMkKeyBitConst, bind_assoc, pure_bind]
    refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => bind_congr fun ac => ?_
    unfold bhFinishStartSpkGen bhE2EFinishStartSpk
    have hG2 : bhE2EGuard { σ with st := st2 } sid = bhE2EGuard σ sid := rfl
    rw [hG2, hG]
    cases kr1 with
    | drKeyResp dk =>
      cases kr2 with
      | spkSkResp sk =>
        by_cases hLen : (dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
            dk.pqrKey.length == 32 && sk.length == 32) = true <;>
          simp [hLen]
      | _ => rfl
    | _ => cases kr2 <;> rfl

/-- Every instance in `σ.insts` has challenge bit `b`. -/
def BHAllInstsBit {S : SignalPqxdh.Setup} {ℓ : ℕ} (b : Bool) (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ d ∈ σ.insts, ∀ gs, d.gs = some gs → gs.b = b

theorem bhAllInstsBit_empty {S : SignalPqxdh.Setup} {ℓ : ℕ} (b : Bool) :
    BHAllInstsBit b ({} : BHE2EDrvState S ℓ) := by
  rintro _ ⟨⟩

theorem bhE2EDrvWon_not_of_allInstsBit {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {b : Bool} {σ : BHE2EDrvState S ℓ} (h : BHAllInstsBit b σ) :
    bhE2EDrvWon σ (!b) = false := by
  unfold bhE2EDrvWon
  rw [List.any_eq_false]
  intro d hd
  cases hgs : d.gs with
  | none => simp
  | some gs =>
    have hb : gs.b = b := h d hd gs hgs
    cases b <;> simp [hb]

private theorem deliverRM_smSchemeTrackState_preserves_b {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C)
    (P : Party) (c : C) (gs : GameState St Msg C) (tr : τ)
    {p : (Option (CryptoGames.SM.RecvResult Msg) × GameState St Msg C) × τ}
    (hp : p ∈ support (((deliverRM (smSchemeTrackState sm) cfg (P, c)).run gs).run tr)) :
    p.1.2.b = gs.b := by
  unfold deliverRM smSchemeTrackState at hp
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
  cases h1 : gs.win
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hp
    cases htr : gs.inTransit P.other c with
    | none =>
      simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; rfl
    | some r =>
      simp only [htr, StateT.run_bind, stateT_run_lift, stateT_run_liftM, StateT.run_pure,
        bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at hp
      rcases hp with ⟨rc, _, hp⟩
      cases hrcv : sm.receive (gs.st P) c rc with
      | none =>
        simp only [hrcv] at hp
        split_ifs at hp <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hp <;>
          (subst hp; rfl)
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        simp only [hrcv] at hp
        split_ifs at hp <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hp <;>
          (subst hp; rfl)
  · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp; rfl

set_option maxHeartbeats 800000 in
theorem oracleImplRSessionTracked_preserves_b {Key St Msg Coins RCoins C τ : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (T : SessionHaltTracker St Msg Coins C Key τ)
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain) (gs : GameState St Msg C) (tr : τ)
    {p : ((CryptoGames.SM.spec St Msg Coins C).Range q × GameState St Msg C) × τ}
    (hp : p ∈ support (((oracleImplRSessionTracked T sm Δ qep cfg q).run gs).run tr)) :
    p.1.2.b = gs.b := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change p ∈ support (((transmitRSessionTracked T sm Δ qep cfg (P, m, r)).run gs).run tr) at hp
    unfold transmitRSessionTracked at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    cases h1 : cfg.sendOK gs P
    · simp only [h1, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hp
      subst hp; rfl
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
      cases h2 : gs.win
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_run_lift,
          stateT_run_liftM, bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at hp
        rcases hp with ⟨⟨coins, bad⟩, _, hp⟩
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
          subst hp; rfl
        | some s₁ =>
          simp only [hep, StateT.run_bind, stateT_run_lift, StateT.run_pure, bind_assoc,
            pure_bind, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
          rcases hp with ⟨⟨isBad, tr_mid⟩, _, hp⟩
          cases isBad
          · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hp
            subst hp; exact epMgmt_b gs s₁ Δ qep P bad hep
          · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
            subst hp; rfl
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
  · change p ∈ support (((challRSessionTracked T sm Δ qep cfg (P, m₀, m₁, r)).run gs).run tr) at hp
    unfold challRSessionTracked at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    cases h1 : cfg.sendOK gs P
    · simp only [h1, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hp
      subst hp; rfl
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
      cases h2 : gs.win
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_run_lift,
          stateT_run_liftM, bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at hp
        rcases hp with ⟨⟨coins, bad⟩, _, hp⟩
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
          subst hp; rfl
        | some s₁ =>
          simp only [hep] at hp
          cases h3 : (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · simp only [h3, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_run_lift,
              StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
              Set.mem_iUnion, Set.mem_singleton_iff] at hp
            rcases hp with ⟨⟨isBad, tr_mid⟩, _, hp⟩
            cases isBad
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hp
              subst hp; exact epMgmt_b gs s₁ Δ qep P bad hep
            · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
              subst hp; rfl
          · simp only [h3, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
            subst hp; rfl
      · simp only [h2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
  · change p ∈ support (((deliverRSessionTracked T sm cfg (P, c)).run gs).run tr) at hp
    unfold deliverRSessionTracked at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_lift, StateT.run_pure,
      bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨⟨res, gs'⟩, tr₁⟩, hdel, ⟨_, _, rfl⟩⟩
    exact deliverRM_smSchemeTrackState_preserves_b sm cfg P c gs tr (p := ((res, gs'), tr₁)) hdel
  · change p ∈ support (((injectRM (smSchemeTrackState sm) Δ qep cfg (P, c)).run gs).run tr) at hp
    unfold injectRM smSchemeTrackState at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    cases h1 : (gs.win || (gs.inTransit P.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_run_lift,
        stateT_run_liftM, StateT.run_pure, bind_assoc, pure_bind, support_bind,
        Set.mem_iUnion] at hp
      rcases hp with ⟨rc, _, hp⟩
      cases hrcv : sm.receive (gs.st P) c rc with
      | none =>
        simp only [hrcv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp; rfl
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        simp only [hrcv] at hp
        split_ifs at hp <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hp <;>
          (subst hp; rfl)
    · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; rfl
  · change p ∈ support ((corrR cfg P).run gs >>= fun a => pure (a, tr)) at hp
    unfold corrR at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨q_out, hcorr, rfl⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hcorr
    split_ifs at hcorr <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hcorr <;>
      (subst hcorr; rfl)

theorem bhE2EStepLocalSmSessionTracked_preserves_allInstsBit {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) (σH : BHE2EDrvState S ℓ × List τ) (hσ : BHAllInstsBit b σH.1)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {p : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    BHAllInstsBit b p.2.1 := by
  rw [bhE2EStepLocalSmSessionTracked_eq_filter] at hp
  by_cases hC : (!bhE2EDrvInstClean σH.1 i) = true
  · simp only [hC, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hσ
  · simp only [hC, Bool.false_eq_true, ↓reduceIte] at hp
    cases hi : σH.1.insts[i]? with
    | none =>
      rw [hi] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hσ
    | some d =>
      rw [hi] at hp
      cases him : σH.1.instMeta[i]? with
      | none =>
        rw [him] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact hσ
      | some im =>
        rw [him] at hp; dsimp only at hp
        split_ifs at hp
        · simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact hσ
        · cases hd : d.gs with
          | none =>
            rw [hd] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp; exact hσ
          | some gs =>
            rw [hd] at hp
            cases hf : bhFilterSmQuery d im sq with
            | none =>
              rw [hf] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
              subst hp; exact hσ
            | some q' =>
              rw [hf] at hp
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
              rcases hp with ⟨⟨⟨r, gs'⟩, tr'⟩, hsm, rfl⟩
              have hgs_b : gs.b = b := hσ d (List.mem_of_getElem? hi) gs hd
              have hgs'_b : gs'.b = b :=
                (oracleImplRSessionTracked_preserves_b T _ _ _ _ q' gs _ hsm).trans hgs_b
              intro d' hd' gs_d' hgs_d'
              rcases List.mem_or_eq_of_mem_set hd' with hd'_old | rfl
              · exact hσ d' hd'_old gs_d' hgs_d'
              · simp only [Option.some.injEq] at hgs_d'
                subst hgs_d'
                exact hgs'_b

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWithSessionTracked_const_preserves_allInstsBit {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (hσ : BHAllInstsBit b σH.1)
    {p : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support
      ((bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
        (bhMkKeyBitConst b) q).run σH)) :
    BHAllInstsBit b p.2.1 := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change p ∈ support ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, σH)) at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, rfl⟩; exact hσ
  · dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hσ
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hσ
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr, st'⟩, _, rfl⟩
      exact hσ
  · rcases σH with ⟨σ, tracks⟩
    dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
      bhE2ELocalStartGenWithSessionTracked_const_eq] at hp
    dsimp only [bhE2ELocalStartSessionTracked] at hp
    cases hG : bhE2EGuard σ sid with
    | none =>
      rw [hG] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hσ
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      rw [hG] at hp; dsimp only at hp
      simp only [bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, ac, _, rfl⟩
      unfold bhE2EFinishStartSpk
      have hG2 : bhE2EGuard { σ with st := st2 } sid = bhE2EGuard σ sid := rfl
      rw [hG2, hG]
      cases kr1 <;> cases kr2 <;> try exact hσ
      dsimp only
      split_ifs
      · intro d' hd' gs hgs
        rcases List.mem_append.mp hd' with hd' | hd'
        · exact hσ d' hd' gs hgs
        · rw [List.mem_singleton.mp hd'] at hgs
          simp only [Option.map_some, Option.some.injEq] at hgs
          subst hgs; rfl
      · exact hσ
  · dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨sr, σH'⟩, hsm, rfl⟩
    exact bhE2EStepLocalSmSessionTracked_preserves_allInstsBit T C K qep decT encT
      b σH hσ i sq hsm

theorem simulateQ_bhE2EDrvImplGenWithSessionTracked_const_preserves_allInstsBit {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) {α : Type}
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) (hσ : BHAllInstsBit b σH.1)
    {p : α × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support
      ((simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
        (bhMkKeyBitConst b)) oa).run σH)) :
    BHAllInstsBit b p.2.1 := by
  induction oa using OracleComp.inductionOn generalizing σH p with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hσ
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, support_bind] at hp
    rcases Set.mem_iUnion₂.mp hp with ⟨⟨u, σH'⟩, hstep, hp⟩
    exact ih u σH'
      (bhE2EDrvImplGenWithSessionTracked_const_preserves_allInstsBit T ki P C K qep
        decT encT b q σH hσ hstep) hp

theorem bhE2EStepLocalSmSessionTracked_with_b {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (b' : Bool) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    bhE2EStepLocalSmSessionTracked T C K qep decT encT
        ({ σH.1 with b := b' }, σH.2) i q =
      (fun p => (p.1, ({ p.2.1 with b := b' }, p.2.2))) <$>
        bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i q := by
  rcases σH with ⟨σ, tracks⟩
  rw [bhE2EStepLocalSmSessionTracked_eq_filter, bhE2EStepLocalSmSessionTracked_eq_filter]
  dsimp only
  have hCleanEq : bhE2EDrvInstClean { σ with b := b' } i = bhE2EDrvInstClean σ i := rfl
  rw [hCleanEq]
  by_cases hC : (!bhE2EDrvInstClean σ i) = true
  · simp [hC]
  · simp only [hC, Bool.false_eq_true, ↓reduceIte]
    cases hi : σ.insts[i]? with
    | none => simp [hi]
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp [hi, him]
      | some im =>
        simp only [hi, him]
        have hCorrEq : bhE2EInstIkACorr { σ with b := b' } d = bhE2EInstIkACorr σ d := rfl
        rw [hCorrEq]
        split_ifs
        · simp
        · cases d.gs with
          | none => simp
          | some gs =>
            cases bhFilterSmQuery d im q with
            | none => simp
            | some q' =>
              simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWithSessionTracked_with_b {τ : Type} {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ) (b' : Bool) :
    (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit q).run
        ({ σH.1 with b := b' }, σH.2) =
      (fun (r, σH') => (r, ({ σH'.1 with b := b' }, σH'.2))) <$>
        (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit q).run σH := by
  rcases σH with ⟨σ, tracks⟩
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, ({ σ with b := b' }, tracks))) =
      ((fun (r, σH') => (r, ({ σH'.1 with b := b' }, σH'.2))) <$>
        ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun u => pure (u, (σ, tracks))))
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · dsimp only [bhE2EDrvImplGenWithSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    have hBase : ({ σ with b := b' } : BHE2EDrvState S ℓ).toModelDriverBase =
        σ.toModelDriverBase := rfl
    have hMeta : ({ σ with b := b' } : BHE2EDrvState S ℓ).instMeta = σ.instMeta := rfl
    rw [hBase, hMeta]
    split_ifs
    · simp [StateT.run_pure]
    · simp [StateT.run_pure]
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
      rfl
  · dsimp only [bhE2EDrvImplGenWithSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure]
    unfold bhE2ELocalStartGenWithSessionTracked
    dsimp only
    have hG : bhE2EGuard { σ with b := b' } sid = bhE2EGuard σ sid := rfl
    rw [hG]
    cases bhE2EGuard σ sid with
    | none => simp
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨kr1, st1⟩ => bind_congr fun ⟨kr2, st2⟩ => bind_congr fun kb => ?_
      unfold bhFinishStartSpkGen
      have hG2 : bhE2EGuard { σ with b := b', st := st2 } sid =
          bhE2EGuard { σ with st := st2 } sid := rfl
      rw [hG2]
      cases bhE2EGuard { σ with st := st2 } sid with
      | none => rfl
      | some val2 =>
        rcases val2 with ⟨hdr2, bnd2, ⟨u2, j2⟩⟩
        cases kr1 <;> cases kr2 <;> try rfl
        dsimp only
        split_ifs <;> rfl
  · dsimp only [bhE2EDrvImplGenWithSessionTracked]
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind]
    have hSm := bhE2EStepLocalSmSessionTracked_with_b T C K qep decT encT
      (σ, tracks) b' i sq
    dsimp only at hSm
    rw [hSm]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

theorem simulateQ_bhE2EDrvImplWithSessionTracked_eq_gen_const {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool) (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ) :
    (simulateQ (bhE2EDrvImplWithSessionTracked T P ki C K qep decT encT) oa).run
        ({ σH.1 with b := b }, σH.2) =
      (fun (r, σH') => (r, ({ σH'.1 with b := b }, σH'.2))) <$>
        (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
          (bhMkKeyBitConst b)) oa).run σH := by
  induction oa using OracleComp.inductionOn generalizing σH with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind]
    have hStep :
        (bhE2EDrvImplWithSessionTracked T P ki C K qep decT encT q).run
            ({ σH.1 with b := b }, σH.2) =
          (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
            (bhMkKeyBitConst b) q).run ({ σH.1 with b := b }, σH.2) := by
      rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
      · rfl
      · rfl
      · dsimp only [bhE2EDrvImplWithSessionTracked, bhE2EDrvImplGenWithSessionTracked]
        simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure,
          bhE2ELocalStartGenWithSessionTracked_const_eq]
      · rfl
    rw [hStep,
      bhE2EDrvImplGenWithSessionTracked_with_b T ki P C K qep decT encT
        (bhMkKeyBitConst b) q σH b]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    exact bind_congr fun ⟨r, σH'⟩ => by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using ih r σH'

theorem bhPrefixHybExpWithSessionTracked_zero_eq {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT 0 B =
      bhModeExpWithSessionTracked T S ki P C K qep decT encT false B := by
  unfold bhPrefixHybExpWithSessionTracked bhModeExpWithSessionTracked
  have hmk : ∀ len : ℕ, bhMkPrefixHyb 0 len = bhMkKeyBitConst false := by
    intro len; funext kr1 kr2; simp [bhMkPrefixHyb, bhMkKeyBitConst]
  have hsim : ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
      (σH : BHE2EDrvState S ℓ × List τ),
      (simulateQ (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT
          (bhMkPrefixHyb 0)) oa).run σH =
        (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
          (bhMkKeyBitConst false)) oa).run σH := by
    intro oa σH
    induction oa using OracleComp.inductionOn generalizing σH with
    | pure x => rfl
    | query_bind q mx ih =>
      rw [run_simulateQ_query_bind, run_simulateQ_query_bind,
        bhE2EDrvImplPrefixWithSessionTracked_run_eq_gen, hmk]
      exact bind_congr fun ⟨r, σH'⟩ => ih r σH'
  rw [hsim]

theorem bhE2EStepLocalSmSessionTracked_insts_length_eq {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σH : BHE2EDrvState S ℓ × List τ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {p : BHE2ESmResp ℓ × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support (bhE2EStepLocalSmSessionTracked T C K qep decT encT σH i sq)) :
    p.2.1.insts.length = σH.1.insts.length ∧ p.2.2.length = σH.2.length := by
  rw [bhE2EStepLocalSmSessionTracked_eq_filter] at hp
  by_cases hC : (!bhE2EDrvInstClean σH.1 i) = true
  · simp only [hC, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨rfl, rfl⟩
  · simp only [hC, Bool.false_eq_true, ↓reduceIte] at hp
    cases hi : σH.1.insts[i]? with
    | none =>
      rw [hi] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨rfl, rfl⟩
    | some d =>
      rw [hi] at hp
      cases him : σH.1.instMeta[i]? with
      | none =>
        rw [him] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact ⟨rfl, rfl⟩
      | some im =>
        rw [him] at hp; dsimp only at hp
        split_ifs at hp
        · simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp; exact ⟨rfl, rfl⟩
        · cases hd : d.gs with
          | none =>
            rw [hd] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp; exact ⟨rfl, rfl⟩
          | some gs =>
            rw [hd] at hp
            cases hf : bhFilterSmQuery d im sq with
            | none =>
              rw [hf] at hp; simp only [support_pure, Set.mem_singleton_iff] at hp
              subst hp; exact ⟨rfl, rfl⟩
            | some q' =>
              rw [hf] at hp
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
              rcases hp with ⟨⟨⟨_, _⟩, _⟩, _, rfl⟩
              simp

set_option maxHeartbeats 800000 in
theorem bhE2EDrvImplGenWithSessionTracked_step_length {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (mkKeyBit : ModelDriverKeyBitGen)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σH : BHE2EDrvState S ℓ × List τ)
    {p : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Range q × (BHE2EDrvState S ℓ × List τ)}
    (hp : p ∈ support
      ((bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT mkKeyBit q).run σH)) :
    (bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = false →
      p.2.1.insts.length = σH.1.insts.length) ∧
    σH.1.insts.length ≤ p.2.1.insts.length ∧
    p.2.1.insts.length ≤ σH.1.insts.length + 1 := by
  rcases q with n | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
  · change p ∈ support ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, σH)) at hp
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨_, _, rfl⟩
    exact ⟨fun _ => rfl, le_rfl, Nat.le_succ _⟩
  · dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hp
    split_ifs at hp
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨fun _ => rfl, le_rfl, Nat.le_succ _⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨fun _ => rfl, le_rfl, Nat.le_succ _⟩
    · simp only [stateT_run_liftM, StateT.run_bind, StateT.run_set, StateT.run_pure,
        bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr, st'⟩, _, rfl⟩
      exact ⟨fun _ => rfl, le_rfl, Nat.le_succ _⟩
  · simp only [bhClassifyTarget, bhClassifyTargetOnly, Bool.true_eq_false, IsEmpty.forall_iff,
      true_and]
    dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, Prod.mk.eta, bind_pure] at hp
    unfold bhE2ELocalStartGenWithSessionTracked at hp
    cases hG : bhE2EGuard σH.1 sid with
    | none =>
      rw [hG] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ⟨le_rfl, Nat.le_succ _⟩
    | some val =>
      rcases val with ⟨hdr, bnd, ⟨u, j⟩⟩
      rw [hG] at hp; dsimp only at hp
      simp only [bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      rcases hp with ⟨⟨kr1, st1⟩, _, ⟨kr2, st2⟩, _, kb, _, rfl⟩
      unfold bhFinishStartSpkGen
      have hG2 : bhE2EGuard { σH.1 with st := st2 } sid = bhE2EGuard σH.1 sid := rfl
      rw [hG2, hG]
      cases kr1 <;> cases kr2 <;> try exact ⟨le_rfl, Nat.le_succ _⟩
      dsimp only
      split_ifs
      · simp
      · exact ⟨le_rfl, Nat.le_succ _⟩
  · dsimp only [bhE2EDrvImplGenWithSessionTracked] at hp
    simp only [StateT.run_bind, StateT.run_get, stateT_run_liftM, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hp
    rcases hp with ⟨⟨sr, σH'⟩, hsm, rfl⟩
    have hlen := (bhE2EStepLocalSmSessionTracked_insts_length_eq T C K qep decT encT
      σH i sq hsm).1
    dsimp only at hlen ⊢
    exact ⟨fun _ => hlen, by omega, by omega⟩

theorem simulateQ_bhE2EDrvImplPrefixWithSessionTracked_hyb_eq_const_true {τ : Type}
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart n : ℕ)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σH : BHE2EDrvState S ℓ × List τ)
    (hQ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n)
    (hlen : σH.1.insts.length + n ≤ qStart) :
    (simulateQ (bhE2EDrvImplPrefixWithSessionTracked T ki P C K qep decT encT
        (bhMkPrefixHyb qStart)) oa).run σH =
      (simulateQ (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
        (bhMkKeyBitConst true)) oa).run σH := by
  induction oa using OracleComp.inductionOn generalizing n σH with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hQ
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind,
      bhE2EDrvImplPrefixWithSessionTracked_run_eq_gen]
    by_cases hCtl : bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true
    · have hn : 0 < n := hQ.1.resolve_left (by simp [hCtl])
      have hlt : σH.1.insts.length < qStart := by omega
      have hmk : bhMkPrefixHyb qStart σH.1.insts.length = bhMkKeyBitConst true := by
        funext kr1 kr2
        simp [bhMkPrefixHyb, bhMkKeyBitConst, hlt]
      rw [hmk]
      refine prob_bind_congr_of_support _ _ _ (fun ⟨r, σH'⟩ hp => ?_)
      have hStep :=
        (bhE2EDrvImplGenWithSessionTracked_step_length T ki P C K qep decT encT
          (bhMkKeyBitConst true) q σH hp).2.2
      dsimp only at hStep
      have hQr : (mx r).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
          (n - 1) := by
        simpa [hCtl] using hQ.2 r
      exact ih r (n - 1) σH' hQr (by omega)
    · have hCtlF : bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = false :=
        Bool.eq_false_iff.mpr hCtl
      have hNonCtlEq :
          (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
              (bhMkPrefixHyb qStart σH.1.insts.length) q).run σH =
            (bhE2EDrvImplGenWithSessionTracked T ki P C K qep decT encT
              (bhMkKeyBitConst true) q).run σH := by
        rcases q with m | ((kq | ⟨⟨sid⟩⟩) | ⟨i, sq⟩)
        · rfl
        · rfl
        · simp [bhClassifyTarget, bhClassifyTargetOnly] at hCtlF
        · rfl
      rw [hNonCtlEq]
      refine prob_bind_congr_of_support _ _ _ (fun ⟨r, σH'⟩ hp => ?_)
      have hLenEq :=
        (bhE2EDrvImplGenWithSessionTracked_step_length T ki P C K qep decT encT
          (bhMkKeyBitConst true) q σH hp).1 hCtlF
      dsimp only at hLenEq
      have hQr : (mx r).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
          n := by
        simpa [hCtl] using hQ.2 r
      exact ih r n σH' hQr (by omega)

theorem bhPrefixHybExpWithSessionTracked_qStart_eq {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hStart : B.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart) :
    bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT qStart B =
      bhModeExpWithSessionTracked T S ki P C K qep decT encT true B := by
  unfold bhPrefixHybExpWithSessionTracked bhModeExpWithSessionTracked
  rw [simulateQ_bhE2EDrvImplPrefixWithSessionTracked_hyb_eq_const_true T ki P C K qep
    decT encT qStart qStart B ({}, []) hStart (by simp)]

private theorem bhWin_cond_eq_of_drvWon_not {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (b b' : Bool) (σ : BHE2EDrvState S ℓ)
    (h : bhE2EDrvWon σ (!b) = false) :
    (b' == b || bhE2EDrvWon σ b) =
      (b == (if bhE2EDrvWon σ true then true else if bhE2EDrvWon σ false then false else b')) := by
  cases b <;> cases b' <;>
    cases h1 : bhE2EDrvWon σ true <;> cases h2 : bhE2EDrvWon σ false <;> simp_all

private theorem evalDist_uniformBool_beq_left (b : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun z => pure (b == z)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  cases b
  · simpa using ProbComp.evalDist_bind_not_uniformBool (fun z => (pure z : ProbComp Bool))
  · simp

theorem evalDist_bhE2EExpWithKiSessionTracked_false_branch {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : Bool)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[do
      let (b', σH) ← (simulateQ (bhE2EDrvImplWithSessionTracked T P ki C K qep decT
        encT) B).run ({ b := b, st := SignalPqxdh.KeyIndState.empty S false }, [])
      if !allTestedSessionsFresh P σH.1.st then $ᵗ Bool
      else return (b' == b || bhE2EDrvWon σH.1 b)] =
    𝒟[do
      let g ← bhModeExpWithSessionTracked T S ki P C K qep decT encT b B
      return (b == g)] := by
  have hRun :=
    simulateQ_bhE2EDrvImplWithSessionTracked_eq_gen_const T ki P C K qep decT encT b B ({}, [])
  dsimp only at hRun
  have hInit :
      (({ b := b, st := SignalPqxdh.KeyIndState.empty S false } : BHE2EDrvState S ℓ),
        ([] : List τ)) =
      ({ ({} : BHE2EDrvState S ℓ) with b := b }, ([] : List τ)) := rfl
  rw [hInit, hRun]
  unfold bhModeExpWithSessionTracked bhComposedPostObsSessionTracked bhComposedPostObs
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine evalDist_bind_congr_of_support _ _ _ fun ⟨b', σ, tracks⟩ hp => ?_
  have hbit : BHAllInstsBit b σ :=
    simulateQ_bhE2EDrvImplGenWithSessionTracked_const_preserves_allInstsBit T ki P C K
      qep decT encT b B ({}, []) (bhAllInstsBit_empty b) hp
  have hnot : bhE2EDrvWon σ (!b) = false := bhE2EDrvWon_not_of_allInstsBit hbit
  have hWonEq : ∀ z, bhE2EDrvWon { σ with b := b } z = bhE2EDrvWon σ z := fun _ => rfl
  simp only [hWonEq]
  cases allTestedSessionsFresh P σ.st
  · simp only [Bool.not_false, ↓reduceIte]
    exact (evalDist_uniformBool_beq_left b).symm
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
    rw [bhWin_cond_eq_of_drvWon_not b b' σ hnot]

theorem evalDist_bhE2EExpWithKiSessionTracked_false_eq_bind_modeExp {τ : Type} {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    𝒟[bhE2EExpWithKiSessionTracked T false S P ki C K qep decT encT B] =
      𝒟[do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let g ← if b then bhModeExpWithSessionTracked T S ki P C K qep decT encT true B
                else bhModeExpWithSessionTracked T S ki P C K qep decT encT false B
        return (b == g)] := by
  unfold bhE2EExpWithKiSessionTracked
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  cases b
  · exact evalDist_bhE2EExpWithKiSessionTracked_false_branch T S ki P C K qep decT
      encT false B
  · exact evalDist_bhE2EExpWithKiSessionTracked_false_branch T S ki P C K qep decT
      encT true B

theorem boolBias_bhE2EExpWithKiSessionTracked_false_eq_boolDist_prefixHyb_endpoints {τ : Type}
    {ℓ : ℕ}
    (T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey τ)
    (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qStart : ℕ)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hStart : B.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart) :
    𝒟[bhE2EExpWithKiSessionTracked T false S P ki C K qep decT encT B].boolBias =
      𝒟[bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT qStart B].boolDist
        𝒟[bhPrefixHybExpWithSessionTracked T S ki P C K qep decT encT 0 B] := by
  rw [evalDist_bhE2EExpWithKiSessionTracked_false_eq_bind_modeExp,
    evalDist_boolBias_bind_uniformBool,
    bhPrefixHybExpWithSessionTracked_zero_eq,
    bhPrefixHybExpWithSessionTracked_qStart_eq T S ki P C K qep decT encT qStart B
      hStart]

end Computational.Proofs.LibsignalCli.MainHaltedPrefixEndpoints
