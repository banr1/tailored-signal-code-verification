/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionSimStepsAux -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.SmReachInv -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import

/-!
# Online-Halted Double Ratchet Send and Challenge Step Arms

Lifts the single-session `transmit` and `chall` stages into `atomicE2EOps`, composes them with
the post-send `KemFailSessionTrack` update, and proves `Comp.eval` agreement with
`MainHaltedPrefixCore` alongside `SmReachBounded` and `KemBridgeTrackInv` preservation.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedDrSessionSimSteps

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Env Iface Expr Comp
  atomicSig atomicE2EOps atomicBaseSamplers B BV512 GhostStT PlainT
  smRT partyToBool bits)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (ConfigR GameState partyEnc)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes SampledSessionKey bhPackSmResp
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmReachBounded)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (e2eGsEnc)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (liftTy liftVal)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
  (transmitRSessionTracked challRSessionTracked oracleImplRSessionTracked)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailSessionTrack stepKemFailSend transmitRTrackHalted challRTrackHalted)
open Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl
  (kemTrackT sessHTy kemTrackBridgeAtomicEnc sessHEnc KemBridgeTrackInv kemBridgeTrackInv_mono
   stepKemFailSendAtomicC prependHonestWireAtomicE
   stepKemFailSendAtomicC_queries_zero stepKemFailSendAtomicC_cost_le stepKemFailSendAtomicC_size_le
   prependHonestWireAtomicE_cost prependHonestWireAtomicE_size stepKemFailSendAtomicC_eval_and_inv)
open Computational.Proofs.E2E.Dsl.HaltedDrSessionSimAux
  (kemFailSessionTracker gsAtomicTy gsAtomicEnc smRWireAtomicE prependHonestWireAtomicE_eval
   packAtomicSmRespEnc appLiftC appLiftC_queries_zero appLiftC_cost appLiftC_size appLiftC_eval_prob)
open Computational.Proofs.E2E.Dsl.HaltedDrSessionSimStepsAux
  (liftP_bind liftP_map e2eTrInTy e2eChInTy e2eSendStageOutTy
   drTrSendStageC drChSendStageC drTrSendStageC_cost_le drChSendStageC_cost_le
   size_var_loc drTrSendStageC_size_le drChSendStageC_size_le
   trStageProb chStageProb drTrSendStageC_eval drChSendStageC_eval
   smReachBounded_of_trStageProb smReachBounded_of_chStageProb)

/-! ## Equivalence with `KemFailTrackBridge` oracles -/

theorem transmitRSessionTracked_kemFail_run_eq {ℓ : ℕ} (C : Crypto) (K : MlKem)
    {RCoins : Type} [SampleableType RCoins]
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (Δ qep : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (arg : Party × Plain ℓ × Option (BitVec 512))
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes) :
    (((transmitRSessionTracked (kemFailSessionTracker C K) sm Δ qep cfg arg).run gs).run sh) =
      (((transmitRTrackHalted C.F K sm Δ qep cfg arg).run gs).run sh) := by
  rcases arg with ⟨Q, m, optR⟩
  unfold transmitRSessionTracked transmitRTrackHalted kemFailSessionTracker
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hok : cfg.sendOK gs Q
  · by_cases hwin : gs.win
    · simp [hok, hwin]
    · simp only [hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_lift, StateT.run_monadLift, monadLift_self,
        pure_bind, bind_assoc]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      cases gs.epMgmt Δ qep Q bad with
      | none => simp
      | some s₁ =>
        rcases sh with ⟨tr, hw⟩
        dsimp only [StateT.run, Bind.bind, Pure.pure, Functor.map,
          StateT.bind, StateT.pure, StateT.map, StateT.lift,
          get, set, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
        cases hcand : (stepKemFailSend C.F K tr Q coins).cand.isSome <;>
          (simp [hcand, StateT.bind, StateT.pure, StateT.lift, StateT.set]; rfl)
  · simp [hok]

theorem challRSessionTracked_kemFail_run_eq {ℓ : ℕ} (C : Crypto) (K : MlKem)
    {RCoins : Type} [SampleableType RCoins]
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (Δ qep : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (arg : Party × Plain ℓ × Plain ℓ × Option (BitVec 512))
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes) :
    (((challRSessionTracked (kemFailSessionTracker C K) sm Δ qep cfg arg).run gs).run sh) =
      (((challRTrackHalted C.F K sm Δ qep cfg arg).run gs).run sh) := by
  rcases arg with ⟨Q, m0, m1, optR⟩
  unfold challRSessionTracked challRTrackHalted kemFailSessionTracker
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hok : cfg.sendOK gs Q
  · by_cases hwin : gs.win
    · simp [hok, hwin]
    · simp only [hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_lift, StateT.run_monadLift, monadLift_self,
        pure_bind, bind_assoc]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      cases gs.epMgmt Δ qep Q bad with
      | none => simp
      | some s₁ =>
        by_cases hch : !(s₁.safeCh Δ Q) || !(cfg.base.challAllowedIn (s₁.epoch Q))
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          rcases sh with ⟨tr, hw⟩
          dsimp only [StateT.run, Bind.bind, Pure.pure, Functor.map,
            StateT.bind, StateT.pure, StateT.map, StateT.lift,
            get, set, getThe, MonadStateOf.get, MonadStateOf.set, StateT.get, StateT.set]
          cases hcand : (stepKemFailSend C.F K tr Q coins).cand.isSome <;>
            (simp [hcand, StateT.bind, StateT.pure, StateT.lift, StateT.set]; rfl)
  · simp [hok]

private theorem bits_le_bits_succ (n : ℕ) : bits n ≤ bits (n + 1) :=
  Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ n)) 1

/-! ## Post-send tracker tail and halted step arms -/

abbrev sendJoinedTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (liftTy (Pt := Pt) (e2eSendStageOutTy ℓ))
    (.prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) .bool))

@[expose] def finishHaltedSendBodyC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T) (q : ℕ)
    {Δctx : List (Ty (atomicSig ℓ Pt))} :
    Comp (atomicE2EOps ℓ P C K decT encT) I (sendJoinedTy ℓ Pt :: Δctx)
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  .caseOpt (.fst .v0)
    (.ret (.pair (smRWireAtomicE .none) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0))))))
    (.bind (stepKemFailSendAtomicC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        q (I := I) (.fst (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd .v1))) (.fst .v0))
      (.ite (.fst .v0)
        (.ret (.pair (smRWireAtomicE .none)
          (.pair (.fst (.snd .v2)) (.pair (.snd .v0) (.snd (.fst (.snd (.snd .v2))))))))
        (.ret (.pair (smRWireAtomicE (.some (.fst (.snd .v1))))
          (.pair (.snd (.snd .v1))
            (prependHonestWireAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
              (.snd .v0) (.snd (.fst (.snd (.snd .v2))))
              (.fst (.snd .v1)) (.snd (.snd (.snd .v2)))))))))

private theorem finishHaltedSendBodyC_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T) (q : ℕ)
    {Δctx : List (Ty (atomicSig ℓ Pt))} (w : I.Tag → ℕ) :
    (finishHaltedSendBodyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I q (Δctx := Δctx)).queries w (fun _ => 0) = 0 := by
  simp [finishHaltedSendBodyC, Comp.queries, stepKemFailSendAtomicC_queries_zero]

private theorem finishHaltedSendBodyC_cost_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T) (q : ℕ)
    {Δctx : List (Ty (atomicSig ℓ Pt))} :
    (finishHaltedSendBodyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I q (Δctx := Δctx)).cost ≤ q + 1160060 := by
  have hstep := stepKemFailSendAtomicC_cost_le (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) q (I := I)
    (.fst (.fst (.snd (.snd .v1))) : Expr (atomicE2EOps ℓ P C K decT encT)
      (.prod BV512 (.prod (B 32) (gsAtomicTy ℓ Pt)) :: sendJoinedTy ℓ Pt :: Δctx) _)
    (.snd (.snd (.snd .v1))) (.fst .v0)
  simp only [finishHaltedSendBodyC, smRWireAtomicE, prependHonestWireAtomicE_cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hstep ⊢
  omega

private theorem finishHaltedSendBodyC_size_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T) (q : ℕ)
    {Δctx : List (Ty (atomicSig ℓ Pt))} :
    (finishHaltedSendBodyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I q (Δctx := Δctx)).size ≤ 970 + bits (q + 1) := by
  have hstep := stepKemFailSendAtomicC_size_le (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) q (I := I)
    (.fst (.fst (.snd (.snd .v1))) : Expr (atomicE2EOps ℓ P C K decT encT)
      (.prod BV512 (.prod (B 32) (gsAtomicTy ℓ Pt)) :: sendJoinedTy ℓ Pt :: Δctx) _)
    (.snd (.snd (.snd .v1))) (.fst .v0)
  simp only [finishHaltedSendBodyC, smRWireAtomicE, prependHonestWireAtomicE_size,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var_loc] at hstep ⊢
  omega

private def finishSendStageProb {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes) (Q : Party)
    (mStage : ProbComp (Option (BitVec 512 × (Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes)))) :
    ProbComp ((Option Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes) ×
      KemFailSessionTrack C.F Bytes) := do
  match ← mStage with
  | none => pure ((none, gs), sh)
  | some (coins, (ct, gsRec)) =>
    let tr' := stepKemFailSend C.F K sh.1 Q coins
    if tr'.cand.isSome then
      pure ((none, gs), ({ sh.1 with cand := tr'.cand }, sh.2))
    else
      pure ((some ct, gsRec), (tr', (ct, Q) :: sh.2))

private theorem finishHaltedSendBodyC_eval_pt {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T) (q : ℕ)
    {Δctx : List (Ty (atomicSig ℓ Pt))} (ρ : Env Δctx)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes) (Q : Party)
    (optStage : Option (BitVec 512 × (Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes)))
    (hShInv : KemBridgeTrackInv C.F K q sh) :
    (finishHaltedSendBodyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I q).eval
        (.cons (liftVal (Pt := Pt) (t := e2eSendStageOutTy ℓ)
            (optStage.map fun (coins, (ct, gsRec)) => (coins, (ct, e2eGsEnc gsRec))),
          (gsAtomicEnc gs, (sessHEnc sh, partyToBool Q))) ρ) =
      I.liftP ((fun ((w, gs'), sh') => ((w, (none, none)), (gsAtomicEnc gs', sessHEnc sh'))) <$>
        finishSendStageProb C K gs sh Q (pure optStage)) := by
  cases optStage with
  | none =>
    simp [finishHaltedSendBodyC, finishSendStageProb, liftVal, smRWireAtomicE,
      Comp.eval, Expr.eval, Expr.v0]
  | some val =>
    rcases val with ⟨coins, ⟨ct, gsRec⟩⟩
    have hVal :
        liftVal (Pt := Pt) (t := e2eSendStageOutTy ℓ) (some (coins, (ct, e2eGsEnc gsRec))) =
          some (coins, (ct, gsAtomicEnc (Pt := Pt) gsRec)) := rfl
    rw [Option.map_some, hVal]
    set ρ₁ : Env (.prod BV512 (.prod (B 32) (gsAtomicTy ℓ Pt)) :: sendJoinedTy ℓ Pt :: Δctx) :=
      .cons (coins, (ct, gsAtomicEnc gsRec))
        (.cons (some (coins, (ct, gsAtomicEnc gsRec)),
          (gsAtomicEnc gs, (sessHEnc sh, partyToBool Q))) ρ)
    have hstep := (stepKemFailSendAtomicC_eval_and_inv (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) q (I := I)
      (.fst (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd .v1))) (.fst .v0)
      ρ₁ sh Q coins hShInv rfl rfl rfl).1
    simp only [finishHaltedSendBodyC, finishSendStageProb, Comp.eval, Expr.eval, Env.get,
      Expr.v0, Expr.v1] at hstep ⊢
    rw [hstep]
    simp only [pure_bind, Expr.eval, Expr.v2, Env.get,
      smRWireAtomicE, prependHonestWireAtomicE_eval]
    cases (stepKemFailSend C.F K sh.1 Q coins).cand.isSome <;>
      simp [sessHEnc]

private theorem finishSendStageProb_inv {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes) (Q : Party)
    (mStage : ProbComp (Option (BitVec 512 × (Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes))))
    (hGsInv : SmReachBounded C K q gs)
    (hShInv : KemBridgeTrackInv C.F K q sh)
    (hStageInv : ∀ coins ct gsRec, some (coins, (ct, gsRec)) ∈ support mStage →
      SmReachBounded C K (q + 1) gsRec) :
    ∀ out ∈ support (finishSendStageProb C K gs sh Q mStage),
      SmReachBounded C K (q + 1) out.1.2 ∧ KemBridgeTrackInv C.F K (q + 1) out.2 := by
  intro out hout
  unfold finishSendStageProb at hout
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hout
  rcases hout with ⟨optS, hmem, hout⟩
  cases optS with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨hGsInv.mono (Nat.le_succ q), kemBridgeTrackInv_mono (Nat.le_succ q) hShInv⟩
  | some val =>
    rcases val with ⟨coins, ⟨ct, gsRec⟩⟩
    have hGsRec := hStageInv coins ct gsRec hmem
    let I0 : Iface.{0} (atomicSig ℓ Pt) unifSpec :=
      { fwdU := fun n => query (spec := unifSpec) n
        uCost := 8
        Tag := Empty
        dom := Empty.elim
        cod := Empty.elim
        enc := fun g => g.elim
        dec := fun g => g.elim
        qCost := Empty.elim
        smp := atomicBaseSamplers ℓ Pt }
    have hInvStep := stepKemFailSendAtomicC_eval_and_inv (ℓ := ℓ) (Pt := Pt)
      (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      q (I := I0) (Γ := [kemTrackT ℓ Pt, .bool, BV512])
      .v0 .v1 .v2
      (.cons (kemTrackBridgeAtomicEnc sh.1) (.cons (partyToBool Q) (.cons coins .nil)))
      sh Q coins hShInv rfl rfl rfl
    rcases hInvStep with ⟨_, hInvHalt, hInvOk⟩
    dsimp only at hout
    split_ifs at hout with hcand
    · simp only [support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact ⟨hGsInv.mono (Nat.le_succ q), hInvHalt⟩
    · simp only [support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact ⟨hGsRec, hInvOk ct⟩

private theorem finishSendStageProb_tr_eq {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (Δ qep : ℕ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes)
    (Q : Party) (m : Plain ℓ) (optR : Option (BitVec 512)) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    finishSendStageProb C K gs sh Q (trStageProb sm Δ qep cfg gs Q m optR) =
      (((transmitRTrackHalted C.F K sm Δ qep cfg (Q, m, optR)).run gs).run sh) := by
  intro sm cfg
  unfold finishSendStageProb trStageProb transmitRTrackHalted
  by_cases hok : cfg.sendOK gs Q
  · by_cases hwin : gs.win
    · simp [hok, hwin]
    · simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_lift, StateT.run_get,
        StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      cases gs.epMgmt Δ qep Q bad with
      | none => simp
      | some s₁ =>
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_get,
          StateT.run_pure, pure_bind]
        rcases sh with ⟨tr, hw⟩
        dsimp only
        cases (stepKemFailSend C.F K tr Q coins).cand.isSome <;> simp
  · simp [hok]

private theorem finishSendStageProb_ch_eq {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (Δ qep : ℕ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes)
    (Q : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    finishSendStageProb C K gs sh Q (chStageProb sm Δ qep cfg gs Q m0 m1 optR) =
      (((challRTrackHalted C.F K sm Δ qep cfg (Q, m0, m1, optR)).run gs).run sh) := by
  intro sm cfg
  have hchallAllowed : ∀ t, cfg.base.challAllowedIn t = true := fun _ => rfl
  have hchallMsg : ∀ t, cfg.base.challMsg t = none := fun _ => rfl
  unfold finishSendStageProb chStageProb challRTrackHalted
  by_cases hok : cfg.sendOK gs Q
  · by_cases hwin : gs.win
    · simp [hok, hwin]
    · simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_lift, StateT.run_get,
        StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc]
      refine bind_congr fun ⟨coins, bad⟩ => ?_
      cases gs.epMgmt Δ qep Q bad with
      | none => simp
      | some s₁ =>
        by_cases hsafe : s₁.safeCh Δ Q
        · simp only [hsafe, hchallAllowed, hchallMsg, Bool.not_true, Bool.or_self,
            Bool.false_eq_true, ↓reduceIte, Option.getD_none,
            StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure,
            pure_bind]
          rcases sh with ⟨tr, hw⟩
          dsimp only
          cases (stepKemFailSend C.F K tr Q coins).cand.isSome <;> simp
        · simp [hsafe]
  · simp [hok]

/-- Single-session tracker-halted `transmit` arm over `atomicE2EOps`. -/
@[expose] def haltedDrTrArmC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (trArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512)))) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  .bind (.ret (.pair gsE (.pair shE trArg)))
    (.bind (appLiftC I hsmp (drTrSendStageC P C K decT encT q Δ qep)
        (.pair (.fst .v0) (.snd (.snd .v0))))
      (.bind (.ret (.pair .v0 (.pair (.fst .v1)
          (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))))
        (finishHaltedSendBodyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I q)))

/-- Single-session tracker-halted `chall` arm over `atomicE2EOps`. -/
@[expose] def haltedDrChArmC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (chArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  .bind (.ret (.pair gsE (.pair shE chArg)))
    (.bind (appLiftC I hsmp (drChSendStageC P C K decT encT q Δ qep)
        (.pair (.fst .v0) (.snd (.snd .v0))))
      (.bind (.ret (.pair .v0 (.pair (.fst .v1)
          (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))))
        (finishHaltedSendBodyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I q)))

@[simp] theorem haltedDrTrArmC_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (trArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512))))
    (w : I.Tag → ℕ) :
    (haltedDrTrArmC I hsmp q Δ qep gsE shE trArg).queries w (fun _ => 0) = 0 := by
  simp [haltedDrTrArmC, Comp.queries, appLiftC_queries_zero, finishHaltedSendBodyC_queries_zero]

@[simp] theorem haltedDrChArmC_queries_zero {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (chArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
    (w : I.Tag → ℕ) :
    (haltedDrChArmC I hsmp q Δ qep gsE shE chArg).queries w (fun _ => 0) = 0 := by
  simp [haltedDrChArmC, Comp.queries, appLiftC_queries_zero, finishHaltedSendBodyC_queries_zero]

theorem haltedDrTrArmC_cost_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (trArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512)))) :
    (haltedDrTrArmC I hsmp q Δ qep gsE shE trArg).cost ≤
      gsE.cost + shE.cost + trArg.cost + 1235000 + 10 * (ℓ / 32 + 1) +
        140 * q + 3 * bits Δ + bits qep := by
  let tOuter : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512))))
  have hlift := appLiftC_cost I hsmp (drTrSendStageC P C K decT encT q Δ qep)
    (.pair (.fst .v0) (.snd (.snd .v0)) :
      Expr (atomicE2EOps ℓ P C K decT encT) (tOuter :: Γ) (liftTy (Pt := Pt) (e2eTrInTy ℓ)))
  have hstage := drTrSendStageC_cost_le P C K decT encT q Δ qep (ℓ := ℓ) (Pt := Pt)
  have hbody := finishHaltedSendBodyC_cost_le (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I q
    (Δctx := liftTy (Pt := Pt) (e2eSendStageOutTy ℓ) :: tOuter :: Γ)
  simp only [haltedDrTrArmC, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hlift ⊢
  omega

theorem haltedDrChArmC_cost_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (chArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (haltedDrChArmC I hsmp q Δ qep gsE shE chArg).cost ≤
      gsE.cost + shE.cost + chArg.cost + 1235000 + 10 * (ℓ / 32 + 1) +
        140 * q + 3 * bits Δ + bits qep := by
  let tOuter : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt)
      (.prod (sessHTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
  have hlift := appLiftC_cost I hsmp (drChSendStageC P C K decT encT q Δ qep)
    (.pair (.fst .v0) (.snd (.snd .v0)) :
      Expr (atomicE2EOps ℓ P C K decT encT) (tOuter :: Γ) (liftTy (Pt := Pt) (e2eChInTy ℓ)))
  have hstage := drChSendStageC_cost_le P C K decT encT q Δ qep (ℓ := ℓ) (Pt := Pt)
  have hbody := finishHaltedSendBodyC_cost_le (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I q
    (Δctx := liftTy (Pt := Pt) (e2eSendStageOutTy ℓ) :: tOuter :: Γ)
  simp only [haltedDrChArmC, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hlift ⊢
  omega

theorem haltedDrTrArmC_size_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (trArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512)))) :
    (haltedDrTrArmC I hsmp q Δ qep gsE shE trArg).size ≤
      gsE.size + shE.size + trArg.size + 29500 +
        3 * bits Δ + 3 * bits (q + 1) + 2 * bits (qep + 1) := by
  let tOuter : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512))))
  have hlift := appLiftC_size I hsmp (drTrSendStageC P C K decT encT q Δ qep)
    (.pair (.fst .v0) (.snd (.snd .v0)) :
      Expr (atomicE2EOps ℓ P C K decT encT) (tOuter :: Γ) (liftTy (Pt := Pt) (e2eTrInTy ℓ)))
  have hstage := drTrSendStageC_size_le P C K decT encT q Δ qep (ℓ := ℓ) (Pt := Pt)
  have hbody := finishHaltedSendBodyC_size_le (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I q
    (Δctx := liftTy (Pt := Pt) (e2eSendStageOutTy ℓ) :: tOuter :: Γ)
  have hbq := bits_le_bits_succ q
  have hbqep := bits_le_bits_succ qep
  simp only [haltedDrTrArmC, Comp.size, Expr.size, Expr.v0, Expr.v1, size_var_loc] at hlift ⊢
  omega

theorem haltedDrChArmC_size_le {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (chArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (haltedDrChArmC I hsmp q Δ qep gsE shE chArg).size ≤
      gsE.size + shE.size + chArg.size + 29500 +
        3 * bits Δ + 3 * bits (q + 1) + 2 * bits (qep + 1) := by
  let tOuter : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt)
      (.prod (sessHTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
  have hlift := appLiftC_size I hsmp (drChSendStageC P C K decT encT q Δ qep)
    (.pair (.fst .v0) (.snd (.snd .v0)) :
      Expr (atomicE2EOps ℓ P C K decT encT) (tOuter :: Γ) (liftTy (Pt := Pt) (e2eChInTy ℓ)))
  have hstage := drChSendStageC_size_le P C K decT encT q Δ qep (ℓ := ℓ) (Pt := Pt)
  have hbody := finishHaltedSendBodyC_size_le (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I q
    (Δctx := liftTy (Pt := Pt) (e2eSendStageOutTy ℓ) :: tOuter :: Γ)
  have hbq := bits_le_bits_succ q
  have hbqep := bits_le_bits_succ qep
  simp only [haltedDrChArmC, Comp.size, Expr.size, Expr.v0, Expr.v1, size_var_loc] at hlift ⊢
  omega

theorem haltedDrTrArmC_eval_and_inv {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (trArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512))))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes)
    (Q : Party) (m : Plain ℓ) (optR : Option (BitVec 512))
    (hGsInv : SmReachBounded C K q gs)
    (hShInv : KemBridgeTrackInv C.F K q sh)
    (hgs : gsE.eval ρ = gsAtomicEnc gs)
    (hsh : shE.eval ρ = sessHEnc sh)
    (harg : trArg.eval ρ = (partyToBool Q, (m, optR))) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    (haltedDrTrArmC I hsmp q Δ qep gsE shE trArg).eval ρ =
      I.liftP ((fun ((w, gs'), sh') => ((w, (none, none)), (gsAtomicEnc gs', sessHEnc sh'))) <$>
        (((transmitRSessionTracked (kemFailSessionTracker C K) sm Δ qep cfg (Q, m, optR)).run gs).run sh)) ∧
    ∀ out ∈ support
        (((transmitRSessionTracked (kemFailSessionTracker C K) sm Δ qep cfg (Q, m, optR)).run gs).run sh),
      SmReachBounded C K (q + 1) out.1.2 ∧ KemBridgeTrackInv C.F K (q + 1) out.2 := by
  intro sm cfg
  rw [transmitRSessionTracked_kemFail_run_eq C K sm Δ qep cfg (Q, m, optR) gs sh,
      ← finishSendStageProb_tr_eq C K idA idB spkCoins decT encT Δ qep gs sh Q m optR]
  refine ⟨?_, finishSendStageProb_inv (Pt := Pt) P C K decT encT q gs sh Q
    (trStageProb sm Δ qep cfg gs Q m optR)
    hGsInv hShInv fun coins ct gsRec hmem =>
      smReachBounded_of_trStageProb C K idA idB spkCoins decT encT q Δ qep gs Q m optR hGsInv hmem⟩
  let tOuter : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt) (.prod (sessHTy ℓ Pt) (.prod .bool (.prod PlainT (.opt BV512))))
  set ρ₁ : Env (tOuter :: Γ) :=
    .cons (gsAtomicEnc gs, (sessHEnc sh, (partyToBool Q, (m, optR)))) ρ
  have hIn :
      (Expr.pair (.fst (Expr.v0 (O := atomicE2EOps ℓ P C K decT encT))) (.snd (.snd .v0))).eval ρ₁ =
        liftVal (Pt := Pt) (t := e2eTrInTy ℓ) (e2eGsEnc gs, (partyEnc Q, (m, optR))) := by
    simp only [Expr.eval, Expr.v0, Env.get, ρ₁]
    cases optR <;> rfl
  have hlift := appLiftC_eval_prob I hsmp (drTrSendStageC P C K decT encT q Δ qep)
    (.pair (.fst .v0) (.snd (.snd .v0))) ρ₁
    (e2eGsEnc gs, (partyEnc Q, (m, optR)))
    ((Option.map fun (coins, (ct, gsRec)) => (coins, (ct, e2eGsEnc gsRec))) <$>
      trStageProb sm Δ qep cfg gs Q m optR)
    hIn (drTrSendStageC_eval P C K decT encT q Δ qep idA idB spkCoins gs Q m optR hGsInv)
  simp only [haltedDrTrArmC, Comp.eval, Expr.eval, hgs, hsh, harg, pure_bind]
  rw [hlift, Functor.map_map, liftP_map, map_eq_bind_pure_comp, bind_assoc]
  conv_rhs =>
    rw [show finishSendStageProb C K gs sh Q (trStageProb sm Δ qep cfg gs Q m optR) =
      (trStageProb sm Δ qep cfg gs Q m optR >>= fun optS =>
        finishSendStageProb C K gs sh Q (pure optS)) by rfl,
      map_bind, liftP_bind]
  refine bind_congr fun optS => ?_
  simp only [Function.comp_apply, pure_bind, Expr.eval, Expr.v0, Expr.v1, Env.get]
  exact finishHaltedSendBodyC_eval_pt I q _ gs sh Q optS hShInv

theorem haltedDrChArmC_eval_and_inv {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q Δ qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (chArg : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes)
    (Q : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512))
    (hGsInv : SmReachBounded C K q gs)
    (hShInv : KemBridgeTrackInv C.F K q sh)
    (hgs : gsE.eval ρ = gsAtomicEnc gs)
    (hsh : shE.eval ρ = sessHEnc sh)
    (harg : chArg.eval ρ = (partyToBool Q, (m0, (m1, optR)))) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    (haltedDrChArmC I hsmp q Δ qep gsE shE chArg).eval ρ =
      I.liftP ((fun ((w, gs'), sh') => ((w, (none, none)), (gsAtomicEnc gs', sessHEnc sh'))) <$>
        (((challRSessionTracked (kemFailSessionTracker C K) sm Δ qep cfg (Q, m0, m1, optR)).run gs).run sh)) ∧
    ∀ out ∈ support
        (((challRSessionTracked (kemFailSessionTracker C K) sm Δ qep cfg (Q, m0, m1, optR)).run gs).run sh),
      SmReachBounded C K (q + 1) out.1.2 ∧ KemBridgeTrackInv C.F K (q + 1) out.2 := by
  intro sm cfg
  rw [challRSessionTracked_kemFail_run_eq C K sm Δ qep cfg (Q, m0, m1, optR) gs sh,
      ← finishSendStageProb_ch_eq C K idA idB spkCoins decT encT Δ qep gs sh Q m0 m1 optR]
  refine ⟨?_, finishSendStageProb_inv (Pt := Pt) P C K decT encT q gs sh Q
    (chStageProb sm Δ qep cfg gs Q m0 m1 optR)
    hGsInv hShInv fun coins ct gsRec hmem =>
      smReachBounded_of_chStageProb C K idA idB spkCoins decT encT q Δ qep gs Q m0 m1 optR hGsInv hmem⟩
  let tOuter : Ty (atomicSig ℓ Pt) :=
    .prod (gsAtomicTy ℓ Pt)
      (.prod (sessHTy ℓ Pt) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
  set ρ₁ : Env (tOuter :: Γ) :=
    .cons (gsAtomicEnc gs, (sessHEnc sh, (partyToBool Q, (m0, (m1, optR))))) ρ
  have hIn :
      (Expr.pair (.fst (Expr.v0 (O := atomicE2EOps ℓ P C K decT encT))) (.snd (.snd .v0))).eval ρ₁ =
        liftVal (Pt := Pt) (t := e2eChInTy ℓ) (e2eGsEnc gs, (partyEnc Q, (m0, (m1, optR)))) := by
    simp only [Expr.eval, Expr.v0, Env.get, ρ₁]
    cases optR <;> rfl
  have hlift := appLiftC_eval_prob I hsmp (drChSendStageC P C K decT encT q Δ qep)
    (.pair (.fst .v0) (.snd (.snd .v0))) ρ₁
    (e2eGsEnc gs, (partyEnc Q, (m0, (m1, optR))))
    ((Option.map fun (coins, (ct, gsRec)) => (coins, (ct, e2eGsEnc gsRec))) <$>
      chStageProb sm Δ qep cfg gs Q m0 m1 optR)
    hIn (drChSendStageC_eval P C K decT encT q Δ qep idA idB spkCoins gs Q m0 m1 optR hGsInv)
  simp only [haltedDrChArmC, Comp.eval, Expr.eval, hgs, hsh, harg, pure_bind]
  rw [hlift, Functor.map_map, liftP_map, map_eq_bind_pure_comp, bind_assoc]
  conv_rhs =>
    rw [show finishSendStageProb C K gs sh Q (chStageProb sm Δ qep cfg gs Q m0 m1 optR) =
      (chStageProb sm Δ qep cfg gs Q m0 m1 optR >>= fun optS =>
        finishSendStageProb C K gs sh Q (pure optS)) by rfl,
      map_bind, liftP_bind]
  refine bind_congr fun optS => ?_
  simp only [Function.comp_apply, pure_bind, Expr.eval, Expr.v0, Expr.v1, Env.get]
  exact finishHaltedSendBodyC_eval_pt I q _ gs sh Q optS hShInv

/-! ### `HaltedDrStepOps` wrappers -/

@[expose] def haltedDrTrStepC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512)))) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  haltedDrTrArmC I hsmp q (2 + 1) qep gsE shE argE

theorem haltedDrTrStepC_queries {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512))))
    (w : I.Tag → ℕ) :
    (haltedDrTrStepC I hsmp q qep gsE shE argE).queries w (fun _ => 0) = 0 :=
  haltedDrTrArmC_queries_zero I hsmp q (2 + 1) qep gsE shE argE w

theorem haltedDrTrStepC_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512)))) :
    (haltedDrTrStepC I hsmp q qep gsE shE argE).cost ≤
      gsE.cost + shE.cost + argE.cost + 525 * q + 10 * (ℓ / 32 + 1) + bits (qep + 1) + 6500000 := by
  have hc := haltedDrTrArmC_cost_le I hsmp q (2 + 1) qep gsE shE argE
  have hb3 : bits (2 + 1) = 2 := rfl
  have hbqep := bits_le_bits_succ qep
  unfold haltedDrTrStepC
  omega

theorem haltedDrTrStepC_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512)))) :
    (haltedDrTrStepC I hsmp q qep gsE shE argE).size ≤
      gsE.size + shE.size + argE.size + 25 * bits (q + 1) + 5 * bits (qep + 1) + 30000 := by
  have hs := haltedDrTrArmC_size_le I hsmp q (2 + 1) qep gsE shE argE
  have hb3 : bits (2 + 1) = 2 := rfl
  unfold haltedDrTrStepC
  omega

theorem haltedDrTrStepC_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512))))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes)
    (Q : Party) (m : Plain ℓ) (optR : Option (BitVec 512))
    (hGsInv : SmReachBounded C K q gs)
    (hShInv : KemBridgeTrackInv C.F K q sh)
    (hgs : gsE.eval ρ = gsAtomicEnc gs)
    (hsh : shE.eval ρ = sessHEnc sh)
    (harg : argE.eval ρ = (partyToBool Q, (m, optR))) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
      .inl (.inl (.inl (.inl (Q, m, optR))))
    (haltedDrTrStepC I hsmp q qep gsE shE argE).eval ρ =
      I.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp sq out.1.1),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$>
        (((oracleImplRSessionTracked (kemFailSessionTracker C K) sm (2 + 1) qep cfg sq).run gs).run sh)) :=
  (haltedDrTrArmC_eval_and_inv I hsmp q (2 + 1) qep gsE shE argE ρ idA idB spkCoins
    gs sh Q m optR hGsInv hShInv hgs hsh harg).1

@[expose] def haltedDrChStepC {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    Comp (atomicE2EOps ℓ P C K decT encT) I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (.prod (gsAtomicTy ℓ Pt) (sessHTy ℓ Pt))) :=
  haltedDrChArmC I hsmp q (2 + 1) qep gsE shE argE

theorem haltedDrChStepC_queries {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
    (w : I.Tag → ℕ) :
    (haltedDrChStepC I hsmp q qep gsE shE argE).queries w (fun _ => 0) = 0 :=
  haltedDrChArmC_queries_zero I hsmp q (2 + 1) qep gsE shE argE w

theorem haltedDrChStepC_cost {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (haltedDrChStepC I hsmp q qep gsE shE argE).cost ≤
      gsE.cost + shE.cost + argE.cost + 525 * q + 10 * (ℓ / 32 + 1) + bits (qep + 1) + 6500000 := by
  have hc := haltedDrChArmC_cost_le I hsmp q (2 + 1) qep gsE shE argE
  have hb3 : bits (2 + 1) = 2 := rfl
  have hbqep := bits_le_bits_succ qep
  unfold haltedDrChStepC
  omega

theorem haltedDrChStepC_size {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (haltedDrChStepC I hsmp q qep gsE shE argE).size ≤
      gsE.size + shE.size + argE.size + 25 * bits (q + 1) + 5 * bits (qep + 1) + 30000 := by
  have hs := haltedDrChArmC_size_le I hsmp q (2 + 1) qep gsE shE argE
  have hb3 : bits (2 + 1) = 2 := rfl
  unfold haltedDrChStepC
  omega

theorem haltedDrChStepC_eval {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (atomicSig ℓ Pt) T)
    (hsmp : I.smp = atomicBaseSamplers ℓ Pt) (q qep : ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (gsE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (gsAtomicTy ℓ Pt))
    (shE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (sessHTy ℓ Pt))
    (argE : Expr (atomicE2EOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
    (ρ : Env Γ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sh : KemFailSessionTrack C.F Bytes)
    (Q : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512))
    (hGsInv : SmReachBounded C K q gs)
    (hShInv : KemBridgeTrackInv C.F K q sh)
    (hgs : gsE.eval ρ = gsAtomicEnc gs)
    (hsh : shE.eval ρ = sessHEnc sh)
    (harg : argE.eval ρ = (partyToBool Q, (m0, (m1, optR)))) :
    let sm := sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
    let cfg := configRefuseEarlyBobCorr decT encT
    let sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
      .inl (.inl (.inl (.inr (Q, m0, m1, optR))))
    (haltedDrChStepC I hsmp q qep gsE shE argE).eval ρ =
      I.liftP ((fun out => (packAtomicSmRespEnc (Pt := Pt) (bhPackSmResp sq out.1.1),
        (gsAtomicEnc out.1.2, sessHEnc out.2))) <$>
        (((oracleImplRSessionTracked (kemFailSessionTracker C K) sm (2 + 1) qep cfg sq).run gs).run sh)) :=
  (haltedDrChArmC_eval_and_inv I hsmp q (2 + 1) qep gsE shE argE ρ idA idB spkCoins
    gs sh Q m0 m1 optR hGsInv hShInv hgs hsh harg).1

end Computational.Proofs.E2E.Dsl.HaltedDrSessionSimSteps
