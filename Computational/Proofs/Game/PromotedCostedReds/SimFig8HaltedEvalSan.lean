/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalStep -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanSem
public import Computational.Proofs.HeadlineV1.SendShortC -- proof-setup: allow-public-import

/-!
# Sanitized Evaluation and Guard Bounds for `simFig8RedProgHalted`

Re-exports `simFig8RedProgHalted_eval_san` and proves the query, public-header, and short-circuit
guard invariants for `simFig8RedProgHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalSan

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (RecvResult partyEnc)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C Fig8Comp SimState
  inReceiveOnlyEpoch onAcceptPure onAnswerPure simParseRecvC mkPub)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.LibsignalSession (Params Crypto ShaCompress IdentityKey PublicKey GhostState
  signalWireCodec)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack)
open CryptoGames.LibsignalSM.Proofs.SessionShort (SendMsgsOk GuardedSMShort)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (evalCKS semFwdAnswerHookS semResyncHookS semFwdEvictHookS semFwdHookS
   semRecvHookS semCorrHookTGB semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
  (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (fig8IdSemHook lengthsOk_paramsIdsWithSpqr_v1)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
  (semSendHookHalted simFig8OracleSanHalted simFig8ClampSanHalted
   simHaltedT simFig8RedProgHalted)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalStep
  (semSendHookHalted_eq)

noncomputable section

abbrev simHaltedEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ × KemFailTrackState F) :
    (simHaltedT ℓ Pt).denote :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalStep.simHaltedEnc st

private theorem on_ite {α : Type _} (P : α → Prop) {c : Prop} [Decidable c] {a b : α}
    (ha : P a) (hb : P b) : P (if c then a else b) := by
  by_cases hc : c <;> simp [hc, ha, hb]

section QueryInvariants

open CryptoGames.LibsignalSM.Proofs.QueryBounds
  (FSpec QInr QEq hQu_QInr hQu_QEq isQueryBoundP_congr isQueryBoundP_simulateQ_run_zero)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (QShort hQu_QShort badSendMsg shortB_mkPub)
open CryptoVerification.LibsignalSession.HeadlineV1
  (AtomicLengthsOk atomicLengthsOk_paramsIdsWithSpqr_v1 QAtomicShort hQu_QAtomicShort
   atomicShortPubB_mkPub)

private theorem liftProb_isQueryBoundP_zero {Pt α : Type} {ℓ : ℕ}
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hQu : ∀ n, ¬ p (.inl n)) (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : Fig8Comp Pt ℓ α) p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure p x 0
  | query_bind t mx ih =>
    change IsQueryBoundP (query (spec := FSpec Pt ℓ) (.inl t) >>= fun u => liftM (mx u)) p 0
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind (p := p)
      ((isQueryBoundP_query_iff p (.inl t) 0).2 fun h => absurd h (hQu t)) fun u _ => ih u

private theorem semSendHookHalted_fig8_isQueryBoundP {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p] (hQu : ∀ n, ¬ p (.inl n))
    (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (hSendQ : ∀ pub rc, (∃ rq pn pq', mkPub (P := P) st.1.base Q rq pn = some (pq', pub)) →
      (match chal with
       | none => p (.inr (.inl (.inl (.inl (.inl (Q, (pub, m₀), rc))))))
       | some m₁ => p (.inr (.inl (.inl (.inl (.inr (Q, (pub, m₀), (pub, m₁), rc))))))) → 0 < d) :
    IsQueryBoundP (semSendHookHalted P K Dh encPt encT lam qep st Q m₀ chal r) p d := by
  rcases st with ⟨sC, tr⟩
  rw [semSendHookHalted_eq]
  dsimp only []
  generalize ($ᵗ BitVec 512 : ProbComp (BitVec 512)) = p512
  generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = p256
  split
  · exact isQueryBoundP_pure p _ d
  · rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · exact isQueryBoundP_pure p _ d
    · dsimp only []; split
      · exact isQueryBoundP_pure p _ d
      · have hrq : IsQueryBoundP (match r with
            | some rq => pure rq
            | none => (liftM p512 : Fig8Comp Pt ℓ _)) p 0 := by
          cases r with
          | some _ => exact isQueryBoundP_pure p _ 0
          | none => exact liftProb_isQueryBoundP_zero hQu p512
        rw [← Nat.zero_add d]
        refine isQueryBoundP_bind (p := p) hrq fun rq _ => ?_
        split
        · exact isQueryBoundP_pure p _ d
        · have hrc : IsQueryBoundP (match r with
              | some _ => some <$> (liftM p256 : Fig8Comp Pt ℓ _)
              | none => pure none) p 0 := by
            cases r with
            | none => exact isQueryBoundP_pure p _ 0
            | some _ => simp only [isQueryBoundP_map_iff]; exact liftProb_isQueryBoundP_zero hQu p256
          rw [← Nat.zero_add d]
          refine isQueryBoundP_bind (p := p) hrc fun rc _ => ?_
          let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q
            then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          rcases hmk : mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q
              then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩
          · exact isQueryBoundP_pure p _ d
          · rw [← Nat.add_zero d]
            cases chal with
            | none =>
              dsimp only [CryptoGames.SM.transmitQuery]
              refine isQueryBoundP_bind (p := p)
                ((isQueryBoundP_query_iff p _ d).2 (hSendQ pub rc ⟨rq, pn, pq', hmk⟩)) fun x _ => ?_
              rcases x with _ | _ <;> exact isQueryBoundP_pure p _ 0
            | some m₁ =>
              dsimp only [CryptoGames.SM.challQuery]
              refine isQueryBoundP_bind (p := p)
                ((isQueryBoundP_query_iff p _ d).2 (hSendQ pub rc ⟨rq, pn, pq', hmk⟩)) fun x _ => ?_
              rcases x with _ | _ <;> exact isQueryBoundP_pure p _ 0

private theorem semRecvHookS_fig8_isQueryBoundP {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (T Kc qep B d : ℕ) {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hDl : ∀ Q c, p (.inr (.inl (.inl (.inr (Q, c))))) → 0 < d)
    (hIj : ∀ Q c, p (.inr (.inl (.inr (Q, c)))) → 0 < d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool) :
    IsQueryBoundP (semRecvHookS P Dh encPt encT decT lam T Kc
      (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel) p d := by
  have hDlQ : ∀ c, IsQueryBoundP ((fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).onDl Q c ()) p d :=
    fun c => by
      dsimp only [fig8IdSemHook, CryptoGames.SM.deliverQuery]; rw [← Nat.add_zero d]
      exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hDl Q c))
        fun res _ => isQueryBoundP_pure p (res, ()) 0
  have hIjQ : ∀ c, IsQueryBoundP ((fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).onIj Q c ()) p d :=
    fun c => by
      dsimp only [fig8IdSemHook, CryptoGames.SM.injectQuery]; rw [← Nat.add_zero d]
      exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hIj Q c))
        fun res _ => isQueryBoundP_pure p (res, ()) 0
  have hAns : ∀ sC' ci? Tpk pq' c', IsQueryBoundP (semFwdAnswerHookS P Dh encPt encT lam T
      (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w isDel ci? Tpk pq' c') p d :=
    fun _ _ _ _ c' => by
      unfold semFwdAnswerHookS; dsimp only []; rw [← Nat.add_zero d]
      refine isQueryBoundP_bind (p := p) ?_ fun ⟨_, _⟩ _ => isQueryBoundP_pure p _ 0
      exact on_ite (fun x => IsQueryBoundP x p d) (hDlQ c') (hIjQ c')
  have hResync : ∀ sC' ci? Tpk pq' c r, IsQueryBoundP (semResyncHookS P Dh encPt encT lam T
      (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w ci? Tpk pq' c r) p d :=
    fun _ _ _ _ c r => by
      unfold semResyncHookS; rcases r with _ | ⟨_, _, ⟨_, _⟩⟩
      · exact isQueryBoundP_pure p _ d
      · rw [← Nat.add_zero d]; refine isQueryBoundP_bind (p := p) (hDlQ c) fun ⟨res, _⟩ _ => ?_
        rcases res with _ | (_ | _) <;> exact isQueryBoundP_pure p _ 0
  have hEvict : ∀ sC' Tpk pq' c', IsQueryBoundP (semFwdEvictHookS P Dh encPt encT lam T
      (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w isDel Tpk pq' c') p d :=
    fun sC' Tpk pq' c' => by
      unfold semFwdEvictHookS
      refine on_ite (fun x => IsQueryBoundP x p d) ?_ (hAns sC' none Tpk pq' c')
      dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure p _ d
  have hFwd : ∀ sC' ci? Tpk pq' hc c', IsQueryBoundP (semFwdHookS P Dh encPt encT lam T Kc
      (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC' () Q w isDel ci? Tpk pq' hc c') p d :=
    fun sC' ci? Tpk pq' hc c' => by
      unfold semFwdHookS; rcases hc with _ | c
      · exact hAns sC' ci? Tpk pq' c'
      · dsimp only []
        refine on_ite (fun x => IsQueryBoundP x p d) ?_ (hAns sC' ci? Tpk pq' c')
        rcases evalCKS P Dh encPt encT lam T Kc B sC' Q w c c' with _ | r
        · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure p _ d
        · exact hResync sC' ci? Tpk pq' c r
  unfold semRecvHookS; dsimp only []
  refine on_ite (fun x => IsQueryBoundP x p d) (isQueryBoundP_pure p _ d) ?_
  rcases simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with _ | ⟨pq', i, pk, T?, lct⟩
  · exact isQueryBoundP_pure p _ d
  · rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;> simp only [hidx]
    · refine on_ite (fun x => IsQueryBoundP x p d) (isQueryBoundP_pure p _ d) ?_
      refine on_ite (fun x => IsQueryBoundP x p d) (isQueryBoundP_pure p _ d) ?_
      refine on_ite (fun x => IsQueryBoundP x p d) (isQueryBoundP_pure p _ d) ?_
      rcases T? with _ | T₀
      · exact isQueryBoundP_pure p _ d
      · exact on_ite (fun x => IsQueryBoundP x p d) (hEvict _ pk pq' _) (hFwd _ none pk pq' _ _)
    · exact on_ite (fun x => IsQueryBoundP x p d) (isQueryBoundP_pure p _ d)
        (hFwd sC (some ci) pk pq' _ _)

private theorem semCorrHookTGB_fig8_isQueryBoundP {PQ PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Bsk d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p] (hCr : ∀ Q, p (.inr (.inr Q)) → 0 < d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    IsQueryBoundP (semCorrHookTGB P Dh encT
      (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) Bsk sC () Q) p d := by
  unfold semCorrHookTGB; dsimp only []
  refine on_ite (fun x => IsQueryBoundP x p d) (isQueryBoundP_pure p _ d) ?_
  rw [← Nat.add_zero d]; refine isQueryBoundP_bind (p := p) ?_ fun x _ => ?_
  · dsimp only [fig8IdSemHook, CryptoGames.SM.corrQuery]; rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hCr Q))
      fun _ _ => isQueryBoundP_pure p _ 0
  · rcases x with ⟨_ | _, _⟩ <;> exact isQueryBoundP_pure p _ 0

private theorem simFig8OracleSanHalted_step_isQueryBoundP {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p] (hQu : ∀ n, ¬ p (.inl n))
    (hDl : ∀ Q c, p (.inr (.inl (.inl (.inr (Q, c))))) → 0 < d)
    (hIj : ∀ Q c, p (.inr (.inl (.inr (Q, c)))) → 0 < d)
    (hCr : ∀ Q, p (.inr (.inr Q)) → 0 < d)
    (o : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
    (hSendQ : ∀ (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) pub rc,
      (∃ rq pn pq', mkPub (P := P) st.1.base Q rq pn = some (pq', pub)) →
      (match chal with
       | none => p (.inr (.inl (.inl (.inl (.inl (Q, (pub, m₀), rc))))))
       | some m₁ => p (.inr (.inl (.inl (.inl (.inr (Q, (pub, m₀), (pub, m₁), rc))))))) → 0 < d) :
    IsQueryBoundP
      ((simFig8OracleSanHalted P K Dh encPt encT decT lam qep B T Kc Bsk (.inr o)).run st) p d := by
  rcases st with ⟨sC, tr⟩
  rcases o with ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    dsimp only [StateT.run, StateT.mk]
    exact semSendHookHalted_fig8_isQueryBoundP P K Dh encPt encT lam qep d hQu (sC, tr) Q m none r
      (hSendQ Q m none)
  · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    dsimp only [StateT.run, StateT.mk]
    exact semSendHookHalted_fig8_isQueryBoundP P K Dh encPt encT lam qep d hQu (sC, tr) Q m₀ (some m₁) r
      (hSendQ Q m₀ (some m₁))
  · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    dsimp only [simFig8OracleSan, semHandleHookDedupS, StateT.run, StateT.mk]
    rw [bind_map_left, ← Nat.add_zero d]
    refine isQueryBoundP_bind (p := p) ?_ fun _ _ => isQueryBoundP_pure p _ 0
    rw [← Nat.add_zero d]
    refine isQueryBoundP_bind (p := p)
      (semRecvHookS_fig8_isQueryBoundP P Dh encPt encT decT lam T Kc qep B d hDl hIj sC Q w true)
      fun ⟨_, _, _⟩ _ => ?_
    dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure p _ 0
  · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
    dsimp only [simFig8OracleSan, semHandleHookDedupS, StateT.run, StateT.mk]
    rw [Functor.map_map]; simp only [isQueryBoundP_map_iff]
    exact semRecvHookS_fig8_isQueryBoundP P Dh encPt encT decT lam T Kc qep B d hDl hIj sC Q w false
  · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inr]
    dsimp only [simFig8OracleSan, semHandleHookDedupS, StateT.run, StateT.mk]
    rw [Functor.map_map]; simp only [isQueryBoundP_map_iff]
    exact semCorrHookTGB_fig8_isQueryBoundP P Dh encT Bsk d hCr sC Q

private theorem simFig8ClampSanHalted_queries {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) {q : ℕ}
    {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      (simFig8ClampSanHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A) q := by
  unfold CryptoGames.SM.MakesAtMostQueries simFig8ClampSanHalted
  refine isQueryBoundP_congr (p := QInr Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = p256
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind (p := QInr Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QInr p256) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleSanHalted P K Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
         initKemFailTrack P.C.F pqrKey)) (QInr Pt ℓ) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp st; · cases hp
      · exact simFig8OracleSanHalted_step_isQueryBoundP P K Dh encPt encT decT lam qep B T Kc Bsk 1
          hQu_QInr (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one)
          (fun _ _ => Nat.zero_lt_one) o st (fun _ _ _ _ _ _ _ => Nat.zero_lt_one)
    · rintro (n | o) hnp ⟨sC, tr⟩
      · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl]
        dsimp only [simFig8OracleSan, StateT.lift, StateT.run, StateT.mk]
        simp only [isQueryBoundP_map_iff]
        rw [← Nat.add_zero 0]
        exact isQueryBoundP_bind (p := QInr Pt ℓ)
          ((isQueryBoundP_query_iff (QInr Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QInr n))
          fun u _ => isQueryBoundP_pure (QInr Pt ℓ) (u, sC) 0
      · exact absurd rfl hnp
  rw [StateT.run'_eq]; simp only [isQueryBoundP_map_iff]; exact hsim

private theorem simFig8ClampSanHalted_zero {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p] (hQu : ∀ n, ¬ p (.inl n))
    (hDl : ∀ Q c, ¬ p (.inr (.inl (.inl (.inr (Q, c))))))
    (hIj : ∀ Q c, ¬ p (.inr (.inl (.inr (Q, c)))))
    (hCr : ∀ Q, ¬ p (.inr (.inr Q)))
    (hSend : ∀ (st : SimState PQ Pt ℓ) Q m₀ chal pub rc,
      (∃ rq pn pq', mkPub (P := P) st Q rq pn = some (pq', pub)) →
      ¬ (match chal with
         | none => p (.inr (.inl (.inl (.inl (.inl (Q, (pub, m₀), rc))))))
         | some m₁ => p (.inr (.inl (.inl (.inl (.inr (Q, (pub, m₀), (pub, m₁), rc))))))))
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    IsQueryBoundP (simFig8ClampSanHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A) p 0 := by
  unfold simFig8ClampSanHalted
  generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = p256
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (p := p) (liftProb_isQueryBoundP_zero hQu p256) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleSanHalted P K Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
         initKemFailTrack P.C.F pqrKey)) p 0 := by
    refine isQueryBoundP_simulateQ_run_zero A (fun t st => ?_) _
    rcases t with (n | o)
    · rcases st with ⟨sC, tr⟩
      unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl]
      dsimp only [simFig8OracleSan, StateT.lift, StateT.run, StateT.mk]
      simp only [isQueryBoundP_map_iff]; rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := p)
        ((isQueryBoundP_query_iff p (.inl n) 0).2 fun h => absurd h (hQu n))
        fun u _ => isQueryBoundP_pure p (u, sC) 0
    · exact simFig8OracleSanHalted_step_isQueryBoundP P K Dh encPt encT decT lam qep B T Kc Bsk 0
        hQu (fun Q c h => absurd h (hDl Q c)) (fun Q c h => absurd h (hIj Q c))
        (fun Q h => absurd h (hCr Q)) o st
        (fun Q m₀ chal pub rc hex h => absurd h (hSend st.1.base Q m₀ chal pub rc hex))
  rw [StateT.run'_eq]; simp only [isQueryBoundP_map_iff]; exact hsim

end QueryInvariants

section GuardedSMShortSan

open CryptoGames.GuardedSafe (GuardedSafePost)
open CryptoGames.LibsignalSM.Proofs.QueryBounds (FSpec)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (smRespShort smRecvLong SimShortInv simShortInv_initSim simShortInv_record
   hQu_smRecvLong epMgmt_trans_eq mem_accept_trans inTransit_mem_and_ct)

private abbrev Fig8SafePost (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (x : Fig8Comp Pt ℓ (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit))) : Prop :=
  GuardedSafePost
    (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (fun r => SimShortInv r.2.1.base) x

private theorem simShortInv_onAcceptPure {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (onAcceptPure qep Q w isDel t i m ci? T pq' s).2 := by
  unfold onAcceptPure; dsimp only []; split_ifs
  · rcases s.mir.inTransit Q.other w with _ | _
    · exact hs
    · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact hs
  · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact ⟨hs.1, hs.2⟩

private theorem simShortInv_onAnswerPure {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (onAnswerPure qep Q w isDel ci? T pq' res s).2 := by
  unfold onAnswerPure; rcases res with _ | (_ | ⟨t, i, _⟩)
  · exact hs
  · exact hs
  · exact simShortInv_onAcceptPure qep Q w isDel t i _ ci? T pq' s hs

private theorem simParseRecvC_ser_eq {PQ PQC Pt : Type} (P : Params PQ PQC)
    (decT : PublicKey → Option Pt) (B : ℕ) (qB : Bool) (pq : PQ) (w : Bytes)
    {pq' : PQ} {i : ℕ} {pk : PublicKey} {T? : Option Pt} {lct : ℕ × LibsignalCiphertextWithSalt32}
    (hp : simParseRecvC P decT B qB pq w = some (pq', (i, (pk, (T?, lct))))) :
    lct.2.1.1 = w.take (w.length - 8) := by
  unfold simParseRecvC at hp; split_ifs at hp; dsimp only [] at hp
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
  · rw [hparse] at hp; cases hp
  · rw [hparse] at hp; dsimp only [] at hp; split_ifs at hp
    rcases hspqr : P.spqr.recv pq h.pqRatchet with _ | ⟨_, _⟩
    · rw [hspqr] at hp; cases hp
    · rw [hspqr] at hp; simp only [Option.some.injEq, Prod.mk.injEq] at hp
      exact congrArg (fun x : ℕ × LibsignalCiphertextWithSalt32 => x.2.1.1) hp.2.2.2.2.symm

private theorem semSendHookHalted_safePost {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
    (hs : SimShortInv st.1.base) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    GuardedSafePost
      (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun x => SimShortInv x.2.1.base)
      (semSendHookHalted P K Dh encPt encT lam qep st Q m₀ chal r) := by
  rcases st with ⟨sC, tr⟩
  rw [semSendHookHalted_eq]
  dsimp only []
  generalize ($ᵗ BitVec 512 : ProbComp (BitVec 512)) = p512
  generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = p256
  split
  · exact GuardedSafePost.pure hs
  · rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · exact GuardedSafePost.pure hs
    · have htr₁ : s₁.trans = sC.base.mir.trans := epMgmt_trans_eq hep
      dsimp only []; split
      · exact GuardedSafePost.pure hs
      · have hrq : GuardedSafePost
            (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
            (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
            (fun _ => True)
            (match r with
             | some rq => pure rq
             | none => (liftM p512 : Fig8Comp Pt ℓ _)) := by
          cases r with
          | some _ => exact GuardedSafePost.pure trivial
          | none => exact GuardedSafePost.liftComp_unif hQu_smRecvLong p512
        refine hrq.bind fun rq _ => ?_
        split
        · exact GuardedSafePost.pure hs
        · have hrc : GuardedSafePost
              (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
              (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
              (fun _ => True)
              (match r with
               | some _ => some <$> (liftM p256 : Fig8Comp Pt ℓ _)
               | none => pure none) := by
            cases r with
            | none => exact GuardedSafePost.pure trivial
            | some _ =>
              exact (GuardedSafePost.liftComp_unif hQu_smRecvLong p256).map some fun _ _ => trivial
          refine hrc.bind fun rc _ => ?_
          let pn : BitVec 32 := if s₁.epoch Q ≠ sC.base.mir.epoch Q
            then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          rcases mkPub (P := P) sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q
              then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩
          · exact GuardedSafePost.pure hs
          · cases chal with
            | none =>
              dsimp only [CryptoGames.SM.transmitQuery]
              refine GuardedSafePost.query_bind not_false fun res hres => ?_
              rcases res with _ | c
              · exact GuardedSafePost.pure hs
              · exact GuardedSafePost.pure (simShortInv_record hs htr₁ Q m₀ false pq' pn c (hres c rfl))
            | some m₁ =>
              dsimp only [CryptoGames.SM.challQuery]
              refine GuardedSafePost.query_bind not_false fun res hres => ?_
              rcases res with _ | c
              · exact GuardedSafePost.pure hs
              · exact GuardedSafePost.pure (simShortInv_record hs htr₁ Q m₀ true pq' pn c (hres c rfl))

private theorem semFwdAnswerHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    Fig8SafePost PQ Pt ℓ
      (semFwdAnswerHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q w isDel ci? Tpk pq' c') := by
  unfold semFwdAnswerHookS; dsimp only []
  refine GuardedSafePost.bind (P := fun _ => True) ?_ fun ⟨res, _⟩ _ =>
    GuardedSafePost.pure (simShortInv_onAnswerPure qep Q w isDel ci? Tpk pq' res sC.base hs)
  split_ifs
  · dsimp only [fig8IdSemHook, CryptoGames.SM.deliverQuery]
    exact GuardedSafePost.query_bind (fun h => h hc') fun _ _ => GuardedSafePost.pure trivial
  · dsimp only [fig8IdSemHook, CryptoGames.SM.injectQuery]
    exact GuardedSafePost.query_bind (fun h => h hc') fun _ _ => GuardedSafePost.pure trivial

private theorem semResyncHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    Fig8SafePost PQ Pt ℓ
      (semResyncHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q w ci? Tpk pq' c r) := by
  unfold semResyncHookS; rcases r with _ | ⟨t, i, ⟨_, m'⟩⟩
  · exact GuardedSafePost.pure hs
  · dsimp only [fig8IdSemHook, CryptoGames.SM.deliverQuery]; rw [bind_assoc]
    refine GuardedSafePost.query_bind (fun h => h hc) fun res _ => ?_
    rw [pure_bind]; rcases res with _ | (_ | _)
    · exact GuardedSafePost.pure hs
    · exact GuardedSafePost.pure hs
    · exact GuardedSafePost.pure (simShortInv_onAcceptPure qep Q w true t i m' ci? Tpk pq' sC.base hs)

private theorem semFwdEvictHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ)
    (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    Fig8SafePost PQ Pt ℓ
      (semFwdEvictHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q w isDel Tpk pq' c') := by
  unfold semFwdEvictHookS; split_ifs
  · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact GuardedSafePost.pure hs
  · exact semFwdAnswerHookS_safePost P Dh encPt encT lam T qep sC hs Q w isDel none Tpk pq' c' hc'

private theorem semFwdHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T Kc qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt))
    (hhon : ∀ c, honestC = some c → c.2.2.1.1.length < 2 ^ 32)
    (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    Fig8SafePost PQ Pt ℓ
      (semFwdHookS P Dh encPt encT lam T Kc
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel ci? Tpk pq'
          honestC c') := by
  unfold semFwdHookS; rcases honestC with _ | c
  · exact semFwdAnswerHookS_safePost P Dh encPt encT lam T qep sC hs Q w isDel ci? Tpk pq' c' hc'
  · dsimp only []; split_ifs
    · rcases evalCKS P Dh encPt encT lam T Kc B sC Q w c c' with _ | r
      · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact GuardedSafePost.pure hs
      · exact semResyncHookS_safePost P Dh encPt encT lam T qep sC hs Q w ci? Tpk pq' c (hhon c rfl) r
    · exact semFwdAnswerHookS_safePost P Dh encPt encT lam T qep sC hs Q w isDel ci? Tpk pq' c' hc'

private theorem semRecvHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (T Kc qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) :
    Fig8SafePost PQ Pt ℓ
      (semRecvHookS P Dh encPt encT decT lam T Kc
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel) := by
  unfold semRecvHookS; dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with _ | ⟨pq', i, pk, T?, lct⟩
    · exact GuardedSafePost.pure hs
    · have hwlen : w.length < 2 ^ 32 := by
        cases isDel with
        | true =>
          rcases htr : sC.base.mir.inTransit Q.other w with _ | rec'
          · simp [htr] at href
          · obtain ⟨hmem, rfl⟩ := inTransit_mem_and_ct htr; exact hs.1 rec' hmem
        | false =>
          by_cases hw9 : w.length < 9
          · omega
          · have hadm : ratchetKeyAdmissible P.codec decT encT w = true := by
              revert href; cases ratchetKeyAdmissible P.codec decT encT w <;> simp
            unfold ratchetKeyAdmissible at hadm; simp only [hw9, ↓reduceIte] at hadm
            have hp0 := hp; unfold simParseRecvC at hp0; split_ifs at hp0; dsimp only [] at hp0
            rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
            · rw [hparse] at hp0; cases hp0
            · simp only [hparse, Bool.and_eq_true, decide_eq_true_eq] at hadm; exact hadm.1
      have hlct : lct.2.1.1.length < 2 ^ 32 := by
        rw [simParseRecvC_ser_eq P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w hp, List.length_take]; omega
      have hhon : ∀ c : Fig8C Pt,
          (sC.base.honest.find? fun (wc : Bytes × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
              (fun (wc : Bytes × Fig8C Pt) => wc.2) = some c → c.2.2.1.1.length < 2 ^ 32 := by
        intro c hc_eq; rcases Option.mem_map.mp hc_eq with ⟨wc, hfind, rfl⟩
        exact hs.2 wc (List.mem_of_find?_eq_some hfind)
      have hmkC : ∀ (t : ℕ) (To : Option Pt),
          (match (sC.base.honest.find? fun (wc : Bytes × Fig8C Pt) =>
               wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (fun (wc : Bytes × Fig8C Pt) => wc.2) with
           | some (c : Fig8C Pt) => if c.2.2.2 = lct.2.2 then c else ((t, To), lct)
           | none => ((t, To), lct)).2.2.1.1.length < 2 ^ 32 := by
        intro t To
        rcases hfind : sC.base.honest.find? (fun (wc : Bytes × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with _ | wc
        · exact hlct
        · simp only [Option.map]; split
          · exact hs.2 wc (List.mem_of_find?_eq_some hfind)
          · exact hlct
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;> simp only [hidx]
      · have hsAmb : SimShortInv
            ({ sC with base :=
                if inReceiveOnlyEpoch sC.base.mir Q ||
                    (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
                  { sC.base with amb := sC.base.amb + 1 }
                else sC.base }).base := by
          dsimp only []; exact on_ite SimShortInv ⟨hs.1, hs.2⟩ ⟨hs.1, hs.2⟩
        refine on_ite (Fig8SafePost PQ Pt ℓ) (GuardedSafePost.pure hs) ?_
        refine on_ite (Fig8SafePost PQ Pt ℓ) (GuardedSafePost.pure hs) ?_
        refine on_ite (Fig8SafePost PQ Pt ℓ) (GuardedSafePost.pure hsAmb) ?_
        rcases T? with _ | T₀
        · exact GuardedSafePost.pure hsAmb
        · exact on_ite (Fig8SafePost PQ Pt ℓ)
            (semFwdEvictHookS_safePost P Dh encPt encT lam T qep _ hsAmb Q w isDel pk pq' _ hlct)
            (semFwdHookS_safePost P Dh encPt encT lam T Kc qep B _ hsAmb Q w isDel none
              pk pq' _ hhon _ (hmkC _ _))
      · exact on_ite (Fig8SafePost PQ Pt ℓ) (GuardedSafePost.pure hs)
          (semFwdHookS_safePost P Dh encPt encT lam T Kc qep B sC hs Q w isDel (some ci)
            pk pq' _ hhon _ (hmkC _ _))
  · simp only [↓reduceIte]; exact GuardedSafePost.pure hs

private theorem semCorrHookTGB_safePost {PQ PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Bsk : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base) (Q : Party) :
    Fig8SafePost PQ Pt ℓ
      (semCorrHookTGB P Dh encT (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) Bsk sC () Q) := by
  unfold semCorrHookTGB; dsimp only []
  refine on_ite (Fig8SafePost PQ Pt ℓ) (GuardedSafePost.pure hs) ?_
  dsimp only [fig8IdSemHook, CryptoGames.SM.corrQuery]; rw [bind_assoc]
  refine GuardedSafePost.query_bind not_false fun res _ => ?_
  rw [pure_bind]
  rcases res with _ | _
  · exact GuardedSafePost.pure hs
  · exact GuardedSafePost.pure ⟨hs.1, hs.2⟩

private theorem simFig8ClampSanHalted_guardedSMShort {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt]
    [Zero Pt] {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    GuardedSMShort (simFig8ClampSanHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A) := by
  unfold GuardedSMShort simFig8ClampSanHalted
  generalize ($ᵗ BitVec 256 : ProbComp (BitVec 256)) = p256
  refine (GuardedSafePost.liftComp_unif hQu_smRecvLong p256).bind fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost
      (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun r => SimShortInv r.2.1.base)
      ((simulateQ (simFig8OracleSanHalted P K Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
         initKemFailTrack P.C.F pqrKey)) := by
    refine GuardedSafePost.simulateQ_run
      (I := fun st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F =>
        SimShortInv st.1.base)
      (GuardedSafePost.true_of_false A) ?_ (simShortInv_initSim _ _)
    rintro (n | o) _ ⟨sC, tr⟩ hs
    · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl]
      dsimp only [simFig8OracleSan, StateT.lift, StateT.run, StateT.mk]
      exact GuardedSafePost.map _ ((GuardedSafePost.query (hQu_smRecvLong n)).bind
        fun _ _ => GuardedSafePost.pure hs) (fun _ hp => ⟨trivial, hp⟩)
    · rcases o with ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
        dsimp only [StateT.run, StateT.mk]
        exact (semSendHookHalted_safePost P K Dh encPt encT lam qep (sC, tr) hs Q m none r).mono
          fun _ hp => ⟨trivial, hp⟩
      · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
        dsimp only [StateT.run, StateT.mk]
        exact (semSendHookHalted_safePost P K Dh encPt encT lam qep (sC, tr) hs Q m₀ (some m₁) r).mono
          fun _ hp => ⟨trivial, hp⟩
      · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
        dsimp only [simFig8OracleSan, semHandleHookDedupS, StateT.run, StateT.mk]
        rw [bind_map_left]
        refine GuardedSafePost.bind
          (P := fun r : Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit) =>
            SimShortInv r.2.1.base) ?_
          fun ⟨_, _, _⟩ hs₂ => GuardedSafePost.pure ⟨trivial, hs₂⟩
        refine (semRecvHookS_safePost P Dh encPt encT decT lam T Kc qep B sC hs Q w true).bind
          fun ⟨_, _, _⟩ hs₁ => ?_
        dsimp only [fig8IdSemHook]; rw [pure_bind]
        exact GuardedSafePost.pure hs₁
      · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
        dsimp only [simFig8OracleSan, semHandleHookDedupS, StateT.run, StateT.mk]
        rw [Functor.map_map]
        exact GuardedSafePost.map _
          (semRecvHookS_safePost P Dh encPt encT decT lam T Kc qep B sC hs Q w false)
          (fun _ hp => ⟨trivial, hp⟩)
      · unfold simFig8OracleSanHalted; simp only [QueryImpl.add_apply_inr]
        dsimp only [simFig8OracleSan, semHandleHookDedupS, StateT.run, StateT.mk]
        rw [Functor.map_map]
        exact GuardedSafePost.map _ (semCorrHookTGB_safePost P Dh encT Bsk sC hs Q)
          (fun _ hp => ⟨trivial, hp⟩)
  exact hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial

end GuardedSMShortSan

section Theorems

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem simFig8RedProgHalted_eval_san (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) () =
      simFig8ClampSanHalted (paramsV1 C K idA idB) K ℓ Dh encPt encT decT
        lam qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A :=
  Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalStep.simFig8RedProgHalted_eval_san
    hℓ C K idA idB Dh encPt encT decT lam qep q A hq

theorem simFig8RedProgHalted_queries (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) q := by
  rw [simFig8RedProgHalted_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  exact simFig8ClampSanHalted_queries (paramsV1 C K idA idB) K Dh encPt encT decT lam
    qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) hq

theorem simFig8RedProgHalted_equalPub (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) := by
  rw [simFig8RedProgHalted_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  exact simFig8ClampSanHalted_zero (paramsV1 C K idA idB) K Dh encPt encT decT lam
    qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
    CryptoGames.LibsignalSM.Proofs.QueryBounds.hQu_QEq
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ chal _ _ _ h => by
      cases chal with
      | none => exact nomatch h
      | some _ => simp [CryptoGames.LibsignalSM.Proofs.QueryBounds.QEq,
          CryptoGames.SM.unequalPubChall] at h) A

theorem simFig8RedProgHalted_sendShort (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) := by
  rw [simFig8RedProgHalted_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  have hL := lengthsOk_paramsIdsWithSpqr_v1 C K idA idB (ℓ := ℓ) (by omega)
  exact simFig8ClampSanHalted_zero (paramsV1 C K idA idB) K Dh encPt encT decT lam
    qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
    CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.hQu_QShort
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h)
    (fun st Q _ chal pub _ ⟨rq, pn, _, hmk⟩ h => by
      have hpub := CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.shortB_mkPub hL st Q rq pn hmk
      cases chal <;> simp [CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.QShort,
        CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.badSendMsg, hpub] at h) A

theorem simFig8RedProgHalted_sendAtomicShort (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) := by
  rw [simFig8RedProgHalted_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  have hL := CryptoVerification.LibsignalSession.HeadlineV1.atomicLengthsOk_paramsIdsWithSpqr_v1
    C K idA idB ℓ hℓ
  exact simFig8ClampSanHalted_zero (paramsV1 C K idA idB) K Dh encPt encT decT lam
    qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
    CryptoVerification.LibsignalSession.HeadlineV1.hQu_QAtomicShort
    (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h)
    (fun st Q _ chal pub _ ⟨rq, pn, _, hmk⟩ h => by
      have hpub := CryptoVerification.LibsignalSession.HeadlineV1.atomicShortPubB_mkPub hL st Q rq pn hmk
      cases chal <;> simp [CryptoVerification.LibsignalSession.HeadlineV1.QAtomicShort,
        CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM.badSendMsg, hpub] at h) A

theorem simFig8RedProgHalted_guardedSMShort (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    GuardedSMShort
      ((simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).eval
        (fun _ => A) ()) := by
  rw [simFig8RedProgHalted_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  exact simFig8ClampSanHalted_guardedSMShort (paramsV1 C K idA idB) K Dh encPt encT decT lam
    qep (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A

end Theorems

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedEvalSan
