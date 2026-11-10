/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim
public import Computational.Proofs.HeadlineV1.SendShortC

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCouplingBounds

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Comp CostedReduction handlerImpl atomicSessionOps e2eSessionCodec
  GhostStT fig8SmIfaceDF smQT smRT isGameQuery)
open _root_.CryptoGames (Party SMScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.GuardedSafe (GuardedSafePost)
open CryptoGames.SM.Construction (Header)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimCStateBounded SimCStateInv
  deliverForgeSemHook inReceiveOnlyEpoch onAcceptPure onAnswerPure simParseRecvC)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params
  signalWireCodec)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (SimShortInv simShortInv_initSim smRespShort smRecvLong SimSafeS guardedSafeS_simSend
   inTransit_mem_and_ct mem_accept_trans)
open CryptoGames.SM.Construction.DeliverForge (AdversaryDF AdversaryCompDF specDF MakesAtMostQueriesDF)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open CryptoVerification.LibsignalSession.HeadlineV1
  (DFSpec SendMsgsOkDF QAtomicShortDF hQ_QAtomicShortDF df_QBC df_qbc_guardC
   df_qbc_simSendC_atomicShort atomicLengthsOk_paramsIdsWithSpqr_v1
   smDFRespShort smDFRecvLong GuardedSMDFShort hQu_smDFRecvLong toDFDom)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (semFwdAnswerHookS semResyncHookS semFwdEvictHookS semFwdHookS semRecvHookS
   semCorrHookTGB semHandleHookDedupS evalCKS)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (dfFullT dfFullDec simDeliverForgeOracleSan simDeliverForgeOracleSanQ
   simDeliverForgeClampSan simDeliverForgeClampSanQ simDeliverForgeProgOfStep
   simDeliverForgeProgOfStep_eval_san simDeliverForgeProgOfStep_eval_sanQ
   simDeliverForgeOracleSan_preserves_dfStateInv dfStateInv_initSimC DFStateInv)

section QueryBoundHelpers

private theorem isQueryBoundP_liftProb_zero {Pt : Type} {ℓ : ℕ}
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (hQu : ∀ n, ¬ Q (.inl n))
    {α : Type} (mx : ProbComp α) :
    IsQueryBoundP
      (liftM mx : AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt) α) Q 0 := by
  induction mx using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure Q x 0
  | query_bind t mx ih =>
    change IsQueryBoundP (query (spec := DFSpec Pt ℓ) (.inl t) >>= fun u => liftM (mx u)) Q 0
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind
      ((isQueryBoundP_query_iff Q (.inl t) 0).2 fun h => absurd h (hQu t))
      fun u _ => ih u

private theorem isQueryBoundP_runDFM {PQ Pt : Type} {ℓ : ℕ}
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {α : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (CryptoGames.LibsignalSM.Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    {n : ℕ} (hx : df_QBC Q x n)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) :
    IsQueryBoundP (CryptoGames.Ratchet.LibsignalSim.runDFM x sC ex) Q n := by
  unfold CryptoGames.Ratchet.LibsignalSim.runDFM
  rw [← Nat.add_zero n]
  exact isQueryBoundP_bind (hx sC ex) fun p _ => isQueryBoundP_pure Q (p.1.1, p.1.2, p.2) 0

private abbrev DlBound (Pt : Type) (ℓ : ℕ) (Q : (DFSpec Pt ℓ).Domain → Prop)
    [DecidablePred Q] (d : ℕ) : Prop :=
  ∀ R c, IsQueryBoundP (CryptoGames.SM.Construction.DeliverForge.deliverQueryDF
    (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (C := Fig8C Pt) R c) Q d

private abbrev IjBound (Pt : Type) (ℓ : ℕ) (Q : (DFSpec Pt ℓ).Domain → Prop)
    [DecidablePred Q] (d : ℕ) : Prop :=
  ∀ R c, IsQueryBoundP (CryptoGames.SM.Construction.DeliverForge.injectQueryDF
    (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (C := Fig8C Pt) R c) Q d

private abbrev DfBound (Pt : Type) (ℓ : ℕ) (Q : (DFSpec Pt ℓ).Domain → Prop)
    [DecidablePred Q] (d : ℕ) : Prop :=
  ∀ R c c', IsQueryBoundP (CryptoGames.SM.Construction.DeliverForge.deliverForgeQuery
    (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (C := Fig8C Pt) R c c') Q d

private theorem isQueryBoundP_onProbe {PQC Pt : Type} [DecidableEq Pt] [SampleableType PQC]
    {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDf : DfBound Pt ℓ Q d) (R : Party) (c' : Fig8C Pt) (ex : List (Fig8C Pt)) :
    IsQueryBoundP
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe R c' ex) Q d := by
  unfold deliverForgeSemHook
  dsimp only
  rcases ex.find? (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c') with _ | c
  · exact isQueryBoundP_pure Q ex d
  · rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (hDf R c c') fun _ _ => isQueryBoundP_pure Q ex 0

private theorem isQueryBoundP_semFwdAnswerHookS {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBound Pt ℓ Q d) (hIj : IjBound Pt ℓ Q d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (R : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    IsQueryBoundP
      (semFwdAnswerHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex R w isDel ci? Tpk pq' c') Q d := by
  unfold semFwdAnswerHookS deliverForgeSemHook
  dsimp only
  rw [← Nat.add_zero d]
  refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_pure Q _ 0
  split
  · rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (hDl R c') fun _ _ => isQueryBoundP_pure Q _ 0
  · rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (hIj R c') fun _ _ => isQueryBoundP_pure Q _ 0

private theorem isQueryBoundP_semResyncHookS {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBound Pt ℓ Q d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (R : Party) (w : Bytes) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    IsQueryBoundP
      (semResyncHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex R w ci? Tpk pq' c r) Q d := by
  unfold semResyncHookS deliverForgeSemHook
  rcases r with _ | ⟨t, i, _, m'⟩
  · exact isQueryBoundP_pure Q _ d
  · dsimp only
    rw [← Nat.add_zero d]
    refine isQueryBoundP_bind
      (by rw [← Nat.add_zero d]; exact isQueryBoundP_bind (hDl R c) fun _ _ => isQueryBoundP_pure Q _ 0)
      fun ⟨res, ex₁⟩ _ => ?_
    rcases res with _ | (_ | _) <;> exact isQueryBoundP_pure Q _ 0

private theorem isQueryBoundP_semFwdEvictHookS {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBound Pt ℓ Q d) (hIj : IjBound Pt ℓ Q d) (hDf : DfBound Pt ℓ Q d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (R : Party) (w : Bytes) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    IsQueryBoundP
      (semFwdEvictHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex R w isDel Tpk pq' c') Q d := by
  unfold semFwdEvictHookS
  split
  · rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (isQueryBoundP_onProbe hDf R c' ex) fun _ _ => isQueryBoundP_pure Q _ 0
  · exact isQueryBoundP_semFwdAnswerHookS P Dh encPt encT lam T qep hDl hIj sC ex R w isDel none Tpk pq' c'

private theorem isQueryBoundP_semFwdHookS {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T Kc qep B : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBound Pt ℓ Q d) (hIj : IjBound Pt ℓ Q d) (hDf : DfBound Pt ℓ Q d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (R : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    IsQueryBoundP
      (semFwdHookS P Dh encPt encT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep B sC ex R w isDel ci? Tpk pq' honestC c') Q d := by
  unfold semFwdHookS
  rcases honestC with _ | c
  · exact isQueryBoundP_semFwdAnswerHookS P Dh encPt encT lam T qep hDl hIj sC ex R w isDel ci? Tpk pq' c'
  · dsimp only
    split
    · rcases evalCKS P Dh encPt encT lam T Kc B sC R w c c' with _ | r
      · rw [← Nat.add_zero d]
        exact isQueryBoundP_bind (isQueryBoundP_onProbe hDf R c' ex) fun _ _ => isQueryBoundP_pure Q _ 0
      · exact isQueryBoundP_semResyncHookS P Dh encPt encT lam T qep hDl sC ex R w ci? Tpk pq' c r
    · exact isQueryBoundP_semFwdAnswerHookS P Dh encPt encT lam T qep hDl hIj sC ex R w isDel ci? Tpk pq' c'

private theorem isQueryBoundP_semRecvHookS {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (T Kc qep B : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBound Pt ℓ Q d) (hIj : IjBound Pt ℓ Q d) (hDf : DfBound Pt ℓ Q d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (R : Party) (w : Bytes) (isDel : Bool) :
    IsQueryBoundP
      (semRecvHookS P Dh encPt encT decT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep B sC ex R w isDel) Q d := by
  unfold semRecvHookS
  dsimp only []
  split
  · exact isQueryBoundP_pure Q _ d
  · rcases simParseRecvC P decT (2 ^ 32)
        (CryptoGames.SM.partyEnc R) (sC.base.pq R) w with
      _ | ⟨pq', i, pk, T?, lct⟩
    · exact isQueryBoundP_pure Q _ d
    · rcases hidx : (sC.base.chains R).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · split
        · exact isQueryBoundP_pure Q _ d
        · split
          · exact isQueryBoundP_pure Q _ d
          · split
            · exact isQueryBoundP_pure Q _ d
            · rcases T? with _ | T₀
              · exact isQueryBoundP_pure Q _ d
              · dsimp only
                split
                · exact isQueryBoundP_semFwdEvictHookS P Dh encPt encT lam T qep hDl hIj hDf
                    _ ex R w isDel pk pq' _
                · exact isQueryBoundP_semFwdHookS P Dh encPt encT lam T Kc qep B hDl hIj hDf
                    _ ex R w isDel none pk pq' _ _
      · split
        · exact isQueryBoundP_pure Q _ d
        · exact isQueryBoundP_semFwdHookS P Dh encPt encT lam T Kc qep B hDl hIj hDf
            sC ex R w isDel (some ci) pk pq' _ _

private theorem isQueryBoundP_semCorrHookTGB {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Bsk : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hCr : ∀ R, IsQueryBoundP
      (CryptoGames.SM.Construction.DeliverForge.corrQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) R) Q d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (R : Party) :
    IsQueryBoundP
      (semCorrHookTGB P Dh encT
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) Bsk sC ex R) Q d := by
  unfold semCorrHookTGB deliverForgeSemHook
  dsimp only
  split
  · exact isQueryBoundP_pure Q _ d
  · rw [← Nat.add_zero d]
    refine isQueryBoundP_bind
      (by rw [← Nat.add_zero d]; exact isQueryBoundP_bind (hCr R) fun _ _ => isQueryBoundP_pure Q _ 0)
      fun ⟨res, ex₁⟩ _ => ?_
    rcases res with _ | _ <;> exact isQueryBoundP_pure Q _ 0

private theorem isQueryBoundP_semSendHook {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hQu : ∀ n, ¬ Q (.inl n))
    (hTr : ∀ R m rc, IsQueryBoundP
      (CryptoGames.SM.Construction.DeliverForge.transmitQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) R m rc) Q d)
    (hCh : ∀ R m₀ m₁ rc, IsQueryBoundP
      (CryptoGames.SM.Construction.DeliverForge.challQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) R m₀ m₁ rc) Q d)
    (qep : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    IsQueryBoundP
      (CryptoGames.Ratchet.LibsignalSim.semSendHook (P := P) (Dh := Dh)
        (encPt := encPt) (encT := encT) (lam := lam)
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC ex R m₀ chal r) Q d := by
  unfold CryptoGames.Ratchet.LibsignalSim.semSendHook
    CryptoGames.Ratchet.LibsignalSim.semDrawSendCoins deliverForgeSemHook
  dsimp only
  split
  · exact isQueryBoundP_pure Q _ d
  · rcases sC.base.mir.epMgmt 3 qep R r.isSome with _ | s₁
    · exact isQueryBoundP_pure Q _ d
    · dsimp only
      split
      · exact isQueryBoundP_pure Q _ d
      · have hcoins : IsQueryBoundP
            (match r with
            | none => do
              let rq ← (liftM ($ᵗ PQC : ProbComp PQC) : OracleComp (DFSpec Pt ℓ) PQC)
              pure (rq, none)
            | some rq => do
              let rc ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
                OracleComp (DFSpec Pt ℓ) (BitVec 256))
              pure (rq, some rc)) Q 0 := by
          rcases r with _ | rq
          · rw [← Nat.add_zero 0]
            exact isQueryBoundP_bind (isQueryBoundP_liftProb_zero hQu ($ᵗ PQC))
              fun _ _ => isQueryBoundP_pure Q _ 0
          · rw [← Nat.add_zero 0]
            exact isQueryBoundP_bind (isQueryBoundP_liftProb_zero hQu ($ᵗ (BitVec 256)))
              fun _ _ => isQueryBoundP_pure Q _ 0
        rw [← Nat.zero_add d]
        refine isQueryBoundP_bind hcoins fun ⟨rq, rc⟩ _ => ?_
        rw [pure_bind]
        dsimp only
        rcases CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) sC.base R rq _ with _ | ⟨pq', pub⟩
        · exact isQueryBoundP_pure Q _ d
        · dsimp only
          rw [← Nat.add_zero d]
          refine isQueryBoundP_bind ?_ fun ⟨res, ex₂⟩ _ => ?_
          · rcases chal with _ | m₁
            · rw [← Nat.add_zero d]
              exact isQueryBoundP_bind (hTr R (pub, m₀) rc) fun _ _ => isQueryBoundP_pure Q _ 0
            · rw [← Nat.add_zero d]
              exact isQueryBoundP_bind (hCh R (pub, m₀) (pub, m₁) rc)
                fun _ _ => isQueryBoundP_pure Q _ 0
          · dsimp only
            rcases res with _ | c <;> exact isQueryBoundP_pure Q _ 0

end QueryBoundHelpers

theorem simDeliverForgeClampSan_makesAtMostQueriesDF {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    MakesAtMostQueriesDF (simDeliverForgeClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) q := by
  rw [CryptoGames.Ratchet.LibsignalSim.makesAtMostQueriesDF_iff_isGameQuery]
  let Q := _root_.ReductionDsl.isGameQuery
    (G := specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
  change IsQueryBoundP _ Q q
  have hQu : ∀ n, ¬ Q (.inl n) := fun _ h => nomatch h
  have hTr : ∀ R m rc, IsQueryBoundP (CryptoGames.SM.Construction.DeliverForge.transmitQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (C := Fig8C Pt) R m rc) Q 1 :=
    fun _ _ _ => (isQueryBoundP_query_iff Q _ 1).2 fun _ => Nat.zero_lt_one
  have hCh : ∀ R m₀ m₁ rc, IsQueryBoundP (CryptoGames.SM.Construction.DeliverForge.challQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (C := Fig8C Pt) R m₀ m₁ rc) Q 1 :=
    fun _ _ _ _ => (isQueryBoundP_query_iff Q _ 1).2 fun _ => Nat.zero_lt_one
  have hDl : DlBound Pt ℓ Q 1 := fun _ _ => (isQueryBoundP_query_iff Q _ 1).2 fun _ => Nat.zero_lt_one
  have hIj : IjBound Pt ℓ Q 1 := fun _ _ => (isQueryBoundP_query_iff Q _ 1).2 fun _ => Nat.zero_lt_one
  have hDf : DfBound Pt ℓ Q 1 := fun _ _ _ => (isQueryBoundP_query_iff Q _ 1).2 fun _ => Nat.zero_lt_one
  have hCr : ∀ R, IsQueryBoundP (CryptoGames.SM.Construction.DeliverForge.corrQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (C := Fig8C Pt) R) Q 1 :=
    fun _ => (isQueryBoundP_query_iff Q _ 1).2 fun _ => Nat.zero_lt_one
  unfold simDeliverForgeClampSan
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind (isQueryBoundP_liftProb_zero hQu ($ᵗ (BitVec 256))) fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  simpa only [Nat.one_mul] using
    CryptoGames.SM.Construction.ReductionsQueries.simulateQ_run_of_step_mul (k := 1) hq
      (fun t ht ⟨sC, ex⟩ => by
        rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
        · exact False.elim (nomatch ht)
        · exact isQueryBoundP_semSendHook P Dh encPt encT lam hQu hTr hCh qep sC ex R m none r
        · exact isQueryBoundP_semSendHook P Dh encPt encT lam hQu hTr hCh qep sC ex R m₀ (some m₁) r
        · dsimp only [simDeliverForgeOracleSan, StateT.run, StateT.mk, semHandleHookDedupS]
          rw [← Nat.add_zero 1]
          exact isQueryBoundP_bind
            (isQueryBoundP_semRecvHookS P Dh encPt encT decT lam T Kc qep B hDl hIj hDf sC ex R w
              true)
            fun ⟨rr, sC₁, ex₁⟩ _ => by
              dsimp only [deliverForgeSemHook]
              rw [pure_bind]
              exact isQueryBoundP_pure Q _ 0
        · exact isQueryBoundP_semRecvHookS P Dh encPt encT decT lam T Kc qep B hDl hIj hDf sC ex R w
            false
        · exact isQueryBoundP_semCorrHookTGB P Dh encT Bsk hCr sC ex R)
      (fun t ht ⟨sC, ex⟩ => by
        rcases t with (n | t')
        · dsimp only [simDeliverForgeOracleSan, StateT.lift, StateT.run, StateT.mk]
          rw [← Nat.add_zero 0]
          exact isQueryBoundP_bind
            ((isQueryBoundP_query_iff Q (.inl n) 0).2 fun h => absurd h (hQu n))
            fun u _ => isQueryBoundP_pure Q (u, (sC, ex)) 0
        · exact False.elim (ht rfl))
      _

theorem simDeliverForgeClampSan_sendAtomicShortDF {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (simDeliverForgeClampSan (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep B T Kc Bsk A) := by
  let P := paramsV1 C K idA idB
  have hL := atomicLengthsOk_paramsIdsWithSpqr_v1 C K idA idB ℓ hℓ
  have hDl : DlBound Pt ℓ (QAtomicShortDF Pt ℓ) 0 :=
    fun _ _ => (isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) _ 0).2 fun h => nomatch h
  have hIj : IjBound Pt ℓ (QAtomicShortDF Pt ℓ) 0 :=
    fun _ _ => (isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) _ 0).2 fun h => nomatch h
  have hDf : DfBound Pt ℓ (QAtomicShortDF Pt ℓ) 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) _ 0).2 fun h => nomatch h
  have hCr : ∀ R, IsQueryBoundP (CryptoGames.SM.Construction.DeliverForge.corrQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (C := Fig8C Pt) R) (QAtomicShortDF Pt ℓ) 0 :=
    fun _ => (isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) _ 0).2 fun h => nomatch h
  unfold SendMsgsOkDF simDeliverForgeClampSan
  change IsQueryBoundP _ (QAtomicShortDF Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind
    (isQueryBoundP_liftProb_zero (fun _ h => nomatch h) ($ᵗ (BitVec 256))) fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  refine CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_simulateQ_run_zero A
    (fun t ⟨sC, ex⟩ => ?_) _
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
  · dsimp only [simDeliverForgeOracleSan, StateT.lift, StateT.run, StateT.mk]
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind
      ((isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) (.inl n) 0).2 fun h => nomatch h)
      fun u _ => isQueryBoundP_pure (QAtomicShortDF Pt ℓ) (u, (sC, ex)) 0
  · dsimp only [simDeliverForgeOracleSan, StateT.run, StateT.mk, semHandleHookDedupS]
    rw [CryptoGames.Ratchet.LibsignalSim.semSendHook_deliverForge_eq]
    exact isQueryBoundP_runDFM
      (df_qbc_guardC (df_qbc_simSendC_atomicShort P hL qep _ hQ_QAtomicShortDF R m none r)) sC ex
  · dsimp only [simDeliverForgeOracleSan, StateT.run, StateT.mk, semHandleHookDedupS]
    rw [CryptoGames.Ratchet.LibsignalSim.semSendHook_deliverForge_eq]
    exact isQueryBoundP_runDFM
      (df_qbc_guardC (df_qbc_simSendC_atomicShort P hL qep _ hQ_QAtomicShortDF R m₀ (some m₁) r))
      sC ex
  · dsimp only [simDeliverForgeOracleSan, StateT.run, StateT.mk, semHandleHookDedupS]
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind
      (isQueryBoundP_semRecvHookS P Dh encPt encT decT lam T Kc qep B hDl hIj hDf sC ex R w true)
      fun ⟨rr, sC₁, ex₁⟩ _ => by
        dsimp only [deliverForgeSemHook]
        rw [pure_bind]
        exact isQueryBoundP_pure (QAtomicShortDF Pt ℓ) _ 0
  · exact isQueryBoundP_semRecvHookS P Dh encPt encT decT lam T Kc qep B hDl hIj hDf sC ex R w false
  · exact isQueryBoundP_semCorrHookTGB P Dh encT Bsk hCr sC ex R

section GuardedShortHelpers

open CryptoGames.SM (partyEnc)
open CryptoGames.SM.Construction.DeliverForge
  (transmitQueryDF challQueryDF deliverQueryDF injectQueryDF deliverForgeQuery corrQueryDF)
open CryptoGames.Ratchet.LibsignalSim (Fig8Comp runDFM SimState)
open CryptoGames.Ratchet.LibsignalSimC (guardC runOnBaseState simSendC)
open CryptoGames.LibsignalSM.Proofs.QueryBounds (FSpec)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (fig8ToDFImpl DeliverForgeM deliverForgeHook sameWireFig8)

private abbrev dfResp (Pt : Type) (ℓ : ℕ) :=
  smDFRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (T := Pt)

private abbrev dfLong (Pt : Type) (ℓ : ℕ) :=
  smDFRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (T := Pt)

private theorem guardedSafePost_fig8ToDFImpl_step {Pt : Type} {ℓ : ℕ}
    (t : (FSpec Pt ℓ).Domain)
    (ht : ¬ smRecvLong (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t)
    (sent : List (Fig8C Pt)) :
    GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ)
      (fun r => smRespShort (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t r.1)
      ((fig8ToDFImpl Pt ℓ t).run sent) := by
  have hQt : ¬ dfLong Pt ℓ (toDFDom t) := by
    rcases t with _ | _
    · exact not_false
    · exact ht
  have hq := GuardedSafePost.query (RespOk := dfResp Pt ℓ) hQt
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, c⟩) | ⟨R, c⟩) | R))
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ) (toDFDom (.inl n)) >>=
      fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · unfold fig8ToDFImpl transmitQueryDF
    rw [StateT.run_bind]
    have hlift : GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ)
        (fun p : Option (Fig8C Pt) × List (Fig8C Pt) =>
          smRespShort (St := Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt)
            (.inr (.inl (.inl (.inl (.inl (R, m, r)))))) p.1)
        ((StateT.lift (query (spec := DFSpec Pt ℓ)
            (toDFDom (.inr (.inl (.inl (.inl (.inl (R, m, r)))))))) :
          DeliverForgeM Pt ℓ _).run sent) := by
      dsimp only [StateT.lift, StateT.run]
      exact hq.bind fun _ ha => GuardedSafePost.pure ha
    refine hlift.bind fun ⟨res, sent'⟩ hres => ?_
    cases res <;>
      (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind];
       exact GuardedSafePost.pure hres)
  · unfold fig8ToDFImpl challQueryDF
    rw [StateT.run_bind]
    have hlift : GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ)
        (fun p : Option (Fig8C Pt) × List (Fig8C Pt) =>
          smRespShort (St := Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt)
            (.inr (.inl (.inl (.inl (.inr (R, m₀, m₁, r)))))) p.1)
        ((StateT.lift (query (spec := DFSpec Pt ℓ)
            (toDFDom (.inr (.inl (.inl (.inl (.inr (R, m₀, m₁, r)))))))) :
          DeliverForgeM Pt ℓ _).run sent) := by
      dsimp only [StateT.lift, StateT.run]
      exact hq.bind fun _ ha => GuardedSafePost.pure ha
    refine hlift.bind fun ⟨res, sent'⟩ hres => ?_
    cases res <;>
      (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind];
       exact GuardedSafePost.pure hres)
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inl (.inl (.inr (R, c)))))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inl (.inr (R, c))))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inr R))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial

private theorem guardedSafePost_deliverForgeHook_lift {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {α : Type} {P : α → Prop} {x : Fig8Comp Pt ℓ α}
    (hx : GuardedSafePost
      (smRespShort (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      P x)
    (sent : List (Fig8C Pt)) :
    GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ) (fun r => P r.1)
      (((deliverForgeHook Pt ℓ).lift x).run sent) := by
  dsimp only [deliverForgeHook]
  induction hx generalizing sent with
  | pure h =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact GuardedSafePost.pure (P := fun r : α × List (Fig8C Pt) => P r.1) h
  | @query_bind t mx hQt _ ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    have hlift : GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ)
        (fun r : (FSpec Pt ℓ).Range t × List (Fig8C Pt) =>
          smRespShort (St := Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t r.1)
        ((liftM (fig8ToDFImpl Pt ℓ t) :
          DeliverForgeM Pt ℓ _).run sent) := by
      simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using
        guardedSafePost_fig8ToDFImpl_step t hQt sent
    exact hlift.bind fun pu hpu => ih pu.1 hpu pu.2

private abbrev DFSafePost (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (oa : AdversaryCompDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
      (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)))) : Prop :=
  GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ) (fun r => True ∧ SimShortInv r.2.1.base) oa

private def dfSafeC (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (DeliverForgeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt)),
    SimShortInv sC.base →
    GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ) (fun p => SimShortInv p.1.2.base)
      ((x.run sC).run sent)

private theorem dfSafePost_runDFM {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (DeliverForgeM Pt ℓ) α}
    (hx : dfSafeC PQ Pt ℓ x)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base) :
    DFSafePost PQ Pt ℓ (runDFM x sC ex) := by
  unfold runDFM
  exact (hx sC ex hs).bind fun _ hp => GuardedSafePost.pure ⟨trivial, hp⟩

private theorem dfSafeC_pure {PQ Pt : Type} {ℓ : ℕ} {α : Type} (a : α) :
    dfSafeC PQ Pt ℓ (pure a) := fun _ _ hs => by
  simp only [StateT.run_pure]
  exact GuardedSafePost.pure
    (P := fun p : (α × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt) =>
      SimShortInv p.1.2.base) hs

private theorem dfSafeC_bind {PQ Pt : Type} {ℓ : ℕ} {α β : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (DeliverForgeM Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (DeliverForgeM Pt ℓ) β}
    (hx : dfSafeC PQ Pt ℓ x) (hf : ∀ a, dfSafeC PQ Pt ℓ (f a)) :
    dfSafeC PQ Pt ℓ (x >>= f) := fun sC sent hs => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hx sC sent hs).bind fun p hp => hf p.1.1 p.1.2 p.2 hp

private theorem dfSafeC_get_bind {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    {f : LibsignalToModularSchemeSimState PQ Pt ℓ →
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
        (DeliverForgeM Pt ℓ) α}
    (hf : ∀ sC, SimShortInv sC.base → dfSafeC PQ Pt ℓ (f sC)) :
    dfSafeC PQ Pt ℓ (get >>= f) := fun sC sent hs => by
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf sC hs sC sent hs

private theorem dfSafeC_set {PQ Pt : Type} {ℓ : ℕ}
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (h : SimShortInv sC'.base) :
    dfSafeC PQ Pt ℓ (set sC') := fun _ _ _ => by
  simp only [StateT.run_set, StateT.run_pure]
  exact GuardedSafePost.pure
    (P := fun p : (PUnit × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt) =>
      SimShortInv p.1.2.base) h

private theorem dfSafeC_guardC {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ)
      (DeliverForgeM Pt ℓ) (Option α)}
    (hx : dfSafeC PQ Pt ℓ x) :
    dfSafeC PQ Pt ℓ (guardC x) := by
  unfold guardC
  refine dfSafeC_get_bind fun _ _ => ?_
  split
  · exact dfSafeC_pure none
  · exact hx

private theorem dfSafeC_zoomB {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {α : Type}
    {x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    (hx : SimSafeS PQ Pt ℓ x) :
    dfSafeC PQ Pt ℓ
      (runOnBaseState (deliverForgeHook Pt ℓ) x) :=
  fun sC sent hs => by
    show GuardedSafePost _ _ _
      (((deliverForgeHook Pt ℓ).lift (x.run sC.base) >>=
        fun p => pure (p.1, { sC with base := p.2 })).run sent)
    rw [StateT.run_bind]
    exact (guardedSafePost_deliverForgeHook_lift (hx sC.base hs) sent).bind fun p hp => by
      simp only [StateT.run_pure]
      exact GuardedSafePost.pure
        (P := fun r : (α × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt) =>
          SimShortInv r.1.2.base) hp

private theorem dfSafeC_simSendC {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] (P : Params PQ PQC) {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    dfSafeC PQ Pt ℓ
      (simSendC P qep fig (deliverForgeHook Pt ℓ) Q m₀ chal r) := by
  unfold simSendC
  refine dfSafeC_bind (dfSafeC_zoomB (guardedSafeS_simSend P qep Q m₀ chal r)) fun res => ?_
  cases res with
  | none => exact dfSafeC_pure none
  | some w =>
    refine dfSafeC_get_bind fun _ hsC => ?_
    exact dfSafeC_bind (dfSafeC_set _ hsC) fun _ => dfSafeC_pure (some w)

private theorem simShortInv_onAcceptPure {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2 := by
  unfold onAcceptPure
  dsimp only
  split_ifs
  · rcases s.mir.inTransit Q.other w with _ | r
    · exact hs
    · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact hs
  · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact ⟨hs.1, hs.2⟩

private theorem simShortInv_onAnswerPure {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (CryptoGames.SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (onAnswerPure qep Q w isDel ci? Tpk pq' res s).2 := by
  unfold onAnswerPure
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact simShortInv_onAcceptPure qep Q w isDel t i _ ci? Tpk pq' s hs

private theorem guardedSafePost_deliverQueryDF {Pt : Type} {ℓ : ℕ} (Q : Party)
    (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ) (fun _ => True)
      (deliverQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q c) := by
  unfold deliverQueryDF
  exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfResp Pt ℓ) (Q := dfLong Pt ℓ)
    (t := Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Q, c)))))) (fun h => h hc)

private theorem guardedSafePost_injectQueryDF {Pt : Type} {ℓ : ℕ} (Q : Party)
    (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ) (fun _ => True)
      (injectQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q c) := by
  unfold injectQueryDF
  exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfResp Pt ℓ) (Q := dfLong Pt ℓ)
    (t := Sum.inr (Sum.inl (Sum.inl (Sum.inr (Q, c))))) (fun h => h hc)

private theorem guardedSafePost_deliverForgeSemHook_onProbe {PQC Pt : Type} [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ} (Q : Party) (c' : Fig8C Pt)
    (hc' : c'.2.2.1.1.length < 2 ^ 32) (ex : List (Fig8C Pt)) :
    GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ) (fun _ => True)
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex) := by
  unfold deliverForgeSemHook
  dsimp only
  rcases ex.find? (fun c => sameWireFig8 c c') with _ | c
  · exact GuardedSafePost.pure trivial
  · have hq : GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ) (fun _ => True)
        (deliverForgeQuery
          (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
          (Coins := BitVec 256) (C := Fig8C Pt) Q c c') := by
      unfold deliverForgeQuery
      exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfResp Pt ℓ) (Q := dfLong Pt ℓ)
        (t := Sum.inr (Sum.inr (Q, c, c'))) (fun h => h hc')
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial

private theorem dfSafePost_semFwdAnswerHookS {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (semFwdAnswerHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex Q w isDel ci? Tpk pq' c') := by
  unfold semFwdAnswerHookS deliverForgeSemHook
  dsimp only
  refine GuardedSafePost.bind (P := fun _ => True) ?_ fun ⟨res, ex₁⟩ _ =>
    GuardedSafePost.pure
      ⟨trivial, simShortInv_onAnswerPure qep Q w isDel ci? Tpk pq' res sC.base hs⟩
  split_ifs
  · exact (guardedSafePost_deliverQueryDF Q c' hc').bind fun _ _ => GuardedSafePost.pure trivial
  · exact (guardedSafePost_injectQueryDF Q c' hc').bind fun _ _ => GuardedSafePost.pure trivial

private theorem dfSafePost_semResyncHookS {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    DFSafePost PQ Pt ℓ
      (semResyncHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex Q w ci? Tpk pq' c r) := by
  unfold semResyncHookS deliverForgeSemHook
  rcases r with _ | ⟨t, i, _, m'⟩
  · exact GuardedSafePost.pure ⟨trivial, hs⟩
  · dsimp only
    refine GuardedSafePost.bind (P := fun _ => True)
      ((guardedSafePost_deliverQueryDF Q c hc).bind fun _ _ => GuardedSafePost.pure trivial)
      fun ⟨res, ex₁⟩ _ => ?_
    rcases res with _ | (_ | _)
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure
        ⟨trivial, simShortInv_onAcceptPure qep Q w true t i m' ci? Tpk pq' sC.base hs⟩

private theorem dfSafePost_semFwdEvictHookS {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (semFwdEvictHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex Q w isDel Tpk pq' c') := by
  unfold semFwdEvictHookS
  split_ifs
  · exact (guardedSafePost_deliverForgeSemHook_onProbe (PQC := PQC) Q c' hc' ex).bind
      fun _ _ => GuardedSafePost.pure ⟨trivial, hs⟩
  · exact dfSafePost_semFwdAnswerHookS P Dh encPt encT lam T qep sC ex hs Q w isDel none
      Tpk pq' c' hc'

private theorem dfSafePost_semFwdHookS {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T Kc qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt))
    (hhon : ∀ c, honestC = some c → c.2.2.1.1.length < 2 ^ 32)
    (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (semFwdHookS P Dh encPt encT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep B sC ex Q w isDel ci? Tpk pq' honestC c') := by
  unfold semFwdHookS
  rcases honestC with _ | c
  · exact dfSafePost_semFwdAnswerHookS P Dh encPt encT lam T qep sC ex hs Q w isDel ci?
      Tpk pq' c' hc'
  · dsimp only
    split_ifs
    · rcases evalCKS P Dh encPt encT lam T Kc B sC Q w c c' with _ | r
      · exact (guardedSafePost_deliverForgeSemHook_onProbe (PQC := PQC) Q c' hc' ex).bind
          fun _ _ => GuardedSafePost.pure ⟨trivial, hs⟩
      · exact dfSafePost_semResyncHookS P Dh encPt encT lam T qep sC ex hs Q w ci? Tpk pq' c
          (hhon c rfl) r
    · exact dfSafePost_semFwdAnswerHookS P Dh encPt encT lam T qep sC ex hs Q w isDel ci?
        Tpk pq' c' hc'

private theorem simParseRecvC_ser_eq {PQ PQC Pt : Type} (P : Params PQ PQC)
    (decT : PublicKey → Option Pt) (B : ℕ) (qB : Bool) (pq : PQ) (w : Bytes)
    {pq' : PQ} {i : ℕ} {pk : PublicKey} {T? : Option Pt}
    {lct : ℕ × LibsignalCiphertextWithSalt32}
    (hp : simParseRecvC P decT B qB pq w = some (pq', (i, (pk, (T?, lct))))) :
    lct.2.1.1 = w.take (w.length - 8) := by
  unfold simParseRecvC at hp
  split_ifs at hp
  dsimp only [] at hp
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
  · rw [hparse] at hp; cases hp
  · rw [hparse] at hp; dsimp only [] at hp
    split_ifs at hp
    rcases hspqr : P.spqr.recv pq h.pqRatchet with _ | ⟨pq1, salt⟩
    · rw [hspqr] at hp; cases hp
    · rw [hspqr] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      exact congrArg (fun x : ℕ × LibsignalCiphertextWithSalt32 => x.2.1.1) hp.2.2.2.2.symm

private theorem dfSafePost_semRecvHookS {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (T Kc qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) :
    DFSafePost PQ Pt ℓ
      (semRecvHookS P Dh encPt encT decT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep B sC ex Q w isDel) := by
  unfold semRecvHookS
  dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w
      with _ | ⟨pq', i, pk, T?, lct⟩
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · have hwlen : w.length < 2 ^ 32 := by
        cases isDel with
        | true =>
          rcases htr : sC.base.mir.inTransit Q.other w with _ | rec'
          · simp [htr] at href
          · obtain ⟨hmem, rfl⟩ := inTransit_mem_and_ct htr
            exact hs.1 rec' hmem
        | false =>
          by_cases hw9 : w.length < 9
          · omega
          · have hadm : ratchetKeyAdmissible P.codec decT encT w = true := by
              revert href
              cases ratchetKeyAdmissible P.codec decT encT w <;> simp
            unfold ratchetKeyAdmissible at hadm
            simp only [hw9, ↓reduceIte] at hadm
            have hp0 := hp
            unfold simParseRecvC at hp0
            split_ifs at hp0
            dsimp only [] at hp0
            rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
            · rw [hparse] at hp0; cases hp0
            · simp only [hparse, Bool.and_eq_true, decide_eq_true_eq] at hadm
              exact hadm.1
      have hlct : lct.2.1.1.length < 2 ^ 32 := by
        rw [simParseRecvC_ser_eq P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w hp,
          List.length_take]
        omega
      have hhon : ∀ c : Fig8C Pt,
          (sC.base.honest.find? fun (wc : Bytes × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
              (fun (wc : Bytes × Fig8C Pt) => wc.2) = some c →
          c.2.2.1.1.length < 2 ^ 32 := by
        intro c hc_eq
        rcases Option.mem_map.mp hc_eq with ⟨wc, hfind, rfl⟩
        exact hs.2 wc (List.mem_of_find?_eq_some hfind)
      have hmkC : ∀ (t : ℕ) (To : Option Pt),
          (match (sC.base.honest.find? fun (wc : Bytes × Fig8C Pt) =>
               wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
                 (fun (wc : Bytes × Fig8C Pt) => wc.2) with
           | some (c : Fig8C Pt) =>
             if c.2.2.2 = lct.2.2 then c else ((t, To), lct)
           | none => ((t, To), lct)).2.2.1.1.length < 2 ^ 32 := by
        intro t To
        rcases hfind : sC.base.honest.find? (fun (wc : Bytes × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with _ | wc
        · exact hlct
        · simp only [Option.map]
          split
          · exact hs.2 wc (List.mem_of_find?_eq_some hfind)
          · exact hlct

      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · have hsAmb : SimShortInv
            ({ sC with base :=
                if inReceiveOnlyEpoch sC.base.mir Q ||
                    (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
                  { sC.base with amb := sC.base.amb + 1 }
                else sC.base }).base := by
          dsimp only
          split_ifs <;> exact ⟨hs.1, hs.2⟩
        split
        · exact GuardedSafePost.pure ⟨trivial, hs⟩
        · split
          · exact GuardedSafePost.pure ⟨trivial, hs⟩
          · split
            · exact GuardedSafePost.pure ⟨trivial, hsAmb⟩
            · rcases T? with _ | T₀
              · exact GuardedSafePost.pure ⟨trivial, hsAmb⟩
              · dsimp only
                split
                · exact dfSafePost_semFwdEvictHookS P Dh encPt encT lam T qep _ ex hsAmb
                    Q w isDel pk pq' _ hlct
                · exact dfSafePost_semFwdHookS P Dh encPt encT lam T Kc qep B _ ex hsAmb
                    Q w isDel none pk pq' _ hhon _ (hmkC _ _)
      · split
        · exact GuardedSafePost.pure ⟨trivial, hs⟩
        · exact dfSafePost_semFwdHookS P Dh encPt encT lam T Kc qep B sC ex hs
            Q w isDel (some ci) pk pq' _ hhon _ (hmkC _ _)
  · simp only [↓reduceIte]
    exact GuardedSafePost.pure ⟨trivial, hs⟩

private theorem dfSafePost_semCorrHookTGB {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (Bsk : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base) (Q : Party) :
    DFSafePost PQ Pt ℓ
      (semCorrHookTGB P Dh encT
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        Bsk sC ex Q) := by
  unfold semCorrHookTGB deliverForgeSemHook
  dsimp only
  split
  · exact GuardedSafePost.pure ⟨trivial, hs⟩
  · have hq : GuardedSafePost (dfResp Pt ℓ) (dfLong Pt ℓ) (fun _ => True)
        (corrQueryDF
          (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
          (Coins := BitVec 256) (C := Fig8C Pt) Q) := by
      unfold corrQueryDF
      exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfResp Pt ℓ) (Q := dfLong Pt ℓ)
        (t := Sum.inr (Sum.inl (Sum.inr Q))) not_false
    refine GuardedSafePost.bind (P := fun _ => True)
      (hq.bind fun _ _ => GuardedSafePost.pure trivial) fun ⟨res, ex₁⟩ _ => ?_
    rcases res with _ | _
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure ⟨trivial, hs.1, hs.2⟩

end GuardedShortHelpers

theorem simDeliverForgeClampSan_guardedSMDFShort {PQ PQC Pt : Type}
    [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    GuardedSMDFShort (simDeliverForgeClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) := by
  unfold GuardedSMDFShort simDeliverForgeClampSan
  refine (GuardedSafePost.liftComp_unif hQu_smDFRecvLong ($ᵗ BitVec 256)).bind fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost
      (smDFRespShort (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun r => SimShortInv r.2.1.base)
      ((simulateQ (simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), [])) := by
    refine GuardedSafePost.simulateQ_run
      (I := fun p : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt) =>
        SimShortInv p.1.base)
      (GuardedSafePost.true_of_false A) ?_ (simShortInv_initSim _ _)
    rintro (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) _ ⟨sC, ex⟩ hs
    · show DFSafePost PQ Pt ℓ
        (query (spec := DFSpec Pt ℓ) (.inl n) >>= fun a => pure (a, (sC, ex)))
      exact (GuardedSafePost.query (hQu_smDFRecvLong n)).bind fun _ _ =>
        GuardedSafePost.pure ⟨trivial, hs⟩
    · change DFSafePost PQ Pt ℓ
        (CryptoGames.Ratchet.LibsignalSim.semSendHook P Dh encPt encT lam
          deliverForgeSemHook qep sC ex Q m none r)
      rw [CryptoGames.Ratchet.LibsignalSim.semSendHook_deliverForge_eq]
      exact dfSafePost_runDFM (dfSafeC_guardC (dfSafeC_simSendC P qep _ Q m none r)) sC ex hs
    · change DFSafePost PQ Pt ℓ
        (CryptoGames.Ratchet.LibsignalSim.semSendHook P Dh encPt encT lam
          deliverForgeSemHook qep sC ex Q m₀ (some m₁) r)
      rw [CryptoGames.Ratchet.LibsignalSim.semSendHook_deliverForge_eq]
      exact dfSafePost_runDFM
        (dfSafeC_guardC (dfSafeC_simSendC P qep _ Q m₀ (some m₁) r)) sC ex hs
    · change DFSafePost PQ Pt ℓ
        (semRecvHookS P Dh encPt encT decT lam T Kc deliverForgeSemHook qep B sC ex Q w true >>=
          fun ⟨rr, sC₁, ex₁⟩ =>
            (deliverForgeSemHook (PQC := PQC)).onDeliverPost Q
              (sC.base.honest.reverse.findIdx? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) rr ex₁ >>=
              fun ex₂ => pure (rr, (sC₁, ex₂)))
      exact (dfSafePost_semRecvHookS P Dh encPt encT decT lam T Kc qep B sC ex hs Q w true).bind
        fun ⟨rr, sC₁, ex₁⟩ ⟨_, hs₁⟩ => by
          dsimp only [deliverForgeSemHook]
          rw [pure_bind]
          exact GuardedSafePost.pure ⟨trivial, hs₁⟩
    · exact dfSafePost_semRecvHookS P Dh encPt encT decT lam T Kc qep B sC ex hs Q w false
    · exact dfSafePost_semCorrHookTGB P Dh encT Bsk sC ex hs Q
  exact hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial

theorem simDeliverForgeEval_bounds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (L qep T Kc Bsk q : ℕ) (hqL : q ≤ L)
    (prog : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool)
    (dec : prog.σ.denote → LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt))
    (Extra : LibsignalToModularSchemeSimState Bytes Pt ℓ → Prop)
    (hExtra_init : ∀ pqrKey : BitVec 256,
      Extra (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
        ((paramsV1 C K idA idB).spqr.init .b2a pqrKey)))
    (hExtra_step : ∀ t (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ) (ex : List (Fig8C Pt)),
      Extra sC →
      ∀ x ∈ support ((simDeliverForgeOracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep (2 ^ 32) T Kc Bsk (.inr t)).run (sC, ex)), Extra x.2.1)
    (hinit : (Prod.map id dec <$> prog.init.eval (.cons () .nil)) =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
            (BitVec 256))
        return ((), (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
          ((paramsV1 C K idA idB).spqr.init .b2a pqrKey), []))))
    (hfin : ∀ s b, prog.finish.eval (.cons s (.cons b .nil)) = pure b)
    (hstep : ∀ t (s_raw : prog.σ.denote),
      let s := dec s_raw
      SimCStateBounded L s.1 →
      s.2.length ≤ L →
      Extra s.1 →
      (Prod.map id dec <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) prog.handle (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam
        qep (2 ^ 32) T Kc Bsk (.inr t)).run s))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    prog.eval (fun _ => A) () =
        simDeliverForgeClampSan (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam
          qep (2 ^ 32) T Kc Bsk A ∧
      MakesAtMostQueriesDF (prog.eval (fun _ => A) ()) q ∧
      SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        (prog.eval (fun _ => A) ()) ∧
      GuardedSMDFShort (prog.eval (fun _ => A) ()) := by
  have hq' := (CryptoGames.Ratchet.LibsignalSim.makesAtMostQueries_iff_isGameQuery A q).mp hq
  let P := paramsV1 C K idA idB
  have hinit_inv : ∀ r ∈ support (prog.init.eval (.cons () .nil)),
      DFStateInv L q (dec r.2) ∧ Extra (dec r.2).1 := by
    rintro ⟨u₀, s_raw⟩ hr
    have hmem : (u₀, dec s_raw) ∈ support (Prod.map id dec <$> prog.init.eval (.cons () .nil)) := by
      rw [support_map, Set.mem_image]
      exact ⟨(u₀, s_raw), hr, rfl⟩
    rw [hinit, mem_support_bind_iff] at hmem
    obtain ⟨pqrKey, -, hmem⟩ := hmem
    rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, hEq⟩
    rw [hEq]
    exact ⟨dfStateInv_initSimC hqL _ _, hExtra_init pqrKey⟩
  have habs := prog.eval_eq_simulateQ_of_abs dec
    (fun m s_raw => DFStateInv L m (dec s_raw) ∧ Extra (dec s_raw).1)
    (fun _ => do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
          (BitVec 256))
      return ((), (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), [])))
    (simDeliverForgeOracleSan P Dh encPt encT decT lam qep (2 ^ 32) T Kc Bsk)
    (fun _ b => pure b) q () hinit hinit_inv (fun _ _ => rfl)
    (fun m t s_raw hInv => by
      have hbnd := hInv.1.toBounded
      have heq := hstep t s_raw hbnd.1 hbnd.2 hInv.2
      refine ⟨heq, ?_⟩
      rintro ⟨rr, s_raw'⟩ hmem
      have hmem' : (rr, dec s_raw') ∈
          support ((simDeliverForgeOracleSan P Dh encPt encT decT lam
            qep (2 ^ 32) T Kc Bsk (.inr t)).run (dec s_raw)) := by
        rw [← heq, support_map, Set.mem_image]
        exact ⟨(rr, s_raw'), hmem, rfl⟩
      exact ⟨simDeliverForgeOracleSan_preserves_dfStateInv P Dh encPt encT decT lam
          L m qep (2 ^ 32) T Kc Bsk t (dec s_raw) hInv.1 (rr, dec s_raw') hmem',
        hExtra_step t (dec s_raw).1 (dec s_raw).2 hInv.2 (rr, dec s_raw') hmem'⟩)
    (fun s b _ => hfin s b) (fun _ hle hInv => ⟨hInv.1.mono hle, hInv.2⟩)
    (fun _ => A) (fun _ => hq')
  have heval : prog.eval (fun _ => A) () =
      simDeliverForgeClampSan P ℓ Dh encPt encT decT lam qep (2 ^ 32) T Kc Bsk A := by
    rw [habs]
    dsimp only [simDeliverForgeClampSan, P]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun pqrKey => ?_
    rw [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]
  refine ⟨heval, ?_, ?_, ?_⟩ <;> rw [heval]
  · exact simDeliverForgeClampSan_makesAtMostQueriesDF P Dh encPt encT decT lam
      qep (2 ^ 32) T Kc Bsk q A hq
  · exact simDeliverForgeClampSan_sendAtomicShortDF hℓ C K idA idB Dh encPt encT decT lam
      qep (2 ^ 32) T Kc Bsk A
  · exact simDeliverForgeClampSan_guardedSMDFShort P Dh encPt encT decT lam
      qep (2 ^ 32) T Kc Bsk A

theorem simDeliverForgeProgOfStep_sendAtomicShortDF_and_guarded {Pt : Type} [DecidableEq Pt]
    [Zero Pt] [SampleableType Pt] {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (Extra : LibsignalToModularSchemeSimState Bytes Pt ℓ → Prop)
    (hExtra_init : ∀ pqrKey : BitVec 256,
      Extra (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
        ((paramsV1 C K idA idB).spqr.init .b2a pqrKey)))
    (hExtra_step : ∀ t (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)),
      Extra s.1 →
      ∀ x ∈ support ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep q (.inr t)).run s), Extra x.2.1)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (dfFullT ℓ Pt).denote),
      SimCStateBounded q (dfFullDec s_raw).1 → (dfFullDec s_raw).2.length ≤ q →
      Extra (dfFullDec s_raw).1 →
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam qep q
        (.inr t)).run (dfFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        ((simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) ()) ∧
      GuardedSMDFShort
        ((simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) ()) := by
  rw [simDeliverForgeProgOfStep_eval_sanQ C K idA idB Dh encPt encT decT lam qep q hℓ
        Extra hExtra_init hExtra_step step hstep A hq]
  exact ⟨simDeliverForgeClampSan_sendAtomicShortDF hℓ C K idA idB Dh encPt encT decT lam _ _ _ _ _ A,
    simDeliverForgeClampSan_guardedSMDFShort _ Dh encPt encT decT lam _ _ _ _ _ A⟩

theorem simDeliverForgeProgOfStep_makesAtMostQueriesDF {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {ℓ : ℕ} (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (Extra : LibsignalToModularSchemeSimState Bytes Pt ℓ → Prop)
    (hExtra_init : ℓ < 10 ^ 6 → ∀ pqrKey : BitVec 256,
      Extra (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
        ((paramsV1 C K idA idB).spqr.init .b2a pqrKey)))
    (hExtra_step : ℓ < 10 ^ 6 → ∀ t (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)),
      Extra s.1 →
      ∀ x ∈ support ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep q (.inr t)).run s), Extra x.2.1)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep : ℓ < 10 ^ 6 → ∀ t (s_raw : (dfFullT ℓ Pt).denote),
      SimCStateBounded q (dfFullDec s_raw).1 → (dfFullDec s_raw).2.length ≤ q →
      Extra (dfFullDec s_raw).1 →
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam qep q
        (.inr t)).run (dfFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    MakesAtMostQueriesDF
      ((simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) ()) q := by
  by_cases hℓ : ℓ < 10 ^ 6
  · rw [simDeliverForgeProgOfStep_eval_sanQ C K idA idB Dh encPt encT decT lam qep q hℓ
        Extra (hExtra_init hℓ) (hExtra_step hℓ) step (hstep hℓ) A hq]
    exact simDeliverForgeClampSan_makesAtMostQueriesDF _ Dh encPt encT decT lam _ _ _ _ _ q A hq
  · unfold simDeliverForgeProgOfStep
    simp only [hℓ, ↓reduceDIte]
    rw [CryptoGames.Ratchet.LibsignalSim.makesAtMostQueriesDF_iff_isGameQuery]
    have hq' := (CryptoGames.Ratchet.LibsignalSim.makesAtMostQueries_iff_isGameQuery A q).mp hq
    have h0 := CostedReduction.queryBound_eval
      (Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon.dummyBoolSessionRed
        (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt) .unit)
      (isGameQuery (G := specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (Fig8C Pt)))
      (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl)
      (fun _ => by simp [isGameQuery, isQueryBoundP_query_iff])
      (fun _ => A) q (fun _ => hq') ()
    exact h0.mono ((Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon.dummyBoolSessionRed_totalQueries
      (fig8SmIfaceDF ℓ Pt) .unit (fun _ => 1) (fun _ => 0) q).le.trans (Nat.zero_le q))

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCouplingBounds
