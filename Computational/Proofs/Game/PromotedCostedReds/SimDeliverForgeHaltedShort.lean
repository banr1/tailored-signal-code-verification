/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanCouplingBounds

/-!
# Shortness and Guardedness for `SimDeliverForgeHalted`

Proves `SendMsgsOkDF` (`atomicShortPubB`) and `GuardedSMDFShort` for the tracker-halted sanitized
`DeliverForge` reduction `simDeliverForgeClampSanTrackHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedShort

noncomputable section

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (partyEnc noBobSendInEpoch0)
open CryptoGames.GuardedSafe (GuardedSafePost)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params)
open CryptoGames.Ratchet.LibsignalInst
  (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32 ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C SimState inReceiveOnlyEpoch onAcceptPure onAnswerPure
   deliverForgeSemHook simParseRecvC mkPub scPostSendPure toWire)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.SM.Construction.DeliverForge
  (AdversaryCompDF transmitQueryDF challQueryDF deliverQueryDF injectQueryDF
   deliverForgeQuery corrQueryDF)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack sameWireFig8 stepKemFailSend)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (SimShortInv simShortInv_initSim simShortInv_record epMgmt_trans_eq
   inTransit_mem_and_ct mem_accept_trans)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes paramsV1)
open CryptoVerification.LibsignalSession.HeadlineV1
  (DFSpec SendMsgsOkDF QAtomicShortDF AtomicLengthsOk atomicShortPubB_mkPub
   atomicLengthsOk_paramsIdsWithSpqr_v1 smDFRespShort smDFRecvLong GuardedSMDFShort
   hQu_smDFRecvLong badSendMsgDF)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (semRecvHookS semFwdAnswerHookS semResyncHookS semFwdEvictHookS semFwdHookS
   semCorrHookTGB evalCKS)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedBase
  (semSendTrackHalted simDeliverForgeOracleSanTrackHalted simDeliverForgeClampSanTrackHalted)

private theorem isQueryBoundP_liftProb_zero_local {Pt : Type} {ℓ : ℕ}
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

private abbrev DlBoundH (Pt : Type) (ℓ : ℕ) (Q : (DFSpec Pt ℓ).Domain → Prop)
    [DecidablePred Q] (d : ℕ) : Prop :=
  ∀ R c, IsQueryBoundP (deliverQueryDF
    (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (C := Fig8C Pt) R c) Q d

private abbrev IjBoundH (Pt : Type) (ℓ : ℕ) (Q : (DFSpec Pt ℓ).Domain → Prop)
    [DecidablePred Q] (d : ℕ) : Prop :=
  ∀ R c, IsQueryBoundP (injectQueryDF
    (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (C := Fig8C Pt) R c) Q d

private abbrev DfBoundH (Pt : Type) (ℓ : ℕ) (Q : (DFSpec Pt ℓ).Domain → Prop)
    [DecidablePred Q] (d : ℕ) : Prop :=
  ∀ R c c', IsQueryBoundP (deliverForgeQuery
    (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (C := Fig8C Pt) R c c') Q d

private theorem isQueryBoundP_onProbe_local {PQC Pt : Type} [DecidableEq Pt] [SampleableType PQC]
    {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDf : DfBoundH Pt ℓ Q d) (R : Party) (c' : Fig8C Pt) (ex : List (Fig8C Pt)) :
    IsQueryBoundP
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe R c' ex) Q d := by
  unfold deliverForgeSemHook
  dsimp only
  rcases ex.find? (fun c => sameWireFig8 c c') with _ | c
  · exact isQueryBoundP_pure Q ex d
  · rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (hDf R c c') fun _ _ => isQueryBoundP_pure Q ex 0

private theorem isQueryBoundP_semFwdAnswerHookS_local {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBoundH Pt ℓ Q d) (hIj : IjBoundH Pt ℓ Q d)
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

private theorem isQueryBoundP_semResyncHookS_local {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBoundH Pt ℓ Q d)
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

private theorem isQueryBoundP_semFwdEvictHookS_local {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBoundH Pt ℓ Q d) (hIj : IjBoundH Pt ℓ Q d) (hDf : DfBoundH Pt ℓ Q d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (R : Party) (w : Bytes) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    IsQueryBoundP
      (semFwdEvictHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex R w isDel Tpk pq' c') Q d := by
  unfold semFwdEvictHookS
  split
  · rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (isQueryBoundP_onProbe_local hDf R c' ex) fun _ _ =>
      isQueryBoundP_pure Q _ 0
  · exact isQueryBoundP_semFwdAnswerHookS_local P Dh encPt encT lam T qep hDl hIj
      sC ex R w isDel none Tpk pq' c'

private theorem isQueryBoundP_semFwdHookS_local {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (T Kc qep B : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBoundH Pt ℓ Q d) (hIj : IjBoundH Pt ℓ Q d) (hDf : DfBoundH Pt ℓ Q d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (R : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    IsQueryBoundP
      (semFwdHookS P Dh encPt encT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep B sC ex R w isDel ci? Tpk pq' honestC c') Q d := by
  unfold semFwdHookS
  rcases honestC with _ | c
  · exact isQueryBoundP_semFwdAnswerHookS_local P Dh encPt encT lam T qep hDl hIj
      sC ex R w isDel ci? Tpk pq' c'
  · dsimp only
    split
    · rcases evalCKS P Dh encPt encT lam T Kc B sC R w c c' with _ | r
      · rw [← Nat.add_zero d]
        exact isQueryBoundP_bind (isQueryBoundP_onProbe_local hDf R c' ex) fun _ _ =>
          isQueryBoundP_pure Q _ 0
      · exact isQueryBoundP_semResyncHookS_local P Dh encPt encT lam T qep hDl
          sC ex R w ci? Tpk pq' c r
    · exact isQueryBoundP_semFwdAnswerHookS_local P Dh encPt encT lam T qep hDl hIj
        sC ex R w isDel ci? Tpk pq' c'

private theorem isQueryBoundP_semRecvHookS_local {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (T Kc qep B : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hDl : DlBoundH Pt ℓ Q d) (hIj : IjBoundH Pt ℓ Q d) (hDf : DfBoundH Pt ℓ Q d)
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
  · rcases simParseRecvC P decT (2 ^ 32) (partyEnc R) (sC.base.pq R) w with
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
                · exact isQueryBoundP_semFwdEvictHookS_local P Dh encPt encT lam T qep
                    hDl hIj hDf _ ex R w isDel pk pq' _
                · exact isQueryBoundP_semFwdHookS_local P Dh encPt encT lam T Kc qep B
                    hDl hIj hDf _ ex R w isDel none pk pq' _ _
      · split
        · exact isQueryBoundP_pure Q _ d
        · exact isQueryBoundP_semFwdHookS_local P Dh encPt encT lam T Kc qep B
            hDl hIj hDf sC ex R w isDel (some ci) pk pq' _ _

private theorem isQueryBoundP_semCorrHookTGB_local {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Bsk : ℕ)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {d : ℕ}
    (hCr : ∀ R, IsQueryBoundP
      (corrQueryDF
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

private theorem isQueryBoundP_semSendTrackHalted_atomicShort
    {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (hL : AtomicLengthsOk P ℓ)
    (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (R : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    IsQueryBoundP
      (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr R m₀ chal r)
      (QAtomicShortDF Pt ℓ) 0 := by
  let Q := QAtomicShortDF Pt ℓ
  have hQu : ∀ n, ¬ Q (.inl n) := fun _ h => nomatch h
  unfold semSendTrackHalted
  split
  · exact isQueryBoundP_pure Q _ 0
  · rcases sC.base.mir.epMgmt 3 qep R r.isSome with _ | s₁
    · exact isQueryBoundP_pure Q _ 0
    · dsimp only
      split
      · exact isQueryBoundP_pure Q _ 0
      · generalize ($ᵗ (BitVec 512) : ProbComp (BitVec 512)) = p512
        generalize ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) = p256
        have hrq : IsQueryBoundP
            (match r with
            | some rq => pure rq
            | none => (liftM p512 :
                AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
                  (BitVec 256) (Fig8C Pt) (BitVec 512))) Q 0 := by
          rcases r with _ | rq
          · exact isQueryBoundP_liftProb_zero_local hQu p512
          · exact isQueryBoundP_pure Q rq 0
        rw [← Nat.zero_add 0]
        refine isQueryBoundP_bind hrq fun rq _ => ?_
        split
        · exact isQueryBoundP_pure Q _ 0
        · have hrc : IsQueryBoundP
              (match r with
              | some _ => some <$> (liftM p256 :
                  AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
                    (BitVec 256) (Fig8C Pt) (BitVec 256))
              | none => pure none) Q 0 := by
            rcases r with _ | _
            · exact isQueryBoundP_pure Q none 0
            · simp only [isQueryBoundP_map_iff]
              exact isQueryBoundP_liftProb_zero_local hQu p256
          rw [← Nat.zero_add 0]
          refine isQueryBoundP_bind hrc fun rc _ => ?_
          rcases hmk : mkPub (P := P) sC.base R rq
              (if s₁.epoch R ≠ sC.base.mir.epoch R then
                BitVec.ofNat 32 (sC.base.mir.idx R - 1) else sC.base.pn R) with _ | ⟨pq', pub⟩
          · exact isQueryBoundP_pure Q _ 0
          · dsimp only
            have hshort : atomicShortPubB pub = true :=
              atomicShortPubB_mkPub hL sC.base R rq _ hmk
            rw [← Nat.add_zero 0]
            refine isQueryBoundP_bind ?_ fun res _ => ?_
            · rcases chal with _ | m₁
              · exact (isQueryBoundP_query_iff Q _ 0).2 (by simp [Q, QAtomicShortDF, badSendMsgDF, hshort])
              · exact (isQueryBoundP_query_iff Q _ 0).2 (by simp [Q, QAtomicShortDF, badSendMsgDF, hshort])
            · rcases res with _ | c <;> exact isQueryBoundP_pure Q _ 0

theorem simDeliverForgeClampSanTrackHalted_sendAtomicShortDF
    {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (simDeliverForgeClampSanTrackHalted (paramsV1 C K idA idB) K ℓ Dh encPt encT decT lam
        qep B T Kc Bsk A) := by
  let P := paramsV1 C K idA idB
  have hL := atomicLengthsOk_paramsIdsWithSpqr_v1 C K idA idB ℓ hℓ
  have hDl : DlBoundH Pt ℓ (QAtomicShortDF Pt ℓ) 0 :=
    fun _ _ => (isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) _ 0).2 fun h => nomatch h
  have hIj : IjBoundH Pt ℓ (QAtomicShortDF Pt ℓ) 0 :=
    fun _ _ => (isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) _ 0).2 fun h => nomatch h
  have hDf : DfBoundH Pt ℓ (QAtomicShortDF Pt ℓ) 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) _ 0).2 fun h => nomatch h
  have hCr : ∀ R, IsQueryBoundP (corrQueryDF
      (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (C := Fig8C Pt) R) (QAtomicShortDF Pt ℓ) 0 :=
    fun _ => (isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) _ 0).2 fun h => nomatch h
  unfold SendMsgsOkDF simDeliverForgeClampSanTrackHalted
  change IsQueryBoundP _ (QAtomicShortDF Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind
    (isQueryBoundP_liftProb_zero_local (fun _ h => nomatch h) ($ᵗ (BitVec 256))) fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  refine CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_simulateQ_run_zero A
    (fun t ⟨⟨sC, ex⟩, tr⟩ => ?_) _
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
  · dsimp only [simDeliverForgeOracleSanTrackHalted, StateT.lift, StateT.run, StateT.mk]
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind
      ((isQueryBoundP_query_iff (QAtomicShortDF Pt ℓ) (.inl n) 0).2 fun h => nomatch h)
      fun u _ => isQueryBoundP_pure (QAtomicShortDF Pt ℓ) (u, ((sC, ex), tr)) 0
  · exact isQueryBoundP_semSendTrackHalted_atomicShort P hL K Dh encPt encT lam qep
      sC ex tr R m none r
  · exact isQueryBoundP_semSendTrackHalted_atomicShort P hL K Dh encPt encT lam qep
      sC ex tr R m₀ (some m₁) r
  · dsimp only [simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk]
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind
      (isQueryBoundP_semRecvHookS_local P Dh encPt encT decT lam T Kc qep B hDl hIj hDf
        sC ex R w true)
      fun ⟨rr, s'⟩ _ => isQueryBoundP_pure (QAtomicShortDF Pt ℓ) _ 0
  · dsimp only [simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk]
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind
      (isQueryBoundP_semRecvHookS_local P Dh encPt encT decT lam T Kc qep B hDl hIj hDf
        sC ex R w false)
      fun ⟨rr, s'⟩ _ => isQueryBoundP_pure (QAtomicShortDF Pt ℓ) _ 0
  · dsimp only [simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk]
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind
      (isQueryBoundP_semCorrHookTGB_local P Dh encT Bsk hCr sC ex R)
      fun ⟨rr, s'⟩ _ => isQueryBoundP_pure (QAtomicShortDF Pt ℓ) _ 0

private abbrev dfRespH (Pt : Type) (ℓ : ℕ) :=
  smDFRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (T := Pt)

private abbrev dfLongH (Pt : Type) (ℓ : ℕ) :=
  smDFRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
    (Coins := BitVec 256) (T := Pt)

private abbrev DFSafePostH (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (oa : AdversaryCompDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
      (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)))) : Prop :=
  GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ) (fun r => True ∧ SimShortInv r.2.1.base) oa

private theorem simShortInv_onAcceptPure_local {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
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

private theorem simShortInv_onAnswerPure_local {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (CryptoGames.SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (onAnswerPure qep Q w isDel ci? Tpk pq' res s).2 := by
  unfold onAnswerPure
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact simShortInv_onAcceptPure_local qep Q w isDel t i _ ci? Tpk pq' s hs

private theorem guardedSafePost_deliverQueryDF_local {Pt : Type} {ℓ : ℕ} (Q : Party)
    (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ) (fun _ => True)
      (deliverQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q c) := by
  unfold deliverQueryDF
  exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfRespH Pt ℓ) (Q := dfLongH Pt ℓ)
    (t := Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Q, c)))))) (fun h => h hc)

private theorem guardedSafePost_injectQueryDF_local {Pt : Type} {ℓ : ℕ} (Q : Party)
    (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ) (fun _ => True)
      (injectQueryDF
        (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := Fig8C Pt) Q c) := by
  unfold injectQueryDF
  exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfRespH Pt ℓ) (Q := dfLongH Pt ℓ)
    (t := Sum.inr (Sum.inl (Sum.inl (Sum.inr (Q, c))))) (fun h => h hc)

private theorem guardedSafePost_deliverForgeSemHook_onProbe_local {PQC Pt : Type} [DecidableEq Pt]
    [Zero Pt] [SampleableType PQC] {ℓ : ℕ} (Q : Party) (c' : Fig8C Pt)
    (hc' : c'.2.2.1.1.length < 2 ^ 32) (ex : List (Fig8C Pt)) :
    GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ) (fun _ => True)
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex) := by
  unfold deliverForgeSemHook
  dsimp only
  rcases ex.find? (fun c => sameWireFig8 c c') with _ | c
  · exact GuardedSafePost.pure trivial
  · have hq : GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ) (fun _ => True)
        (deliverForgeQuery
          (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
          (Coins := BitVec 256) (C := Fig8C Pt) Q c c') := by
      unfold deliverForgeQuery
      exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfRespH Pt ℓ) (Q := dfLongH Pt ℓ)
        (t := Sum.inr (Sum.inr (Q, c, c'))) (fun h => h hc')
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial

private theorem dfSafePost_semFwdAnswerHookS_local {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePostH PQ Pt ℓ
      (semFwdAnswerHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex Q w isDel ci? Tpk pq' c') := by
  unfold semFwdAnswerHookS deliverForgeSemHook
  dsimp only
  refine GuardedSafePost.bind (P := fun _ => True) ?_ fun ⟨res, ex₁⟩ _ =>
    GuardedSafePost.pure
      ⟨trivial, simShortInv_onAnswerPure_local qep Q w isDel ci? Tpk pq' res sC.base hs⟩
  split_ifs
  · exact (guardedSafePost_deliverQueryDF_local Q c' hc').bind fun _ _ =>
      GuardedSafePost.pure trivial
  · exact (guardedSafePost_injectQueryDF_local Q c' hc').bind fun _ _ =>
      GuardedSafePost.pure trivial

private theorem dfSafePost_semResyncHookS_local {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    DFSafePostH PQ Pt ℓ
      (semResyncHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex Q w ci? Tpk pq' c r) := by
  unfold semResyncHookS deliverForgeSemHook
  rcases r with _ | ⟨t, i, _, m'⟩
  · exact GuardedSafePost.pure ⟨trivial, hs⟩
  · dsimp only
    refine GuardedSafePost.bind (P := fun _ => True)
      ((guardedSafePost_deliverQueryDF_local Q c hc).bind fun _ _ => GuardedSafePost.pure trivial)
      fun ⟨res, ex₁⟩ _ => ?_
    rcases res with _ | (_ | _)
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure
        ⟨trivial, simShortInv_onAcceptPure_local qep Q w true t i m' ci? Tpk pq' sC.base hs⟩

private theorem dfSafePost_semFwdEvictHookS_local {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePostH PQ Pt ℓ
      (semFwdEvictHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC ex Q w isDel Tpk pq' c') := by
  unfold semFwdEvictHookS
  split_ifs
  · exact (guardedSafePost_deliverForgeSemHook_onProbe_local (PQC := PQC) Q c' hc' ex).bind
      fun _ _ => GuardedSafePost.pure ⟨trivial, hs⟩
  · exact dfSafePost_semFwdAnswerHookS_local P Dh encPt encT lam T qep sC ex hs Q w isDel none
      Tpk pq' c' hc'

private theorem dfSafePost_semFwdHookS_local {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T Kc qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt))
    (hhon : ∀ c, honestC = some c → c.2.2.1.1.length < 2 ^ 32)
    (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePostH PQ Pt ℓ
      (semFwdHookS P Dh encPt encT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep B sC ex Q w isDel ci? Tpk pq' honestC c') := by
  unfold semFwdHookS
  rcases honestC with _ | c
  · exact dfSafePost_semFwdAnswerHookS_local P Dh encPt encT lam T qep sC ex hs Q w isDel ci?
      Tpk pq' c' hc'
  · dsimp only
    split_ifs
    · rcases evalCKS P Dh encPt encT lam T Kc B sC Q w c c' with _ | r
      · exact (guardedSafePost_deliverForgeSemHook_onProbe_local (PQC := PQC) Q c' hc' ex).bind
          fun _ _ => GuardedSafePost.pure ⟨trivial, hs⟩
      · exact dfSafePost_semResyncHookS_local P Dh encPt encT lam T qep sC ex hs Q w ci? Tpk pq' c
          (hhon c rfl) r
    · exact dfSafePost_semFwdAnswerHookS_local P Dh encPt encT lam T qep sC ex hs Q w isDel ci?
        Tpk pq' c' hc'

private theorem simParseRecvC_ser_eq_local {PQ PQC Pt : Type} (P : Params PQ PQC)
    (decT : PublicKey → Option Pt) (B : ℕ) (qB : Bool) (pq : PQ) (w : Bytes)
    {pq' : PQ} {i : ℕ} {pk : PublicKey} {T? : Option Pt}
    {lct : ℕ × LibsignalCiphertextWithSalt32}
    (hp : simParseRecvC P decT B qB pq w = some (pq', (i, (pk, (T?, lct))))) :
    lct.2.1.1 = w.take (w.length - 8) := by
  unfold simParseRecvC at hp
  split_ifs at hp
  dsimp only [] at hp
  rcases hparse : (CryptoGames.LibsignalSession.signalWireCodec P.codec).parse
      (w.take (w.length - 8)) with _ | ⟨h, _⟩
  · rw [hparse] at hp; cases hp
  · rw [hparse] at hp; dsimp only [] at hp
    split_ifs at hp
    rcases hspqr : P.spqr.recv pq h.pqRatchet with _ | ⟨pq1, salt⟩
    · rw [hspqr] at hp; cases hp
    · rw [hspqr] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      exact congrArg (fun x : ℕ × LibsignalCiphertextWithSalt32 => x.2.1.1) hp.2.2.2.2.symm

private theorem dfSafePost_semRecvHookS_local {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (T Kc qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) :
    DFSafePostH PQ Pt ℓ
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
            rcases hparse : (CryptoGames.LibsignalSession.signalWireCodec P.codec).parse
                (w.take (w.length - 8)) with _ | ⟨h, _⟩
            · rw [hparse] at hp0; cases hp0
            · simp only [hparse, Bool.and_eq_true, decide_eq_true_eq] at hadm
              exact hadm.1
      have hlct : lct.2.1.1.length < 2 ^ 32 := by
        rw [simParseRecvC_ser_eq_local P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w hp,
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
                · exact dfSafePost_semFwdEvictHookS_local P Dh encPt encT lam T qep _ ex hsAmb
                    Q w isDel pk pq' _ hlct
                · exact dfSafePost_semFwdHookS_local P Dh encPt encT lam T Kc qep B _ ex hsAmb
                    Q w isDel none pk pq' _ hhon _ (hmkC _ _)
      · split
        · exact GuardedSafePost.pure ⟨trivial, hs⟩
        · exact dfSafePost_semFwdHookS_local P Dh encPt encT lam T Kc qep B sC ex hs
            Q w isDel (some ci) pk pq' _ hhon _ (hmkC _ _)
  · simp only [↓reduceIte]
    exact GuardedSafePost.pure ⟨trivial, hs⟩

private theorem dfSafePost_semCorrHookTGB_local {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (Bsk : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (hs : SimShortInv sC.base) (Q : Party) :
    DFSafePostH PQ Pt ℓ
      (semCorrHookTGB P Dh encT
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        Bsk sC ex Q) := by
  unfold semCorrHookTGB deliverForgeSemHook
  dsimp only
  split
  · exact GuardedSafePost.pure ⟨trivial, hs⟩
  · have hq : GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ) (fun _ => True)
        (corrQueryDF
          (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
          (Coins := BitVec 256) (C := Fig8C Pt) Q) := by
      unfold corrQueryDF
      exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfRespH Pt ℓ) (Q := dfLongH Pt ℓ)
        (t := Sum.inr (Sum.inl (Sum.inr Q))) not_false
    refine GuardedSafePost.bind (P := fun _ => True)
      (hq.bind fun _ _ => GuardedSafePost.pure trivial) fun ⟨res, ex₁⟩ _ => ?_
    rcases res with _ | _
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure ⟨trivial, hs.1, hs.2⟩

private theorem guardedSafePost_semSendTrackHalted
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (hs : SimShortInv sC.base)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ)
      (fun p => True ∧ SimShortInv p.2.1.1.base)
      (semSendTrackHalted P K Dh encPt encT lam qep sC ex tr Q m₀ chal r) := by
  unfold semSendTrackHalted
  split
  · exact GuardedSafePost.pure ⟨trivial, hs⟩
  · rcases hEp : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · dsimp only
      split
      · exact GuardedSafePost.pure ⟨trivial, hs⟩
      · have hrq : GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ) (fun _ => True)
            (match r with
            | some rq => pure rq
            | none => (liftM ($ᵗ (BitVec 512) : ProbComp (BitVec 512)) :
                AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
                  (BitVec 256) (Fig8C Pt) (BitVec 512))) := by
          rcases r with _ | rq
          · exact GuardedSafePost.liftComp_unif hQu_smDFRecvLong ($ᵗ BitVec 512)
          · exact GuardedSafePost.pure trivial
        refine hrq.bind fun rq _ => ?_
        split
        · exact GuardedSafePost.pure ⟨trivial, hs⟩
        · have hrc : GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ) (fun _ => True)
              (match r with
              | some _ => some <$> (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
                  AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
                    (BitVec 256) (Fig8C Pt) (BitVec 256))
              | none => pure none) := by
            rcases r with _ | _
            · exact GuardedSafePost.pure trivial
            · exact (GuardedSafePost.liftComp_unif hQu_smDFRecvLong ($ᵗ BitVec 256)).map
                (R := fun _ => True) some fun _ _ => trivial
          refine hrc.bind fun rc _ => ?_
          let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
            BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          rcases mkPub (P := P) sC.base Q rq pn with _ | ⟨pq', pub⟩
          · exact GuardedSafePost.pure ⟨trivial, hs⟩
          · dsimp only
            have htr₁ : s₁.trans = sC.base.mir.trans := epMgmt_trans_eq hEp
            rcases chal with _ | m₁
            · dsimp only
              have hq : GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ)
                  (fun res : Option (Fig8C Pt) => ∀ c, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
                  (transmitQueryDF (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
                    (Coins := BitVec 256) (C := Fig8C Pt) Q (pub, m₀) rc) := by
                unfold transmitQueryDF
                exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfRespH Pt ℓ)
                  (Q := dfLongH Pt ℓ)
                  (t := .inr (.inl (.inl (.inl (.inl (.inl (Q, (pub, m₀), rc))))))) not_false
              refine hq.bind fun res hres => ?_
              rcases res with _ | c
              · exact GuardedSafePost.pure ⟨trivial, hs⟩
              · have hrec := simShortInv_record hs htr₁ Q m₀ false pq' pn c (hres c rfl)
                exact GuardedSafePost.pure ⟨trivial, hrec.1, hrec.2⟩
            · dsimp only
              have hq : GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ)
                  (fun res : Option (Fig8C Pt) => ∀ c, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
                  (challQueryDF (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
                    (Coins := BitVec 256) (C := Fig8C Pt) Q (pub, m₀) (pub, m₁) rc) := by
                unfold challQueryDF
                exact GuardedSafePost.query (spec := DFSpec Pt ℓ) (RespOk := dfRespH Pt ℓ)
                  (Q := dfLongH Pt ℓ)
                  (t := .inr (.inl (.inl (.inl (.inl (.inr (Q, (pub, m₀), (pub, m₁), rc))))))) not_false
              refine hq.bind fun res hres => ?_
              rcases res with _ | c
              · exact GuardedSafePost.pure ⟨trivial, hs⟩
              · have hrec := simShortInv_record hs htr₁ Q m₀ true pq' pn c (hres c rfl)
                exact GuardedSafePost.pure ⟨trivial, hrec.1, hrec.2⟩

theorem simDeliverForgeClampSanTrackHalted_guardedSMDFShort
    {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    GuardedSMDFShort
      (simDeliverForgeClampSanTrackHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A) := by
  unfold GuardedSMDFShort simDeliverForgeClampSanTrackHalted
  refine (GuardedSafePost.liftComp_unif hQu_smDFRecvLong ($ᵗ BitVec 256)).bind fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ)
      (fun r => SimShortInv r.2.1.1.base)
      ((simulateQ (simDeliverForgeOracleSanTrackHalted P K Dh encPt encT decT lam qep B T Kc Bsk)
        A).run ((initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), []),
          initKemFailTrack P.C.F pqrKey)) := by
    refine GuardedSafePost.simulateQ_run
      (I := fun p : (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) ×
        KemFailTrackState P.C.F => SimShortInv p.1.1.base)
      (GuardedSafePost.true_of_false A) ?_ (simShortInv_initSim _ _)
    rintro (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) _ ⟨⟨sC, ex⟩, tr⟩ hs
    · show GuardedSafePost (dfRespH Pt ℓ) (dfLongH Pt ℓ)
        (fun p => True ∧ SimShortInv p.2.1.1.base)
        (query (spec := DFSpec Pt ℓ) (.inl n) >>= fun a => pure (a, ((sC, ex), tr)))
      exact (GuardedSafePost.query (hQu_smDFRecvLong n)).bind fun _ _ =>
        GuardedSafePost.pure ⟨trivial, hs⟩
    · exact guardedSafePost_semSendTrackHalted P K Dh encPt encT lam qep sC ex tr hs Q m none r
    · exact guardedSafePost_semSendTrackHalted P K Dh encPt encT lam qep sC ex tr hs Q m₀
        (some m₁) r
    · dsimp only [simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk]
      exact (dfSafePost_semRecvHookS_local P Dh encPt encT decT lam T Kc qep B sC ex hs
        Q w true).bind fun ⟨rr, s'⟩ ⟨_, hs'⟩ => GuardedSafePost.pure ⟨trivial, hs'⟩
    · dsimp only [simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk]
      exact (dfSafePost_semRecvHookS_local P Dh encPt encT decT lam T Kc qep B sC ex hs
        Q w false).bind fun ⟨rr, s'⟩ ⟨_, hs'⟩ => GuardedSafePost.pure ⟨trivial, hs'⟩
    · dsimp only [simDeliverForgeOracleSanTrackHalted, StateT.run, StateT.mk]
      exact (dfSafePost_semCorrHookTGB_local P Dh encT Bsk sC ex hs Q).bind
        fun ⟨rr, s'⟩ ⟨_, hs'⟩ => GuardedSafePost.pure ⟨trivial, hs'⟩
  exact hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeHaltedShort
