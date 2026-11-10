/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedSanGame -- proof-setup: allow-public-import
import Computational.Proofs.GameHop.CompDedup
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep

/-!
# Canonicalization and Step Alignment for Tracker-Halted Figure 8

Proves `simStateCCanon` projection equivalence from `simFig8OracleTGDedupHalted` to
`simFig8ClampTGHalted`, step-level `idHook` alignment with `simRecvC` and `simCorrC`, and
`TGInv` clamp preservation lemmas.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedTG

noncomputable section

open OracleComp OracleSpec
open CryptoGames (Party effectiveHkdfSalt32)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Params PublicKey IdentityKey GhostState signalWireCodec)
open CryptoGames.Ratchet.LibsignalInst
  (LibsignalMsgPublicPart lFS lFig8 ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C Fig8Comp GhostChain SimState initSim pushChain
   inReceiveOnlyEpoch mkPub toWire simParseRecvC
   onAccept onAnswer onAcceptPure onAnswerPure onAccept_run_eq_pure onAnswer_run_eq_pure
   fwd fwd_run_eq evalCKClamp evalCKClamp_eq_evalCK
   semFwdAnswerHook semResyncHook semFwdEvictHook semFwdHook semRecvHook
   simStateCanon simStateCCanon simStateCCanon_idem SimBaseClampInv)
open CryptoGames.Ratchet.LibsignalSimC
  (Kept LibsignalToModularSchemeSimState idHook guardC liftC runOnBaseState initSimC
   predictReceive sentEval kDecryptFig8
   predictReceiveWithSnapshots fwdAnswerC resyncC fwdEvictC fwdC simRecvC simCorrC)
open CryptoGames.SM
  (GameState RecvResult Record partyEnc partyDec partyDec_partyEnc
   noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10)
open CryptoVerification.LibsignalSpqrV1 (MlKem Bytes)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack stepKemFailSend stepKemFailDeliver)
open Computational.Proofs.GameHop.CompDedup
  (canonComp canonComp_epMgmt canonComp_record canonComp_corrAllowed
   canonComp_afterCorr canonComp_afterCorrDedup run'_simulateQ_eq_of_idem_proj)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
  (simSendCTrackHalted semSendHookHalted simFig8ClampSanHalted)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame
  (GameSanInv gameSanInv_init gameSanInv_corrImpl)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (Fig8G fig8GameImpl)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (fig8IdSemHook fig8StTruncSkOpt fig8StTruncSkOpt_eq_self semCorrHookTG semCorrHookTGDedup
   simFig8OracleTG simFig8OracleTGDedup
   semHandleHookDedup_simStateCCanon' semHandleHook_simStateCCanon')
open Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedSanGame
  (wrapHaltedOracle simFig8OracleTGDedupHalted simFig8OracleTGHalted
   simFig8ClampOfHalted simFig8ClampTGHalted
   simulateQ_fig8GameImpl_corrQuery modify_mem_inv
   sm_run_simFig8ClampSanHalted_eq_tgDedup)

section Hop2Canon

private theorem stateT_lift_run_id' {σ : Type} {M : Type → Type} [Monad M] {α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

private theorem mkPub_simStateCanon {PQ Pt : Type} {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (s : SimState PQ Pt ℓ) (Q : Party)
    (rq : BitVec 512) (pn : BitVec 32) :
    mkPub (P := P) (simStateCanon s) Q rq pn = mkPub (P := P) s Q rq pn := rfl

private theorem semSendHookHalted_simStateCCanon {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        semSendHookHalted P K Dh encPt encT lam qep (simStateCCanon sC, tr) Q m₀ chal r =
      Prod.map id (Prod.map simStateCCanon id) <$>
        semSendHookHalted P K Dh encPt encT lam qep (sC, tr) Q m₀ chal r := by
  unfold semSendHookHalted simSendCTrackHalted
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only [simStateCCanon]
  by_cases href : (sC.base.stopped || sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q) = true
  · have href' : ((simStateCanon sC.base).stopped || (simStateCanon sC.base).mir.win ||
        !noBobSendInEpoch0 (simStateCanon sC.base).mir Q) = true := href
    simp only [href, href', ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    congr 2; exact Prod.ext (simStateCCanon_idem sC) rfl
  · have href' : ¬ ((simStateCanon sC.base).stopped || (simStateCanon sC.base).mir.win ||
        !noBobSendInEpoch0 (simStateCanon sC.base).mir Q) = true := href
    simp only [href, href', Bool.false_eq_true, ↓reduceIte]
    have hep_c : (simStateCanon sC.base).mir.epMgmt 3 qep Q r.isSome =
        Option.map canonComp (sC.base.mir.epMgmt 3 qep Q r.isSome) :=
      (canonComp_epMgmt sC.base.mir 3 qep Q r.isSome).symm
    rw [hep_c]
    rcases hepR : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | sR
    · simp only [Option.map_none, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
      congr 2; exact Prod.ext (simStateCCanon_idem sC) rfl
    · simp only [Option.map_some]
      have hsafe_eq : (canonComp sR).safeCh 3 Q = sR.safeCh 3 Q := rfl
      rw [hsafe_eq]
      by_cases hch : (chal.isSome && !sR.safeCh 3 Q) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
        congr 2; exact Prod.ext (simStateCCanon_idem sC) rfl
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run_id',
          bind_assoc, pure_bind, map_bind]
        refine bind_congr fun rq => ?_
        by_cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome = true
        · simp only [hcand, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, map_pure, Prod.map_apply, id_eq]
          congr 2; exact Prod.ext (simStateCCanon_idem sC) rfl
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run_id',
            bind_assoc, pure_bind, map_bind]
          refine bind_congr fun rc => ?_
          simp only [mkPub_simStateCanon,
            show (canonComp sR).epoch = sR.epoch from rfl,
            show (canonComp sR).idx = sR.idx from rfl,
            show (simStateCanon sC.base).mir.epoch = sC.base.mir.epoch from rfl,
            show (simStateCanon sC.base).mir.idx = sC.base.mir.idx from rfl,
            show (simStateCanon sC.base).pn = sC.base.pn from rfl]
          rcases mkPub (P := P) sC.base Q rq
              (if sR.epoch Q ≠ sC.base.mir.epoch Q then
                BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
              else sC.base.pn Q) with _ | ⟨pq', pub⟩
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              map_pure, Prod.map_apply, id_eq]
            congr 2; exact Prod.ext (simStateCCanon_idem sC) rfl
          · simp only [StateT.run_bind, stateT_lift_run_id', bind_assoc, pure_bind, map_bind]
            refine bind_congr fun res => ?_
            rcases res with _ | c
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
                Prod.map_apply, id_eq]
              congr 2; exact Prod.ext (simStateCCanon_idem sC) rfl
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, map_pure,
                Prod.map_apply, id_eq]
              congr 2
              refine Prod.ext ?_ rfl
              have hmir_c :
                  canonComp ((canonComp sR).record 3 Q ()
                    ⟨⟨Q, sR.epoch Q, sR.idx Q + 1⟩, m₀, toWire c⟩
                    chal.isSome) =
                  canonComp (sR.record 3 Q ()
                    ⟨⟨Q, sR.epoch Q, sR.idx Q + 1⟩, m₀, toWire c⟩
                    chal.isSome) :=
                (canonComp_record sR 3 Q ()
                  ⟨⟨Q, sR.epoch Q, sR.idx Q + 1⟩, m₀, toWire c⟩ chal.isSome).symm
              unfold simStateCCanon simStateCanon
              dsimp only
              rw [hmir_c]

private theorem semCorrHookTGDedup_simStateCCanon {PQ Pt : Type} {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    Prod.map id simStateCCanon <$>
        semCorrHookTGDedup (PQC := BitVec 512) P Dh encT B_skip? sC Q =
      Prod.map id simStateCCanon <$>
        semCorrHookTG (PQC := BitVec 512) P Dh encT B_skip? (simStateCCanon sC) Q := by
  unfold semCorrHookTGDedup semCorrHookTG
  have hca : (simStateCCanon sC).base.mir.corrAllowed Q = sC.base.mir.corrAllowed Q :=
    canonComp_corrAllowed sC.base.mir Q
  have hcond :
      ((simStateCCanon sC).base.stopped || (simStateCCanon sC).base.mir.win ||
       !(simStateCCanon sC).base.mir.corrAllowed Q ||
       inReceiveOnlyEpoch (simStateCCanon sC).base.mir Q ||
       !noAliceCorrWhileAliceBelowEpoch10 (simStateCCanon sC).base.mir Q) =
      (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
       inReceiveOnlyEpoch sC.base.mir Q ||
       !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) := by
    rw [hca]; rfl
  rw [hcond]
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
       inReceiveOnlyEpoch sC.base.mir Q ||
       !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · simp [hc, Prod.map, simStateCCanon_idem]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | fig8st
    · simp [Prod.map, simStateCCanon_idem]
    · simp only [map_pure, Prod.map, id_eq,
        show (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch from rfl,
        show (simStateCCanon sC).base.chains = sC.base.chains from rfl,
        show (simStateCCanon sC).kept = sC.kept from rfl,
        show (simStateCCanon sC).sent = sC.sent from rfl,
        show (simStateCCanon sC).snaps = sC.snaps from rfl]
      have htg : ∀ cs st₀, CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
          { (simStateCCanon sC).base with chains := cs } Q st₀ =
          CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
            { sC.base with chains := cs } Q st₀ := fun _ _ => rfl
      simp only [htg]
      congr 1
      refine Prod.ext rfl ?_
      simp only [simStateCCanon, simStateCanon]
      congr 2
      exact canonComp_afterCorrDedup sC.base.mir Q

private theorem semCorrHookTG_simStateCCanon {PQ Pt : Type} {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (B_skip? : Option ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    Prod.map id simStateCCanon <$>
        semCorrHookTG (PQC := BitVec 512) P Dh encT B_skip? sC Q =
      Prod.map id simStateCCanon <$>
        semCorrHookTG (PQC := BitVec 512) P Dh encT B_skip? (simStateCCanon sC) Q := by
  unfold semCorrHookTG
  have hca : (simStateCCanon sC).base.mir.corrAllowed Q = sC.base.mir.corrAllowed Q :=
    canonComp_corrAllowed sC.base.mir Q
  have hcond :
      ((simStateCCanon sC).base.stopped || (simStateCCanon sC).base.mir.win ||
       !(simStateCCanon sC).base.mir.corrAllowed Q ||
       inReceiveOnlyEpoch (simStateCCanon sC).base.mir Q ||
       !noAliceCorrWhileAliceBelowEpoch10 (simStateCCanon sC).base.mir Q) =
      (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
       inReceiveOnlyEpoch sC.base.mir Q ||
       !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) := by
    rw [hca]; rfl
  rw [hcond]
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
       inReceiveOnlyEpoch sC.base.mir Q ||
       !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · simp [hc, Prod.map, simStateCCanon_idem]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, map_bind]
    refine bind_congr fun res => ?_
    rcases res with _ | fig8st
    · simp [Prod.map, simStateCCanon_idem]
    · simp only [map_pure, Prod.map, id_eq,
        show (simStateCCanon sC).base.mir.epoch = sC.base.mir.epoch from rfl,
        show (simStateCCanon sC).base.chains = sC.base.chains from rfl,
        show (simStateCCanon sC).kept = sC.kept from rfl,
        show (simStateCCanon sC).sent = sC.sent from rfl,
        show (simStateCCanon sC).snaps = sC.snaps from rfl]
      have htg : ∀ cs st₀, CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
          { (simStateCCanon sC).base with chains := cs } Q st₀ =
          CryptoGames.Ratchet.LibsignalSim.toGhost (P := P)
            { sC.base with chains := cs } Q st₀ := fun _ _ => rfl
      simp only [htg]
      congr 1
      refine Prod.ext rfl ?_
      simp only [simStateCCanon, simStateCanon]
      congr 2
      exact canonComp_afterCorr sC.base.mir Q

private theorem wrapHaltedOracle_simStateCCanon {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (base₁ base₂ : QueryImpl
      (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ)))
    (hbase : ∀ t sC,
      Prod.map id simStateCCanon <$> (base₁ t).run sC =
        Prod.map id simStateCCanon <$> (base₂ t).run (simStateCCanon sC))
    (q : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) :
    Prod.map id (Prod.map simStateCCanon id) <$>
        (wrapHaltedOracle P K Dh encPt encT lam qep base₁ q).run s =
      Prod.map id (Prod.map simStateCCanon id) <$>
        (wrapHaltedOracle P K Dh encPt encT lam qep base₂ q).run
          (Prod.map simStateCCanon id s) := by
  rcases s with ⟨sC, tr⟩
  have hlift : ∀ {α : Type} (m₁ m₂ : Fig8Comp Pt ℓ
      (α × LibsignalToModularSchemeSimState PQ Pt ℓ)),
      Prod.map id simStateCCanon <$> m₁ = Prod.map id simStateCCanon <$> m₂ →
      Prod.map id (Prod.map simStateCCanon id) <$> ((fun (a, sC') => (a, (sC', tr))) <$> m₁) =
        Prod.map id (Prod.map simStateCCanon id) <$> ((fun (a, sC') => (a, (sC', tr))) <$> m₂) := by
    intro α m₁ m₂ hm
    have hc : ∀ (m : Fig8Comp Pt ℓ (α × LibsignalToModularSchemeSimState PQ Pt ℓ)),
        Prod.map id (Prod.map simStateCCanon id) <$> ((fun (a, sC') => (a, (sC', tr))) <$> m) =
          (fun (a, sC') => (a, (sC', tr))) <$> (Prod.map id simStateCCanon <$> m) := by
      intro m; simp only [Functor.map_map]; rfl
    rw [hc, hc, hm]
  rcases q with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · dsimp only [wrapHaltedOracle, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, StateT.run,
      StateT.mk, Prod.map_apply, id_eq]
    exact hlift _ _ (hbase (.inl n) sC)
  · exact (semSendHookHalted_simStateCCanon P K Dh encPt encT lam qep sC tr Q m₀ none r).symm
  · exact (semSendHookHalted_simStateCCanon P K Dh encPt encT lam qep sC tr Q m₀ (some m₁) r).symm
  · dsimp only [wrapHaltedOracle, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr,
      StateT.run, StateT.mk, Prod.map_apply, id_eq]
    have hhon : (simStateCCanon sC).base.honest = sC.base.honest := rfl
    rw [hhon]
    set j? := sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == (w : List (BitVec 8)) && Party.senderOf wc.2.1.1 == Q.other)
    let k : Option (RecvResult (Plain ℓ)) → KemFailTrackState P.C.F := fun res =>
      match res, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    have hdel : ∀ (m₁ m₂ : Fig8Comp Pt ℓ
          (Option (RecvResult (Plain ℓ)) × LibsignalToModularSchemeSimState PQ Pt ℓ)),
        Prod.map id simStateCCanon <$> m₁ = Prod.map id simStateCCanon <$> m₂ →
        Prod.map id (Prod.map simStateCCanon id) <$>
          (m₁ >>= fun x => pure (x.1, (x.2, k x.1))) =
        Prod.map id (Prod.map simStateCCanon id) <$>
          (m₂ >>= fun x => pure (x.1, (x.2, k x.1))) := by
      intro m₁ m₂ hm
      have hc : ∀ (m : Fig8Comp Pt ℓ
          (Option (RecvResult (Plain ℓ)) × LibsignalToModularSchemeSimState PQ Pt ℓ)),
          Prod.map id (Prod.map simStateCCanon id) <$>
            (m >>= fun x => pure (x.1, (x.2, k x.1))) =
          (fun x => (x.1, (x.2, k x.1))) <$> (Prod.map id simStateCCanon <$> m) := by
        intro m
        rw [map_bind, Functor.map_map, map_eq_bind_pure_comp]
        refine bind_congr fun ⟨res, sC'⟩ => ?_
        simp [Function.comp, Prod.map]
      rw [hc, hc, hm]
    refine Eq.trans ?_
      (Eq.trans (hdel _ _ (hbase (.inr (.inl (.inl (.inr (Q, w))))) sC)) ?_)
    · congr 1
      refine bind_congr fun ⟨res, sC'⟩ => ?_
      rcases res with _ | r
      · rcases j? with _ | j <;> rfl
      · cases r <;> rcases j? with _ | j <;> rfl
    · congr 1
      refine bind_congr fun ⟨res, sC'⟩ => ?_
      rcases res with _ | r
      · rcases j? with _ | j <;> rfl
      · cases r <;> rcases j? with _ | j <;> rfl
  · dsimp only [wrapHaltedOracle, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr,
      StateT.run, StateT.mk, Prod.map_apply, id_eq]
    exact hlift _ _ (hbase (.inr (.inl (.inr (Q, w)))) sC)
  · dsimp only [wrapHaltedOracle, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inr,
      StateT.run, StateT.mk, Prod.map_apply, id_eq]
    exact hlift _ _ (hbase (.inr (.inr Q)) sC)

private theorem simFig8ClampOfHalted_tgDedup_eq_tg {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    simFig8ClampOfHalted P
      (simFig8OracleTGDedupHalted P K Dh encPt encT decT lam qep B B_skip?) A =
    simFig8ClampTGHalted P K ℓ Dh encPt encT decT lam qep B B_skip? A := by
  unfold simFig8ClampTGHalted simFig8ClampOfHalted
  have hcomm : ∀ {t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain}
      (oa : Fig8Comp Pt ℓ
        ((CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Range t ×
          (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit))),
      Prod.map id simStateCCanon <$> (Prod.map id Prod.fst <$> oa) =
        Prod.map id Prod.fst <$> (Prod.map id (Prod.map simStateCCanon id) <$> oa) := by
    intro _ oa; simp [Functor.map_map, Prod.map]
  refine bind_congr fun pqrKey => ?_
  refine run'_simulateQ_eq_of_idem_proj
    (simFig8OracleTGDedupHalted P K Dh encPt encT decT lam qep B B_skip?)
    (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B B_skip?)
    (Prod.map (simStateCCanon (PQ := PQ) (Pt := Pt) (ℓ := ℓ))
      (id : KemFailTrackState P.C.F → KemFailTrackState P.C.F))
    ?_ ?_ A rfl
  · intro q s
    exact wrapHaltedOracle_simStateCCanon P K Dh encPt encT lam qep _ _
      (fun t sC₀ => by
        rcases t with n | (t₀ | Q)
        · simp [simFig8OracleTGDedup, simFig8OracleTG, StateT.run_lift, Prod.map,
            simStateCCanon_idem]
        · dsimp only [simFig8OracleTGDedup, simFig8OracleTG, StateT.run, StateT.mk]
          exact (hcomm _).trans ((congrArg (Functor.map (Prod.map id Prod.fst))
            (semHandleHookDedup_simStateCCanon' P Dh encPt encT decT lam
              (fig8IdSemHook (PQC := BitVec 512) none) qep B (.inl t₀) sC₀ ())).trans
            (hcomm _).symm)
        · exact semCorrHookTGDedup_simStateCCanon P Dh encT B_skip? sC₀ Q) q s
  · intro q s
    exact wrapHaltedOracle_simStateCCanon P K Dh encPt encT lam qep _ _
      (fun t sC₀ => by
        rcases t with n | (t₀ | Q)
        · simp [simFig8OracleTG, StateT.run_lift, Prod.map, simStateCCanon_idem]
        · dsimp only [simFig8OracleTG, StateT.run, StateT.mk]
          exact (hcomm _).trans ((congrArg (Functor.map (Prod.map id Prod.fst))
            (semHandleHook_simStateCCanon' P Dh encPt encT decT lam
              (fig8IdSemHook (PQC := BitVec 512) none) qep B (.inl t₀) sC₀ ())).trans
            (hcomm _).symm)
        · exact semCorrHookTG_simStateCCanon P Dh encT B_skip? sC₀ Q) q s

theorem sm_run_simFig8ClampSanHalted_eq_tgHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q ≤ Kc) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampSanHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampTGHalted P K ℓ Dh encPt encT decT lam qep B (some Bsk) A) := by
  intro fig
  rw [sm_run_simFig8ClampSanHalted_eq_tgDedup P K Dh encPt encT decT lam qep B T Kc Bsk cfg b
    hq hT hKc, simFig8ClampOfHalted_tgDedup_eq_tg]

end Hop2Canon

section Hop3IdHook

private def runIdM {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Fig8Comp Pt ℓ (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit)) := do
  let (a, sC') ← x.run sC
  return (a, (sC', ()))

private theorem map_fst_runIdM {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Prod.map id Prod.fst <$> runIdM x sC = x.run sC := by
  unfold runIdM
  rw [map_bind]
  conv_rhs => rw [← bind_pure (x.run sC)]
  refine bind_congr fun ⟨a, sC'⟩ => ?_
  simp [Prod.map]

private theorem runIdM_pure {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (a : α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    runIdM (pure a) sC = pure (a, (sC, ())) := rfl

private theorem runIdM_guardC_neg {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (h : ¬ sC.base.stopped = true) :
    runIdM (guardC x) sC = runIdM x sC := by
  unfold runIdM guardC; simp [h]

private theorem runIdM_get_bind {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ →
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    runIdM (get >>= f) sC = runIdM (f sC) sC := rfl

private theorem runIdM_ite_modify {PQ Pt : Type} {ℓ : ℕ} {α : Type} (c : Bool)
    (k : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    runIdM (if c then
        (modify (fun sC : LibsignalToModularSchemeSimState PQ Pt ℓ =>
          { sC with base := { sC.base with amb := sC.base.amb + 1 } }) >>= fun _ => k)
      else k) sC =
      runIdM k
        { sC with base := if c then { sC.base with amb := sC.base.amb + 1 } else sC.base } := by
  cases c <;> rfl

private theorem stateT_lift_run_id {σ : Type} {M : Type → Type} [Monad M] {α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

private theorem runOnBaseState_idHook_run {PQ Pt α : Type} {ℓ : ℕ}
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (runOnBaseState (H := idHook) x).run sC =
      (x.run sC.base >>= fun (a, s') => pure (a, { sC with base := s' })) := rfl

private theorem liftC_idHook_run {PQ Pt α : Type} {ℓ : ℕ}
    (x : Fig8Comp Pt ℓ α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (liftC (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (H := idHook) x).run sC =
      (x >>= fun a => pure (a, sC)) := rfl

private theorem semFwdAnswerHook_idHook_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    semFwdAnswerHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
        qep sC () Q w isDel ci? Tpk pq' c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (fwdAnswerC (qep := qep) (fig := fig) (fs := fs) (H := idHook)
        Q w isDel ci? Tpk pq' c') sC := by
  unfold semFwdAnswerHook runIdM fwdAnswerC
  simp only [StateT.run_bind, runOnBaseState_idHook_run, fwd_run_eq, bind_assoc]
  split_ifs <;>
    simp only [fig8IdSemHook, pure_bind, bind_assoc] <;>
    (refine bind_congr fun res => ?_;
     rcases res with _ | (_ | ⟨t, i, pm⟩) <;>
       simp [runOnBaseState_idHook_run, onAnswer_run_eq_pure])

private theorem semResyncHook_idHook_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    semResyncHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
        qep sC () Q w ci? Tpk pq' c r =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (resyncC (qep := qep) (fig := fig) (fs := fs) (H := idHook)
        Q w ci? Tpk pq' c r) sC := by
  unfold semResyncHook runIdM resyncC
  rcases r with _ | ⟨t, i, ⟨pub, m'⟩⟩
  · simp
  · simp only [fig8IdSemHook, StateT.run_bind, liftC_idHook_run, pure_bind, bind_assoc]
    refine bind_congr fun res => ?_
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp [runOnBaseState_idHook_run, onAccept_run_eq_pure]

private theorem semFwdEvictHook_idHook_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    semFwdEvictHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
        qep sC () Q w isDel Tpk pq' c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (fwdEvictC (qep := qep) (fig := fig) (fs := fs) (H := idHook)
        Q w isDel Tpk pq' c') sC := by
  unfold semFwdEvictHook fwdEvictC
  by_cases h : (isDel && !sC.base.mir.safeInj 3) = true
  · dsimp only [idHook, fig8IdSemHook]
    simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte,
      stateT_lift_run_id, StateT.run_pure]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [semFwdAnswerHook_idHook_eq]
    simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, Bool.false_eq_true,
      ↓reduceIte]

private theorem semFwdHook_idHook_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (hc' : ∀ c, honestC = some c → c ≠ c' → c'.1.1 ≤ B ∧ c'.2.1 ≤ B) :
    semFwdHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
        qep B sC () Q w isDel ci? Tpk pq' honestC c' =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := idHook)
        Q w isDel ci? Tpk pq' honestC c') sC := by
  unfold semFwdHook fwdC
  rcases honestC with _ | c
  · dsimp only
    rw [semFwdAnswerHook_idHook_eq]
    simp [runIdM]
  · dsimp only
    have hcond : (!(decide (c = c')) && (isDel && !sC.base.mir.safeInj 3)) =
        (decide (c ≠ c') && isDel && !sC.base.mir.safeInj 3) := by
      rw [decide_not, Bool.and_assoc]
    rw [hcond]
    by_cases h : (decide (c ≠ c') && isDel && !sC.base.mir.safeInj 3) = true
    · have hne : c ≠ c' := of_decide_eq_true (by revert h; cases decide (c ≠ c') <;> simp)
      obtain ⟨ht, hi⟩ := hc' c rfl hne
      simp only [h, ↓reduceIte, evalCKClamp_eq_evalCK P Dh encPt encT lam B sC Q w c c' ht hi]
      rcases heval : predictReceiveWithSnapshots
          (fig := lFig8 Dh encPt P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
          (fs := lFS P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000)
          P sC Q w c c' with _ | r
      · dsimp only [idHook, fig8IdSemHook]
        simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte, heval,
          stateT_lift_run_id, StateT.run_pure]
      · dsimp only
        rw [semResyncHook_idHook_eq]
        simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, ↓reduceIte, heval]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [semFwdAnswerHook_idHook_eq]
      simp only [runIdM, StateT.run_bind, StateT.run_get, pure_bind, h, Bool.false_eq_true,
        ↓reduceIte]

private theorem getD_chains_epoch_le (cs : List GhostChain) (ci B : ℕ)
    (hch : ∀ g ∈ cs, g.epoch ≤ B) :
    (cs.getD ci ⟨none, 0, 0, []⟩).epoch ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : cs[ci]? with _ | g
  · exact Nat.zero_le B
  · exact hch g (List.mem_of_getElem? h)

private theorem semRecvHook_idHook_runIdM {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (h232 : 2 ^ 32 ≤ B)
    (hep : sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ g ∈ sC.base.chains Q, g.epoch ≤ B) :
    semRecvHook P Dh encPt encT decT lam
        (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
        qep B sC () Q w isDel =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      runIdM (guardC (simRecvC (P := P) (encT := encT) (decT := decT)
        (qep := qep) (fig := fig) (fs := fs) (H := idHook) Q w isDel)) sC := by
  dsimp only
  by_cases hstop : sC.base.stopped = true
  · unfold semRecvHook runIdM guardC; simp [hstop]
  · rw [runIdM_guardC_neg _ sC hstop]
    unfold semRecvHook simRecvC
    have hcond : (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !sC.base.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w))) =
      (sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !sC.base.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w))) := by
      simp [hstop]
    rw [hcond, runIdM_get_bind]
    by_cases hwin : sC.base.mir.win = true
    · simp [hwin, runIdM_pure]
    · simp only [hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hdel : (isDel && (sC.base.mir.inTransit Q.other w).isNone) = true
      · simp [hdel, runIdM_pure]
      · simp only [hdel, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        by_cases hinj : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
            !sC.base.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w)) = true
        · simp [hinj, runIdM_pure]
        · simp only [hinj, Bool.false_eq_true, ↓reduceIte]
          unfold simParseRecvC
          rw [partyDec_partyEnc]
          by_cases hlen : w.length < 9
          · simp [hlen, runIdM_pure]
          · simp only [hlen, ↓reduceIte]
            rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
              _ | ⟨h, rest⟩
            · simp [runIdM_pure]
            · cases haddr : CryptoGames.LibsignalAead.addressCheckPasses h.addresses
                (P.expectedAddrs Q)
              · simp [haddr, runIdM_pure]
              · cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet
                · dsimp only
                  simp only [haddr, hpan, Bool.not_true, Bool.false_or, Bool.false_eq_true,
                    ↓reduceIte]
                  rcases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with _ | ⟨pq', salt⟩
                  · simp [runIdM_pure]
                  · have hlt : h.counter.toNat < 2 ^ 32 := h.counter.isLt
                    have hmin : min (h.counter.toNat + 1) (2 ^ 32) = h.counter.toNat + 1 :=
                      Nat.min_eq_left (by omega)
                    dsimp only
                    simp only [hmin]
                    rcases hfind : (sC.base.chains Q).findIdx?
                        (fun g => g.key == some h.senderRatchetKey) with _ | ci <;>
                      simp only [hfind]
                    · by_cases hev : (((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                            (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
                        ((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                            (fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) ==
                              some true) = true
                      · simp only [hev, ↓reduceIte, runIdM_pure]
                      · simp only [hev, Bool.false_eq_true, ↓reduceIte]
                        by_cases hT0 : (decT h.senderRatchetKey == some 0) = true
                        · simp [hT0, runIdM_pure]
                        · simp only [hT0, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel,
                            runIdM_ite_modify]
                          by_cases hexit : (inReceiveOnlyEpoch sC.base.mir Q ||
                              decide (25000 < h.counter.toNat) ||
                              decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                          · simp only [hexit, ↓reduceIte, runIdM_pure]
                          · simp only [hexit, Bool.false_eq_true, ↓reduceIte]
                            rcases hT : decT h.senderRatchetKey with _ | T
                            · simp only [runIdM_pure]
                            · dsimp only
                              by_cases hev1 : (((sC.base.honest.find? fun wc =>
                                  wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                                    (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
                                      some true) = true
                              · simp only [hev1, ↓reduceIte]
                                rw [semFwdEvictHook_idHook_eq]
                              · simp only [hev1, Bool.false_eq_true, ↓reduceIte]
                                rw [semFwdHook_idHook_eq P Dh encPt encT lam qep B]
                                · rfl
                                · intro c hc hne; rw [hc] at hne ⊢
                                  by_cases hs : c.2.2.2 = effectiveHkdfSalt32 salt
                                  · simp [hs] at hne
                                  · simp only [hs, ↓reduceIte]; exact ⟨hep, by omega⟩
                    · by_cases hrej :
                          ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects
                            (h.counter.toNat + 1) = true
                      · simp only [hrej, ↓reduceIte, runIdM_pure]
                      · simp only [hrej, Bool.false_eq_true, ↓reduceIte]
                        have hgep : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch ≤ B :=
                          getD_chains_epoch_le (sC.base.chains Q) ci B hch
                        rw [semFwdHook_idHook_eq P Dh encPt encT lam qep B]
                        · rfl
                        · intro c hc hne
                          rw [hc] at hne ⊢
                          by_cases hs : c.2.2.2 = effectiveHkdfSalt32 salt
                          · simp [hs] at hne
                          · simp only [hs, ↓reduceIte]; exact ⟨hgep, by omega⟩
                · simp [haddr, hpan, runIdM_pure]

theorem semRecvHook_idHook_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (h232 : 2 ^ 32 ≤ B)
    (hep : sC.base.mir.epoch Q + 1 ≤ B)
    (hch : ∀ g ∈ sC.base.chains Q, g.epoch ≤ B)
    (_hhon : ∀ wc ∈ sC.base.honest, wc.2.1.1 ≤ B ∧ wc.2.2.1 ≤ B) :
    Prod.map id Prod.fst <$>
        semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep B sC () Q w isDel =
      let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      (guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := idHook) Q w isDel)).run sC := by
  dsimp only
  rw [semRecvHook_idHook_runIdM P Dh encPt encT decT lam qep B sC Q w isDel h232 hep hch]
  exact map_fst_runIdM _ sC

theorem semCorrHookTG_simImpl_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep Bsk : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (gs : Fig8G Pt ℓ) (Q : Party)
    (hBsk : 25000 * q ≤ Bsk) (hg : GameSanInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    (simulateQ (fig8GameImpl fig qep cfg)
      ((fun (a, sC') => (a, (sC', tr))) <$>
        semCorrHookTG (PQC := BitVec 512) P Dh encT (some Bsk) sC Q)).run gs =
    (simulateQ (fig8GameImpl fig qep cfg)
      ((fun (a, sC') => (a, (sC', tr))) <$>
        (guardC (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q)).run sC)).run gs := by
  intro fig
  have hm1 : m + 1 ≤ q := hg.hm
  by_cases hstop : sC.base.stopped = true
  · unfold semCorrHookTG guardC; simp [hstop]
  · have hguard : (guardC (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q)).run sC =
        (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q).run sC := by
      unfold guardC; simp [hstop]
    rw [hguard]
    unfold semCorrHookTG simCorrC
    simp only [hstop, Bool.false_or, StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
         inReceiveOnlyEpoch sC.base.mir Q ||
         !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
    · simp only [href, ↓reduceIte, StateT.run_pure, map_pure, simulateQ_pure]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, liftC_idHook_run, bind_assoc, pure_bind,
        map_bind, simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_corrQuery]
      refine bind_congr_of_forall_mem_support _ fun ⟨res, gs'⟩ hcr => ?_
      obtain ⟨_, hst_eq⟩ := gameSanInv_corrImpl hg hcr
      rcases res with _ | fig8st
      · simp
      · have hst0 := hst_eq fig8st rfl
        have htrunc : fig8StTruncSkOpt (some Bsk) fig8st = fig8st := by
          refine fig8StTruncSkOpt_eq_self (some Bsk) fig8st fun Bs hBs t₀ v hv => ?_
          injection hBs with rfl
          rw [hst0] at hv
          have hv_le : v.skippedKeys.length ≤ _ := (hg.hparty Q).2 t₀ v hv
          omega
        dsimp only [Option.map]
        simp only [htrunc, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          map_pure, simulateQ_pure]
        cases fig8st.γ <;> rfl

end Hop3IdHook

section TGInvHelpers

structure TGInv {PQ Pt : Type} {ℓ : ℕ} (q B m : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) : Prop where
  hgame : GameSanInv q m gs
  htcur : ∀ R : Party, (gs.st R).tcur + m + 1 ≤ B
  hbase : SimBaseClampInv B m sC.base

private theorem simBaseClampInv_mono {PQ Pt : Type} {ℓ B m₁ m₂ : ℕ}
    {s : SimState PQ Pt ℓ} (hle : m₁ ≤ m₂) (h : SimBaseClampInv B m₂ s) :
    SimBaseClampInv B m₁ s where
  hep R := by have := h.hep R; omega
  htrans r hr := by have := h.htrans r hr; omega
  hch R g hg := by have := h.hch R g hg; omega
  hhonest wc hwc := by have := h.hhonest wc hwc; exact ⟨by omega, by omega⟩

theorem TGInv.mono {PQ Pt : Type} {ℓ q B m₁ m₂ : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {gs : Fig8G Pt ℓ}
    (h : TGInv q B m₂ sC gs) (hle : m₁ ≤ m₂) : TGInv q B m₁ sC gs where
  hgame := h.hgame.mono hle
  htcur R := by have := h.htcur R; omega
  hbase := simBaseClampInv_mono hle h.hbase

theorem tgInv_init {PQ Pt : Type} [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (q B : ℕ) (hqB : q + 2 ≤ B)
    (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256) (b : Bool) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    TGInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ) q B q
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (CryptoGames.SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b) where
  hgame := gameSanInv_init Dh encPt P.C P.codec encT
    (fun R => if R == Party.A then P.idA else P.idB) lam q k b
  htcur R := by
    have ht0 : ((CryptoGames.SM.initState
        (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam) k b).st R).tcur = 0 := by
      cases R <;> rfl
    rw [ht0]; omega
  hbase := {
    hep := fun R => by dsimp [initSimC, initSim]; omega
    htrans := fun _ hr => nomatch hr
    hch := fun R g hg => by
      cases R <;> simp [initSimC, initSim] at hg
      subst hg; dsimp; omega
    hhonest := fun _ hwc => nomatch hwc
  }

theorem epMgmt_bounds_local {St Msg C : Type}
    {s s₁ : GameState St Msg C} {Δ qep : ℕ} {Q : Party} {bad : Bool}
    (h : s.epMgmt Δ qep Q bad = some s₁) :
    (∀ R : Party, s₁.epoch R ≤ s.epoch R + 1) ∧ s₁.trans = s.trans ∧ s₁.st = s.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> injection h with h <;> subst h
  · refine ⟨fun R => ?_, rfl, rfl⟩; by_cases hR : R = Q <;> simp [hR, GameState.leak]
  · refine ⟨fun R => ?_, rfl, rfl⟩; by_cases hR : R = Q <;> simp [hR]
  · exact ⟨fun _ => Nat.le_add_right _ 1, rfl, rfl⟩

private theorem lFig8_send_tcur_epoch {PQ Pt : Type} [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (st : Fig8St Pt) (msg : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (fig.send st msg coins).1.tcur ≤ st.tcur + 1 ∧
      (fig.send st msg coins).2.1.1 ≤ st.tcur + 1 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.send]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp [hs]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases st.vS <;> exact ⟨Nat.le_add_right _ 1, Nat.le_add_right _ 1⟩

private theorem lFig8_receive_tcur_epoch {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (st st' : Fig8St Pt) (c : Fig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c = some (st', t, i, pm)) :
    t = c.1.1 ∧ t ≤ st.tcur + 1 ∧ st'.tcur ≤ st.tcur + 1 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.receive] at h
  split at h
  · cases h
  · rename_i h1
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h1
    split at h
    · cases h
    · rename_i s₁ hs₁
      have hs₁_le : s₁.tcur ≤ st.tcur + 1 := by
        split_ifs at hs₁
        · rcases hc12 : c.1.2 with _ | Tn <;> rw [hc12] at hs₁
          · cases hs₁
          · injection hs₁ with hs₁; subst hs₁; exact h1.2
        · injection hs₁ with hs₁; subst hs₁; exact Nat.le_add_right _ 1
      split at h
      · cases h
      · rename_i v _
        rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c.1 c.2 with
          _ | ⟨v', i', pm'⟩ <;> rw [hfs] at h
        · cases h
        · injection h with h
          rcases Prod.mk.inj h with ⟨rfl, h2⟩
          rcases Prod.mk.inj h2 with ⟨rfl, _⟩
          exact ⟨rfl, h1.2, hs₁_le⟩

private theorem stateT_liftProb_run {σ α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = (p >>= fun a => pure (a, s)) := rfl

theorem transmitImpl_tcur_epoch {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ qep B m : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    {gs gs' : Fig8G Pt ℓ} {Q : Party} {msg : LibsignalMsgPublicPart × Plain ℓ}
    {rc : Option (BitVec 256)} {res : Option (Fig8C Pt)}
    (htcur : ∀ R : Party, (gs.st R).tcur + (m + 1) + 1 ≤ B)
    (hmem : (res, gs') ∈ support
      ((CryptoGames.SM.transmitImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        3 (qep + 1) (Q, msg, rc)).run gs)) :
    (∀ R : Party, (gs'.st R).tcur + m + 1 ≤ B) ∧
      (∀ c, res = some c → c.1.1 + m + 1 ≤ B) := by
  have htcur0 : ∀ R : Party, (gs.st R).tcur + m + 1 ≤ B := fun R => by have := htcur R; omega
  unfold CryptoGames.SM.transmitImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;>
      simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ hc => nomatch hc⟩
    · rcases hmem with ⟨hres, rfl⟩
      obtain ⟨_, _, hst_eq⟩ := epMgmt_bounds_local hep
      obtain ⟨hst_le, hc_le⟩ := lFig8_send_tcur_epoch P Dh encPt encT idOf lam (s₁.st Q) msg coins
      have hQ_tcur := htcur Q
      rw [← hst_eq] at hQ_tcur
      refine ⟨fun R => ?_, fun c hc => ?_⟩
      · dsimp only [GameState.record]
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self]; omega
        · simp only [Function.update_of_ne hR, hst_eq]; exact htcur0 R
      · rw [hres, Option.some.injEq] at hc; subst hc; omega

theorem challImpl_tcur_epoch {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ qep B m : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : Fig8G Pt ℓ} {Q : Party} {m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ}
    {rc : Option (BitVec 256)} {res : Option (Fig8C Pt)}
    (htcur : ∀ R : Party, (gs.st R).tcur + (m + 1) + 1 ≤ B)
    (hmem : (res, gs') ∈ support
      ((CryptoGames.SM.challImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        3 (qep + 1) cfg (Q, m₀, m₁, rc)).run gs)) :
    (∀ R : Party, (gs'.st R).tcur + m + 1 ≤ B) ∧
      (∀ c, res = some c → c.1.1 + m + 1 ≤ B) := by
  have htcur0 : ∀ R : Party, (gs.st R).tcur + m + 1 ≤ B := fun R => by have := htcur R; omega
  unfold CryptoGames.SM.challImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;> simp only [hep] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ hc => nomatch hc⟩
    · by_cases hch : (!(s₁.safeCh 3 Q) || !(cfg.challAllowedIn (s₁.epoch Q))) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ hc => nomatch hc⟩
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨hres, rfl⟩
        obtain ⟨_, _, hst_eq⟩ := epMgmt_bounds_local hep
        set msg := (cfg.challMsg (s₁.epoch Q)).getD (if gs.b then m₁ else m₀)
        obtain ⟨hst_le, hc_le⟩ := lFig8_send_tcur_epoch P Dh encPt encT idOf lam (s₁.st Q) msg coins
        have hQ_tcur := htcur Q
        rw [← hst_eq] at hQ_tcur
        refine ⟨fun R => ?_, fun c hc => ?_⟩
        · dsimp only [GameState.record]
          by_cases hR : R = Q
          · subst hR; simp only [Function.update_self]; omega
          · simp only [Function.update_of_ne hR, hst_eq]; exact htcur0 R
        · rw [hres, Option.some.injEq] at hc; subst hc; omega

theorem deliverImpl_tcur_epoch {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ B m : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : Fig8G Pt ℓ} {Q : Party} {c : Fig8C Pt}
    {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (htcur : ∀ R : Party, (gs.st R).tcur + (m + 1) + 1 ≤ B)
    (hmem : (res, gs') ∈ support
      ((CryptoGames.SM.deliverImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        cfg (Q, c)).run gs)) :
    (∀ R : Party, (gs'.st R).tcur + m + 1 ≤ B) ∧
      (∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B) := by
  have htcur0 : ∀ R : Party, (gs.st R).tcur + m + 1 ≤ B := fun R => by have := htcur R; omega
  unfold CryptoGames.SM.deliverImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ _ _ hr => nomatch hr⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      at hmem
    rcases hin : gs.inTransit Q.other c with _ | rec₀ <;> simp only [hin] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ _ _ hr => nomatch hr⟩
    · rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
        _ | ⟨st', t, i, pm⟩ <;> simp only [hrcv] at hmem
      · split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          rcases hmem with ⟨rfl, rfl⟩ <;>
          exact ⟨htcur0, fun _ _ _ hr => nomatch hr⟩
      · obtain ⟨_, ht_le, hst'_le⟩ :=
          lFig8_receive_tcur_epoch P Dh encPt encT idOf lam (gs.st Q) st' c t i pm hrcv
        have hQ_tcur := htcur Q
        have hacc_st : ∀ R : Party, ((gs.accept Q st' rec₀.pos).st R).tcur + m + 1 ≤ B := by
          intro R
          dsimp only [GameState.accept]
          by_cases hR : R = Q
          · subst hR; simp only [Function.update_self]; omega
          · simp only [Function.update_of_ne hR]; exact htcur0 R
        by_cases hbad :
            (cfg.deliverWin &&
              gs.mustBeCorrect (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).maxSkip Q rec₀ &&
              !decide (t = rec₀.pos.epoch ∧ i = rec₀.pos.idx ∧ pm = rec₀.msg)) = true
        · simp only [hbad, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨hres, rfl⟩
          exact ⟨hacc_st, fun t₀ i₀ pm₀ hr => by
            rw [hres] at hr; injection hr with hr; injection hr with rfl _ _; omega⟩
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨hres, rfl⟩
          exact ⟨hacc_st, fun t₀ i₀ pm₀ hr => by
            rw [hres] at hr; injection hr with hr; injection hr with rfl _ _; omega⟩

theorem injectImpl_tcur_epoch {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ qep B m : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : Fig8G Pt ℓ} {Q : Party} {c : Fig8C Pt}
    {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (htcur : ∀ R : Party, (gs.st R).tcur + (m + 1) + 1 ≤ B)
    (hmem : (res, gs') ∈ support
      ((CryptoGames.SM.injectImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        3 (qep + 1) cfg (Q, c)).run gs)) :
    (∀ R : Party, (gs'.st R).tcur + m + 1 ≤ B) ∧
      (∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B) := by
  have htcur0 : ∀ R : Party, (gs.st R).tcur + m + 1 ≤ B := fun R => by have := htcur R; omega
  unfold CryptoGames.SM.injectImpl at hmem
  by_cases href : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3)) = true
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ _ _ hr => nomatch hr⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      at hmem
    rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
      _ | ⟨st', t, i, pm⟩ <;> simp only [hrcv] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ _ _ hr => nomatch hr⟩
    · obtain ⟨_, ht_le, hst'_le⟩ :=
        lFig8_receive_tcur_epoch P Dh encPt encT idOf lam (gs.st Q) st' c t i pm hrcv
      have hQ_tcur := htcur Q
      by_cases hcap : qep + 1 + 1 < t
      · simp only [hcap, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; exact ⟨htcur0, fun _ _ _ hr => nomatch hr⟩
      · simp only [hcap, ↓reduceIte] at hmem
        by_cases htriv : gs.trivial 3 ⟨Q.other, t, i⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨hres, rfl⟩
          refine ⟨fun R => ?_, fun t₀ i₀ pm₀ hr => ?_⟩
          · dsimp only [GameState.accept]
            by_cases hR : R = Q
            · subst hR; simp only [Function.update_self]; omega
            · simp only [Function.update_of_ne hR]; exact htcur0 R
          · rw [hres] at hr; injection hr with hr; injection hr with rfl _ _; omega
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
            rcases hmem with ⟨rfl, rfl⟩ <;>
            exact ⟨htcur0, fun _ _ _ hr => nomatch hr⟩

theorem onAcceptPure_clampInv_local {PQ Pt : Type} {ℓ qep B m : ℕ}
    (Q : Party) (w : Bytes) (isDel : Bool) (t i : ℕ) (msg : Plain ℓ)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (st : SimState PQ Pt ℓ)
    (hInv : SimBaseClampInv B m st) (ht : t + m + 1 ≤ B) :
    SimBaseClampInv B m (onAcceptPure qep Q w isDel t i msg ci? Tpk pq' st).2 := by
  have hacc : ∀ (pos : CryptoGames.SM.Pos), pos.epoch + m + 1 ≤ B →
      SimBaseClampInv B m
        { st with
          chains := Function.update st.chains Q
            (match ci? with
             | some ci => (st.chains Q).modify ci (·.accept i)
             | none => pushChain (st.chains Q) (GhostChain.accept ⟨some Tpk, t, 0, []⟩ i)),
          pq := Function.update st.pq Q pq',
          unackA := st.unackA && Q != Party.A,
          mir := st.mir.accept Q () pos } := by
    intro pos hpos
    refine {
      hep := fun R => by
        dsimp only [GameState.accept, GameState.delete]
        have := hInv.hep R
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self]; omega
        · simp only [Function.update_of_ne hR]; omega
      htrans := fun r hr => by
        dsimp only [GameState.accept, GameState.delete] at hr
        exact hInv.htrans r (List.mem_of_mem_filter hr)
      hch := fun R g' hg' => by
        dsimp only at hg'
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self] at hg'
          rcases ci? with _ | ci
          · rcases List.mem_append.mp (List.mem_of_mem_drop hg') with hmem | hmem
            · exact hInv.hch R g' hmem
            · rw [List.mem_singleton] at hmem; subst hmem
              unfold GhostChain.accept; split_ifs <;> exact ht
          · refine modify_mem_inv (P := fun g => g.epoch + m + 1 ≤ B) (hInv.hch R)
              (fun g hg => ?_) g' hg'
            unfold GhostChain.accept; split_ifs <;> exact hg
        · simp only [Function.update_of_ne hR] at hg'
          exact hInv.hch R g' hg'
      hhonest := hInv.hhonest }
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact hInv
    · exact hacc ⟨Q.other, t, i⟩ ht
    · exact ⟨hInv.hep, hInv.htrans, hInv.hch, hInv.hhonest⟩
  · simp only [↓reduceIte]
    rcases hin : st.mir.inTransit Q.other w with _ | r
    · exact hInv
    · exact hacc r.pos (hInv.htrans r (List.mem_of_find?_eq_some hin))

theorem onAnswerPure_clampInv_local {PQ Pt : Type} {ℓ qep B m : ℕ}
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (st : SimState PQ Pt ℓ)
    (hInv : SimBaseClampInv B m st)
    (hres : ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B) :
    SimBaseClampInv B m (onAnswerPure qep Q w isDel ci? Tpk pq' res st).2 := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hInv
  · exact hInv
  · exact onAcceptPure_clampInv_local Q w isDel t i ((pm.map (·.2)).getD default) ci? Tpk pq'
      st hInv (hres t i pm rfl)

theorem predictReceiveWithSnapshots_epoch_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes)
    (c c' : Fig8C Pt) {t i : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (h : predictReceiveWithSnapshots
      (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' = some (some (t, i, pm))) :
    t = c'.1.1 := by
  unfold predictReceiveWithSnapshots predictReceive at h
  dsimp only [Option.orElse] at h
  rcases hk : Kept.eval (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q) with _ | r <;> rw [hk] at h
  · rcases hs : sentEval (fs := lFS P.C P.codec ℓ encT idOf 25000) sC.sent c c' with _ | r' <;>
      rw [hs] at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨seed, _, hkdec⟩ := h
      unfold kDecryptFig8 at hkdec
      split at hkdec <;> simp at hkdec
      exact hkdec.1.symm
    · injection h with hr'
      subst hr'
      unfold sentEval at hs
      simp only [Option.map_eq_some_iff] at hs
      obtain ⟨e, _, hfs⟩ := hs
      obtain ⟨x, _, hx⟩ := hfs
      exact (Prod.mk.inj hx).1.symm
  · injection h with hr
    subst hr
    unfold Kept.eval at hk
    rcases hfull : (sC.kept Q).full with _ | st <;> rw [hfull] at hk
    · simp only [Option.map_eq_some_iff] at hk
      obtain ⟨v, _, hfs⟩ := hk
      obtain ⟨x, _, hx⟩ := hfs
      exact (Prod.mk.inj hx).1.symm
    · injection hk with hk
      obtain ⟨⟨st', t', i', pm'⟩, hrcv, h2⟩ := Option.map_eq_some_iff.mp hk
      rcases Prod.mk.inj h2 with ⟨rfl, _⟩
      exact (lFig8_receive_tcur_epoch P Dh encPt encT idOf lam st st' c' t' i' pm' hrcv).1

end TGInvHelpers

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedTG
