/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep

/-!
# Sanitized-to-Deduplicated Coupling for Tracker-Halted Figure 8

Defines the generic tracker-halted oracle wrapper `wrapHaltedOracle` and proves `SM.run`
equivalence between `simFig8ClampSanHalted` and `simFig8OracleTGDedupHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedSanGame

noncomputable section

open OracleSpec OracleComp
open _root_.ReductionDsl (isGameQuery)
open CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet.LibsignalInst
  (LibsignalMsgPublicPart lFS lFig8 ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C SimFig8C Fig8Comp GhostChain SimState pushChain inReceiveOnlyEpoch
   mkPub toWire simParseRecvC onAcceptPure onAnswerPure evalCKClamp
   semFwdAnswerHook semResyncHook semFwdEvictHook semFwdHook semRecvHook
   semHandleHookDedup makesAtMostQueries_iff_isGameQuery)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState idHook initSimC)
open CryptoGames.SM
  (GameState RecvResult Record partyEnc noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10)
open CryptoGames.LibsignalSession (Params PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack stepKemFailSend stepKemFailDeliver)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
  (simSendCTrackHalted semSendHookHalted simFig8OracleSanHalted simFig8ClampSanHalted)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame
  (KeptInv keptInv_unknown keptInv_ofSt keptInv_send keptInv_recv
   GameSanInv gameSanInv_init gameSanInv_transmitImpl gameSanInv_challImpl
   gameSanInv_deliverImpl gameSanInv_injectImpl gameSanInv_corrImpl)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
  (Fig8G fig8GameImpl simParseRecvC_tryFrom_and_idx evalCKClamp_index_le
   semHandleHookDedupS_inl_eq semCorrHookTGB_idHook_eq_semCorrHookTGDedup)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (fig8IdSemHook semCorrHookTGDedup simFig8OracleTG simFig8OracleTGDedup)

/-- Wraps a base Figure 8 simulator oracle with `KemFailTrackState` halting on send and delivery tracking. -/
@[expose] def wrapHaltedOracle {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (base : QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ))) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (Fig8Comp Pt ℓ)) :=
  let TrM := StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
    (Fig8Comp Pt ℓ)
  let liftBase {α : Type}
      (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) : TrM α :=
    StateT.mk fun (sC, tr) => (fun (a, sC') => (a, (sC', tr))) <$> m.run sC
  let c : QueryImpl unifSpec TrM := fun n => liftBase (base (.inl n))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option (BitVec 512)) →ₒ Option Bytes) TrM :=
    fun ⟨Q, m, r⟩ => StateT.mk fun st =>
      semSendHookHalted P K Dh encPt encT lam qep st Q m none r
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) →ₒ Option Bytes) TrM :=
    fun ⟨Q, m₀, m₁, r⟩ => StateT.mk fun st =>
      semSendHookHalted P K Dh encPt encT lam qep st Q m₀ (some m₁) r
  let i₃ : QueryImpl ((Party × Bytes) →ₒ Option (RecvResult (Plain ℓ))) TrM :=
    fun ⟨Q, w⟩ => StateT.mk fun (sC, tr) => do
      let j? := sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == (w : List (BitVec 8)) && Party.senderOf wc.2.1.1 == Q.other)
      let (res, sC') ← (base (.inr (.inl (.inl (.inr (Q, w)))))).run sC
      let tr' := match res, j? with
        | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
        | _, _ => tr
      return (res, (sC', tr'))
  let i₄ : QueryImpl ((Party × Bytes) →ₒ Option (RecvResult (Plain ℓ))) TrM :=
    fun q => liftBase (base (.inr (.inl (.inr q))))
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) TrM :=
    fun q => liftBase (base (.inr (.inr q)))
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

theorem simFig8OracleSanHalted_eq_wrap {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) :
    (simFig8OracleSanHalted P K Dh encPt encT decT lam qep B T Kc Bsk :
      QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
        (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
          (Fig8Comp Pt ℓ))) =
      wrapHaltedOracle P K Dh encPt encT lam qep
        (simFig8OracleSan (PQC := BitVec 512) P Dh encPt encT decT lam qep B T Kc Bsk) := rfl

@[expose] def simFig8OracleTGDedupHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (Fig8Comp Pt ℓ)) :=
  wrapHaltedOracle P K Dh encPt encT lam qep
    (simFig8OracleTGDedup (PQC := BitVec 512) P Dh encPt encT decT lam qep B B_skip?)

@[expose] def simFig8OracleTGHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (Fig8Comp Pt ℓ)) :=
  wrapHaltedOracle P K Dh encPt encT lam qep
    (simFig8OracleTG (PQC := BitVec 512) P Dh encPt encT decT lam qep B B_skip?)

@[expose] def simFig8ClampOfHalted {PQ Pt : Type} {ℓ : ℕ} (P : Params PQ (BitVec 512))
    (O : QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (Fig8Comp Pt ℓ)))
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    Fig8Comp Pt ℓ Bool := do
  let pqrKey ← (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  (simulateQ O A).run'
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), initKemFailTrack P.C.F pqrKey)

@[expose] def simFig8ClampTGHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ) (B_skip? : Option ℕ := none)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    Fig8Comp Pt ℓ Bool :=
  simFig8ClampOfHalted P (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B B_skip?) A

section GameImplHelpers

theorem simulateQ_fig8GameImpl_liftProb {Pt α : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (p : ProbComp α) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (liftM p : Fig8Comp Pt ℓ α)).run gs = (p >>= fun a => pure (a, gs)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (fig8GameImpl fig qep cfg)
      (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl t) >>=
          fun u => liftM (mx u))).run gs = ((query t >>= mx) >>= fun a => pure (a, gs))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hinl : (simulateQ (fig8GameImpl fig qep cfg)
        (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl t))).run gs =
        (query t >>= fun u => pure (u, gs)) := by
      simp only [query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]; rfl
    rw [hinl]; simp only [bind_assoc, pure_bind]; exact bind_congr fun u => ih u

theorem simulateQ_fig8GameImpl_inl_halted {PQ Pt τ : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (n : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : τ) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg)
      ((fun (a, sC') => (a, (sC', tr))) <$>
        (StateT.lift (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
            (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)) :
          StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC)).run gs =
      (query (spec := unifSpec) n >>= fun u => pure ((u, (sC, tr)), gs)) := by
  have h : (fun (a, sC') => (a, (sC', tr))) <$>
      (StateT.lift (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)) :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _).run sC =
      (liftM ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, (sC, tr))) :
        Fig8Comp Pt ℓ _) := by
    change (fun (a, sC') => (a, (sC', tr))) <$>
      (query (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt)
        (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n) >>=
          fun u => pure (u, sC)) = _
    rw [map_bind, liftM_bind]; exact bind_congr fun _ => rfl
  rw [h, simulateQ_fig8GameImpl_liftProb, bind_assoc]
  exact bind_congr fun _ => by simp

theorem simulateQ_fig8GameImpl_transmitQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (Q : Party)
    (msg : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.transmitQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
      Q msg rc)).run gs = (CryptoGames.SM.transmitImpl fig 3 (qep + 1) (Q, msg, rc)).run gs := by
  simp only [CryptoGames.SM.transmitQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

theorem simulateQ_fig8GameImpl_challQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (Q : Party)
    (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.challQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
      Q m₀ m₁ rc)).run gs = (CryptoGames.SM.challImpl fig 3 (qep + 1) cfg (Q, m₀, m₁, rc)).run gs := by
  simp only [CryptoGames.SM.challQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

theorem simulateQ_fig8GameImpl_deliverQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.deliverQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
      Q c)).run gs = (CryptoGames.SM.deliverImpl fig cfg (Q, c)).run gs := by
  simp only [CryptoGames.SM.deliverQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

theorem simulateQ_fig8GameImpl_injectQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.injectQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
      Q c)).run gs = (CryptoGames.SM.injectImpl fig 3 (qep + 1) cfg (Q, c)).run gs := by
  simp only [CryptoGames.SM.injectQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

theorem simulateQ_fig8GameImpl_corrQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (qep : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (Q : Party) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8GameImpl fig qep cfg) (CryptoGames.SM.corrQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
      Q)).run gs = (CryptoGames.SM.corrImpl Q).run gs := by
  simp only [CryptoGames.SM.corrQuery, query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8GameImpl_halted_eq_of_inv {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512))
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (O₁ O₂ : QueryImpl
      (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (Fig8Comp Pt ℓ)))
    (hinl₁ : ∀ n sC tr gs,
      (simulateQ (fig8GameImpl fig qep cfg) ((O₁ (.inl n)).run (sC, tr))).run gs =
        (query (spec := unifSpec) n >>= fun u => pure ((u, (sC, tr)), gs)))
    (hinl₂ : ∀ n sC tr gs,
      (simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inl n)).run (sC, tr))).run gs =
        (query (spec := unifSpec) n >>= fun u => pure ((u, (sC, tr)), gs)))
    (Inv : ℕ → LibsignalToModularSchemeSimState PQ Pt ℓ → Fig8G Pt ℓ → Prop)
    (hstepEq : ∀ (m : ℕ)
      (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
      (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
      (gs : Fig8G Pt ℓ), Inv (m + 1) sC gs →
      (simulateQ (fig8GameImpl fig qep cfg) ((O₁ (.inr t)).run (sC, tr))).run gs =
        (simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inr t)).run (sC, tr))).run gs)
    (hstepInv : ∀ (m : ℕ)
      (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
      (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
      (gs : Fig8G Pt ℓ), Inv (m + 1) sC gs →
      ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inr t)).run (sC, tr))).run gs),
        Inv m x.1.2.1 x.2)
    {α : Type}
    (oa : OracleComp
      (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) α)
    (m : ℕ) (hq : oa.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (gs : Fig8G Pt ℓ) (hInv : Inv m sC gs) :
    (simulateQ (fig8GameImpl fig qep cfg) ((simulateQ O₁ oa).run (sC, tr))).run gs =
      (simulateQ (fig8GameImpl fig qep cfg) ((simulateQ O₂ oa).run (sC, tr))).run gs := by
  induction oa using OracleComp.inductionOn generalizing m sC tr gs with
  | pure a => rfl
  | query_bind q mx ih =>
    have hq' := (isQueryBoundP_query_bind_iff _ q mx m).mp hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases q with n | t
    · have hqu : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)) m :=
        fun u => by simpa [isGameQuery] using hq'.2 u
      rw [hinl₁ n sC tr gs, hinl₂ n sC tr gs]
      simp only [bind_assoc, pure_bind]
      exact bind_congr fun u => ih u m (hqu u) sC tr gs hInv
    · have hm_pos : 0 < m := by simpa [isGameQuery] using hq'.1
      rcases m with _ | m'
      · omega
      have hqu : ∀ u, (mx u).IsQueryBoundP
          (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)) m' :=
        fun u => by simpa [isGameQuery] using hq'.2 u
      rw [hstepEq m' t sC tr gs hInv]
      exact bind_congr_of_forall_mem_support _ fun x hx =>
        ih x.1.1 m' (hqu x.1.1) x.1.2.1 x.1.2.2 x.2 (hstepInv m' t sC tr gs hInv x hx)

theorem sm_run_simFig8ClampOfHalted_eq_of_inv {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512))
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    (O₁ O₂ : QueryImpl
      (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (Fig8Comp Pt ℓ)))
    (hinl₁ : ∀ n sC tr gs,
      (simulateQ (fig8GameImpl fig qep cfg) ((O₁ (.inl n)).run (sC, tr))).run gs =
        (query (spec := unifSpec) n >>= fun u => pure ((u, (sC, tr)), gs)))
    (hinl₂ : ∀ n sC tr gs,
      (simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inl n)).run (sC, tr))).run gs =
        (query (spec := unifSpec) n >>= fun u => pure ((u, (sC, tr)), gs)))
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (Inv : ℕ → LibsignalToModularSchemeSimState PQ Pt ℓ → Fig8G Pt ℓ → Prop)
    (hinit : ∀ (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256),
      Inv q (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
        (CryptoGames.SM.initState fig k b))
    (hstepEq : ∀ (m : ℕ)
      (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
      (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
      (gs : Fig8G Pt ℓ), Inv (m + 1) sC gs →
      (simulateQ (fig8GameImpl fig qep cfg) ((O₁ (.inr t)).run (sC, tr))).run gs =
        (simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inr t)).run (sC, tr))).run gs)
    (hstepInv : ∀ (m : ℕ)
      (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
      (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
      (gs : Fig8G Pt ℓ), Inv (m + 1) sC gs →
      ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg) ((O₂ (.inr t)).run (sC, tr))).run gs),
        Inv m x.1.2.1 x.2) :
    CryptoGames.SM.run fig 3 (qep + 1) cfg b (simFig8ClampOfHalted P O₁ A) =
      CryptoGames.SM.run fig 3 (qep + 1) cfg b (simFig8ClampOfHalted P O₂ A) := by
  have hqP : A.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)) q :=
    (makesAtMostQueries_iff_isGameQuery A q).mp hq
  unfold CryptoGames.SM.run simFig8ClampOfHalted
  refine bind_congr fun k => ?_
  change (simulateQ (fig8GameImpl fig qep cfg) _).run (CryptoGames.SM.initState fig k b) =
    (simulateQ (fig8GameImpl fig qep cfg) _).run (CryptoGames.SM.initState fig k b)
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_liftProb, bind_assoc,
    pure_bind, StateT.run'_eq, simulateQ_map, StateT.run_map]
  refine bind_congr fun pqrKey => congrArg (Functor.map (Prod.map Prod.fst id)) ?_
  exact simulateQ_fig8GameImpl_halted_eq_of_inv P fig qep cfg O₁ O₂ hinl₁ hinl₂ Inv hstepEq hstepInv
    A q hqP (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (initKemFailTrack P.C.F pqrKey) (CryptoGames.SM.initState fig k b) (hinit k pqrKey)

end GameImplHelpers

section Hop1SanToTGDedup

private structure SanInv {PQ Pt : Type} {ℓ : ℕ} (q m : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) : Prop where
  hgame : GameSanInv q m gs
  hkept : ∀ R : Party, KeptInv (25000 * (q - m)) (sC.kept R)
  hchains : ∀ R : Party, ∀ g ∈ sC.base.chains R, g.last ≤ 25001 * (q - m)
  hhonest : ∀ wc ∈ sC.base.honest, wc.2.2.1 ≤ q - m

private theorem SanInv.mono {PQ Pt : Type} {ℓ q m₁ m₂ : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {gs : Fig8G Pt ℓ}
    (hle : m₁ ≤ m₂) (h : SanInv q m₂ sC gs) : SanInv q m₁ sC gs where
  hgame := h.hgame.mono hle
  hkept R := (h.hkept R).mono (Nat.mul_le_mul_left 25000 (by omega))
  hchains R g hg := Nat.le_trans (h.hchains R g hg) (Nat.mul_le_mul_left 25001 (by omega))
  hhonest wc hwc := Nat.le_trans (h.hhonest wc hwc) (by omega)

private theorem sanInv_init {PQ Pt : Type} [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (q : ℕ)
    (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256) (b : Bool) :
    SanInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ) q q
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (CryptoGames.SM.initState
        (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam) k b) where
  hgame := gameSanInv_init Dh encPt P.C P.codec encT
    (fun R => if R == Party.A then P.idA else P.idB) lam q k b
  hkept R := by
    simp only [Nat.sub_self, Nat.mul_zero, initSimC]
    exact keptInv_unknown 0
  hchains R g hg := by
    cases R <;> simp [initSimC, CryptoGames.Ratchet.LibsignalSim.initSim] at hg ⊢
    subst hg; rfl
  hhonest _ hwc := nomatch hwc

theorem modify_mem_inv {α : Type} {P : α → Prop} {l : List α} {n : ℕ} {f : α → α}
    (hl : ∀ x ∈ l, P x) (hf : ∀ x, P x → P (f x)) : ∀ x ∈ l.modify n f, P x := by
  induction l generalizing n with
  | nil => intro _ hx; simp at hx
  | cons a as ih =>
    cases n with
    | zero =>
      intro x hx; dsimp only [List.modify] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hf _ (hl _ (List.mem_cons_self ..))
      · exact hl x (List.mem_cons_of_mem _ hx)
    | succ k =>
      intro x hx; dsimp only [List.modify] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hl _ (List.mem_cons_self ..)
      · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx

private theorem ghostChain_accept_last_le {g : GhostChain} {i M : ℕ}
    (hg : g.last ≤ M) (hi : i ≤ M) : (g.accept i).last ≤ M := by
  unfold GhostChain.accept; split_ifs <;> assumption

private theorem pushChain_last_le {cs : List GhostChain} {g₀ : GhostChain} {M : ℕ}
    (hcs : ∀ g ∈ cs, g.last ≤ M) (hg₀ : g₀.last ≤ M) :
    ∀ g ∈ pushChain cs g₀, g.last ≤ M := by
  intro g hgm
  rcases List.mem_append.mp (List.mem_of_mem_drop hgm) with hmem | hmem
  · exact hcs g hmem
  · exact (List.mem_singleton.mp hmem) ▸ hg₀

private theorem onAcceptPure_last_le {PQ Pt : Type} {ℓ M : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, ∀ g ∈ s.chains R, g.last ≤ M) (hi : i ≤ M) :
    ∀ R, ∀ g ∈ (onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2.chains R, g.last ≤ M := by
  let cs' : List GhostChain := match ci? with
    | some ci => (s.chains Q).modify ci (·.accept i)
    | none => pushChain (s.chains Q)
        (GhostChain.accept { key := some Tpk, epoch := t, last := 0, skipped := [] } i)
  have hcs : ∀ g ∈ cs', g.last ≤ M := by
    rcases ci? with _ | ci
    · exact pushChain_last_le (hs Q) (ghostChain_accept_last_le (Nat.zero_le M) hi)
    · exact modify_mem_inv (hs Q) (fun _ hg => ghostChain_accept_last_le hg hi)
  have hu : ∀ R, ∀ g ∈ Function.update s.chains Q cs' R, g.last ≤ M := fun R => by
    by_cases hR : R = Q
    · subst hR; simpa using hcs
    · simpa [Function.update_of_ne hR] using hs R
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> assumption
  · simp only [↓reduceIte]; rcases s.mir.inTransit Q.other w with _ | r <;> assumption

private theorem onAnswerPure_last_le {PQ Pt : Type} {ℓ M : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, ∀ g ∈ s.chains R, g.last ≤ M)
    (hres : ∀ t i pm, res = some (.accepted t i pm) → i ≤ M) :
    ∀ R, ∀ g ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res s).2.chains R, g.last ≤ M := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact onAcceptPure_last_le qep Q w isDel t i ((pm.map (·.2)).getD default) ci? Tpk pq' s hs
      (hres t i pm rfl)

private theorem find?_mem {α : Type} {l : List α} {p : α → Bool} {a : α}
    (h : l.find? p = some a) : a ∈ l := List.mem_of_find?_eq_some h

theorem getD_mem_of_findIdx?_eq_some {α : Type} {l : List α} {p : α → Bool}
    {i : ℕ} (d : α) (h : l.findIdx? p = some i) : l.getD i d ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a as ih =>
    rw [List.findIdx?_cons] at h
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [List.getD]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      simp only [List.getD, List.getElem?_cons_succ]
      exact List.mem_cons_of_mem a (ih hj)

private theorem rejects_false_le {g : GhostChain} {i : ℕ}
    (h : g.rejects i = false) : i ≤ g.last + 25001 ∧ i - 1 ≤ g.last + 25000 := by
  unfold GhostChain.rejects at h
  by_cases hle : i ≤ g.last
  · omega
  · simp only [hle, ↓reduceIte, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    omega

theorem stateT_lift_idHook_mem {Pt σ α : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (p : ProbComp α) (st : σ) (k : α → StateT σ (Fig8Comp Pt ℓ) (Option Bytes))
    (gs : Fig8G Pt ℓ) {x : (Option Bytes × σ) × Fig8G Pt ℓ}
    (hx : x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
      (((StateT.lift (idHook.lift (liftM p : Fig8Comp Pt ℓ α)) :
        StateT σ (Fig8Comp Pt ℓ) α) >>= k).run st)).run gs)) :
    ∃ a, x ∈ support ((simulateQ (fig8GameImpl fig qep cfg) ((k a).run st)).run gs) := by
  have hl : (StateT.lift (idHook.lift (liftM p : Fig8Comp Pt ℓ α)) :
      StateT σ (Fig8Comp Pt ℓ) α).run st =
      (liftM (p >>= fun a => pure (a, st)) : Fig8Comp Pt ℓ (α × σ)) := by
    change ((liftM p : Fig8Comp Pt ℓ α) >>= fun a => pure (a, st)) = _
    rw [liftM_bind]; exact bind_congr fun _ => rfl
  rw [StateT.run_bind, hl] at hx
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_liftProb,
    bind_assoc, pure_bind, mem_support_bind_iff] at hx
  obtain ⟨a, -, hx⟩ := hx; exact ⟨a, hx⟩

set_option exponentiation.threshold 1024 in
private theorem semSendHookHalted_sanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ q m qep : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (gs : Fig8G Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (hInv : SanInv q (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semSendHookHalted P K Dh encPt encT lam qep (sC, tr) Q m₀ chal r)).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig ⟨⟨out₁, sC₁, tr₁⟩, gs₁⟩ hx
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semSendHookHalted simSendCTrackHalted at hx
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hx; dsimp only at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · by_cases hch : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hx
        let postRc (rq : BitVec 512) (rc : Option (BitVec 256)) :
            StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
              (Fig8Comp Pt ℓ) (Option Bytes) := do
          let tr' := stepKemFailSend P.C.F K tr Q rq
          let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then
            BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
          match mkPub (P := P) sC.base Q rq pn with
          | none => set (sC, { tr with cand := tr'.cand }); return none
          | some (pq', pub) =>
            let res ← StateT.lift (idHook.lift (match chal with
              | none => CryptoGames.SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
              | some m₁ => CryptoGames.SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc))
            match res with
            | none => set (sC, { tr with cand := tr'.cand }); return none
            | some c =>
              let w := toWire c
              let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
              let base' : SimState PQ Pt ℓ := { sC.base with
                mir := s₁.record 3 Q () rec' chal.isSome, pq := Function.update sC.base.pq Q pq',
                pn := Function.update sC.base.pn Q pn, honest := (w, c) :: sC.base.honest }
              let sent' := match (sC.kept Q).full, base'.honest.head? with
                | some st, some (_, c₀) => if st.id.sendsIn (st.tcur + 1) then sC.sent
                  else match st.vS with | some v => (c₀, v) :: sC.sent | none => sC.sent
                | _, _ => sC.sent
              set ({ sC with base := base',
                             kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)),
                             sent := sent' }, tr')
              return some w
        let postRq (r' : Option (BitVec 512)) (rq : BitVec 512) :
            StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
              (Fig8Comp Pt ℓ) (Option Bytes) := do
          let tr' := stepKemFailSend P.C.F K tr Q rq
          if tr'.cand.isSome then set (sC, { tr with cand := tr'.cand }); return none
          else
            let rc : Option (BitVec 256) ← StateT.lift (idHook.lift (match r' with
              | some _ => some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))
              | none => pure none))
            postRc rq rc
        change ((out₁, sC₁, tr₁), gs₁) ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
          ((StateT.lift ((idHook (Pt := Pt) (ℓ := ℓ)).lift (match r with
            | some rq => pure rq
            | none => liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512)))) >>= postRq r).run
            (sC, tr))).run gs) at hx
        have hrq : ∃ rq, ((out₁, sC₁, tr₁), gs₁) ∈
            support ((simulateQ (fig8GameImpl fig qep cfg) ((postRq r rq).run (sC, tr))).run gs) := by
          cases r with
          | none =>
            exact stateT_lift_idHook_mem fig qep cfg ($ᵗ BitVec 512) (sC, tr) (postRq none) gs hx
          | some rq₀ =>
            have hpure : ((StateT.lift ((idHook (Pt := Pt) (ℓ := ℓ)).lift (pure rq₀)) >>=
                postRq (some rq₀)).run (sC, tr)) = (postRq (some rq₀) rq₀).run (sC, tr) := by
              dsimp only [idHook]; rw [StateT.run_bind, StateT.run_lift, pure_bind, pure_bind]
            rw [hpure] at hx; exact ⟨rq₀, hx⟩
        obtain ⟨rq, hx⟩ := hrq
        dsimp only [postRq] at hx
        by_cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome = true
        · simp only [hcand, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hcand, Bool.false_eq_true, ↓reduceIte] at hx
          have hrc : ∃ rc : Option (BitVec 256), ((out₁, sC₁, tr₁), gs₁) ∈
              support ((simulateQ (fig8GameImpl fig qep cfg)
                ((postRc rq rc).run (sC, tr))).run gs) := by
            cases r with
            | none =>
              exact ⟨none, by simpa only [StateT.run_bind, idHook, StateT.run_lift, pure_bind] using hx⟩
            | some _ =>
              have hmap : (some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) :
                  Fig8Comp Pt ℓ (Option (BitVec 256))) =
                  liftM (some <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))) := by
                rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, liftM_bind]
                exact bind_congr fun _ => rfl
              dsimp only [idHook] at hx; rw [hmap] at hx
              exact stateT_lift_idHook_mem fig qep cfg
                (some <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))) (sC, tr) (postRc rq) gs hx
          obtain ⟨rc, hx⟩ := hrc; dsimp only [postRc] at hx
          rcases hmk : mkPub (P := P) sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
                BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;>
            simp only [hmk] at hx
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
          · have hpost : ∀ (c : Fig8C Pt),
                GameSanInv q m gs₁ → c.2.1 ≤ q - m →
                sC₁.kept = Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)) →
                sC₁.base.chains = sC.base.chains →
                sC₁.base.honest = (toWire c, c) :: sC.base.honest →
                SanInv q m sC₁ gs₁ := by
              intro c hg' hc hk_eq hch_eq hhon_eq
              refine ⟨hg', ?_, hch_eq ▸ hInv0.hchains, ?_⟩
              · intro R; rw [hk_eq]
                by_cases hR : R = Q
                · subst hR; simp only [Function.update_self]
                  exact (keptInv_send (hInv.hkept R)).mono (Nat.mul_le_mul_left 25000 (by omega))
                · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
              · intro wc hwc; rw [hhon_eq, List.mem_cons] at hwc
                rcases hwc with rfl | hwc
                · exact hc
                · exact hInv0.hhonest wc hwc
            cases chal with
            | none =>
              dsimp only [idHook] at hx
              simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind,
                simulateQ_fig8GameImpl_transmitQuery, mem_support_bind_iff] at hx
              obtain ⟨⟨res, gs'⟩, htr, hEq⟩ := hx; obtain ⟨hg', hc⟩ := gameSanInv_transmitImpl hInv.hgame htr
              rcases res with _ | c <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
              · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
              · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) rfl rfl rfl
            | some m₁ =>
              dsimp only [idHook] at hx
              simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind,
                simulateQ_fig8GameImpl_challQuery, mem_support_bind_iff] at hx
              obtain ⟨⟨res, gs'⟩, hch', hEq⟩ := hx; obtain ⟨hg', hc⟩ := gameSanInv_challImpl hInv.hgame hch'
              rcases res with _ | c <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
              · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
              · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) rfl rfl rfl

private theorem semFwdAnswerHook_sanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (hg : GameSanInv q (m + 1) gs)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m)
    (hc' : c'.2.1 ≤ 25001 * (q - m)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semFwdAnswerHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep sC' () Q w isDel ci? Tpk pq' c')).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig ⟨⟨rr₁, sC₁, ex₁⟩, gs₁⟩ hx
  have hm1 : m + 1 ≤ q := hg.hm
  have hsubK : 25000 * (q - (m + 1)) + 25000 = 25000 * (q - m) := by omega
  unfold semFwdAnswerHook at hx
  dsimp only at hx
  have hfin : ∀ (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))),
      GameSanInv q m gs₁ → (∀ t i pm, res = some (.accepted t i pm) → i = c'.2.1) →
      sC₁ = { (match res with
         | some (.accepted _ _ _) =>
           { sC' with kept := Function.update sC'.kept Q (Kept.recv (fig := fig)
               (fs := lFS P.C P.codec ℓ encT
                 (fun R => if R == Party.A then P.idA else P.idB) 25000)
               c' (sC'.kept Q)) }
         | _ => sC') with base := (onAnswerPure qep Q w isDel ci? Tpk pq' res sC'.base).2 } →
      SanInv q m sC₁ gs₁ := by
    intro res hg' hi_eq hsC₁
    subst hsC₁
    have hhon_oa : ∀ wc ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res sC'.base).2.honest,
        wc.2.2.1 ≤ q - m := by
      rcases res with _ | (_ | ⟨t, i, pm⟩)
      · exact hhon'
      · exact hhon'
      · dsimp only [onAnswerPure, onAcceptPure]
        cases isDel
        · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> exact hhon'
        · simp only [↓reduceIte]
          rcases sC'.base.mir.inTransit Q.other w with _ | _ <;> exact hhon'
    refine ⟨hg', ?_, onAnswerPure_last_le qep Q w isDel ci? Tpk pq' res sC'.base hch'
      (fun t i pm hr => (hi_eq t i pm hr) ▸ hc'), hhon_oa⟩
    rcases res with _ | (_ | ⟨t, i, pm⟩)
    · exact fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
    · exact fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
    · intro R
      by_cases hR : R = Q
      · subst hR
        change KeptInv _ (Function.update sC'.kept R _ R)
        rw [Function.update_self]
        exact hsubK ▸ keptInv_recv (hk' R)
      · change KeptInv _ (Function.update sC'.kept Q _ R)
        rw [Function.update_of_ne hR]
        exact (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
  by_cases hinT :
      (sC'.base.honest.any fun wc =>
        decide (wc.2 = c') && (sC'.base.mir.inTransit Q.other wc.1).isSome) = true
  · simp only [hinT, ↓reduceIte] at hx
    dsimp only [fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_deliverQuery, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨res, gs'⟩, hdl, ⟨_, hsC₁, _⟩, rfl⟩ := hx
    obtain ⟨hg', hi_eq⟩ := gameSanInv_deliverImpl hg hdl
    exact hfin res hg' hi_eq hsC₁
  · simp only [hinT, Bool.false_eq_true, ↓reduceIte] at hx
    dsimp only [fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_injectQuery, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨res, gs'⟩, hij, ⟨_, hsC₁, _⟩, rfl⟩ := hx
    obtain ⟨hg', hi_eq⟩ := gameSanInv_injectImpl hg hij
    exact hfin res hg' hi_eq hsC₁

private theorem semResyncHook_sanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes)
    (hg : GameSanInv q (m + 1) gs)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m)
    (hr_le : ∀ t_r i_r pm, r = some (t_r, i_r, pm) → i_r ≤ 25001 * (q - m)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semResyncHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep sC' () Q w ci? Tpk pq' c r)).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  have hm1 : m + 1 ≤ q := hg.hm
  have hsubK : 25000 * (q - (m + 1)) + 25000 = 25000 * (q - m) := by omega
  unfold semResyncHook at hx
  rcases r with _ | ⟨t_r, i_r, pub_r, m_r⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
    exact ⟨hg.mono (Nat.le_succ m),
      fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
  · dsimp only [fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_deliverQuery, mem_support_bind_iff] at hx
    obtain ⟨⟨res, gs'⟩, hdl, hx⟩ := hx
    obtain ⟨hg', -⟩ := gameSanInv_deliverImpl hg hdl
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      exact ⟨hg', fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      exact ⟨hg', fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      have hhon_oa : ∀ wc ∈ (onAcceptPure qep Q w true t_r i_r m_r ci? Tpk pq' sC'.base).2.honest,
          wc.2.2.1 ≤ q - m := by
        dsimp only [onAcceptPure]
        rcases sC'.base.mir.inTransit Q.other w with _ | _ <;> exact hhon'
      refine ⟨hg', ?_,
        onAcceptPure_last_le qep Q w true t_r i_r m_r ci? Tpk pq' sC'.base hch'
          (hr_le t_r i_r (pub_r, m_r) rfl), hhon_oa⟩
      intro R; dsimp only
      by_cases hR : R = Q
      · subst hR; simp only [Function.update_self]
        exact hsubK ▸ keptInv_recv (hk' R)
      · simp only [Function.update_of_ne hR]
        exact (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))

private theorem semFwdHook_sanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep B : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (hg : GameSanInv q (m + 1) gs)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (hc : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m)
    (hc' : c'.2.1 ≤ 25001 * (q - m)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semFwdHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep B sC' () Q w isDel ci? Tpk pq' hc c')).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig x hx
  have hm1 : m + 1 ≤ q := hg.hm
  unfold semFwdHook at hx
  rcases hc with _ | c
  · exact semFwdAnswerHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hg
      sC' ci? Tpk pq' c' hk' hch' hhon' hc' x hx
  · dsimp only at hx
    split at hx
    · rcases hev : evalCKClamp P Dh encPt encT lam B sC' Q w c c' with _ | r <;>
        simp only [hev] at hx
      · rcases x with ⟨⟨_, sC₁, _⟩, gs₁⟩
        dsimp only [fig8IdSemHook] at hx
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
        exact ⟨hg.mono (Nat.le_succ m),
          fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
      · exact semResyncHook_sanInv P Dh encPt encT lam cfg gs Q w hg
          sC' ci? Tpk pq' c r hk' hch' hhon'
          (fun t_r i_r pm hr =>
            (evalCKClamp_index_le P Dh encPt encT lam sC' Q w c c' (hr ▸ hev)).trans hc') x hx
    · exact semFwdAnswerHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hg
        sC' ci? Tpk pq' c' hk' hch' hhon' hc' x hx

private theorem semRecvHook_sanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep B : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (hInv : SanInv q (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel)).run gs),
      SanInv q m x.1.2.1 x.2 := by
  rintro fig ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semRecvHook at hx
  by_cases href :
      (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !(sC.base.mir.safeInj 3) ||
          !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hp] at hx
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · obtain ⟨_, -, _, hlct_i, _⟩ :=
        simParseRecvC_tryFrom_and_idx P decT Q (sC.base.pq Q) pq' w i pk T? lct hp
      let hcOpt : Option (SimFig8C Pt) :=
        Option.map (fun (wc : Bytes × SimFig8C Pt) => wc.2)
          (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      have hmkC : ∀ (t : ℕ) (T : Option Pt), i ≤ 25001 * (q - m) →
          (match hcOpt with
            | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
            | none => ((t, T), lct)).2.1 ≤ 25001 * (q - m) := by
        intro t T hi_le
        cases hhc : hcOpt with
        | none => dsimp only; omega
        | some c =>
          obtain ⟨wc, hfind, rfl⟩ := Option.map_eq_some_iff.mp hhc
          have hwc := hInv.hhonest wc (find?_mem hfind)
          dsimp only
          by_cases hct : wc.2.2.2.2 = lct.2.2 <;> simp only [hct, ↓reduceIte] <;> omega
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hsAmb_k : ∀ amb : Bool, ∀ R, KeptInv (25000 * (q - (m + 1)))
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.kept R) :=
          fun amb => by cases amb <;> exact hInv.hkept
        have hsAmb_c : ∀ amb : Bool, ∀ R, ∀ g ∈
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.base.chains R),
            g.last ≤ 25001 * (q - m) :=
          fun amb => by cases amb <;> exact hInv0.hchains
        have hsAmb_h : ∀ amb : Bool, ∀ wc ∈
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.base.honest),
            wc.2.2.1 ≤ q - m :=
          fun amb => by cases amb <;> exact hInv0.hhonest
        by_cases hc1 :
            ((((sC.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
             (((sC.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC.base.mir Q ||
                  decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
              exact ⟨hInv0.hgame,
                fun R => (hsAmb_k _ R).mono (Nat.mul_le_mul_left 25000 (by omega)),
                hsAmb_c _, hsAmb_h _⟩
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              have hnot : ¬ 25000 < i - 1 := fun hlt => hc2 (by simp [hlt])
              have hi_le : i ≤ 25001 * (q - m) := by omega
              rcases hT : T? with _ | T₀ <;>
                simp only [hT] at hx
              · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hx
                rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
                exact ⟨hInv0.hgame,
                  fun R => (hsAmb_k _ R).mono (Nat.mul_le_mul_left 25000 (by omega)),
                  hsAmb_c _, hsAmb_h _⟩
              · by_cases hev_b :
                    ((((sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  unfold semFwdEvictHook at hx
                  have hsAmb_mir :
                      (if (inReceiveOnlyEpoch sC.base.mir Q ||
                            (Q == Party.A && (sC.base.chains Q).any fun x => x.key.isNone)) = true then
                        { sC.base with amb := sC.base.amb + 1 }
                      else sC.base).mir = sC.base.mir := by
                    split_ifs <;> rfl
                  rw [hsAmb_mir] at hx
                  by_cases hev2 : (isDel && !sC.base.mir.safeInj 3) = true
                  · simp only [hev2, ↓reduceIte] at hx
                    dsimp only [fig8IdSemHook] at hx
                    simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff, Prod.mk.injEq] at hx
                    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
                    exact ⟨hInv0.hgame,
                      fun R => (hsAmb_k _ R).mono (Nat.mul_le_mul_left 25000 (by omega)),
                      hsAmb_c _, hsAmb_h _⟩
                  · simp only [hev2, Bool.false_eq_true, ↓reduceIte] at hx
                    exact semFwdAnswerHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hInv.hgame
                      _ none pk pq' ((sC.base.mir.epoch Q + 1, some T₀), lct)
                      (hsAmb_k _) (hsAmb_c _) (hsAmb_h _)
                      (by dsimp only; omega) _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hInv.hgame
                    _ none pk pq' hcOpt _ (hsAmb_k _) (hsAmb_c _) (hsAmb_h _)
                    (hmkC (sC.base.mir.epoch Q + 1) (some T₀) hi_le) _ hx
      · by_cases hrej :
            ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          have hrej0 :
              ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = false :=
            Bool.eq_false_iff.mpr hrej
          have hgmem := getD_mem_of_findIdx?_eq_some ⟨none, 0, 0, []⟩ hidx
          have hgl := hInv.hchains Q _ hgmem
          have hle := (rejects_false_le hrej0).1
          have hi_le : i ≤ 25001 * (q - m) := by omega
          exact semFwdHook_sanInv P Dh encPt encT lam cfg gs Q w isDel hInv.hgame
            sC (some ci) pk pq' hcOpt _ hInv.hkept hInv0.hchains hInv0.hhonest
            (hmkC (((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) T? hi_le) _ hx

private theorem semCorrHookTGDedup_sanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (B_skip? : Option ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) (Q : Party)
    (hInv : SanInv q (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semCorrHookTGDedup (PQC := BitVec 512) P Dh encT B_skip? sC Q)).run gs),
      SanInv q m x.1.2 x.2 := by
  intro fig ⟨⟨_, sC₁⟩, gs₁⟩ hx
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semCorrHookTGDedup at hx
  by_cases href :
      (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
       inReceiveOnlyEpoch sC.base.mir Q ||
       !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_corrQuery, mem_support_bind_iff] at hx
    obtain ⟨⟨res, gs'⟩, hcr, hx⟩ := hx
    obtain ⟨hg', hst_eq⟩ := gameSanInv_corrImpl hInv.hgame hcr
    rcases res with _ | fig8st
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl⟩, rfl⟩
      exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl⟩, rfl⟩
      refine ⟨hg', ?_, ?_, hInv0.hhonest⟩
      · intro R; dsimp only
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self, hst_eq fig8st rfl]
          exact (keptInv_ofSt (hInv.hgame.hparty R)).mono
            (Nat.mul_le_mul_left 25000 (by omega))
        · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
      · intro R g hg; dsimp only at hg
        by_cases hB0 : (Q == Party.B && sC.base.mir.epoch Party.B == 0) = true <;>
          simp only [hB0, ↓reduceIte, Bool.false_eq_true] at hg
        · rcases hγ : fig8st.γ with _ | x <;> simp only [hγ] at hg
          · exact hInv0.hchains R g hg
          · by_cases hR : R = .A
            · subst hR; simp only [Function.update_self, List.mem_map] at hg
              obtain ⟨g₀, hg₀, rfl⟩ := hg
              split_ifs <;> exact hInv0.hchains .A g₀ hg₀
            · simp only [Function.update_of_ne hR] at hg
              exact hInv0.hchains R g hg
        · exact hInv0.hchains R g hg

private theorem simFig8OracleTGDedupHalted_step_sanInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep B : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (B_skip? : Option ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (gs : Fig8G Pt ℓ)
    (hInv : SanInv q (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        ((simFig8OracleTGDedupHalted P K Dh encPt encT decT lam qep B B_skip? (.inr t)).run
          (sC, tr))).run gs),
      SanInv q m x.1.2.1 x.2 := by
  intro fig x hx
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHookHalted_sanInv P K Dh encPt encT lam cfg sC tr gs Q m₀ none r hInv x hx
  · exact semSendHookHalted_sanInv P K Dh encPt encT lam cfg sC tr gs Q m₀ (some m₁) r hInv x hx
  · have hstep :
        (simFig8OracleTGDedupHalted P K Dh encPt encT decT lam qep B B_skip?
          (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, tr) =
        (semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w true >>=
          fun y => pure (y.1, (y.2.1,
            match y.1, sC.base.honest.reverse.findIdx?
              (fun wc => wc.1 == (w : List (BitVec 8)) && Party.senderOf wc.2.1.1 == Q.other) with
            | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
            | _, _ => tr))) := by
      dsimp only [simFig8OracleTGDedupHalted, wrapHaltedOracle, simFig8OracleTGDedup,
        HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr, StateT.run, StateT.mk]
      change (Prod.map id Prod.fst <$> (semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w true >>=
          fun y => pure () >>= fun ex₂ => pure (y.1, y.2.1, ex₂))) >>= _ = _
      simp only [pure_bind, map_bind, map_pure, bind_assoc, Prod.map_apply, id_eq]
      refine bind_congr fun y => ?_; rcases y.1 with _ | r; · rfl
      cases r <;> cases sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == (w : List (BitVec 8)) && Party.senderOf wc.2.1.1 == Q.other) <;> rfl
    rw [hstep] at hx
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semRecvHook_sanInv P Dh encPt encT decT lam cfg sC gs Q w true hInv y hy
  · have hstep :
        (simFig8OracleTGDedupHalted P K Dh encPt encT decT lam qep B B_skip?
          (.inr (.inl (.inr (Q, w))))).run (sC, tr) =
        ((fun y => (y.1, (y.2.1, tr))) <$> semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w false) := by
      dsimp only [simFig8OracleTGDedupHalted, wrapHaltedOracle, simFig8OracleTGDedup,
        HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr, StateT.run, StateT.mk]
      change (fun (a, sC') => (a, (sC', tr))) <$> (Prod.map id Prod.fst <$>
        semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w false) = _
      simp only [Functor.map_map]; rfl
    rw [hstep, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semRecvHook_sanInv P Dh encPt encT decT lam cfg sC gs Q w false hInv y hy
  · have hstep : (simFig8OracleTGDedupHalted P K Dh encPt encT decT lam qep B B_skip?
        (.inr (.inr Q))).run (sC, tr) =
        ((fun (a, sC') => (a, (sC', tr))) <$> semCorrHookTGDedup P Dh encT B_skip? sC Q) := rfl
    rw [hstep, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semCorrHookTGDedup_sanInv P Dh encPt encT lam B_skip? cfg sC gs Q hInv y hy

private theorem simFig8OracleSanHalted_step_eq_tgDedup {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q m qep B T Kc Bsk : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    {gs : Fig8G Pt ℓ} (hT : 25000 * q ≤ T) (hKc : 25001 * q ≤ Kc) (hInv : SanInv q (m + 1) sC gs) :
    (simFig8OracleSanHalted P K Dh encPt encT decT lam qep B T Kc Bsk (.inr t)).run (sC, tr) =
      (simFig8OracleTGDedupHalted P K Dh encPt encT decT lam qep B (some Bsk) (.inr t)).run
        (sC, tr) := by
  have hm1 : m + 1 ≤ q := hInv.hgame.hm
  change (wrapHaltedOracle P K Dh encPt encT lam qep
      (simFig8OracleSan (PQC := BitVec 512) P Dh encPt encT decT lam qep B T Kc Bsk) (.inr t)).run
      (sC, tr) = _
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · dsimp only [simFig8OracleTGDedupHalted, wrapHaltedOracle,
      HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr]
  · dsimp only [simFig8OracleTGDedupHalted, wrapHaltedOracle,
      HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr]
  · dsimp only [simFig8OracleTGDedupHalted, wrapHaltedOracle,
      HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr, StateT.run, StateT.mk]
    have hbase : (simFig8OracleSan (PQC := BitVec 512) P Dh encPt encT decT lam qep B T Kc Bsk
        (.inr (.inl (.inl (.inr (Q, w)))))).run sC =
      (simFig8OracleTGDedup (PQC := BitVec 512) P Dh encPt encT decT lam qep B (some Bsk)
        (.inr (.inl (.inl (.inr (Q, w)))))).run sC := by
      exact congrArg (Prod.map id Prod.fst <$> ·) (semHandleHookDedupS_inl_eq P Dh encPt encT
        decT lam (fig8IdSemHook (PQC := BitVec 512) none) qep (.inl (.inr (Q, w))) sC ()
        (by omega) hInv.hkept (by omega) (fun R g hg => by have := hInv.hchains R g hg; omega))
    dsimp only [StateT.run] at hbase; rw [hbase]
  · dsimp only [simFig8OracleTGDedupHalted, wrapHaltedOracle,
      HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr, StateT.run, StateT.mk]
    have hbase : (simFig8OracleSan (PQC := BitVec 512) P Dh encPt encT decT lam qep B T Kc Bsk
        (.inr (.inl (.inr (Q, w))))).run sC =
      (simFig8OracleTGDedup (PQC := BitVec 512) P Dh encPt encT decT lam qep B (some Bsk)
        (.inr (.inl (.inr (Q, w))))).run sC := by
      exact congrArg (Prod.map id Prod.fst <$> ·) (semHandleHookDedupS_inl_eq P Dh encPt encT
        decT lam (fig8IdSemHook (PQC := BitVec 512) none) qep (.inr (Q, w)) sC ()
        (by omega) hInv.hkept (by omega) (fun R g hg => by have := hInv.hchains R g hg; omega))
    dsimp only [StateT.run] at hbase; rw [hbase]
  · dsimp only [simFig8OracleTGDedupHalted, wrapHaltedOracle,
      HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr, StateT.run, StateT.mk]
    exact congrArg ((fun (a, sC') => (a, (sC', tr))) <$> ·)
      (semCorrHookTGB_idHook_eq_semCorrHookTGDedup P Dh encT Bsk sC Q)

theorem sm_run_simFig8ClampSanHalted_eq_tgDedup {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool) {q : ℕ}
    {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q) (hT : 25000 * q ≤ T) (hKc : 25001 * q ≤ Kc) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampSanHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b (simFig8ClampOfHalted P
      (simFig8OracleTGDedupHalted P K Dh encPt encT decT lam qep B (some Bsk)) A) := by
  intro fig
  change CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampOfHalted P (simFig8OracleSanHalted P K Dh encPt encT decT lam qep B T Kc Bsk) A) = _
  refine sm_run_simFig8ClampOfHalted_eq_of_inv P fig qep cfg b _ _ ?_ ?_ hq (SanInv q)
    (fun k pqrKey => sanInv_init P Dh encPt encT lam q k pqrKey b) ?_ ?_
  · exact fun n sC tr gs => simulateQ_fig8GameImpl_inl_halted fig qep cfg n sC tr gs
  · exact fun n sC tr gs => simulateQ_fig8GameImpl_inl_halted fig qep cfg n sC tr gs
  · intro m t sC tr gs hInv
    rw [simFig8OracleSanHalted_step_eq_tgDedup P K Dh encPt encT decT lam t sC tr hT hKc hInv]
  · exact fun m t sC tr gs hInv => simFig8OracleTGDedupHalted_step_sanInv P K Dh encPt encT decT
      lam (some Bsk) cfg t sC tr gs hInv

end Hop1SanToTGDedup

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedSanGame
