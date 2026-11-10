/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp
import VCVio.EvalDist.Monad.Basic

/-!
# Cell-Game `simulateQ` Coupling for `simDeliverForgeClampSan`

Proves that `simDeliverForgeClampSan` agrees with `simDeliverForgeClamp` inside
`runBaseDFCellTPaper` whenever the adversary makes at most `q` game queries and the truncation
parameters satisfy `25000 * q ≤ T`, `25001 * q + 25000 ≤ Kc`, and `25000 * q ≤ Bsk`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanGame

open OracleSpec OracleComp
open _root_.ReductionDsl (isGameQuery)
open _root_.CryptoGames (Party SMScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.Ratchet (RootKey)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  lFS lFig8 ratchetKeyAdmissible)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimFig8St SimFig8C GhostChain SimState
  initSim pushChain inReceiveOnlyEpoch mkPub simParseRecvC onAcceptPure onAnswerPure scPostSendPure
  evalCKClamp semDrawSendCoins semSendHook semFwdAnswerHook semResyncHook semFwdEvictHook
  semFwdHook semRecvHook semCorrHookDedup semHandleHookDedup deliverForgeSemHook
  simDeliverForgeOracle simDeliverForgeOracleDedup simDeliverForgeClamp
  makesAtMostQueries_iff_isGameQuery stateT_lift_run)
open _root_.CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState initSimC)
open _root_.CryptoGames.SM (GameState Config Pos RecvResult partyEnc noBobSendInEpoch0
  noAliceCorrWhileAliceBelowEpoch10 initState transmitImpl deliverImpl)
open _root_.CryptoGames.SM.Thm1 (Mirror)
open _root_.CryptoGames.SM.Construction.DeliverForge (sameHdrScheme challSimDF'Paper specDF
  AdversaryDF AdversaryCompDF simImplDF'Paper simOraclesDF'Paper simTransmitDF'Paper
  simChallDF'Paper simDeliverDF simInjectDF simCorrDFPaper simDeliverForgeDF simCoinsDF
  transmitQueryDF challQueryDF deliverQueryDF injectQueryDF corrQueryDF deliverForgeQuery
  corrImplShiftedPaper afterCorrShifted)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params
  SignalMessageProtoCodec)
open _root_.CryptoGames.LibsignalSM.Proofs.Refinement (sameWireFig8)
open CryptoVerification.E2E (Bytes)
open CryptoVerification.LibsignalSession.HeadlineV1 (cellDelta cellShift cellTrivialT
  injectImplCellT deliverForgeBaseImplCellT oracleImplCellTPaper oracleImplBaseDFCellTPaper
  fullImplBaseDFCellTPaper runBaseDFCellTPaper)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame (SkippedLenLe KeptInv
  keptInv_unknown keptInv_ofSt keptInv_send keptInv_recv fig8PartyInv_send fig8PartyInv_receive
  lFig8_send_vS_and_idx lFig8_receive_vS_and_idx GameSanInv gameSanInv_init gameSanInv_deliverImpl)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling (simParseRecvC_tryFrom_and_idx
  evalCKClamp_index_le)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle (simDeliverForgeOracleSan
  simDeliverForgeClampSan)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanSem
  (simDeliverForgeOracleSan_inr_inl_eq simDeliverForgeOracleSan_inr_inr_eq_of_support
   run'_simulateQ_simDeliverForgeOracleDedup_eq_public)

private abbrev CellState (Pt : Type) (ℓ : ℕ) :=
  Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt) ×
    GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)

section CellSetup

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
  (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)

private def cellImplDF : QueryImpl
    (unifSpec + specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
    (StateT (CellState Pt ℓ) ProbComp) := fun q s => do
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT (fun R => if R == Party.A then P.idA else P.idB)
    25000 lam
  let ((a, mir'), gs') ←
    (simulateQ (fullImplBaseDFCellTPaper fig (qep + 1) tL tStar sameHdrScheme (Config.auth tStar))
      ((simImplDF'Paper (2 + 1) (qep + 1) q).run s.1)).run s.2
  return (a, (mir', gs'))

private theorem cellImplDF_run
    (q : (unifSpec +
      specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)).Domain)
    (mir : Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) :
    (cellImplDF P Dh encPt encT lam qep tL tStar q).run (mir, gs) =
      (do
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
        let ((a, mir'), gs') ←
          (simulateQ
            (fullImplBaseDFCellTPaper fig (qep + 1) tL tStar sameHdrScheme (Config.auth tStar))
            ((simImplDF'Paper (2 + 1) (qep + 1) q).run mir)).run gs
        return (a, (mir', gs'))) := rfl

private def runCellDF {α : Type}
    (oa : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt) α)
    (ms₀ : CellState Pt ℓ) : ProbComp (α × CellState Pt ℓ) :=
  (simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar) oa).run ms₀

private theorem cellImplDF_inl (n : unifSpec.Domain) (s : CellState Pt ℓ) :
    cellImplDF P Dh encPt encT lam qep tL tStar (.inl n) s =
      (query (spec := unifSpec) n >>= fun r => pure (r, s)) := by
  rcases s with ⟨mir, gs⟩; unfold cellImplDF simImplDF'Paper simCoinsDF fullImplBaseDFCellTPaper; simp

private theorem cellImplDF_liftM_probComp {α : Type} (p : ProbComp α) (s₀ : CellState Pt ℓ) :
    (simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar)
      (liftM p : AdversaryCompDF
        (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)).run s₀ =
      (p >>= fun a => pure (a, s₀)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar)
      (query (spec := unifSpec +
        specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt))
        (.inl t) >>= fun u => liftM (mx u))).run s₀ =
      ((query (spec := unifSpec) t >>= mx) >>= fun a => pure (a, s₀))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    change (cellImplDF P Dh encPt encT lam qep tL tStar (.inl t) s₀ >>=
      fun ⟨u, s₁⟩ => (simulateQ (cellImplDF P Dh encPt encT lam qep tL tStar)
        (liftM (mx u))).run s₁) = _
    rw [cellImplDF_inl]; simp only [bind_assoc, pure_bind]; exact bind_congr fun u => ih u

private theorem simulateQ_fullImplBaseDFCellTPaper_simImplDF'Paper_eq_runCellDF {α : Type}
    (oa : AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt) α)
    (mir : Mirror (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    (simulateQ (fullImplBaseDFCellTPaper fig (qep + 1) tL tStar sameHdrScheme (Config.auth tStar))
      ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1)) oa).run mir)).run gs =
    (runCellDF P Dh encPt encT lam qep tL tStar oa (mir, gs) >>=
      fun ⟨a, mir', gs'⟩ => pure ((a, mir'), gs')) := by
  dsimp only [runCellDF]
  induction oa using OracleComp.inductionOn generalizing mir gs with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind q u ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
      MonadLift.monadLift]
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, cellImplDF_run]
    simp only [bind_assoc, pure_bind]; exact bind_congr fun ⟨⟨a, mir'⟩, gs'⟩ => ih a mir' gs'

private theorem runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF
    (oa : AdversaryDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    runBaseDFCellTPaper fig (qep + 1) tL tStar sameHdrScheme (Config.auth tStar) false
      (challSimDF'Paper (2 + 1) (qep + 1) oa) =
    (do
      let k ← ($ᵗ (RootKey × BitVec 256) : ProbComp (RootKey × BitVec 256))
      let b ← ($ᵗ Bool : ProbComp Bool)
      let (u, _, gs') ← runCellDF P Dh encPt encT lam qep tL tStar oa
        ({ st := fun _ => (), b := b }, initState fig k false)
      return (u, gs')) := by
  dsimp only [runBaseDFCellTPaper, challSimDF'Paper]; refine bind_congr fun k => ?_
  rw [simulateQ_bind]
  change (StateT.lift ($ᵗ Bool : ProbComp Bool) >>= fun b =>
    simulateQ _ ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1)) oa).run'
      { st := fun _ => (), b := b })).run _ = _
  simp only [StateT.run_bind, stateT_lift_run, StateT.run'_eq, map_eq_bind_pure_comp,
    Function.comp_def, simulateQ_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [simulateQ_fullImplBaseDFCellTPaper_simImplDF'Paper_eq_runCellDF]
  simp only [bind_assoc, pure_bind]

end CellSetup

private theorem epMgmt_st_eq {St Msg C : Type}
    {gs s₁ : GameState St Msg C} {Δ qep : ℕ} {Q : Party} {bad : Bool}
    (h : gs.epMgmt Δ qep Q bad = some s₁) : s₁.st = gs.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> injection h with h <;> subst h <;> rfl

private theorem stateT_liftProb_run {σ α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = (p >>= fun a => pure (a, s)) := rfl

section BaseCellInv

variable {Pt : Type} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
  {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
  {lam : Pt} {q m qep : ℕ} {tL : Option ℕ} {tStar : ℕ}

private theorem gameSanInv_transmitImpl_delta [DecidableEq Pt] [Zero Pt] {Δ : ℕ}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {msg : LibsignalMsgPublicPart × Plain ℓ} {rc : Option (BitVec 256)}
    {res : Option (Fig8C Pt)} (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((transmitImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) Δ (qep + 1) (Q, msg, rc)).run gs)) :
    GameSanInv q m gs' ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  have hInv0 := hInv.mono (Nat.le_succ m); unfold transmitImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨hInv0, fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt Δ (qep + 1) Q bad with _ | s₁ <;>
      simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨rfl, rfl⟩; exact ⟨hInv0, fun _ hc => nomatch hc⟩
    · rcases hmem with ⟨rfl, rfl⟩
      have hst := epMgmt_st_eq hep; have hm1 : m + 1 ≤ q := hInv.hm
      have hsub : (q - (m + 1)) + 1 = q - m := by omega
      have hvsQ : ∀ vs, (s₁.st Q).vS = some vs → vs.lastIndex ≤ q - (m + 1) := by
        rw [hst]; exact hInv.hvs Q
      have hsend := lFig8_send_vS_and_idx (Dh := Dh) (encPt := encPt) (C := C) (codec := codec)
        (ℓ := ℓ) (encT := encT) (idOf := idOf) (lam := lam) hvsQ msg coins
      refine ⟨{ hm := hInv0.hm, hparty := fun R => ?_, hvs := fun R vs hv => ?_ },
        fun _ hc => Option.some.inj hc ▸ hsend.2.trans_eq hsub⟩
      · dsimp only [GameState.record]; by_cases hR : R = Q
        · subst hR; simp only [Function.update_self]
          exact (fig8PartyInv_send (hst ▸ hInv.hparty R) msg coins).mono
            (Nat.mul_le_mul_left 25000 (by omega))
        · simp only [Function.update_of_ne hR, hst]; exact hInv0.hparty R
      · dsimp only [GameState.record] at hv; by_cases hR : R = Q
        · subst hR; simp only [Function.update_self] at hv; exact (hsend.1 vs hv).trans_eq hsub
        · simp only [Function.update_of_ne hR, hst] at hv; exact hInv0.hvs R vs hv

private theorem gameSanInv_accept_cell [Zero Pt]
    {gs : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {c : Fig8C Pt} {st' : Fig8St Pt} {t i : ℕ}
    {pm : LibsignalMsgPublicPart × Plain ℓ} (pos : Pos) (hInv : GameSanInv q (m + 1) gs)
    (hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c =
      some (st', t, i, pm)) :
    GameSanInv q m (gs.accept Q st' pos) ∧ i = c.2.1 := by
  have hm1 : m + 1 ≤ q := hInv.hm; have hInv0 := hInv.mono (Nat.le_succ m)
  obtain ⟨hvS_eq, hi_eq⟩ := lFig8_receive_vS_and_idx hrcv
  refine ⟨{ hm := hInv0.hm, hparty := fun R => ?_, hvs := fun R vs hv => ?_ }, hi_eq⟩
  · dsimp only [GameState.accept, GameState.delete]; by_cases hR : R = Q
    · subst hR; simp only [Function.update_self]
      exact (fig8PartyInv_receive (hInv.hparty R) hrcv).mono (by omega)
    · simp only [Function.update_of_ne hR]; exact hInv0.hparty R
  · dsimp only [GameState.accept, GameState.delete] at hv; by_cases hR : R = Q
    · subst hR; simp only [Function.update_self, hvS_eq] at hv; exact hInv0.hvs R vs hv
    · simp only [Function.update_of_ne hR] at hv; exact hInv0.hvs R vs hv

private theorem gameSanInv_injectImplCellT [DecidableEq Pt] [Zero Pt]
    {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {c : Fig8C Pt} {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((injectImplCellT
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) qep tL tStar cfg (Q, c)).run gs)) :
    GameSanInv q m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  have hInv0 := hInv.mono (Nat.le_succ m); unfold injectImplCellT at hmem
  by_cases hw : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj (cellDelta tL tStar))) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
      _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩; exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
      · simp only [hqep, ↓reduceIte] at hmem
        obtain ⟨hacc, hi_eq⟩ := gameSanInv_accept_cell ⟨Q.other, t', i'⟩ hInv hrcv
        by_cases htriv : cellTrivialT tL tStar gs ⟨Q.other, t', i'⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          exact ⟨hacc, fun _ _ _ hc => by
            injection hc with hc; injection hc with _ hi _; exact hi.symm.trans hi_eq⟩
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
            (rcases hmem with ⟨rfl, rfl⟩;
             exact ⟨⟨hInv0.hm, hInv0.hparty, hInv0.hvs⟩, fun _ _ _ hc => nomatch hc⟩)

private theorem gameSanInv_deliverForgeBaseImplCellT [DecidableEq Pt] [Zero Pt]
    {cfg : Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {c c' : Fig8C Pt} {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((deliverForgeBaseImplCellT
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) qep tL tStar
      sameHdrScheme cfg (Q, c, c')).run gs)) :
    GameSanInv q m gs' := by
  have hInv0 := hInv.mono (Nat.le_succ m); unfold deliverForgeBaseImplCellT at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInv0
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases htr : gs.inTransit Q.other c with _ | r <;> simp only [htr] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv0
    · by_cases hcnd : ((gs.inTransit Q.other c').isSome || gs.comp.contains r.pos ||
          !(sameHdrScheme c c')) = true
      · simp only [hcnd, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv0
      · simp only [hcnd, Bool.false_eq_true, ↓reduceIte] at hmem
        rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c' with
          _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv0
        · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv0
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : cellTrivialT tL tStar gs ⟨Q.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact (gameSanInv_accept_cell ⟨Q.other, t', i'⟩ hInv hrcv).1
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              split_ifs at hmem <;>
                simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
                (rcases hmem with ⟨_, rfl⟩; exact ⟨hInv0.hm, hInv0.hparty, hInv0.hvs⟩)

end BaseCellInv

private theorem gameSanInv_corrImplShiftedPaper {Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {q m l : ℕ}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {res : Option (Fig8St Pt)}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support
      ((corrImplShiftedPaper (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (C := Fig8C Pt) l Q).run gs)) :
    GameSanInv q m gs' ∧ ∀ fig8st, res = some fig8st → fig8st = gs.st Q := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold corrImplShiftedPaper at hmem
  by_cases hw : (gs.win || !(gs.corrAllowedPaper Q)) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨hInv0, fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    have hst : (afterCorrShifted l gs Q).st = gs.st := by
      unfold afterCorrShifted; split_ifs <;> rfl
    exact ⟨⟨hInv0.hm, fun R => hst ▸ hInv0.hparty R, fun R => hst ▸ hInv0.hvs R⟩,
      fun _ hc => (Option.some.inj hc).symm⟩

section CellHookInv

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
  {ℓ q m qep : ℕ} {tL : Option ℕ} {tStar : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)

omit [SampleableType PQC] in
private theorem runCellDF_inr_bind_mem {β : Type}
    (q₀ : (specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt)).Domain)
    (f : (specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt)).Range q₀ → β)
    (ms ms' : CellState Pt ℓ) {b : β}
    (hy : (b, ms') ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
      (query (spec := unifSpec + specDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (SimFig8C Pt)) (.inr q₀) >>= fun r => pure (f r)) ms)) :
    ∃ r, b = f r ∧ ((r, ms'.1), ms'.2) ∈ support ((simulateQ
      (fullImplBaseDFCellTPaper (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
        (qep + 1) tL tStar sameHdrScheme (Config.auth tStar))
      ((simOraclesDF'Paper (2 + 1) (qep + 1) q₀).run ms.1)).run ms.2) := by
  rcases ms with ⟨mir, gs⟩; rcases ms' with ⟨mir', gs'⟩
  dsimp only [runCellDF] at hy
  simp only [query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
    simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨⟨r, mir₂, gs₂⟩, hmem, rfl, rfl, rfl⟩ := hy
  rw [cellImplDF_run] at hmem
  simp only [simImplDF'Paper, QueryImpl.add_apply_inr, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  obtain ⟨⟨⟨r', mir'⟩, gs'⟩, hmem, rfl, rfl, rfl⟩ := hmem
  exact ⟨r, rfl, hmem⟩

private theorem runCellDF_onTr_inv (Q : Party) (msg : LibsignalMsgPublicPart × Plain ℓ)
    (rc : Option (BitVec 256)) (ex ex' : List (Fig8C Pt)) (ms ms' : CellState Pt ℓ)
    (res : Option (Fig8C Pt)) (hInv : GameSanInv q (m + 1) ms.2)
    (hy : ((res, ex'), ms') ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onTr Q msg rc ex) ms)) :
    GameSanInv q m ms'.2 ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  dsimp only [deliverForgeSemHook, transmitQueryDF] at hy
  obtain ⟨res₂, hbf, hmem⟩ := runCellDF_inr_bind_mem P Dh encPt encT lam _ _ ms ms' hy
  rcases Prod.mk.inj hbf with ⟨rfl, -⟩
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl] at hmem
  unfold simTransmitDF'Paper transmitQueryDF
    fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
  obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
  have hgs : res = res₁ ∧ ms'.2 = gs₁ := by
    rcases res₁ with _ | c
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h2; exact ⟨h2.1.1, h2.2⟩
    · rcases hep : ms.1.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;>
        simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
        exact ⟨h2.1.1, h2.2⟩
  rw [hgs.1, hgs.2]; exact gameSanInv_transmitImpl_delta hInv hbase

private theorem runCellDF_onCh_inv (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ)
    (rc : Option (BitVec 256)) (ex ex' : List (Fig8C Pt)) (ms ms' : CellState Pt ℓ)
    (res : Option (Fig8C Pt)) (hInv : GameSanInv q (m + 1) ms.2)
    (hy : ((res, ex'), ms') ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onCh Q m₀ m₁ rc ex) ms)) :
    GameSanInv q m ms'.2 ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  dsimp only [deliverForgeSemHook, challQueryDF] at hy
  obtain ⟨res₂, hbf, hmem⟩ := runCellDF_inr_bind_mem P Dh encPt encT lam _ _ ms ms' hy
  rcases Prod.mk.inj hbf with ⟨rfl, -⟩
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simChallDF'Paper transmitQueryDF
    fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hep : ms.1.epMgmt (2 + 1) (qep + 1) Q false with _ | s₁ <;> simp only [hep] at hmem
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
  · cases hsc : s₁.safeCh (2 + 1) Q <;> simp only [hsc] at hmem
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
        query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
        simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
      have hgs : res = res₁ ∧ ms'.2 = gs₁ := by
        rcases res₁ with _ | c <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
          exact ⟨h2.1.1, h2.2⟩
      rw [hgs.1, hgs.2]; exact gameSanInv_transmitImpl_delta hInv hbase

private theorem runCellDF_onDl_inv (Q : Party) (c : Fig8C Pt) (ex ex' : List (Fig8C Pt))
    (ms ms' : CellState Pt ℓ) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hInv : GameSanInv q (m + 1) ms.2)
    (hy : ((res, ex'), ms') ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDl Q c ex) ms)) :
    GameSanInv q m ms'.2 ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  dsimp only [deliverForgeSemHook, deliverQueryDF] at hy
  obtain ⟨res₂, hbf, hmem⟩ := runCellDF_inr_bind_mem P Dh encPt encT lam _ _ ms ms' hy
  rcases Prod.mk.inj hbf with ⟨rfl, -⟩
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simDeliverDF deliverQueryDF
    fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
  obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
  obtain ⟨hfg', hacc⟩ := gameSanInv_deliverImpl hInv hbase
  have hgs : ms'.2 = gs₁ ∧ (∀ t i pm, res = some (.accepted t i pm) →
      ∃ pm', res₁ = some (.accepted t i pm')) := by
    rcases res₁ with _ | (_ | ⟨t', i', pm'⟩)
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h2; exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h2; exact ⟨h2.2, fun _ _ _ hc => by rw [h2.1.1] at hc; cases hc⟩
    · rcases htr : ms.1.inTransit Q.other c with _ | r <;>
        simp only [htr, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
          pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
        exact ⟨h2.2, fun t i pm hc => by rw [h2.1.1] at hc; cases hc; exact ⟨pm', rfl⟩⟩
  rw [hgs.1]; exact ⟨hfg', fun t i pm hc => by obtain ⟨pm', h1⟩ := hgs.2 t i pm hc; exact hacc t i pm' h1⟩

private theorem runCellDF_onIj_inv (Q : Party) (c : Fig8C Pt) (ex ex' : List (Fig8C Pt))
    (ms ms' : CellState Pt ℓ) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hInv : GameSanInv q (m + 1) ms.2)
    (hy : ((res, ex'), ms') ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onIj Q c ex) ms)) :
    GameSanInv q m ms'.2 ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  dsimp only [deliverForgeSemHook, injectQueryDF] at hy
  obtain ⟨res₂, hbf, hmem⟩ := runCellDF_inr_bind_mem P Dh encPt encT lam _ _ ms ms' hy
  rcases Prod.mk.inj hbf with ⟨rfl, -⟩
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simInjectDF injectQueryDF
    fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inl,
    QueryImpl.add_apply_inr, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
  obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
  have hgs : res = res₁ ∧ ms'.2 = gs₁ := by
    rcases res₁ with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
      exact ⟨h2.1.1, h2.2⟩
  rw [hgs.1, hgs.2]; exact gameSanInv_injectImplCellT hInv hbase

private theorem runCellDF_onCr_inv (Q : Party) (ex ex' : List (Fig8C Pt))
    (ms ms' : CellState Pt ℓ) (res : Option (Fig8St Pt)) (hInv : GameSanInv q (m + 1) ms.2)
    (hy : ((res, ex'), ms') ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onCr Q ex) ms)) :
    GameSanInv q m ms'.2 ∧ ∀ fig8st, res = some fig8st → fig8st = ms.2.st Q := by
  dsimp only [deliverForgeSemHook, corrQueryDF] at hy
  obtain ⟨res₂, hbf, hmem⟩ := runCellDF_inr_bind_mem P Dh encPt encT lam _ _ ms ms' hy
  rcases Prod.mk.inj hbf with ⟨rfl, -⟩
  simp only [simOraclesDF'Paper, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hmem
  unfold simCorrDFPaper corrQueryDF
    fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  cases hca : ms.1.corrAllowedPaper Q <;> simp only [hca] at hmem
  · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨rfl, -⟩, hms⟩; rw [hms]; exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, stateT_lift_run,
      query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
      simulateQ_query, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, bind_assoc, pure_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
    have hgs : res = res₁ ∧ ms'.2 = gs₁ := by
      rcases res₁ with _ | st' <;>
        simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
        exact ⟨h2.1.1, h2.2⟩
    rw [hgs.1, hgs.2]; exact gameSanInv_corrImplShiftedPaper hInv hbase

private theorem runCellDF_onProbe_inv (Q : Party) (c' : Fig8C Pt) (ex ex' : List (Fig8C Pt))
    (ms ms' : CellState Pt ℓ) (hInv : GameSanInv q (m + 1) ms.2)
    (hy : (ex', ms') ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
      ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex) ms)) :
    GameSanInv q m ms'.2 := by
  dsimp only [deliverForgeSemHook] at hy
  rcases hfind : ex.find? (fun c => sameWireFig8 c c') with _ | c <;> simp only [hfind] at hy
  · simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hy
    rcases hy with ⟨_, rfl⟩; exact hInv.mono (Nat.le_succ m)
  · dsimp only [deliverForgeQuery] at hy
    obtain ⟨_, -, hmem⟩ := runCellDF_inr_bind_mem P Dh encPt encT lam _ _ ms ms' hy
    simp only [simOraclesDF'Paper, QueryImpl.add_apply_inr] at hmem
    unfold simDeliverForgeDF deliverForgeQuery
      fullImplBaseDFCellTPaper oracleImplBaseDFCellTPaper oracleImplCellTPaper at hmem
    simp only [StateT.run_bind, StateT.run_get, stateT_lift_run, query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, simulateQ_bind, simulateQ_query, QueryImpl.add_apply_inr,
      pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨res₁, gs₁⟩, hbase, h2⟩ := hmem
    have hgs : ms'.2 = gs₁ := by
      rcases res₁ with _ | (_ | ⟨t', i', pm'⟩) <;>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2 <;>
        exact h2.2
    rw [hgs]; exact gameSanInv_deliverForgeBaseImplCellT hInv hbase

end CellHookInv

private structure DFSanInv {PQ Pt : Type} {ℓ : ℕ} (q m : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gs : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop where
  hgame : GameSanInv q m gs
  hkept : ∀ R : Party, KeptInv (25000 * (q - m)) (sC.kept R)
  hchains : ∀ R : Party, ∀ g ∈ sC.base.chains R, g.last ≤ 25001 * (q - m)
  hhonest : ∀ wc ∈ sC.base.honest, wc.2.2.1 ≤ q - m

private theorem DFSanInv.mono {PQ Pt : Type} {ℓ q m₁ m₂ : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {gs : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hle : m₁ ≤ m₂) (h : DFSanInv q m₂ sC gs) : DFSanInv q m₁ sC gs where
  hgame := h.hgame.mono hle
  hkept R := (h.hkept R).mono (Nat.mul_le_mul_left 25000 (by omega))
  hchains R g hg := Nat.le_trans (h.hchains R g hg) (Nat.mul_le_mul_left 25001 (by omega))
  hhonest wc hwc := Nat.le_trans (h.hhonest wc hwc) (by omega)

private theorem dfSanInv_init {PQ PQC Pt : Type} [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (q : ℕ)
    (k : RootKey × BitVec 256) (pqrKey : BitVec 256) (b : Bool) :
    DFSanInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ) q q
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (initState (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam) k b) where
  hgame := gameSanInv_init Dh encPt P.C P.codec encT
    (fun R => if R == Party.A then P.idA else P.idB) lam q k b
  hkept _ := by simp only [Nat.sub_self, Nat.mul_zero, initSimC]; exact keptInv_unknown 0
  hchains R g hg := by cases R <;> simp [initSimC, initSim] at hg ⊢; subst hg; rfl
  hhonest _ hwc := nomatch hwc

private theorem modify_mem_inv {α : Type} {Pred : α → Prop} {cs : List α} {ci : ℕ} {f : α → α}
    (hcs : ∀ x ∈ cs, Pred x) (hf : ∀ x, Pred x → Pred (f x)) : ∀ y ∈ cs.modify ci f, Pred y := by
  induction cs generalizing ci with
  | nil => intro _ hy; simp at hy
  | cons a xs ih =>
    cases ci <;> (intro y hy; dsimp only [List.modify] at hy; rcases List.mem_cons.mp hy with rfl | hy)
    · exact hf _ (hcs _ (List.mem_cons_self ..))
    · exact hcs y (List.mem_cons_of_mem _ hy)
    · exact hcs _ (List.mem_cons_self ..)
    · exact ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) y hy

private theorem ghostChain_accept_last_le {g : GhostChain} {i M : ℕ}
    (hg : g.last ≤ M) (hi : i ≤ M) : (g.accept i).last ≤ M := by
  unfold GhostChain.accept; split_ifs <;> assumption

private theorem pushChain_last_le {cs : List GhostChain} {g₀ : GhostChain} {M : ℕ}
    (hcs : ∀ g ∈ cs, g.last ≤ M) (hg₀ : g₀.last ≤ M) : ∀ g ∈ pushChain cs g₀, g.last ≤ M := by
  intro g hgm; rcases List.mem_append.mp (List.mem_of_mem_drop hgm) with hmem | hmem
  · exact hcs g hmem
  · rw [List.mem_singleton.mp hmem]; exact hg₀

private theorem onAcceptPure_last_le {PQ Pt : Type} {ℓ M : ℕ} (qep : ℕ) (Q : Party) (w : Bytes)
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) (hs : ∀ R, ∀ g ∈ s.chains R, g.last ≤ M) (hi : i ≤ M) :
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
  unfold onAcceptPure; cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> first | exact hs | exact hu
  · simp only [↓reduceIte]; rcases s.mir.inTransit Q.other w with _ | _ <;> first | exact hs | exact hu

private theorem onAnswerPure_last_le {PQ Pt : Type} {ℓ M : ℕ} (qep : ℕ) (Q : Party) (w : Bytes)
    (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, ∀ g ∈ s.chains R, g.last ≤ M)
    (hres : ∀ t i pm, res = some (.accepted t i pm) → i ≤ M) :
    ∀ R, ∀ g ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res s).2.chains R, g.last ≤ M := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact onAcceptPure_last_le qep Q w isDel t i ((pm.map (·.2)).getD default) ci? Tpk pq' s hs
      (hres t i pm rfl)

private theorem getD_mem_of_findIdx?_eq_some {α : Type} {p : α → Bool} {cs : List α} {ci : ℕ}
    (d : α) (h : cs.findIdx? p = some ci) : cs.getD ci d ∈ cs := by
  induction cs generalizing ci with
  | nil => simp at h
  | cons a xs ih =>
    rw [List.findIdx?_cons] at h; by_cases ha : p a = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at h; subst h; simp [List.getD]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h; exact List.mem_cons_of_mem a (ih hj)

private theorem rejects_false_le {g : GhostChain} {i : ℕ} (h : g.rejects i = false) :
    i ≤ g.last + 25001 ∧ i - 1 ≤ g.last + 25000 := by
  unfold GhostChain.rejects at h; by_cases hle : i ≤ g.last
  · omega
  · simp only [hle, ↓reduceIte, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h; omega

private theorem find?_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h : xs.find? p = some x) : x ∈ xs := List.mem_of_find?_eq_some h

section HookSanInv

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
  {ℓ q m qep : ℕ} {tL : Option ℕ} {tStar : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)

private theorem runCellDF_semDrawSendCoins {α : Type} (r : Option PQC)
    (k : PQC × Option (BitVec 256) →
      AdversaryCompDF (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (SimFig8C Pt) α)
    (ms : CellState Pt ℓ) {x : α × CellState Pt ℓ}
    (hx : x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
      (semDrawSendCoins (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) r >>= k) ms)) :
    ∃ rq rc, x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar (k (rq, rc)) ms) := by
  cases r <;>
    (dsimp only [semDrawSendCoins, deliverForgeSemHook, runCellDF] at hx ⊢;
     simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
       cellImplDF_liftM_probComp, mem_support_bind_iff] at hx;
     obtain ⟨c, -, hx⟩ := hx; exact ⟨_, _, hx⟩)

private theorem semSendHook_dfSanInv
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : CellState Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hInv : DFSanInv q (m + 1) sC ms.2) :
    ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
        (semSendHook P Dh encPt encT lam
          (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC ex Q m₀ chal r) ms),
      DFSanInv q m x.1.2.1 x.2.2 := by
  rintro ⟨⟨out₁, sC₁, ex₁⟩, ms₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm; have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semSendHook at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;> simp only [hep] at hx
    · simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · by_cases hch : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [hch, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hx
        obtain ⟨rq, rc, hx⟩ := runCellDF_semDrawSendCoins P Dh encPt encT lam r _ ms hx
        change _ ∈ support (runCellDF P Dh encPt encT lam qep tL tStar (pure (ex, ex) >>= _) ms) at hx
        rw [pure_bind] at hx
        rcases hmk : mkPub P sC.base Q rq (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
            BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hmk] at hx
        · simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · have hpost : ∀ (c : Fig8C Pt), GameSanInv q m ms₁.2 → c.2.1 ≤ q - m →
              sC₁ = scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ chal.isSome pq'
                (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
                  BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) c →
              DFSanInv q m sC₁ ms₁.2 := by
            intro c hg' hc hsC₁; subst hsC₁; refine ⟨hg', ?_, hInv0.hchains, ?_⟩
            · intro R; unfold scPostSendPure; by_cases hR : R = Q
              · subst hR; simp only [Function.update_self]
                exact (keptInv_send (hInv.hkept R)).mono (Nat.mul_le_mul_left 25000 (by omega))
              · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
            · intro wc hwc; unfold scPostSendPure at hwc
              rcases List.mem_cons.mp hwc with rfl | hwc
              · exact hc
              · exact hInv0.hhonest wc hwc
          cases chal with
          | none =>
            simp only [runCellDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
            obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, htr, hEq⟩ := hx
            obtain ⟨hg', hc⟩ := runCellDF_onTr_inv P Dh encPt encT lam Q (pub, m₀) rc
              ex ex₂ ms ms' res hInv.hgame htr
            rcases res with _ | c <;>
              simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hEq
            · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
            · rcases hEq with ⟨⟨_, hsC₁, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) hsC₁
          | some m₁ =>
            simp only [runCellDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
            obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hch', hEq⟩ := hx
            obtain ⟨hg', hc⟩ := runCellDF_onCh_inv P Dh encPt encT lam Q (pub, m₀) (pub, m₁) rc
              ex ex₂ ms ms' res hInv.hgame hch'
            rcases res with _ | c <;>
              simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hEq
            · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
            · rcases hEq with ⟨⟨_, hsC₁, _⟩, rfl⟩; exact hpost c hg' (hc c rfl) hsC₁

private theorem semFwdAnswerHook_dfSanInv (ms : CellState Pt ℓ) (Q : Party) (w : Bytes)
    (isDel : Bool) (hg : GameSanInv q (m + 1) ms.2)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m) (hc' : c'.2.1 ≤ 25001 * (q - m)) :
    ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
        (semFwdAnswerHook P Dh encPt encT lam
          (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
          qep sC' ex Q w isDel ci? Tpk pq' c') ms),
      DFSanInv q m x.1.2.1 x.2.2 := by
  rintro ⟨⟨_, sC₁, _⟩, ms₁⟩ hx
  let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  have hm1 : m + 1 ≤ q := hg.hm; have hsubK : 25000 * (q - (m + 1)) + 25000 = 25000 * (q - m) := by omega
  unfold semFwdAnswerHook at hx; dsimp only at hx
  have hfin : ∀ (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))),
      GameSanInv q m ms₁.2 → (∀ t i pm, res = some (.accepted t i pm) → i = c'.2.1) →
      sC₁ = { (match res with
         | some (.accepted _ _ _) =>
           { sC' with kept := Function.update sC'.kept Q (Kept.recv (fig := fig)
               (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC'.kept Q)) }
         | _ => sC') with base := (onAnswerPure qep Q w isDel ci? Tpk pq' res sC'.base).2 } →
      DFSanInv q m sC₁ ms₁.2 := by
    intro res hg' hi_eq hsC₁; subst hsC₁
    have hhon_oa : ∀ wc ∈ (onAnswerPure qep Q w isDel ci? Tpk pq' res sC'.base).2.honest,
        wc.2.2.1 ≤ q - m := by
      rcases res with _ | (_ | ⟨t, i, pm⟩)
      · exact hhon'
      · exact hhon'
      · dsimp only [onAnswerPure, onAcceptPure]; cases isDel
        · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> exact hhon'
        · simp only [↓reduceIte]; rcases sC'.base.mir.inTransit Q.other w with _ | _ <;> exact hhon'
    refine ⟨hg', ?_, onAnswerPure_last_le qep Q w isDel ci? Tpk pq' res sC'.base hch'
      (fun t i pm hr => (hi_eq t i pm hr) ▸ hc'), hhon_oa⟩
    rcases res with _ | (_ | ⟨t, i, pm⟩)
    · exact fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
    · exact fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
    · intro R; by_cases hR : R = Q
      · subst hR; change KeptInv _ (Function.update sC'.kept R _ R)
        rw [Function.update_self]; exact hsubK ▸ keptInv_recv (hk' R)
      · change KeptInv _ (Function.update sC'.kept Q _ R)
        rw [Function.update_of_ne hR]; exact (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))
  by_cases hinT : (sC'.base.honest.any fun wc =>
      decide (wc.2 = c') && (sC'.base.mir.inTransit Q.other wc.1).isSome) = true
  · simp only [hinT, ↓reduceIte, runCellDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hdl, ⟨_, hsC₁, _⟩, rfl⟩ := hx
    obtain ⟨hg', hi_eq⟩ := runCellDF_onDl_inv P Dh encPt encT lam Q c' ex ex₂ ms ms₁ res hg hdl
    exact hfin res hg' hi_eq hsC₁
  · simp only [hinT, Bool.false_eq_true, ↓reduceIte, runCellDF, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hx
    obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hij, ⟨_, hsC₁, _⟩, rfl⟩ := hx
    obtain ⟨hg', hi_eq⟩ := runCellDF_onIj_inv P Dh encPt encT lam Q c' ex ex₂ ms ms₁ res hg hij
    exact hfin res hg' hi_eq hsC₁

private theorem semResyncHook_dfSanInv (ms : CellState Pt ℓ) (Q : Party) (w : Bytes)
    (hg : GameSanInv q (m + 1) ms.2) (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (Fig8C Pt)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m)
    (hr_le : ∀ t_r i_r pm, r = some (t_r, i_r, pm) → i_r ≤ 25001 * (q - m)) :
    ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
        (semResyncHook P Dh encPt encT lam
          (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC' ex Q w ci? Tpk pq' c r) ms),
      DFSanInv q m x.1.2.1 x.2.2 := by
  rintro ⟨⟨_, sC₁, _⟩, ms₁⟩ hx
  have hm1 : m + 1 ≤ q := hg.hm; have hsubK : 25000 * (q - (m + 1)) + 25000 = 25000 * (q - m) := by omega
  unfold semResyncHook at hx; rcases r with _ | ⟨t_r, i_r, pub_r, m_r⟩
  · simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
    exact ⟨hg.mono (Nat.le_succ m),
      fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
  · simp only [runCellDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
    obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hdl, hx⟩ := hx
    obtain ⟨hg', -⟩ := runCellDF_onDl_inv P Dh encPt encT lam Q c ex ex₂ ms ms' res hg hdl
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
        dsimp only [onAcceptPure]; rcases sC'.base.mir.inTransit Q.other w with _ | _ <;> exact hhon'
      refine ⟨hg', ?_, onAcceptPure_last_le qep Q w true t_r i_r m_r ci? Tpk pq' sC'.base hch'
        (hr_le t_r i_r (pub_r, m_r) rfl), hhon_oa⟩
      intro R; dsimp only; by_cases hR : R = Q
      · subst hR; simp only [Function.update_self]; exact hsubK ▸ keptInv_recv (hk' R)
      · simp only [Function.update_of_ne hR]
        exact (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega))

private theorem semFwdHook_dfSanInv (B : ℕ) (ms : CellState Pt ℓ) (Q : Party) (w : Bytes)
    (isDel : Bool) (hg : GameSanInv q (m + 1) ms.2)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt))
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (hc : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hk' : ∀ R, KeptInv (25000 * (q - (m + 1))) (sC'.kept R))
    (hch' : ∀ R, ∀ g ∈ sC'.base.chains R, g.last ≤ 25001 * (q - m))
    (hhon' : ∀ wc ∈ sC'.base.honest, wc.2.2.1 ≤ q - m) (hc' : c'.2.1 ≤ 25001 * (q - m)) :
    ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
        (semFwdHook P Dh encPt encT lam
          (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
          qep B sC' ex Q w isDel ci? Tpk pq' hc c') ms),
      DFSanInv q m x.1.2.1 x.2.2 := by
  intro x hx; have hm1 : m + 1 ≤ q := hg.hm; unfold semFwdHook at hx; rcases hc with _ | c
  · exact semFwdAnswerHook_dfSanInv P Dh encPt encT lam ms Q w isDel hg
      sC' ex ci? Tpk pq' c' hk' hch' hhon' hc' x hx
  · dsimp only at hx; split at hx
    · rcases hev : evalCKClamp P Dh encPt encT lam B sC' Q w c c' with _ | r <;> simp only [hev] at hx
      · rcases x with ⟨⟨_, sC₁, _⟩, ms₁⟩
        simp only [runCellDF, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
          simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨⟨ex₂, ms'⟩, hpr, ⟨_, rfl, _⟩, rfl⟩ := hx
        exact ⟨runCellDF_onProbe_inv P Dh encPt encT lam Q c' ex ex₂ ms ms₁ hg hpr,
          fun R => (hk' R).mono (Nat.mul_le_mul_left 25000 (by omega)), hch', hhon'⟩
      · exact semResyncHook_dfSanInv P Dh encPt encT lam ms Q w hg sC' ex ci? Tpk pq' c r hk' hch'
          hhon' (fun t_r i_r pm hr =>
            (evalCKClamp_index_le P Dh encPt encT lam sC' Q w c c' (hr ▸ hev)).trans hc') x hx
    · exact semFwdAnswerHook_dfSanInv P Dh encPt encT lam ms Q w isDel hg
        sC' ex ci? Tpk pq' c' hk' hch' hhon' hc' x hx

private theorem semRecvHook_dfSanInv (decT : PublicKey → Option Pt) (B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : CellState Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (hInv : DFSanInv q (m + 1) sC ms.2) :
    ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
        (semRecvHook P Dh encPt encT decT lam
          (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w isDel) ms),
      DFSanInv q m x.1.2.1 x.2.2 := by
  rintro ⟨⟨_, sC₁, _⟩, ms₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm; have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semRecvHook at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
        !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;> simp only [hp] at hx
    · simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · obtain ⟨_, -, _, hlct_i, _⟩ :=
        simParseRecvC_tryFrom_and_idx P decT Q (sC.base.pq Q) pq' w i pk T? lct hp
      let hcOpt : Option (SimFig8C Pt) := Option.map (fun (wc : Bytes × SimFig8C Pt) => wc.2)
        (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      have hmkC : ∀ (t : ℕ) (T : Option Pt), i ≤ 25001 * (q - m) →
          (match hcOpt with
            | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
            | none => ((t, T), lct)).2.1 ≤ 25001 * (q - m) := fun t T hi_le => by
        cases hhc : hcOpt
        · dsimp only; omega
        · obtain ⟨wc, hfind, rfl⟩ := Option.map_eq_some_iff.mp hhc
          have hwc := hInv.hhonest wc (find?_mem hfind)
          dsimp only; by_cases hct : wc.2.2.2.2 = lct.2.2 <;> simp only [hct, ↓reduceIte] <;> omega
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hsAmb_k : ∀ amb : Bool, ∀ R, KeptInv (25000 * (q - (m + 1)))
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.kept R) :=
          fun amb => by cases amb <;> exact hInv.hkept
        have hsAmb_c : ∀ amb : Bool, ∀ R, ∀ g ∈
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.base.chains R),
            g.last ≤ 25001 * (q - m) := fun amb => by cases amb <;> exact hInv0.hchains
        have hsAmb_h : ∀ amb : Bool, ∀ wc ∈
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }.base.honest),
            wc.2.2.1 ≤ q - m := fun amb => by cases amb <;> exact hInv0.hhonest
        have hsAmb_inv : ∀ amb : Bool, DFSanInv q m
            { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base } ms.2 :=
          fun amb => ⟨hInv0.hgame,
            fun R => (hsAmb_k amb R).mono (Nat.mul_le_mul_left 25000 (by omega)),
            hsAmb_c amb, hsAmb_h amb⟩
        by_cases hc1 : ((((sC.base.honest.find? fun wc =>
              wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
            fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
           (((sC.base.honest.find? fun wc =>
              wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
            fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff, Prod.mk.injEq] at hx; rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) ||
                decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hsAmb_inv _
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              have hnot : ¬ 25000 < i - 1 := fun hlt => hc2 (by simp [hlt])
              have hi_le : i ≤ 25001 * (q - m) := by omega
              rcases hT : T? with _ | T₀ <;> simp only [hT] at hx
              · simp only [runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
                  Set.mem_singleton_iff, Prod.mk.injEq] at hx
                rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hsAmb_inv _
              · by_cases hev_b : ((((sC.base.honest.find? fun wc =>
                      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                    fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx; unfold semFwdEvictHook at hx
                  have hsAmb_mir : (if (inReceiveOnlyEpoch sC.base.mir Q ||
                        (Q == Party.A && (sC.base.chains Q).any fun x => x.key.isNone)) = true then
                      { sC.base with amb := sC.base.amb + 1 } else sC.base).mir = sC.base.mir := by
                    split_ifs <;> rfl
                  rw [hsAmb_mir] at hx
                  by_cases hev2 : (isDel && !sC.base.mir.safeInj 3) = true
                  · simp only [hev2, ↓reduceIte, runCellDF, simulateQ_bind, StateT.run_bind,
                      mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff, Prod.mk.injEq] at hx
                    obtain ⟨⟨ex₂, ms'⟩, hpr, ⟨_, rfl, _⟩, rfl⟩ := hx
                    exact ⟨runCellDF_onProbe_inv P Dh encPt encT lam Q
                        ((sC.base.mir.epoch Q + 1, some T₀), lct) ex ex₂ ms ms₁ hInv.hgame hpr,
                      (hsAmb_inv _).hkept, hsAmb_c _, hsAmb_h _⟩
                  · simp only [hev2, Bool.false_eq_true, ↓reduceIte] at hx
                    exact semFwdAnswerHook_dfSanInv P Dh encPt encT lam ms Q w isDel hInv.hgame
                      _ ex none pk pq' ((sC.base.mir.epoch Q + 1, some T₀), lct)
                      (hsAmb_k _) (hsAmb_c _) (hsAmb_h _) (by dsimp only; omega) _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_dfSanInv P Dh encPt encT lam B ms Q w isDel hInv.hgame
                    _ ex none pk pq' hcOpt _ (hsAmb_k _) (hsAmb_c _) (hsAmb_h _)
                    (hmkC (sC.base.mir.epoch Q + 1) (some T₀) hi_le) _ hx
      · by_cases hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          have hgl := hInv.hchains Q _ (getD_mem_of_findIdx?_eq_some ⟨none, 0, 0, []⟩ hidx)
          have hle := (rejects_false_le (Bool.eq_false_iff.mpr hrej)).1
          exact semFwdHook_dfSanInv P Dh encPt encT lam B ms Q w isDel hInv.hgame
            sC ex (some ci) pk pq' hcOpt _ hInv.hkept hInv0.hchains hInv0.hhonest
            (hmkC (((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) T? (by omega)) _ hx

private theorem semCorrHookDedup_dfSanInv
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : CellState Pt ℓ)
    (Q : Party) (hInv : DFSanInv q (m + 1) sC ms.2) :
    ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
        (semCorrHookDedup P Dh encT
          (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) sC ex Q) ms),
      DFSanInv q m x.1.2.1 x.2.2 := by
  rintro ⟨⟨_, sC₁, _⟩, ms₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm; have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semCorrHookDedup at hx
  by_cases href : (sC.base.stopped || sC.base.mir.win || !sC.base.mir.corrAllowed Q ||
      inReceiveOnlyEpoch sC.base.mir Q || !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true
  · simp only [href, ↓reduceIte, runCellDF, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte, runCellDF, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hx
    obtain ⟨⟨⟨res, ex₂⟩, ms'⟩, hcr, hx⟩ := hx
    obtain ⟨hg', hst_eq⟩ := runCellDF_onCr_inv P Dh encPt encT lam Q ex ex₂ ms ms' res
      hInv.hgame hcr
    rcases res with _ | fig8st <;>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', hInv0.hkept, hInv0.hchains, hInv0.hhonest⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; refine ⟨hg', ?_, ?_, hInv0.hhonest⟩
      · intro R; dsimp only; by_cases hR : R = Q
        · subst hR; simp only [Function.update_self, hst_eq fig8st rfl]
          exact (keptInv_ofSt (hInv.hgame.hparty R)).mono (Nat.mul_le_mul_left 25000 (by omega))
        · simp only [Function.update_of_ne hR]; exact hInv0.hkept R
      · intro R g hg; dsimp only at hg
        by_cases hB0 : (Q == Party.B && sC.base.mir.epoch Party.B == 0) = true <;>
          simp only [hB0, ↓reduceIte, Bool.false_eq_true] at hg
        · rcases hγ : fig8st.γ with _ | x <;> simp only [hγ] at hg
          · exact hInv0.hchains R g hg
          · by_cases hR : R = .A
            · subst hR; simp only [Function.update_self, List.mem_map] at hg
              obtain ⟨g₀, hg₀, rfl⟩ := hg; split_ifs <;> exact hInv0.hchains .A g₀ hg₀
            · simp only [Function.update_of_ne hR] at hg; exact hInv0.hchains R g hg
        · exact hInv0.hchains R g hg

private theorem simDeliverForgeOracleDedup_step_dfSanInv
    (decT : PublicKey → Option Pt) (B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : CellState Pt ℓ)
    (hInv : DFSanInv q (m + 1) sC ms.2) :
    ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar
        ((simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B (.inr t)).run (sC, ex)) ms),
      DFSanInv q m x.1.2.1 x.2.2 := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_dfSanInv P Dh encPt encT lam sC ex ms Q m₀ none r hInv
  · exact semSendHook_dfSanInv P Dh encPt encT lam sC ex ms Q m₀ (some m₁) r hInv
  · have hstep : ((simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B
        (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, ex)) =
      semRecvHook P Dh encPt encT decT lam
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w true := by
      dsimp only [simDeliverForgeOracleDedup, StateT.run, StateT.mk, semHandleHookDedup]
      have hpost : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDeliverPost =
          fun _ _ _ ex' => pure ex' := rfl
      rw [hpost]; simp only [pure_bind, Prod.mk.eta, bind_pure]
    rw [hstep]
    exact semRecvHook_dfSanInv P Dh encPt encT lam decT B sC ex ms Q w true hInv
  · exact semRecvHook_dfSanInv P Dh encPt encT lam decT B sC ex ms Q w false hInv
  · exact semCorrHookDedup_dfSanInv P Dh encPt encT lam sC ex ms Q hInv

omit [SampleableType PQC] in
private theorem simulateQ_runCellDF_eq_of_inv
    (O₁ O₂ : QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt))
        (AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))))
    (hinl₁ : ∀ n, O₁ (.inl n) = StateT.lift (query (spec := unifSpec +
      specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)))
    (hinl₂ : ∀ n, O₂ (.inl n) = StateT.lift (query (spec := unifSpec +
      specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n)))
    (hstepEq : ∀ m' t sC ex ms, DFSanInv q (m' + 1) sC ms.2 →
      runCellDF P Dh encPt encT lam qep tL tStar ((O₁ (.inr t)).run (sC, ex)) ms =
        runCellDF P Dh encPt encT lam qep tL tStar ((O₂ (.inr t)).run (sC, ex)) ms)
    (hstepInv : ∀ m' t sC ex ms, DFSanInv q (m' + 1) sC ms.2 →
      ∀ x ∈ support (runCellDF P Dh encPt encT lam qep tL tStar ((O₂ (.inr t)).run (sC, ex)) ms),
        DFSanInv q m' x.1.2.1 x.2.2)
    {α : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes) α)
    (m : ℕ) (hq : oa.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : CellState Pt ℓ)
    (hInv : DFSanInv q m sC ms.2) :
    runCellDF P Dh encPt encT lam qep tL tStar ((simulateQ O₁ oa).run (sC, ex)) ms =
      runCellDF P Dh encPt encT lam qep tL tStar ((simulateQ O₂ oa).run (sC, ex)) ms := by
  induction oa using OracleComp.inductionOn generalizing m sC ex ms with
  | pure a => simp only [runCellDF, simulateQ_pure, StateT.run_pure]
  | query_bind q_in mx ih =>
    have hq' := (isQueryBoundP_query_bind_iff _ q_in mx m).mp hq
    dsimp only [runCellDF] at hstepEq hstepInv ⊢
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases q_in with n | t
    · have hinl : (cellImplDF P Dh encPt encT lam qep tL tStar (.inl n)).run ms =
          (query (spec := unifSpec) n >>= fun u => pure (u, ms)) :=
        cellImplDF_inl P Dh encPt encT lam qep tL tStar n ms
      rw [hinl₁ n, hinl₂ n]
      simp only [stateT_lift_run, query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_bind, simulateQ_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        hinl, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u m (by simpa [isGameQuery] using hq'.2 u) sC ex ms hInv
    · have hm_pos : 0 < m := by simpa [isGameQuery] using hq'.1
      rcases m with _ | m'
      · omega
      rw [hstepEq m' t sC ex ms hInv]
      exact bind_congr_of_forall_mem_support _ fun x hx =>
        ih x.1.1 m' (by simpa [isGameQuery] using hq'.2 x.1.1) x.1.2.1 x.1.2.2 x.2
          (hstepInv m' t sC ex ms hInv x hx)

private theorem simulateQ_runCellDF_simDeliverForgeOracleSan_eq
    (decT : PublicKey → Option Pt) (B T Kc Bsk : ℕ) {α : Type}
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes) α)
    (m : ℕ) (hq : oa.IsQueryBoundP
      (isGameQuery (G := CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) (ms : CellState Pt ℓ)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk)
    (hInv : DFSanInv q m sC ms.2) :
    runCellDF P Dh encPt encT lam qep tL tStar
      ((simulateQ (simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk) oa).run
        (sC, ex)) ms =
    runCellDF P Dh encPt encT lam qep tL tStar
      ((simulateQ (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B) oa).run
        (sC, ex)) ms := by
  refine simulateQ_runCellDF_eq_of_inv P Dh encPt encT lam _ _ (fun _ => rfl) (fun _ => rfl)
    (fun m' t sC ex ms hInv' => ?_)
    (fun m' t sC ex ms hInv' =>
      simDeliverForgeOracleDedup_step_dfSanInv P Dh encPt encT lam decT B t sC ex ms hInv')
    oa m hq sC ex ms hInv
  have hm1 : m' + 1 ≤ q := hInv'.hgame.hm
  rcases t with t₀ | Q
  · rw [simDeliverForgeOracleSan_inr_inl_eq P Dh encPt encT decT lam qep t₀ (sC, ex)
      (B0 := 25000 * (q - (m' + 1))) (by omega) hInv'.hkept (by omega)
      (fun R g hg => by have := hInv'.hchains R g hg; omega)]
  · refine simDeliverForgeOracleSan_inr_inr_eq_of_support P Dh encPt encT decT lam qep Q
      (sC, ex) (cellImplDF P Dh encPt encT lam qep tL tStar) ms
      fun x hx fig8st hres t_ep v hv => ?_
    rcases x with ⟨⟨res, ex'⟩, ms'⟩
    obtain ⟨-, hst_eq⟩ := runCellDF_onCr_inv P Dh encPt encT lam Q ex ex' ms ms' res
      hInv'.hgame hx
    rw [hst_eq fig8st hres] at hv
    exact ((hInv'.hgame.hparty Q).2 t_ep v hv).mono (by omega)

end HookSanInv

/-- Sanitized-to-clamped oracle coupling in `runBaseDFCellTPaper` under `25000 * q ≤ T`,
`25001 * q + 25000 ≤ Kc`, and `25000 * q ≤ Bsk`. -/
theorem runBaseDFCellTPaper_challSimDF'Paper_simDeliverForgeClampSan_eq
    {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) (tL : Option ℕ) (t : ℕ)
    (idOf : Party → IdentityKey)
    (hid : idOf = fun R => if R == Party.A then P.idA else P.idB)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hT : 25000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    runBaseDFCellTPaper fig (qep + 1) tL t
        sameHdrScheme (Config.auth t) false
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A)) =
      runBaseDFCellTPaper fig (qep + 1) tL t
        sameHdrScheme (Config.auth t) false
        (challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForgeClamp P Dh encPt encT decT lam qep B A)) := by
  subst hid; dsimp only
  have hClamp : simDeliverForgeClamp P Dh encPt encT decT lam qep B A =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
            (BitVec 256))
        let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        (simulateQ (simDeliverForgeOracleDedup P Dh encPt encT decT lam qep B) A).run' (sC₀, [])) := by
    unfold simDeliverForgeClamp
    exact bind_congr fun pqrKey =>
      (run'_simulateQ_simDeliverForgeOracleDedup_eq_public P Dh encPt encT decT lam qep B A _).symm
  rw [hClamp, runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF,
    runBaseDFCellTPaper_challSimDF'Paper_eq_runCellDF]
  refine bind_congr fun k => bind_congr fun b => ?_
  unfold simDeliverForgeClampSan
  simp only [runCellDF, simulateQ_bind, StateT.run_bind, cellImplDF_liftM_probComp,
    StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, simulateQ_pure, StateT.run_pure,
    bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  have h1 := simulateQ_runCellDF_simDeliverForgeOracleSan_eq (q := q) (qep := qep) (tL := tL)
    (tStar := t) P Dh encPt encT lam decT B T Kc Bsk A q
    ((makesAtMostQueries_iff_isGameQuery A q).mp hq)
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) []
    ({ st := fun _ => (), b := b },
      initState (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam) k false)
    hT hKc hBsk (dfSanInv_init P Dh encPt encT lam q k pqrKey false)
  dsimp only [runCellDF] at h1
  rw [h1]

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanGame
