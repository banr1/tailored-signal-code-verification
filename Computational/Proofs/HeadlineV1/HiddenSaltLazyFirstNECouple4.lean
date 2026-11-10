/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple3
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyWire
import ProofLib.SepLogic.WP.StateNorm

/-!
# Per-Query Cell-Family Step Infrastructure

**Checked by Lean.** Defines single-step cell execution `runCellStep`, proves that `CellK4Doomed`
cells win with probability zero under `cellSimRun`, and provides query-bind decomposition and
double-sum step lemmas across cells.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem cellSimRun_bind {α β : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (ob : α → OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (oa >>= ob) sC sent m' s =
      (cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa sC sent m' s >>=
        fun z => cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (ob z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2) := by
  simp only [cellSimRun, simulateQ_bind, StateT.run_bind]

/-! ## Doomed-cell zero-probability lemmas -/

theorem fullImplBaseDFCellPaper_state_eq_of_win_true {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (q_df : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain)
    {s : SM.GameState St Msg C} (hswin : s.win = true)
    {z : (unifSpec + DeliverForge.specDF St Msg Coins C).Range q_df × SM.GameState St Msg C}
    (hz : z ∈ support ((fullImplBaseDFCellPaper sm (qep + 1) sameHdr tL t
      (SM.Config.auth t) q_df).run s)) :
    z.2 = s := by
  rcases q_df with q_u | q_rest
  · simp only [fullImplBaseDFCellPaper, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, StateT.run_liftM, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨x, _, hzx⟩; rw [hzx]
  · rcases q_rest with q_sm | ⟨Q, c, c'⟩
    · rcases q_sm with (((⟨P, m_msg, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | P
      · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
          SM.transmitImpl, hswin] at hz; exact congrArg Prod.snd hz
      · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
          SM.challImpl, hswin] at hz; exact congrArg Prod.snd hz
      · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
          SM.deliverImpl, hswin] at hz; exact congrArg Prod.snd hz
      · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
          injectImplCell, hswin] at hz; exact congrArg Prod.snd hz
      · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
          corrImplShiftedPaper, hswin] at hz; exact congrArg Prod.snd hz
    · simp [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper,
        deliverForgeBaseImplCell, hswin] at hz; exact congrArg Prod.snd hz

theorem simulateQ_fullImplBaseDFCellPaper_state_eq_of_win_true
    {α Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ)
    (oa : OracleComp (unifSpec + DeliverForge.specDF St Msg Coins C) α) :
    ∀ (s : SM.GameState St Msg C) (z : α × SM.GameState St Msg C),
      z ∈ support ((simulateQ (fullImplBaseDFCellPaper sm (qep + 1) sameHdr tL t
        (SM.Config.auth t)) oa).run s) →
      s.win = true →
      z.2 = s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  | query_bind q_df u ih =>
    intro s z hz hswin
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u₁, s₁⟩, h₁, h₂⟩
    have hs₁ : s₁ = s := fullImplBaseDFCellPaper_state_eq_of_win_true sm qep sameHdr tL t q_df
      hswin h₁
    rw [hs₁] at h₂
    exact ih u₁ s z h₂ hswin

theorem CellK4Doomed.cellWinPred_eq_false {St Msg C : Type}
    {tL : Option ℕ} {t : ℕ} {g s : SM.GameState St Msg C}
    (h : CellK4Doomed tL t g s) :
    cellWinPred tL t s = false := by
  rcases h with ⟨ht2, htL, ⟨_, hmem_s⟩, _⟩
  have hB1 : 2 ≤ t ∧ tL = some (t - 2) := ⟨ht2, htL⟩
  unfold cellWinPred authOKDir2
  simp [hB1, hmem_s]

theorem evalDist_cellSimRun_cellWinPred_eq_zero_of_doomed {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {g s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hd : CellK4Doomed tL t g s) :
    𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa sC sent m' s >>=
      fun z => pure (cellWinPred tL t z.2)] {true} = 0 := by
  have hcongr :
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa sC sent m' s >>=
        fun z => pure (cellWinPred tL t z.2)] =
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa sC sent m' s >>=
        fun _ => (pure false : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    have hz_eq := simulateQ_fullImplBaseDFCellPaper_state_eq_of_win_true
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep DeliverForge.sameHdrScheme tL t _
      s z hz hd.2.2.2
    rw [hz_eq, hd.cellWinPred_eq_false]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

/-! ## Query-bind decomposition -/

theorem cellSimRun_inr_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ)
    (q_game : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (u : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr q_game) →
      OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr q_game) >>= u)
      sC sent m' s =
    (let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
     let fs := lFS P.C P.codec ℓ encT idOf 25000
     (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
         (SM.Config.auth t))
       ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
         (((LibsignalSimC.simImplC P encT decT qep fig fs (deliverForgeHook Pt ℓ) Dh
           (.inr q_game)).run sC).run sent)).run m')).run s >>=
     fun z =>
       cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2) := by
  rw [cellSimRun_bind]
  congr 1
  unfold cellSimRun
  simp only [simulateQ_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
    OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
    PFunctor.Obj.mk, id]
  simp only [id_map]

theorem simulateQ_cell_fig8ToDFImpl_corr_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Fig8C Pt))
    (Q : Party) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
        (SM.Config.auth t))
      ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        ((fig8ToDFImpl Pt ℓ (.inr (.inr Q))).run sent)).run m')).run s =
    if !(m'.corrAllowedPaper Q) then
      pure (((none, sent), m'), s)
    else
      ((corrImplShiftedPaper (cellShift tL t) Q).run s >>= fun z =>
        pure (((z.1, sent), if z.1.isSome then m'.afterCorr Q else m'), z.2)) := by
  rw [fig8ToDFImpl_corr_run]
  unfold DeliverForge.corrQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
      (SM.Config.auth t))
    ((DeliverForge.simCorrDFPaper Q).run m')).run s >>=
      fun p => pure (((p.1.1, sent), p.1.2), p.2)) = _
  unfold DeliverForge.simCorrDFPaper DeliverForge.corrQueryDF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hm : m'.corrAllowedPaper Q = true
  · simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT_run_lift,
      simulateQ_bind, simulateQ_HasQuery_query,
      StateT.run_bind, bind_assoc, pure_bind]
    change ((corrImplShiftedPaper (cellShift tL t) Q).run s >>= _) = _
    refine bind_congr fun z => ?_
    rcases z with ⟨res, s'⟩
    cases res <;> simp [StateT.run_set]
  · have hmF : m'.corrAllowedPaper Q = false := Bool.eq_false_iff.mpr hm
    simp [hmF]

theorem simulateQ_cell_fig8ToDFImpl_inject_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Fig8C Pt))
    (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
        (SM.Config.auth t))
      ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inr (Q, c))))).run sent)).run m')).run s =
    ((injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c)).run s >>=
      fun z =>
        let m₁' := match z.1 with
          | some (.accepted t' i' _) => m'.accept Q () ⟨Q.other, t', i'⟩
          | _ => m'
        pure (((z.1, sent), m₁'), z.2)) := by
  rw [fig8ToDFImpl_inject_run]
  unfold DeliverForge.injectQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
      (SM.Config.auth t))
    ((DeliverForge.simInjectDF (Q, c)).run m')).run s >>=
      fun p => pure (((p.1.1, sent), p.1.2), p.2)) = _
  unfold DeliverForge.simInjectDF DeliverForge.injectQueryDF
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query, bind_assoc]
  change ((injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c)).run s >>= _) = _
  refine bind_congr fun z => ?_
  rcases z with ⟨res, s'⟩
  rcases res with _ | (_ | ⟨t', i', m_opt⟩) <;> simp [StateT.run_set]

theorem simulateQ_cell_fig8ToDFImpl_deliver_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Fig8C Pt))
    (Q : Party) (c : Fig8C Pt) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
        (SM.Config.auth t))
      ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inr (Q, c)))))).run sent)).run m')).run s =
    ((SM.deliverImpl fig (SM.Config.auth t) (Q, c)).run s >>=
      fun z =>
        match z.1, m'.inTransit Q.other c with
        | some (.accepted t' i' m), some r =>
          pure (((some (.accepted t' i' (if r.pos ∈ m'.chall then none else m)), sent),
            m'.accept Q () r.pos), z.2)
        | res, _ => pure (((res, sent), m'), z.2)) := by
  rw [fig8ToDFImpl_deliver_run]
  unfold DeliverForge.deliverQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
      (SM.Config.auth t))
    ((DeliverForge.simDeliverDF (Q, c)).run m')).run s >>=
      fun p => pure (((p.1.1, sent), p.1.2), p.2)) = _
  unfold DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query, bind_assoc]
  change ((SM.deliverImpl fig (SM.Config.auth t) (Q, c)).run s >>= _) = _
  refine bind_congr fun z => ?_
  rcases z with ⟨res, s'⟩
  rcases res with _ | (_ | ⟨t', i', m_opt⟩)
  · simp
  · simp
  · cases htr : m'.inTransit Q.other c <;> simp [StateT.run_set]

theorem simulateQ_cell_deliverForgeHook_probe_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Fig8C Pt))
    (Q : Party) (c' : Fig8C Pt) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
        (SM.Config.auth t))
      ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        (((deliverForgeHook Pt ℓ).probe Q c').run sent)).run m')).run s =
    match sent.find? (fun c => sameWireFig8 c c') with
    | some c =>
        ((deliverForgeBaseImplCell fig (qep + 1) tL t DeliverForge.sameHdrScheme
            (SM.Config.auth t) (Q, c, c')).run s >>=
          fun z =>
            let m₁' := match z.1 with
              | some (.accepted t' i' _) => m'.accept Q () ⟨Q.other, t', i'⟩
              | _ => m'
            pure ((((), sent), m₁'), z.2))
    | none => pure ((((), sent), m'), s) := by
  rw [deliverForgeHook_probe_run]
  cases hfind : sent.find? (fun c => sameWireFig8 c c') with
  | none =>
    simp [simulateQ_pure, StateT.run_pure]
  | some c =>
    dsimp only
    unfold DeliverForge.deliverForgeQuery
    simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
      StateT.run_bind, StateT.run_pure]
    change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
        (SM.Config.auth t))
      ((DeliverForge.simDeliverForgeDF (Q, c, c')).run m')).run s >>=
        fun p => pure ((((), sent), p.1.2), p.2)) = _
    unfold DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
      simulateQ_bind, simulateQ_HasQuery_query, bind_assoc]
    change ((deliverForgeBaseImplCell fig (qep + 1) tL t DeliverForge.sameHdrScheme
        (SM.Config.auth t) (Q, c, c')).run s >>= _) = _
    refine bind_congr fun z => ?_
    rcases z with ⟨res, s'⟩
    rcases res with _ | (_ | ⟨t', i', m_opt⟩) <;> simp [StateT.run_set]

theorem simulateQ_cell_fig8ToDFImpl_transmit_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Fig8C Pt))
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r_opt : Option (BitVec 256))
    (sent : List (Fig8C Pt)) (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
        (SM.Config.auth t))
      ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inl (Q, m, r_opt))))))).run sent)).run
          m')).run s =
    ((SM.transmitImpl fig (cellDelta tL t) (qep + 1) (Q, m, none)).run s >>=
      fun z =>
        let sent₁ := match z.1 with | some c => c :: sent | none => sent
        let m₁' := match z.1, m'.epMgmt (2 + 1) (qep + 1) Q false with
          | some c, some m₁ =>
            m₁.record (2 + 1) Q () ⟨⟨Q, m₁.epoch Q, m₁.idx Q + 1⟩, m, c⟩ false
          | _, _ => m'
        pure (((z.1, sent₁), m₁'), z.2)) := by
  rw [fig8ToDFImpl_transmit_run]
  unfold DeliverForge.transmitQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  unfold DeliverForge.simImplDF'Paper DeliverForge.simOraclesDF'Paper
  dsimp only [HAdd.hAdd, Add.add, QueryImpl.add]
  unfold DeliverForge.simTransmitDF'Paper DeliverForge.transmitQueryDF
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query, bind_assoc]
  change ((SM.transmitImpl fig (cellDelta tL t) (qep + 1) (Q, m, none)).run s >>= _) = _
  refine bind_congr fun z => ?_
  rcases z with ⟨res, s'⟩
  rcases res with _ | c <;> cases hep : m'.epMgmt (2 + 1) (qep + 1) Q false <;>
    simp [StateT.run_set]

theorem simulateQ_cell_fig8ToDFImpl_chall_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (Fig8C Pt))
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (r_opt : Option (BitVec 256))
    (sent : List (Fig8C Pt)) (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme tL t
        (SM.Config.auth t))
      ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
        ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r_opt))))))).run sent)).run
          m')).run s =
    match m'.epMgmt (2 + 1) (qep + 1) Q false with
    | none => pure (((none, sent), m'), s)
    | some m₁' =>
      if !(m₁'.safeCh (2 + 1) Q) then
        pure (((none, sent), m'), s)
      else
        let m_ch := if m'.b then m₁ else m₀
        ((SM.transmitImpl fig (cellDelta tL t) (qep + 1) (Q, m_ch, none)).run s >>=
          fun z =>
            match z.1 with
            | some c =>
              pure (((some c, c :: sent),
                m₁'.record (2 + 1) Q () ⟨⟨Q, m₁'.epoch Q, m₁'.idx Q + 1⟩, m_ch, c⟩ true), z.2)
            | none => pure (((none, sent), m'), z.2)) := by
  rw [fig8ToDFImpl_chall_run]
  unfold DeliverForge.challQueryDF
  simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  unfold DeliverForge.simImplDF'Paper DeliverForge.simOraclesDF'Paper
  dsimp only [HAdd.hAdd, Add.add, QueryImpl.add]
  unfold DeliverForge.simChallDF'Paper DeliverForge.transmitQueryDF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hep : m'.epMgmt (2 + 1) (qep + 1) Q false with
  | none =>
    simp [simulateQ_pure, StateT.run_pure]
  | some m₁' =>
    dsimp only
    by_cases hcond : m₁'.safeCh (2 + 1) Q = true
    · simp only [hcond, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT_run_lift, simulateQ_bind, simulateQ_HasQuery_query, bind_assoc, pure_bind]
      change ((SM.transmitImpl fig (cellDelta tL t) (qep + 1)
          (Q, if m'.b then m₁ else m₀, none)).run s >>= _) = _
      refine bind_congr fun z => ?_
      rcases z with ⟨res, s'⟩
      rcases res with _ | c <;> simp [StateT.run_set]
    · have hcondF : m₁'.safeCh (2 + 1) Q = false := Bool.eq_false_iff.mpr hcond
      simp [hcondF, simulateQ_pure, StateT.run_pure]

/-! ## Single-step cell execution -/

theorem sum_cellSimRun_le_of_doomed_or_eq {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa_pre oa_post : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (sent sent₁ : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hcells : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      CellK4Doomed tL t g₁ (s_cell₁ t tL) ∨
      cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC sent m' (s_cell t tL) =
        cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_post sC₁ sent₁ m₁'
          (s_cell₁ t tL)) :
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_post sC₁ sent₁ m₁'
          (s_cell₁ t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa_pre sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun tL htL => ?_
  rcases hcells t ht tL htL with hdoomed | heq
  · rw [evalDist_cellSimRun_cellWinPred_eq_zero_of_doomed P ℓ Dh encPt encT decT idOf lam qep
      t tL oa_post sC₁ sent₁ m₁' hdoomed]
    exact zero_le
  · rw [heq]

/-- Executes one simulator step inside the `(t, tL)` paper reduction cell. -/
noncomputable def runCellStep {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ)
    (mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp ((((α × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :=
  (simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
      tL t (SM.Config.auth t))
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((mDF.run sC).run sent)).run m')).run s_cell

theorem runCellStep_pure {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (a : α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL (pure a) sC sent m' s_cell =
      pure ((((a, sC), sent), m'), s_cell) := by
  unfold runCellStep
  simp only [StateT.run_pure, simulateQ_pure]

theorem runCellStep_bind {PQ Pt α β : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ)
    (mDF : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) α)
    (kDF : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL (mDF >>= kDF) sC sent m' s_cell =
      (runCellStep fig qep t tL mDF sC sent m' s_cell >>= fun z =>
        runCellStep fig qep t tL (kDF z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2) := by
  unfold runCellStep
  simp only [StateT.run_bind, simulateQ_bind]

theorem runCellStep_get {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL get sC sent m' s_cell =
      pure ((((sC, sC), sent), m'), s_cell) := by
  unfold runCellStep
  simp only [StateT.run_get, StateT.run_pure, simulateQ_pure]

theorem runCellStep_set {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL (set sC') sC sent m' s_cell =
      pure (((((), sC'), sent), m'), s_cell) := by
  unfold runCellStep
  simp only [StateT.run_set, StateT.run_pure, simulateQ_pure]

theorem runCellStep_modify {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL (modify f) sC sent m' s_cell =
      pure (((((), f sC), sent), m'), s_cell) := by
  unfold runCellStep
  simp only [StateT.run_modify, StateT.run_pure, simulateQ_pure]

theorem runCellStep_liftC {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (x : Fig8Comp Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) x) sC sent m' s_cell =
      ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
          tL t (SM.Config.auth t))
        ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
          ((simulateQ (fig8ToDFImpl Pt ℓ) x).run sent)).run m')).run s_cell >>= fun z =>
        pure ((((z.1.1.1, sC), z.1.1.2), z.1.2), z.2)) := by
  unfold runCellStep LibsignalSimC.liftC deliverForgeHook
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]

theorem runCellStep_zoomB {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ) x) sC sent m' s_cell =
      ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
          tL t (SM.Config.auth t))
        ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
          ((simulateQ (fig8ToDFImpl Pt ℓ) (x.run sC.base)).run sent)).run m')).run s_cell >>=
        fun z => pure ((((z.1.1.1.1, { sC with base := z.1.1.1.2 }), z.1.1.2), z.1.2), z.2)) := by
  unfold runCellStep
  rw [zoomB_deliverForgeHook_run]
  simp only [deliverForgeHook, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]

theorem runCellStep_simCorrC_refused {PQ PQC Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ PQC) (encT : Pt → PublicKey) (Dh : DHFun (BitVec 256) Pt)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (href : sC.base.stopped = true ∨
      (((sC.base.mir.win || !sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q) ||
        !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT (deliverForgeHook Pt ℓ) Dh Q))
      sC sent m' s_cell =
      pure ((((none, sC), sent), m'), s_cell) := by
  unfold LibsignalSimC.guardC LibsignalSimC.simCorrC
  rcases href with h1 | h2
  · simp only [runCellStep_bind, runCellStep_get, pure_bind, h1, ↓reduceIte, runCellStep_pure]
  · by_cases h1 : sC.base.stopped = true
    · simp only [runCellStep_bind, runCellStep_get, pure_bind, h1, ↓reduceIte, runCellStep_pure]
    · simp only [runCellStep_bind, runCellStep_get, pure_bind, h1, Bool.false_eq_true, ↓reduceIte,
        h2, runCellStep_pure]

theorem firstNESimImpl_corr_refused
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool) (tr : KemFailTrackState P.C.F)
    (href : sC.base.stopped = true ∨
      (((sC.base.mir.win || !sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q) ||
        !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = true) :
    (firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inr (.inr Q))).run
      (sC, (g, fl), tr) =
      pure (none, (sC, (g, fl), tr)) := by
  change (runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q))).run
    (sC, (g, fl), tr) = _
  rw [runProbeStep_run]
  unfold LibsignalSimC.guardC LibsignalSimC.simCorrC
  rcases href with h1 | h2
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, h1, ↓reduceIte, StateT.run_pure]
  · by_cases h1 : sC.base.stopped = true
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, h1, ↓reduceIte, StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, h1, Bool.false_eq_true, ↓reduceIte,
        h2, StateT.run_pure]

theorem runCellStep_liftC_corr {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (SM.corrQuery Q)) sC sent m' s_cell =
      if !(m'.corrAllowedPaper Q) then
        pure ((((none, sC), sent), m'), s_cell)
      else
        ((corrImplShiftedPaper (cellShift tL t) Q).run s_cell >>= fun z =>
          pure ((((z.1, sC), sent), if z.1.isSome then m'.afterCorr Q else m'), z.2)) := by
  rw [runCellStep_liftC]
  unfold SM.corrQuery
  simp only [simulateQ_HasQuery_query]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
      tL t (SM.Config.auth t))
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((fig8ToDFImpl Pt ℓ (.inr (.inr Q))).run sent)).run m')).run s_cell >>= _) = _
  rw [simulateQ_cell_fig8ToDFImpl_corr_run]
  split_ifs <;> simp

theorem runCellStep_liftC_inject {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (c : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (SM.injectQuery Q c)) sC sent m' s_cell =
      ((injectImplCell fig (qep + 1) tL t (SM.Config.auth t) (Q, c)).run s_cell >>=
        fun z =>
          let m₁' := match z.1 with
            | some (.accepted t' i' _) => m'.accept Q () ⟨Q.other, t', i'⟩
            | _ => m'
          pure ((((z.1, sC), sent), m₁'), z.2)) := by
  rw [runCellStep_liftC]
  unfold SM.injectQuery
  simp only [simulateQ_HasQuery_query]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
      tL t (SM.Config.auth t))
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inr (Q, c))))).run sent)).run m')).run s_cell >>= _) = _
  rw [simulateQ_cell_fig8ToDFImpl_inject_run]
  simp

theorem runCellStep_liftC_deliver {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (c : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (SM.deliverQuery Q c)) sC sent m' s_cell =
      ((SM.deliverImpl fig (SM.Config.auth t) (Q, c)).run s_cell >>=
        fun z =>
          match z.1, m'.inTransit Q.other c with
          | some (.accepted t' i' m), some r =>
            pure ((((some (.accepted t' i' (if r.pos ∈ m'.chall then none else m)), sC), sent),
              m'.accept Q () r.pos), z.2)
          | res, _ => pure ((((res, sC), sent), m'), z.2)) := by
  rw [runCellStep_liftC]
  unfold SM.deliverQuery
  simp only [simulateQ_HasQuery_query]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
      tL t (SM.Config.auth t))
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inr (Q, c)))))).run sent)).run m')).run
      s_cell >>= _) = _
  rw [simulateQ_cell_fig8ToDFImpl_deliver_run]
  simp only [bind_assoc]
  refine bind_congr fun z => ?_
  rcases z with ⟨res, s'⟩
  rcases res with _ | (_ | ⟨t', i', m⟩)
  · simp
  · simp
  · cases m'.inTransit Q.other c <;> simp

theorem runCellStep_liftC_transmit {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r_opt : Option (BitVec 256))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (SM.transmitQuery Q m r_opt))
      sC sent m' s_cell =
      ((SM.transmitImpl fig (cellDelta tL t) (qep + 1) (Q, m, none)).run s_cell >>=
        fun z =>
          let sent₁ := match z.1 with | some c => c :: sent | none => sent
          let m₁' := match z.1, m'.epMgmt (2 + 1) (qep + 1) Q false with
            | some c, some m₁ =>
              m₁.record (2 + 1) Q () ⟨⟨Q, m₁.epoch Q, m₁.idx Q + 1⟩, m, c⟩ false
            | _, _ => m'
          pure ((((z.1, sC), sent₁), m₁'), z.2)) := by
  rw [runCellStep_liftC]
  unfold SM.transmitQuery
  simp only [simulateQ_HasQuery_query]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
      tL t (SM.Config.auth t))
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inl (Q, m, r_opt))))))).run sent)).run
        m')).run s_cell >>= _) = _
  rw [simulateQ_cell_fig8ToDFImpl_transmit_run]
  simp

theorem runCellStep_liftC_chall {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ)
    (r_opt : Option (BitVec 256))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (SM.challQuery Q m₀ m₁ r_opt))
      sC sent m' s_cell =
      match m'.epMgmt (2 + 1) (qep + 1) Q false with
      | none => pure ((((none, sC), sent), m'), s_cell)
      | some m₁' =>
        if !(m₁'.safeCh (2 + 1) Q) then
          pure ((((none, sC), sent), m'), s_cell)
        else
          let m_ch := if m'.b then m₁ else m₀
          ((SM.transmitImpl fig (cellDelta tL t) (qep + 1) (Q, m_ch, none)).run s_cell >>=
            fun z =>
              match z.1 with
              | some c =>
                pure ((((some c, sC), c :: sent),
                  m₁'.record (2 + 1) Q () ⟨⟨Q, m₁'.epoch Q, m₁'.idx Q + 1⟩, m_ch, c⟩ true), z.2)
              | none => pure ((((none, sC), sent), m'), z.2)) := by
  rw [runCellStep_liftC]
  unfold SM.challQuery
  simp only [simulateQ_HasQuery_query]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
      tL t (SM.Config.auth t))
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((fig8ToDFImpl Pt ℓ (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r_opt))))))).run sent)).run
        m')).run s_cell >>= _) = _
  rw [simulateQ_cell_fig8ToDFImpl_chall_run]
  cases m'.epMgmt (2 + 1) (qep + 1) Q false with
  | none => simp
  | some m₁' =>
    dsimp only
    by_cases hcond : m₁'.safeCh (2 + 1) Q = true
    · simp only [hcond, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
      refine bind_congr fun z => ?_
      rcases z with ⟨res, s'⟩
      rcases res with _ | c <;> simp
    · have hcondF : m₁'.safeCh (2 + 1) Q = false := Bool.eq_false_iff.mpr hcond
      simp [hcondF]

theorem runCellStep_liftC_liftM {α PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (p : ProbComp α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (liftM p : Fig8Comp Pt ℓ α))
      sC sent m' s_cell =
      (p >>= fun u => pure ((((u, sC), sent), m'), s_cell)) := by
  rw [runCellStep_liftC]
  change ((simulateQ (fullImplBaseDFCellPaper fig (qep + 1) DeliverForge.sameHdrScheme
      tL t (SM.Config.auth t))
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      (((deliverForgeHook Pt ℓ).lift (liftM p)).run sent)).run m')).run s_cell >>= _) = _
  rw [deliverForgeHook_lift_liftM_run]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    simulateQ_simImplDF'Paper_liftM_probComp,
    simulateQ_fullImplBaseDFCellPaper_liftM_probComp, bind_assoc, pure_bind]

theorem runCellStep_guardC_stopped_true {α PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ)
    (act : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) (Option α))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : sC.base.stopped = true) :
    runCellStep fig qep t tL (LibsignalSimC.guardC act) sC sent m' s_cell =
      pure ((((none, sC), sent), m'), s_cell) := by
  unfold LibsignalSimC.guardC
  rw [runCellStep_bind, runCellStep_get]
  simp only [pure_bind, hstop, ↓reduceIte, runCellStep_pure]

theorem runCellStep_guardC_stopped_false {α PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ)
    (act : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (DeliverForgeM Pt ℓ) (Option α))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : sC.base.stopped = false) :
    runCellStep fig qep t tL (LibsignalSimC.guardC act) sC sent m' s_cell =
      runCellStep fig qep t tL act sC sent m' s_cell := by
  unfold LibsignalSimC.guardC
  rw [runCellStep_bind, runCellStep_get]
  simp only [pure_bind, hstop, Bool.false_eq_true, ↓reduceIte]

def corrStepChains {PQ Pt : Type} {ℓ : ℕ} (encT : Pt → PublicKey) (Dh : DHFun (BitVec 256) Pt)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) : Party → List GhostChain :=
  if Q == Party.B && s.mir.epoch Party.B == 0 then
    match st.γ with
    | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
        if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
    | _ => s.chains
  else s.chains

def corrStepGhost {PQ PQC Pt : Type} {ℓ : ℕ} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (Dh : DHFun (BitVec 256) Pt) (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) :
    GhostState PQ :=
  toGhost (P := P) { s with chains := corrStepChains encT Dh s Q st } Q st

def corrStepStateC {PQ PQC Pt : Type} {ℓ : ℕ} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (Dh : DHFun (BitVec 256) Pt) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt) :
    LibsignalToModularSchemeSimState PQ Pt ℓ :=
  let s := sC.base
  let chains := corrStepChains encT Dh s Q st
  let g := corrStepGhost P encT Dh s Q st
  { sC with base := { s with mir := s.mir.afterCorr Q, chains },
            kept := Function.update sC.kept Q (Kept.ofSt st),
            snaps := (Q, s.mir.epoch Q, g) :: sC.snaps }

theorem runCellStep_simCorrC_accepted {PQ PQC Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (P : Params PQ PQC) (encT : Pt → PublicKey) (Dh : DHFun (BitVec 256) Pt)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : sC.base.stopped = false)
    (href : (((sC.base.mir.win || !sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q) ||
      !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = false)
    (hallow_m : m'.corrAllowedPaper Q = true) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT (deliverForgeHook Pt ℓ) Dh Q))
      sC sent m' s_cell =
      ((corrImplShiftedPaper (cellShift tL t) Q).run s_cell >>= fun z =>
        match z.1 with
        | none => pure ((((none, sC), sent), m'), z.2)
        | some st =>
          pure ((((some (corrStepGhost P encT Dh sC.base Q st),
                    corrStepStateC P encT Dh sC Q st), sent), m'.afterCorr Q), z.2)) := by
  rw [runCellStep_guardC_stopped_false fig qep t tL _ sC sent m' s_cell hstop]
  unfold LibsignalSimC.simCorrC
  rw [runCellStep_bind, runCellStep_get, pure_bind]
  simp only [href, Bool.false_eq_true, ↓reduceIte]
  rw [runCellStep_bind, runCellStep_liftC_corr]
  simp only [hallow_m, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  refine bind_congr fun z => ?_
  rcases z with ⟨res, s'⟩
  rcases res with _ | st
  · exact runCellStep_pure fig qep t tL none sC sent m' s'
  · dsimp only
    rw [runCellStep_bind, runCellStep_set, pure_bind, runCellStep_pure]
    rfl

theorem corrImplShiftedPaper_run_eq {St Msg C : Type}
    (l : ℕ) (Q : Party) (s : SM.GameState St Msg C)
    (hwin : s.win = false) (hallow : s.corrAllowedPaper Q = true) :
    (corrImplShiftedPaper l Q).run s =
      pure (some (s.st Q), DeliverForge.afterCorrShifted l s Q) := by
  unfold corrImplShiftedPaper
  simp [hwin, hallow, StateT.run_bind, StateT.run_get, StateT.run_set]

theorem probeHook_liftC_corr_run {PQ Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (hwin_g : g.win = false) (hallow_g : g.corrAllowed Q = true) :
    ((LibsignalSimC.liftC (probeHook fig (qep + 1)) (SM.corrQuery Q)).run sC).run (g, fl) =
      pure ((some (g.st Q), sC), (g.afterCorr Q, fl)) := by
  unfold LibsignalSimC.liftC probeHook fig8ImplH1 SM.oracleImpl SM.corrQuery
  simp only [StateT_run_lift, simulateQ_HasQuery_query, StateT.run_bind, StateT.run_pure]
  change (((SM.corrImpl Q).run g >>= fun x => pure (x.1, (x.2, fl))) >>=
    fun p => pure ((p.1, sC), p.2)) = _
  unfold SM.corrImpl
  simp [hwin_g, hallow_g, StateT.run_bind, StateT.run_get, StateT.run_set]

theorem firstNESimImpl_corr_accepted {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool) (tr : KemFailTrackState P.C.F)
    (hstop : sC.base.stopped = false)
    (href : (((sC.base.mir.win || !sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q) ||
      !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = false)
    (hwin_g : g.win = false)
    (hallow_g : g.corrAllowed Q = true) :
    (firstNESimImpl P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inr (.inr Q))).run
      (sC, (g, fl), tr) =
      pure (some (corrStepGhost P encT Dh sC.base Q (g.st Q)),
        (corrStepStateC P encT Dh sC Q (g.st Q), (g.afterCorr Q, fl), tr)) := by
  change (runProbeStep P ℓ Dh encPt encT decT idOf lam qep
    (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
      (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q))).run
    (sC, (g, fl), tr) = _
  rw [runProbeStep_run]
  unfold LibsignalSimC.guardC LibsignalSimC.simCorrC
  rw [StateT.run_bind, StateT.run_get, pure_bind, hstop]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [StateT.run_bind, StateT.run_get, pure_bind, href]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [StateT.run_bind, StateT.run_bind, probeHook_liftC_corr_run _ qep Q sC g fl hwin_g hallow_g]
  simp only [pure_bind, StateT.run_bind, StateT.run_set, StateT.run_pure]
  rfl

theorem runCellStep_simCorrC_accepted_cell {PQ PQC Pt : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (P : Params PQ PQC) (encT : Pt → PublicKey) (Dh : DHFun (BitVec 256) Pt)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (Q : Party)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : sC.base.stopped = false)
    (href : (((sC.base.mir.win || !sC.base.mir.corrAllowed Q) || inReceiveOnlyEpoch sC.base.mir Q) ||
      !noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) = false)
    (hallow_m : m'.corrAllowedPaper Q = true)
    (hwin_df : s_cell.win = false)
    (hallow_df : s_cell.corrAllowedPaper Q = true)
    (hst : s_cell.st Q = g.st Q) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT (deliverForgeHook Pt ℓ) Dh Q))
      sC sent m' s_cell =
      pure ((((some (corrStepGhost P encT Dh sC.base Q (g.st Q)),
                corrStepStateC P encT Dh sC Q (g.st Q)), sent), m'.afterCorr Q),
        DeliverForge.afterCorrShifted (cellShift tL t) s_cell Q) := by
  rw [runCellStep_simCorrC_accepted P encT Dh fig qep t tL Q sC sent m' s_cell hstop href hallow_m,
    corrImplShiftedPaper_run_eq (cellShift tL t) Q s_cell hwin_df hallow_df, hst]
  simp only [pure_bind]

theorem cellSimRun_corr_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (Q : Party)
    (u : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inr Q)) →
      OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inr Q)) >>= u)
      sC sent m' s_cell =
    (runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT (deliverForgeHook Pt ℓ) Dh Q))
      sC sent m' s_cell >>=
     fun z =>
       cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
  cellSimRun_inr_query_bind P ℓ Dh encPt encT decT idOf lam qep t tL (.inr Q) u sC sent m' s_cell

theorem cellSimRun_inject_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inr (Q, w)))) →
      OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)
      sC sent m' s_cell =
    (runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Q w false))
      sC sent m' s_cell >>=
     fun z =>
       cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
  cellSimRun_inr_query_bind P ℓ Dh encPt encT decT idOf lam qep t tL (.inl (.inr (Q, w))) u
    sC sent m' s_cell

theorem cellSimRun_deliver_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC sent m' s_cell =
    (runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Q w true))
      sC sent m' s_cell >>=
     fun z =>
       cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
  cellSimRun_inr_query_bind P ℓ Dh encPt encT decT idOf lam qep t tL (.inl (.inl (.inr (Q, w)))) u
    sC sent m' s_cell

theorem cellSimRun_transmit_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) →
      OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)
      sC sent m' s_cell =
    (runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (deliverForgeHook Pt ℓ) Q m₀ none r))
      sC sent m' s_cell >>=
     fun z =>
       cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
  cellSimRun_inr_query_bind P ℓ Dh encPt encT decT idOf lam qep t tL
    (.inl (.inl (.inl (.inl (Q, m₀, r))))) u sC sent m' s_cell

theorem cellSimRun_chall_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) →
      OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>= u)
      sC sent m' s_cell =
    (runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (deliverForgeHook Pt ℓ)
        Q m₀ (some m₁) r))
      sC sent m' s_cell >>=
     fun z =>
       cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
         (u z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
  cellSimRun_inr_query_bind P ℓ Dh encPt encT decT idOf lam qep t tL
    (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) u sC sent m' s_cell

end CryptoVerification.LibsignalSession.HeadlineV1

end
