/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4
import Computational.Specifications.Pqxdh.Game
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# `SyncInv` Preservation Across `deliver` Steps

Proves `SyncInv` preservation across `deliver` queries and establishes the non-probe,
rejected-probe, and non-lazy-probe `FirstNECoupledInvD` step lemmas.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

variable (Pt : Type) [Zero Pt] [DecidableEq Pt] [SampleableType Pt]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem honestSentSync_updAmbSimStateC {PQ : Type} {ℓ : ℕ}
    (b : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (h : HonestSentSync Pt sC.base.honest sent) :
    HonestSentSync Pt (updAmbSimStateC Pt b sC).base.honest sent := by
  unfold updAmbSimStateC
  split_ifs <;> exact h

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem sameMeta_updAmbSimStateC {PQ : Type} {ℓ : ℕ}
    (b : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (h : SameMeta s_R sC.base g) :
    SameMeta s_R (updAmbSimStateC Pt b sC).base g := by
  unfold updAmbSimStateC
  split_ifs
  · cases h; constructor <;> assumption
  · exact h

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem keptInv_updAmbSimStateC {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (b : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : KeptInv P Dh encPt encT idOf lam sC g) :
    KeptInv P Dh encPt encT idOf lam (updAmbSimStateC Pt b sC) g := by
  unfold updAmbSimStateC
  split_ifs
  · cases h; constructor <;> assumption
  · exact h

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem syncInv_updAmbSimStateC {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (b : Bool) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : SyncInv P Dh encPt encT idOf lam qep sC sent m' g s_unsh) :
    SyncInv P Dh encPt encT idOf lam qep (updAmbSimStateC Pt b sC) sent m' g s_unsh := by
  rcases h with ⟨hmeta, hmir, hwf, hle, hep, hsnapIdx, hsnaps, hfig, hkept, hk, hid, hhon⟩
  refine ⟨fun hstop => ?_, hmir, hwf, hle, hep, ?_, ?_, hfig,
    corrsKeptRecvInv_updAmbSimStateC Pt b sC g hkept,
    keptInv_updAmbSimStateC Pt P Dh encPt encT idOf lam b sC g hk,
    hid, honestSentSync_updAmbSimStateC Pt b sC sent hhon⟩
  · rw [(updAmbSimStateC_fields Pt b sC).2.2.2.2.2] at hstop
    rcases hmeta hstop with ⟨s_R, hs_R⟩
    exact ⟨s_R, sameMeta_updAmbSimStateC Pt b sC hs_R⟩
  · rw [(updAmbSimStateC_fields Pt b sC).2.2.1]; exact hsnapIdx
  · rw [(updAmbSimStateC_fields Pt b sC).2.2.1]; exact hsnaps

omit [SampleableType Pt] in
theorem probeStep_of_guardC_pure {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (byDeliver : Bool)
    (sC sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ans : Option (RecvResult (Plain ℓ)))
    (hpure :
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (probeHook fig (qep + 1)) Q w byDeliver)).run sC = pure (ans, sC₁)) :
    (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (probeHook fig (qep + 1)) Q w byDeliver)).run sC).run (g, fl)) =
      pure ((ans, sC₁), (g, fl)) := by
  rw [hpure, StateT.run_pure]

omit [SampleableType Pt] in
theorem runCellStep_guardC_pure {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep t : ℕ)
    (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (byDeliver : Bool)
    (sC sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ)))
    (hpure : (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
      (deliverForgeHook Pt ℓ) Q w byDeliver)).run sC = pure (ans, sC₁)) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (deliverForgeHook Pt ℓ) Q w byDeliver))
      sC sent m' s_cell =
      pure ((((ans, sC₁), sent), m'), s_cell) := by
  rw [runCellStep_congr_run fig qep t tL _ (pure ans) sC sC₁ sent m' s_cell hpure,
    runCellStep_pure]

theorem runCellStep_probe_rejected_win {PQ : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep t' : ℕ) (tL : Option ℕ)
    (Q : Party) (c c' : Fig8C Pt)
    (r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (st' : Fig8St Pt) (i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {s_cell g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hrel : PPrimePaperRelShifted s_cell m' g)
    (hfind : sent.find? (fun c₀ => sameWireFig8 c₀ c') = some c)
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hin_g : g.inTransit Q.other c = some r)
    (hnone_g : (g.inTransit Q.other c').isSome = false)
    (hcomp_df : s_cell.comp.contains r.pos = false)
    (hhdr : DeliverForge.sameHdrScheme c c' = true)
    (hrcv_g : fig.receive (g.st Q) c' = some (st', t', i', m_out))
    (hr_pos : r.pos = ⟨Q.other, t', i'⟩)
    (htriv : s_cell.trivial (cellDelta tL t') ⟨Q.other, t', i'⟩ = false) :
    runCellStep fig qep t' tL
      (StateT.lift ((deliverForgeHook Pt ℓ).probe Q c') >>=
        fun _ => pure (some RecvResult.rejected : Option (RecvResult (Plain ℓ))))
      sC₀ sent m' s_cell =
      pure ((((some RecvResult.rejected, sC₀), sent), m'), { s_cell with win := true }) := by
  rw [runCellStep_bind]
  have h1 :
      runCellStep fig qep t' tL (StateT.lift ((deliverForgeHook Pt ℓ).probe Q c'))
        sC₀ sent m' s_cell =
        pure (((((), sC₀), sent), m'), { s_cell with win := true }) := by
    unfold runCellStep
    exact cellSimRun_deliverForgeHook_probe_win Pt fig qep t' tL Q c c' r st' i' m_out
      sC₀ sent m' hrel hfind ht'_le hin_g hnone_g hcomp_df hhdr hrcv_g hr_pos htriv
  rw [h1, pure_bind, runCellStep_pure]

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_probe_run
    {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep_lim : ℕ) (Q : Party) (c' : Fig8C Pt)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    ((probeHook fig qep_lim).probe Q c').run (g, fl) =
      pure ((), (g, fl || (fig.receive (g.st Q) c').isSome)) :=
  rfl

omit [Zero Pt] [SampleableType Pt] in
theorem updKeptOnRes_base_sent_snaps_eq {PQ : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (c : Fig8C Pt) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (updKeptOnRes fig fs Q c res sC).base = sC.base ∧
    (updKeptOnRes fig fs Q c res sC).sent = sC.sent ∧
    (updKeptOnRes fig fs Q c res sC).snaps = sC.snaps := by
  unfold updKeptOnRes
  cases res with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some r => cases r <;> exact ⟨rfl, rfl, rfl⟩

omit [Zero Pt] [SampleableType Pt] in
theorem updKeptOnRes_rejected {PQ : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (c : Fig8C Pt) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    updKeptOnRes fig fs Q c (some RecvResult.rejected) sC = sC :=
  rfl

theorem keptInv_updKeptOnRes_accept {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (Q : Party) (c' : Fig8C Pt) (st' : Fig8St Pt)
    (t' i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ) (pos : SM.Pos)
    (hk : KeptInv P Dh encPt encT idOf lam sC g)
    (hid : (g.st Q).id = Q)
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', t', i', m_out)) :
    KeptInv P Dh encPt encT idOf lam
      (updKeptOnRes (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) Q c' (some (.accepted t' i' m_out)) sC)
      (g.accept Q st' pos) :=
  keptInv_recv_accept hk Q hid c' st' (t', i', m_out) hfig rfl rfl

omit [DecidableEq Pt] [SampleableType Pt] in
theorem lFig8_receive_spec {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    {s st' : Fig8St Pt} {c' : Fig8C Pt} {t' i' : ℕ} {m_out : LibsignalMsgPublicPart × Plain ℓ}
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive s c' =
      some (st', t', i', m_out)) :
    s.id.sendsIn c'.1.1 = false ∧ t' = c'.1.1 ∧ st'.id = s.id ∧
    ((c'.1.1 = s.tcur + 1 ∧ st'.tcur = c'.1.1) ∨
      (c'.1.1 ≤ s.tcur ∧ st'.tcur = s.tcur ∧ st'.γ = s.γ ∧ st'.vS = s.vS ∧
        ∃ v v', s.vR c'.1.1 = some v ∧
          (lFS P.C P.codec ℓ encT idOf 25000).receive v c'.1 c'.2 = some (v', i', m_out))) := by
  change SM.Construction.receive (dhScheme Dh) (rootPRNG P.C.F encPt)
    (lFS P.C P.codec ℓ encT idOf 25000) s c' = some (st', t', i', m_out) at hfig
  unfold SM.Construction.receive at hfig
  dsimp only at hfig
  split_ifs at hfig with hcond hnew
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_lt] at hcond
    cases hT : c'.1.2 with
    | none => simp [hT] at hfig
    | some Tn =>
      simp only [hT, Function.update_self] at hfig
      rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive
          ((lFS P.C P.codec ℓ encT idOf 25000).initReceiver
            ((rootPRNG P.C.F encPt).up s.root ((dhScheme Dh).receive s.γ Tn).2).2)
          c'.1 c'.2 with _ | ⟨v', i₁, m₁⟩
      · simp [hfs] at hfig
      · simp only [hfs, Option.some.injEq, Prod.mk.injEq] at hfig
        rcases hfig with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨hcond.1, rfl, rfl, Or.inl ⟨hnew, rfl⟩⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_lt] at hcond
    cases hv : s.vR c'.1.1 with
    | none => simp [hv] at hfig
    | some v =>
      simp only [hv] at hfig
      rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c'.1 c'.2 with _ | ⟨v', i₁, m₁⟩
      · simp [hfs] at hfig
      · simp only [hfs, Option.some.injEq, Prod.mk.injEq] at hfig
        rcases hfig with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨hcond.1, rfl, rfl, Or.inr ⟨by omega, rfl, rfl, rfl, v, v', rfl, hfs⟩⟩

omit [SampleableType Pt] in
theorem corrsKeptRecvInv_updKeptOnRes_accept {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (Q : Party) (c' : Fig8C Pt) (st' : Fig8St Pt)
    (t' i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ) (pos : SM.Pos)
    (hk : KeptInv P Dh encPt encT idOf lam sC g)
    (hle : CorrsLeEpoch g)
    (htcur : (g.st Q).tcur = g.epoch Q)
    (hcorr : CorrsKeptRecvInv sC g)
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', t', i', m_out)) :
    CorrsKeptRecvInv
      (updKeptOnRes (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) Q c' (some (.accepted t' i' m_out)) sC)
      (g.accept Q st' pos) := by
  intro R e hmem t hte hsends
  change (R, e) ∈ g.corrs at hmem
  dsimp [updKeptOnRes]
  by_cases hRQ : R = Q
  · subst hRQ
    rw [Function.update_self]
    dsimp [Kept.recv]
    cases hfull : (sC.kept R).full with
    | some st =>
      have hst_eq : st = g.st R := hk.hfull R st hfull
      subst hst_eq
      simp [hfig]
    | none =>
      rcases hcorr R e hmem t hte hsends with hfull_some | hrs_some
      · simp [hfull] at hfull_some
      · right
        by_cases htc : t = c'.1.1
        · subst htc
          obtain ⟨v₀, hv₀⟩ := Option.isSome_iff_exists.mp hrs_some
          have hv₀_st : (g.st R).vR c'.1.1 = some v₀ := hk.hrs R c'.1.1 v₀ hfull hv₀
          have hle_ep : e ≤ g.epoch R := hle R e hmem
          have ht_le : c'.1.1 ≤ (g.st R).tcur := by omega
          rcases (lFig8_receive_spec Pt P Dh encPt encT idOf lam hfig).2.2.2 with
            ⟨hnew, _⟩ | ⟨_, _, _, _, v₁, v', hv₁, hfs⟩
          · omega
          · rw [hv₀_st] at hv₁
            cases hv₁
            simp [hv₀, hfs]
        · simp [Function.update_of_ne htc, hrs_some]
  · rw [Function.update_of_ne hRQ]
    exact hcorr R e hmem t hte hsends

theorem fig8SenderSync_accept {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (Q : Party) (c' : Fig8C Pt) (st' : Fig8St Pt)
    (t' i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ) (pos : SM.Pos)
    (hk : KeptInv P Dh encPt encT idOf lam sC g)
    (hid : (g.st Q).id = Q)
    (hfig8 : Fig8SenderSync g)
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', t', i', m_out))
    (hpos_ep : pos.epoch = c'.1.1) :
    Fig8SenderSync (g.accept Q st' pos) where
  htcur R := by
    dsimp [SM.GameState.accept, SM.GameState.delete]
    by_cases hRQ : R = Q
    · subst hRQ
      simp only [Function.update_self, hpos_ep]
      have htcurR := hfig8.htcur R
      rcases (lFig8_receive_spec Pt P Dh encPt encT idOf lam hfig).2.2.2 with
        ⟨hnew, hst_tcur⟩ | ⟨hle_tcur, hst_tcur, _⟩ <;> omega
    · simp only [Function.update_of_ne hRQ]
      exact hfig8.htcur R
  hvS R hsends := by
    dsimp [SM.GameState.accept, SM.GameState.delete] at hsends ⊢
    by_cases hRQ : R = Q
    · subst hRQ
      simp only [Function.update_self, hpos_ep] at hsends ⊢
      have htcurR := hfig8.htcur R
      have hspec := lFig8_receive_spec Pt P Dh encPt encT idOf lam hfig
      have hsendsF : R.sendsIn c'.1.1 = false := hid ▸ hspec.1
      rcases hspec.2.2.2 with ⟨hnew, _⟩ | ⟨hle_tcur, _, hγ, hvS_eq, _⟩
      · have hmax : max (g.epoch R) c'.1.1 = c'.1.1 := by omega
        rw [hmax, hsendsF] at hsends
        cases hsends
      · have hmax : max (g.epoch R) c'.1.1 = g.epoch R := by omega
        rw [hmax] at hsends
        rw [hγ, hvS_eq]
        exact hfig8.hvS R hsends
    · simp only [Function.update_of_ne hRQ] at hsends ⊢
      exact hfig8.hvS R hsends
  hvR := (keptInv_updKeptOnRes_accept Pt P Dh encPt encT idOf lam Q c' st' t' i' m_out pos
    hk hid hfig).hvR

omit [DecidableEq Pt] [SampleableType Pt] in
theorem st_id_accept {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (Q : Party) (c' : Fig8C Pt) (st' : Fig8St Pt)
    (t' i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ) (pos : SM.Pos)
    (hid : ∀ R, (g.st R).id = R)
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' =
      some (st', t', i', m_out)) :
    ∀ R, ((g.accept Q st' pos).st R).id = R := by
  intro R
  dsimp [SM.GameState.accept, SM.GameState.delete]
  by_cases hRQ : R = Q
  · subst hRQ
    rw [Function.update_self, (lFig8_receive_spec Pt P Dh encPt encT idOf lam hfig).2.2.1, hid R]
  · rw [Function.update_of_ne hRQ, hid R]

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem epoch_le_accept {St Msg C : Type}
    {g : SM.GameState St Msg C} {qep : ℕ}
    (Q : Party) (st' : St) (pos : SM.Pos)
    (hep : ∀ R, g.epoch R ≤ qep + 1)
    (hpos : pos.epoch ≤ qep + 1) :
    ∀ R, (g.accept Q st' pos).epoch R ≤ qep + 1 := by
  intro R
  dsimp [SM.GameState.accept, SM.GameState.delete]
  by_cases hRQ : R = Q
  · subst hRQ
    rw [Function.update_self]
    exact max_le (hep R) hpos
  · rw [Function.update_of_ne hRQ]
    exact hep R

theorem onAnswer_rejected_run
    {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (b : SimState PQ Pt ℓ) :
    (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w isDel ci? T pq' (some .rejected)).run b = pure (some .rejected, b) :=
  rfl

theorem simRecvStepC_of_probeHook_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl₁ : Bool) (ans : Option (RecvResult (Plain ℓ)))
    (hstep : (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Q w isDel)).run sC).run (g, fl)) = pure ((ans, sC₁), (g₁, fl₁))) :
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel (sC, (g, fl)) =
      (ans, (sC₁, (g₁, fl₁))) := by
  have h := simRecvC_probe_run P ℓ Dh encPt encT decT idOf lam qep Q w isDel (sC, (g, fl))
  dsimp only at h
  rw [hstep] at h
  simp only [pure_inj, Prod.mk.injEq] at h
  exact Prod.ext h.1.1.symm (Prod.ext h.1.2.symm h.2.symm)

open Classical in
theorem firstNESimImpl'_deliver_of_noProbe
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ)))
    (tr : KemFailTrackState P.C.F)
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hstep : (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Q w true)).run sC).run (g, false)) = pure ((ans, sC₁), (g₁, false))) :
    ∃ tr' : KemFailTrackState P.C.F,
      (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, false), tr) =
        pure (ans, (sC₁, (g₁, false, false), tr')) := by
  have hr := simRecvStepC_of_probeHook_run P ℓ Dh encPt encT decT idOf lam qep Q w true
    sC sC₁ g g₁ false false ans hstep
  have hlazy_true :
      decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) =
        true :=
    decide_eq_true hlazy
  rw [firstNESimImpl'_deliver_run]
  dsimp only
  rw [hr, hlazy_true]
  simp only [Bool.and_false, Bool.or_false, Bool.false_and, Bool.not_true]
  exact ⟨_, rfl⟩

open Classical in
theorem firstNESimImpl'_deliver_of_not_lazy
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hnot_lazy : ¬ ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) :
    ∃ (ans : Option (RecvResult (Plain ℓ)))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (tr' : KemFailTrackState P.C.F),
      (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, false), tr) =
        pure (ans, (sC₁, (g₁, false, true), tr')) := by
  have hlazy_false :
      decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) =
        false :=
    decide_eq_false hnot_lazy
  rw [firstNESimImpl'_deliver_run]
  dsimp only
  rw [hlazy_false]
  simp only [Bool.false_and, Bool.or_false, Bool.not_false]
  exact ⟨_, _, _, _, rfl⟩

theorem cellSimRun_deliver_pure_eq {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep t : ℕ)
    (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (u : Option (RecvResult (Plain ℓ)) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) (ans : Option (RecvResult (Plain ℓ)))
    (sent : List (Fig8C Pt)) (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpure :
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let fs := lFS P.C P.codec ℓ encT idOf 25000
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (deliverForgeHook Pt ℓ) Q w true)).run sC = pure (ans, sC₁)) :
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC sent m' s_cell =
    cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u ans) sC₁ sent m' s_cell := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  rw [cellSimRun_deliver_query_bind,
    runCellStep_guardC_pure Pt P encT decT qep t tL fig fs Q w true sC sC₁ sent m' s_cell ans
      hpure,
    pure_bind]

theorem firstNECoupledInvD_deliver_pure_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (ans : Option (RecvResult (Plain ℓ))) (b : Bool)
    (hpure : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        pure (ans, updAmbSimStateC Pt b sC))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let sC₁ := updAmbSimStateC Pt b sC
  have hpure_probe := probeStep_of_guardC_pure Pt P encT decT qep fig fs Q w true
    sC sC₁ g false ans (hpure (probeHook fig (qep + 1)))
  obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf lam
    qep q Q w sC sC₁ g g ans tr hlazy hpure_probe
  rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
  have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₁ sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, hbody, (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig,
      syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g
        (s_cell 0 none) hsync⟩)
  refine le_trans (hih ans sC₁ g false false tr' sent m' s_cell hinv₁) ?_
  refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
    _ (u ans) sC sC₁ sent sent m' m' g s_cell s_cell fun t _ tL _ => Or.inr ?_
  exact cellSimRun_deliver_pure_eq P ℓ Dh encPt encT decT idOf lam qep t tL Q w u
    sC sC₁ ans sent m' (s_cell t tL) (hpure (deliverForgeHook Pt ℓ))

omit [SampleableType Pt] in
theorem probeStep_of_guardC_probe_rejected {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (c' : Fig8C Pt)
    (sC sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hprobe :
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (probeHook fig (qep + 1)) Q w true)).run sC =
      ((StateT.lift ((probeHook fig (qep + 1)).probe Q c') >>=
        fun _ => pure (some RecvResult.rejected)) :
          StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) _).run sC₁) :
    (((LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
      pure ((some RecvResult.rejected, sC₁), (g, (fig.receive (g.st Q) c').isSome)) := by
  rw [hprobe]
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, probeHook_probe_run,
    Bool.false_or, bind_assoc, pure_bind]

theorem runCellStep_guardC_probe_rejected_of_receive_none {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep t : ℕ)
    (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (c' : Fig8C Pt)
    (sC sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {s_cell g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hrel : PPrimePaperRelShifted s_cell m' g)
    (hrcv : fig.receive (g.st Q) c' = none)
    (hprobe :
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (deliverForgeHook Pt ℓ) Q w true)).run sC =
      ((StateT.lift ((deliverForgeHook Pt ℓ).probe Q c') >>=
        fun _ => pure (some RecvResult.rejected)) :
          StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) _ _).run sC₁) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep fig fs
        (deliverForgeHook Pt ℓ) Q w true))
      sC sent m' s_cell =
      pure ((((some RecvResult.rejected, sC₁), sent), m'), s_cell) := by
  rw [runCellStep_congr_run fig qep t tL _
    (StateT.lift ((deliverForgeHook Pt ℓ).probe Q c') >>= fun _ => pure (some RecvResult.rejected))
    sC sC₁ sent m' s_cell hprobe,
    runCellStep_bind,
    cellSimRun_deliverForgeHook_probe_of_receive_none Pt fig qep t tL Q c' sC₁ sent m' hrel hrcv,
    pure_bind, runCellStep_pure]

theorem firstNECoupledInvD_deliver_probe_none_step {α : Type} {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8)) (b : Bool) (c' : Fig8C Pt)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' = none)
    (hprobe : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        ((StateT.lift (H.probe Q c') >>= fun _ => pure (some RecvResult.rejected)) :
          StateT (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) M _).run (updAmbSimStateC Pt b sC))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let sC₁ := updAmbSimStateC Pt b sC
  have hprobe_run := probeStep_of_guardC_probe_rejected Pt P encT decT qep fig fs Q w c'
    sC sC₁ g (hprobe (probeHook fig (qep + 1)))
  rw [hrcv, Option.isSome_none] at hprobe_run
  obtain ⟨tr', hrun⟩ := firstNESimImpl'_deliver_of_noProbe P K InvPQ ℓ Dh encPt encT decT idOf lam
    qep q Q w sC sC₁ g g (some RecvResult.rejected) tr hlazy hprobe_run
  rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind]
  have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₁ sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, hbody, (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig,
      syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g
        (s_cell 0 none) hsync⟩)
  refine le_trans (hih (some RecvResult.rejected) sC₁ g false false tr' sent m' s_cell hinv₁) ?_
  refine sum_cellSimRun_le_of_post_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
    _ (u (some RecvResult.rejected)) sC sC₁ sent sent m' m' g s_cell s_cell fun t ht tL htL => ?_
  rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
  · exact Or.inl hdoomed
  · right
    rw [cellSimRun_deliver_query_bind,
      runCellStep_guardC_probe_rejected_of_receive_none Pt P encT decT qep t tL fig fs Q w c'
        sC sC₁ sent m' hrel_sh hrcv (hprobe (deliverForgeHook Pt ℓ)),
      pure_bind]

theorem firstNECoupledInvD_deliver_probe_nonlazy_step {α : Type} {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ)))
    (tr tr' : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hrun :
      (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, false), tr) =
      pure (ans, (sC₁, (g₁, false, true), tr'))) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  rw [simulateQ_firstNESimImpl'_deliver_query_bind, hrun, pure_bind,
    fl_false_of_dead_support P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (u ans) sC₁ g₁ false true tr' ⟨rfl, rfl⟩]
  exact zero_le

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAccept_true_of_inTransit_some {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (t_v i_v : ℕ) (m_v : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (b : SimState PQ Pt ℓ) {r_m : _}
    (hinT : b.mir.inTransit Q.other w = some r_m) :
    ∃ (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ),
      (onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
        Q w true t_v i_v m_v ci? T pq').run b = pure (ans, b') ∧
      b'.honest = b.honest ∧
      b'.stopped = b.stopped ∧
      b'.mir = b.mir.accept Q () r_m.pos := by
  unfold onAccept putS
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
    ↓reduceIte, hinT]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem onAnswer_true_accepted_of_inTransit_some {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (t' i' : ℕ) (pm : Option (LibsignalMsgPublicPart × Plain ℓ))
    (b : SimState PQ Pt ℓ) {r_m : _}
    (hinT : b.mir.inTransit Q.other w = some r_m) :
    ∃ (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ),
      (onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
        Q w true ci? T pq' (some (.accepted t' i' pm))).run b = pure (ans, b') ∧
      b'.honest = b.honest ∧
      b'.stopped = b.stopped ∧
      b'.mir = b.mir.accept Q () r_m.pos := by
  unfold onAnswer
  exact onAccept_true_of_inTransit_some Pt qep Q w t' i'
    ((pm.map Prod.snd).getD default) ci? T pq' b hinT

theorem resyncC_some_of_receive_none {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (t_v i_v : ℕ) (pm_v : LibsignalMsgPublicPart × Plain ℓ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (fl : Bool)
    (hrel : PPrimePaperRelShifted s_cell m' g)
    (hsync : MirrorSync m' g s_unsh)
    {r : _}
    (htr : g.inTransit Q.other c = some r)
    (hrcv : fig.receive (g.st Q) c = none) :
    (((LibsignalSimC.resyncC qep fig fs (probeHook fig (qep + 1))
        Q w ci? T pq' c (some (t_v, i_v, pm_v))).run sC₀).run (g, fl)) =
      pure ((some RecvResult.rejected, sC₀), (g, fl)) ∧
    runCellStep fig qep t tL
      (LibsignalSimC.resyncC qep fig fs (deliverForgeHook Pt ℓ)
        Q w ci? T pq' c (some (t_v, i_v, pm_v)))
      sC₀ sent m' s_cell =
      pure ((((some RecvResult.rejected, sC₀), sent), m'), s_cell) := by
  obtain ⟨ans, b', hrun, _, _, _⟩ :=
    onAccept_run_pure qep Q w true t_v i_v pm_v.2 ci? T pq' sC₀.base
  have h := resyncC_some_lockstep Pt fig fs qep t tL Q w ci? T pq' c t_v i_v pm_v sC₀ sent fl
    hrel hsync ans b' hrun
  simpa [htr, hrcv] using h

omit [Zero Pt] [SampleableType Pt] in
theorem updKeptOnRes_accepted_eq {PQ : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (c : Fig8C Pt) (t₁ i₁ t₂ i₂ : ℕ)
    (pm₁ pm₂ : Option (LibsignalMsgPublicPart × Plain ℓ)) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    updKeptOnRes fig fs Q c (some (.accepted t₁ i₁ pm₁)) sC =
      updKeptOnRes fig fs Q c (some (.accepted t₂ i₂ pm₂)) sC :=
  rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem inTransit_eq_some_mem {St Msg C : Type} [DecidableEq C]
    {g : SM.GameState St Msg C} {P : Party} {c : C} {r : SM.Record Msg C}
    (htr : g.inTransit P c = some r) :
    r ∈ g.trans ∧ r.pos.sender = P ∧ r.ct = c := by
  unfold SM.GameState.inTransit at htr
  have hmem := List.mem_of_find?_eq_some htr
  have hpred := List.find?_some htr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpred
  exact ⟨hmem, hpred.1, hpred.2⟩

omit [Zero Pt] [SampleableType Pt] in
theorem corrsSnapsInv_updKeptOnRes_accept {PQ : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (c : Fig8C Pt) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (b' : SimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (st' : Fig8St Pt) (pos : SM.Pos)
    (hsnaps : CorrsSnapsInv sC.snaps g) :
    CorrsSnapsInv
      ({ updKeptOnRes fig fs Q c res sC with base := b' }).snaps
      (g.accept Q st' pos) := by
  intro R e hmem
  dsimp only
  rw [(updKeptOnRes_base_sent_snaps_eq Pt fig fs Q c res sC).2.2]
  exact hsnaps R e hmem

omit [Zero Pt] [SampleableType Pt] in
theorem corrsSnapIdxInv_updKeptOnRes_accept {PQ : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (c : Fig8C Pt) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (b' : SimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (st' : Fig8St Pt) (pos : SM.Pos)
    (hsnapIdx : CorrsSnapIdxInv sC.snaps g)
    (hle : CorrsLeEpoch g) :
    CorrsSnapIdxInv
      ({ updKeptOnRes fig fs Q c res sC with base := b' }).snaps
      (g.accept Q st' pos) := by
  dsimp only
  rw [(updKeptOnRes_base_sent_snaps_eq Pt fig fs Q c res sC).2.2]
  exact corrsSnapIdxInv_accept Q st' pos hsnapIdx hle

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem honestSentSync_with_base {PQ : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (b' : SimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (hhon : HonestSentSync Pt sC.base.honest sent)
    (heq : b'.honest = sC.base.honest) :
    HonestSentSync Pt ({ sC with base := b' }).base.honest sent := by
  dsimp only
  rw [heq]
  exact hhon

theorem resyncC_some_of_accept {PQ : Type} {ℓ : ℕ} [Inhabited PQ]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qep t : ℕ) (tL : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (t_v i_v : ℕ) (pm_v : LibsignalMsgPublicPart × Plain ℓ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell g s_unsh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (fl : Bool)
    (hrel : PPrimePaperRelShifted s_cell m' g)
    (hsync : MirrorSync m' g s_unsh)
    {r : _} {st' : Fig8St Pt} {t' i' : ℕ} {m : LibsignalMsgPublicPart × Plain ℓ}
    (htr : g.inTransit Q.other c = some r)
    (hrcv : fig.receive (g.st Q) c = some (st', t', i', m))
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState PQ Pt ℓ)
    (hrun : (onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
      Q w true t_v i_v pm_v.2 ci? T pq').run sC₀.base = pure (ans, b')) :
    let sC₁ := { updKeptOnRes fig fs Q c (some (.accepted t' i' (some m))) sC₀ with base := b' }
    (((LibsignalSimC.resyncC qep fig fs (probeHook fig (qep + 1))
        Q w ci? T pq' c (some (t_v, i_v, pm_v))).run sC₀).run (g, fl)) =
      pure ((ans, sC₁), (g.accept Q st' r.pos, fl)) ∧
    runCellStep fig qep t tL
      (LibsignalSimC.resyncC qep fig fs (deliverForgeHook Pt ℓ)
        Q w ci? T pq' c (some (t_v, i_v, pm_v)))
      sC₀ sent m' s_cell =
      pure ((((ans, sC₁), sent), m'.accept Q () r.pos), s_cell.accept Q st' r.pos) := by
  intro sC₁
  have h := resyncC_some_lockstep Pt fig fs qep t tL Q w ci? T pq' c t_v i_v pm_v sC₀ sent fl
    hrel hsync ans b' hrun
  have heq := updKeptOnRes_accepted_eq Pt fig fs Q c t' i' t' i'
    (if r.pos ∈ g.chall then none else some m) (some m) sC₀
  simpa [htr, hrcv, sC₁, heq] using h

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem keptInv_with_base {PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (b' : SimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : KeptInv P Dh encPt encT idOf lam sC g) :
    KeptInv P Dh encPt encT idOf lam { sC with base := b' } g := by
  cases h; constructor <;> assumption

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] in
theorem corrsKeptRecvInv_with_base {PQ : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (b' : SimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : CorrsKeptRecvInv sC g) :
    CorrsKeptRecvInv { sC with base := b' } g :=
  h

end CryptoVerification.LibsignalSession.HeadlineV1

end
