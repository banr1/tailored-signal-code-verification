/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted
import Computational.Proofs.HeadlineV1.DeliverForgeShifted
import Computational.Proofs.HeadlineV1.HiddenSaltLazyWire
import Computational.Proofs.SignalWireRoundTrip
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Online-Halted Evict-Only Bound

**Checked by Lean.** Bounds the probe probability of `evictOnlyHalted'` under
`EvictedSpurHistSimInvLazy` and decomposes `hiddenSaltTermTrackHalted` without a
`kemFailFindAdvantage` error term.
-/

@[expose] public section

set_option autoImplicit false

open scoped MeasureTheory
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted (cleanCand evalDist_simulateQ_kemFailSimImplHalted_le_firstNE'_add_evictOnly' evictOnlyHalted' firstNEHalted' hiddenSaltGameTrackHalted_eq_kemFailSimImplHalted_proj kemFailSendStepHalted_mem_support_cases splitSimImplHalted splitSimImplHalted_non_deliver_run stepKemFailDeliver_cand_eq)
open CryptoGames (Party effectiveHkdfSalt32)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM.Proofs.Refinement (InvB KemFailTrackState SameMeta SpqrCLocal badCoin_prob_le challPure cxSend evalDist_bind_true_le_of_support hiddenSaltTermTrackHalted initKemFailTrack kemFailSendStepHalted kemFailSendStepPostCoin kemFailSimImpl kemFailSimImplHalted runProbeStep simRecvStepC simSendStep spurBadList spurUnit stepKemFailDeliver stepKemFailSend transmitPure)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey Params PublicKey)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart X25519RealizesDh dummyKey lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St inReceiveOnlyEpoch spuriousStepTerm)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState ProbeM initSimC)
open CryptoVerification.E2E.RefuseCorrB0 (refuseCorrB0_queries)
open CryptoVerification.LibsignalSession (signalEncodeFits32_proto signalRoundTripShort_proto)
open CryptoVerification.LibsignalSession.HeadlineV1 (EvictedSpurHistSimInvLazy evalDist_bind_le_add_bool_of_support evalDist_bind_true_le_add_of_badCoin evictedSpurHistSimInvLazy_corr_step evictedSpurHistSimInvLazy_deliver_step evictedSpurHistSimInvLazy_inject_step evictedSpurHistSimInvLazy_mono_r evictedSpurHistSimInv_init f8_send_eq_some_of_sameMeta kemFailSendStep_new_epoch_preserves_evictedSpurHistSimInvLazy_of_good_coin kemFailSendStep_same_epoch_preserves_evictedSpurHistSimInvLazy kemFailSimImpl_deliver_run kemFailSimImpl_inl_state_eq kemFailSimImpl_send_flag_eq_false lengthsOk_paramsIdsWithSpqr_v1 mkPub_eq_some_of_spqrCLocal probeHook_lift_challQuery_run probeHook_lift_transmitQuery_run runProbeStep_run sendCoinCollBad sendCoinCollPts sendCoinCollPts_length simSendStep_eq_of_mkPub_some spqrCLocal_and_topState_v1 spurSlack spurSlack_le_spuriousStepTerm spurSlack_step_le)

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedEvict

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec

open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.E2E (Bytes paramsV1 idsOf)
open CryptoVerification.E2E.Signed (paramsV1_C)

/-! ## Support lift for `runProbeStep` -/

private theorem mem_support_runProbeStep_cleanCand {PQ Pt α : Type} [Zero Pt]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (step : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α)
    (sC sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh gh₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)
    (tr tr₁ : KemFailTrackState P.C.F) (u₁ : α)
    (h : (u₁, sC₁, gh₁, tr₁) ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep step).run
      (sC, gh, tr))) :
    (u₁, sC₁, gh₁, cleanCand tr) ∈ support
      ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep step).run (sC, gh, cleanCand tr)) := by
  rw [runProbeStep_run, MonadAttach.mem_support_bind] at h ⊢
  rcases h with ⟨⟨⟨a, sC'⟩, gh'⟩, hm, hp⟩
  simp only [support_pure, Set.mem_singleton_iff] at hp
  rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
  rcases Prod.mk.inj hp2 with ⟨rfl, hp3⟩
  rcases Prod.mk.inj hp3 with ⟨rfl, _⟩
  exact ⟨((u₁, sC₁), gh₁), hm, by simp⟩

theorem kemFailSendStepPostCoin_some_run_eq_bind_simSendStep
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rq₀ rq : BitVec 512)
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s_R : CryptoGames.SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hep : sC.base.mir.epMgmt 3 qep Q true = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false)
    (hg_win : g.win = false)
    (hmeta : SameMeta s_R sC.base g)
    (hpq : InvB Inv q r (sC.base.pq Q)) :
    (kemFailSendStepPostCoin P K ℓ Dh encPt encT idOf lam qep sC (g, false) tr s₁ Q m₀ chal
      (some rq₀) rq).run (sC, (g, false), tr) =
    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
      let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal true s₁ rq c_cka
        (sC.base, g)
      pure (res.1,
        (cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1, (res.2.2, false),
          stepKemFailSend P.C.F K tr Q rq))) := by
  have hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true := by
    intro hch; revert hg3; rw [hch]; cases s₁.safeCh 3 Q <;> simp
  set pn :=
    if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
    else sC.base.pn Q
  obtain ⟨pq', salt, pqMsg, _, hmk⟩ :=
    mkPub_eq_some_of_spqrCLocal hS hr sC.base Q rq pn hpq
  set pub : LibsignalMsgPublicPart :=
    ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == CryptoGames.Party.A && sC.base.unackA then P.addrAB else none⟩
  unfold kemFailSendStepPostCoin
  simp only [StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
    map_eq_bind_pure_comp, Function.comp_apply, pure_bind, bind_assoc]
  refine bind_congr fun c_cka => ?_
  obtain ⟨_, _, _, hf8_eq⟩ :=
    f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ chal c_cka
      true s₁ s_R sC.base g hmeta hep hsafeCh
  have hf8_1 : (chal.elim
      (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka true g)
      (fun m₁ => challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka true g)).1 =
      some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
        (pub, chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)) c_cka).2 :=
    congrArg Prod.fst hf8_eq
  have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ chal
    true s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
  dsimp only [pn] at hmk hsim_eq ⊢
  rw [hmk]
  dsimp only
  cases chal with
  | none =>
    simp only [Option.elim] at hf8_eq hsim_eq ⊢
    rw [probeHook_lift_transmitQuery_run]
    simp only [hg_win, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.samIfNec,
      StateT.run_monadLift, MonadLiftT.monadLift,
      StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, hf8_eq, hsim_eq]
    rfl
  | some m₁ =>
    simp only [Option.elim] at hf8_eq hsim_eq ⊢
    rw [probeHook_lift_challQuery_run]
    simp only [hg_win, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.samIfNec,
      StateT.run_monadLift, MonadLiftT.monadLift,
      StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, hf8_eq, hsim_eq]
    rfl

theorem kemFailSendStepPostCoin_none_run_eq_bind_simSendStep
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Inv : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rq : BitVec 512)
    (s₁ : CryptoGames.SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s_R : CryptoGames.SM.GameState (GhostState (List (BitVec 8))) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hep : sC.base.mir.epMgmt 3 qep Q false = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false)
    (hg_win : g.win = false)
    (hmeta : SameMeta s_R sC.base g)
    (hpq : InvB Inv q r (sC.base.pq Q)) :
    (kemFailSendStepPostCoin P K ℓ Dh encPt encT idOf lam qep sC (g, false) tr s₁ Q m₀ chal
      none rq).run (sC, (g, false), tr) =
    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
      let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal false s₁ rq c_cka
        (sC.base, g)
      pure (res.1,
        (cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1, (res.2.2, false),
          stepKemFailSend P.C.F K tr Q rq))) := by
  have hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true := by
    intro hch; revert hg3; rw [hch]; cases s₁.safeCh 3 Q <;> simp
  set pn :=
    if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
    else sC.base.pn Q
  obtain ⟨pq', salt, pqMsg, _, hmk⟩ :=
    mkPub_eq_some_of_spqrCLocal hS hr sC.base Q rq pn hpq
  set pub : LibsignalMsgPublicPart :=
    ⟨pn, pqMsg, effectiveHkdfSalt32 salt, if Q == CryptoGames.Party.A && sC.base.unackA then P.addrAB else none⟩
  unfold kemFailSendStepPostCoin
  simp only [pure_bind]
  dsimp only [pn] at hmk ⊢
  rw [hmk]
  dsimp only
  cases chal with
  | none =>
    rw [probeHook_lift_transmitQuery_run]
    simp only [hg_win, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.samIfNec,
      StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      bind_assoc, pure_bind]
    refine bind_congr fun c_cka => ?_
    obtain ⟨_, _, _, hf8_eq⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ none c_cka
        false s₁ s_R sC.base g hmeta hep hsafeCh
    have hf8_1 : (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q
        (pub, m₀) c_cka false g).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, m₀) c_cka).2 :=
      congrArg Prod.fst hf8_eq
    have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ none
      false s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
    simp only [Option.elim] at hf8_eq hsim_eq ⊢
    simp only [hf8_eq, hsim_eq, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    rfl
  | some m₁ =>
    rw [probeHook_lift_challQuery_run]
    simp only [hg_win, Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.samIfNec,
      StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      bind_assoc, pure_bind]
    refine bind_congr fun c_cka => ?_
    obtain ⟨_, _, _, hf8_eq⟩ :=
      f8_send_eq_some_of_sameMeta P ℓ Dh encPt encT idOf lam qep Q pub m₀ (some m₁) c_cka
        false s₁ s_R sC.base g hmeta hep hsafeCh
    have hf8_1 : (challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
        CryptoGames.SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka false g).1 =
        some ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (g.st Q)
          (pub, if s_R.b then m₁ else m₀) c_cka).2 :=
      congrArg Prod.fst hf8_eq
    have hsim_eq := simSendStep_eq_of_mkPub_some P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁)
      false s₁ rq c_cka sC.base g pq' pub _ hmk hf8_1
    simp only [Option.elim] at hf8_eq hsim_eq ⊢
    simp only [hf8_eq, hsim_eq, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    rfl

/-! ## Halted evict-only bounds -/

set_option exponentiation.threshold 1024 in
theorem kemFailSendStepHalted_evictOnly_bound
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' w_rem : ℕ) (hS : SpqrCLocal P.spqr q InvPQ)
    (hq32 : q < 2 ^ 32)
    (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_coin : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q (r' + 1) w_rem sC g)
    (k_cont : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F) → ProbComp Bool)
    (hk_same : ∀ u₁ sC₁ g₁ tr₁,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w_rem sC₁ g₁ →
      𝒟[k_cont (u₁, sC₁, (g₁, false), tr₁)] {true} ≤
        spurSlack P encPt Dh q w_rem + ((w_rem : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ))
    (hk_decr : ∀ w' u₁ sC₁ g₁ tr₁,
      w_rem = w' + 1 →
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w' sC₁ g₁ →
      𝒟[k_cont (u₁, sC₁, (g₁, false), tr₁)] {true} ≤
        spurSlack P encPt Dh q w' + ((w' : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ)) :
    𝒟[(kemFailSendStepHalted P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin).run
        (sC, (g, false), tr) >>= k_cont] {true} ≤
      spurSlack P encPt Dh q w_rem + ((w_rem : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) := by
  have hInv_r' : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w_rem sC g :=
    evictedSpurHistSimInvLazy_mono_r hInv (Nat.le_succ r')
  by_cases hinw : inReceiveOnlyEpoch sC.base.mir Q = true
  · rcases kemFailSendStep_new_epoch_preserves_evictedSpurHistSimInvLazy_of_good_coin
        P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT idOf hX hD hrt hid lam qep q r'
        (r' + 1) w_rem hS hq32 (Nat.lt_succ_self r') Q m₀ chal r_coin sC g tr hInv hinw with
      hnoop | ⟨hw_pos, s₁, rk_base, T_base, L, epExp, hg_win_f, hg1, hep, hg3, hL_len, hmax_le,
        hgood_coin⟩
    · refine evalDist_bind_true_le_of_support _ _ _ fun ⟨u₁, sC₁, gh₁, tr₁⟩ h₁ => ?_
      rcases kemFailSendStepHalted_mem_support_cases P K ℓ Dh encPt encT decT idOf lam qep Q m₀
          chal r_coin sC (g, false) tr h₁ with ⟨tr', heq⟩ | h₁'
      · cases heq
        exact hk_same none sC g _ hInv_r'
      · rcases hnoop (u₁, sC₁, gh₁, tr₁) h₁' with ⟨_, _, hgh₁, hInv₁⟩
        dsimp only at hgh₁ hInv₁
        rw [hgh₁] at hInv₁ ⊢
        exact hk_same u₁ sC₁ g tr₁ hInv₁
    · obtain ⟨w', hw_eq⟩ : ∃ w', w_rem = w' + 1 := ⟨w_rem - 1, by omega⟩
      rcases hInv.2 with ⟨_, s_R, _, _, _, hsim, _⟩
      have hg_clear : { g with win := false } = g := by cases g; simp_all
      have hmeta : SameMeta s_R sC.base g := hg_clear ▸ hsim.hsim.hmeta
      have hpq : InvB InvPQ q (r' + 1) (sC.base.pq Q) := hsim.hsim.hpqInv Q
      have hinner : ∀ rq : BitVec 512,
          𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
            let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r_coin.isSome s₁ rq
              c_cka (sC.base, g)
            k_cont (res.1, (cxSend P Dh encPt encT idOf lam Q sC res.2.1 res.1, (res.2.2, false),
              stepKemFailSend P.C.F K tr Q rq))] {true} ≤
          spurSlack P encPt Dh q w_rem + ((w_rem : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) := by
        intro rq
        set M := max (sC.base.mir.epoch .A) (sC.base.mir.epoch .B)
        have hbad_prob :
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
              {c_cka | (spurBadList P encPt Dh Q rk_base T_base L c_cka ||
                sendCoinCollBad Dh epExp M c_cka) = true} ≤
              (L.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh + ((qep + 2 : ℕ) : ℝ≥0∞) * δ := by
          have hb := badCoin_prob_le P encPt Dh δ hδ Q rk_base T_base L (sendCoinCollPts Dh epExp M)
          rw [sendCoinCollPts_length] at hb
          exact hb.trans (add_le_add le_rfl (by gcongr))
        refine (evalDist_bind_true_le_add_of_badCoin
          (d₂ := spurSlack P encPt Dh q w' + ((w' : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ))
          ($ᵗ BitVec 256)
          (fun c_cka => spurBadList P encPt Dh Q rk_base T_base L c_cka ||
            sendCoinCollBad Dh epExp M c_cka)
          hbad_prob _ fun c_cka hgood => ?_).trans ?_
        · dsimp only
          have hInv₁ := hgood_coin rq c_cka hgood
          rw [hw_eq] at hInv₁
          exact hk_decr w' _ _ _ _ hw_eq hInv₁
        · rw [hw_eq]
          calc ((L.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh + ((qep + 2 : ℕ) : ℝ≥0∞) * δ) +
                (spurSlack P encPt Dh q w' + ((w' : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ))
              = ((L.length : ℝ≥0∞) * spurUnit P.C.F encPt Dh + spurSlack P encPt Dh q w') +
                (((w' + 1 : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ)) := by
                push_cast; ring
            _ ≤ spurSlack P encPt Dh q (w' + 1) +
                (((w' + 1 : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ)) :=
                add_le_add (spurSlack_step_le P encPt Dh q hL_len) le_rfl
      unfold kemFailSendStepHalted
      rw [StateT.run_bind, StateT.run_get, pure_bind]
      simp only [hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3]
      cases r_coin with
      | some rq =>
        simp only [pure_bind]
        split_ifs with hcand
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
          exact hk_same none sC g _ hInv_r'
        · rw [kemFailSendStepPostCoin_some_run_eq_bind_simSendStep P K InvPQ ℓ Dh encPt encT idOf
            lam qep q (r' + 1) hS (Nat.succ_pos r') Q m₀ chal rq rq s₁ s_R sC g tr hep hg3
            hg_win_f hmeta hpq, bind_assoc]
          simpa only [pure_bind, Option.isSome_some] using hinner rq
      | none =>
        rw [StateT.run_bind, StateT.run_monadLift]
        dsimp only [MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift]
        rw [bind_assoc, bind_assoc]
        generalize ($ᵗ BitVec 512 : ProbComp (BitVec 512)) = m512
        refine evalDist_bind_true_le_of_support m512 _ _ fun rq _ => ?_
        rw [pure_bind]
        dsimp only
        split_ifs with hcand
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
          exact hk_same none sC g _ hInv_r'
        · rw [kemFailSendStepPostCoin_none_run_eq_bind_simSendStep P K InvPQ ℓ Dh encPt encT idOf
            lam qep q (r' + 1) hS (Nat.succ_pos r') Q m₀ chal rq s₁ s_R sC g tr hep hg3 hg_win_f
            hmeta hpq, bind_assoc]
          simpa only [pure_bind, Option.isSome_none] using hinner rq
  · have hinw_f : inReceiveOnlyEpoch sC.base.mir Q = false := Bool.eq_false_iff.mpr hinw
    refine evalDist_bind_true_le_of_support _ _ _ fun ⟨u₁, sC₁, gh₁, tr₁⟩ h₁ => ?_
    rcases kemFailSendStepHalted_mem_support_cases P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal
        r_coin sC (g, false) tr h₁ with ⟨tr', heq⟩ | h₁'
    · cases heq
      exact hk_same none sC g _ hInv_r'
    · have hInv₁ := kemFailSendStep_same_epoch_preserves_evictedSpurHistSimInvLazy P K hspqr_eq
        InvPQ hInv_top ℓ Dh hDh encPt encT decT idOf hX hD hrt hid lam qep q r' (r' + 1) w_rem
        hS hq32 (Nat.lt_succ_self r') Q m₀ chal r_coin sC g tr hInv hinw_f (u₁, sC₁, gh₁, tr₁) h₁'
      have hfl₁ : gh₁.2 = false := by
        cases chal with
        | none =>
          exact kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
            (.inl (Q, m₀, r_coin)) sC g tr (u₁, sC₁, gh₁, tr₁) h₁'
        | some m₁ =>
          exact kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
            (.inr (Q, m₀, m₁, r_coin)) sC g tr (u₁, sC₁, gh₁, tr₁) h₁'
      have hgh₁ : gh₁ = (gh₁.1, false) := Prod.ext rfl hfl₁
      rw [hgh₁]
      exact hk_same u₁ sC₁ gh₁.1 tr₁ hInv₁

private theorem simulateQ_evictOnlyHalted'_prob_le_of_evictedSpurHistSimInvLazy
    {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q : ℕ) (hS : SpqrCLocal P.spqr q InvPQ)
    (hq32 : q < 2 ^ 32)
    (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    {p : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ n, ¬ p (.inl n)) (hp_inr : ∀ q_game, p (.inr q_game))
    (oa : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α) :
    ∀ (r w_rem : ℕ)
      (_hq : oa.IsQueryBoundP p r)
      (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (tr : KemFailTrackState P.C.F)
      (_hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g),
      𝒟[(simulateQ (evictOnlyHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, false, false), tr) >>=
        fun z => pure z.2.2.1.2.1] {true} ≤
        spurSlack P encPt Dh q w_rem + ((w_rem : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro r w_rem _ sC g tr _
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    intro r w_rem hq sC g tr hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases hq with ⟨hq0, hu⟩
    rw [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
      PFunctor.Obj.mk, id]
    rcases q_sm with n | q_game
    · rw [evictOnlyHalted', splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT
        idOf lam qep q (.inl n) (fun _ _ h => nomatch h) sC g false false tr, bind_assoc]
      simp only [pure_bind]
      refine evalDist_bind_true_le_of_support _ _ _ fun z₁ h₁ => ?_
      have hz₁ := kemFailSimImpl_inl_state_eq P K ℓ Dh encPt encT decT idOf lam qep n
        sC (g, false) tr z₁ h₁
      have h1 : z₁.2.1 = sC := congrArg (·.1) hz₁
      have h2 : z₁.2.2.1.1 = g := congrArg (·.2.1.1) hz₁
      have h3 : z₁.2.2.1.2 = false := congrArg (·.2.1.2) hz₁
      have h4 : z₁.2.2.2 = tr := congrArg (·.2.2) hz₁
      rw [h1, h2, h3, h4]
      exact ih z₁.1 r w_rem (by simpa [hp_inl n] using hu z₁.1) sC g tr hInv
    · have hr_pos : 0 < r := hq0.resolve_left (not_not.mpr (hp_inr q_game))
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rcases q_game with (((⟨Q, m₀, r_coin⟩ | ⟨Q, m₀, m₁, r_coin⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
      · rw [evictOnlyHalted', splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT
          idOf lam qep q (.inr (.inl (.inl (.inl (.inl (Q, m₀, r_coin)))))) (fun _ _ h => nomatch h)
          sC g false false tr, bind_assoc]
        simp only [pure_bind]
        exact kemFailSendStepHalted_evictOnly_bound P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT
          decT idOf hX hD hrt hid lam qep q r' w_rem hS hq32 δ hδ Q m₀ none r_coin sC g tr hInv _
          (fun u₁ sC₁ g₁ tr₁ hInv₁ =>
            ih u₁ r' w_rem (by simpa [hp_inr _] using hu u₁) sC₁ g₁ tr₁ hInv₁)
          (fun w' u₁ sC₁ g₁ tr₁ _ hInv₁ =>
            ih u₁ r' w' (by simpa [hp_inr _] using hu u₁) sC₁ g₁ tr₁ hInv₁)
      · rw [evictOnlyHalted', splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT
          idOf lam qep q (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r_coin))))))
          (fun _ _ h => nomatch h) sC g false false tr, bind_assoc]
        simp only [pure_bind]
        exact kemFailSendStepHalted_evictOnly_bound P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT
          decT idOf hX hD hrt hid lam qep q r' w_rem hS hq32 δ hδ Q m₀ (some m₁) r_coin sC g tr
          hInv _
          (fun u₁ sC₁ g₁ tr₁ hInv₁ =>
            ih u₁ r' w_rem (by simpa [hp_inr _] using hu u₁) sC₁ g₁ tr₁ hInv₁)
          (fun w' u₁ sC₁ g₁ tr₁ _ hInv₁ =>
            ih u₁ r' w' (by simpa [hp_inr _] using hu u₁) sC₁ g₁ tr₁ hInv₁)
      · let r₀ := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
        let j? := sC.base.honest.reverse.findIdx?
          (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
        let tr' := match r₀.1, j? with
          | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
          | _, _ => tr
        let tr_c' := match r₀.1, j? with
          | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K (cleanCand tr) Q j
          | _, _ => cleanCand tr
        have hlazy_true :
            decide (∃ r_idx w_rem,
              EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) =
              true :=
          decide_eq_true ⟨r' + 1, w_rem, hInv⟩
        have hdel_ev' :
            (evictOnlyHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
              (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, false), tr) =
            pure (r₀.1, (r₀.2.1, (r₀.2.2.1, false, false), tr')) := by
          simp [evictOnlyHalted', splitSimImplHalted, r₀, j?, tr', hlazy_true, StateT.run_bind,
            StateT.run_get, StateT.run_set]
          rfl
        rw [hdel_ev', pure_bind]
        dsimp only
        have hcand_c' : tr_c'.cand = none := by
          dsimp only [tr_c']
          cases r₀.1 with
          | none => rfl
          | some res =>
            cases res with
            | rejected => rfl
            | accepted _ _ _ =>
              cases j? with
              | none => rfl
              | some j => exact (stepKemFailDeliver_cand_eq K (cleanCand tr) Q j).trans rfl
        have hmem_kem : (r₀.1, (r₀.2.1, (r₀.2.2.1, r₀.2.2.2), tr_c')) ∈
            support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
              (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false), cleanCand tr)) := by
          rw [kemFailSimImpl_deliver_run]
          simp only [support_pure, Set.mem_singleton_iff]
          rfl
        have hInv₁ := evictedSpurHistSimInvLazy_deliver_step P K hspqr_eq InvPQ hInv_top ℓ Dh
          encPt encT decT idOf hinj hdec lam qep q r' (r' + 1) w_rem hS (Nat.lt_succ_self r')
          Q w sC g (cleanCand tr) hInv (r₀.1, (r₀.2.1, (r₀.2.2.1, r₀.2.2.2), tr_c')) hmem_kem
          hcand_c'
        exact ih r₀.1 r' w_rem (by simpa [hp_inr _] using hu r₀.1) r₀.2.1 r₀.2.2.1 tr' hInv₁
      · rw [evictOnlyHalted', splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT
          idOf lam qep q (.inr (.inl (.inr (Q, w)))) (fun _ _ h => nomatch h) sC g false false tr,
          bind_assoc]
        simp only [pure_bind]
        refine evalDist_bind_true_le_of_support _ _ _ fun ⟨u₁, sC₁, gh₁, tr₁⟩ h₁ => ?_
        have h₁_clean : (u₁, sC₁, gh₁, cleanCand tr) ∈
            support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
              (.inr (.inl (.inr (Q, w))))).run (sC, (g, false), cleanCand tr)) :=
          mem_support_runProbeStep_cleanCand P ℓ Dh encPt encT decT idOf lam qep _ sC sC₁
            (g, false) gh₁ tr tr₁ u₁ h₁
        rcases evictedSpurHistSimInvLazy_inject_step P K hspqr_eq InvPQ hInv_top ℓ Dh encPt encT
            decT idOf hinj hid lam qep q r' (r' + 1) w_rem hS (Nat.lt_succ_self r') Q w sC g
            (cleanCand tr) hInv (u₁, sC₁, gh₁, cleanCand tr) h₁_clean rfl with ⟨hfl₁, hInv₁⟩
        dsimp only at hfl₁ hInv₁ ⊢
        rw [hfl₁]
        exact ih u₁ r' w_rem (by simpa [hp_inr _] using hu u₁) sC₁ gh₁.1 tr₁ hInv₁
      · rw [evictOnlyHalted', splitSimImplHalted_non_deliver_run _ P K InvPQ ℓ Dh encPt encT decT
          idOf lam qep q (.inr (.inr Q)) (fun _ _ h => nomatch h) sC g false false tr, bind_assoc]
        simp only [pure_bind]
        refine evalDist_bind_true_le_of_support _ _ _ fun ⟨u₁, sC₁, gh₁, tr₁⟩ h₁ => ?_
        have h₁_clean : (u₁, sC₁, gh₁, cleanCand tr) ∈
            support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
              (.inr (.inr Q))).run (sC, (g, false), cleanCand tr)) :=
          mem_support_runProbeStep_cleanCand P ℓ Dh encPt encT decT idOf lam qep _ sC sC₁
            (g, false) gh₁ tr tr₁ u₁ h₁
        rcases evictedSpurHistSimInvLazy_corr_step P K InvPQ hInv_top ℓ Dh encPt encT decT idOf
            lam qep q r' (r' + 1) w_rem hq32 (Nat.le_succ r') Q sC g (cleanCand tr) hInv
            (u₁, sC₁, gh₁, cleanCand tr) h₁_clean rfl with ⟨hfl₁, hInv₁⟩
        dsimp only at hfl₁ hInv₁ ⊢
        rw [hfl₁]
        exact ih u₁ r' w_rem (by simpa [hp_inr _] using hu u₁) sC₁ gh₁.1 tr₁ hInv₁

/-! ## Halted hidden-salt decomposition -/

theorem halted_prob_le_add_spuriousStepTerm_of_evictedSpurHistSimInvLazy'
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    {InvPQ : ℕ → List (BitVec 8) → Prop}
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : CryptoGames.LibsignalSM.Proofs.RoundTrip.RtHyp P ℓ)
    (lam : Pt) (qep q : ℕ)
    (hq32 : q < 2 ^ 32)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hS : SpqrCLocal P.spqr q InvPQ)
    (hcoll0 : ∀ x₀ : BitVec 256, ∃ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base)
    (D δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : CryptoGames.LibsignalSM.LibAdv (List (BitVec 8)) (BitVec 512) ℓ)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hfirstNE' :
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (CryptoGames.SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
            (sC₀, ghd₀, tr₀)
        return z.2.2.1.2.1] {true} ≤ D) :
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let gh₀ := (CryptoGames.SM.initState fig k b, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep) A).run
          (sC₀, gh₀, tr₀)
      return z.2.2.1.2] {true} ≤
    D + spuriousStepTerm P.C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ := by
  have hunion :
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let gh₀ := (CryptoGames.SM.initState fig k b, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (kemFailSimImplHalted P K ℓ Dh encPt encT decT idOf lam qep) A).run
            (sC₀, gh₀, tr₀)
        return z.2.2.1.2] {true} ≤
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (CryptoGames.SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
            (sC₀, ghd₀, tr₀)
        return z.2.2.1.2.1] {true} +
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (CryptoGames.SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (evictOnlyHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
            (sC₀, ghd₀, tr₀)
        return z.2.2.1.2.1] {true} := by
    refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun b _ => ?_
    refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun k _ => ?_
    refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun pqrKey _ => ?_
    exact evalDist_simulateQ_kemFailSimImplHalted_le_firstNE'_add_evictOnly' P K InvPQ ℓ Dh encPt
      encT decT idOf lam qep q A
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (CryptoGames.SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b)
      false
      (initKemFailTrack P.C.F pqrKey)
  have hevict :
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (CryptoGames.SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (evictOnlyHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
            (sC₀, ghd₀, tr₀)
        return z.2.2.1.2.1] {true} ≤
      spuriousStepTerm P.C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ := by
    refine evalDist_bind_true_le_of_support _ _ _ fun b _ => ?_
    refine evalDist_bind_true_le_of_support _ _ _ fun k _ => ?_
    refine evalDist_bind_true_le_of_support _ _ _ fun pqrKey _ => ?_
    have hstep := simulateQ_evictOnlyHalted'_prob_le_of_evictedSpurHistSimInvLazy
      P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT idOf hX hD hrt hinj hdec hid lam
      qep q hS hq32 δ hδ (fun _ h => nomatch h) (fun _ => rfl) A q qep hq
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (CryptoGames.SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b)
      (initKemFailTrack P.C.F pqrKey)
      (CryptoVerification.LibsignalSession.HeadlineV1.EvictedSpurHistSimInv.toLazy hInv_top
        (evictedSpurHistSimInv_init P K InvPQ ℓ Dh encPt encT idOf lam qep q hX hS b k pqrKey
          (hcoll0 k.2)))
    have hcoll_le :
        ((qep : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) ≤
          (qep + 1) * (qep + 2) * δ := by
      calc ((qep : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ)
          ≤ ((qep + 1 : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) := by
            gcongr
            exact Nat.le_succ qep
        _ = (qep + 1) * (qep + 2) * δ := by
            push_cast
            ring
    exact hstep.trans (add_le_add (spurSlack_le_spuriousStepTerm P encPt Dh q qep le_rfl) hcoll_le)
  calc _ ≤ D + (spuriousStepTerm P.C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ) :=
      hunion.trans (add_le_add hfirstNE' hevict)
    _ = D + spuriousStepTerm P.C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ := by
      ring

/-- Bounds `hiddenSaltTermTrackHalted` on `RefuseB0.refuseCorrB0 A` via `firstNEHalted'` and
`evictOnlyHalted'` without a `kemFailFindAdvantage` term. -/
theorem hiddenSaltTermTrackHalted_le_add_spuriousStepTerm_v1_refuseCorrB0_lazy'
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (hK_tot : Encaps1Total K)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (_hdum : ∀ T, encT T ≠ dummyKey)
    (_hz : ∀ x, Dh.dh x 0 = 0) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (D δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (hfirstNE' :
      let P := paramsV1 C K idA idB
      let idOf := idsOf idA idB
      ∀ (InvPQ : ℕ → List (BitVec 8) → Prop),
      SpqrCLocal P.spqr q InvPQ →
      (∀ n pq, InvPQ n pq → TopState P.C.F K pq) →
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (CryptoGames.SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
            A.refuseCorrB0).run (sC₀, ghd₀, tr₀)
        return z.2.2.1.2.1] {true} ≤ D) :
    let P := paramsV1 C K idA idB
    let idOf := idsOf idA idB
    hiddenSaltTermTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A.refuseCorrB0 ≤
      D + spuriousStepTerm C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ := by
  intro P idOf
  by_cases hcoll0 : ∀ x₀ : BitVec 256, ∃ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base
  · obtain ⟨InvPQ, hS, hInv_top⟩ := spqrCLocal_and_topState_v1 P K rfl hK_tot q (by omega)
    unfold hiddenSaltTermTrackHalted
    rw [hiddenSaltGameTrackHalted_eq_kemFailSimImplHalted_proj]
    have hle := halted_prob_le_add_spuriousStepTerm_of_evictedSpurHistSimInvLazy'
      P K rfl hInv_top ℓ Dh hDh encPt encT decT hinj idOf ⟨rfl, rfl⟩ hdec hD
      ⟨signalRoundTripShort_proto, lengthsOk_paramsIdsWithSpqr_v1 C K idA idB ℓ hℓ,
        signalEncodeFits32_proto⟩
      lam qep q (by omega) hX hS hcoll0 D δ hδ A.refuseCorrB0 (refuseCorrB0_queries A q hq)
      (hfirstNE' InvPQ hS hInv_top)
    exact hle.trans (le_of_eq (by simp only [P, paramsV1_C]))
  · have ⟨x₀, hx₀⟩ :
        ∃ x₀ : BitVec 256, ∀ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base = Dh.dh x₀ Dh.base := by
      classical
      simpa only [not_forall, not_exists, not_ne_iff] using hcoll0
    have h1δ : (1 : ℝ≥0∞) ≤ δ := by
      have h := hδ (Dh.dh x₀ Dh.base)
      have huniv : {x : BitVec 256 | Dh.dh x Dh.base = Dh.dh x₀ Dh.base} = Set.univ :=
        Set.eq_univ_of_forall hx₀
      rwa [huniv, evalDist_apply_univ_eq_one] at h
    have hpow : (1 : ℝ≥0∞) ≤ (qep + 1) * (qep + 2) := by
      have hnat : 1 ≤ (qep + 1) * (qep + 2) := by nlinarith
      exact_mod_cast hnat
    have h1_le : (1 : ℝ≥0∞) ≤ (qep + 1) * (qep + 2) * δ := by
      simpa using mul_le_mul' hpow h1δ
    exact (evalDist_apply_le_one _ _).trans (h1_le.trans (le_add_of_nonneg_left zero_le))

end

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedEvict
