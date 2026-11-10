/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.QueryBounds
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.SimAndSM
public import Computational.Proofs.SpqrV1Sync.TopStateTight

/-!
# Query Invariants and SPQR Tightness for `simFig8ClampSan`

Proves query count, equal-public-challenge, and short-public-part invariants for `simFig8ClampSan`,
together with initial establishment and step preservation of `SanExtra`.
-/

@[expose] public section

set_option autoImplicit false

open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (evalCKS semCorrHookTGB semFwdAnswerHookS semFwdEvictHookS semFwdHookS semHandleHookDedupS semRecvHookS semResyncHookS)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM.Proofs.QueryBounds (FSpec QEq QInr hQu_QEq hQu_QInr isQueryBoundP_congr isQueryBoundP_simulateQ_run_zero)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM (QShort SendMsgsOk badSendMsg hQu_QShort shortB_mkPub)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey LengthsOk Params PublicKey signalWireCodec)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8Comp SemHook SimFig8C SimState inReceiveOnlyEpoch initSim mkPub onAcceptPure onAnswerPure semDrawSendCoins semSendHook simParseRecvC)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.SM (RecvResult noAliceCorrWhileAliceBelowEpoch10 noBobSendInEpoch0 partyEnc)

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8SanSem

open OracleSpec OracleComp
open CryptoVerification.E2E (Bytes paramsV1)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1 coinBytes)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight topStateTight_init topStateTight_send
  topStateTight_recv)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
  (simFig8OracleSan simFig8ClampSan SanExtra)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (fig8IdSemHook)

/-! ## Query invariants -/

section QueryInvariants

open CryptoGames.LibsignalSM.Proofs.QueryBounds
  (FSpec QInr QEq hQu_QInr hQu_QEq isQueryBoundP_congr isQueryBoundP_simulateQ_run_zero)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (QShort hQu_QShort SendMsgsOk badSendMsg shortB_mkPub)

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
      ((isQueryBoundP_query_iff p (.inl t) 0).2 fun h => absurd h (hQu t))
      fun u _ => ih u

private theorem simDrawSendCoins_isQueryBoundP {PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hQu : ∀ n, ¬ p (.inl n)) (r : Option PQC) :
    IsQueryBoundP (semDrawSendCoins
      (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) r) p 0 := by
  cases r with
  | none =>
    dsimp only [semDrawSendCoins, fig8IdSemHook]
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (p := p) (liftProb_isQueryBoundP_zero hQu ($ᵗ PQC))
      fun rq _ => isQueryBoundP_pure p (rq, none) 0
  | some rq =>
    dsimp only [semDrawSendCoins, fig8IdSemHook]
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (p := p) (liftProb_isQueryBoundP_zero hQu ($ᵗ (BitVec 256)))
      fun rc _ => isQueryBoundP_pure p (rq, some rc) 0

private theorem semSendHook_fig8_isQueryBoundP {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (qep d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hQu : ∀ n, ¬ p (.inl n))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hSendQ : ∀ pub rc,
      (∃ rq pn pq', mkPub (P := P) sC.base Q rq pn = some (pq', pub)) →
      (match chal with
       | none => p (.inr (.inl (.inl (.inl (.inl (Q, (pub, m₀), rc))))))
       | some m₁ => p (.inr (.inl (.inl (.inl (.inr (Q, (pub, m₀), (pub, m₁), rc))))))) → 0 < d) :
    IsQueryBoundP
      (semSendHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q m₀ chal r) p d := by
  unfold semSendHook
  by_cases hc1 : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp only [hc1, ↓reduceIte]; exact isQueryBoundP_pure p _ d
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · exact isQueryBoundP_pure p _ d
    · dsimp only []
      by_cases hc2 : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hc2, ↓reduceIte]; exact isQueryBoundP_pure p _ d
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        rw [← Nat.zero_add d]
        refine isQueryBoundP_bind (p := p) (simDrawSendCoins_isQueryBoundP hQu r)
          fun ⟨rq, rc⟩ _ => ?_
        dsimp only [fig8IdSemHook]
        rw [pure_bind]
        set pn : BitVec 32 := if s₁.epoch Q ≠ sC.base.mir.epoch Q
          then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
        rcases hmk : mkPub (P := P) sC.base Q rq pn with
          _ | ⟨pq', pub⟩
        · exact isQueryBoundP_pure p _ d
        · dsimp only []
          rw [← Nat.add_zero d]
          cases chal with
          | none =>
            refine isQueryBoundP_bind (p := p) ?_ fun x _ => ?_
            · dsimp only [CryptoGames.SM.transmitQuery]
              rw [← Nat.add_zero d]
              exact isQueryBoundP_bind (p := p)
                ((isQueryBoundP_query_iff p _ d).2 (hSendQ pub rc ⟨rq, pn, pq', hmk⟩))
                fun r₀ _ => isQueryBoundP_pure p (r₀, ()) 0
            · rcases x with ⟨_ | c, _⟩ <;> exact isQueryBoundP_pure p _ 0
          | some m₁ =>
            refine isQueryBoundP_bind (p := p) ?_ fun x _ => ?_
            · dsimp only [CryptoGames.SM.challQuery]
              rw [← Nat.add_zero d]
              exact isQueryBoundP_bind (p := p)
                ((isQueryBoundP_query_iff p _ d).2 (hSendQ pub rc ⟨rq, pn, pq', hmk⟩))
                fun r₀ _ => isQueryBoundP_pure p (r₀, ()) 0
            · rcases x with ⟨_ | c, _⟩ <;> exact isQueryBoundP_pure p _ 0

private theorem semRecvHookS_fig8_isQueryBoundP {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (T K qep B d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hDl : ∀ Q c, p (.inr (.inl (.inl (.inr (Q, c))))) → 0 < d)
    (hIj : ∀ Q c, p (.inr (.inl (.inr (Q, c)))) → 0 < d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool) :
    IsQueryBoundP
      (semRecvHookS P Dh encPt encT decT lam T K
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel) p d := by
  have hDlQ : ∀ c, IsQueryBoundP
      ((fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).onDl Q c ()) p d := fun c => by
    dsimp only [fig8IdSemHook, CryptoGames.SM.deliverQuery]
    rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hDl Q c)) fun res _ =>
      isQueryBoundP_pure p (res, ()) 0
  have hIjQ : ∀ c, IsQueryBoundP
      ((fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).onIj Q c ()) p d := fun c => by
    dsimp only [fig8IdSemHook, CryptoGames.SM.injectQuery]
    rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hIj Q c)) fun res _ =>
      isQueryBoundP_pure p (res, ()) 0
  have hAns : ∀ sC' ci? Tpk pq' c', IsQueryBoundP
      (semFwdAnswerHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w isDel ci? Tpk pq' c')
      p d := fun sC' ci? Tpk pq' c' => by
    unfold semFwdAnswerHookS
    dsimp only []
    rw [← Nat.add_zero d]
    refine isQueryBoundP_bind (p := p) ?_ fun ⟨res, _⟩ _ => isQueryBoundP_pure p _ 0
    split_ifs
    · exact hDlQ c'
    · exact hIjQ c'
  have hResync : ∀ sC' ci? Tpk pq' c r, IsQueryBoundP
      (semResyncHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w ci? Tpk pq' c r)
      p d := fun sC' ci? Tpk pq' c r => by
    unfold semResyncHookS
    rcases r with _ | ⟨t, i, ⟨pub, m'⟩⟩
    · exact isQueryBoundP_pure p _ d
    · rw [← Nat.add_zero d]
      refine isQueryBoundP_bind (p := p) (hDlQ c) fun ⟨res, _⟩ _ => ?_
      rcases res with _ | (_ | _) <;> exact isQueryBoundP_pure p _ 0
  have hEvict : ∀ sC' Tpk pq' c', IsQueryBoundP
      (semFwdEvictHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w isDel Tpk pq' c')
      p d := fun sC' Tpk pq' c' => by
    unfold semFwdEvictHookS
    split_ifs
    · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure p _ d
    · exact hAns sC' none Tpk pq' c'
  have hFwd : ∀ sC' ci? Tpk pq' hc c', IsQueryBoundP
      (semFwdHookS P Dh encPt encT lam T K
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC' () Q w isDel ci? Tpk pq'
          hc c')
      p d := fun sC' ci? Tpk pq' hc c' => by
    unfold semFwdHookS
    rcases hc with _ | c
    · exact hAns sC' ci? Tpk pq' c'
    · dsimp only []
      split_ifs
      · rcases evalCKS P Dh encPt encT lam T K B sC' Q w c c' with _ | r
        · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure p _ d
        · exact hResync sC' ci? Tpk pq' c r
      · exact hAns sC' ci? Tpk pq' c'
  unfold semRecvHookS
  dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩
    · exact isQueryBoundP_pure p _ d
    · rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) ||
                decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T₀
              · exact isQueryBoundP_pure p _ d
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
                        sC.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hFwd _ none pk pq' _ _
                · simp only [↓reduceIte]
                  exact hEvict _ pk pq' _
            · exact isQueryBoundP_pure p _ d
          · exact isQueryBoundP_pure p _ d
        · exact isQueryBoundP_pure p _ d
      · cases h5 :
          ((sC.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact hFwd sC (some ci) pk pq' _ _
        · exact isQueryBoundP_pure p _ d
  · simp only [↓reduceIte]; exact isQueryBoundP_pure p _ d

private theorem semCorrHookTGB_fig8_isQueryBoundP {PQ PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (Bsk d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hCr : ∀ Q, p (.inr (.inr Q)) → 0 < d)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    IsQueryBoundP
      (semCorrHookTGB P Dh encT
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) Bsk sC () Q) p d := by
  unfold semCorrHookTGB
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp only [hc, ↓reduceIte]; exact isQueryBoundP_pure p _ d
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [← Nat.add_zero d]
    refine isQueryBoundP_bind (p := p) ?_ fun x _ => ?_
    · dsimp only [fig8IdSemHook, CryptoGames.SM.corrQuery]
      rw [← Nat.add_zero d]
      exact isQueryBoundP_bind (p := p) ((isQueryBoundP_query_iff p _ d).2 (hCr Q)) fun st? _ =>
        isQueryBoundP_pure p _ 0
    · rcases x with ⟨_ | _, _⟩ <;> exact isQueryBoundP_pure p _ 0

private theorem simFig8OracleSan_step_isQueryBoundP {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk d : ℕ)
    {p : (FSpec Pt ℓ).Domain → Prop} [DecidablePred p]
    (hQu : ∀ n, ¬ p (.inl n))
    (hDl : ∀ Q c, p (.inr (.inl (.inl (.inr (Q, c))))) → 0 < d)
    (hIj : ∀ Q c, p (.inr (.inl (.inr (Q, c)))) → 0 < d)
    (hCr : ∀ Q, p (.inr (.inr Q)) → 0 < d)
    (o : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hSendQ : ∀ (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) pub rc,
      (∃ rq pn pq', mkPub (P := P) sC.base Q rq pn = some (pq', pub)) →
      (match chal with
       | none => p (.inr (.inl (.inl (.inl (.inl (Q, (pub, m₀), rc))))))
       | some m₁ => p (.inr (.inl (.inl (.inl (.inr (Q, (pub, m₀), (pub, m₁), rc))))))) → 0 < d) :
    IsQueryBoundP
      ((simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk (.inr o)).run sC) p d := by
  dsimp only [simFig8OracleSan, StateT.run, StateT.mk]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  rcases o with ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_fig8_isQueryBoundP P Dh encPt encT lam qep d hQu sC Q m none r
      (hSendQ Q m none)
  · exact semSendHook_fig8_isQueryBoundP P Dh encPt encT lam qep d hQu sC Q m₀ (some m₁) r
      (hSendQ Q m₀ (some m₁))
  · dsimp only [semHandleHookDedupS, fig8IdSemHook]
    rw [← Nat.add_zero d]
    exact isQueryBoundP_bind (p := p)
      (semRecvHookS_fig8_isQueryBoundP P Dh encPt encT decT lam T Kc qep B d hDl hIj sC Q w true)
      fun ⟨rr, sC₁, _⟩ _ => by rw [pure_bind]; exact isQueryBoundP_pure p _ 0
  · exact semRecvHookS_fig8_isQueryBoundP P Dh encPt encT decT lam T Kc qep B d hDl hIj sC Q w false
  · exact semCorrHookTGB_fig8_isQueryBoundP P Dh encT Bsk d hCr sC Q

/-- `simFig8ClampSan` makes at most `q` game queries whenever `A` makes at most `q` game
queries. -/
theorem simFig8ClampSan_queries {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) {q : ℕ}
    {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) q := by
  unfold CryptoGames.SM.MakesAtMostQueries simFig8ClampSan
  refine isQueryBoundP_congr (p := QInr Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind (p := QInr Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QInr ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QInr Pt ℓ) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp sC
      · cases hp
      · exact simFig8OracleSan_step_isQueryBoundP P Dh encPt encT decT lam qep B T Kc Bsk 1
          hQu_QInr (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one)
          (fun _ _ => Nat.zero_lt_one) o sC (fun _ _ _ _ _ _ _ => Nat.zero_lt_one)
    · rintro (n | o) hnp sC
      · dsimp only [simFig8OracleSan, StateT.lift, StateT.run, StateT.mk]
        rw [← Nat.add_zero 0]
        exact isQueryBoundP_bind (p := QInr Pt ℓ)
          ((isQueryBoundP_query_iff (QInr Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QInr n))
          fun u _ => isQueryBoundP_pure (QInr Pt ℓ) (u, sC) 0
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

/-- `simFig8ClampSan` always issues equal public parts on `chall` queries. -/
theorem simFig8ClampSan_equalPub {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
      (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) := by
  unfold CryptoGames.SM.EqualPubChalls simFig8ClampSan
  change IsQueryBoundP _ (QEq Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (p := QEq Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QEq ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QEq Pt ℓ) 0 := by
    refine isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
    rcases t with (n | o)
    · dsimp only [simFig8OracleSan, StateT.lift, StateT.run, StateT.mk]
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QEq Pt ℓ)
        ((isQueryBoundP_query_iff (QEq Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QEq n))
        fun u _ => isQueryBoundP_pure (QEq Pt ℓ) (u, sC) 0
    · refine simFig8OracleSan_step_isQueryBoundP P Dh encPt encT decT lam qep B T Kc Bsk 0
        hQu_QEq (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h) o sC
        (fun Q m₀ chal pub rc _ h => ?_)
      cases chal with
      | none => exact nomatch h
      | some m₁ => simp [QEq, CryptoGames.SM.unequalPubChall] at h
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

/-- `simFig8ClampSan` always issues `shortB = true` public parts on send/chall queries under
`LengthsOk P ℓ`. -/
theorem simFig8ClampSan_sendShort {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) := by
  unfold SendMsgsOk simFig8ClampSan
  change IsQueryBoundP _ (QShort Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (p := QShort Pt ℓ)
    (liftProb_isQueryBoundP_zero hQu_QShort ($ᵗ BitVec 256)) fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QShort Pt ℓ) 0 := by
    refine isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
    rcases t with (n | o)
    · dsimp only [simFig8OracleSan, StateT.lift, StateT.run, StateT.mk]
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QShort Pt ℓ)
        ((isQueryBoundP_query_iff (QShort Pt ℓ) (.inl n) 0).2 fun h => absurd h (hQu_QShort n))
        fun u _ => isQueryBoundP_pure (QShort Pt ℓ) (u, sC) 0
    · refine simFig8OracleSan_step_isQueryBoundP P Dh encPt encT decT lam qep B T Kc Bsk 0
        hQu_QShort (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ h => nomatch h) o sC
        (fun Q m₀ chal pub rc ⟨rq, pn, pq', hmk⟩ h => ?_)
      have hpub := shortB_mkPub hL sC.base Q rq pn hmk
      cases chal with
      | none => simp [QShort, badSendMsg, hpub] at h
      | some m₁ => simp [QShort, badSendMsg, hpub] at h
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

end QueryInvariants

/-! ## Generic `pq`-invariant preservation -/

section PqInv

def PqInv {PQ Pt : Type} {ℓ : ℕ} (G : PQ → Prop)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : Prop :=
  ∀ Q, G (sC.base.pq Q)

theorem pqInv_update {PQ : Type} {G : PQ → Prop} {f : Party → PQ} {Q : Party} {pq' : PQ}
    (hf : ∀ R, G (f R)) (h' : G pq') : ∀ R, G (Function.update f Q pq' R) := by
  intro R
  by_cases hR : R = Q
  · subst hR; simpa using h'
  · simpa [Function.update_of_ne hR] using hf R

theorem onAcceptPure_pq {PQ Pt : Type} {ℓ : ℕ} {G : PQ → Prop} (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, G (s.pq R)) (h' : G pq') :
    ∀ R, G ((onAcceptPure qep Q w isDel t i m ci? Tpk pq' s).2.pq R) := by
  have hu := pqInv_update (Q := Q) hs h'
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact hs
    · exact hu
    · exact hs
  · simp only [↓reduceIte]
    rcases s.mir.inTransit Q.other w with _ | r
    · exact hs
    · exact hu

theorem onAnswerPure_pq {PQ Pt : Type} {ℓ : ℕ} {G : PQ → Prop} (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hs : ∀ R, G (s.pq R)) (h' : G pq') :
    ∀ R, G ((onAnswerPure qep Q w isDel ci? Tpk pq' res s).2.pq R) := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact onAcceptPure_pq qep Q w isDel t i _ ci? Tpk pq' s hs h'

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt) {G : PQ → Prop}

omit [DecidableEq Pt] [Zero Pt] in
theorem mkPub_pq
    (hS : ∀ pq r pq' x, G pq → P.spqr.send pq r = some (pq', x) → G pq')
    (s : SimState PQ Pt ℓ) (Q : Party) (r : PQC) (pn : BitVec 32) (pq' : PQ)
    (pub : LibsignalMsgPublicPart) (h : mkPub P s Q r pn = some (pq', pub))
    (hs : G (s.pq Q)) : G pq' := by
  unfold mkPub at h
  rcases hsend : P.spqr.send (s.pq Q) r with _ | ⟨a, b⟩ <;> rw [hsend] at h
  · cases h
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact hS _ _ _ _ hs hsend

omit [DecidableEq Pt] [Zero Pt] in
theorem simParseRecvC_pq
    (hR : ∀ pq msg pq' salt, G pq → P.spqr.recv pq msg = .ok (pq', salt) → G pq')
    (B : ℕ) (qB : Bool) (pq : PQ) (w : List (BitVec 8)) (pq' : PQ)
    (rest : ℕ × (PublicKey × (Option Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (h : simParseRecvC P decT B qB pq w = some (pq', rest)) (hpq : G pq) : G pq' := by
  unfold simParseRecvC at h
  split_ifs at h
  dsimp only [] at h
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨hd, _⟩
  · rw [hparse] at h; cases h
  · rw [hparse] at h; dsimp only [] at h
    split_ifs at h
    rcases hrecv : P.spqr.recv pq hd.pqRatchet with _ | ⟨pq1, salt⟩
    · rw [hrecv] at h; cases h
    · rw [hrecv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact hR _ _ _ _ hpq hrecv

theorem semFwdAnswerHookS_pq {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hs : PqInv G sC₀) (h' : G pq') :
    ∀ x ∈ support (semFwdAnswerHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      PqInv G x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdAnswerHookS at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, -, _, rfl, _⟩ := hx
  exact onAnswerPure_pq qep Q w isDel ci? Tpk pq' res sC₀.base hs h'

omit [DecidableEq Pt] in
theorem semResyncHookS_pq {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hs : PqInv G sC₀) (h' : G pq') :
    ∀ x ∈ support (semResyncHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w ci? Tpk pq' c r),
      PqInv G x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semResyncHookS at hx
  rcases r with _ | ⟨t, i, _, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hx with ⟨_, rfl, _⟩
      exact onAcceptPure_pq qep Q w true t i m' ci? Tpk pq' sC₀.base hs h'

theorem semFwdEvictHookS_pq {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hs : PqInv G sC₀) (h' : G pq') :
    ∀ x ∈ support (semFwdEvictHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      PqInv G x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdEvictHookS at hx
  split_ifs at hx
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨_, -, _, rfl, _⟩ := hx; exact hs
  · exact semFwdAnswerHookS_pq P Dh encPt encT lam T sh qep
      sC₀ ex₀ Q w isDel none Tpk pq' c' hs h' _ hx

theorem semFwdHookS_pq {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T K : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hs : PqInv G sC₀) (h' : G pq') :
    ∀ x ∈ support
        (semFwdHookS P Dh encPt encT lam T K sh qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c'),
      PqInv G x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdHookS at hx
  rcases honestC with _ | c
  · exact semFwdAnswerHookS_pq P Dh encPt encT lam T sh qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' hs h' _ hx
  · dsimp only [] at hx
    split_ifs at hx
    · rcases hev : evalCKS P Dh encPt encT lam T K B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨_, -, _, rfl, _⟩ := hx; exact hs
      · exact semResyncHookS_pq P Dh encPt encT lam T sh qep
          sC₀ ex₀ Q w ci? Tpk pq' c r hs h' _ hx
    · exact semFwdAnswerHookS_pq P Dh encPt encT lam T sh qep
        sC₀ ex₀ Q w isDel ci? Tpk pq' c' hs h' _ hx

theorem semRecvHookS_pq {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (hR : ∀ pq msg pq' salt, G pq → P.spqr.recv pq msg = .ok (pq', salt) → G pq')
    (T K : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (hs : PqInv G sC₀) :
    ∀ x ∈ support (semRecvHookS P Dh encPt encT decT lam T K sh qep B sC₀ ex₀ Q w isDel),
      PqInv G x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semRecvHookS at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hparse] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, _⟩; exact hs
    · have h' : G pq' :=
        simParseRecvC_pq P decT hR _ _ _ w pq' _ hparse (hs Q)
      rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hsAmb : PqInv G
            ({ sC₀ with base :=
                if inReceiveOnlyEpoch sC₀.base.mir Q ||
                  (Q == CryptoGames.Party.A && (sC₀.base.chains Q).any (·.key.isNone))
                then { sC₀.base with amb := sC₀.base.amb + 1 } else sC₀.base } :
              LibsignalToModularSchemeSimState PQ Pt ℓ) := by
          intro R
          split_ifs <;> exact hs R
        by_cases hc1 :
            ((((sC₀.base.honest.find? fun wc =>
                wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
             (((sC₀.base.honest.find? fun wc =>
                wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hs
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨_, rfl, _⟩; exact hs
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) ||
                  decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨_, rfl, _⟩; exact hsAmb
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T₀ <;>
                simp only [hT] at hx
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                rcases hx with ⟨_, rfl, _⟩; exact hsAmb
              · by_cases hev_b :
                    ((((sC₀.base.honest.find? fun wc =>
                        wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  exact semFwdEvictHookS_pq P Dh encPt encT lam T sh qep
                    _ ex₀ Q w isDel pk pq' _ hsAmb h' _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHookS_pq P Dh encPt encT lam T K sh qep B
                    _ ex₀ Q w isDel none pk pq' _ _ hsAmb h' _ hx
      · by_cases hrej : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hs
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          exact semFwdHookS_pq P Dh encPt encT lam T K sh qep B
            sC₀ ex₀ Q w isDel (some ci) pk pq' _ _ hs h' _ hx

omit [DecidableEq Pt] in
theorem semSendHook_pq {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (hS : ∀ pq r pq' x, G pq → P.spqr.send pq r = some (pq', x) → G pq')
    (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hs : PqInv G sC₀) :
    ∀ x ∈ support (semSendHook P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ chal r),
      PqInv G x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semSendHook at hx
  by_cases href : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;>
      simp only [hep] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, _⟩; exact hs
    · by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨_, rfl, _⟩; exact hs
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
        obtain ⟨⟨rq, rc⟩, -, ⟨exOk, exFail⟩, -, hx⟩ := hx
        rcases hpub : mkPub P sC₀.base Q rq
          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hpub] at hx
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hs
        · have h' : G pq' := mkPub_pq P hS sC₀.base Q rq _ pq' pub hpub (hs Q)
          simp only [mem_support_bind_iff] at hx
          obtain ⟨⟨res, ex₂⟩, -, hx⟩ := hx
          rcases res with _ | c <;>
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          · rcases hx with ⟨_, rfl, _⟩; exact hs
          · rcases hx with ⟨_, rfl, _⟩
            exact pqInv_update (Q := Q) hs h'

omit [DecidableEq Pt] [Zero Pt] in
theorem semCorrHookTGB_pq {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T' Ex) (B_skip : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hs : PqInv G sC₀) :
    ∀ x ∈ support (semCorrHookTGB P Dh encT sh B_skip sC₀ ex₀ Q), PqInv G x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semCorrHookTGB at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hs
  · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hs
    · rcases hx with ⟨_, rfl, _⟩; exact hs

theorem semHandleHookDedupS_pq {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (hS : ∀ pq r pq' x, G pq → P.spqr.send pq r = some (pq', x) → G pq')
    (hR : ∀ pq msg pq' salt, G pq → P.spqr.recv pq msg = .ok (pq', salt) → G pq')
    (T K B_skip : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex)
    (hs : PqInv G sC₀) :
    ∀ x ∈ support (semHandleHookDedupS P Dh encPt encT decT lam T K B_skip sh qep B t sC₀ ex₀),
      PqInv G x.2.1 := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_pq P Dh encPt encT lam hS sh qep sC₀ ex₀ Q m₀ none r hs
  · exact semSendHook_pq P Dh encPt encT lam hS sh qep sC₀ ex₀ Q m₀ (some m₁) r hs
  · rintro ⟨_, sC₁, ex₁⟩ hx
    unfold semHandleHookDedupS at hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨rr, sC', ex'⟩, hrec, ex₂, -, _, rfl, rfl⟩ := hx
    exact semRecvHookS_pq P Dh encPt encT decT lam hR T K sh qep B
      sC₀ ex₀ Q w true hs (rr, sC₁, ex') hrec
  · exact semRecvHookS_pq P Dh encPt encT decT lam hR T K sh qep B sC₀ ex₀ Q w false hs
  · exact semCorrHookTGB_pq P Dh encT sh B_skip sC₀ ex₀ Q hs

end PqInv

/-! ## `SanExtra` for `paramsV1` -/

section SanExtraV1

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]

omit [DecidableEq Pt] [Zero Pt] in
theorem sanExtra_init (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (k : BitVec 256) :
    SanExtra (ℓ := ℓ) (Pt := Pt) C K
      (initSimC ((paramsV1 C K idA idB).spqr.init .a2b k)
        ((paramsV1 C K idA idB).spqr.init .b2a k)) := by
  intro Q
  cases Q
  · dsimp only [SanExtra, initSimC, initSim]
    exact topStateTight_init C.F K .a2b k
  · dsimp only [SanExtra, initSimC, initSim]
    exact topStateTight_init C.F K .b2a k

/-- `SanExtra` is preserved by every `simFig8OracleSan (paramsV1 C K idA idB)` game step. -/
theorem sanExtra_step (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep B T Kc Bsk : ℕ) :
    ∀ t (sC : LibsignalToModularSchemeSimState Bytes Pt ℓ), SanExtra C K sC →
      ∀ x ∈ support ((simFig8OracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep B T Kc Bsk (.inr t)).run sC), SanExtra C K x.2 := by
  intro t sC hsC x hx
  dsimp only [simFig8OracleSan, StateT.run, StateT.mk] at hx
  rw [support_map, Set.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hS : ∀ (pq : Bytes) (r : BitVec 512) (pq' : Bytes) x,
      TopStateTight C.F K pq → (paramsV1 C K idA idB).spqr.send pq r = some (pq', x) →
        TopStateTight C.F K pq' := by
    intro pq r pq' x hpq h
    rcases x with ⟨salt, msg⟩
    change (spqrV1 C.F K).send pq (coinBytes r) = some (pq', salt, msg) at h
    exact topStateTight_send C.F K hpq h
  have hR : ∀ (pq msg pq' : Bytes) salt,
      TopStateTight C.F K pq → (paramsV1 C K idA idB).spqr.recv pq msg = .ok (pq', salt) →
        TopStateTight C.F K pq' := by
    intro pq msg pq' salt hpq h
    change (spqrV1 C.F K).recv pq msg = .ok (pq', salt) at h
    exact topStateTight_recv C.F K hpq h
  exact semHandleHookDedupS_pq (paramsV1 C K idA idB) Dh encPt encT decT lam hS hR
    T Kc Bsk (fig8IdSemHook (PQC := BitVec 512) none) qep B t sC () hsC y hy

end SanExtraV1

end Computational.Proofs.Game.PromotedCostedReds.SimFig8SanSem
