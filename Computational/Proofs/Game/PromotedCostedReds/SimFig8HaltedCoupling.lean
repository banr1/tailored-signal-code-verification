/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedSanGame
import Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedTG
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep

/-!
# Game-Level Coupling for Tracker-Halted Figure 8 Simulation

Proves `SM.run`, `SM.game`, and `simCNoneWinEventHalted` equivalence between
`simFig8ClampSanHalted` and `libsignalToModularSchemeSimHalted` under `MakesAtMostQueries A q`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedCoupling

noncomputable section

open OracleComp OracleSpec
open CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Params PublicKey IdentityKey GhostState)
open CryptoGames.Ratchet.LibsignalInst
  (LibsignalMsgPublicPart lFS lFig8 ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C SimFig8C Fig8Comp SimState inReceiveOnlyEpoch mkPub toWire
   simParseRecvC evalCKClamp_eq_evalCK
   semFwdAnswerHook semResyncHook semFwdEvictHook semFwdHook semRecvHook semHandleHook
   SimBaseClampInv)
open CryptoGames.Ratchet.LibsignalSimC
  (Kept LibsignalToModularSchemeSimState idHook guardC
   predictReceiveWithSnapshots simRecvC simCorrC)
open CryptoGames.SM
  (GameState Record partyEnc noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10)
open CryptoVerification.LibsignalSpqrV1 (MlKem Bytes)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState stepKemFailSend stepKemFailDeliver)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
  (simSendCTrackHalted simImplCTrackHalted
   libsignalToModularSchemeSimHalted simCNoneWinEventHalted
   semSendHookHalted simFig8ClampSanHalted)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame
  (GameSanInv gameSanInv_transmitImpl gameSanInv_challImpl
   gameSanInv_deliverImpl gameSanInv_injectImpl gameSanInv_corrImpl)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
  (Fig8G fig8GameImpl simParseRecvC_tryFrom_and_idx)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (fig8IdSemHook semCorrHookTG simFig8OracleTG)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedSanGame
  (wrapHaltedOracle simFig8OracleTGHalted simFig8ClampOfHalted simFig8ClampTGHalted
   simulateQ_fig8GameImpl_liftProb simulateQ_fig8GameImpl_inl_halted
   simulateQ_fig8GameImpl_transmitQuery simulateQ_fig8GameImpl_challQuery
   simulateQ_fig8GameImpl_deliverQuery simulateQ_fig8GameImpl_injectQuery
   simulateQ_fig8GameImpl_corrQuery sm_run_simFig8ClampOfHalted_eq_of_inv
   getD_mem_of_findIdx?_eq_some stateT_lift_idHook_mem)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedTG
  (sm_run_simFig8ClampSanHalted_eq_tgHalted semRecvHook_idHook_eq semCorrHookTG_simImpl_eq
   TGInv tgInv_init epMgmt_bounds_local transmitImpl_tcur_epoch challImpl_tcur_epoch
   deliverImpl_tcur_epoch injectImpl_tcur_epoch onAcceptPure_clampInv_local
   onAnswerPure_clampInv_local predictReceiveWithSnapshots_epoch_eq)

section Hop3ClampInv

set_option exponentiation.threshold 1024 in
private theorem semSendHookHalted_tgInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q B m qep : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (gs : Fig8G Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (hqB : q + 2 ≤ B) (hInv : TGInv q B (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semSendHookHalted P K Dh encPt encT lam qep (sC, tr) Q m₀ chal r)).run gs),
      TGInv q B m x.1.2.1 x.2 := by
  intro fig ⟨⟨out₁, sC₁, tr₁⟩, gs₁⟩ hx
  have hm1 : m + 1 ≤ q := hInv.hgame.hm
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semSendHookHalted simSendCTrackHalted at hx
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hx
  dsimp only at hx
  by_cases href :
      (sC.base.stopped || sC.base.mir.win || !noBobSendInEpoch0 sC.base.mir Q) = true
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
              let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
                ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
              let base' : SimState PQ Pt ℓ := { sC.base with
                mir := s₁.record 3 Q () rec' chal.isSome,
                pq := Function.update sC.base.pq Q pq',
                pn := Function.update sC.base.pn Q pn,
                honest := (w, c) :: sC.base.honest }
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
          obtain ⟨rc, hx⟩ := hrc
          dsimp only [postRc] at hx
          rcases hmk : mkPub (P := P) sC.base Q rq
              (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
                BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with _ | ⟨pq', pub⟩ <;>
            simp only [hmk] at hx
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
          · obtain ⟨hs₁_ep, hs₁_tr, _⟩ := epMgmt_bounds_local hep
            have hbase_post : ∀ (c : Fig8C Pt),
                c.1.1 + m + 1 ≤ B → c.2.1 ≤ q - m →
                SimBaseClampInv B m
                  { sC.base with
                    mir := s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, toWire c⟩ chal.isSome,
                    pq := Function.update sC.base.pq Q pq',
                    pn := Function.update sC.base.pn Q
                      (if s₁.epoch Q ≠ sC.base.mir.epoch Q then
                        BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q),
                    honest := (toWire c, c) :: sC.base.honest } := by
              intro c hc1 hc2
              refine {
                hep := fun R => by
                  dsimp only [GameState.record]
                  have := hs₁_ep R; have := hInv.hbase.hep R; omega
                htrans := fun rec₀ hr => by
                  dsimp only [GameState.record] at hr
                  rcases List.mem_cons.mp hr with rfl | hr
                  · dsimp only; have := hs₁_ep Q; have := hInv.hbase.hep Q; omega
                  · rw [hs₁_tr] at hr; exact hInv0.hbase.htrans rec₀ hr
                hch := hInv0.hbase.hch
                hhonest := fun wc hwc => by
                  rcases List.mem_cons.mp hwc with rfl | hwc
                  · dsimp only; exact ⟨hc1, by omega⟩
                  · exact hInv0.hbase.hhonest wc hwc }
            cases chal with
            | none =>
              dsimp only [idHook] at hx
              simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind,
                simulateQ_fig8GameImpl_transmitQuery, mem_support_bind_iff] at hx
              obtain ⟨⟨res, gs'⟩, htr, hEq⟩ := hx
              obtain ⟨hg', hc2⟩ := gameSanInv_transmitImpl hInv.hgame htr
              obtain ⟨htcur', hc1⟩ := transmitImpl_tcur_epoch P Dh encPt encT _ lam hInv.htcur htr
              rcases res with _ | c <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
              · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', htcur', hInv0.hbase⟩
              · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩
                exact ⟨hg', htcur', hbase_post c (hc1 c rfl) (hc2 c rfl)⟩
            | some m₁ =>
              dsimp only [idHook] at hx
              simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind,
                simulateQ_fig8GameImpl_challQuery, mem_support_bind_iff] at hx
              obtain ⟨⟨res, gs'⟩, hch', hEq⟩ := hx
              obtain ⟨hg', hc2⟩ := gameSanInv_challImpl hInv.hgame hch'
              obtain ⟨htcur', hc1⟩ := challImpl_tcur_epoch P Dh encPt encT _ lam hInv.htcur hch'
              rcases res with _ | c <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hEq
              · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', htcur', hInv0.hbase⟩
              · rcases hEq with ⟨⟨_, rfl, _⟩, rfl⟩
                exact ⟨hg', htcur', hbase_post c (hc1 c rfl) (hc2 c rfl)⟩

private theorem semFwdAnswerHook_tgInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q B m qep : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (hg : GameSanInv q (m + 1) gs)
    (htcur : ∀ R : Party, (gs.st R).tcur + (m + 1) + 1 ≤ B)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hbase0 : SimBaseClampInv B m sC'.base)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semFwdAnswerHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep sC' () Q w isDel ci? Tpk pq' c')).run gs),
      TGInv q B m x.1.2.1 x.2 := by
  intro fig ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  unfold semFwdAnswerHook at hx; dsimp only at hx
  by_cases hinT :
      (sC'.base.honest.any fun wc =>
        decide (wc.2 = c') && (sC'.base.mir.inTransit Q.other wc.1).isSome) = true
  · simp only [hinT, ↓reduceIte, fig8IdSemHook, bind_assoc, pure_bind, simulateQ_bind,
      StateT.run_bind, simulateQ_fig8GameImpl_deliverQuery, mem_support_bind_iff,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨res, gs'⟩, hdl, ⟨_, rfl, _⟩, rfl⟩ := hx
    obtain ⟨hg', -⟩ := gameSanInv_deliverImpl hg hdl
    obtain ⟨htcur', ht_le⟩ := deliverImpl_tcur_epoch P Dh encPt encT _ lam htcur hdl
    exact ⟨hg', htcur', onAnswerPure_clampInv_local Q w isDel ci? Tpk pq' res sC'.base hbase0 ht_le⟩
  · simp only [hinT, Bool.false_eq_true, ↓reduceIte, fig8IdSemHook, bind_assoc, pure_bind,
      simulateQ_bind, StateT.run_bind, simulateQ_fig8GameImpl_injectQuery, mem_support_bind_iff,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨res, gs'⟩, hij, ⟨_, rfl, _⟩, rfl⟩ := hx
    obtain ⟨hg', -⟩ := gameSanInv_injectImpl hg hij
    obtain ⟨htcur', ht_le⟩ := injectImpl_tcur_epoch P Dh encPt encT _ lam htcur hij
    exact ⟨hg', htcur', onAnswerPure_clampInv_local Q w isDel ci? Tpk pq' res sC'.base hbase0 ht_le⟩

private theorem semResyncHook_tgInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q B m qep : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes)
    (hg : GameSanInv q (m + 1) gs)
    (htcur : ∀ R : Party, (gs.st R).tcur + (m + 1) + 1 ≤ B)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hbase0 : SimBaseClampInv B m sC'.base)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hr_ep : ∀ t_r i_r pm, r = some (t_r, i_r, pm) → t_r + m + 1 ≤ B) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semResyncHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep sC' () Q w ci? Tpk pq' c r)).run gs),
      TGInv q B m x.1.2.1 x.2 := by
  intro fig ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  unfold semResyncHook at hx
  rcases r with _ | ⟨t_r, i_r, pub_r, m_r⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
    dsimp only
    exact ⟨hg.mono (Nat.le_succ m), fun R => by have := htcur R; omega, hbase0⟩
  · dsimp only [fig8IdSemHook] at hx
    simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      simulateQ_fig8GameImpl_deliverQuery, mem_support_bind_iff] at hx
    obtain ⟨⟨res, gs'⟩, hdl, hx⟩ := hx
    obtain ⟨hg', -⟩ := gameSanInv_deliverImpl hg hdl
    obtain ⟨htcur', -⟩ := deliverImpl_tcur_epoch P Dh encPt encT _ lam htcur hdl
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', htcur', hbase0⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact ⟨hg', htcur', hbase0⟩
    · rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
      exact ⟨hg', htcur', onAcceptPure_clampInv_local Q w true t_r i_r m_r ci? Tpk pq'
        sC'.base hbase0 (hr_ep t_r i_r (pub_r, m_r) rfl)⟩

private theorem semFwdHook_tgInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q B m qep : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs : Fig8G Pt ℓ) (Q : Party) (w : Bytes) (isDel : Bool)
    (hg : GameSanInv q (m + 1) gs)
    (htcur : ∀ R : Party, (gs.st R).tcur + (m + 1) + 1 ≤ B)
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hbase0 : SimBaseClampInv B m sC'.base)
    (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (hc : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (ht_c' : c'.1.1 + m + 1 ≤ B) (hi_c' : c'.2.1 ≤ B) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semFwdHook P Dh encPt encT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep B sC' () Q w isDel ci? Tpk pq' hc c')).run gs),
      TGInv q B m x.1.2.1 x.2 := by
  intro fig x hx
  unfold semFwdHook at hx
  rcases hc with _ | c
  · exact semFwdAnswerHook_tgInv P Dh encPt encT lam cfg gs Q w isDel hg htcur sC' hbase0
      ci? Tpk pq' c' x hx
  · dsimp only at hx
    split at hx
    · rw [evalCKClamp_eq_evalCK P Dh encPt encT lam B sC' Q w c c' (by omega) hi_c'] at hx
      dsimp only at hx
      rcases hev : predictReceiveWithSnapshots (fig := fig)
          (fs := lFS P.C P.codec ℓ encT
            (fun R => if R == Party.A then P.idA else P.idB) 25000)
          P sC' Q w c c' with _ | r <;> rw [hev] at hx
      · rcases x with ⟨⟨_, sC₁, _⟩, gs₁⟩
        simp only [fig8IdSemHook, pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
        dsimp only
        exact ⟨hg.mono (Nat.le_succ m), fun R => by have := htcur R; omega, hbase0⟩
      · exact semResyncHook_tgInv P Dh encPt encT lam cfg gs Q w hg htcur sC' hbase0
          ci? Tpk pq' c r (fun t_r i_r pm hr => by
            have ht_eq := predictReceiveWithSnapshots_epoch_eq P Dh encPt encT _ lam sC' Q w c c'
              (hr ▸ hev)
            omega) x hx
    · exact semFwdAnswerHook_tgInv P Dh encPt encT lam cfg gs Q w isDel hg htcur sC' hbase0
        ci? Tpk pq' c' x hx

private theorem semRecvHook_tgInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q B m qep : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (h232 : 2 ^ 32 ≤ B) (hInv : TGInv q B (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
          qep B sC () Q w isDel)).run gs),
      TGInv q B m x.1.2.1 x.2 := by
  rintro fig ⟨⟨_, sC₁, _⟩, gs₁⟩ hx
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semRecvHook at hx
  by_cases href :
      (sC.base.stopped || sC.base.mir.win ||
        (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
          !sC.base.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp only [href, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;> simp only [hp] at hx
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
    · have hlct_B : lct.1 ≤ B := by
        obtain ⟨_, -, -, hlct_i, hi_le⟩ :=
          simParseRecvC_tryFrom_and_idx P decT Q (sC.base.pq Q) pq' w i pk T? lct hp
        omega
      let honestC : Option (SimFig8C Pt) :=
        (sC.base.honest.find? fun wc =>
          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      have hmkC : ∀ (t : ℕ) (T : Option Pt), t + m + 1 ≤ B →
          (match honestC with
           | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
           | none => ((t, T), lct)).1.1 + m + 1 ≤ B ∧
          (match honestC with
           | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
           | none => ((t, T), lct)).2.1 ≤ B := by
        intro t T ht_le
        rcases hhc : honestC with _ | c
        · exact ⟨ht_le, hlct_B⟩
        · obtain ⟨wc, hfind, rfl⟩ := Option.map_eq_some_iff.mp hhc
          have hwc := hInv.hbase.hhonest wc (List.mem_of_find?_eq_some hfind)
          dsimp only
          split_ifs
          · exact ⟨by have := hwc.1; omega, by have := hwc.2; omega⟩
          · exact ⟨ht_le, hlct_B⟩
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hbaseAmb : ∀ amb : Bool, SimBaseClampInv B m
            ({ sC with base := if amb then { sC.base with amb := sC.base.amb + 1 }
               else sC.base }.base) := fun amb => by
          cases amb
          · exact hInv0.hbase
          · exact ⟨hInv0.hbase.hep, hInv0.hbase.htrans, hInv0.hbase.hch, hInv0.hbase.hhonest⟩
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
              exact ⟨hInv0.hgame, hInv0.htcur, hbaseAmb _⟩
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T₀ <;> simp only [hT] at hx
              · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hx
                rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
                exact ⟨hInv0.hgame, hInv0.htcur, hbaseAmb _⟩
              · have hep1 : (sC.base.mir.epoch Q + 1) + m + 1 ≤ B := by
                  have := hInv.hbase.hep Q; omega
                by_cases hev_b :
                    ((((sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  unfold semFwdEvictHook at hx
                  have hsAmb_mir :
                      (if (inReceiveOnlyEpoch sC.base.mir Q ||
                            (Q == Party.A && (sC.base.chains Q).any fun x => x.key.isNone)) = true
                       then { sC.base with amb := sC.base.amb + 1 }
                       else sC.base).mir = sC.base.mir := by split_ifs <;> rfl
                  rw [hsAmb_mir] at hx
                  by_cases hev2 : (isDel && !sC.base.mir.safeInj 3) = true
                  · simp only [hev2, ↓reduceIte, fig8IdSemHook, pure_bind, simulateQ_pure,
                      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                    rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩
                    exact ⟨hInv0.hgame, hInv0.htcur, hbaseAmb _⟩
                  · simp only [hev2, Bool.false_eq_true, ↓reduceIte] at hx
                    exact semFwdAnswerHook_tgInv P Dh encPt encT lam cfg gs Q w isDel
                      hInv.hgame hInv.htcur _ (hbaseAmb _) none pk pq' _ _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  obtain ⟨ht_c', hi_c'⟩ := hmkC (sC.base.mir.epoch Q + 1) (some T₀) hep1
                  exact semFwdHook_tgInv P Dh encPt encT lam cfg gs Q w isDel
                    hInv.hgame hInv.htcur _ (hbaseAmb _) none pk pq' honestC _ ht_c' hi_c' _ hx
      · by_cases hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨⟨_, rfl, _⟩, rfl⟩; exact hInv0
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          have hgep : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch + m + 1 ≤ B := by
            have := hInv.hbase.hch Q _ (getD_mem_of_findIdx?_eq_some ⟨none, 0, 0, []⟩ hidx)
            omega
          obtain ⟨ht_c', hi_c'⟩ := hmkC
            (((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch) T? hgep
          exact semFwdHook_tgInv P Dh encPt encT lam cfg gs Q w isDel
            hInv.hgame hInv.htcur sC hInv0.hbase (some ci) pk pq' honestC _ ht_c' hi_c' _ hx

private theorem semCorrHookTG_tgInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q B m qep : ℕ}
    (P : Params PQ (BitVec 512)) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (lam : Pt) (B_skip? : Option ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) (Q : Party)
    (hInv : TGInv q B (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        (semCorrHookTG (PQC := BitVec 512) P Dh encT B_skip? sC Q)).run gs),
      TGInv q B m x.1.2 x.2 := by
  intro fig ⟨⟨_, sC₁⟩, gs₁⟩ hx
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold semCorrHookTG at hx
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
    obtain ⟨hg', -⟩ := gameSanInv_corrImpl hInv.hgame hcr
    have htcur' : ∀ R, (gs'.st R).tcur + m + 1 ≤ B := by
      unfold CryptoGames.SM.corrImpl at hcr
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hcr
      split_ifs at hcr <;>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hcr <;>
        rcases hcr with ⟨_, rfl⟩
      · exact hInv0.htcur
      · intro R; dsimp only [GameState.afterCorr, GameState.leak]; exact hInv0.htcur R
    rcases res with _ | fig8st <;>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
    · rcases hx with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hg', htcur', hInv0.hbase⟩
    · rcases hx with ⟨⟨_, rfl⟩, rfl⟩
      refine ⟨hg', htcur', {
        hep := fun R => by dsimp only [GameState.afterCorr, GameState.leak]; exact hInv0.hbase.hep R
        htrans := fun r hr => by
          dsimp only [GameState.afterCorr, GameState.leak] at hr; exact hInv0.hbase.htrans r hr
        hch := fun R g' hg' => by
          dsimp only at hg'
          split_ifs at hg'
          · rcases hγ : fig8st.γ with _ | x <;> simp only [hγ] at hg'
            · exact hInv0.hbase.hch R g' hg'
            · by_cases hR : R = .A
              · subst hR; simp only [Function.update_self, List.mem_map] at hg'
                obtain ⟨g₀, hg₀, rfl⟩ := hg'
                split_ifs <;> exact hInv0.hbase.hch .A g₀ hg₀
              · simp only [Function.update_of_ne hR] at hg'
                exact hInv0.hbase.hch R g' hg'
          · exact hInv0.hbase.hch R g' hg'
        hhonest := hInv0.hbase.hhonest }⟩

private theorem simFig8OracleTGHalted_step_eq_simImpl {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q B m qep Bsk : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (gs : Fig8G Pt ℓ)
    (h232 : 2 ^ 32 ≤ B) (hBsk : 25000 * q ≤ Bsk)
    (hInv : TGInv q B (m + 1) sC gs) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk) (.inr t)).run
        (sC, tr))).run gs =
    (simulateQ (fig8GameImpl fig qep cfg)
      ((simImplCTrackHalted P K encT decT qep fig fs idHook Dh (.inr t)).run (sC, tr))).run gs := by
  intro idOf fig fs
  have hInv0 := hInv.mono (Nat.le_succ m)
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · have hrcv := semRecvHook_idHook_eq P Dh encPt encT decT lam qep B sC Q w true h232
      (by have := hInv0.hbase.hep Q; omega)
      (fun g hg => by have := hInv0.hbase.hch Q g hg; omega)
      (fun wc hwc => by have := hInv0.hbase.hhonest wc hwc; exact ⟨by omega, by omega⟩)
    let k : Option (CryptoGames.SM.RecvResult (Plain ℓ)) → KemFailTrackState P.C.F := fun res =>
      match res, sC.base.honest.reverse.findIdx?
          (fun wc => wc.1 == (w : List (BitVec 8)) && Party.senderOf wc.2.1.1 == Q.other) with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    have hL :
        (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk)
          (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, tr) =
        ((Prod.map id Prod.fst <$>
            semRecvHook P Dh encPt encT decT lam
              (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
              qep B sC () Q w true) >>= fun x =>
          pure (x.1, (x.2, k x.1))) := by
      dsimp only [simFig8OracleTGHalted, wrapHaltedOracle, simFig8OracleTG,
        HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr, StateT.run, StateT.mk]
      have hstep :
          semHandleHook P Dh encPt encT decT lam
            (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
            qep B (.inl (.inl (.inr (Q, w)))) sC () =
          (semRecvHook P Dh encPt encT decT lam
            (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w true >>=
            fun y => pure () >>= fun ex₂ => pure (y.1, y.2.1, ex₂)) := rfl
      rw [hstep]
      simp only [pure_bind, map_bind, bind_map_left, map_pure, bind_assoc, Prod.map_apply, id_eq]
      refine bind_congr fun ⟨res, sC', _⟩ => ?_
      dsimp only [k, Prod.map]
      generalize sC.base.honest.reverse.findIdx? _ = j?
      rcases res with _ | r
      · cases j? <;> rfl
      · cases r <;> cases j? <;> rfl
    have hR :
        (simImplCTrackHalted P K encT decT qep fig fs idHook Dh
          (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, tr) =
        ((guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
            (fig := fig) (fs := fs) (H := idHook) Q w true)).run sC >>= fun x =>
          pure (x.1, (x.2, k x.1))) := by
      dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_lift,
        pure_bind, bind_assoc]
      refine bind_congr fun ⟨res, sC'⟩ => ?_
      dsimp only [k]
      generalize sC.base.honest.reverse.findIdx? _ = j?
      rcases res with _ | r
      · cases j? <;> simp
      · cases r <;> cases j? <;> simp
    rw [hL, hR, hrcv]
  · have hrcv := semRecvHook_idHook_eq P Dh encPt encT decT lam qep B sC Q w false h232
      (by have := hInv0.hbase.hep Q; omega)
      (fun g hg => by have := hInv0.hbase.hch Q g hg; omega)
      (fun wc hwc => by have := hInv0.hbase.hhonest wc hwc; exact ⟨by omega, by omega⟩)
    have hL :
        (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk)
          (.inr (.inl (.inr (Q, w))))).run (sC, tr) =
        (fun (a, sC') => (a, (sC', tr))) <$>
          (Prod.map id Prod.fst <$>
            semRecvHook P Dh encPt encT decT lam
              (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none)
              qep B sC () Q w false) := rfl
    have hR :
        (simImplCTrackHalted P K encT decT qep fig fs idHook Dh
          (.inr (.inl (.inr (Q, w))))).run (sC, tr) =
        (fun (a, sC') => (a, (sC', tr))) <$>
          (guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
            (fig := fig) (fs := fs) (H := idHook) Q w false)).run sC := by
      dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        StateT.run_lift, pure_bind, bind_assoc, map_eq_bind_pure_comp]
      exact bind_congr fun ⟨_, _⟩ => rfl
    rw [hL, hR, hrcv]
  · have hL :
        (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk)
          (.inr (.inr Q))).run (sC, tr) =
        (fun (a, sC') => (a, (sC', tr))) <$>
          semCorrHookTG (PQC := BitVec 512) P Dh encT (some Bsk) sC Q := rfl
    have hR :
        (simImplCTrackHalted P K encT decT qep fig fs idHook Dh (.inr (.inr Q))).run (sC, tr) =
        (fun (a, sC') => (a, (sC', tr))) <$>
          (guardC (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q)).run sC := by
      dsimp only [simImplCTrackHalted, HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inr]
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        StateT.run_lift, pure_bind, bind_assoc, map_eq_bind_pure_comp]
      exact bind_congr fun ⟨_, _⟩ => rfl
    rw [hL, hR]
    exact semCorrHookTG_simImpl_eq P Dh encPt encT lam cfg sC tr gs Q hBsk hInv.hgame

private theorem simFig8OracleTGHalted_step_tgInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ q B m qep Bsk : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (gs : Fig8G Pt ℓ)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B) (hInv : TGInv q B (m + 1) sC gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT
      (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
    ∀ x ∈ support ((simulateQ (fig8GameImpl fig qep cfg)
        ((simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk) (.inr t)).run
          (sC, tr))).run gs),
      TGInv q B m x.1.2.1 x.2 := by
  intro fig x hx
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHookHalted_tgInv P K Dh encPt encT lam cfg sC tr gs Q m₀ none r hqB hInv x hx
  · exact semSendHookHalted_tgInv P K Dh encPt encT lam cfg sC tr gs Q m₀ (some m₁) r hqB hInv x hx
  · have hstep :
        (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk)
          (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, tr) =
        (semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w true >>=
          fun y => pure (y.1, (y.2.1,
            match y.1, sC.base.honest.reverse.findIdx?
              (fun wc => wc.1 == (w : List (BitVec 8)) && Party.senderOf wc.2.1.1 == Q.other) with
            | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
            | _, _ => tr))) := by
      dsimp only [simFig8OracleTGHalted, wrapHaltedOracle, simFig8OracleTG,
        HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr, StateT.run, StateT.mk]
      change (Prod.map id Prod.fst <$> (semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w true >>=
          fun y => pure () >>= fun ex₂ => pure (y.1, y.2.1, ex₂))) >>= _ = _
      simp only [pure_bind, map_bind, map_pure, bind_assoc, Prod.map_apply, id_eq]
      refine bind_congr fun ⟨res, sC', _⟩ => ?_
      generalize sC.base.honest.reverse.findIdx? _ = j?
      rcases res with _ | r
      · cases j? <;> rfl
      · cases r <;> cases j? <;> rfl
    rw [hstep] at hx
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semRecvHook_tgInv P Dh encPt encT decT lam cfg sC gs Q w true h232 hInv y hy
  · have hstep :
        (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk)
          (.inr (.inl (.inr (Q, w))))).run (sC, tr) =
        ((fun y => (y.1, (y.2.1, tr))) <$> semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w false) := by
      dsimp only [simFig8OracleTGHalted, wrapHaltedOracle, simFig8OracleTG,
        HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, Sum.elim_inr, StateT.run, StateT.mk]
      change (fun (a, sC') => (a, (sC', tr))) <$> (Prod.map id Prod.fst <$>
        semRecvHook P Dh encPt encT decT lam
          (fig8IdSemHook (PQC := BitVec 512) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w false) = _
      simp only [Functor.map_map]; rfl
    rw [hstep, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semRecvHook_tgInv P Dh encPt encT decT lam cfg sC gs Q w false h232 hInv y hy
  · have hstep :
        (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk)
          (.inr (.inr Q))).run (sC, tr) =
        ((fun (a, sC') => (a, (sC', tr))) <$>
          semCorrHookTG (PQC := BitVec 512) P Dh encT (some Bsk) sC Q) := rfl
    rw [hstep, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact semCorrHookTG_tgInv P Dh encPt encT lam (some Bsk) cfg sC gs Q hInv y hy

private theorem sm_run_simFig8ClampTGHalted_eq {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B) (hBsk : 25000 * q ≤ Bsk) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then P.idA else P.idB
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampTGHalted P K ℓ Dh encPt encT decT lam qep B (some Bsk) A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (libsignalToModularSchemeSimHalted P K ℓ Dh encPt encT decT idOf lam qep A) := by
  intro idOf fig
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  change CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampOfHalted P (simFig8OracleTGHalted P K Dh encPt encT decT lam qep B (some Bsk)) A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampOfHalted P (simImplCTrackHalted P K encT decT qep fig fs idHook Dh) A)
  have hinl₂ : ∀ n sC tr gs,
      (simulateQ (fig8GameImpl fig qep cfg)
        ((simImplCTrackHalted P K encT decT qep fig fs idHook Dh (.inl n)).run (sC, tr))).run gs =
      (query (spec := unifSpec) n >>= fun u => pure ((u, (sC, tr)), gs)) := by
    intro n sC tr gs
    have h : (simImplCTrackHalted P K encT decT qep fig fs idHook Dh (.inl n)).run (sC, tr) =
        (liftM ((query (spec := unifSpec) n : ProbComp _) >>= fun u => pure (u, (sC, tr))) :
          Fig8Comp Pt ℓ _) := by
      change ((liftM (query (spec := unifSpec) n : ProbComp _) : Fig8Comp Pt ℓ _) >>=
        fun u => pure (u, (sC, tr))) = _
      rw [liftM_bind]; exact bind_congr fun _ => rfl
    rw [h, simulateQ_fig8GameImpl_liftProb, bind_assoc]
    exact bind_congr fun _ => by simp
  refine sm_run_simFig8ClampOfHalted_eq_of_inv P fig qep cfg b _ _
    (fun n sC tr gs => by
      dsimp only [simFig8OracleTGHalted, wrapHaltedOracle, simFig8OracleTG,
        HAdd.hAdd, Add.add, QueryImpl.add, Sum.elim_inl, StateT.run, StateT.mk]
      exact simulateQ_fig8GameImpl_inl_halted fig qep cfg n sC tr gs)
    hinl₂ hq (TGInv q B)
    (fun k pqrKey => tgInv_init P Dh encPt encT lam q B hqB k pqrKey b)
    (fun m t sC tr gs hInv =>
      simFig8OracleTGHalted_step_eq_simImpl P K Dh encPt encT decT lam cfg t sC tr gs
        h232 hBsk hInv)
    (fun m t sC tr gs hInv x hx => ?_)
  rw [← simFig8OracleTGHalted_step_eq_simImpl P K Dh encPt encT decT lam cfg t sC tr gs
    h232 hBsk hInv] at hx
  exact simFig8OracleTGHalted_step_tgInv P K Dh encPt encT decT lam cfg t sC tr gs
    h232 hqB hInv x hx

end Hop3ClampInv

theorem sm_run_simFig8ClampSanHalted_eq {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampSanHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (libsignalToModularSchemeSimHalted P K ℓ Dh encPt encT decT idOf lam qep A) := by
  have hid_eq : (fun R : Party => if R == Party.A then P.idA else P.idB) = idOf := funext hid
  subst hid_eq
  let _ := (inferInstance : Inhabited PQ)
  exact (sm_run_simFig8ClampSanHalted_eq_tgHalted P K Dh encPt encT decT lam qep B T Kc Bsk cfg b
    hq (by omega) (by omega)).trans
    (sm_run_simFig8ClampTGHalted_eq P K Dh encPt encT decT lam qep B Bsk cfg b hq h232 hqB hBsk)

theorem simFig8ClampSanHalted_sm_game_eq {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.game fig 3 (qep + 1) cfg
      (simFig8ClampSanHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A) =
    CryptoGames.SM.game fig 3 (qep + 1) cfg
      (libsignalToModularSchemeSimHalted P K ℓ Dh encPt encT decT idOf lam qep A) := by
  unfold CryptoGames.SM.game
  refine bind_congr fun b => ?_
  dsimp only
  rw [sm_run_simFig8ClampSanHalted_eq P K Dh encPt encT decT idOf hid lam qep B T Kc Bsk cfg b
    hq h232 hqB hT hKc hBsk]

theorem simFig8ClampSanHalted_simCNoneWinEvent_eq {PQ Pt : Type} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : ∀ R : Party, (if R == Party.A then P.idA else P.idB) = idOf R)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    {q : ℕ} {A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes}
    (hq : CryptoGames.SM.MakesAtMostQueries A q)
    (h232 : 2 ^ 32 ≤ B) (hqB : q + 2 ≤ B)
    (hT : 50000 * q ≤ T) (hKc : 25001 * q + 25000 ≤ Kc) (hBsk : 25000 * q ≤ Bsk) :
    simCNoneWinEventHalted P K ℓ Dh encPt encT decT idOf lam qep A =
    (do
      let b ← $ᵗ Bool
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let (_, s) ← CryptoGames.SM.run fig 3 (qep + 1) CryptoGames.SM.Config.h1 b
        (simFig8ClampSanHalted P K ℓ Dh encPt encT decT lam qep B T Kc Bsk A)
      return s.win) := by
  unfold simCNoneWinEventHalted
  refine bind_congr fun b => ?_
  dsimp only
  rw [sm_run_simFig8ClampSanHalted_eq P K Dh encPt encT decT idOf hid lam qep B T Kc Bsk
    CryptoGames.SM.Config.h1 b hq h232 hqB hT hKc hBsk]

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8HaltedCoupling
