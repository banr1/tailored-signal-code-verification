/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedBase
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.TrackHaltedEagerCore
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Eager
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Eager-coin bridges for tracker-halted `RefinementC`

Equivalence between the lazy tracker-halted `RefinementC` games and their eager-coin counterparts
(`runSimCEagerTrack`, `runWinAtCTrack`, and `runHidCTrack`).
-/

set_option autoImplicit false

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory
open Computational.Proofs.SpecLemmas.Session
open CryptoGames
open CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.CKA CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Proofs
open CryptoGames.CBC
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (Seed)
open CryptoVerification.SpqrV1Sync.Braid (EncRand)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section EagerBridge

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

private theorem tb_evalDist_bind_congr_support {α β : Type} [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    exact evalDist_bind_congr _ _ _ fun u =>
      ih u fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

private theorem tb_initSimC_pqInvB (P : Params PQ (BitVec 512)) (Inv : ℕ → PQ → Prop) (q : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (pqrKey : BitVec 256) :
    ∀ Q, InvB Inv q q
      ((initSimC (Pt := Pt) (ℓ := ℓ) (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).base.pq Q) := by
  intro Q
  cases Q <;> simpa [initSimC, initSim] using InvB.init hS _ pqrKey

private def tb_stPost {S α : Type} (fig : Fig8Sch Pt ℓ) (qep : ℕ)
    (post : S → α → S → Prop) (m : StateT S (Fig8Comp Pt ℓ) α) : Prop :=
  ∀ s s_f z, z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1)) (m.run s)).run s_f) → post s z.1.1 z.1.2

private theorem tb_stPost_pure {S α : Type} (fig : Fig8Sch Pt ℓ) (qep : ℕ)
    (post : S → α → S → Prop) (a : α) (h : ∀ s, post s a s) : tb_stPost fig qep post (pure a) := by
  intro s s_f z hz; simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact h s

private theorem tb_stPost_set_pure {S α : Type} (fig : Fig8Sch Pt ℓ) (qep : ℕ)
    (post : S → α → S → Prop) (s' : S) (a : α) (h : ∀ s, post s a s') :
    tb_stPost fig qep post (set s' >>= fun _ => pure a) := by
  intro s s_f z hz
  change z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1)) (pure (a, s'))).run s_f) at hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact h s

private theorem tb_stPost_get_bind {S α : Type} (fig : Fig8Sch Pt ℓ) (qep : ℕ)
    (post : S → α → S → Prop) (k : S → StateT S (Fig8Comp Pt ℓ) α)
    (hk : ∀ s, tb_stPost fig qep (fun s₀ a s' => s₀ = s → post s₀ a s') (k s)) :
    tb_stPost fig qep post (get >>= k) := by
  intro s s_f z hz; rw [StateT.run_bind, StateT.run_get, pure_bind] at hz; exact hk s s s_f z hz rfl

private theorem tb_stPost_lift_bind {S α β : Type} (fig : Fig8Sch Pt ℓ) (qep : ℕ)
    (post : S → β → S → Prop) (c : Fig8Comp Pt ℓ α) (k : α → StateT S (Fig8Comp Pt ℓ) β)
    (hk : ∀ a, tb_stPost fig qep post (k a)) : tb_stPost fig qep post (StateT.lift c >>= k) := by
  intro s s_f z hz
  have hrun : (StateT.lift c >>= k).run s = (c >>= fun a => (k a).run s) := by simp [StateT.run_bind, StateT.run_lift]
  rw [hrun, simulateQ_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨y, _, hz⟩; exact hk y.1 s y.2 z hz

private theorem tb_stPost_ite {S α : Type} (fig : Fig8Sch Pt ℓ) (qep : ℕ) (post : S → α → S → Prop)
    {P_cond : Prop} [Decidable P_cond] {t e : StateT S (Fig8Comp Pt ℓ) α}
    (ht : tb_stPost fig qep post t) (he : tb_stPost fig qep post e) :
    tb_stPost fig qep post (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]; exact ht; exact he

private theorem tb_simSendCTrackHalted_isNone_sC (P : Params PQ (BitVec 512)) (K : MlKem)
    (qep : ℕ) (fig : Fig8Sch Pt ℓ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (s_f : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (z : (Option (List (BitVec 8)) ×
        (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hz : z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1))
        ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (sC, tr))).run s_f))
    (hnone : z.1.1.isNone = true) :
    z.1.2.1 = sC := by
  suffices h : tb_stPost fig qep
      (fun st (ans : Option (List (BitVec 8))) st' => ans.isNone = true → st'.1 = st.1)
      (simSendCTrackHalted P K qep fig idHook Q m₀ chal r) from
    h (sC, tr) s_f z hz hnone
  unfold simSendCTrackHalted
  refine tb_stPost_get_bind fig qep _ _ fun ⟨sC₀, tr₀⟩ => ?_
  refine tb_stPost_ite fig qep _ (tb_stPost_pure fig qep _ _ fun _ h _ => by rw [h]) ?_
  cases sC₀.base.mir.epMgmt 3 qep Q r.isSome with
  | none => exact tb_stPost_pure fig qep _ _ fun _ h _ => by rw [h]
  | some s₁ =>
    refine tb_stPost_ite fig qep _ (tb_stPost_pure fig qep _ _ fun _ h _ => by rw [h]) ?_
    refine tb_stPost_lift_bind fig qep _ _ _ fun rq => ?_
    refine tb_stPost_ite fig qep _ (tb_stPost_set_pure fig qep _ _ _ fun _ h _ => by rw [h]) ?_
    refine tb_stPost_lift_bind fig qep _ _ _ fun rc => ?_
    cases LibsignalSim.mkPub (P := P) sC₀.base Q rq
        (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with
    | none => exact tb_stPost_set_pure fig qep _ _ _ fun _ h _ => by rw [h]
    | some pp =>
      rcases pp with ⟨pq', pub⟩
      refine tb_stPost_lift_bind fig qep _ _ _ fun res => ?_
      cases res with
      | none => exact tb_stPost_set_pure fig qep _ _ _ fun _ h _ => by rw [h]
      | some c => exact tb_stPost_set_pure fig qep _ _ _ fun _ _ hno => by simp at hno

private theorem tb_simSendStep_none_eq (P : Params PQ (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (Q : Party) (m₀ : Plain ℓ) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : BitVec 512) (c_cka : BitVec 256)
    (x : JointC PQ Pt ℓ) (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (hmk : LibsignalSim.mkPub (P := P) x.1.base Q rq
      (if s₁.epoch Q ≠ x.1.base.mir.epoch Q then BitVec.ofNat 32 (x.1.base.mir.idx Q - 1) else x.1.base.pn Q) =
      some (pq', pub)) :
    simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none bad s₁ rq c_cka x.sim =
      let z := transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q (pub, m₀) c_cka bad x.2.1
      match z.1 with
      | none => (none, (x.1.base, z.2))
      | some c =>
        let w := LibsignalSim.toWire c
        (some w, ({ x.1.base with
          mir := s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩ false,
          pq := Function.update x.1.base.pq Q pq',
          pn := Function.update x.1.base.pn Q
            (if s₁.epoch Q ≠ x.1.base.mir.epoch Q then BitVec.ofNat 32 (x.1.base.mir.idx Q - 1) else x.1.base.pn Q),
          honest := (w, c) :: x.1.base.honest }, z.2)) := by
  unfold simSendStep; dsimp only [JointC.sim]; rw [hmk]; rfl

private theorem tb_simSendStep_some_eq (P : Params PQ (BitVec 512)) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (Q : Party) (m₀ m₁ : Plain ℓ) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : BitVec 512) (c_cka : BitVec 256)
    (x : JointC PQ Pt ℓ) (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (hmk : LibsignalSim.mkPub (P := P) x.1.base Q rq
      (if s₁.epoch Q ≠ x.1.base.mir.epoch Q then BitVec.ofNat 32 (x.1.base.mir.idx Q - 1) else x.1.base.pn Q) =
      some (pq', pub)) :
    simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) bad s₁ rq c_cka x.sim =
      let z := challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad x.2.1
      match z.1 with
      | none => (none, (x.1.base, z.2))
      | some c =>
        let w := LibsignalSim.toWire c
        (some w, ({ x.1.base with
          mir := s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩ true,
          pq := Function.update x.1.base.pq Q pq',
          pn := Function.update x.1.base.pn Q
            (if s₁.epoch Q ≠ x.1.base.mir.epoch Q then BitVec.ofNat 32 (x.1.base.mir.idx Q - 1) else x.1.base.pn Q),
          honest := (w, c) :: x.1.base.honest }, z.2)) := by
  unfold simSendStep; dsimp only [JointC.sim]; rw [hmk]; rfl

private theorem tb_stepSimCTrackNoneSend_run_eq (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (hwin : x.2.1.win = false)
    (hpq : ∀ R, Inv (x.1.base.pq R))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSimCTrackNoneSend P K ℓ Dh encPt encT idOf lam qep Q m₀ chal r x tr =
      if x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q) then
        pure (none, (x, tr))
      else match x.1.base.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, (x, tr))
      | some s₁ =>
        if chal.isSome && !(s₁.safeCh 3 Q) then pure (none, (x, tr))
        else
          (match r with | some rq => pure rq | none => ($ᵗ BitVec 512 : ProbComp (BitVec 512))) >>= fun rq =>
          let tr' := stepKemFailSend P.C.F K tr Q rq
          if tr'.cand.isSome then
            pure (none, (x, { tr with cand := tr'.cand }))
          else
            ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
            let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r.isSome s₁ rq c_cka x.sim
            let tr'' := if res.1.isSome then tr' else { tr with cand := tr'.cand }
            pure (res.1, ((cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2), tr'')) := by
  unfold stepSimCTrackNoneSend simSendCTrackHalted
  dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : (x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q)) = true
  · simp [hstop]
  · simp only [hstop, Bool.false_eq_true, ↓reduceIte]
    cases hep : x.1.base.mir.epMgmt 3 qep Q r.isSome with
    | none => simp [hep]
    | some s₁ =>
      simp only [hep]
      by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp [hch]
      · simp only [hch, Bool.false_eq_true, ↓reduceIte]
        cases r with
        | some rq =>
          simp only [tb_idHook_lift, StateT.run_bind, StateT.run_lift, pure_bind,
            simulateQ_pure, bind_assoc]
          cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome with
          | true =>
            simp [hcand, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
          | false =>
            simp only [hcand, Bool.false_eq_true, ↓reduceIte, tb_idHook_lift, map_eq_bind_pure_comp,
              Function.comp_apply, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
            rw [simulateQ_fig8ImplH1_liftM_bind]
            simp only [bind_assoc]
            congr 1; funext c_cka
            have hmk := Option.isSome_iff_exists.mp (mkPub_isSomeW P Inv x.1.base Q rq
              (if s₁.epoch Q ≠ x.1.base.mir.epoch Q then BitVec.ofNat 32 (x.1.base.mir.idx Q - 1) else x.1.base.pn Q)
              hpq hW0)
            rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
            simp only [hmk, tb_idHook_lift, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
            cases chal with
            | none =>
              dsimp only [fig8ImplH1]; rw [simulateQ_transmitQuery_run]
              simp only [hwin, Bool.false_eq_true, ↓reduceIte, SM.samIfNec, pure_bind]
              rcases htp : transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q (pub, m₀) c_cka true x.2.1 with ⟨res_f, s_f'⟩
              simp only [Option.isSome, tb_simSendStep_none_eq P ℓ Dh encPt encT idOf lam qep Q m₀ true s₁ rq c_cka x pq' pub hmk, htp]
              cases res_f with
              | none => simp [cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
              | some c =>
                simp [cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
                cases (x.1.kept Q).full <;> rfl
            | some m₁ =>
              dsimp only [fig8ImplH1]; rw [simulateQ_challQuery_run]
              simp only [hwin, Bool.false_eq_true, ↓reduceIte, SM.samIfNec, pure_bind]
              rcases htp : challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Config.h1 Q (pub, m₀) (pub, m₁) c_cka true x.2.1 with ⟨res_f, s_f'⟩
              simp only [Option.isSome, tb_simSendStep_some_eq P ℓ Dh encPt encT idOf lam qep Q m₀ m₁ true s₁ rq c_cka x pq' pub hmk, htp]
              cases res_f with
              | none => simp [cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
              | some c =>
                simp [cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
                cases (x.1.kept Q).full <;> rfl
        | none =>
          simp only [tb_idHook_lift, StateT.run_bind, StateT.run_lift, bind_assoc]
          rw [simulateQ_fig8ImplH1_liftM_bind]; simp only [bind_assoc]; congr 1; funext rq
          cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome with
          | true => simp [hcand, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
          | false =>
            simp only [hcand, Bool.false_eq_true, ↓reduceIte, tb_idHook_lift, StateT.run_bind,
              StateT.run_lift, pure_bind, simulateQ_pure, bind_assoc]
            have hmk := Option.isSome_iff_exists.mp (mkPub_isSomeW P Inv x.1.base Q rq
              (if s₁.epoch Q ≠ x.1.base.mir.epoch Q then BitVec.ofNat 32 (x.1.base.mir.idx Q - 1) else x.1.base.pn Q) hpq hW0)
            rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
            simp only [hmk, tb_idHook_lift, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
            cases chal with
            | none =>
              dsimp only [fig8ImplH1]; rw [simulateQ_transmitQuery_run]
              simp only [hwin, Bool.false_eq_true, ↓reduceIte, SM.samIfNec, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]; congr 1; funext c_cka
              rcases htp : transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Q (pub, m₀) c_cka false x.2.1 with ⟨res_f, s_f'⟩
              simp only [Option.isSome, tb_simSendStep_none_eq P ℓ Dh encPt encT idOf lam qep Q m₀ false s₁ rq c_cka x pq' pub hmk, htp]
              cases res_f with
              | none => simp [cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
              | some c =>
                simp [cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
                cases (x.1.kept Q).full <;> rfl
            | some m₁ =>
              dsimp only [fig8ImplH1]; rw [simulateQ_challQuery_run]
              simp only [hwin, Bool.false_eq_true, ↓reduceIte, SM.samIfNec, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]; congr 1; funext c_cka
              rcases htp : challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Config.h1 Q (pub, m₀) (pub, m₁) c_cka false x.2.1 with ⟨res_f, s_f'⟩
              simp only [Option.isSome, tb_simSendStep_some_eq P ℓ Dh encPt encT idOf lam qep Q m₀ m₁ false s₁ rq c_cka x pq' pub hmk, htp]
              cases res_f with
              | none => simp [cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
              | some c =>
                simp [cxSend, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure]
                cases (x.1.kept Q).full <;> rfl

private theorem tb_evalDist_stepSimCEagerSendTrack_none (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (G : Option (List (BitVec 8)) → JointC PQ Pt ℓ × KemFailTrackState P.C.F →
      (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ R, Inv (x.1.base.pq R))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep none Q m₀ chal r x tr ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSimCTrackNoneSend P K ℓ Dh encPt encT idOf lam qep Q m₀ chal r x tr >>= fun res =>
        withEagerCoins res.2.1.1.base.mir (G res.1 res.2)] := by
  unfold stepSimCEagerSendTrack
  cases hcond : (!x.2.1.win && inReceiveOnlyEpoch x.1.base.mir Q &&
      !(x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q))) with
  | false =>
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let M := (simulateQ (fig8ImplH1 fig (qep + 1))
      ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (x.1, tr))).run x.2.1
    simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
    rw [evalDist_withEagerCoins_bind_swap x.1.base.mir M]
    unfold stepSimCTrackNoneSend
    simp only [bind_assoc, pure_bind]
    refine tb_evalDist_bind_congr_support M _ _ fun z hz => ?_
    cases hno : z.1.1.isNone with
    | true =>
      have hsC : z.1.2.1 = x.1 :=
        tb_simSendCTrackHalted_isNone_sC P K qep fig Q m₀ chal r x.1 tr x.2.1 z hz hno
      simp [hno, hsC]
    | false =>
      simp only [hno, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      simpa only [pure_bind] using
        evalDist_withEagerCoins_step_unused x.1.base.mir (pure z)
          (fun w => w.1.2.1.base.mir)
          (fun w ec' => G w.1.1 ((w.1.2.1, w.2, x.2.2), w.1.2.2) ec')
  | true =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    rcases hcond with ⟨⟨hwin, hinw⟩, hstop⟩
    rw [tb_stepSimCTrackNoneSend_run_eq P K Inv ℓ Dh encPt encT idOf lam qep Q m₀ chal r x tr hwin hpq hW0]
    simp only [hstop, Bool.false_eq_true, ↓reduceIte]
    cases hep : x.1.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      simp [hep]
    | some s₁ =>
      simp only [hep]
      cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) with
      | true =>
        simp [hch]
      | false =>
        simp only [hch, Bool.false_eq_true, ↓reduceIte, bind_assoc]
        cases r with
        | some rq =>
          simp only [pure_bind, Option.isSome_some]
          cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome with
          | true =>
            simp [hcand]
          | false =>
            simp only [hcand, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
            have hused := evalDist_withEagerCoins_used_pair_pure Q x.1.base.mir hinw
              (fun c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal true s₁ rq c_cka x.sim)
              (fun ans st' ec' => G ans
                ((cxSend P Dh encPt encT idOf lam Q x.1 st'.1 ans, st'.2, x.2.2),
                 if ans.isSome then stepKemFailSend P.C.F K tr Q rq
                 else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }) ec')
            simp only [bind_assoc, pure_bind] at hused
            exact hused.trans (by simp only [tb_cxSend_base])
        | none =>
          simp only [bind_assoc, Option.isSome_none]
          rw [evalDist_withEagerCoins_bind_swap x.1.base.mir ($ᵗ BitVec 512 : ProbComp (BitVec 512))]
          refine evalDist_bind_congr _ _ _ fun rq => ?_
          cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome with
          | true =>
            simp [hcand]
          | false =>
            simp only [hcand, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
            have hused := evalDist_withEagerCoins_used_pair_pure Q x.1.base.mir hinw
              (fun c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal false s₁ rq c_cka x.sim)
              (fun ans st' ec' => G ans
                ((cxSend P Dh encPt encT idOf lam Q x.1 st'.1 ans, st'.2, x.2.2),
                 if ans.isSome then stepKemFailSend P.C.F K tr Q rq
                 else { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }) ec')
            simp only [bind_assoc, pure_bind] at hused
            exact hused.trans (by simp only [tb_cxSend_base])

private theorem tb_evalDist_stepSimCEagerTrack_none (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (G : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      JointC PQ Pt ℓ × KemFailTrackState P.C.F → (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ R, Inv (x.1.base.pq R))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm x tr ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep q_sm x tr >>= fun r =>
        withEagerCoins r.2.1.1.base.mir (G r.1 r.2)] := by
  rcases q_sm with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · dsimp only [stepSimCEagerTrack]
    rw [tb_stepSimCTrackNone_transmit_eq]
    exact tb_evalDist_stepSimCEagerSendTrack_none P K Inv ℓ Dh encPt encT decT idOf lam qep
      Q m₀ none r x tr G hpq hW0
  · dsimp only [stepSimCEagerTrack]
    rw [tb_stepSimCTrackNone_chall_eq]
    exact tb_evalDist_stepSimCEagerSendTrack_none P K Inv ℓ Dh encPt encT decT idOf lam qep
      Q m₀ (some m₁) r x tr G hpq hW0
  · dsimp only [stepSimCEagerTrack]
    exact tb_evalDist_stepSimCEagerDeliverTrack_none P K ℓ Dh encPt encT decT idOf lam qep Q w x tr G
  · exact tb_evalDist_stepSimCEagerInjectTrack_none P K ℓ Dh encPt encT decT idOf lam qep Q w x tr G
  · exact tb_evalDist_stepSimCEagerCorrTrack_none P K ℓ Dh encPt encT decT idOf lam qep Q x tr G

private theorem tb_pq_update_inv {Inv' : PQ → Prop} {pq : Party → PQ} {Q : Party} {pq' : PQ}
    (hpq : ∀ R, Inv' (pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' (Function.update pq Q pq' R) := by
  intro R
  by_cases hR : R = Q
  · subst hR; simpa using hpq'
  · simpa [Function.update_of_ne hR] using hpq R

private theorem tb_mkPub_invB (P : Params PQ (BitVec 512)) {q r : ℕ} {Inv : ℕ → PQ → Prop}
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : BitVec 512) (pn : BitVec 32)
    (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (hpq : ∀ R, InvB Inv q r (s.pq R))
    (hmk : LibsignalSim.mkPub (P := P) s Q rq pn = some (pq', pub)) :
    InvB Inv q (r - 1) pq' := by
  unfold LibsignalSim.mkPub at hmk
  rw [Option.map_eq_some_iff] at hmk
  rcases hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  have hpq' : st' = pq' := congrArg Prod.fst hpair
  subst hpq'
  exact InvB.send hS hr0 (hpq Q) hsend

private theorem tb_onAcceptPure_pqInv (Inv' : PQ → Prop) (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv' (s.pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' ((onAcceptPure qep Q w isDel t i m ci? T pq' s).2.pq R) := by
  have hupd : ∀ R, Inv' (Function.update s.pq Q pq' R) := tb_pq_update_inv hpq hpq'
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit Q.other w with
    | none => exact hpq
    | some _ => exact hupd
  · split
    · exact hpq
    · split
      · exact hupd
      · exact hpq

private theorem tb_onAnswerPure_pqInv (Inv' : PQ → Prop) (qep : ℕ) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv' (s.pq R)) (hpq' : Inv' pq') :
    ∀ R, Inv' ((onAnswerPure qep Q w isDel ci? T pq' res s).2.pq R) := by
  unfold onAnswerPure
  cases res with
  | none => exact hpq
  | some r =>
    cases r with
    | rejected => exact hpq
    | accepted t i pm =>
      exact tb_onAcceptPure_pqInv Inv' qep Q w isDel t i _ ci? T pq' s hpq hpq'

private def tb_pres {α : Type} (Inv' : PQ → Prop)
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    (∀ R, Inv' (sC.base.pq R)) →
    ∀ r ∈ support ((m.run sC).run gh), ∀ R, Inv' (r.1.2.base.pq R)

private theorem tb_pres_pure {α : Type} (Inv' : PQ → Prop) (a : α) :
    tb_pres (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' (pure a) := by
  intro sC gh hpq r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact hpq

private theorem tb_pres_bind {α β : Type} {Inv' : PQ → Prop}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : tb_pres Inv' m) (hk : ∀ a, tb_pres Inv' (k a)) :
    tb_pres Inv' (m >>= k) := by
  intro sC gh hpq r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  exact hk r₁.1.1 r₁.1.2 r₁.2 (hm sC gh hpq r₁ hr₁) r hr

private theorem tb_pres_get (Inv' : PQ → Prop) :
    tb_pres (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' get := by
  intro sC gh hpq r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact hpq

private theorem tb_pres_get_bind {α : Type} {Inv' : PQ → Prop}
    {k : LibsignalToModularSchemeSimState PQ Pt ℓ →
      StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (hk : ∀ sC, (∀ R, Inv' (sC.base.pq R)) → tb_pres Inv' (k sC)) :
    tb_pres Inv' (get >>= k) := by
  intro sC gh hpq r hr
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind] at hr
  exact hk sC hpq sC gh hpq r hr

private theorem tb_pres_ite {α : Type} {Inv' : PQ → Prop} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : tb_pres Inv' t) (he : tb_pres Inv' e) :
    tb_pres Inv' (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem tb_pres_modify (Inv' : PQ → Prop)
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hf : ∀ sC, (f sC).base.pq = sC.base.pq) :
    tb_pres (PQ := PQ) (Pt := Pt) (ℓ := ℓ) Inv' (modify f) := by
  intro sC gh hpq r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr; rw [hf sC]; exact hpq

private theorem tb_pres_lift {α : Type} (Inv' : PQ → Prop) (u : ProbeM Pt ℓ α) :
    tb_pres (PQ := PQ) Inv'
      (StateT.lift u : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) := by
  intro sC gh hpq r hr
  change r ∈ support ((u >>= fun a => pure (a, sC)).run gh) at hr
  rw [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨_, _, hr⟩
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact hpq

private theorem tb_pres_zoomB_fwd (Inv' : PQ → Prop) (fig : Fig8Sch Pt ℓ)
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    tb_pres (PQ := PQ) Inv' (runOnBaseState (probeHook fig qepF) (LibsignalSim.fwd Q c')) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift ((LibsignalSim.fwd Q c').run sC.base) >>=
    fun p => pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  have hfwd : (LibsignalSim.fwd Q c').run sC.base = (LibsignalSim.fwd Q c' >>= pure).run sC.base := by
    simp
  rw [hfwd, StateT.run_bind, tb_probeHook_lift_run] at hr
  dsimp only [fig8ImplH1] at hr
  rw [simulateQ_fwd_run fig 3 qepF SM.Config.h1 Q c' pure sC.base gh.1] at hr
  simp only [StateT.run_pure, simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr; exact hpq

private theorem tb_pres_zoomB_onAnswer (Inv' : PQ → Prop) (qep : ℕ) (fig : Fig8Sch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq')
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) :
    tb_pres (PQ := PQ) Inv'
      (runOnBaseState (probeHook fig qepF)
        (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res)) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift
    ((LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res).run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, tb_probeHook_lift_run, onAnswer_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact tb_onAnswerPure_pqInv Inv' qep Q w isDel ci? T pq' res sC.base hpq hpq'

private theorem tb_pres_zoomB_onAccept (Inv' : PQ → Prop) (qep : ℕ) (fig : Fig8Sch Pt ℓ)
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') :
    tb_pres (PQ := PQ) Inv'
      (runOnBaseState (probeHook fig qepF)
        (LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq')) := by
  intro sC gh hpq r hr
  change r ∈ support ((((probeHook fig qepF).lift
    ((LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq').run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, tb_probeHook_lift_run, onAccept_run_eq] at hr
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact tb_onAcceptPure_pqInv Inv' qep Q w isDel t i m ci? T pq' sC.base hpq hpq'

private theorem tb_pres_fwdAnswerC (Inv' : PQ → Prop) (qep : ℕ) (fig : Fig8Sch Pt ℓ)
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (c' : Fig8C Pt) :
    tb_pres Inv' (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine tb_pres_bind (tb_pres_zoomB_fwd Inv' fig qepF Q c') fun res => ?_
  cases res with
  | none => exact tb_pres_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq' none
  | some r =>
    cases r with
    | rejected =>
      exact tb_pres_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq' (some .rejected)
    | accepted t i pm =>
      refine tb_pres_bind (tb_pres_modify Inv' _ (fun _ => rfl)) fun _ => ?_
      exact tb_pres_zoomB_onAnswer Inv' qep fig qepF Q w isDel ci? T pq' hpq' (some (.accepted t i pm))

private theorem tb_pres_resyncC (Inv' : PQ → Prop) (qep : ℕ) (fig : Fig8Sch Pt ℓ)
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (hpq' : Inv' pq') (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    tb_pres Inv' (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact tb_pres_pure Inv' _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine tb_pres_bind (tb_pres_lift Inv' _) fun res => ?_
    cases res with
    | none => exact tb_pres_pure Inv' _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        refine tb_pres_bind (tb_pres_modify Inv' _ (fun _ => rfl)) fun _ => ?_
        exact tb_pres_zoomB_onAccept Inv' qep fig qepF Q w true t i pm.2 ci? T pq' hpq'
      | _ => exact tb_pres_pure Inv' _

private theorem tb_pres_fwdC (P : Params PQ (BitVec 512)) (Inv' : PQ → Prop) (qep : ℕ)
    (fig : Fig8Sch Pt ℓ)
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    tb_pres Inv' (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold fwdC
  refine tb_pres_bind (tb_pres_get Inv') fun sC => ?_
  cases honestC with
  | none => exact tb_pres_fwdAnswerC Inv' qep fig fs qepF Q w isDel ci? T pq' hpq' c'
  | some c =>
    refine tb_pres_ite ?_ (tb_pres_fwdAnswerC Inv' qep fig fs qepF Q w isDel ci? T pq' hpq' c')
    cases predictReceiveWithSnapshots fig fs P sC Q w c c' with
    | some r => exact tb_pres_resyncC Inv' qep fig fs qepF Q w ci? T pq' hpq' c r
    | none =>
      exact tb_pres_bind (tb_pres_lift Inv' _) fun _ => tb_pres_pure Inv' _

private theorem tb_pres_fwdEvictC (Inv' : PQ → Prop) (qep : ℕ) (fig : Fig8Sch Pt ℓ)
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (hpq' : Inv' pq') (c' : Fig8C Pt) :
    tb_pres Inv' (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine tb_pres_bind (tb_pres_get Inv') fun sC => ?_
  refine tb_pres_ite ?_ (tb_pres_fwdAnswerC Inv' qep fig fs qepF Q w isDel none T pq' hpq' c')
  exact tb_pres_bind (tb_pres_lift Inv' _) fun _ => tb_pres_pure Inv' _

private theorem tb_pres_simRecvC (P : Params PQ (BitVec 512)) (Inv' : PQ → Prop)
    (hrecv : ∀ st msg st' salt, Inv' st → P.spqr.recv st msg = .ok (st', salt) → Inv' st')
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : Fig8Sch Pt ℓ)
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    tb_pres Inv' (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine tb_pres_get_bind fun sC hpq => ?_
  dsimp only
  refine tb_pres_ite (tb_pres_pure Inv' _) ?_
  refine tb_pres_ite (tb_pres_pure Inv' _) ?_
  refine tb_pres_ite (tb_pres_pure Inv' _) ?_
  refine tb_pres_ite (tb_pres_pure Inv' _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact tb_pres_pure Inv' _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine tb_pres_ite (tb_pres_pure Inv' _) ?_
    refine tb_pres_ite (tb_pres_pure Inv' _) ?_
    cases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact tb_pres_pure Inv' _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      have hpq' : Inv' pq' := hrecv (sC.base.pq Q) h.pqRatchet pq' salt (hpq Q) hspqr
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine tb_pres_ite (tb_pres_pure Inv' _) ?_
        exact tb_pres_fwdC P Inv' qep fig fs qepF Q w isDel (some ci) h.senderRatchetKey pq' hpq' _ _
      | none =>
        dsimp only
        refine tb_pres_ite (tb_pres_pure Inv' _) ?_
        refine tb_pres_ite (tb_pres_pure Inv' _) ?_
        refine tb_pres_ite
          (tb_pres_bind (tb_pres_modify Inv' _ (fun _ => rfl)) fun _ => ?_) ?_ <;>
        · refine tb_pres_ite (tb_pres_pure Inv' _) ?_
          cases decT h.senderRatchetKey with
          | none => exact tb_pres_pure Inv' _
          | some T =>
            exact tb_pres_ite
              (tb_pres_fwdEvictC Inv' qep fig fs qepF Q w isDel h.senderRatchetKey pq' hpq' _)
              (tb_pres_fwdC P Inv' qep fig fs qepF Q w isDel none h.senderRatchetKey pq' hpq' _ _)

private theorem tb_pres_simCorrC (P : Params PQ (BitVec 512)) (Inv' : PQ → Prop)
    (encT : Pt → PublicKey) (fig : Fig8Sch Pt ℓ) (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (Q : Party) :
    tb_pres Inv' (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  refine tb_pres_get_bind fun sC hpq => ?_
  dsimp only
  refine tb_pres_ite (tb_pres_pure Inv' _) ?_
  refine tb_pres_bind (tb_pres_lift Inv' _) fun ok => ?_
  cases ok with
  | none => exact tb_pres_pure Inv' _
  | some _st =>
    dsimp only
    intro _ gh _ r hr
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hpq

private theorem tb_pres_guardC {α : Type} {Inv' : PQ → Prop}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : tb_pres Inv' m) :
    tb_pres Inv' (guardC m) := by
  unfold guardC
  refine tb_pres_bind (tb_pres_get Inv') fun sC => ?_
  exact tb_pres_ite (tb_pres_pure Inv' none) hm

private theorem tb_simSendStep_preserves (P : Params PQ (BitVec 512)) (Inv : ℕ → PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rIsSome : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (rq : BitVec 512) (c_cka : BitVec 256) (x : JointC PQ Pt ℓ)
    (hpq : ∀ R, InvB Inv q r (x.1.base.pq R)) :
    ∀ R, InvB Inv q (r - 1)
      ((simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal rIsSome s₁ rq c_cka x.sim).2.1.pq R) := by
  have hpqm : ∀ R, InvB Inv q (r - 1) (x.1.base.pq R) :=
    fun R => InvB.mono (by omega) (hpq R)
  unfold simSendStep
  dsimp only [JointC.sim]
  cases hmk : mkPub P x.1.base Q rq
      (if s₁.epoch Q ≠ x.1.base.mir.epoch Q then BitVec.ofNat 32 (x.1.base.mir.idx Q - 1)
       else x.1.base.pn Q) with
  | none => exact hpqm
  | some pp =>
    rcases pp with ⟨pq', pub⟩
    have hpq' : InvB Inv q (r - 1) pq' := tb_mkPub_invB P hS hr0 x.1.base Q rq _ pq' pub hpq hmk
    have hupd : ∀ R, InvB Inv q (r - 1) (Function.update x.1.base.pq Q pq' R) :=
      tb_pq_update_inv hpqm hpq'
    dsimp only
    cases chal with
    | none =>
      cases (transmitPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1)
          Q (pub, m₀) c_cka rIsSome x.2.1).1 with
      | none => exact hpqm
      | some _ => exact hupd
    | some m₁ =>
      cases (challPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) Config.h1
          Q (pub, m₀) (pub, m₁) c_cka rIsSome x.2.1).1 with
      | none => exact hpqm
      | some _ => exact hupd

private theorem tb_simSendCTrackHalted_win_true (P : Params PQ (BitVec 512)) (K : MlKem)
    (qep : ℕ) (fig : Fig8Sch Pt ℓ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (s_f : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : s_f.win = true) :
    ∀ z ∈ support ((simulateQ (fig8ImplH1 fig (qep + 1))
        ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (sC, tr))).run s_f),
      z.1.2.1 = sC ∧ z.2 = s_f := by
  intro z hz
  unfold simSendCTrackHalted at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hstop : (sC.base.stopped || sC.base.mir.win || !(SM.noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp only [hstop, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl⟩
  · simp only [hstop, Bool.false_eq_true, ↓reduceIte] at hz
    cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl⟩
    | some s₁ =>
      simp only [hep] at hz
      by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, rfl⟩
      · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hz
        cases r with
        | some rq =>
          simp only [tb_idHook_lift, StateT.run_bind, StateT.run_lift, pure_bind, simulateQ_pure, bind_assoc] at hz
          cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome with
          | true =>
            simp only [hcand, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨rfl, rfl⟩
          | false =>
            simp only [hcand, Bool.false_eq_true, ↓reduceIte, tb_idHook_lift, map_eq_bind_pure_comp,
              Function.comp_apply, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind] at hz
            rw [simulateQ_fig8ImplH1_liftM_bind] at hz
            simp only [bind_assoc, MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨c_cka, _, hz⟩
            cases hmk : mkPub P sC.base Q rq
                (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with
            | none =>
              simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨rfl, rfl⟩
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              simp only [hmk, tb_idHook_lift, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind] at hz
              cases chal <;> dsimp only [fig8ImplH1] at hz <;>
                (first | rw [simulateQ_transmitQuery_run] at hz | rw [simulateQ_challQuery_run] at hz) <;>
                simp only [hwin, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                  simulateQ_pure, pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_apply,
                  support_pure, Set.mem_singleton_iff] at hz <;>
                (subst hz; exact ⟨rfl, rfl⟩)
        | none =>
          simp only [tb_idHook_lift, StateT.run_bind, StateT.run_lift, bind_assoc] at hz
          rw [simulateQ_fig8ImplH1_liftM_bind] at hz
          simp only [bind_assoc, MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨rq, _, hz⟩
          cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome with
          | true =>
            simp only [hcand, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              simulateQ_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨rfl, rfl⟩
          | false =>
            simp only [hcand, Bool.false_eq_true, ↓reduceIte, tb_idHook_lift, StateT.run_bind,
              StateT.run_lift, pure_bind, simulateQ_pure, bind_assoc] at hz
            cases hmk : mkPub P sC.base Q rq
                (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q) with
            | none =>
              simp only [hmk, StateT.run_bind, StateT.run_set, StateT.run_pure, simulateQ_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨rfl, rfl⟩
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              simp only [hmk, tb_idHook_lift, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind] at hz
              cases chal <;> dsimp only [fig8ImplH1] at hz <;>
                (first | rw [simulateQ_transmitQuery_run] at hz | rw [simulateQ_challQuery_run] at hz) <;>
                simp only [hwin, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                  simulateQ_pure, pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_apply,
                  support_pure, Set.mem_singleton_iff] at hz <;>
                (subst hz; exact ⟨rfl, rfl⟩)

private theorem tb_stepSimCTrackNoneSend_preserves (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rc : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (hpq : ∀ R, InvB Inv q r (x.1.base.pq R)) :
    ∀ z ∈ support (stepSimCTrackNoneSend P K ℓ Dh encPt encT idOf lam qep Q m₀ chal rc x tr),
      ∀ R, InvB Inv q (r - 1) (z.2.1.1.base.pq R) := by
  have hpqm : ∀ R, InvB Inv q (r - 1) (x.1.base.pq R) :=
    fun R => InvB.mono (by omega) (hpq R)
  intro z hz
  cases hwin : x.2.1.win with
  | true =>
    unfold stepSimCTrackNoneSend at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨w, hw, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨hsC, _⟩ := tb_simSendCTrackHalted_win_true P K qep _ Q m₀ chal rc x.1 tr x.2.1 hwin w hw
    dsimp only; rw [hsC]; exact hpqm
  | false =>
    rw [tb_stepSimCTrackNoneSend_run_eq P K (InvB Inv q r) ℓ Dh encPt encT idOf lam qep Q m₀ chal
      rc x tr hwin hpq (spqrCLocal_total hS hr0)] at hz
    by_cases hstop : (x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q)) = true
    · simp only [hstop, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hpqm
    · simp only [hstop, Bool.false_eq_true, ↓reduceIte] at hz
      cases hep : x.1.base.mir.epMgmt 3 qep Q rc.isSome with
      | none => simp only [hep, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hpqm
      | some s₁ =>
        simp only [hep] at hz
        cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) with
        | true => simp only [hch, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hpqm
        | false =>
          simp only [hch, Bool.false_eq_true, ↓reduceIte] at hz
          cases rc with
          | some rq =>
            simp only [pure_bind, Option.isSome_some] at hz
            cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome with
            | true =>
              simp only [hcand, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hpqm
            | false =>
              simp only [hcand, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
                support_pure, Set.mem_singleton_iff] at hz
              rcases hz with ⟨c_cka, _, rfl⟩
              simpa [tb_cxSend_base] using
                tb_simSendStep_preserves P Inv ℓ Dh encPt encT idOf lam qep q r hS hr0 Q m₀ chal
                  true s₁ rq c_cka x hpq
          | none =>
            simp only [Option.isSome_none, MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨rq, _, hz⟩
            cases hcand : (stepKemFailSend P.C.F K tr Q rq).cand.isSome with
            | true =>
              simp only [hcand, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hpqm
            | false =>
              simp only [hcand, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
                support_pure, Set.mem_singleton_iff] at hz
              rcases hz with ⟨c_cka, _, rfl⟩
              simpa [tb_cxSend_base] using
                tb_simSendStep_preserves P Inv ℓ Dh encPt encT idOf lam qep q r hS hr0 Q m₀ chal
                  false s₁ rq c_cka x hpq

private theorem tb_stepSimCTrackNone_preserves (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    (hS : SpqrCLocal P.spqr q Inv) (hr0 : 0 < r)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (hpq : ∀ R, InvB Inv q r (x.1.base.pq R)) :
    ∀ z ∈ support (stepSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep q_sm x tr),
      ∀ R, InvB Inv q (r - 1) (z.2.1.1.base.pq R) := by
  have hpqm : ∀ R, InvB Inv q (r - 1) (x.1.base.pq R) :=
    fun R => InvB.mono (by omega) (hpq R)
  intro z hz
  rcases q_sm with ((((⟨Q, m₀, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rw [tb_stepSimCTrackNone_transmit_eq] at hz
    exact tb_stepSimCTrackNoneSend_preserves P K Inv ℓ Dh encPt encT idOf lam qep q r
      hS hr0 Q m₀ none rc x tr hpq z hz
  · rw [tb_stepSimCTrackNone_chall_eq] at hz
    exact tb_stepSimCTrackNoneSend_preserves P K Inv ℓ Dh encPt encT idOf lam qep q r
      hS hr0 Q m₀ (some m₁) rc x tr hpq z hz
  · rw [tb_stepSimCTrackNone_deliver_eq, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    unfold stepSimCNone at hres
    rw [MonadAttach.mem_support_bind] at hres
    rcases hres with ⟨r₁, hr₁, hres⟩
    simp only [support_pure, Set.mem_singleton_iff] at hres; subst hres
    exact tb_pres_guardC
      (tb_pres_simRecvC P (InvB Inv q (r - 1)) (spqrCLocal_closedRecv hS) encT decT qep _ _
        (qep + 1) Q w true) x.1 x.2 hpqm r₁ hr₁
  · rw [tb_stepSimCTrackNone_inject_eq, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    unfold stepSimCNone at hres
    rw [MonadAttach.mem_support_bind] at hres
    rcases hres with ⟨r₁, hr₁, hres⟩
    simp only [support_pure, Set.mem_singleton_iff] at hres; subst hres
    exact tb_pres_guardC
      (tb_pres_simRecvC P (InvB Inv q (r - 1)) (spqrCLocal_closedRecv hS) encT decT qep _ _
        (qep + 1) Q w false) x.1 x.2 hpqm r₁ hr₁
  · rw [tb_stepSimCTrackNone_corr_eq, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    unfold stepSimCNone at hres
    rw [MonadAttach.mem_support_bind] at hres
    rcases hres with ⟨r₁, hr₁, hres⟩
    simp only [support_pure, Set.mem_singleton_iff] at hres; subst hres
    exact tb_pres_guardC
      (tb_pres_simCorrC P (InvB Inv q (r - 1)) encT _ (qep + 1) Dh Q) x.1 x.2 hpqm r₁ hr₁

private theorem tb_evalDist_runSimCEagerTrack_none {α : Type}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ)
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r)
    (hS : SpqrCLocal P.spqr q Inv)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (F : α → JointC PQ Pt ℓ × KemFailTrackState P.C.F → (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, InvB Inv q r (x.1.base.pq Q)) :
    𝒟[withEagerCoins x.1.base.mir (fun ec =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none oa x tr ec >>= fun res =>
        F res.1 res.2.1 res.2.2)] =
      𝒟[runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep oa x tr >>= fun res =>
        withEagerCoins res.2.1.1.base.mir (F res.1 res.2)] := by
  induction oa using OracleComp.inductionOn generalizing r x tr with
  | pure a =>
    simp only [runSimCEagerTrack_pure, runSimCTrackNone_pure, pure_bind]
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    cases t with
    | inl u =>
      have hq' : ∀ y, (cont y).IsQueryBoundP p r := fun y => by simpa [hp_inl u] using hq.2 y
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inl_bind, runSimCTrackNone_inl_bind, bind_assoc]
      rw [evalDist_withEagerCoins_bind_swap x.1.base.mir
        (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _)]
      refine evalDist_bind_congr _ _ _ fun y => ?_
      exact ih y r (hq' y) x tr hpq
    | inr q_sm =>
      have hr0 : 0 < r := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      have hq' : ∀ ans, (cont ans).IsQueryBoundP p (r - 1) := fun ans => by
        simpa [hp_inr q_sm] using hq.2 ans
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEagerTrack_inr_bind, runSimCTrackNone_inr_bind, bind_assoc]
      rw [tb_evalDist_stepSimCEagerTrack_none P K (InvB Inv q r) ℓ Dh encPt encT decT idOf lam
        qep q_sm x tr
        (fun ans xt' ec' =>
          runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none (cont ans) xt'.1 xt'.2 ec' >>=
          fun res => F res.1 res.2.1 res.2.2)
        hpq (spqrCLocal_total hS hr0)]
      refine tb_evalDist_bind_congr_support _ _ _ fun res hres => ?_
      have hpres := tb_stepSimCTrackNone_preserves P K Inv ℓ Dh encPt encT decT idOf lam qep q r
        hS hr0 q_sm x tr hpq res hres
      exact ih res.1 (r - 1) (hq' res.1) res.2.1 res.2.2 hpres

private theorem tb_evalDist_runSimCTrackNone_eq_withEagerCoins_runSimCEagerTrack
    (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) (hq : SM.MakesAtMostQueries A q)
    (hS : SpqrCLocal P.spqr q Inv)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F)
    (G : Bool → JointC PQ Pt ℓ × KemFailTrackState P.C.F → ProbComp Bool)
    (hpq : ∀ Q, InvB Inv q q (x.1.base.pq Q)) :
    𝒟[runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A x tr >>= fun r => G r.1 r.2] =
      𝒟[withEagerCoins x.1.base.mir (fun ec =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none A x tr ec >>=
        fun r => G r.1 r.2.1)] := by
  rw [tb_evalDist_runSimCEagerTrack_none P K Inv ℓ Dh encPt encT decT idOf lam qep q q
    (fun _ => by rintro ⟨⟩) (fun _ => rfl) A hq hS x tr (fun a s _ => G a s) hpq]
  refine evalDist_bind_congr _ _ _ fun r => ?_
  exact (evalDist_withEagerCoins_const r.2.1.1.base.mir (G r.1 r.2)).symm

/-- Eager-coin equivalence for `SM.game` on `runLibsignalToModularSchemeSimTrackHalted`. -/
theorem evalDist_game_simRunCTrackHalted_eq_eagerCTrack (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) (hq : SM.MakesAtMostQueries A q)
    (hS : SpqrCLocal P.spqr q Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[SM.game sm 3 (qep + 1) SM.Config.h1
        (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (initKemFailTrack P.C.F pqrKey)
            (fun Q => match Q with | .A => eA₀ | .B => 0) >>=
          fun z => pure ((b == z.1) || z.2.1.1.2.1.win)] := by
  intro sm
  rw [tb_game_simRunCTrackHalted_eq_runSimCTrackNone]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (initKemFailTrack P.C.F pqrKey) >>= fun z =>
          pure (b == z.1 || z.2.1.2.1.win)] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (initKemFailTrack P.C.F pqrKey)
            (fun Q => match Q with | .A => eA₀ | .B => 0) >>= fun z =>
            pure ((b == z.1) || z.2.1.1.2.1.win)] := by
    intro pqrKey
    rw [tb_evalDist_runSimCTrackNone_eq_withEagerCoins_runSimCEagerTrack P K Inv ℓ Dh encPt encT
      decT idOf lam qep q A hq hS
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
       SM.initState sm (k_root, x₀) b, false)
      (initKemFailTrack P.C.F pqrKey)
      (fun a s => pure (b == a || s.1.2.1.win))
      (tb_initSimC_pqInvB P Inv q hS pqrKey)]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

/-- Eager-coin equivalence for `simCNoneWinEventTrackHalted`. -/
theorem evalDist_simCNoneWinEventTrackHalted_eq_eagerCTrack (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) (hq : SM.MakesAtMostQueries A q)
    (hS : SpqrCLocal P.spqr q Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[simCNoneWinEventTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (initKemFailTrack P.C.F pqrKey)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) 0] := by
  intro sm
  rw [tb_simCNoneWinEventTrackHalted_eq_runSimCTrackNone]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (initKemFailTrack P.C.F pqrKey) >>= fun z =>
          pure z.2.1.2.1.win] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (initKemFailTrack P.C.F pqrKey)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) 0] := by
    intro pqrKey
    rw [tb_evalDist_runSimCTrackNone_eq_withEagerCoins_runSimCEagerTrack P K Inv ℓ Dh encPt encT
      decT idOf lam qep q A hq hS
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
       SM.initState sm (k_root, x₀) b, false)
      (initKemFailTrack P.C.F pqrKey)
      (fun _ s => pure s.1.2.1.win)
      (tb_initSimC_pqInvB P Inv q hS pqrKey)]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

/-- Eager-coin equivalence for `hiddenSaltGameTrackHalted`. -/
theorem evalDist_hiddenSaltGameTrackHalted_eq_eagerCTrack (P : Params PQ (BitVec 512)) (K : MlKem)
    (Inv : ℕ → PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) (hq : SM.MakesAtMostQueries A q)
    (hS : SpqrCLocal P.spqr q Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[hiddenSaltGameTrackHalted P K ℓ Dh encPt encT decT idOf lam qep A] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runHidCTrack P K ℓ Dh encPt encT decT idOf lam qep A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (initKemFailTrack P.C.F pqrKey)
            (fun Q => match Q with | .A => eA₀ | .B => 0)] := by
  intro sm
  rw [tb_hiddenSaltGameTrackHalted_eq_runSimCTrackNone]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[runSimCTrackNone P K ℓ Dh encPt encT decT idOf lam qep A
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b, false)
          (initKemFailTrack P.C.F pqrKey) >>= fun z =>
          pure z.2.1.2.2] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runHidCTrack P K ℓ Dh encPt encT decT idOf lam qep A
            (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b, false)
            (initKemFailTrack P.C.F pqrKey)
            (fun Q => match Q with | .A => eA₀ | .B => 0)] := by
    intro pqrKey
    rw [tb_evalDist_runSimCTrackNone_eq_withEagerCoins_runSimCEagerTrack P K Inv ℓ Dh encPt encT
      decT idOf lam qep q A hq hS
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
       SM.initState sm (k_root, x₀) b, false)
      (initKemFailTrack P.C.F pqrKey)
      (fun _ s => pure s.1.2.2)
      (tb_initSimC_pqInvB P Inv q hS pqrKey)]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

end EagerBridge

end CryptoGames.LibsignalSM.Proofs.Refinement
