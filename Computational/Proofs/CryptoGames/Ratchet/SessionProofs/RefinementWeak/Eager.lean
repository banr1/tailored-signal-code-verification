/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrHyp
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement

/-!
# Eager coins under the weak SPQR hypothesis

Adapts the eager-coin simulation equivalences of `Refinement/Simulation.lean` and
`Refinement.lean` to `SimInvW` and `SpqrWLocal`, showing that simulator steps preserve `Inv`
on SPQR states.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

theorem mkPub_isSomeW (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32)
    (hpq : ∀ Q, Inv (s.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    (LibsignalSim.mkPub (P := P) s Q rq pn).isSome := by
  simp [LibsignalSim.mkPub, hW0 (s.pq Q) rq (hpq Q)]

theorem stepSim_send_run_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
      SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
    (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
      (fun x => pure (x.1.1, (x.1.2, x.2))) =
    if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
    else match st.1.mir.epMgmt 3 qep Q r.isSome with
    | none => pure (none, st)
    | some s₁ =>
      if chal.isSome && !(s₁.safeCh 3 Q) then pure (none, st)
      else
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r.isSome s₁ rq c_cka st) := by
  intro sm impl
  unfold LibsignalSim.guard LibsignalSim.simSend
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : st.1.stopped
  · simp [hstop]
  · simp only [hstop, Bool.false_eq_true, Bool.false_or, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir]
    · simp only [hmir, Bool.false_eq_true, ite_false]
      cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => simp [hep]
      | some s₁ =>
        simp only [hep]
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ite_false]
          cases r with
          | some rq =>
            simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
            rw [simulateQ_coin_run]
            simp only [bind_assoc, pure_bind]
            congr 1; funext c_cka
            unfold simSendStep
            have hmk := Option.isSome_iff_exists.mp (mkPub_isSomeW P Inv st.1 Q rq
              (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q)
              hpq hW0)
            rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
            simp only [hmk]
            cases chal with
            | none =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_transmitQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, pure_bind]
              cases hz : (transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka true st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
            | some m₁ =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_challQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, pure_bind]
              cases hz : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka true st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
          | none =>
            simp only [pure_bind, bind_assoc]
            rw [simulateQ_coin_run]
            simp only [bind_assoc, pure_bind]
            congr 1; funext rq
            unfold simSendStep
            have hmk := Option.isSome_iff_exists.mp (mkPub_isSomeW P Inv st.1 Q rq
              (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q)
              hpq hW0)
            rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
            simp only [hmk]
            cases chal with
            | none =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_transmitQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              congr 1; funext c_cka
              cases hz : (transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka false st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
            | some m₁ =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_challQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              congr 1; funext c_cka
              cases hz : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka false st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]

theorem stepSimNone_transmit_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSimNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inl (Q, m₀, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) := by
  have h := stepSim_send_run_eqW P Inv ℓ Dh encPt encT idOf lam qep Q m₀ none r st hwin hpq hW0
  simpa [stepSimNone, LibsignalSim.simImpl] using h

theorem stepSimNone_chall_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSimNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        if !(s₁.safeCh 3 Q) then pure (none, st)
        else
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) := by
  have h := stepSim_send_run_eqW P Inv ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r st hwin hpq hW0
  simpa [stepSimNone, LibsignalSim.simImpl] using h

theorem stepSim_transmit_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) := by
  cases k <;> exact stepSimNone_transmit_eqW P Inv ℓ Dh encPt encT decT idOf lam qep Q m₀ r st hwin hpq hW0

theorem stepSim_chall_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        if !(s₁.safeCh 3 Q) then pure (none, st)
        else
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) := by
  cases k <;> exact stepSimNone_chall_eqW P Inv ℓ Dh encPt encT decT idOf lam qep Q m₀ m₁ r st hwin hpq hW0

theorem evalDist_stepSimEagerTransmitW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (List (BitVec 8)) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerTransmit
  cases hcond : !st.2.win && inReceiveOnlyEpoch st.1.mir Q && !(st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q))
  · exact evalDist_withEagerCoins_unused_pair st.1.mir
      (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st) G
  · cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      exact evalDist_withEagerCoins_unused_pair st.1.mir
        (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st) G
    | some s₁ =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      rcases hcond with ⟨⟨hwin, hinw⟩, hstop⟩
      refine (evalDist_withEagerCoins_used_pair Q st.1.mir hinw
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC))
        (fun rq c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) G).trans ?_
      rw [stepSim_transmit_eqW P Inv ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st hwin hpq hW0]
      rw [hstop, hep]
      rfl

theorem evalDist_stepSimEagerChallW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (List (BitVec 8)) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerChall
  cases hcond : !st.2.win && inReceiveOnlyEpoch st.1.mir Q && !(st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q))
  · exact evalDist_withEagerCoins_unused_pair st.1.mir
      (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G
  · cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      exact evalDist_withEagerCoins_unused_pair st.1.mir
        (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G
    | some s₁ =>
      dsimp only
      cases hch : !(s₁.safeCh 3 Q)
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        rcases hcond with ⟨⟨hwin, hinw⟩, hstop⟩
        refine (evalDist_withEagerCoins_used_pair Q st.1.mir hinw
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC))
          (fun rq c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) G).trans ?_
        rw [stepSim_chall_eqW P Inv ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st hwin hpq hW0]
        rw [hstop, hep]
        dsimp only
        rw [hch]
        rfl
      · exact evalDist_withEagerCoins_unused_pair st.1.mir
          (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G

theorem evalDist_stepSimEagerW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q st ec >>= fun r =>
        G r.1 r.2.1 r.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k q st >>= fun r =>
        withEagerCoins r.2.1.mir (G r.1 r.2)] := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact evalDist_stepSimEagerTransmitW P Inv ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st G hpq hW0
  · exact evalDist_stepSimEagerChallW P Inv ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st G hpq hW0
  · exact evalDist_stepSimEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w st G
  · exact evalDist_stepSimEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w st G
  · exact evalDist_stepSimEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q st G

namespace WP2A.E4

private theorem pq_update_inv {PQ : Type} {Inv : PQ → Prop} {pq : Party → PQ} {Q : Party} {pq' : PQ}
    (hpq : ∀ R, Inv (pq R)) (hpq' : Inv pq') :
    ∀ R, Inv (Function.update pq Q pq' R) := by
  intro R
  by_cases hR : R = Q
  · subst hR; simpa using hpq'
  · simpa [Function.update_of_ne hR] using hpq R

private theorem mkPub_inv (P : Params PQ PQC) (Inv : PQ → Prop)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32)
    (pq' : PQ) (pub : LibsignalMsgPublicPart)
    (hpq : ∀ R, Inv (s.pq R))
    (hmk : LibsignalSim.mkPub (P := P) s Q rq pn = some (pq', pub)) :
    Inv pq' := by
  unfold LibsignalSim.mkPub at hmk
  rw [Option.map_eq_some_iff] at hmk
  rcases hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  have hpq' : st' = pq' := congrArg Prod.fst hpair
  subst hpq'
  exact hcl.send (s.pq Q) rq st' salt msg (hpq Q) hsend

private theorem onAcceptPure_pqInv (Inv : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv (s.pq R)) (hpq' : Inv pq') :
    ∀ R, Inv ((onAcceptPure qep Q w isDel t i m ci? T pq' s).2.pq R) := by
  have hupd : ∀ R, Inv (Function.update s.pq Q pq' R) := pq_update_inv hpq hpq'
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

private theorem onAnswerPure_pqInv (Inv : PQ → Prop) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hpq : ∀ R, Inv (s.pq R)) (hpq' : Inv pq') :
    ∀ R, Inv ((onAnswerPure qep Q w isDel ci? T pq' res s).2.pq R) := by
  unfold onAnswerPure
  cases res with
  | none => exact hpq
  | some r =>
    cases r with
    | rejected => exact hpq
    | accepted t i pm =>
      exact onAcceptPure_pqInv Inv qep Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq' s hpq hpq'

private theorem simRecvStep_pqInv (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ R, Inv (st.1.pq R)) :
    ∀ R, Inv ((simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel c_cka st).2.1.pq R) := by
  unfold simRecvStep
  dsimp only
  by_cases hstop : st.1.stopped
  · simp only [hstop, ite_true]; exact hpq
  · simp only [hstop, Bool.false_eq_true, ite_false]
    by_cases hmir : st.1.mir.win
    · simp only [hmir, ite_true]; exact hpq
    · simp only [hmir, Bool.false_eq_true, ite_false]
      by_cases hdel : isDel && (st.1.mir.inTransit Q.other w).isNone
      · simp only [hdel, ite_true]; exact hpq
      · simp only [hdel, Bool.false_eq_true, ite_false]
        by_cases hinj : !isDel && ((st.1.mir.inTransit Q.other w).isSome || !(st.1.mir.safeInj 3)
            || !(ratchetKeyAdmissible P.codec decT encT w))
        · simp only [hinj, ite_true]; exact hpq
        · simp only [hinj, Bool.false_eq_true, ite_false]
          by_cases hlen : w.length < 9
          · simp only [hlen, ite_true]; exact hpq
          · simp only [hlen, ite_false]
            cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
            | none => exact hpq
            | some hb =>
              rcases hb with ⟨h, _⟩
              dsimp only
              by_cases haddr : !(addressCheckPasses h.addresses (P.expectedAddrs Q))
              · simp only [haddr, ite_true]; exact hpq
              · simp only [haddr, Bool.false_eq_true, ite_false]
                cases hspqr : P.spqr.recv (st.1.pq Q) h.pqRatchet with
                | error _ => exact hpq
                | ok ps =>
                  rcases ps with ⟨pq', salt⟩
                  have hpq' : Inv pq' := hcl.recv (st.1.pq Q) h.pqRatchet pq' salt (hpq Q) hspqr
                  dsimp only
                  cases hci : (st.1.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
                  | some ci =>
                    dsimp only
                    by_cases hrej : ((st.1.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1)
                    · simp only [hrej, ite_true]; exact hpq
                    · simp only [hrej, Bool.false_eq_true, ite_false]
                      exact onAnswerPure_pqInv Inv qep Q w isDel (some ci) h.senderRatchetKey pq' _ st.1 hpq hpq'
                  | none =>
                    dsimp only
                    by_cases hevict : (((st.1.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                        fun c => decide (c.1.1 ≠ st.1.mir.epoch Q + 1)) == some true
                    · simp only [hevict, ite_true]; exact hpq
                    · simp only [hevict, Bool.false_eq_true, ite_false]
                      by_cases hzero : decT h.senderRatchetKey == some 0
                      · simp only [hzero, ite_true]; exact hpq
                      · simp only [hzero, Bool.false_eq_true, ite_false]
                        by_cases hamb_k : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any (·.key.isNone))) &&
                            k == some st.1.amb
                        · simp only [hamb_k, ite_true]
                          by_cases hamb : inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any (·.key.isNone)) <;>
                            simp only [hamb, ite_true, Bool.false_eq_true, ite_false] <;> exact hpq
                        · simp only [hamb_k, Bool.false_eq_true, ite_false]
                          by_cases hamb : inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any (·.key.isNone)) <;>
                            simp only [hamb, ite_true, Bool.false_eq_true, ite_false]
                          · by_cases hcond : inReceiveOnlyEpoch st.1.mir Q || 25000 < h.counter.toNat + 1 - 1 ||
                                2 ^ 32 ≤ h.counter.toNat + 1
                            · simp only [hcond, ite_true]; exact hpq
                            · simp only [hcond, Bool.false_eq_true, ite_false]
                              cases hT : decT h.senderRatchetKey with
                              | none => exact hpq
                              | some T =>
                                exact onAnswerPure_pqInv Inv qep Q w isDel none h.senderRatchetKey pq' _ _ hpq hpq'
                          · by_cases hcond : inReceiveOnlyEpoch st.1.mir Q || 25000 < h.counter.toNat + 1 - 1 ||
                                2 ^ 32 ≤ h.counter.toNat + 1
                            · simp only [hcond, ite_true]; exact hpq
                            · simp only [hcond, Bool.false_eq_true, ite_false]
                              cases hT : decT h.senderRatchetKey with
                              | none => exact hpq
                              | some T =>
                                exact onAnswerPure_pqInv Inv qep Q w isDel none h.senderRatchetKey pq' _ _ hpq hpq'

private theorem simCorrPure_pqInv (P : Params PQ PQC) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Q : Party)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ R, Inv (st.1.pq R)) :
    ∀ R, Inv ((simCorrPure P Dh encT Q st).2.1.pq R) := by
  unfold simCorrPure
  dsimp only
  split
  · exact hpq
  · split
    · exact hpq
    · cases (corrPure Q st.2).1 <;> exact hpq

private theorem stepSim_send_pqInv (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ R, Inv (st.1.pq R))
    (z : Option (List (BitVec 8)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hz : z ∈ support (
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
        SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
      (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
        (fun x => pure (x.1.1, (x.1.2, x.2))))) :
    ∀ R, Inv (z.2.1.pq R) := by
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  change z ∈ support ((simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
    (fun x => pure (x.1.1, (x.1.2, x.2)))) at hz
  unfold LibsignalSim.guard LibsignalSim.simSend at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hstop : st.1.stopped
  · simp [hstop] at hz; subst hz; exact hpq
  · simp only [hstop, Bool.false_eq_true, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir] at hz; subst hz; exact hpq
    · simp only [hmir, Bool.false_eq_true, ite_false] at hz
      cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => simp [hep] at hz; subst hz; exact hpq
      | some s₁ =>
        simp only [hep] at hz
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch] at hz; subst hz; exact hpq
        · simp only [hch, Bool.false_eq_true, ite_false] at hz
          cases r with
          | some rq =>
            simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨c_cka, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact hpq
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hpq' : Inv pq' := mkPub_inv P Inv hcl st.1 Q rq _ pq' pub hpq hmk
              have hupd : ∀ R, Inv (Function.update st.1.pq Q pq' R) := pq_update_inv hpq hpq'
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq
                  · exact hupd
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq
                  · exact hupd
          | none =>
            simp only [pure_bind, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨rq, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact hpq
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              have hpq' : Inv pq' := mkPub_inv P Inv hcl st.1 Q rq _ pq' pub hpq hmk
              have hupd : ∀ R, Inv (Function.update st.1.pq Q pq' R) := pq_update_inv hpq hpq'
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq
                  · exact hupd
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact hpq
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb
                  · exact hpq
                  · exact hupd

end WP2A.E4

/-- One simulator step preserves `Inv` on both simulated SPQR states under `SpqrInvClosed`. -/
theorem stepSim_pqInvW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hpq : ∀ Q, Inv (st.1.pq Q)) :
    ∀ z ∈ support (stepSim P ℓ Dh encPt encT decT idOf lam qep k q st), ∀ Q, Inv (z.2.1.pq Q) := by
  intro z hz
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · have hz' : z ∈ support (
        let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
          SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
        (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ none r)).run st.1)).run st.2 >>=
          (fun x => pure (x.1.1, (x.1.2, x.2)))) := by
      cases k <;> simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hz
    exact WP2A.E4.stepSim_send_pqInv P Inv ℓ Dh encPt encT idOf lam qep hcl Q m₀ none r st hpq z hz'
  · have hz' : z ∈ support (
        let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
          SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
        (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ (some m₁) r)).run st.1)).run st.2 >>=
          (fun x => pure (x.1.1, (x.1.2, x.2)))) := by
      cases k <;> simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hz
    exact WP2A.E4.stepSim_send_pqInv P Inv ℓ Dh encPt encT idOf lam qep hcl Q m₀ (some m₁) r st hpq z hz'
  · rw [stepSim_deliver_eq] at hz
    split at hz
    · rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨c_cka, _, hz⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact WP2A.E4.simRecvStep_pqInv P Inv ℓ Dh encPt encT decT idOf lam qep k hcl Q w true c_cka st hpq
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact WP2A.E4.simRecvStep_pqInv P Inv ℓ Dh encPt encT decT idOf lam qep k hcl Q w true 0 st hpq
  · rw [stepSim_inject_eq] at hz
    split at hz
    · rw [MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨c_cka, _, hz⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact WP2A.E4.simRecvStep_pqInv P Inv ℓ Dh encPt encT decT idOf lam qep k hcl Q w false c_cka st hpq
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact WP2A.E4.simRecvStep_pqInv P Inv ℓ Dh encPt encT decT idOf lam qep k hcl Q w false 0 st hpq
  · rw [stepSim_corr_eq] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact WP2A.E4.simCorrPure_pqInv P Inv Dh encT Q st hpq

namespace WP2A.E5

private theorem evalDist_bind_congr_support {α : Type}
    (mx : ProbComp α) (f g : α → ProbComp Bool)
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

end WP2A.E5

theorem evalDist_runSimEagerW {α : Type} (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (F : α → (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv)
    (hpq : ∀ Q, Inv (st.1.pq Q)) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        runSimEager P ℓ Dh encPt encT decT idOf lam qep k oa st ec >>= fun r =>
        F r.1 r.2.1 r.2.2)] =
      𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep k oa st >>= fun r =>
        withEagerCoins r.2.1.mir (F r.1 r.2)] := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [runSimEager_pure, runSim_pure, pure_bind]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimEager_inl_bind, runSim_inl_bind, bind_assoc]
      rw [evalDist_withEagerCoins_bind_swap st.1.mir
        (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _)]
      refine evalDist_bind_congr _ _ _ fun x => ?_
      exact ih x st hpq
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimEager_inr_bind, runSim_inr_bind, bind_assoc]
      rw [evalDist_stepSimEagerW P Inv ℓ Dh encPt encT decT idOf lam qep k q st
        (fun ans st' ec' =>
          runSimEager P ℓ Dh encPt encT decT idOf lam qep k (cont ans) st' ec' >>= fun r =>
          F r.1 r.2.1 r.2.2) hpq hW0]
      refine WP2A.E5.evalDist_bind_congr_support _ _ _ fun r hr => ?_
      exact ih r.1 r.2 (stepSim_pqInvW P Inv ℓ Dh encPt encT decT idOf lam qep k hcl q st hpq r hr)

theorem evalDist_runSim_eq_withEagerCoins_runSimEagerW {α : Type}
    (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : α → (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) → ProbComp Bool)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv)
    (hpq : ∀ Q, Inv (st.1.pq Q)) :
    𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep k oa st >>= fun r => G r.1 r.2] =
      𝒟[withEagerCoins st.1.mir (fun ec =>
        runSimEager P ℓ Dh encPt encT decT idOf lam qep k oa st ec >>= fun r =>
        G r.1 r.2.1)] := by
  rw [evalDist_runSimEagerW P Inv ℓ Dh encPt encT decT idOf lam qep k oa st (fun a s _ => G a s) hcl hW0 hpq]
  refine evalDist_bind_congr _ _ _ fun r => ?_
  exact (evalDist_withEagerCoins_const r.2.1.mir (G r.1 r.2)).symm

namespace WP2A.E6

private theorem initSim_pqInv (P : Params PQ PQC) (Inv : PQ → Prop)
    (hcl : Corr.SpqrInvClosed P.spqr Inv) (pqrKey : BitVec 256) :
    ∀ Q, Inv ((initSim (Pt := Pt) (ℓ := ℓ) (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)).pq Q) := by
  intro Q
  cases Q <;> simp [initSim, hcl.init]

end WP2A.E6

/-- Equates the `simRun` game distribution with its eager-coin counterpart under `SpqrInvClosed` and `SpqrSendTotalOn`. -/
theorem evalDist_game_simRun_none_eq_eagerW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[SM.game sm (2 + 1) (qep + 1) SM.Config.h1 (LibsignalSim.simRun P Dh encT decT qep none A)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runSimEager P ℓ Dh encPt encT decT idOf lam qep none A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0) >>= fun z =>
            pure (b == z.1 || z.2.1.2.win)] := by
  intro sm
  rw [game_simRun_none_eq_runSim]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep none A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b) >>= fun z =>
          pure (b == z.1 || z.2.2.win)] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runSimEager P ℓ Dh encPt encT decT idOf lam qep none A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0) >>= fun z =>
            pure (b == z.1 || z.2.1.2.win)] := by
    intro pqrKey
    rw [evalDist_runSim_eq_withEagerCoins_runSimEagerW P Inv ℓ Dh encPt encT decT idOf lam qep none A
      (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm (k_root, x₀) b)
      (fun a s => pure (b == a || s.2.win)) hcl hW0 (WP2A.E6.initSim_pqInv P Inv hcl pqrKey)]
    rw [evalDist_withEagerCoins_initSim Pt]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

theorem evalDist_simNoneWinEvent_eq_eagerW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[simNoneWinEvent P ℓ Dh encPt encT decT idOf lam qep A] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
        ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
          runWinAt P ℓ Dh encPt encT decT idOf lam qep A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) 0] := by
  intro sm
  rw [simNoneWinEvent_eq_runSim]
  refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
  rw [sample_prod_bind]
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun k_root => ?_
  refine evalDist_bind_congr ($ᵗ BitVec 256) _ _ fun x₀ => ?_
  have h1 : ∀ pqrKey,
      𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep none A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b) >>= fun z =>
          pure z.2.2.win] =
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runWinAt P ℓ Dh encPt encT decT idOf lam qep A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) 0] := by
    intro pqrKey
    rw [evalDist_runSim_eq_withEagerCoins_runSimEagerW P Inv ℓ Dh encPt encT decT idOf lam qep none A
      (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm (k_root, x₀) b)
      (fun _ s => pure s.2.win) hcl hW0 (WP2A.E6.initSim_pqInv P Inv hcl pqrKey)]
    rw [evalDist_withEagerCoins_initSim Pt]
    rfl
  rw [evalDist_bind_congr ($ᵗ BitVec 256) _ _ h1]
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256) _

theorem evalDist_runWinAt_succ_init_leW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ)
    (A : LibAdv PQ PQC ℓ)
    (hcl : Corr.SpqrInvClosed P.spqr Inv)
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun k_root =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun x₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
      ($ᵗ BitVec 256 : ProbComp _) >>= fun pqrKey =>
        runWinAt P ℓ Dh encPt encT decT idOf lam qep A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b)
          (fun Q => match Q with | .A => eA₀ | .B => 0)
          (fun _ => false) (j + 1)] {true} ≤
      spurUnitPt P.C.F encPt Dh := by
  intro sm
  refine evalDist_bind_true_le_of_support _ _ _ fun b _ => ?_
  refine evalDist_bind_true_le_of_support _ _ _ fun k_root _ => ?_
  refine evalDist_bind_true_le_of_support _ _ _ fun x₀ _ => ?_
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ BitVec 256) ($ᵗ BitVec 256)]
  refine evalDist_bind_true_le_of_support _ _ _ fun pqrKey _ => ?_
  have h1 :
      𝒟[($ᵗ BitVec 256 : ProbComp _) >>= fun eA₀ =>
          runWinAt P ℓ Dh encPt encT decT idOf lam qep A
            (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
             SM.initState sm (k_root, x₀) b)
            (fun Q => match Q with | .A => eA₀ | .B => 0)
            (fun _ => false) (j + 1)] =
      𝒟[runSim P ℓ Dh encPt encT decT idOf lam qep (some j) A
          (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey),
           SM.initState sm (k_root, x₀) b) >>=
          fun r => pure (r.2.1.stopped && r.2.2.win)] := by
    rw [evalDist_runSim_eq_withEagerCoins_runSimEagerW P Inv ℓ Dh encPt encT decT idOf lam qep (some j) A
      (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), SM.initState sm (k_root, x₀) b)
      (fun _ s => pure (s.1.stopped && s.2.win)) hcl hW0 (WP2A.E6.initSim_pqInv P Inv hcl pqrKey)]
    rw [evalDist_withEagerCoins_initSim Pt]
    rfl
  rw [h1]
  exact runSim_some_stopped_and_win_prob_le P ℓ Dh encPt encT decT idOf lam qep j A _ rfl

end CryptoGames.LibsignalSM.Proofs.Refinement
