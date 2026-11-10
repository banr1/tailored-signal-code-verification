/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Deliver.Base
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv

/-!
# Evicted salt mismatch: shared combinators

Provides coupling combinators for an honest wire of an evicted epoch whose received SPQR salt
differs from its honest salt (`DEV-LS36`), where the C side may increment `amb` without triggering a
stopping run at `k = some amb`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

private theorem n1_cxSend_base (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ) (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam Q sC s' res).base = s' := by
  cases res <;> rfl

private theorem n1_simSendStep_stopped_and_amb (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : PQC) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka st).2.1.stopped = st.1.stopped ∧
    (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka st).2.1.amb = st.1.amb := by
  unfold simSendStep
  dsimp only
  cases LibsignalSim.mkPub (P := P) st.1 Q rq
      (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
  | none => exact ⟨rfl, rfl⟩
  | some pp =>
    rcases pp with ⟨pq', pub⟩
    dsimp only
    split <;> exact ⟨rfl, rfl⟩

private theorem n1_stepSim_send_stopped_and_amb (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (z : Option (List (BitVec 8)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (hz : z ∈ support (
      let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
        SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
      (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
        (fun x => pure (x.1.1, (x.1.2, x.2))))) :
    z.2.1.stopped = st.1.stopped ∧ z.2.1.amb = st.1.amb := by
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
    SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
  change z ∈ support ((simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
    (fun x => pure (x.1.1, (x.1.2, x.2)))) at hz
  unfold LibsignalSim.guard LibsignalSim.simSend at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hstop : st.1.stopped
  · simp [hstop] at hz; subst hz; exact ⟨rfl, rfl⟩
  · simp only [hstop, Bool.false_eq_true, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir] at hz; subst hz; exact ⟨rfl, rfl⟩
    · simp only [hmir, Bool.false_eq_true, ite_false] at hz
      cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => simp [hep] at hz; subst hz; exact ⟨rfl, rfl⟩
      | some s₁ =>
        simp only [hep] at hz
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch] at hz; subst hz; exact ⟨rfl, rfl⟩
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
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact ⟨rfl, rfl⟩
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact ⟨rfl, rfl⟩
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb <;> simp [hstop]
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact ⟨rfl, rfl⟩
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb <;> simp [hstop]
          | none =>
            simp only [pure_bind, bind_assoc] at hz
            rw [simulateQ_coin_run] at hz
            simp only [bind_assoc] at hz
            rw [MonadAttach.mem_support_bind] at hz
            rcases hz with ⟨rq, _, hzb⟩
            cases hmk : LibsignalSim.mkPub (P := P) st.1 Q rq
                (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q) with
            | none => simp only [hmk] at hzb; simp at hzb; subst hzb; exact ⟨rfl, rfl⟩
            | some pp =>
              rcases pp with ⟨pq', pub⟩
              simp only [hmk] at hzb
              cases chal with
              | none =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_transmitQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact ⟨rfl, rfl⟩
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (transmitPure sm 3 (qep + 1) Q (pub, m₀) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb <;> simp [hstop]
              | some m₁ =>
                simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                  Function.comp_apply, bind_assoc, pure_bind] at hzb
                rw [simulateQ_challQuery_run] at hzb
                by_cases hw : st.2.win
                · simp [hw] at hzb; subst hzb; exact ⟨rfl, rfl⟩
                · simp only [hw, Bool.false_eq_true, ite_false, bind_assoc] at hzb
                  rw [MonadAttach.mem_support_bind] at hzb
                  rcases hzb with ⟨cb, _, hzb⟩
                  cases hz1 : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 st.2).1 <;>
                    simp [hz1, sm, LibsignalSim.putS, StateT.run_bind, StateT.run_set] at hzb <;>
                    subst hzb <;> simp [hstop]

private theorem n1_onAcceptPure_stopped_and_amb (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.stopped = s.stopped ∧
    (onAcceptPure qep Q w isDel t i m ci? T pq' s).2.amb = s.amb := by
  unfold onAcceptPure
  dsimp only
  repeat' (first | exact ⟨rfl, rfl⟩ | split)

private theorem n1_onAnswerPure_stopped_and_amb (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.stopped = s.stopped ∧
    (onAnswerPure qep Q w isDel ci? T pq' res s).2.amb = s.amb := by
  unfold onAnswerPure
  cases res with
  | none => exact ⟨rfl, rfl⟩
  | some r =>
    cases r with
    | rejected => exact ⟨rfl, rfl⟩
    | accepted t i pm => exact n1_onAcceptPure_stopped_and_amb qep Q w isDel t i _ ci? T pq' s

private theorem n1_fwdCPure_stopped_and_amb (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) {honestC : Option (Fig8C Pt)} {c' : Fig8C Pt}
    (x : JointC PQ Pt ℓ) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.1.base.stopped =
      x.1.base.stopped ∧
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.1.base.amb =
      x.1.base.amb := by
  unfold fwdCPure
  dsimp only
  have hplain := n1_onAnswerPure_stopped_and_amb qep Q w isDel ci? T pq'
    (fwdPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) 3 (qep + 1) SM.Config.h1 x.1.base Q c' x.2.1).1
    x.1.base
  cases honestC with
  | none => exact hplain
  | some c =>
    dsimp only
    split
    · cases predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c c' with
      | none => exact ⟨rfl, rfl⟩
      | some o =>
        cases o with
        | none => exact ⟨rfl, rfl⟩
        | some tipm =>
          rcases tipm with ⟨t, i, pm⟩
          dsimp only
          split
          · exact n1_onAcceptPure_stopped_and_amb qep Q w true t i pm.2 ci? T pq' x.1.base
          · exact ⟨rfl, rfl⟩
    · exact hplain

private theorem n1_fwdEvictCPure_stopped_and_amb (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) {c' : Fig8C Pt}
    (x : JointC PQ Pt ℓ) :
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' x).2.1.base.stopped =
      x.1.base.stopped ∧
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' x).2.1.base.amb =
      x.1.base.amb := by
  unfold fwdEvictCPure
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · exact n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep false Q w isDel none T pq' x

private theorem n1_simRecvStepCGen_stopped_and_amb_le (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) :
    (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x).2.1.base.stopped =
      x.1.base.stopped ∧
    x.1.base.amb ≤ (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x).2.1.base.amb := by
  let Goal (r : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ) : Prop :=
    r.2.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ r.2.1.base.amb
  have hite : ∀ {c : Prop} [Decidable c] {a b : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ},
      Goal a → Goal b → Goal (if c then a else b) := by
    intro c _ a b ha hb
    by_cases hc : c <;> simp only [hc, ↓reduceIte]
    · exact ha
    · exact hb
  change Goal (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a Q w isDel x)
  unfold simRecvStepCGen
  dsimp only
  refine hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ ?_))))
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact ⟨rfl, le_rfl⟩
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine hite ⟨rfl, le_rfl⟩ ?_
    refine hite ⟨rfl, le_rfl⟩ ?_
    cases P.spqr.recv (x.1.base.pq Q) h.pqRatchet with
    | error _ => exact ⟨rfl, le_rfl⟩
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases (x.1.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine hite ⟨rfl, le_rfl⟩ ⟨(n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel
          (some ci) h.senderRatchetKey pq' x).1,
          (n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a Q w isDel
          (some ci) h.senderRatchetKey pq' x).2.ge⟩
      | none =>
        dsimp only
        refine hite ⟨rfl, le_rfl⟩ (hite ⟨rfl, le_rfl⟩ ?_)
        set x₁ : JointC PQ Pt ℓ :=
          if (inReceiveOnlyEpoch x.1.base.mir Q || (Q == Party.A && (x.1.base.chains Q).any (·.key.isNone))) then
            ({ x.1 with base := { x.1.base with amb := x.1.base.amb + 1 } }, x.2)
          else x
        have hx₁ : x₁.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ x₁.1.base.amb := by
          dsimp only [x₁]
          split
          · exact ⟨rfl, Nat.le_succ _⟩
          · exact ⟨rfl, le_rfl⟩
        refine hite hx₁ ?_
        cases decT h.senderRatchetKey with
        | none => exact hx₁
        | some T =>
          dsimp only
          refine hite ?_ ?_
          · exact ⟨(n1_fwdEvictCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a
              Q w isDel h.senderRatchetKey pq' x₁).1.trans hx₁.1,
              hx₁.2.trans (n1_fwdEvictCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a
              Q w isDel h.senderRatchetKey pq' x₁).2.ge⟩
          · exact ⟨(n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a
              Q w isDel none h.senderRatchetKey pq' x₁).1.trans hx₁.1,
              hx₁.2.trans (n1_fwdCPure_stopped_and_amb P ℓ Dh encPt encT idOf lam qep c3a
              Q w isDel none h.senderRatchetKey pq' x₁).2.ge⟩

private theorem n1_simRecvUsesCoin_none (P : Params PQ PQC)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvUsesCoin P encT decT none Q w isDel st = false := by
  unfold simRecvUsesCoin
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  dsimp only
  simp only [hnone, Bool.and_false, Bool.false_eq_true, ite_false]
  repeat' (first | rfl | split)

private theorem n1_simRecvStep_none_stopped (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (c_cka : BitVec 256)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel c_cka st).2.1.stopped =
      st.1.stopped := by
  unfold simRecvStep
  have hnone : ((none : Option ℕ) == some st.1.amb) = false := rfl
  dsimp only
  by_cases h1 : st.1.stopped = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : st.1.mir.win = true
    · simp [h2, h1]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (isDel && (st.1.mir.inTransit Q.other w).isNone) = true
      · simp [h3, h1]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : (!isDel && ((st.1.mir.inTransit Q.other w).isSome || !st.1.mir.safeInj 3 || !ratchetKeyAdmissible P.codec decT encT w)) = true
        · simp [h4, h1]
        · simp only [h4, Bool.false_eq_true, ↓reduceIte]
          by_cases h5 : w.length < 9
          · simp [h5, h1]
          · simp only [h5, ↓reduceIte]
            cases (signalWireCodec P.codec).parse (List.take (w.length - 8) w) with
            | none => simp [h1]
            | some hb =>
              rcases hb with ⟨h, _⟩
              dsimp only
              by_cases h6 : (!addressCheckPasses h.addresses (P.expectedAddrs Q)) = true
              · simp [h6, h1]
              · simp only [h6, Bool.false_eq_true, ↓reduceIte]
                cases P.spqr.recv (st.1.pq Q) h.pqRatchet with
                | error _ => simp [h1]
                | ok ps =>
                  rcases ps with ⟨pq', salt⟩
                  dsimp only
                  cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (st.1.chains Q) with
                  | some ci =>
                    dsimp only
                    by_cases h7 : ((st.1.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects (h.counter.toNat + 1) = true
                    · simp only [h7, ↓reduceIte]; simp [h1]
                    · simp only [h7, Bool.false_eq_true, ↓reduceIte, onAnswerPure_stopped]; simp [h1]
                  | none =>
                    dsimp only
                    by_cases h8 : (Option.map (fun c => decide (c.1.1 ≠ st.1.mir.epoch Q + 1)) (Option.map (fun x => x.2) (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) st.1.honest)) == some true) = true
                    · simp only [h8, ↓reduceIte]; simp [h1]
                    · simp only [h8, Bool.false_eq_true, ↓reduceIte]
                      by_cases h9 : (decT h.senderRatchetKey == some 0) = true
                      · simp [h9, h1]
                      · simp only [h9, hnone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                        by_cases h10 : (inReceiveOnlyEpoch st.1.mir Q || decide (25000 < h.counter.toNat + 1 - 1) || decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
                        · simp only [h10, ↓reduceIte]
                          by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]
                        · simp only [h10, Bool.false_eq_true, ↓reduceIte]
                          cases decT h.senderRatchetKey with
                          | none =>
                            dsimp only
                            by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]
                          | some T =>
                            simp only [Bool.false_eq_true, ↓reduceIte, onAnswerPure_stopped]
                            by_cases h11 : (inReceiveOnlyEpoch st.1.mir Q || (Q == Party.A && (st.1.chains Q).any fun x => x.key.isNone)) = true <;> simp [h11, h1]

private theorem n1_simRecvStops_none (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep none Q w isDel st = false := by
  unfold simRecvStops
  rw [n1_simRecvStep_none_stopped]
  cases st.1.stopped <;> simp

private theorem n1_stepSimCNone_corr_stopped_and_amb (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (x : JointC PQ Pt ℓ)
    (z : Option (GhostState PQ) × JointC PQ Pt ℓ)
    (hz : z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x)) :
    z.2.1.base.stopped = x.1.base.stopped ∧ z.2.1.base.amb = x.1.base.amb := by
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨r, hr, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  change r ∈ support (((guardC (simCorrC P encT
    (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q)).run x.1).run x.2) at hr
  unfold guardC simCorrC at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact ⟨rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
      rcases hr with ⟨res, hres, hr⟩
      change res ∈ support ((((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)).lift
        (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q) >>= fun a =>
        pure (a, x.1)) : ProbeM Pt ℓ _).run x.2) at hres
      rw [StateT.run_bind] at hres
      simp only [MonadAttach.mem_support_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
      rcases hres with ⟨⟨res₀, gh₁⟩, _, rfl⟩
      cases res₀ with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, rfl⟩
      | some st =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact ⟨rfl, rfl⟩

private theorem n1_stepSimCEager_none_stopped_and_amb_le (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (z : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q ×
      (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hz : z ∈ support (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q x ec)) :
    z.2.1.1.base.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ z.2.1.1.base.amb := by
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · change z ∈ support (stepSimCEagerTransmit P ℓ Dh encPt encT decT idOf lam qep none Q m₀ r x ec) at hz
    unfold stepSimCEagerTransmit at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    rw [n1_cxSend_base]
    unfold stepSimEagerTransmit at hres
    have hbranch : ∀ (h : res ∈ support (
        stepSim P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inl (.inl (Q, m₀, r))))) x.sim >>= fun res =>
        updateAllEagerCoins x.sim.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
        pure (res.1, (res.2, ec')))),
        res.2.1.1.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ res.2.1.1.amb := by
      intro h
      rw [MonadAttach.mem_support_bind] at h
      rcases h with ⟨res₀, hres₀, h⟩
      rw [MonadAttach.mem_support_bind] at h
      rcases h with ⟨ec', _, h⟩
      simp only [support_pure, Set.mem_singleton_iff] at h
      subst h
      have hsend := n1_stepSim_send_stopped_and_amb P ℓ Dh encPt encT idOf lam qep Q m₀ none r x.sim res₀
        (by simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hres₀)
      exact ⟨hsend.1, hsend.2.ge⟩
    split at hres
    · cases hep : x.sim.1.mir.epMgmt 3 qep Q r.isSome with
      | some s₁ =>
        simp only [hep] at hres
        rw [MonadAttach.mem_support_bind] at hres
        rcases hres with ⟨rq, _, hres⟩
        rw [MonadAttach.mem_support_bind] at hres
        rcases hres with ⟨ec', _, hres⟩
        simp only [support_pure, Set.mem_singleton_iff] at hres
        subst hres
        have hsend := n1_simSendStep_stopped_and_amb P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq (ec Q) x.sim
        exact ⟨hsend.1, hsend.2.ge⟩
      | none =>
        simp only [hep] at hres
        exact hbranch hres
    · exact hbranch hres
  · change z ∈ support (stepSimCEagerChall P ℓ Dh encPt encT decT idOf lam qep none Q m₀ m₁ r x ec) at hz
    unfold stepSimCEagerChall at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨res, hres, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    rw [n1_cxSend_base]
    unfold stepSimEagerChall at hres
    have hbranch : ∀ (h : res ∈ support (
        stepSim P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) x.sim >>= fun res =>
        updateAllEagerCoins x.sim.1.mir res.2.1.mir (fun _ => false) ec >>= fun ec' =>
        pure (res.1, (res.2, ec')))),
        res.2.1.1.stopped = x.1.base.stopped ∧ x.1.base.amb ≤ res.2.1.1.amb := by
      intro h
      rw [MonadAttach.mem_support_bind] at h
      rcases h with ⟨res₀, hres₀, h⟩
      rw [MonadAttach.mem_support_bind] at h
      rcases h with ⟨ec', _, h⟩
      simp only [support_pure, Set.mem_singleton_iff] at h
      subst h
      have hsend := n1_stepSim_send_stopped_and_amb P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r x.sim res₀
        (by simpa [stepSim, stepSimNone, LibsignalSim.simImpl] using hres₀)
      exact ⟨hsend.1, hsend.2.ge⟩
    split at hres
    · cases hep : x.sim.1.mir.epMgmt 3 qep Q r.isSome with
      | some s₁ =>
        simp only [hep] at hres
        split at hres
        · exact hbranch hres
        · rw [MonadAttach.mem_support_bind] at hres
          rcases hres with ⟨rq, _, hres⟩
          rw [MonadAttach.mem_support_bind] at hres
          rcases hres with ⟨ec', _, hres⟩
          simp only [support_pure, Set.mem_singleton_iff] at hres
          subst hres
          have hsend := n1_simSendStep_stopped_and_amb P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq (ec Q) x.sim
          exact ⟨hsend.1, hsend.2.ge⟩
      | none =>
        simp only [hep] at hres
        exact hbranch hres
    · exact hbranch hres
  · rw [stepSimCEager_deliver_of_not_stops P ℓ Dh encPt encT decT idOf lam qep none Q w x ec
      (n1_simRecvUsesCoin_none P encT decT Q w true x.sim)
      (n1_simRecvStops_none P ℓ Dh encPt encT decT idOf lam qep Q w true x.sim)] at hz
    dsimp only at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨ec', _, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact n1_simRecvStepCGen_stopped_and_amb_le P ℓ Dh encPt encT decT idOf lam qep true Q w true x
  · change z ∈ support (stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep none Q w x ec) at hz
    unfold stepSimCEagerInject at hz
    rw [n1_simRecvUsesCoin_none P encT decT Q w false x.sim] at hz
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, evictStopsC_none, stepSimC,
      n1_simRecvStops_none P ℓ Dh encPt encT decT idOf lam qep Q w false x.sim,
      stepSimCNone_inject_eq, pure_bind] at hz
    rw [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨ec', _, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact n1_simRecvStepCGen_stopped_and_amb_le P ℓ Dh encPt encT decT idOf lam qep true Q w false x
  · change z ∈ support (stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep none Q x ec) at hz
    unfold stepSimCEagerCorr at hz
    simp only [stepSimC, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, ec', _, rfl⟩
    have hcorr := n1_stepSimCNone_corr_stopped_and_amb P ℓ Dh encPt encT decT idOf lam qep Q x res hres
    exact ⟨hcorr.1, hcorr.2.ge⟩

theorem evalDist_runSimCEager_stopped_win_of_lt_amb {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hstop : x.1.base.stopped = false) (hlt : j < x.1.base.amb) :
    𝒟[runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some j) oa x ec >>=
        fun r => pure (r.2.1.1.base.stopped && r.2.1.2.1.win)] =
      𝒟[(pure false : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing x ec with
  | pure a =>
    simp [runSimCEager_pure, hstop]
  | query_bind t cont ih =>
    cases t with
    | inl u =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inl_bind, bind_assoc]
      exact evalDist_bind_const_of_support _ _ (pure false) fun y _ => ih y x ec hstop hlt
    | inr q =>
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq,
        runSimCEager_inr_bind, bind_assoc]
      rw [stepSimCEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep j q x ec
        (Nat.ne_of_lt hlt)]
      refine evalDist_bind_const_of_support _ _ (pure false) fun r hr => ?_
      have hstep := n1_stepSimCEager_none_stopped_and_amb_le P ℓ Dh encPt encT decT idOf lam qep q x ec r hr
      exact ih r.1 r.2.1 r.2.2 (hstep.1.trans hstop) (Nat.lt_of_lt_of_le hlt hstep.2)

theorem evalDist_runWinAtC_inr_amb_noStop_bind {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q ×
      (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.base.amb = x.1.base.amb + 1)
    (hstop' : ∀ y, (f y).2.1.1.base.stopped = false)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q x ec =
      N >>= fun y => pure (f y))
    (hsome : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) q x ec =
      N >>= fun y => pure (f y))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtC P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
          (.inr q)) >>= cont)
        x ec winBefore idx] =
      𝒟[N >>= fun y =>
        runWinAtC P ℓ Dh encPt encT decT idOf lam qep (cont (f y).1) (f y).2.1 (f y).2.2
          (fun j => if j = x.1.base.amb then false else winBefore j) idx] := by
  unfold runWinAtC
  cases idx with
  | zero =>
    rw [runSimCEager_inr_bind, hnone]
    simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only
    simp only [hamb]
    by_cases hlt : j < x.1.base.amb
    · have hlt' : j < x.1.base.amb + 1 := by omega
      have hne0 : j ≠ x.1.base.amb := by omega
      simp only [hlt, hlt', ↓reduceIte, hne0]
      exact (OracleComp.evalDist_bind_const _ _).symm
    · by_cases heq0 : j = x.1.base.amb
      · subst heq0
        have hlt' : x.1.base.amb < x.1.base.amb + 1 := by omega
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', runSimCEager_inr_bind,
          hsome, bind_assoc, pure_bind]
        refine evalDist_bind_congr N _ (fun _ => (pure false : ProbComp Bool)) fun y => ?_
        exact evalDist_runSimCEager_stopped_win_of_lt_amb P ℓ Dh encPt encT decT idOf lam qep
          x.1.base.amb (cont (f y).1) (f y).2.1 (f y).2.2 (hstop' y) (by rw [hamb y]; omega)
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEager_inr_bind]
        rw [stepSimCEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep j
              q x ec heq0,
            hnone]
        simp only [bind_assoc, pure_bind]

/-- Closes a deterministic C step that increments `amb` without setting `stopped` at `k = some amb`,
setting `winBefore amb := false`. -/
theorem closeByStateC_inr_amb_noStop {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl fl' : Bool)
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (N : ProbComp γ)
    (fR : γ → SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      N >>= fun y => pure (ans, fR y))
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      pure (ans, ((sC', s_fig8', fl'), ec')))
    (hsome : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm
      (sC, s_fig8, fl) ec = pure (ans, ((sC', s_fig8', fl'), ec')))
    (hamb : sC'.base.amb = sC.base.amb + 1)
    (hstop' : sC'.base.stopped = false)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ y, CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) (fR y) sC'
      s_fig8' fl' ec' (fun j => if j = sC.base.amb then false else winBefore j)) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun y => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) (hcont y)))
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind]
  · rw [runSimCEager_inr_bind, hnone, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm
  · intro idx _
    have h := evalDist_runWinAtC_inr_amb_noStop_bind P ℓ Dh encPt encT decT idOf lam qep q_sm
      cont (sC, s_fig8, fl) ec (pure ()) (fun _ => (ans, ((sC', s_fig8', fl'), ec')))
      (fun _ => hamb) (fun _ => hstop') (by rw [hnone]; simp) (by rw [hsome]; simp) winBefore idx
    rw [h, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind]
  · unfold runHidC
    rw [runSimCEager_inr_bind, hnone, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm

end CryptoGames.LibsignalSM.Proofs.Refinement
