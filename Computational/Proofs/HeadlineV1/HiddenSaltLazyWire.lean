/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltV1
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import ProofLib.SepLogic.WP.StateNorm

/-!
# Lazy-Coin Probe Predicate and Simulator Wrappers

Defines the reachable wrong-salt probe predicate `firstNEProbeAt` and simulator `firstNESimImpl`
under `EvictedSpurHistSimInvLazy`, and proves probe-flag monotonicity and evict-only send-step
bounds.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoGames CryptoGames.LibsignalSM
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

section KemFailSimCouplingShiftedLazy

open CryptoVerification.LibsignalProtoCodec
open CryptoGames.SM.Construction.DeliverForge

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Reachable non-evicted wrong-salt `deliver` probe predicate under `EvictedSpurHistSimInvLazy`. -/
def firstNEProbeAt {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop :=
  (∃ r w_rem,
    EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g) ∧
  (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 = true

open Classical in
/-- Simulator agreeing with `kemFailSimImpl` except that `deliver` sets the probe flag only when
`firstNEProbeAt` holds at the pre-state. -/
noncomputable def firstNESimImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8)))
      (KemFailSimM (List (BitVec 8)) Pt P.C.F ℓ)
  | .inr (.inl (.inl (.inr (Q, w)))) => do
    let ⟨sC, ⟨g, fl⟩, tr⟩ ← get
    let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
    let j? := sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let tr' := match r.1, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    let fl' := fl || decide (firstNEProbeAt P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w sC g)
    set (r.2.1, (r.2.2.1, fl'), tr')
    return r.1
  | q_sm => kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm

omit [SampleableType Pt] in
theorem fwdCPure_flag_or
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    let r := fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c'
      (sC, (g, false))
    fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' (sC, (g, fl)) =
      (r.1, (r.2.1, r.2.2.1, fl || r.2.2.2)) := by
  dsimp only
  unfold fwdCPure
  dsimp only
  cases honestC with
  | none => simp
  | some c =>
    dsimp only
    split
    · cases predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P sC Q w c c' with
      | none => simp
      | some r_ev =>
        rcases r_ev with _ | ⟨t, i, pm⟩
        · simp
        · dsimp only
          split <;> simp
    · simp

omit [SampleableType Pt] in
theorem fwdEvictCPure_flag_or
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    let r := fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' (sC, (g, false))
    fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' (sC, (g, fl)) =
      (r.1, (r.2.1, r.2.2.1, fl || r.2.2.2)) := by
  dsimp only
  unfold fwdEvictCPure
  dsimp only
  split
  · simp
  · exact fwdCPure_flag_or P ℓ Dh encPt encT idOf lam qep false Q w isDel none T pq' none c'
      sC g fl

omit [SampleableType Pt] in
theorem simRecvStepC_flag_or
    {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool) :
    let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel (sC, (g, false))
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel (sC, (g, fl)) =
      (r.1, (r.2.1, r.2.2.1, fl || r.2.2.2)) := by
  dsimp only
  unfold simRecvStepC simRecvStepCGen
  dsimp only
  by_cases hst : sC.base.stopped = true
  · simp only [hst, ↓reduceIte, Bool.or_false]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : sC.base.mir.win = true
  · simp only [hwin, ↓reduceIte, Bool.or_false]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases hdel : (isDel && (sC.base.mir.inTransit Q.other w).isNone) = true
  · simp only [hdel, ↓reduceIte, Bool.or_false]
  simp only [hdel, Bool.false_eq_true, ↓reduceIte]
  by_cases hinj : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome ||
      !(sC.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp only [hinj, ↓reduceIte, Bool.or_false]
  simp only [hinj, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp only [hlen, ↓reduceIte, Bool.or_false]
  simp only [hlen, ↓reduceIte]
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => simp only [Bool.or_false]
  | some hp =>
    rcases hp with ⟨h, _⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp only [haddr, ↓reduceIte, Bool.or_false]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · simp only [hpan, ↓reduceIte, Bool.or_false]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => simp only [Bool.or_false]
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        by_cases hrej :
            ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
        · simp only [hrej, ↓reduceIte, Bool.or_false]
        simp only [hrej, Bool.false_eq_true, ↓reduceIte]
        exact fwdCPure_flag_or P ℓ Dh encPt encT idOf lam qep true Q w isDel (some ci)
          h.senderRatchetKey pq' _ _ sC g fl
      | none =>
        dsimp only
        by_cases hev_eq :
            (((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
                (·.2)).map (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true &&
              ((sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
                (·.2)).map (fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) = true
        · simp only [hev_eq, ↓reduceIte, Bool.or_false]
        simp only [hev_eq, Bool.false_eq_true, ↓reduceIte]
        by_cases hT0 : (decT h.senderRatchetKey == some 0) = true
        · simp only [hT0, ↓reduceIte, Bool.or_false]
        simp only [hT0, Bool.false_eq_true, ↓reduceIte]
        by_cases hamb :
            (inReceiveOnlyEpoch sC.base.mir Q || Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) = true
        · simp only [hamb, ↓reduceIte]
          by_cases hskip :
              (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
                decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
          · simp only [hskip, ↓reduceIte, Bool.or_false]
          simp only [hskip, Bool.false_eq_true, ↓reduceIte]
          cases decT h.senderRatchetKey with
          | none => simp only [Bool.or_false]
          | some T =>
            dsimp only
            by_cases hev :
                (((sC.base.honest.find? fun wc =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                  (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
            · simp only [hev, ↓reduceIte]
              exact fwdEvictCPure_flag_or P ℓ Dh encPt encT idOf lam qep true Q w isDel
                h.senderRatchetKey pq' _ _ g fl
            · simp only [hev, Bool.false_eq_true, ↓reduceIte]
              exact fwdCPure_flag_or P ℓ Dh encPt encT idOf lam qep true Q w isDel none
                h.senderRatchetKey pq' _ _ _ g fl
        · simp only [hamb, Bool.false_eq_true, ↓reduceIte]
          by_cases hskip :
              (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
                decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
          · simp only [hskip, ↓reduceIte, Bool.or_false]
          simp only [hskip, Bool.false_eq_true, ↓reduceIte]
          cases decT h.senderRatchetKey with
          | none => simp only [Bool.or_false]
          | some T =>
            dsimp only
            by_cases hev :
                (((sC.base.honest.find? fun wc =>
                    wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                  (fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
            · simp only [hev, ↓reduceIte]
              exact fwdEvictCPure_flag_or P ℓ Dh encPt encT idOf lam qep true Q w isDel
                h.senderRatchetKey pq' _ sC g fl
            · simp only [hev, Bool.false_eq_true, ↓reduceIte]
              exact fwdCPure_flag_or P ℓ Dh encPt encT idOf lam qep true Q w isDel none
                h.senderRatchetKey pq' _ _ sC g fl

omit [Zero Pt] [SampleableType Pt] in
theorem probeHook_lift_flag_true_of_true {α : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (m : Fig8Comp Pt ℓ α)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (p : α × (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool))
    (hp : p ∈ support (((probeHook fig qepF).lift m).run (g, true))) :
    p.2.2 = true := by
  rw [probeHook_lift_run, MonadAttach.mem_support_bind] at hp
  rcases hp with ⟨z, _, hp⟩
  simp only [support_pure, Set.mem_singleton_iff] at hp
  subst hp; rfl

theorem kemFailSimImpl_flag_true_of_true
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState PQ Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
      (sC, (g, true), tr))) :
    z.2.2.1.2 = true := by
  have hsend : ∀ Q m₀ (chal : Option (Plain ℓ)) r_coin
      (w_out : (Option (List (BitVec 8)) × LibsignalToModularSchemeSimState PQ Pt ℓ) ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool)),
      w_out ∈ support (((LibsignalSimC.guardC (LibsignalSimC.simSendC P qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1))
        Q m₀ chal r_coin)).run sC).run (g, true)) →
      w_out.2.2 = true := by
    intro Q m₀ chal r_coin w_out hw_out
    unfold LibsignalSimC.guardC LibsignalSimC.simSendC at hw_out
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw_out
    split at hw_out
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_out
      subst hw_out; rfl
    · simp only [StateT.run_bind, zoomB_probeHook_run, MonadAttach.mem_support_bind,
        support_pure, Set.mem_singleton_iff] at hw_out
      rcases hw_out with ⟨_, ⟨⟨⟨w_opt, s_out⟩, g_out⟩, _, rfl⟩, hw_out⟩
      cases w_opt
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_out
        subst hw_out; rfl
      · simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hw_out
        subst hw_out; rfl
  rcases q_sm with n | ((((⟨Q, m₀, r_coin⟩ | ⟨Q, m₀, m₁, r_coin⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · have h := kemFailSimImpl_inl_state_eq P K ℓ Dh encPt encT decT idOf lam qep n
      sC (g, true) tr z hz
    exact congrArg (·.2.1.2) h
  · exact hsend Q m₀ none r_coin ((z.1, z.2.1), z.2.2.1)
      (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inl (Q, m₀, r_coin)))))) sC (g, true) tr z hz)
  · exact hsend Q m₀ (some m₁) r_coin ((z.1, z.2.1), z.2.2.1)
      (mem_support_simImplC_of_mem_support_kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r_coin)))))) sC (g, true) tr z hz)
  · rw [kemFailSimImpl_deliver_run, simRecvStepC_flag_or, Bool.true_or,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  · change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
      (LibsignalSimC.guardC (LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Q w false))).run
      (sC, (g, true), tr)) at hz
    rw [runProbeStep_run, simRecvC_probe_run P ℓ Dh encPt encT decT idOf lam qep Q w false
      (sC, (g, true)), simRecvStepC_flag_or, Bool.true_or, pure_bind,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  · change z ∈ support ((runProbeStep P ℓ Dh encPt encT decT idOf lam qep
      (LibsignalSimC.guardC (LibsignalSimC.simCorrC P encT
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh Q))).run
      (sC, (g, true), tr)) at hz
    rw [runProbeStep_run, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨w_out, hw_out, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    unfold LibsignalSimC.guardC LibsignalSimC.simCorrC at hw_out
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw_out
    split at hw_out
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_out
      subst hw_out; rfl
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hw_out
      split at hw_out
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_out
        subst hw_out; rfl
      · simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hw_out
        rcases hw_out with ⟨res, hres, hw_out⟩
        change res ∈ support ((((probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (qep + 1)).lift (SM.corrQuery Q)).run (g, true)) >>=
          fun p => pure ((p.1, sC), p.2)) at hres
        rw [MonadAttach.mem_support_bind] at hres
        rcases hres with ⟨⟨res₀, gh₁⟩, hgh₁, hres⟩
        simp only [support_pure, Set.mem_singleton_iff] at hres
        subst hres
        have hfl₁ : gh₁.2 = true := probeHook_lift_flag_true_of_true _ _ _ g (res₀, gh₁) hgh₁
        cases res₀ with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw_out
          subst hw_out; exact hfl₁
        | some st =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hw_out
          subst hw_out; exact hfl₁

/-- Single send-step (`transmit` or `chall`) union-bound step for the evict-only simulator under
`EvictedSpurHistSimInvLazy`. -/
theorem kemFailSendStep_evictOnly_bound
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r' w_rem : ℕ) (hS : Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (hq32 : q < 2 ^ 32)
    (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r_coin : Option (BitVec 512))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q (r' + 1) w_rem sC g)
    (k_cont : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F) → ProbComp Bool)
    (hk_some : ∀ u₁ sC₁ gh₁ tr₁
      (p_cand : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32),
      tr₁.cand = some p_cand → 𝒟[k_cont (u₁, sC₁, gh₁, tr₁)] {true} = 0)
    (hk_same : ∀ u₁ sC₁ g₁ tr₁,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w_rem sC₁ g₁ →
      𝒟[k_cont (u₁, sC₁, (g₁, false), tr₁)] {true} ≤
        spurSlack P encPt Dh q w_rem + ((w_rem : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ))
    (hk_decr : ∀ w' u₁ sC₁ g₁ tr₁,
      w_rem = w' + 1 →
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r' w' sC₁ g₁ →
      𝒟[k_cont (u₁, sC₁, (g₁, false), tr₁)] {true} ≤
        spurSlack P encPt Dh q w' + ((w' : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ)) :
    𝒟[(kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r_coin).run
        (sC, (g, false), tr) >>= k_cont] {true} ≤
      spurSlack P encPt Dh q w_rem + ((w_rem : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) := by
  by_cases hinw : inReceiveOnlyEpoch sC.base.mir Q = true
  · rcases kemFailSendStep_new_epoch_preserves_evictedSpurHistSimInvLazy_of_good_coin
        P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT idOf hX hD hrt hid lam qep q r'
        (r' + 1) w_rem hS hq32 (Nat.lt_succ_self r') Q m₀ chal r_coin sC g tr hInv hinw with
      hnoop | ⟨hw_pos, s₁, rk_base, T_base, L, epExp, hg_win_f, hg1, hep, hg3, hL_len, hmax_le,
        hgood_coin⟩
    · refine evalDist_bind_true_le_of_support _ _ _ fun ⟨u₁, sC₁, gh₁, tr₁⟩ h₁ => ?_
      rcases hnoop (u₁, sC₁, gh₁, tr₁) h₁ with ⟨_, _, hgh₁, hInv₁⟩
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
          have hb := Proofs.Refinement.badCoin_prob_le P encPt Dh δ hδ Q rk_base T_base L
            (sendCoinCollPts Dh epExp M)
          rw [sendCoinCollPts_length] at hb
          exact hb.trans (add_le_add le_rfl (by gcongr))
        refine (evalDist_bind_true_le_add_of_badCoin
          (d₂ := spurSlack P encPt Dh q w' + ((w' : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ))
          ($ᵗ BitVec 256)
          (fun c_cka => spurBadList P encPt Dh Q rk_base T_base L c_cka ||
            sendCoinCollBad Dh epExp M c_cka)
          hbad_prob _ fun c_cka hgood => ?_).trans ?_
        · dsimp only
          cases hcand₁ : (stepKemFailSend P.C.F K tr Q rq).cand with
          | some p_cand =>
            rw [hk_some _ _ _ _ p_cand hcand₁]
            exact zero_le
          | none =>
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
      cases r_coin with
      | some rq =>
        rw [kemFailSendStep_some_run_eq_bind_simSendStep P K InvPQ ℓ Dh encPt encT decT idOf lam
          qep q (r' + 1) hS (Nat.succ_pos r') Q m₀ chal rq s₁ s_R sC g tr hg1 hep hg3 hg_win_f
          hmeta hpq, bind_assoc]
        simpa only [pure_bind, Option.isSome_some] using hinner rq
      | none =>
        rw [kemFailSendStep_none_run_eq_bind_simSendStep P K InvPQ ℓ Dh encPt encT decT idOf lam
          qep q (r' + 1) hS (Nat.succ_pos r') Q m₀ chal s₁ s_R sC g tr hg1 hep hg3 hg_win_f
          hmeta hpq, bind_assoc]
        generalize ($ᵗ BitVec 512 : ProbComp (BitVec 512)) = m512
        refine evalDist_bind_true_le_of_support m512 _ _ fun rq _ => ?_
        rw [bind_assoc]
        simpa only [pure_bind, Option.isSome_none] using hinner rq
  · have hinw_f : inReceiveOnlyEpoch sC.base.mir Q = false := Bool.eq_false_iff.mpr hinw
    refine evalDist_bind_true_le_of_support _ _ _ fun ⟨u₁, sC₁, gh₁, tr₁⟩ h₁ => ?_
    cases hcand₁ : tr₁.cand with
    | some p_cand =>
      rw [hk_some u₁ sC₁ gh₁ tr₁ p_cand hcand₁]
      exact zero_le
    | none =>
      have hInv₁ := kemFailSendStep_same_epoch_preserves_evictedSpurHistSimInvLazy P K hspqr_eq
        InvPQ hInv_top ℓ Dh hDh encPt encT decT idOf hX hD hrt hid lam qep q r' (r' + 1) w_rem
        hS hq32 (Nat.lt_succ_self r') Q m₀ chal r_coin sC g tr hInv hinw_f (u₁, sC₁, gh₁, tr₁) h₁
      have hfl₁ : gh₁.2 = false := by
        cases chal with
        | none =>
          exact kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
            (.inl (Q, m₀, r_coin)) sC g tr (u₁, sC₁, gh₁, tr₁) h₁
        | some m₁ =>
          exact kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
            (.inr (Q, m₀, m₁, r_coin)) sC g tr (u₁, sC₁, gh₁, tr₁) h₁
      have hgh₁ : gh₁ = (gh₁.1, false) := Prod.ext rfl hfl₁
      rw [hgh₁]
      exact hk_same u₁ sC₁ gh₁.1 tr₁ hInv₁

end KemFailSimCouplingShiftedLazy

end CryptoVerification.LibsignalSession.HeadlineV1

namespace CryptoVerification.E2E.Signed

open MeasureTheory
open CryptoGames CryptoGames.SM CryptoGames.SM.Construction CryptoGames.Ratchet
  CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSM.Proofs CryptoVerification.E2E
  CryptoGames.LibsignalSession CryptoGames.CKA LibsignalProtoCodec CryptoGames.LibsignalSM
  CryptoGames.LibsignalSM.Proofs.Refinement CryptoGames.Ratchet.LibsignalSim
  CryptoGames.Ratchet.LibsignalSimC CryptoGames.SM.Construction.DeliverForge
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1Sync.SendTotal
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalSession.HeadlineV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

end CryptoVerification.E2E.Signed

end
