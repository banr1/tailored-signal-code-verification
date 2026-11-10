/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs

/-!
# Pure receive step on `libsignalToModularSchemeSim`

Shows that `stepSimCNone` on a `deliver` or `inject` query at `k = none` reduces to the pure state transition `simRecvStepC`, and relates `simRecvStepC` to `simRecvStepCGen … false` and `simRecvStep` when no evicted salt mismatch occurs.
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

section Hooks
variable (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
  (qepF : ℕ)

theorem zoomB_probe_run {α : Type} (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((runOnBaseState (probeHook fig qepF) x).run sC).run gh =
      (simulateQ (fig8ImplH1 fig qepF) (x.run sC.base)).run gh.1 >>= fun r =>
        pure ((r.1.1, { sC with base := r.1.2 }), (r.2, gh.2)) := by
  change StateT.run (((probeHook fig qepF).lift (x.run sC.base) : ProbeM Pt ℓ _) >>= fun r =>
    (pure (r.1, { sC with base := r.2 }) : ProbeM Pt ℓ _)) gh = _
  rw [StateT.run_bind]
  simp only [probeHook, StateT.run_pure]
  simp only [StateT.run, bind_assoc, pure_bind]

theorem liftC_probe_run {α : Type} (x : Fig8Comp Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((LibsignalSimC.liftC (probeHook fig qepF) x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α).run sC).run gh =
      (simulateQ (fig8ImplH1 fig qepF) x).run gh.1 >>= fun r =>
        pure ((r.1, sC), (r.2, gh.2)) := by
  simp only [LibsignalSimC.liftC, StateT.run_lift]
  rw [StateT.run_bind]
  simp only [probeHook, StateT.run_pure]
  simp only [StateT.run, bind_assoc, pure_bind]

private theorem probeHook_probe_runC (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh
      = pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

theorem fig8ImplH1_fwd_run (Q : Party) (c : Fig8C Pt) (s : SimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fig8ImplH1 fig qepF) ((LibsignalSim.fwd Q c).run s)).run g =
      pure (((fwdPure fig 3 qepF SM.Config.h1 s Q c g).1, s), (fwdPure fig 3 qepF SM.Config.h1 s Q c g).2) := by
  have h := simulateQ_fwd_run (Pt := Pt) (PQ := PQ) fig 3 qepF SM.Config.h1 Q c pure s g
  simp only [bind_pure, StateT.run_pure, simulateQ_pure] at h
  exact h

theorem fig8ImplH1_pure_run {α : Type} (a : α) (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fig8ImplH1 fig qepF) (pure a : Fig8Comp Pt ℓ α)).run g = pure (a, g) := by
  simp [simulateQ_pure, StateT.run_pure]

theorem fig8ImplH1_deliver_run (Q : Party) (c : Fig8C Pt)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fig8ImplH1 fig qepF) (SM.deliverQuery (St := Fig8St Pt) Q c)).run g =
      pure ((deliverPure fig SM.Config.h1 Q c g).1, (deliverPure fig SM.Config.h1 Q c g).2) := by
  have h := simulateQ_deliverQuery_run fig 3 qepF SM.Config.h1 Q c pure g
  simp only [bind_pure, StateT.run_pure, simulateQ_pure] at h
  exact h

end Hooks

/-- Absence of an evicted salt mismatch when `Q` receives wire `w`: any honest record of `w` from an evicted epoch carries effective salt `effectiveHkdfSalt32 salt`. -/
def NoEvictMismatch (P : Params PQ PQC) (Q : Party) (w : List (BitVec 8)) (s : SimState PQ Pt ℓ) :
    Prop :=
  ∀ (h : SignalHeader) (body : List (BitVec 8)) (pq' : PQ) (salt : Salt) (c : Fig8C Pt),
    (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) →
    P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt) →
    (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none →
    (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c →
    c.1.1 ≠ s.mir.epoch Q + 1 → c.2.2.2 = effectiveHkdfSalt32 salt


section Fwd
variable (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
  (qep : ℕ)

theorem fwdAnswerC_probe_run (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (x : JointC PQ Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ((fwdAnswerC (qep := qep) (fig := fig) (fs := lFS P.C P.codec ℓ encT idOf 25000)
        (H := probeHook fig (qep + 1)) Q w isDel ci? T pq' c').run x.1).run x.2 =
      let r := fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' x
      pure ((r.1, r.2.1), r.2.2) := by
  intro fig
  unfold fwdAnswerC
  rw [StateT.run_bind, StateT.run_bind, zoomB_probe_run, fig8ImplH1_fwd_run]
  simp only [bind_assoc, pure_bind]
  unfold fwdCPure
  simp only
  generalize hz : fwdPure fig 3 (qep + 1) SM.Config.h1 x.1.base Q c' x.2.1 = z
  rcases z with ⟨res, g'⟩
  rcases res with _ | ⟨t, i, pm⟩ | _
  all_goals
    simp only [StateT.run_bind, StateT.run_modify, zoomB_probe_run, onAnswer_run_eq,
      fig8ImplH1_pure_run, pure_bind, bind_assoc]
  all_goals rfl

theorem fwdC_probe_run (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) (x : JointC PQ Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ((fwdC (P := P) (qep := qep) (fig := fig) (fs := lFS P.C P.codec ℓ encT idOf 25000)
        (H := probeHook fig (qep + 1)) Q w isDel ci? T pq' honestC c').run x.1).run x.2 =
      let r := fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w isDel ci? T pq' honestC c' x
      pure ((r.1, r.2.1), r.2.2) := by
  intro fig
  have hplain := fwdAnswerC_probe_run P ℓ Dh encPt encT idOf lam qep Q w isDel ci? T pq' c' x
  unfold fwdC
  rw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  cases honestC with
  | none => exact hplain
  | some c =>
    dsimp only
    by_cases hcond : (decide (c ≠ c') && isDel && !(x.1.base.mir.safeInj 3)) = true
    · simp only [hcond, ↓reduceIte]
      unfold fwdCPure
      simp only [Bool.true_and, hcond, ↓reduceIte]
      cases hev : predictReceiveWithSnapshots (fig := fig)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c c' with
      | none =>
        simp only [StateT.run_bind, StateT.run_lift, probeHook_probe_runC, StateT.run_pure, pure_bind]
        rfl
      | some r =>
        unfold resyncC
        rcases r with _ | ⟨t, i, pm⟩
        · simp only [StateT.run_pure]
        · dsimp only
          rw [StateT.run_bind, StateT.run_bind, liftC_probe_run, fig8ImplH1_deliver_run]
          simp only [bind_assoc, pure_bind]
          generalize hd : deliverPure fig SM.Config.h1 Q c x.2.1 = d
          rcases d with ⟨res, g'⟩
          rcases res with _ | ⟨t', i', pm'⟩ | _
          all_goals
            simp only [StateT.run_bind, StateT.run_modify, zoomB_probe_run, onAccept_run_eq,
              fig8ImplH1_pure_run, StateT.run_pure, pure_bind, bind_assoc]
          all_goals rfl
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      refine hplain.trans ?_
      unfold fwdCPure
      simp only [Bool.true_and, hcond, Bool.false_eq_true, ↓reduceIte]

theorem fwdEvictC_probe_run (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (x : JointC PQ Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ((fwdEvictC (qep := qep) (fig := fig) (fs := lFS P.C P.codec ℓ encT idOf 25000)
        (H := probeHook fig (qep + 1)) Q w isDel T pq' c').run x.1).run x.2 =
      let r := fwdEvictCPure P ℓ Dh encPt encT idOf lam qep true Q w isDel T pq' c' x
      pure ((r.1, r.2.1), r.2.2) := by
  intro fig
  have hplain := fwdAnswerC_probe_run P ℓ Dh encPt encT idOf lam qep Q w isDel none T pq' c' x
  unfold fwdEvictC
  rw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind]
  by_cases hcond : (isDel && !(x.1.base.mir.safeInj 3)) = true
  · simp only [hcond, ↓reduceIte]
    unfold fwdEvictCPure
    simp only [Bool.true_and, hcond, ↓reduceIte]
    simp only [StateT.run_bind, StateT.run_lift, probeHook_probe_runC, StateT.run_pure, pure_bind]
    rfl
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    refine hplain.trans ?_
    unfold fwdEvictCPure
    simp only [Bool.true_and, hcond, Bool.false_eq_true, ↓reduceIte]

/-- `guardC (simRecvC …)` under the probe hook runs as `simRecvStepC`. -/
theorem simRecvC_probe_run (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ((guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) (H := probeHook fig (qep + 1))
        Q w isDel)).run x.1).run x.2 =
      let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel x
      pure ((r.1, r.2.1), r.2.2) := by
  intro fig
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
  unfold guardC simRecvC simRecvStepC simRecvStepCGen
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hst : s.stopped = true
  · simp only [hst, ↓reduceIte, StateT.run_pure]
  · simp only [hst, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hwin : s.mir.win = true
    · simp only [hwin, ↓reduceIte, StateT.run_pure]
    simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    by_cases hdel : (isDel && (s.mir.inTransit Q.other w).isNone) = true
    · simp only [hdel, ↓reduceIte, StateT.run_pure]
    simp only [hdel, Bool.false_eq_true, ↓reduceIte]
    by_cases hinj : (!isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
        || !(ratchetKeyAdmissible P.codec decT encT w))) = true
    · simp only [hinj, ↓reduceIte, StateT.run_pure]
    simp only [hinj, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : w.length < 9
    · simp only [hlen, ↓reduceIte, StateT.run_pure]
    simp only [hlen, ↓reduceIte]
    cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
    | none => simp only [StateT.run_pure]
    | some hp =>
      rcases hp with ⟨h, _⟩
      dsimp only
      by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
      · simp only [haddr, ↓reduceIte, StateT.run_pure]
      simp only [haddr, Bool.false_eq_true, ↓reduceIte]
      by_cases hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = true
      · simp only [hpan, ↓reduceIte, StateT.run_pure]
      simp only [hpan, Bool.false_eq_true, ↓reduceIte]
      cases hspqr : P.spqr.recv (s.pq Q) h.pqRatchet with
      | error _ => simp only [StateT.run_pure]
      | ok ps =>
        rcases ps with ⟨pq', salt⟩
        dsimp only
        cases hci : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
        | some ci =>
          dsimp only
          by_cases hrej : ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
          · simp only [hrej, ↓reduceIte, StateT.run_pure]
          simp only [hrej, Bool.false_eq_true, ↓reduceIte]
          exact fwdC_probe_run P ℓ Dh encPt encT idOf lam qep Q w isDel (some ci) _ pq' _ _
            ({ base := s, kept := kept, sent := sent, snaps := snaps }, g, fl)
        | none =>
          dsimp only
          cases hev : (Option.map (fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1))
              (Option.map (fun x => x.2)
                (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) s.honest)) ==
              some true) <;>
          cases hsm : (Option.map (fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt))
              (Option.map (fun x => x.2)
                (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) s.honest)) ==
              some true) <;>
          simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte, StateT.run_pure] <;>
          · by_cases hz : (decT h.senderRatchetKey == some 0) = true
            · simp only [hz, ↓reduceIte, StateT.run_pure]
            simp only [hz, Bool.false_eq_true, ↓reduceIte]
            by_cases hamb : (inReceiveOnlyEpoch s.mir Q || Q == Party.A && (s.chains Q).any fun x => x.key.isNone) = true
            · simp only [hamb, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind]
              have hst' : s.stopped = false := by simpa using hst
              simp only [hst']
              by_cases hcond : (inReceiveOnlyEpoch s.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
                  decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
              · simp only [hcond, ↓reduceIte, StateT.run_pure]
              simp only [hcond, Bool.false_eq_true, ↓reduceIte]
              cases hT : decT h.senderRatchetKey with
              | none => simp only [StateT.run_pure]
              | some T =>
                dsimp only
                first
                | exact fwdC_probe_run P ℓ Dh encPt encT idOf lam qep Q w isDel none _ pq' _ _ (_, g, fl)
                | exact fwdEvictC_probe_run P ℓ Dh encPt encT idOf lam qep Q w isDel _ pq' _ (_, g, fl)
            · simp only [hamb, Bool.false_eq_true, ↓reduceIte]
              by_cases hcond : (inReceiveOnlyEpoch s.mir Q || decide (25000 < h.counter.toNat + 1 - 1) ||
                  decide (2 ^ 32 ≤ h.counter.toNat + 1)) = true
              · simp only [hcond, ↓reduceIte, StateT.run_pure]
              simp only [hcond, Bool.false_eq_true, ↓reduceIte]
              cases hT : decT h.senderRatchetKey with
              | none => simp only [StateT.run_pure]
              | some T =>
                dsimp only
                first
                | exact fwdC_probe_run P ℓ Dh encPt encT idOf lam qep Q w isDel none _ pq' _ _ (_, g, fl)
                | exact fwdEvictC_probe_run P ℓ Dh encPt encT idOf lam qep Q w isDel _ pq' _ (_, g, fl)

private theorem stepSimCNone_recv_eq' (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x =
      pure (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true x) ∧
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x =
      pure (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false x) := by
  constructor
  · have h := simRecvC_probe_run P ℓ Dh encPt encT decT idOf lam qep Q w true x
    unfold stepSimCNone
    have h' : ((simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh
        (.inr (.inl (.inl (.inr (Q, w)))))).run x.1).run x.2 = _ := h
    simp only []
    rw [h', pure_bind]
    rfl
  · have h := simRecvC_probe_run P ℓ Dh encPt encT decT idOf lam qep Q w false x
    unfold stepSimCNone
    have h' : ((simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh
        (.inr (.inl (.inr (Q, w))))).run x.1).run x.2 = _ := h
    simp only []
    rw [h', pure_bind]
    rfl

theorem fwdCPure_c3a_irrel (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) (y : JointC PQ Pt ℓ)
    (h : isDel = false ∨ y.1.base.mir.safeInj 3 = true) :
    fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w isDel ci? T pq' honestC c' y =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' y := by
  unfold fwdCPure
  cases honestC with
  | none => rfl
  | some c =>
    dsimp only
    rcases h with h | h <;> simp [h]

theorem fwdEvictCPure_c3a_irrel (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (y : JointC PQ Pt ℓ)
    (h : isDel = false ∨ y.1.base.mir.safeInj 3 = true) :
    fwdEvictCPure P ℓ Dh encPt encT idOf lam qep true Q w isDel T pq' c' y =
      fwdEvictCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel T pq' c' y := by
  unfold fwdEvictCPure
  rcases h with h | h <;> simp [h]

private theorem simRecvStepC_eq_gen_false' (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (x : JointC PQ Pt ℓ) (h : isDel = false ∨ x.1.base.mir.safeInj 3 = true) :
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel x =
      simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w isDel x := by
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
  have hirr := fwdCPure_c3a_irrel P ℓ Dh encPt encT idOf lam qep Q w isDel
  have hirrE := fwdEvictCPure_c3a_irrel P ℓ Dh encPt encT idOf lam qep Q w isDel
  unfold simRecvStepC simRecvStepCGen
  by_cases hst : s.stopped = true
  · simp only [hst, ↓reduceIte]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : s.mir.win = true
  · simp only [hwin, ↓reduceIte]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases hdel : (isDel && (s.mir.inTransit Q.other w).isNone) = true
  · simp only [hdel, ↓reduceIte]
  simp only [hdel, Bool.false_eq_true, ↓reduceIte]
  by_cases hinj : (!isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp only [hinj, ↓reduceIte]
  simp only [hinj, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp only [hlen, ↓reduceIte]
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => rfl
  | some hp =>
    rcases hp with ⟨hd, _⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses hd.addresses (P.expectedAddrs Q))) = true
    · simp only [haddr, ↓reduceIte]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (s.pq Q) hd.pqRatchet = true
    · simp only [hpan, ↓reduceIte]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases hspqr : P.spqr.recv (s.pq Q) hd.pqRatchet with
    | error _ => rfl
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases hci : (s.chains Q).findIdx? (fun g => g.key == some hd.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · rfl
        · exact hirr _ _ _ _ _ _ h
      | none =>
        dsimp only
        split
        · rfl
        split
        · rfl
        split
        · rfl
        cases decT hd.senderRatchetKey with
        | none => rfl
        | some T =>
          dsimp only
          split
          · exact hirrE _ _ _ _ (by split <;> exact h)
          · exact hirr _ _ _ _ _ _ (by split <;> exact h)

theorem fwdCPure_false_spec (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) (y : JointC PQ Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let r := fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' y
    let z := fwdPure fig 3 (qep + 1) SM.Config.h1 y.1.base Q c' y.2.1
    let a := onAnswerPure qep Q w isDel ci? T pq' z.1 y.1.base
    (r.1, r.2.sim) = (a.1, (a.2, z.2)) ∧ r.2.1.sent = y.1.sent ∧ r.2.2.2 = y.2.2 ∧
    (∀ R, R ≠ Q → r.2.1.kept R = y.1.kept R) ∧
    (r.2.1.kept Q = y.1.kept Q ∨
      ∃ c'', r.2.1.kept Q =
        Kept.recv (fig := fig) (fs := lFS P.C P.codec ℓ encT idOf 25000) c'' (y.1.kept Q)) := by
  intro fig
  have hplain : fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' y =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' none c' y := by
    unfold fwdCPure
    cases honestC <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [hplain]
  unfold fwdCPure
  dsimp only
  generalize fwdPure fig 3 (qep + 1) SM.Config.h1 y.1.base Q c' y.2.1 = z
  rcases z with ⟨res, g'⟩
  cases res with
  | none => exact ⟨rfl, rfl, rfl, fun _ _ => rfl, Or.inl rfl⟩
  | some rr =>
    cases rr with
    | accepted t i pm =>
      refine ⟨rfl, rfl, rfl, fun R hR => ?_, Or.inr ⟨c', ?_⟩⟩
      · simp only [Function.update_of_ne hR]
      · simp only [Function.update_self]; rfl
    | rejected => exact ⟨rfl, rfl, rfl, fun _ _ => rfl, Or.inl rfl⟩

/-- Relational specification comparing `simRecvStepCGen … false` against `simRecvStep … none`. -/
def RecvSpecC (Q : Party) (r : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ)
    (rs : Option (RecvResult (Plain ℓ)) ×
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)))
    (x : JointC PQ Pt ℓ) : Prop :=
  (r.1, r.2.sim) = rs ∧ r.2.1.sent = x.1.sent ∧ r.2.2.2 = x.2.2 ∧
    (∀ R, R ≠ Q → r.2.1.kept R = x.1.kept R) ∧
    (r.2.1.kept Q = x.1.kept Q ∨
      ∃ c', r.2.1.kept Q =
        Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (x.1.kept Q))

private theorem simRecvStepCGen_false_spec' (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (x : JointC PQ Pt ℓ) (hnev : NoEvictMismatch P Q w x.1.base)
    (hnp : recvPanicsW P Q w x.1.base = false) :
    let r := simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w isDel x
    (r.1, r.2.sim) = simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel 0 x.sim ∧
    r.2.1.sent = x.1.sent ∧ r.2.2.2 = x.2.2 ∧ (∀ R, R ≠ Q → r.2.1.kept R = x.1.kept R) ∧
    (r.2.1.kept Q = x.1.kept Q ∨
      ∃ c', r.2.1.kept Q =
        Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (x.1.kept Q)) := by
  intro r
  show RecvSpecC P ℓ Dh encPt encT idOf lam Q r
    (simRecvStep P ℓ Dh encPt encT decT idOf lam qep none Q w isDel 0 x.sim) x
  subst r
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
  have hleaf := fwdCPure_false_spec P ℓ Dh encPt encT idOf lam qep Q w isDel
  have hnone_beq : ((none : Option ℕ) == some s.amb) = false := rfl
  have htriv : ∀ (a : Option (RecvResult (Plain ℓ))) (y : JointC PQ Pt ℓ), y.1.kept = kept →
      y.1.sent = sent → y.2.2 = fl →
      RecvSpecC P ℓ Dh encPt encT idOf lam Q (a, y) (a, y.sim)
        (({ base := s, kept := kept, sent := sent, snaps := snaps }, g, fl) : JointC PQ Pt ℓ) := by
    intro a y h1 h2 h3
    exact ⟨rfl, h2, h3, fun R _ => congrFun h1 R, Or.inl (congrFun h1 Q)⟩
  unfold simRecvStepCGen simRecvStep
  dsimp only [JointC.sim]
  by_cases hst : s.stopped = true
  · simp only [hst, ↓reduceIte]
    exact htriv _ _ rfl rfl rfl
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : s.mir.win = true
  · simp only [hwin, ↓reduceIte]
    exact htriv _ _ rfl rfl rfl
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases hdel : (isDel && (s.mir.inTransit Q.other w).isNone) = true
  · simp only [hdel, ↓reduceIte]
    exact htriv _ _ rfl rfl rfl
  simp only [hdel, Bool.false_eq_true, ↓reduceIte]
  by_cases hinj : (!isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp only [hinj, ↓reduceIte]
    exact htriv _ _ rfl rfl rfl
  simp only [hinj, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp only [hlen, ↓reduceIte]
    exact htriv _ _ rfl rfl rfl
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact htriv _ _ rfl rfl rfl
  | some hp =>
    rcases hp with ⟨hd, _⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses hd.addresses (P.expectedAddrs Q))) = true
    · simp only [haddr, ↓reduceIte]
      exact htriv _ _ rfl rfl rfl
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    have haddr' : addressCheckPasses hd.addresses (P.expectedAddrs Q) = true := by simpa using haddr
    have hpan : P.spqr.recvPanics (s.pq Q) hd.pqRatchet = false := by
      simpa [recvPanicsW, hlen, hparse, haddr'] using hnp
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases hspqr : P.spqr.recv (s.pq Q) hd.pqRatchet with
    | error _ => exact htriv _ _ rfl rfl rfl
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases hci : (s.chains Q).findIdx? (fun g => g.key == some hd.senderRatchetKey) with
      | some ci =>
        dsimp only
        by_cases hrej : ((s.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (hd.counter.toNat + 1) = true
        · simp only [hrej, ↓reduceIte]
          exact htriv _ _ rfl rfl rfl
        simp only [hrej, Bool.false_eq_true, ↓reduceIte]
        exact hleaf _ _ _ _ _
          (({ base := s, kept := kept, sent := sent, snaps := snaps }, g, fl) : JointC PQ Pt ℓ)
      | none =>
        dsimp only
        cases hev : (Option.map (fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1))
            (Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) s.honest)) ==
            some true)
        case true =>
          have hsm : (Option.map (fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt))
              (Option.map (fun x => x.2)
                (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) s.honest)) ==
              some true) = true := by
            cases hfc : Option.map (fun x => x.2)
                (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) s.honest) with
            | none => rw [hfc] at hev; simp at hev
            | some c =>
              rw [hfc] at hev
              have hne : c.1.1 ≠ s.mir.epoch Q + 1 := by simpa using hev
              simp [hnev hd _ pq' salt c hparse hspqr hci hfc hne]
          simp only [hsm, Bool.true_and, ↓reduceIte]
          exact htriv _ _ rfl rfl rfl
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        by_cases hz : (decT hd.senderRatchetKey == some 0) = true
        · simp only [hz, ↓reduceIte]
          exact htriv _ _ rfl rfl rfl
        simp only [hz, Bool.false_eq_true, ↓reduceIte]
        by_cases hamb : (inReceiveOnlyEpoch s.mir Q || Q == Party.A && (s.chains Q).any fun x => x.key.isNone) = true
        · simp only [hamb, hnone_beq, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hcond : (inReceiveOnlyEpoch s.mir Q || decide (25000 < hd.counter.toNat + 1 - 1) ||
              decide (2 ^ 32 ≤ hd.counter.toNat + 1)) = true
          · simp only [hcond, ↓reduceIte]
            exact htriv _ _ rfl rfl rfl
          simp only [hcond, Bool.false_eq_true, ↓reduceIte]
          cases hT : decT hd.senderRatchetKey with
          | none => exact htriv _ _ rfl rfl rfl
          | some T =>
            dsimp only
            exact hleaf _ _ _ _ _ (_, g, fl)
        · simp only [hamb, hnone_beq, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hcond : (inReceiveOnlyEpoch s.mir Q || decide (25000 < hd.counter.toNat + 1 - 1) ||
              decide (2 ^ 32 ≤ hd.counter.toNat + 1)) = true
          · simp only [hcond, ↓reduceIte]
            exact htriv _ _ rfl rfl rfl
          simp only [hcond, Bool.false_eq_true, ↓reduceIte]
          cases hT : decT hd.senderRatchetKey with
          | none => exact htriv _ _ rfl rfl rfl
          | some T =>
            dsimp only
            exact hleaf _ _ _ _ _ (_, g, fl)

end Fwd

/-- On a `deliver` query at `k = none`, `stepSimCNone` equals `pure (simRecvStepC … true x)`. -/
theorem stepSimCNone_deliver_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inr (Q, w)))) x =
      pure (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true x) :=
  (stepSimCNone_recv_eq' P ℓ Dh encPt encT decT idOf lam qep Q w x).1

/-- On an `inject` query at `k = none`, `stepSimCNone` equals `pure (simRecvStepC … false x)`. -/
theorem stepSimCNone_inject_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x =
      pure (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false x) :=
  (stepSimCNone_recv_eq' P ℓ Dh encPt encT decT idOf lam qep Q w x).2

/-- On any `inject` query or any `deliver` query with `safeInj 3 = true`, `simRecvStepC` equals `simRecvStepCGen … false`. -/
theorem simRecvStepC_eq_gen_false (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (x : JointC PQ Pt ℓ) (h : isDel = false ∨ x.1.base.mir.safeInj 3 = true) :
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel x =
      simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w isDel x :=
  simRecvStepC_eq_gen_false' P ℓ Dh encPt encT decT idOf lam qep Q w isDel x h

end CryptoGames.LibsignalSM.Proofs.Refinement
