/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv

/-!
# Coupling salt mismatches to steering injections

**Checked by Lean.** Proves that any salt mismatch on an honest wire delivered while `safeInj 3 = false` requires either an earlier accepted steering injection while `safeInj 3 = true` or a failure of `SpqrNoWrongSaltOnUnsafedTrace`. Consequently, along an unsafed SPQR trace satisfying `SpqrNoWrongSaltOnUnsafedTrace`, `simRecvStepC` coincides with `simRecvStepCGen … false` and leaves the probe flag unchanged.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## Unsafed SPQR traces -/

/-- Single-step SPQR state transition at `Q` via `Q`'s own sends or deliveries of honest wires in `honest` from `Q.other`. -/
def UnsafedSpqrStep (P : Params PQ PQC)
    (honest : List (List (BitVec 8) × Fig8C Pt)) (Q : Party) (pq pq' : PQ) : Prop :=
  pq' = pq ∨
  (∃ rq pqrKey pqrMsg, P.spqr.send pq rq = some (pq', pqrKey, pqrMsg)) ∨
  (∃ w c h body salt,
    (w, c) ∈ honest ∧
    Party.senderOf c.1.1 = Q.other ∧
    ¬ w.length < 9 ∧
    (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) ∧
    P.spqr.recv pq h.pqRatchet = .ok (pq', salt))

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem UnsafedSpqrStep.mono {P : Params PQ PQC}
    {honest₁ honest₂ : List (List (BitVec 8) × Fig8C Pt)} {Q : Party} {pq pq' : PQ}
    (hsub : ∀ wc ∈ honest₁, wc ∈ honest₂)
    (h : UnsafedSpqrStep P honest₁ Q pq pq') :
    UnsafedSpqrStep P honest₂ Q pq pq' := by
  rcases h with rfl | hsend | ⟨w, c, hd, body, salt, hmem, hsender, hlen, hparse, hrcv⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hsend)
  · exact Or.inr (Or.inr ⟨w, c, hd, body, salt, hsub (w, c) hmem, hsender, hlen, hparse, hrcv⟩)

/-- Reflexive-transitive closure of `UnsafedSpqrStep` from `pq₀` at party `Q`. -/
inductive UnsafedSpqrTrace (P : Params PQ PQC)
    (honest : List (List (BitVec 8) × Fig8C Pt)) (Q : Party) (pq₀ : PQ) : PQ → Prop where
  | refl : UnsafedSpqrTrace P honest Q pq₀ pq₀
  | step {pq₁ pq₂ : PQ} :
      UnsafedSpqrTrace P honest Q pq₀ pq₁ →
      UnsafedSpqrStep P honest Q pq₁ pq₂ →
      UnsafedSpqrTrace P honest Q pq₀ pq₂

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem UnsafedSpqrTrace.single {P : Params PQ PQC}
    {honest : List (List (BitVec 8) × Fig8C Pt)} {Q : Party} {pq₀ pq₁ : PQ}
    (h : UnsafedSpqrStep P honest Q pq₀ pq₁) :
    UnsafedSpqrTrace P honest Q pq₀ pq₁ :=
  UnsafedSpqrTrace.step .refl h

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem UnsafedSpqrTrace.trans {P : Params PQ PQC}
    {honest : List (List (BitVec 8) × Fig8C Pt)} {Q : Party} {pq₀ pq₁ pq₂ : PQ}
    (h₀₁ : UnsafedSpqrTrace P honest Q pq₀ pq₁)
    (h₁₂ : UnsafedSpqrTrace P honest Q pq₁ pq₂) :
    UnsafedSpqrTrace P honest Q pq₀ pq₂ := by
  induction h₁₂ with
  | refl => exact h₀₁
  | step _ hstep ih => exact UnsafedSpqrTrace.step ih hstep

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem UnsafedSpqrTrace.mono {P : Params PQ PQC}
    {honest₁ honest₂ : List (List (BitVec 8) × Fig8C Pt)} {Q : Party} {pq₀ pq : PQ}
    (hsub : ∀ wc ∈ honest₁, wc ∈ honest₂)
    (htr : UnsafedSpqrTrace P honest₁ Q pq₀ pq) :
    UnsafedSpqrTrace P honest₂ Q pq₀ pq := by
  induction htr with
  | refl => exact .refl
  | step _ hstep ih => exact .step ih (hstep.mono hsub)

/-! ### Trace preservation across simulator steps -/

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] in
theorem onAcceptPure_honest_eq (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep P_party w isDel t i m ci? T pq' s).2.honest = s.honest := by
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit P_party.other w <;> rfl
  · split
    · rfl
    · split <;> rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] in
theorem onAnswerPure_honest_eq (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ) :
    (onAnswerPure qep P_party w isDel ci? T pq' res s).2.honest = s.honest := by
  unfold onAnswerPure
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm =>
      exact onAcceptPure_honest_eq qep P_party w isDel t i
        ((pm.map (·.2)).getD default) ci? T pq' s

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem fwdCPure_honest_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (P_party : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC PQ Pt ℓ) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w isDel ci? T pq'
      honestC c' x).2.1.base.honest = x.1.base.honest := by
  unfold fwdCPure
  dsimp only
  cases honestC with
  | none =>
    exact onAnswerPure_honest_eq qep P_party w isDel ci? T pq' _ x.1.base
  | some c =>
    dsimp only
    split
    · cases predictReceiveWithSnapshots (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) P x.1 P_party w c c' with
      | none => rfl
      | some r =>
        cases r with
        | none => rfl
        | some tipm =>
          rcases tipm with ⟨t, i, pm⟩
          dsimp only
          cases (deliverPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
              SM.Config.h1 P_party c x.2.1).1 with
          | none => rfl
          | some res_d =>
            cases res_d with
            | rejected => rfl
            | accepted t' i' m' =>
              exact onAcceptPure_honest_eq qep P_party w true t i pm.2
                ci? T pq' x.1.base
    · exact onAnswerPure_honest_eq qep P_party w isDel ci? T pq' _ x.1.base

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem fwdEvictCPure_honest_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (P_party : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T_key : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (x : JointC PQ Pt ℓ) :
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w isDel
      T_key pq' c' x).2.1.base.honest = x.1.base.honest := by
  unfold fwdEvictCPure
  dsimp only
  split
  · rfl
  · exact fwdCPure_honest_eq P ℓ Dh encPt encT idOf lam qep false P_party w isDel none
      T_key pq' none c' x

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem simRecvStepCGen_honest_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (P_party : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ) :
    (simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep c3a P_party w isDel x).2.1.base.honest =
      x.1.base.honest := by
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
  unfold simRecvStepCGen
  by_cases hst : s.stopped = true
  · simp only [hst, ↓reduceIte]
  simp only [hst, Bool.false_eq_true, ↓reduceIte]
  by_cases hwin : s.mir.win = true
  · simp only [hwin, ↓reduceIte]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte]
  by_cases hdel : (isDel && (s.mir.inTransit P_party.other w).isNone) = true
  · simp only [hdel, ↓reduceIte]
  simp only [hdel, Bool.false_eq_true, ↓reduceIte]
  by_cases hinj : (!isDel && ((s.mir.inTransit P_party.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp only [hinj, ↓reduceIte]
  simp only [hinj, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : w.length < 9
  · simp only [hlen, ↓reduceIte]
  simp only [hlen, ↓reduceIte]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => rfl
  | some hb =>
    rcases hb with ⟨h, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs P_party))) = true
    · simp only [haddr, ↓reduceIte]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (s.pq P_party) h.pqRatchet = true
    · simp only [hpan, ↓reduceIte]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases P.spqr.recv (s.pq P_party) h.pqRatchet with
    | error _ => rfl
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases (s.chains P_party).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · rfl
        · exact fwdCPure_honest_eq P ℓ Dh encPt encT idOf lam qep c3a P_party w isDel
            (some ci) h.senderRatchetKey pq' _ _ (⟨s, kept, sent, snaps⟩, g, fl)
      | none =>
        dsimp only
        have hx1_honest :
            (if inReceiveOnlyEpoch s.mir P_party ||
                (P_party == Party.A && (s.chains P_party).any (·.key.isNone)) then
              (({ base := { s with amb := s.amb + 1, stopped := false },
                  kept := kept, sent := sent, snaps := snaps }, g, fl) : JointC PQ Pt ℓ)
            else (⟨s, kept, sent, snaps⟩, g, fl)).1.base.honest = s.honest := by
          split <;> rfl
        split
        · rfl
        · split
          · rfl
          · split
            · exact hx1_honest
            · cases decT h.senderRatchetKey with
              | none => exact hx1_honest
              | some T =>
                dsimp only
                split
                · exact (fwdEvictCPure_honest_eq P ℓ Dh encPt encT idOf lam qep c3a
                    P_party w isDel h.senderRatchetKey pq' _ _).trans hx1_honest
                · exact (fwdCPure_honest_eq P ℓ Dh encPt encT idOf lam qep c3a
                    P_party w isDel none h.senderRatchetKey pq' _ _ _).trans hx1_honest

def simCorrPureCSteer (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (Q : Party)
    (x : JointC PQ Pt ℓ) :
    Option (GhostState PQ) × JointC PQ Pt ℓ :=
  let sC := x.1
  let s := sC.base
  let s_fig8 := x.2.1
  let fl := x.2.2
  if s.stopped then (none, x)
  else if s.mir.win || !(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q) then
    (none, x)
  else
    let z := corrPure Q s_fig8
    match z.1 with
    | none => (none, (sC, z.2, fl))
    | some figSt =>
      let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
          match figSt.γ with
          | .exp x_exp => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
              if g.key.isNone then { g with key := some (encT (Dh.dh x_exp Dh.base)) } else g)
          | _ => s.chains
        else s.chains
      let g := LibsignalSim.toGhost (P := P) { s with chains } Q figSt
      (some g,
       ({ sC with base := { s with mir := s.mir.afterCorr Q, chains },
                  kept := Function.update sC.kept Q (Kept.ofSt figSt),
                  snaps := (Q, s.mir.epoch Q, g) :: sC.snaps }, z.2, fl))

omit [Zero Pt] [SampleableType Pt] in
private theorem probeHook_lift_corrQuery_run_steer
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift
      (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)).run gh =
      pure ((corrPure Q gh.1).1, ((corrPure Q gh.1).2, gh.2)) := by
  change ((simulateQ (fig8ImplH1 fig qepF)
    (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)).run gh.1 >>=
    fun p => pure (p.1, (p.2, gh.2))) = _
  have hq := simulateQ_corrQuery_run fig 3 qepF SM.Config.h1 Q pure gh.1
  rw [bind_pure] at hq
  change (simulateQ (fig8ImplH1 fig qepF) (SM.corrQuery Q)).run gh.1 =
    pure ((corrPure Q gh.1).1, (corrPure Q gh.1).2) at hq
  rw [hq, pure_bind]

omit [SampleableType Pt] [Inhabited PQ] in
theorem stepSimCNone_corr_eq_steer (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x =
      pure (simCorrPureCSteer P Dh encT Q x) := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  change (((guardC (simCorrC (P := P) (encT := encT) (H := probeHook fig (qep + 1)) Dh Q)).run
    x.1).run x.2) >>= (fun r => pure (r.1.1, (r.1.2, r.2))) =
    pure (simCorrPureCSteer P Dh encT Q x)
  unfold guardC simCorrC simCorrPureCSteer
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : x.1.base.stopped
  · simp [hstop]
  · simp only [hstop, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : x.1.base.mir.win || !(x.1.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch x.1.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 x.1.base.mir Q)
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ite_false, LibsignalSimC.liftC,
        StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      rw [probeHook_lift_corrQuery_run_steer]
      simp only [pure_bind]
      cases h : (corrPure Q x.2.1).1 with
      | none => simp
      | some figSt =>
        cases hγ : figSt.γ <;>
          simp [hγ, StateT.run_set, StateT.run_pure]

omit [SampleableType Pt] [Inhabited PQ] in
/-- A `corr` step under `stepSimCNone` preserves `base.honest`, `base.pq`, `base.mir.epoch`, `inReceiveOnlyEpoch base.mir`, and `s_fig8.st`. -/
theorem stepSimCNone_corr_invariants (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (P_party : Party)
    (x : JointC PQ Pt ℓ) :
    ∀ w ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr P_party) x),
      w.2.1.base.honest = x.1.base.honest ∧
      w.2.1.base.pq = x.1.base.pq ∧
      w.2.1.base.mir.epoch = x.1.base.mir.epoch ∧
      (∀ Q, inReceiveOnlyEpoch w.2.1.base.mir Q = inReceiveOnlyEpoch x.1.base.mir Q) ∧
      w.2.2.1.st = x.2.1.st := by
  intro w hw
  have hst : (corrPure P_party x.2.1).2.st = x.2.1.st := by
    unfold corrPure
    split <;> rfl
  rw [stepSimCNone_corr_eq_steer] at hw
  simp only [support_pure, Set.mem_singleton_iff] at hw
  subst hw
  unfold simCorrPureCSteer
  dsimp only
  split
  · exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl⟩
    · cases (corrPure P_party x.2.1).1 <;>
        exact ⟨rfl, rfl, rfl, fun _ => rfl, hst⟩

omit [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem cxSend_base_eq_steer (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (P_party : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s' : SimState PQ Pt ℓ)
    (res : Option (List (BitVec 8))) :
    (cxSend P Dh encPt encT idOf lam P_party sC s' res).base = s' := by
  cases res <;> rfl

/-! ## No-wrong-salt predicates -/

/-- State-local no-wrong-salt property at `Q` in SPQR state `pq`: receiving any honest wire in `honest` from `Q.other` either fails or returns its own effective salt. -/
def SpqrNoWrongSaltAt (P : Params PQ PQC)
    (honest : List (List (BitVec 8) × Fig8C Pt)) (Q : Party) (pq : PQ) : Prop :=
  ∀ w c h body pq' salt,
    (w, c) ∈ honest →
    Party.senderOf c.1.1 = Q.other →
    (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) →
    P.spqr.recv pq h.pqRatchet = .ok (pq', salt) →
    c.2.2.2 = effectiveHkdfSalt32 salt

/-- Trace-local no-wrong-salt property asserting `SpqrNoWrongSaltAt` at every SPQR state reachable along `UnsafedSpqrTrace` from `pq₀`. -/
def SpqrNoWrongSaltOnUnsafedTrace (P : Params PQ PQC)
    (honest : List (List (BitVec 8) × Fig8C Pt)) (Q : Party) (pq₀ : PQ) : Prop :=
  ∀ pq₁, UnsafedSpqrTrace P honest Q pq₀ pq₁ → SpqrNoWrongSaltAt P honest Q pq₁

/-! ## Steering injections -/

/-- Predicate holding when `simRecvStepC` accepts an `inject` query `(Q, w)` on joint state `x`. -/
def AcceptedInjSteersSpqr (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) : Prop :=
  ∃ t i pm,
    (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false x).1 = some (.accepted t i pm)

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] in
theorem onAcceptPure_inject_not_accepted_pq_eq (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ)
    (hnot : ∀ t' i' pm',
      (onAcceptPure qep P_party w false t i m ci? T pq' s).1 ≠ some (.accepted t' i' pm')) :
    (onAcceptPure qep P_party w false t i m ci? T pq' s).2.pq = s.pq := by
  unfold onAcceptPure at hnot ⊢
  dsimp only at hnot ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at hnot ⊢
  split
  · rfl
  · rename_i hle
    simp only [hle, ↓reduceIte] at hnot
    split
    · rename_i htriv
      simp only [htriv, ↓reduceIte] at hnot
      exact False.elim (hnot t i (some m) rfl)
    · rfl

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] in
theorem onAnswerPure_inject_not_accepted_pq_eq (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) (s : SimState PQ Pt ℓ)
    (hnot : ∀ t' i' pm',
      (onAnswerPure qep P_party w false ci? T pq' res s).1 ≠ some (.accepted t' i' pm')) :
    (onAnswerPure qep P_party w false ci? T pq' res s).2.pq = s.pq := by
  unfold onAnswerPure at hnot ⊢
  cases res with
  | none => rfl
  | some r =>
    cases r with
    | rejected => rfl
    | accepted t i pm =>
      exact onAcceptPure_inject_not_accepted_pq_eq qep P_party w t i
        ((pm.map (·.2)).getD default) ci? T pq' s hnot

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem fwdCPure_inject_not_accepted_pq_eq (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (c3a : Bool) (P_party : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC PQ Pt ℓ)
    (hnot : ∀ t' i' pm',
      (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq' honestC c' x).1 ≠
        some (.accepted t' i' pm')) :
    (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq'
      honestC c' x).2.1.base.pq = x.1.base.pq := by
  have hc3a : fwdCPure P ℓ Dh encPt encT idOf lam qep c3a P_party w false ci? T pq' honestC c' x =
      fwdCPure P ℓ Dh encPt encT idOf lam qep false P_party w false ci? T pq' none c' x := by
    unfold fwdCPure
    cases honestC <;> simp [Bool.false_and, Bool.and_false]
  rw [hc3a] at hnot ⊢
  unfold fwdCPure at hnot ⊢
  dsimp only at hnot ⊢
  exact onAnswerPure_inject_not_accepted_pq_eq qep P_party w ci? T pq' _ x.1.base hnot

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
/-- Any `inject` query that does not satisfy `AcceptedInjSteersSpqr` leaves `base.pq` unchanged at every party. -/
theorem simRecvStepC_inject_pq_eq_of_not_steers (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ)
    (hnot : ¬ AcceptedInjSteersSpqr P ℓ Dh encPt encT decT idOf lam qep Q w x) :
    (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false x).2.1.base.pq = x.1.base.pq := by
  have hnot_acc : ∀ t' i' pm',
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w false x).1 ≠
        some (.accepted t' i' pm') :=
    fun t' i' pm' heq => hnot ⟨t', i', pm', heq⟩
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
  unfold simRecvStepC simRecvStepCGen at hnot_acc ⊢
  by_cases hst : s.stopped = true
  · simp only [hst, ↓reduceIte]
  simp only [hst, Bool.false_eq_true, ↓reduceIte] at hnot_acc ⊢
  by_cases hwin : s.mir.win = true
  · simp only [hwin, ↓reduceIte]
  simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hnot_acc ⊢
  by_cases hdel : (false && (s.mir.inTransit Q.other w).isNone) = true
  · simp only [hdel, ↓reduceIte]
  simp only [hdel, Bool.false_eq_true, ↓reduceIte] at hnot_acc ⊢
  by_cases hinj : (!false && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp only [hinj, ↓reduceIte]
  simp only [hinj, Bool.false_eq_true, ↓reduceIte] at hnot_acc ⊢
  by_cases hlen : w.length < 9
  · simp only [hlen, ↓reduceIte]
  simp only [hlen, ↓reduceIte] at hnot_acc ⊢
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => rfl
  | some hb =>
    rcases hb with ⟨h, body⟩
    rw [hparse] at hnot_acc
    dsimp only at hnot_acc ⊢
    by_cases haddr : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · simp only [haddr, ↓reduceIte]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte] at hnot_acc ⊢
    by_cases hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = true
    · simp only [hpan, ↓reduceIte]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hnot_acc ⊢
    cases hspqr : P.spqr.recv (s.pq Q) h.pqRatchet with
    | error _ => rfl
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      rw [hspqr] at hnot_acc
      dsimp only at hnot_acc ⊢
      cases hci : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        rw [hci] at hnot_acc
        dsimp only at hnot_acc ⊢
        split
        · rfl
        · rename_i hrej
          simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hnot_acc
          exact fwdCPure_inject_not_accepted_pq_eq P ℓ Dh encPt encT idOf lam qep true
            Q w (some ci) h.senderRatchetKey pq' _ _ (⟨s, kept, sent, snaps⟩, g, fl) hnot_acc
      | none =>
        rw [hci] at hnot_acc
        dsimp only at hnot_acc ⊢
        have hx1_pq :
            (if inReceiveOnlyEpoch s.mir Q ||
                (Q == Party.A && (s.chains Q).any (·.key.isNone)) then
              (({ base := { s with amb := s.amb + 1, stopped := false },
                  kept := kept, sent := sent, snaps := snaps }, g, fl) : JointC PQ Pt ℓ)
            else (⟨s, kept, sent, snaps⟩, g, fl)).1.base.pq = s.pq := by
          split <;> rfl
        split
        · rfl
        · split
          · rfl
          · split
            · exact hx1_pq
            · rename_i hev hz hcond
              simp only [hev, hz, hcond, Bool.false_eq_true, ↓reduceIte] at hnot_acc
              cases hT : decT h.senderRatchetKey with
              | none => exact hx1_pq
              | some T =>
                rw [hT] at hnot_acc
                dsimp only at hnot_acc ⊢
                split
                · rename_i hev_true
                  simp only [hev_true, ↓reduceIte] at hnot_acc
                  unfold fwdEvictCPure at hnot_acc ⊢
                  simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true,
                    ↓reduceIte] at hnot_acc ⊢
                  exact (fwdCPure_inject_not_accepted_pq_eq P ℓ Dh encPt encT idOf lam
                    qep false Q w none h.senderRatchetKey pq' none _ _
                    hnot_acc).trans hx1_pq
                · rename_i hev_false
                  simp only [hev_false, Bool.false_eq_true, ↓reduceIte] at hnot_acc
                  exact (fwdCPure_inject_not_accepted_pq_eq P ℓ Dh encPt encT idOf lam
                    qep true Q w none h.senderRatchetKey pq' _ _ _
                    hnot_acc).trans hx1_pq

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] in
theorem mem_honest_of_find_map_eq_some {s : SimState PQ Pt ℓ} {Q : Party}
    {w : List (BitVec 8)} {c : Fig8C Pt}
    (hfind : (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) =
      some c) :
    (w, c) ∈ s.honest ∧ Party.senderOf c.1.1 = Q.other := by
  rcases Option.map_eq_some_iff.mp hfind with ⟨⟨w', c'⟩, hmem_find, rfl⟩
  have hmem := List.mem_of_find?_eq_some hmem_find
  have hpred := List.find?_some hmem_find
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  rcases hpred with ⟨rfl, hsender⟩
  exact ⟨hmem, hsender⟩

/-! ## Consequences under no-wrong-salt -/

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
/-- Under `SpqrNoWrongSaltAt`, `simRecvStepC` equals `simRecvStepCGen … false` for all `(Q, w, isDel)`. -/
theorem simRecvStepC_eq_gen_false_of_noWrongSaltAt (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ)
    (hno_wrong : SpqrNoWrongSaltAt P x.1.base.honest Q (x.1.base.pq Q)) :
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel x =
      simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w isDel x := by
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
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
  | some hb =>
    rcases hb with ⟨hd, body⟩
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
      have hfwd_eq : ∀ (ci? : Option ℕ) (t : ℕ) (T? : Option Pt) (y : JointC PQ Pt ℓ),
          let honestC := (s.honest.find? fun wc =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
          let mkC : Fig8C Pt :=
            match honestC with
            | some c =>
              if c.2.2.2 = effectiveHkdfSalt32 salt then c
              else ((t, T?), (hd.counter.toNat + 1,
                ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
            | none =>
              ((t, T?), (hd.counter.toNat + 1,
                ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
          fwdCPure P ℓ Dh encPt encT idOf lam qep true Q w isDel ci?
            hd.senderRatchetKey pq' honestC mkC y =
          fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci?
            hd.senderRatchetKey pq' honestC mkC y := by
        intro ci? t T? y
        dsimp only
        cases hfc : (s.honest.find? fun wc =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
        | none =>
          unfold fwdCPure
          rfl
        | some c =>
          rcases mem_honest_of_find_map_eq_some hfc with ⟨hmem, hsender⟩
          have hsalt : c.2.2.2 = effectiveHkdfSalt32 salt :=
            hno_wrong w c hd body pq' salt hmem hsender hparse hspqr
          simp only [hsalt, ↓reduceIte]
          have hne_false : decide (c ≠ c) = false := by simp
          unfold fwdCPure
          simp only [hne_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      cases (s.chains Q).findIdx? (fun g => g.key == some hd.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · rfl
        · exact hfwd_eq (some ci) _ _ (⟨s, kept, sent, snaps⟩, g, fl)
      | none =>
        dsimp only
        cases hev : (Option.map (fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1))
            (Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) s.honest)) ==
            some true)
        case true =>
          have hsm : (Option.map (fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt))
              (Option.map (fun x => x.2)
                (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                  s.honest)) ==
              some true) = true := by
            cases hfc : Option.map (fun x => x.2)
                (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                  s.honest) with
            | none => rw [hfc] at hev; simp at hev
            | some c =>
              rcases mem_honest_of_find_map_eq_some hfc with ⟨hmem, hsender⟩
              have hsalt : c.2.2.2 = effectiveHkdfSalt32 salt :=
                hno_wrong w c hd body pq' salt hmem hsender hparse hspqr
              simp [hsalt]
          simp only [hsm, Bool.true_and, ↓reduceIte]
        case false =>
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          split
          · rfl
          · split
            · rfl
            · cases decT hd.senderRatchetKey with
              | none => rfl
              | some T =>
                exact hfwd_eq none (s.mir.epoch Q + 1) (some T) _

/-- Under `SpqrNoWrongSaltAt`, `simRecvStepC` leaves the probe flag `x.2.2` unchanged. -/
theorem simRecvStepC_flag_eq_of_noWrongSaltAt (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (x : JointC PQ Pt ℓ)
    (hno_wrong : SpqrNoWrongSaltAt P x.1.base.honest Q (x.1.base.pq Q)) :
    (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w isDel x).2.2.2 = x.2.2 := by
  rw [simRecvStepC_eq_gen_false_of_noWrongSaltAt P ℓ Dh encPt encT decT idOf lam qep Q w isDel x
    hno_wrong]
  have hfwd_fl : ∀ ci? T pq' honestC c' (y : JointC PQ Pt ℓ),
      (fwdCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel ci? T pq' honestC c' y).2.2.2 =
        y.2.2 := by
    intro ci? T pq' honestC c' y
    exact (fwdCPure_false_spec P ℓ Dh encPt encT idOf lam qep Q w isDel
      ci? T pq' honestC c' y).2.2.1
  have hev_fl : ∀ T pq' c' (y : JointC PQ Pt ℓ),
      (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep false Q w isDel T pq' c' y).2.2.2 = y.2.2 := by
    intro T pq' c' y
    unfold fwdEvictCPure
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact hfwd_fl none T pq' none c' y
  rcases x with ⟨⟨s, kept, sent, snaps⟩, g, fl⟩
  unfold simRecvStepCGen
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
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => rfl
  | some hb =>
    rcases hb with ⟨hd, body⟩
    dsimp only
    by_cases haddr : (!(addressCheckPasses hd.addresses (P.expectedAddrs Q))) = true
    · simp only [haddr, ↓reduceIte]
    simp only [haddr, Bool.false_eq_true, ↓reduceIte]
    by_cases hpan : P.spqr.recvPanics (s.pq Q) hd.pqRatchet = true
    · simp only [hpan, ↓reduceIte]
    simp only [hpan, Bool.false_eq_true, ↓reduceIte]
    cases P.spqr.recv (s.pq Q) hd.pqRatchet with
    | error _ => rfl
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases (s.chains Q).findIdx? (fun g => g.key == some hd.senderRatchetKey) with
      | some ci =>
        dsimp only
        split
        · rfl
        · exact hfwd_fl (some ci) hd.senderRatchetKey pq' _ _ (⟨s, kept, sent, snaps⟩, g, fl)
      | none =>
        dsimp only
        have hx1_fl :
            (if inReceiveOnlyEpoch s.mir Q ||
                (Q == Party.A && (s.chains Q).any (·.key.isNone)) then
              (({ base := { s with amb := s.amb + 1, stopped := false },
                  kept := kept, sent := sent, snaps := snaps }, g, fl) : JointC PQ Pt ℓ)
            else (⟨s, kept, sent, snaps⟩, g, fl)).2.2 = fl := by
          split <;> rfl
        split
        · rfl
        · split
          · rfl
          · split
            · exact hx1_fl
            · cases decT hd.senderRatchetKey with
              | none => exact hx1_fl
              | some T =>
                dsimp only
                split
                · exact (hev_fl hd.senderRatchetKey pq' _ _).trans hx1_fl
                · exact (hfwd_fl none hd.senderRatchetKey pq' _ _ _).trans hx1_fl

end CryptoGames.LibsignalSM.Proofs.Refinement
