/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.Amb

/-!
# Evicted salt mismatch inside the window: shared combinators

Shared stopping-run and `CloseByStateC` combinators for an evicted salt mismatch inside the receive-only window (`evictCaseC`), used by both `DeliverWin` and `InjectWin`.
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

/-- On an evicted stop of a `deliver`, the stopping run's `stopped && win` equals the spurious-accept bit `spurPtStep`. -/
theorem evalDist_stepSimCEager_deliver_evictStop {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hev : evictStopsC P encT decT k Q w true x = true) :
    𝒟[stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec >>= fun r =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win)] =
      𝒟[(pure (spurPtStep P Dh encPt decT Q w false (ec Q) x.sim) : ProbComp Bool)] := by
  have huse := simRecvUsesCoin_eq_false_of_evictStopsC P encT decT k Q w true x hev
  have hstep : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inr (Q, w)))) x ec =
      (updateAllEagerCoins x.1.base.mir (evictStopStepC P Dh encPt decT Q w (ec Q) x).2.1.base.mir
        (· == Q) ec >>= fun ec' =>
        pure ((evictStopStepC P Dh encPt decT Q w (ec Q) x).1,
          ((evictStopStepC P Dh encPt decT Q w (ec Q) x).2, ec'))) := by
    change stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _
    unfold stepSimCEagerDeliver
    simp only [huse, hev, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hstep]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ _ ?_
  intro ec' hec'
  have hvalid := validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir _ _ ec ec' hec'
  exact evalDist_runSimCEager_stopped_and_win P ℓ Dh encPt encT decT idOf lam qep k
    (cont (evictStopStepC P Dh encPt decT Q w (ec Q) x).1) (evictStopStepC P Dh encPt decT Q w (ec Q) x).2
    ec' rfl hvalid

theorem evalDist_stepSimCEager_inject_evictStop {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (cont : Option (SM.RecvResult (Plain ℓ)) →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hev : evictStopsC P encT decT k Q w false x = true) :
    𝒟[stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec >>= fun r =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win)] =
      𝒟[(pure (spurPtStep P Dh encPt decT Q w false (ec Q) x.sim) : ProbComp Bool)] := by
  have huse := simRecvUsesCoin_eq_false_of_evictStopsC P encT decT k Q w false x hev
  have hstep : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec =
      (updateAllEagerCoins x.1.base.mir (evictStopStepC P Dh encPt decT Q w (ec Q) x).2.1.base.mir
        (· == Q) ec >>= fun ec' =>
        pure ((evictStopStepC P Dh encPt decT Q w (ec Q) x).1,
          ((evictStopStepC P Dh encPt decT Q w (ec Q) x).2, ec'))) := by
    change stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _
    unfold stepSimCEagerInject
    simp only [huse, hev, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hstep]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_const_of_support _ _ _ ?_
  intro ec' hec'
  have hvalid := validEagerCoins_of_mem_support_updateAllEagerCoins x.1.base.mir _ _ ec ec' hec'
  exact evalDist_runSimCEager_stopped_and_win P ℓ Dh encPt encT decT idOf lam qep k
    (cont (evictStopStepC P Dh encPt decT Q w (ec Q) x).1) (evictStopStepC P Dh encPt decT Q w (ec Q) x).2
    ec' rfl hvalid

/-- Decomposes `runWinAtC` across an `amb`-incrementing step whose `k = some amb` stopping run evaluates to `pure w0`. -/
theorem evalDist_runWinAtC_inr_amb_stopEq_bind {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      (JointC PQ Pt ℓ × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.base.amb = x.1.base.amb + 1)
    (hnone : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm x ec =
      N >>= fun y => pure (f y))
    (w0 : Bool)
    (hw0 : 𝒟[stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) q_sm x ec >>= fun r =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some x.1.base.amb) (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win)] = 𝒟[(pure w0 : ProbComp Bool)])
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtC P ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
          (.inr q_sm)) >>= cont)
        x ec winBefore idx] =
      𝒟[N >>= fun y =>
        runWinAtC P ℓ Dh encPt encT decT idOf lam qep (cont (f y).1) (f y).2.1 (f y).2.2
          (fun j => if j = x.1.base.amb then w0 else winBefore j) idx] := by
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
        simp only [hlt, Bool.false_eq_true, ↓reduceIte, hlt', runSimCEager_inr_bind, bind_assoc]
        exact hw0.trans (OracleComp.evalDist_bind_const N (pure w0)).symm
      · have hnot' : ¬ j < x.1.base.amb + 1 := by omega
        simp only [hlt, hnot', Bool.false_eq_true, ↓reduceIte, runSimCEager_inr_bind]
        rw [stepSimCEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep j
              q_sm x ec heq0,
            hnone]
        simp only [bind_assoc, pure_bind]

/-- Closes an `amb` step when the `k = some amb` stopping run wins with probability `1`. -/
theorem closeByStateC_inr_amb_stopEq_win {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hamb_lt : sC.base.amb < q)
    (hw0 : 𝒟[stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm
        (sC, s_fig8, fl) ec >>= fun r =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win)] = 𝒟[(pure true : ProbComp Bool)]) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_of_win_eq_one (k₀ := sC.base.amb + 1)
    (Finset.mem_range.mpr (by omega)) ?_
  unfold runWinAtC
  have hnlt : ¬ sC.base.amb < sC.base.amb := Nat.lt_irrefl _
  simp only [hnlt, ↓reduceIte, runSimCEager_inr_bind, bind_assoc]
  rw [hw0]
  simp

/-- Closes a deterministic `amb` step when the `k = some amb` stopping run evaluates to `pure false`. -/
theorem closeByStateC_inr_amb_stopEq_false {α γ : Type} (P : Params PQ PQC) (ℓ : ℕ)
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
    (hw0 : 𝒟[stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) q_sm
        (sC, s_fig8, fl) ec >>= fun r =>
        runSimCEager P ℓ Dh encPt encT decT idOf lam qep (some sC.base.amb) (cont r.1) r.2.1 r.2.2 >>=
          fun z => pure (z.2.1.1.base.stopped && z.2.1.2.1.win)] = 𝒟[(pure false : ProbComp Bool)])
    (hamb : sC'.base.amb = sC.base.amb + 1)
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
    have h := evalDist_runWinAtC_inr_amb_stopEq_bind P ℓ Dh encPt encT decT idOf lam qep q_sm
      cont (sC, s_fig8, fl) ec (pure ()) (fun _ => (ans, ((sC', s_fig8', fl'), ec')))
      (fun _ => hamb) (by rw [hnone]; simp) false hw0 winBefore idx
    rw [h, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind]
  · unfold runHidC
    rw [runSimCEager_inr_bind, hnone, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm

/-- Inside `inReceiveOnlyEpoch`, if `spurPtStep` is `false` under `ec Q`, libsignal rejects the evicted wire for every receive coin. -/
theorem receive_none_of_spurPtStep_false_inWin (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hsim : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (Q : Party) (w : List (BitVec 8))
    (hlen : ¬ w.length < 9) (hw32 : w.length < 2 ^ 32)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = false)
    (hinw : inReceiveOnlyEpoch s.mir Q = true)
    (T : Pt) (hT_dec : decT h.senderRatchetKey = some T) (hT_ne0 : T ≠ 0)
    (hencT : encT T = h.senderRatchetKey)
    (hfind_res : ((resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains Q).findIdx?
      (fun g => g.key == some h.senderRatchetKey) = none)
    (hdummy_res : ∀ g ∈ (resolveSim (encT (Dh.dh x₀ Dh.base)) s).chains Q,
      g.key = none → h.senderRatchetKey ≠ dummyKey)
    (hspur : spurPtStep P Dh encPt decT Q w false (ec Q) (s, s_fig8) = false) :
    ∀ rc, P.receive (s_R.st Q) w rc = none := by
  letI : DecidableEq PQ := Classical.decEq PQ
  let spkKey := encT (Dh.dh x₀ Dh.base)
  rcases hsim.hspur Q with ⟨rk_base, T_base, hinw_sp, _, _⟩
  rcases hinw_sp hinw with ⟨hroot, hγ, hT_base_ne0, _⟩
  have hspur_single : spurBadSinglePt P encPt Dh Q (s_fig8.st Q).root T_base w salt T (ec Q) = false := by
    unfold spurPtStep at hspur
    simp only [hsim.hmeta.hwin_fig8, hinw, Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hγ, hT_base_ne0, hlen, hparse, hspqr, hpan, hT_dec, hT_ne0] at hspur
    exact hspur
  have hf_R := expectedGhost_session_fields P Dh encPt spkKey s Q (s_fig8.st Q) (ec Q)
  rw [← hsim.hst_R Q] at hf_R
  rcases hf_R with ⟨hparty_R, hver_R, hloc_R, hrem_R, hpq_R, hrc_R⟩
  have hspqr_R : P.spqr.recv (s_R.st Q).session.pqRatchetState h.pqRatchet = .ok (pq', salt) := by
    rw [hpq_R]; exact hspqr
  have hfind_R : (s_R.st Q).session.receiverChains.findIdx?
      (fun ch => ch.senderRatchetKey == h.senderRatchetKey) = none := by
    rw [hrc_R, findIdx_toRecvChain_gen (s_fig8.st Q) ((resolveSim spkKey s).chains Q) h.senderRatchetKey
      hdummy_res]
    exact hfind_res
  have hrk_R : (s_R.st Q).session.rootKey =
      (rootKdf P.C.F (s_fig8.st Q).root (encPt (Dh.dh (ec Q) T_base))).1 := by
    rw [hsim.hst_R Q, expectedGhost_of_inWin_true P Dh encPt spkKey s Q (s_fig8.st Q) (ec Q) T_base hinw hγ]
    rfl
  have hsc_R : (s_R.st Q).session.senderChain =
      some ⟨KeyPair.generate P.C (ec Q),
        ⟨((rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (ec Q) T_base)).2, 0⟩⟩ := by
    rw [hsim.hst_R Q, expectedGhost_of_inWin_true P Dh encPt spkKey s Q (s_fig8.st Q) (ec Q) T_base hinw hγ]
    rfl
  intro rc
  exact receive_newChain_eq_none_of_spurBadSinglePt_false P Dh encPt encT hX Q (s_R.st Q)
    hparty_R hver_R hloc_R hrem_R (s_fig8.st Q).root T_base (ec Q) _ 0 hrk_R hsc_R
    w hlen hw32 h body hparse haddrs pq' salt hspqr_R hfind_R T hT_ne0 hencT hspur_single rc

end CryptoGames.LibsignalSM.Proofs.Refinement
