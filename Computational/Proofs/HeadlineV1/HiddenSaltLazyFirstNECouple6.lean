/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple4
import ProofLib.SepLogic.WP.StateNorm

/-!
# Per-Query Cell Coupling for `transmit`, `chall`, and `MirrorSync`

**Checked by Lean.** Proves `transmit` and `chall` step lemmas for `kemFailSendStep` and defines
the mirror synchronization invariant `MirrorSync` with its preservation lemmas.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem runCellStep_zoomB_eq_liftC {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL (LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ) x) sC sent m' s_cell =
      (runCellStep fig qep t tL (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (x.run sC.base))
        sC sent m' s_cell >>=
        fun z =>
          pure ((((z.1.1.1.1.1, { z.1.1.1.2 with base := z.1.1.1.1.2 }), z.1.1.2), z.1.2),
            z.2)) := by
  rw [runCellStep_zoomB, runCellStep_liftC]
  simp only [bind_assoc, pure_bind]

theorem runCellStep_liftC_pure {PQ Pt α : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (a : α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (pure a : Fig8Comp Pt ℓ α))
      sC sent m' s_cell =
      pure ((((a, sC), sent), m'), s_cell) := by
  rw [runCellStep_liftC]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]

theorem runCellStep_liftC_bind {PQ Pt α β : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ)
    (u : Fig8Comp Pt ℓ α) (v : α → Fig8Comp Pt ℓ β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (u >>= v)) sC sent m' s_cell =
      (runCellStep fig qep t tL (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) u)
        sC sent m' s_cell >>=
        fun z =>
          runCellStep fig qep t tL
            (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (v z.1.1.1.1))
            z.1.1.1.2 z.1.1.2 z.1.2 z.2) := by
  simp only [runCellStep_liftC, simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]

theorem simSend_run_of_guard_fail {PQ PQC Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    (P : Params PQ PQC) (qep : ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option PQC) (s : SimState PQ Pt ℓ)
    (hfail :
      (s.mir.win || !SM.noBobSendInEpoch0 s.mir Q) = true ∨
      s.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, s.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
        (chal.isSome && !s₁.safeCh 3 Q) = true) :
    (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r).run s = pure (none, s) := by
  unfold LibsignalSim.simSend
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hfail with hg1 | hg2 | ⟨s₁, hep, hg3⟩
  · simp [hg1]
  · by_cases hg1 : (s.mir.win || !SM.noBobSendInEpoch0 s.mir Q) = true
    · simp [hg1]
    · simp [hg1, hg2]
  · by_cases hg1 : (s.mir.win || !SM.noBobSendInEpoch0 s.mir Q) = true
    · simp [hg1]
    · simp [hg1, hep, hg3]

theorem runCellStep_simSendC_of_guard_fail {PQ PQC Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (t : ℕ) (tL : Option ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option PQC)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hfail :
      (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true ∨
      sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
      ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
        (chal.isSome && !s₁.safeCh 3 Q) = true) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC
        (LibsignalSimC.simSendC P qep fig (deliverForgeHook Pt ℓ) Q m₀ chal r))
      sC sent m' s_cell =
      pure ((((none, sC), sent), m'), s_cell) := by
  by_cases hstop : sC.base.stopped = true
  · exact runCellStep_guardC_stopped_true fig qep t tL _ sC sent m' s_cell hstop
  · have hstop_f : sC.base.stopped = false := Bool.eq_false_iff.mpr hstop
    rw [runCellStep_guardC_stopped_false fig qep t tL _ sC sent m' s_cell hstop_f]
    have hfail' :
        (sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true ∨
        sC.base.mir.epMgmt 3 qep Q r.isSome = none ∨
        ∃ s₁, sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁ ∧
          (chal.isSome && !s₁.safeCh 3 Q) = true := by
      rcases hfail with hg1 | hg2 | hg3
      · left; simpa [hstop_f] using hg1
      · exact Or.inr (Or.inl hg2)
      · exact Or.inr (Or.inr hg3)
    unfold LibsignalSimC.simSendC
    rw [runCellStep_bind, runCellStep_zoomB_eq_liftC,
      simSend_run_of_guard_fail P qep Q m₀ chal r sC.base hfail',
      runCellStep_liftC_pure]
    simp only [pure_bind, runCellStep_pure]

def drawRq (r : Option (BitVec 512)) : ProbComp (BitVec 512) :=
  match r with
  | some rq => pure rq
  | none => ($ᵗ BitVec 512 : ProbComp (BitVec 512))

def drawRc (r : Option (BitVec 512)) : ProbComp (Option (BitVec 256)) :=
  match r with
  | some _ => some <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))
  | none => pure none

def updSimStateCSend {PQ Pt : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (isChall : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : PQ) (pn : BitVec 32) (c : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : LibsignalToModularSchemeSimState PQ Pt ℓ :=
  let w := LibsignalSim.toWire c
  let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) :=
    ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
  let mir' := s₁.record 3 Q () rec' isChall
  let base' : SimState PQ Pt ℓ :=
    { sC.base with
      mir := mir'
      pq := Function.update sC.base.pq Q pq'
      pn := Function.update sC.base.pn Q pn
      honest := (w, c) :: sC.base.honest }
  let sent' := match (sC.kept Q).full, base'.honest.head? with
    | some st, some (_, c₀) =>
      if st.id.sendsIn (st.tcur + 1) then sC.sent
      else match st.vS with
        | some v => (c₀, v) :: sC.sent
        | none => sC.sent
    | _, _ => sC.sent
  { sC with
    base := base'
    kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q))
    sent := sent' }

def simSendQFig {Pt : Type} {ℓ : ℕ} (Q : Party) (pub : LibsignalMsgPublicPart) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (rc : Option (BitVec 256)) :
    Fig8Comp Pt ℓ (Option (Fig8C Pt)) :=
  match chal with
  | none => SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
  | some m₁ => SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc

theorem kemFailSendStep_run_of_guards_pass {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (tr : KemFailTrackState P.C.F)
    (hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    (kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ chal r).run (sC, (g, fl), tr) =
      (drawRq r >>= fun rq =>
        drawRc r >>= fun rc =>
          let tr' := stepKemFailSend P.C.F K tr Q rq
          match LibsignalSim.mkPub (P := P) sC.base Q rq pn with
          | none => pure (none, (sC, (g, fl), { tr with cand := tr'.cand }))
          | some (pq', pub) =>
            ((probeHook fig (qep + 1)).lift (simSendQFig Q pub m₀ chal rc)).run (g, fl) >>=
              fun p =>
                match p.1 with
                | none => pure (none, (sC, p.2, { tr with cand := tr'.cand }))
                | some c =>
                  pure (some (LibsignalSim.toWire c),
                    (updSimStateCSend fig Q m₀ chal.isSome s₁ pq' pn c sC, p.2, tr'))) := by
  intro fig pn
  unfold kemFailSendStep
  rw [stateT_run_get_bind_prod3]
  simp only [hg1, Bool.false_eq_true, ↓reduceIte, hep, hg3]
  cases r with
  | none =>
    simp only [drawRq, drawRc, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      pure_bind, bind_assoc]
    refine bind_congr fun rq => ?_
    dsimp only [pn]
    cases LibsignalSim.mkPub (P := P) sC.base Q rq pn with
    | none => simp [StateT.run_set]
    | some p_pub =>
      rcases p_pub with ⟨pq', pub⟩
      simp only [simSendQFig, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
        bind_assoc]
      refine bind_congr fun p => ?_
      rcases p with ⟨res, gh'⟩
      cases res
      · simp [StateT.run_set]
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          updSimStateCSend, fig]
        cases (sC.kept Q).full <;> rfl
  | some rq =>
    simp only [drawRq, drawRc, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
      map_eq_bind_pure_comp, Function.comp_apply, pure_bind, bind_assoc]
    refine bind_congr fun c_cka => ?_
    dsimp only [pn]
    cases LibsignalSim.mkPub (P := P) sC.base Q rq pn with
    | none => simp [StateT.run_set]
    | some p_pub =>
      rcases p_pub with ⟨pq', pub⟩
      simp only [simSendQFig, StateT.run_bind, StateT.run_monadLift, MonadLiftT.monadLift,
        bind_assoc]
      refine bind_congr fun p => ?_
      rcases p with ⟨res, gh'⟩
      cases res
      · simp [StateT.run_set]
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          updSimStateCSend, fig]
        cases (sC.kept Q).full <;> rfl

def simSendBodyFig8 {PQ PQC Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt]
    (P : Params PQ PQC) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ) (rq : PQC) (rc : Option (BitVec 256)) :
    Fig8Comp Pt ℓ (Option (List (BitVec 8)) × SimState PQ Pt ℓ) :=
  let pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
  match LibsignalSim.mkPub (P := P) s Q rq pn with
  | none => pure (none, s)
  | some (pq', pub) =>
    simSendQFig Q pub m₀ chal rc >>= fun res =>
      match res with
      | none => pure (none, s)
      | some c =>
        let w := LibsignalSim.toWire c
        let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) :=
          ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
        let mir' := s₁.record 3 Q () rec' chal.isSome
        pure (some w,
          { s with mir := mir', pq := Function.update s.pq Q pq',
                   pn := Function.update s.pn Q pn, honest := (w, c) :: s.honest })

theorem simSend_none_run_of_guards_pass {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (qep : ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (hmir : (s.mir.win || !SM.noBobSendInEpoch0 s.mir Q) = false)
    (hep : s.mir.epMgmt 3 qep Q false = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false) :
    (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal none).run s =
      ((liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512)) : Fig8Comp Pt ℓ (BitVec 512)) >>=
        fun rq => simSendBodyFig8 P Q m₀ chal s₁ s rq none) := by
  unfold LibsignalSim.simSend
  simp only [Option.isSome_none, StateT.run_bind, StateT.run_get, pure_bind, hmir,
    Bool.false_eq_true, ↓reduceIte, hep, hg3]
  unfold LibsignalSim.coin LibsignalSim.liftQ
  rw [StateT_run_lift]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun rq => ?_
  unfold simSendBodyFig8 simSendQFig
  dsimp only
  cases LibsignalSim.mkPub (P := P) s Q rq
    (if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q) with
  | none => simp
  | some p_pub =>
    rcases p_pub with ⟨pq', pub⟩
    cases chal <;>
    · simp only [LibsignalSim.putS, StateT.run_bind, StateT_run_lift, bind_assoc, pure_bind]
      refine bind_congr fun res => ?_
      cases res <;> simp

theorem simSend_some_run_of_guards_pass {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (qep : ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (rq : BitVec 512)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (hmir : (s.mir.win || !SM.noBobSendInEpoch0 s.mir Q) = false)
    (hep : s.mir.epMgmt 3 qep Q true = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false) :
    (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal (some rq)).run s =
      ((liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256)) >>=
        fun c_cka => simSendBodyFig8 P Q m₀ chal s₁ s rq (some c_cka)) := by
  unfold LibsignalSim.simSend
  simp only [Option.isSome_some, StateT.run_bind, StateT.run_get, pure_bind,
    hmir, Bool.false_eq_true, ↓reduceIte, hep, hg3, StateT.run_map]
  unfold LibsignalSim.coin LibsignalSim.liftQ
  rw [StateT_run_lift]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  refine bind_congr fun c_cka => ?_
  unfold simSendBodyFig8 simSendQFig
  dsimp only
  cases LibsignalSim.mkPub (P := P) s Q rq
    (if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q) with
  | none => simp
  | some p_pub =>
    rcases p_pub with ⟨pq', pub⟩
    cases chal <;>
    · simp only [LibsignalSim.putS, StateT.run_bind, StateT_run_lift, bind_assoc, pure_bind]
      refine bind_congr fun res => ?_
      cases res <;> simp

theorem runCellStep_liftC_sC_eq {PQ Pt α β : Type} {ℓ : ℕ} [DecidableEq Pt] [Zero Pt]
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (t : ℕ) (tL : Option ℕ) (y : Fig8Comp Pt ℓ α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (k : (((α × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) → ProbComp β) :
    (runCellStep fig qep t tL (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) y)
      sC sent m' s_cell >>= k) =
      (runCellStep fig qep t tL (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) y)
        sC sent m' s_cell >>=
        fun z => k ((((z.1.1.1.1, sC), z.1.1.2), z.1.2), z.2)) := by
  rw [runCellStep_liftC]
  simp only [bind_assoc, pure_bind]

theorem runCellStep_simSendBodyFig8 {PQ PQC Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt]
    (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (t : ℕ) (tL : Option ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (rq : PQC) (rc : Option (BitVec 256))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
      else sC.base.pn Q
    runCellStep fig qep t tL
      (LibsignalSimC.liftC (deliverForgeHook Pt ℓ)
        (simSendBodyFig8 P Q m₀ chal s₁ sC.base rq rc))
      sC sent m' s_cell =
      match LibsignalSim.mkPub (P := P) sC.base Q rq pn with
      | none => pure (((((none, sC.base), sC), sent), m'), s_cell)
      | some (pq', pub) =>
        runCellStep fig qep t tL
          (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ chal rc))
          sC sent m' s_cell >>= fun z =>
          match z.1.1.1.1 with
          | none => pure (((((none, sC.base), z.1.1.1.2), z.1.1.2), z.1.2), z.2)
          | some c =>
            let w := LibsignalSim.toWire c
            let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) :=
              ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
            let mir' := s₁.record 3 Q () rec' chal.isSome
            let base' : SimState PQ Pt ℓ :=
              { sC.base with mir := mir', pq := Function.update sC.base.pq Q pq',
                             pn := Function.update sC.base.pn Q pn,
                             honest := (w, c) :: sC.base.honest }
            pure (((((some w, base'), z.1.1.1.2), z.1.1.2), z.1.2), z.2) := by
  intro pn
  unfold simSendBodyFig8
  dsimp only [pn]
  cases LibsignalSim.mkPub (P := P) sC.base Q rq pn with
  | none => exact runCellStep_liftC_pure fig qep t tL (none, sC.base) sC sent m' s_cell
  | some p_pub =>
    rcases p_pub with ⟨pq', pub⟩
    dsimp only
    rw [runCellStep_liftC_bind]
    refine bind_congr fun z => ?_
    cases z.1.1.1.1 <;> exact runCellStep_liftC_pure _ _ _ _ _ _ _ _ _

theorem runCellStep_simSendC_of_guards_pass {PQ Pt : Type} {ℓ : ℕ} [Inhabited PQ]
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params PQ (BitVec 512)) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (t : ℕ) (tL : Option ℕ) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3 : (chal.isSome && !s₁.safeCh 3 Q) = false) :
    runCellStep fig qep t tL
      (LibsignalSimC.guardC (LibsignalSimC.simSendC P qep fig (deliverForgeHook Pt ℓ) Q m₀ chal r))
      sC sent m' s_cell =
      (let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
        else sC.base.pn Q
      drawRq r >>= fun rq =>
        drawRc r >>= fun _rc =>
          match LibsignalSim.mkPub (P := P) sC.base Q rq pn with
          | none => pure ((((none, sC), sent), m'), s_cell)
          | some (pq', pub) =>
            runCellStep fig qep t tL
              (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ chal _rc))
              sC sent m' s_cell >>= fun z =>
              match z.1.1.1.1 with
              | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
              | some c =>
                pure ((((some (LibsignalSim.toWire c),
                  updSimStateCSend fig Q m₀ chal.isSome s₁ pq' pn c sC),
                  z.1.1.2), z.1.2), z.2)) := by
  let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
    else sC.base.pn Q
  dsimp only
  have hstop : sC.base.stopped = false := by
    cases h : sC.base.stopped
    · rfl
    · simp [h] at hg1
  have hmir : (sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false := by
    simpa [hstop] using hg1
  rw [runCellStep_guardC_stopped_false fig qep t tL _ sC sent m' s_cell hstop]
  unfold LibsignalSimC.simSendC
  rw [runCellStep_bind, runCellStep_zoomB_eq_liftC]
  simp only [bind_assoc, pure_bind]
  cases r with
  | none =>
    rw [simSend_none_run_of_guards_pass P qep Q m₀ chal s₁ sC.base hmir hep hg3]
    rw [runCellStep_liftC_bind, runCellStep_liftC_liftM]
    simp only [drawRq, drawRc, pure_bind, bind_assoc]
    refine bind_congr fun rq => ?_
    rw [runCellStep_simSendBodyFig8]
    dsimp only [pn]
    cases LibsignalSim.mkPub (P := P) sC.base Q rq pn with
    | none =>
      simp only [pure_bind, runCellStep_pure]
    | some p_pub =>
      rcases p_pub with ⟨pq', pub⟩
      dsimp only
      rw [runCellStep_liftC_sC_eq]
      simp only [bind_assoc]
      refine bind_congr fun z => ?_
      cases z.1.1.1.1 with
      | none =>
        simp only [pure_bind, runCellStep_pure]
      | some c =>
        simp only [pure_bind, runCellStep_bind, runCellStep_get, runCellStep_set,
          runCellStep_pure, updSimStateCSend]
        cases (sC.kept Q).full <;> rfl
  | some rq =>
    rw [simSend_some_run_of_guards_pass P qep Q m₀ chal rq s₁ sC.base hmir hep hg3]
    rw [runCellStep_liftC_bind, runCellStep_liftC_liftM]
    simp only [drawRq, drawRc, map_eq_bind_pure_comp, Function.comp_apply, pure_bind, bind_assoc]
    refine bind_congr fun c_cka => ?_
    rw [runCellStep_simSendBodyFig8]
    dsimp only [pn]
    cases LibsignalSim.mkPub (P := P) sC.base Q rq pn with
    | none =>
      simp only [pure_bind, runCellStep_pure]
    | some p_pub =>
      rcases p_pub with ⟨pq', pub⟩
      dsimp only
      rw [runCellStep_liftC_sC_eq]
      simp only [bind_assoc]
      refine bind_congr fun z => ?_
      cases z.1.1.1.1 with
      | none =>
        simp only [pure_bind, runCellStep_pure]
      | some c =>
        simp only [pure_bind, runCellStep_bind, runCellStep_get, runCellStep_set,
          runCellStep_pure, updSimStateCSend]
        cases (sC.kept Q).full <;> rfl

theorem drawRc_bind_samIfNec {α : Type}
    (r : Option (BitVec 512)) (k : BitVec 256 × Bool → ProbComp α) :
    (drawRc r >>= fun rc => SM.samIfNec rc >>= k) =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun coins => k (coins, r.isSome)) := by
  cases r with
  | none => rfl
  | some _ =>
    simp [drawRc, SM.samIfNec, map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_drawRc_bind_const {α : Type} [MeasurableSpace α]
    (r : Option (BitVec 512)) (q : ProbComp α) :
    𝒟[drawRc r >>= fun _rc => q] = 𝒟[q] := by
  cases r with
  | none => rfl
  | some _ =>
    simp only [drawRc, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _

theorem evalDist_transmitImpl_none_run_eq_bind_coins {Key St Msg C α : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [MeasurableSpace α]
    (sm : SMScheme Key St Msg (BitVec 256) C) (Δ qep : ℕ) (Q : Party) (m_msg : Msg)
    (s_cell : SM.GameState St Msg C)
    (k : Option C × SM.GameState St Msg C → ProbComp α) :
    𝒟[(SM.transmitImpl sm Δ qep (Q, m_msg, none)).run s_cell >>= k] =
      𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun coins =>
        k (if s_cell.win then (none, s_cell)
           else transmitPure sm Δ qep Q m_msg coins false s_cell)] := by
  rw [transmitImpl_run_eq]
  by_cases hwin : s_cell.win = true
  · simp only [hwin, ↓reduceIte, pure_bind]
    exact (OracleComp.evalDist_bind_const _ _).symm
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem transmitPure_eq_of_pprimePaperRelShifted {Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (P : Party) (m_msg : Msg) (coins : Coins)
    (bad : Bool) {s_df : SM.GameState St Msg C} {m' : Mirror Msg C}
    {g g₁ : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁) :
    let c := (sm.send (g₁.st P) m_msg coins).2
    let st' := (sm.send (g₁.st P) m_msg coins).1
    let rec_r : SM.Record Msg C := ⟨⟨P, g₁.epoch P, g₁.idx P + 1⟩, m_msg, c⟩
    transmitPure sm (2 + 1) (qep + 1) P m_msg coins bad g =
      (some c, g₁.record (2 + 1) P st' rec_r false) ∧
    transmitPure sm Δ (qep + 1) P m_msg coins false s_df =
      (some c,
        if s_df.win then s_df
        else match s_df.epMgmt Δ (qep + 1) P false with
          | some s₁ => s₁.record Δ P st' rec_r false
          | none => s_df) := by
  intro c st' rec_r
  obtain ⟨s_df₁, hep_df, _, _, hrel₁⟩ := hrel.epMgmt_step (Δ := Δ) (m₁' := m') hep_g
  have hst : s_df₁.st P = g₁.st P := congrFun hrel₁.st_eq P
  have hep : s_df₁.epoch P = g₁.epoch P := congrFun hrel₁.epoch_eq P
  have hidx : s_df₁.idx P = g₁.idx P := congrFun hrel₁.idx_eq P
  refine ⟨?_, ?_⟩
  · unfold transmitPure
    simp [hep_g, c, st', rec_r]
  · unfold transmitPure
    simp [hrel.win_df_false, hep_df, hst, hep, hidx, c, st', rec_r]

theorem challPure_eq_of_pprimePaperRelShifted {Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (P : Party) (m₀ m₁ : Msg) (coins : Coins)
    (bad : Bool) {s_df : SM.GameState St Msg C} {m' : Mirror Msg C}
    {g g₁ : SM.GameState St Msg C}
    (hrel : PPrimePaperRelShifted s_df m' g)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) P bad = some g₁)
    (hsafe_g : g₁.safeCh (2 + 1) P = true)
    (hb : m'.b = g.b) :
    let m_ch := if m'.b then m₁ else m₀
    let c := (sm.send (g₁.st P) m_ch coins).2
    let st' := (sm.send (g₁.st P) m_ch coins).1
    let rec_r : SM.Record Msg C := ⟨⟨P, g₁.epoch P, g₁.idx P + 1⟩, m_ch, c⟩
    challPure sm (2 + 1) (qep + 1) SM.Config.h1 P m₀ m₁ coins bad g =
      (some c, g₁.record (2 + 1) P st' rec_r true) ∧
    transmitPure sm Δ (qep + 1) P m_ch coins false s_df =
      (some c,
        if s_df.win then s_df
        else match s_df.epMgmt Δ (qep + 1) P false with
          | some s₁ => s₁.record Δ P st' rec_r false
          | none => s_df) := by
  intro m_ch c st' rec_r
  have htr := (transmitPure_eq_of_pprimePaperRelShifted sm Δ qep P m_ch coins bad hrel hep_g).2
  refine ⟨?_, htr⟩
  unfold challPure
  simp [hep_g, hsafe_g, SM.Config.h1, hb, m_ch, c, st', rec_r]

def cellTransmitPost {PQ Pt β : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (Q : Party) (m₀ : Plain ℓ)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : PQ) (pub : LibsignalMsgPublicPart) (pn : BitVec 32)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (k : (((Option (List (BitVec 8)) × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) → ProbComp β)
    (z : Option (Fig8C Pt) × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp β :=
  let sent₁ := match z.1 with | some c => c :: sent | none => sent
  let m₁' := match z.1, m'.epMgmt (2 + 1) (qep + 1) Q false with
    | some c, some m₁ =>
      m₁.record (2 + 1) Q () ⟨⟨Q, m₁.epoch Q, m₁.idx Q + 1⟩, (pub, m₀), c⟩ false
    | _, _ => m'
  match z.1 with
  | none => k ((((none, sC), sent₁), m₁'), z.2)
  | some c =>
    k ((((some (LibsignalSim.toWire c),
      updSimStateCSend fig Q m₀ false s₁ pq' pn c sC),
      sent₁), m₁'), z.2)

theorem evalDist_cell_transmit_mkPub_some {Pt β : Type} {ℓ : ℕ}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [MeasurableSpace β]
    (P : Params (List (BitVec 8)) (BitVec 512)) (qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : List (BitVec 8)) (pub : LibsignalMsgPublicPart) (pn : BitVec 32)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (k : (((Option (List (BitVec 8)) × LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) × List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) → ProbComp β) :
    𝒟[drawRc r >>= fun _rc =>
        (runCellStep fig qep t tL
          (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ none _rc))
          sC sent m' s_cell >>= fun z =>
          match z.1.1.1.1 with
          | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
          | some c =>
            pure ((((some (LibsignalSim.toWire c),
              updSimStateCSend fig Q m₀ false s₁ pq' pn c sC),
              z.1.1.2), z.1.2), z.2)) >>= k] =
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun coins =>
        cellTransmitPost fig qep Q m₀ s₁ pq' pub pn sC sent m' k
          (if s_cell.win then (none, s_cell)
           else transmitPure fig (cellDelta tL t) (qep + 1) Q (pub, m₀) coins false s_cell)] := by
  let _ := P
  rw [← bind_assoc]
  have hcongr :
      ((drawRc r >>= fun _rc =>
        runCellStep fig qep t tL
          (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ none _rc))
          sC sent m' s_cell >>= fun z =>
          match z.1.1.1.1 with
          | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
          | some c =>
            pure ((((some (LibsignalSim.toWire c),
              updSimStateCSend fig Q m₀ false s₁ pq' pn c sC),
              z.1.1.2), z.1.2), z.2)) >>= k) =
      (drawRc r >>= fun _rc =>
        (SM.transmitImpl fig (cellDelta tL t) (qep + 1) (Q, (pub, m₀), none)).run s_cell >>=
          cellTransmitPost fig qep Q m₀ s₁ pq' pub pn sC sent m' k) := by
    simp only [bind_assoc]
    refine bind_congr fun _rc => ?_
    simp only [simSendQFig, runCellStep_liftC_transmit, bind_assoc, pure_bind]
    refine bind_congr fun z => ?_
    rcases z with ⟨res, s'⟩
    dsimp only [cellTransmitPost]
    cases res with
    | none => simp [pure_bind]
    | some c => cases m'.epMgmt (2 + 1) (qep + 1) Q false <;> simp [pure_bind]
  rw [hcongr, evalDist_drawRc_bind_const, evalDist_transmitImpl_none_run_eq_bind_coins]

theorem kemFailSendStep_transmit_mkPub_some {Pt β : Type} {ℓ : ℕ}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : List (BitVec 8)) (pub : LibsignalMsgPublicPart) (pn : BitVec 32)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr tr' : KemFailTrackState P.C.F)
    (hg_win : g.win = false)
    (k : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F) → ProbComp β) :
    (drawRc r >>= fun rc =>
      (((probeHook fig (qep + 1)).lift (simSendQFig Q pub m₀ none rc)).run (g, false) >>=
        fun p =>
          match p.1 with
          | none => pure (none, (sC, p.2, { tr with cand := tr'.cand }))
          | some c =>
            pure (some (LibsignalSim.toWire c),
              (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC, p.2, tr'))) >>= k) =
    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun coins =>
      let z := transmitPure fig (2 + 1) (qep + 1) Q (pub, m₀) coins r.isSome g
      match z.1 with
      | none => k (none, (sC, (z.2, false), { tr with cand := tr'.cand }))
      | some c =>
        k (some (LibsignalSim.toWire c),
          (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC, (z.2, false), tr'))) := by
  rw [← bind_assoc]
  have h1 :
      ((drawRc r >>= fun rc =>
        ((probeHook fig (qep + 1)).lift (simSendQFig Q pub m₀ none rc)).run (g, false) >>=
          fun p =>
            match p.1 with
            | none => pure (none, (sC, p.2, { tr with cand := tr'.cand }))
            | some c =>
              pure (some (LibsignalSim.toWire c),
                (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC, p.2, tr'))) >>= k) =
      (drawRc r >>= fun rc =>
        SM.samIfNec rc >>= fun cb =>
          let z := transmitPure fig (2 + 1) (qep + 1) Q (pub, m₀) cb.1 cb.2 g
          match z.1 with
          | none => k (none, (sC, (z.2, false), { tr with cand := tr'.cand }))
          | some c =>
            k (some (LibsignalSim.toWire c),
              (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC, (z.2, false), tr'))) := by
    simp only [simSendQFig, probeHook_lift_transmitQuery_run, hg_win, Bool.false_eq_true,
      ↓reduceIte, bind_assoc, pure_bind]
    refine bind_congr fun rc => bind_congr fun cb => ?_
    cases (transmitPure fig (2 + 1) (qep + 1) Q (pub, m₀) cb.1 cb.2 g).1 <;> rfl
  rw [h1, drawRc_bind_samIfNec]

def cellChallPost {PQ Pt β : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (m_ch : LibsignalMsgPublicPart × Plain ℓ)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : PQ) (pn : BitVec 32)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (k : (((Option (List (BitVec 8)) × LibsignalToModularSchemeSimState PQ Pt ℓ) × List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) → ProbComp β)
    (z : Option (Fig8C Pt) × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    ProbComp β :=
  match z.1 with
  | none => k ((((none, sC), sent), m'), z.2)
  | some c =>
    k ((((some (LibsignalSim.toWire c),
      updSimStateCSend fig Q m₀ true s₁ pq' pn c sC),
      c :: sent),
      m₁'.record (2 + 1) Q () ⟨⟨Q, m₁'.epoch Q, m₁'.idx Q + 1⟩, m_ch, c⟩ true), z.2)

theorem evalDist_cell_chall_mkPub_some {Pt β : Type} {ℓ : ℕ}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [MeasurableSpace β]
    (qep t : ℕ) (tL : Option ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : List (BitVec 8)) (pub : LibsignalMsgPublicPart) (pn : BitVec 32)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) (sent : List (Fig8C Pt))
    (m' m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hep_m : m'.epMgmt (2 + 1) (qep + 1) Q false = some m₁')
    (hsafe_m : m₁'.safeCh (2 + 1) Q = true)
    (k : (((Option (List (BitVec 8)) × LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) × List (Fig8C Pt)) ×
      Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) → ProbComp β) :
    𝒟[drawRc r >>= fun _rc =>
        (runCellStep fig qep t tL
          (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ (some m₁) _rc))
          sC sent m' s_cell >>= fun z =>
          match z.1.1.1.1 with
          | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
          | some c =>
            pure ((((some (LibsignalSim.toWire c),
              updSimStateCSend fig Q m₀ true s₁ pq' pn c sC),
              z.1.1.2), z.1.2), z.2)) >>= k] =
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun coins =>
        cellChallPost fig Q m₀ (if m'.b then (pub, m₁) else (pub, m₀)) s₁ pq' pn sC sent m' m₁' k
          (if s_cell.win then (none, s_cell)
           else transmitPure fig (cellDelta tL t) (qep + 1) Q
             (if m'.b then (pub, m₁) else (pub, m₀)) coins false s_cell)] := by
  let m_ch := if m'.b then (pub, m₁) else (pub, m₀)
  rw [← bind_assoc]
  have hcongr :
      ((drawRc r >>= fun _rc =>
        runCellStep fig qep t tL
          (LibsignalSimC.liftC (deliverForgeHook Pt ℓ) (simSendQFig Q pub m₀ (some m₁) _rc))
          sC sent m' s_cell >>= fun z =>
          match z.1.1.1.1 with
          | none => pure ((((none, sC), z.1.1.2), z.1.2), z.2)
          | some c =>
            pure ((((some (LibsignalSim.toWire c),
              updSimStateCSend fig Q m₀ true s₁ pq' pn c sC),
              z.1.1.2), z.1.2), z.2)) >>= k) =
      (drawRc r >>= fun _rc =>
        (SM.transmitImpl fig (cellDelta tL t) (qep + 1) (Q, m_ch, none)).run s_cell >>=
          cellChallPost fig Q m₀ m_ch s₁ pq' pn sC sent m' m₁' k) := by
    simp only [bind_assoc]
    refine bind_congr fun _rc => ?_
    simp only [simSendQFig, runCellStep_liftC_chall, hep_m, hsafe_m, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, bind_assoc]
    refine bind_congr fun z => ?_
    rcases z with ⟨res, s'⟩
    dsimp only [cellChallPost, m_ch]
    cases res <;> simp [pure_bind]
  rw [hcongr, evalDist_drawRc_bind_const, evalDist_transmitImpl_none_run_eq_bind_coins]

theorem kemFailSendStep_chall_mkPub_some {Pt β : Type} {ℓ : ℕ}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : List (BitVec 8)) (pub : LibsignalMsgPublicPart) (pn : BitVec 32)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr tr' : KemFailTrackState P.C.F)
    (hg_win : g.win = false)
    (k : Option (List (BitVec 8)) ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState P.C.F) → ProbComp β) :
    (drawRc r >>= fun rc =>
      (((probeHook fig (qep + 1)).lift (simSendQFig Q pub m₀ (some m₁) rc)).run (g, false) >>=
        fun p =>
          match p.1 with
          | none => pure (none, (sC, p.2, { tr with cand := tr'.cand }))
          | some c =>
            pure (some (LibsignalSim.toWire c),
              (updSimStateCSend fig Q m₀ true s₁ pq' pn c sC, p.2, tr'))) >>= k) =
    (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun coins =>
      let z := challPure fig (2 + 1) (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) coins r.isSome g
      match z.1 with
      | none => k (none, (sC, (z.2, false), { tr with cand := tr'.cand }))
      | some c =>
        k (some (LibsignalSim.toWire c),
          (updSimStateCSend fig Q m₀ true s₁ pq' pn c sC, (z.2, false), tr'))) := by
  rw [← bind_assoc]
  have h1 :
      ((drawRc r >>= fun rc =>
        ((probeHook fig (qep + 1)).lift (simSendQFig Q pub m₀ (some m₁) rc)).run (g, false) >>=
          fun p =>
            match p.1 with
            | none => pure (none, (sC, p.2, { tr with cand := tr'.cand }))
            | some c =>
              pure (some (LibsignalSim.toWire c),
                (updSimStateCSend fig Q m₀ true s₁ pq' pn c sC, p.2, tr'))) >>= k) =
      (drawRc r >>= fun rc =>
        SM.samIfNec rc >>= fun cb =>
          let z := challPure fig (2 + 1) (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 g
          match z.1 with
          | none => k (none, (sC, (z.2, false), { tr with cand := tr'.cand }))
          | some c =>
            k (some (LibsignalSim.toWire c),
              (updSimStateCSend fig Q m₀ true s₁ pq' pn c sC, (z.2, false), tr'))) := by
    simp only [simSendQFig, probeHook_lift_challQuery_run, hg_win, Bool.false_eq_true,
      ↓reduceIte, bind_assoc, pure_bind]
    refine bind_congr fun rc => bind_congr fun cb => ?_
    cases (challPure fig (2 + 1) (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) cb.1 cb.2 g).1 <;> rfl
  rw [h1, drawRc_bind_samIfNec]

/-- Synchronization invariant relating the paper-reduction mirror `m'`, the simulator state `g`,
and the unshifted cell state `s_unsh`. -/
structure MirrorSync {St Msg C : Type}
    (m' : Mirror Msg C) (g s_unsh : SM.GameState St Msg C) : Prop where
  b_eq : m'.b = g.b
  epoch_eq : m'.epoch = g.epoch
  idx_eq : m'.idx = g.idx
  corrs_eq : m'.corrs = g.corrs
  trans_eq : m'.trans = g.trans
  chall_eq : m'.chall = g.chall
  tL_eq : m'.tL = s_unsh.tL

theorem mirrorSync_init {Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (k : Key) (b : Bool) :
    MirrorSync (toMirror (SM.initState sm k b))
      (SM.initState sm k b) (SM.initState sm k b) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MirrorSync.corrAllowedPaper_eq {St Msg C : Type}
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh) (Q : Party) :
    m'.corrAllowedPaper Q = g.corrAllowedPaper Q := by
  unfold SM.GameState.corrAllowedPaper
  rw [hsync.chall_eq]

theorem MirrorSync.corrAllowedPaper_of_corrAllowed_g {St Msg C : Type}
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh) {Q : Party}
    (hallow : g.corrAllowed Q = true) :
    m'.corrAllowedPaper Q = true := by
  rw [hsync.corrAllowedPaper_eq]
  exact (corrAllowedPaper_of_corrAllowed (m' := m') hallow).1

theorem MirrorSync.corr_sync {St Msg C : Type} {ℓ : ℕ} {Q : Party}
    {s_mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8))}
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh)
    (hchall_mir : s_mir.chall = g.chall)
    (hcomp_mir : s_mir.comp = g.comp)
    (htrans_pos : s_mir.trans.map SM.Record.pos = g.trans.map SM.Record.pos)
    (href : (((s_mir.win || !s_mir.corrAllowed Q) || inReceiveOnlyEpoch s_mir Q) || !noAliceCorrWhileAliceBelowEpoch10 s_mir Q) =
      false) :
    g.corrAllowed Q = true ∧ m'.corrAllowedPaper Q = true := by
  have hallow_mir : s_mir.corrAllowed Q = true := by
    revert href; cases s_mir.corrAllowed Q <;> simp
  have hallow_g : g.corrAllowed Q = true := by
    unfold SM.GameState.corrAllowed at hallow_mir ⊢
    have htr : (s_mir.trans.any fun r => r.pos.sender == Q.other && !s_mir.comp.contains r.pos) =
        (g.trans.any fun r => r.pos.sender == Q.other && !g.comp.contains r.pos) := by
      have h := congrArg (fun xs : List SM.Pos =>
        xs.any fun pos => pos.sender == Q.other && !g.comp.contains pos) htrans_pos
      simpa [List.any_map, Function.comp_def, hcomp_mir] using h
    rw [← hchall_mir, ← htr]
    exact hallow_mir
  exact ⟨hallow_g, hsync.corrAllowedPaper_of_corrAllowed_g hallow_g⟩

theorem MirrorSync.safeCh_eq_unsh {St Msg C : Type}
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh)
    (hep_unsh : s_unsh.epoch = g.epoch) (Δ : ℕ) (Q : Party) :
    m'.safeCh Δ Q = s_unsh.safeCh Δ Q := by
  unfold SM.GameState.safeCh
  rw [hsync.tL_eq, hsync.epoch_eq, hep_unsh]

theorem MirrorSync.corr_step {St Msg C : Type} (Q : Party)
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh)
    (hep_unsh : s_unsh.epoch = g.epoch) :
    MirrorSync (m'.afterCorr Q) (g.afterCorr Q) (s_unsh.afterCorr Q) where
  b_eq := hsync.b_eq
  epoch_eq := hsync.epoch_eq
  idx_eq := hsync.idx_eq
  corrs_eq := by simp [SM.GameState.afterCorr, hsync.epoch_eq, hsync.corrs_eq]
  trans_eq := hsync.trans_eq
  chall_eq := hsync.chall_eq
  tL_eq := by
    simp [SM.GameState.afterCorr, SM.GameState.leak, hsync.tL_eq, hsync.epoch_eq, hep_unsh]

theorem MirrorSync.inject_step {St Msg C : Type} [DecidableEq C]
    (Q : Party) (st' : St) (pos : SM.Pos)
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh) :
    MirrorSync (m'.accept Q () pos) (g.accept Q st' pos) (s_unsh.accept Q st' pos) where
  b_eq := hsync.b_eq
  epoch_eq := by simp [SM.GameState.accept, SM.GameState.delete, hsync.epoch_eq]
  idx_eq := hsync.idx_eq
  corrs_eq := hsync.corrs_eq
  trans_eq := by simp [SM.GameState.accept, SM.GameState.delete, hsync.trans_eq]
  chall_eq := by simp [SM.GameState.accept, SM.GameState.delete, hsync.chall_eq]
  tL_eq := by simp [SM.GameState.accept, SM.GameState.delete, hsync.tL_eq]

theorem MirrorSync.epMgmt_step {St Msg C : Type} {qep : ℕ} {Q : Party} {bad : Bool}
    {m' : Mirror Msg C} {g g₁ s_unsh s_unsh₁ : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh)
    (hep_unsh : s_unsh.epoch = g.epoch)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) Q bad = some g₁)
    (hep_u : s_unsh.epMgmt (2 + 1) (qep + 1) Q false = some s_unsh₁) :
    ∃ m₁', m'.epMgmt (2 + 1) (qep + 1) Q false = some m₁' ∧
      MirrorSync m₁' g₁ s_unsh₁ := by
  unfold SM.GameState.epMgmt at hep_g hep_u ⊢
  rw [hsync.epoch_eq]
  rw [hep_unsh] at hep_u
  by_cases hsends : Q.sendsIn (g.epoch Q + 1) = true
  · simp only [hsends, ↓reduceIte] at hep_g hep_u ⊢
    by_cases hq : qep + 1 < g.epoch Q + 1
    · simp [hq] at hep_g
    · simp only [hq, ↓reduceIte, Bool.false_and, Bool.false_eq_true, Option.some.injEq]
        at hep_g hep_u ⊢
      subst hep_u
      refine ⟨_, rfl, ?_⟩
      subst hep_g
      by_cases hcond : (bad && !(g.safeCh (2 + 1) Q)) = true <;>
        { simp only [hcond, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hsync.b_eq, by simp [SM.GameState.leak, hsync.epoch_eq],
            by simp [SM.GameState.leak, hsync.idx_eq], hsync.corrs_eq, hsync.trans_eq,
            hsync.chall_eq, hsync.tL_eq⟩ }
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hep_g hep_u ⊢
    by_cases hq : qep + 1 < g.epoch Q
    · simp [hq] at hep_g
    · simp only [hq, ↓reduceIte, Option.some.injEq] at hep_g hep_u ⊢
      subst hep_g hep_u
      exact ⟨m', rfl, hsync⟩

theorem MirrorSync.chall_sync {St Msg C : Type} {ℓ qep : ℕ} {Q : Party} {bad : Bool}
    {s_mir s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))}
    {m' : Mirror Msg C} {g s_unsh : SM.GameState St Msg C}
    (hsync : MirrorSync m' g s_unsh) (hrel : PPrimePaperRel s_unsh m' g)
    (hep_mir : s_mir.epoch = g.epoch) (htL_mir : s_mir.tL = g.tL)
    (hep : s_mir.epMgmt 3 qep Q bad = some s₁) (hsafe : s₁.safeCh 3 Q = true) :
    ∃ g₁ m₁', g.epMgmt (2 + 1) (qep + 1) Q bad = some g₁ ∧ g₁.safeCh (2 + 1) Q = true ∧
      m'.epMgmt (2 + 1) (qep + 1) Q false = some m₁' ∧ m₁'.safeCh (2 + 1) Q = true ∧
      m'.b = g.b := by
  have hg : ∃ g₁, g.epMgmt (2 + 1) (qep + 1) Q bad = some g₁ ∧ g₁.safeCh (2 + 1) Q = true := by
    unfold SM.GameState.epMgmt at hep ⊢; unfold SM.GameState.safeCh at hep hsafe ⊢
    rw [hep_mir, htL_mir] at hep
    by_cases hsends : Q.sendsIn (g.epoch Q + 1) = true
    · simp only [hsends, ↓reduceIte] at hep ⊢
      by_cases hq : qep < g.epoch Q + 1
      · simp [hq] at hep
      · have hq1 : ¬(qep + 1 < g.epoch Q + 1) := by omega
        simp only [hq, hq1, ↓reduceIte, Option.some.injEq] at hep ⊢
        refine ⟨_, rfl, ?_⟩; subst hep; dsimp only at hsafe ⊢
        by_cases hcond : (bad && !SM.healedBy g.tL 3 (g.epoch Q)) = true <;>
          { simp only [hcond, Bool.false_eq_true, ↓reduceIte, SM.GameState.leak, hep_mir,
              htL_mir] at hsafe ⊢; exact hsafe }
    · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hep ⊢
      by_cases hq : qep < g.epoch Q
      · simp [hq] at hep
      · have hq1 : ¬(qep + 1 < g.epoch Q) := by omega
        simp only [hq, hq1, ↓reduceIte, Option.some.injEq] at hep ⊢; subst hep
        exact ⟨g, rfl, by simpa [hep_mir, htL_mir] using hsafe⟩
  rcases hg with ⟨g₁, hep_g, hsafe_g⟩
  obtain ⟨s_unsh₁, hep_u, hrel₁⟩ := hrel.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
  obtain ⟨m₁', hep_m, hsync₁⟩ := hsync.epMgmt_step hrel.epoch_eq hep_g hep_u
  have hsafe_m : m₁'.safeCh (2 + 1) Q = true := by
    rw [hsync₁.safeCh_eq_unsh hrel₁.epoch_eq]; exact hrel₁.safeCh_df_of_safeCh_mir le_rfl hsafe_g
  exact ⟨g₁, m₁', hep_g, hsafe_g, hep_m, hsafe_m, hsync.b_eq⟩

theorem MirrorSync.record_step {St Msg C : Type}
    (Q : Party) (st' : St) (rec_r : SM.Record Msg C) (isChall : Bool)
    {m₁' : Mirror Msg C} {g₁ s_unsh₁ : SM.GameState St Msg C}
    (hsync : MirrorSync m₁' g₁ s_unsh₁) :
    MirrorSync (m₁'.record (2 + 1) Q () rec_r isChall)
      (g₁.record (2 + 1) Q st' rec_r isChall)
      (s_unsh₁.record (2 + 1) Q st' rec_r false) where
  b_eq := hsync.b_eq
  epoch_eq := hsync.epoch_eq
  idx_eq := by simp [SM.GameState.record, hsync.idx_eq]
  corrs_eq := hsync.corrs_eq
  trans_eq := by simp [SM.GameState.record, hsync.trans_eq]
  chall_eq := by simp [SM.GameState.record, hsync.chall_eq]
  tL_eq := hsync.tL_eq

end CryptoVerification.LibsignalSession.HeadlineV1

end
