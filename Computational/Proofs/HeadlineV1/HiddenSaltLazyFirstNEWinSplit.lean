/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple2
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECoupleT
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEInTransTransfer
import ProofLib.BV.WidthNorm
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.StateInv -- shake: keep

/-!
# Deliver-Step Case Split and In-Transit Origin Invariant

Derives the deliver-step case splits `DeliverHcasesAt` and `DeliverHcasesAtExt` from a wrong-salt
probe under the pre-divergence cell-family invariant and the in-transit origin invariant
`FirstNEInTransOriginInv`.
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
open CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem deliverHcasesAt_of_unsh_comp_false {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {Q : Party} {t' : ℕ} {r : SM.Record Msg C}
    {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hwf_unsh : SM.Thm1L17.WFState (2 + 1) (s_cell t' none))
    (hcell_t' : ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t',
      CellK4Doomed tL t' g (s_cell t' tL) ∨
      (PPrimePaperRelShifted (s_cell t' tL) m' g ∧
        SM.Thm1L17.WFState (cellDelta tL t') (s_cell t' tL) ∧
        ShiftedLeakRel (cellShift tL t') (s_cell t' none) (s_cell t' tL) ∧
        CellCompRel tL t' (s_cell t' none) (s_cell t' tL)))
    (hr_trans : r ∈ (s_cell t' none).trans)
    (hr_ep : r.pos.epoch = t')
    (hcomp_unsh : (s_cell t' none).comp.contains r.pos = false) :
    SM.canon t' (s_cell t' none) ∈ SM.admissibleLastLeakGuesses (2 + 1) t' ∧
    SM.canon t' (s_cell t' none) ∈ SM.admissibleLastLeakGuesses 2 t' ∧
    SM.canon t' (s_cell t' none) ≠ some (t' - 2) ∧
    (s_cell t' (SM.canon t' (s_cell t' none))).comp.contains r.pos = false ∧
    DeliverHcasesAt Q t' r g s_cell := by
  have huncomp : r.pos ∉ (s_cell t' none).comp := by
    rw [List.contains_eq_mem, decide_eq_false_iff_not] at hcomp_unsh
    exact hcomp_unsh
  rcases canon_ne_sub_two_of_mem_trans_uncomp hwf_unsh hr_trans hr_ep huncomp with
    ⟨_, hmem3, hmem2, hnot_B1, hne_sub2, _⟩
  set tLStar := SM.canon t' (s_cell t' none)
  rcases (hcell_t' tLStar hmem2).resolve_left (CellK4Doomed.not_of_not_B1 hnot_B1) with
    ⟨_, _, _, hcomp_rel⟩
  have hcomp_star : (s_cell t' tLStar).comp.contains r.pos = false := by
    rw [List.contains_eq_mem, decide_eq_false_iff_not]
    exact fun hmem => huncomp (hcomp_rel.comp_sh_sub_unsh r.pos hmem)
  exact ⟨hmem3, hmem2, hne_sub2, hcomp_star, Or.inr (Or.inl ⟨hcomp_unsh, hcomp_star⟩)⟩

theorem deliverHcasesAt_of_unsh_comp_false_and_inv {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C]
    {Q : Party} {t' : ℕ} {r : SM.Record Msg C}
    {m' : Mirror Msg C} {g : SM.GameState St Msg C}
    {s_cell : ℕ → Option ℕ → SM.GameState St Msg C}
    (hwf_unsh : SM.Thm1L17.WFState (2 + 1) (s_cell t' none))
    (hcell_t' : ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t',
      CellK4Doomed tL t' g (s_cell t' tL) ∨
      (PPrimePaperRelShifted (s_cell t' tL) m' g ∧
        SM.Thm1L17.WFState (cellDelta tL t') (s_cell t' tL) ∧
        ShiftedLeakRel (cellShift tL t') (s_cell t' none) (s_cell t' tL) ∧
        CellCompRel tL t' (s_cell t' none) (s_cell t' tL)))
    (hr_trans : r ∈ (s_cell t' none).trans)
    (hr_ep : r.pos.epoch = t')
    (hcomp_unsh : (s_cell t' none).comp.contains r.pos = false) :
    DeliverHcasesAt Q t' r g s_cell :=
  (deliverHcasesAt_of_unsh_comp_false hwf_unsh hcell_t' hr_trans hr_ep hcomp_unsh).2.2.2.2

theorem mem_trans_and_epoch_eq_of_inTransit {St Msg C : Type} [DecidableEq C]
    {t' i' : ℕ} {Q : Party} {c : C} {r : SM.Record Msg C}
    {m' : Mirror Msg C} {g : SM.GameState St Msg C} {s_unsh : SM.GameState St Msg C}
    (hrel_unsh : PPrimePaperRel s_unsh m' g)
    (hin_g : g.inTransit Q.other c = some r)
    (hr_pos : r.pos = ⟨Q.other, t', i'⟩) :
    r ∈ s_unsh.trans ∧ r.pos.epoch = t' := by
  have hin_unsh : s_unsh.inTransit Q.other c = some r := by
    rw [hrel_unsh.inTransit_eq]; exact hin_g
  exact ⟨List.mem_of_find?_eq_some hin_unsh, by rw [hr_pos]⟩

/-! ## Probe unpacking -/

theorem fwdCPure_flag_true_of_false
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (x : JointC PQ Pt ℓ) (hfl : x.2.2 = false)
    (hfire : (fwdCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel ci? T pq' honestC c' x).2.2.2 =
      true) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    ∃ c, honestC = some c ∧ c3a = true ∧ c ≠ c' ∧ isDel = true ∧
      x.1.base.mir.safeInj 3 = false ∧
      predictReceiveWithSnapshots (fig := fig) (fs := fs) P x.1 Q w c c' = none ∧
      (fig.receive (x.2.1.st Q) c').isSome = true := by
  unfold fwdCPure at hfire
  dsimp only at hfire
  cases honestC with
  | none =>
    simp [hfl] at hfire
  | some c =>
    dsimp only at hfire
    cases hcond : (c3a && decide (c ≠ c') && isDel && !(x.1.base.mir.safeInj 3)) with
    | false =>
      rw [hcond] at hfire
      simp [hfl] at hfire
    | true =>
      rw [hcond] at hfire
      cases heval :
          predictReceiveWithSnapshots (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            (fs := lFS P.C P.codec ℓ encT idOf 25000) P x.1 Q w c c' with
      | some o =>
        rw [heval] at hfire
        cases o with
        | none => simp [hfl] at hfire
        | some tip =>
          rcases tip with ⟨t, i, pm⟩
          dsimp only at hfire
          cases hdel : (deliverPure (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
            SM.Config.h1 Q c x.2.1).1 with
          | none => simp [hdel, hfl] at hfire
          | some res =>
            cases res <;> simp [hdel, hfl] at hfire
      | none =>
        rw [heval] at hfire
        dsimp only at hfire
        rw [hfl, Bool.false_or] at hfire
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcond
        exact ⟨c, rfl, hcond.1.1.1, hcond.1.1.2, hcond.1.2, hcond.2, heval, hfire⟩

theorem fwdEvictCPure_flag_true_of_false
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (x : JointC PQ Pt ℓ) (hfl : x.2.2 = false)
    (hfire : (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel T pq' c' x).2.2.2 =
      true) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    c3a = true ∧ isDel = true ∧ x.1.base.mir.safeInj 3 = false ∧
      (fig.receive (x.2.1.st Q) c').isSome = true := by
  unfold fwdEvictCPure at hfire
  dsimp only at hfire
  cases hcond : (c3a && isDel && !(x.1.base.mir.safeInj 3)) with
  | true =>
    rw [hcond] at hfire
    rw [hfl, Bool.false_or] at hfire
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    exact ⟨hcond.1.1, hcond.1.2, hcond.2, hfire⟩
  | false =>
    rw [hcond] at hfire
    rcases fwdCPure_flag_true_of_false P ℓ Dh encPt encT idOf lam qep false Q w isDel none T pq'
      none c' x hfl hfire with ⟨_, hnone, _⟩
    cases hnone

theorem fwdEvictCPure_not_flag_true_of_evictedOnlyNoForgeAt
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [Inhabited PQ] [SampleableType PQC]
    {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (c3a : Bool)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (x₁ : JointC PQ Pt ℓ)
    (hx₁_st : x₁.2.1 = g) (hx₁_fl : x₁.2.2 = false)
    (hno_ev : EvictedOnlyNoForgeAt P decT (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) sC g Q)
    {c : Fig8C Pt} {h : SignalHeader} {body : List (BitVec 8)} {pq' : PQ} {salt : Salt} {T : Pt}
    (hmem : (w, c) ∈ sC.base.honest)
    (hsender : Party.senderOf c.1.1 = Q.other)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hrecv : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hfind : (sC.base.chains Q).findIdx? (fun ch => ch.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1))
    (hsafe : sC.base.mir.safeInj 3 = false)
    (hT : decT h.senderRatchetKey = some T) :
    (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel h.senderRatchetKey pq'
      ((sC.base.mir.epoch Q + 1, some T),
        (h.counter.toNat + 1,
          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) x₁).2.2.2 =
      false := by
  by_contra hne
  have hfire : (fwdEvictCPure P ℓ Dh encPt encT idOf lam qep c3a Q w isDel h.senderRatchetKey pq'
      ((sC.base.mir.epoch Q + 1, some T),
        (h.counter.toNat + 1,
          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) x₁).2.2.2 =
      true := Bool.eq_true_of_not_eq_false hne
  rcases fwdEvictCPure_flag_true_of_false P ℓ Dh encPt encT idOf lam qep c3a Q w isDel
    h.senderRatchetKey pq' _ x₁ hx₁_fl hfire with ⟨_, _, _, hisSome⟩
  rw [hx₁_st] at hisSome
  have hnone := hno_ev w c h body pq' salt hmem hsender hparse hrecv hfind hepoch hinw hbound
    hsafe T hT
  rw [hnone] at hisSome
  cases hisSome

theorem comp_contains_false_of_wfState_and_healedBy {St Msg C : Type}
    [DecidableEq Msg] [DecidableEq C]
    {Δ : ℕ} {s : SM.GameState St Msg C} {pos : SM.Pos}
    (hwf : SM.Thm1L17.WFState Δ s)
    (hheal : SM.healedBy s.tL Δ pos.epoch = true) :
    s.comp.contains pos = false :=
  (CompUnhealed.of_wfState hwf).comp_contains_false_of_healedBy hheal

theorem not_cellK4Doomed_b2_of_three_le {St Msg C : Type}
    {t' : ℕ} {g s : SM.GameState St Msg C}
    (ht3 : 3 ≤ t') :
    ¬ CellK4Doomed (some (t' - 3)) t' g s := by
  intro ⟨_, heq, _⟩
  injection heq with heq'
  omega

theorem firstNEProbeAt_imp_deliverHcasesAt_of_inv
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (t' i' : ℕ)
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hprobe : (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 =
      true)
    (hcell : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (ht'_le : t' ≤ (qep + 1) + 1)
    (hin_g : g.inTransit Q.other c = some r)
    (hr_pos : r.pos = ⟨Q.other, t', i'⟩)
    (horigin :
      ((Q.other, t') ∉ g.corrs ∧ (Q, t') ∉ g.corrs ∧
        ∀ P₀ e, (P₀, e) ∈ g.corrs → e ≠ t' → e + 2 ≤ t') ∨
      SM.healedBy (s_cell t' none).tL (2 + 1) t' = true ∨
      (s_cell t' none).comp.contains r.pos = false ∨
      (3 ≤ t' ∧ SM.canon t' (s_cell t' none) = some (t' - 2) ∧
        (s_cell t' (some (t' - 3))).comp.contains r.pos = false)) :
    DeliverHcasesAt Q t' r g s_cell := by
  have _ := hprobe
  have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := by
    rw [Finset.mem_range]; omega
  rcases hcell t' ht'_mem with ⟨hrel_unsh, hwf_unsh, hcell_t'⟩
  rcases mem_trans_and_epoch_eq_of_inTransit hrel_unsh hin_g hr_pos with ⟨hr_trans, hr_ep⟩
  rcases horigin with h1 | hheal3 | hcomp_u | hb2
  · exact Or.inl h1
  · have hheal3' : SM.healedBy (s_cell t' none).tL (2 + 1) r.pos.epoch = true := by
      rw [hr_ep]; exact hheal3
    have hcomp_u : (s_cell t' none).comp.contains r.pos = false :=
      comp_contains_false_of_wfState_and_healedBy hwf_unsh hheal3'
    exact deliverHcasesAt_of_unsh_comp_false_and_inv hwf_unsh hcell_t' hr_trans hr_ep hcomp_u
  · exact deliverHcasesAt_of_unsh_comp_false_and_inv hwf_unsh hcell_t' hr_trans hr_ep hcomp_u
  · exact Or.inr (Or.inr hb2)

/-! ## Five-way origin split -/

/-- 5-way origin disjunction for a record `r` in transit at target epoch `t'`, including the
`B1(t')` case. -/
def FirstNEOriginAt {St Msg C : Type}
    (Q : Party) (t' : ℕ) (r : SM.Record Msg C) (g : SM.GameState St Msg C)
    (s_cell : ℕ → Option ℕ → SM.GameState St Msg C) : Prop :=
  ((Q.other, t') ∉ g.corrs ∧ (Q, t') ∉ g.corrs ∧
    ∀ P₀ e, (P₀, e) ∈ g.corrs → e ≠ t' → e + 2 ≤ t') ∨
  SM.healedBy (s_cell t' none).tL (2 + 1) t' = true ∨
  (s_cell t' none).comp.contains r.pos = false ∨
  (3 ≤ t' ∧ SM.canon t' (s_cell t' none) = some (t' - 2) ∧
    (s_cell t' (some (t' - 3))).comp.contains r.pos = false) ∨
  (2 ≤ t' ∧ (Party.senderOf t', t') ∉ g.corrs ∧
    (s_cell t' (some (t' - 2))).comp.contains r.pos = false)

/-- Extended deliver-step case split at target epoch `t'`: `DeliverHcasesAt` or the `B1(t')`
case. -/
def DeliverHcasesAtExt {St Msg C : Type} [DecidableEq C]
    (Q : Party) (t' : ℕ) (r : SM.Record Msg C) (g : SM.GameState St Msg C)
    (s_cell : ℕ → Option ℕ → SM.GameState St Msg C) : Prop :=
  DeliverHcasesAt Q t' r g s_cell ∨
  (2 ≤ t' ∧ (Party.senderOf t', t') ∉ g.corrs ∧
    (s_cell t' (some (t' - 2))).comp.contains r.pos = false)

theorem k4Free_at_deliver_and_not_cellK4Doomed_b1_of_w4 {St Msg C : Type}
    {g : SM.GameState St Msg C} {s_cell : ℕ → Option ℕ → SM.GameState St Msg C} {t' : ℕ}
    (hw4 : ¬((Party.senderOf t', t' - 2) ∈ g.corrs ∧ (Party.senderOf t', t') ∈ g.corrs))
    (hcorr_tm2 : (Party.senderOf t', t' - 2) ∈ g.corrs) :
    (Party.senderOf t', t') ∉ g.corrs ∧
      ¬CellK4Doomed (some (t' - 2)) t' g (s_cell t' (some (t' - 2))) := by
  have hk4_g : (Party.senderOf t', t') ∉ g.corrs := fun hk4 => hw4 ⟨hcorr_tm2, hk4⟩
  exact ⟨hk4_g, CellK4Doomed.not_of_k4Free hk4_g⟩

/-- From the 5-way `FirstNEOriginAt` disjunction and `hprobe`, derive `DeliverHcasesAtExt`. -/
theorem firstNEProbeAt_imp_deliverHcasesAtExt_of_origin
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (t' i' : ℕ)
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hprobe : (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 =
      true)
    (hcell : ∀ t ∈ Finset.range ((qep + 1) + 2),
      PPrimePaperRel (s_cell t none) m' g ∧ SM.Thm1L17.WFState (2 + 1) (s_cell t none) ∧
      ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        CellK4Doomed tL t g (s_cell t tL) ∨
        (PPrimePaperRelShifted (s_cell t tL) m' g ∧
          SM.Thm1L17.WFState (cellDelta tL t) (s_cell t tL) ∧
          ShiftedLeakRel (cellShift tL t) (s_cell t none) (s_cell t tL) ∧
          CellCompRel tL t (s_cell t none) (s_cell t tL)))
    (ht'_le : t' ≤ (qep + 1) + 1) (hin_g : g.inTransit Q.other c = some r)
    (hr_pos : r.pos = ⟨Q.other, t', i'⟩) (horigin : FirstNEOriginAt Q t' r g s_cell) :
    DeliverHcasesAtExt Q t' r g s_cell := by
  rcases horigin with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (firstNEProbeAt_imp_deliverHcasesAt_of_inv P ℓ Dh encPt encT decT idOf lam qep
      Q w c r t' i' hprobe hcell ht'_le hin_g hr_pos (Or.inl h1))
  · exact Or.inl (firstNEProbeAt_imp_deliverHcasesAt_of_inv P ℓ Dh encPt encT decT idOf lam qep
      Q w c r t' i' hprobe hcell ht'_le hin_g hr_pos (Or.inr (Or.inl h2)))
  · exact Or.inl (firstNEProbeAt_imp_deliverHcasesAt_of_inv P ℓ Dh encPt encT decT idOf lam qep
      Q w c r t' i' hprobe hcell ht'_le hin_g hr_pos (Or.inr (Or.inr (Or.inl h3))))
  · exact Or.inl (firstNEProbeAt_imp_deliverHcasesAt_of_inv P ℓ Dh encPt encT decT idOf lam qep
      Q w c r t' i' hprobe hcell ht'_le hin_g hr_pos (Or.inr (Or.inr (Or.inr h4))))
  · exact Or.inr h5

/-- Per-record in-transit origin invariant across all cell families `t < (qep + 1) + 2`. -/
def FirstNEInTransOriginInv {PQ St Msg C : Type} (qep : ℕ)
    (snaps : List (Party × ℕ × GhostState PQ))
    (g : SM.GameState St Msg C) (s_cell : ℕ → Option ℕ → SM.GameState St Msg C) : Prop :=
  ∀ t ∈ Finset.range ((qep + 1) + 2),
    ∀ r ∈ (s_cell t none).trans, r.pos.epoch = t →
      (∃ e, (Party.receiverOf t, e) ∈ g.corrs ∧ ¬(e + 3 ≤ t)) ∨
      (∃ e, (Party.senderOf t, e) ∈ g.corrs ∧ t = e + 1) ∨
      (s_cell t none).comp.contains r.pos = false ∨
      (3 ≤ t ∧ SM.canon t (s_cell t none) = some (t - 2) ∧
        (s_cell t (some (t - 3))).comp.contains r.pos = false) ∨
      (2 ≤ t ∧ (Party.senderOf t, t - 2) ∈ g.corrs ∧
        (s_cell t (some (t - 2))).comp.contains r.pos = false) ∨
      ((Party.senderOf t, t) ∈ g.corrs ∧
        ∃ g₀ sc, (Party.senderOf t, t, g₀) ∈ snaps ∧
          g₀.session.senderChain = some sc ∧
          sc.chainKey.index.toNat < r.pos.idx)

theorem firstNEInTransOriginInv_of_trans_nil {PQ St Msg C : Type} (qep : ℕ)
    (snaps : List (Party × ℕ × GhostState PQ))
    (g : SM.GameState St Msg C) (s_cell : ℕ → Option ℕ → SM.GameState St Msg C)
    (hempty : ∀ t ∈ Finset.range ((qep + 1) + 2), (s_cell t none).trans = []) :
    FirstNEInTransOriginInv qep snaps g s_cell := by
  intro t ht r hr; rw [hempty t ht] at hr; nomatch hr

theorem firstNEInTransOriginInv_init_b {PQ Key St Msg Coins C : Type}
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ)
    (snaps : List (Party × ℕ × GhostState PQ)) (k : Key) (b : Bool) :
    FirstNEInTransOriginInv qep snaps (SM.initState sm k b) (fun _ _ => SM.initState sm k b) :=
  firstNEInTransOriginInv_of_trans_nil qep snaps (SM.initState sm k b)
    (fun _ _ => SM.initState sm k b) (fun _ _ => rfl)

end CryptoVerification.LibsignalSession.HeadlineV1

