/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Eager
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Eager
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Tracker-halted base definitions and combinators

Defines the tracker state isomorphism, the post-latch send-dropping adversary `dropSendsAdv`, the
eager tracker-halted simulator runners and joint invariant `SimInvCXTrack`, and step combinators for
`CloseByStateCTrack`.
-/

set_option autoImplicit false

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open scoped ENNReal
open OracleComp OracleSpec
open Computational.Proofs.SpecLemmas.Session
open CryptoGames
open CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.CKA CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoGames.CBC
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes)
open CryptoVerification.SpqrV1Sync.InSync (Seed)
open CryptoVerification.SpqrV1Sync.Braid (EncRand)
open CryptoVerification.E2E (liftStateT)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Tracker state isomorphism -/

def toRefTrack {F : ShaCompress}
    (tr : KemFailTrackBridge.KemFailTrackState F) : KemFailTrackState F :=
  { e := tr.e, auth := tr.auth, c := tr.c, st := tr.st,
    sentB := tr.sentB, sendCtr := tr.sendCtr, cand := tr.cand }

def ofRefTrack {F : ShaCompress}
    (tr : KemFailTrackState F) : KemFailTrackBridge.KemFailTrackState F :=
  { e := tr.e, auth := tr.auth, c := tr.c, st := tr.st,
    sentB := tr.sentB, sendCtr := tr.sendCtr, cand := tr.cand }

@[simp] theorem toRefTrack_ofRefTrack {F : ShaCompress} (tr : KemFailTrackState F) :
    toRefTrack (ofRefTrack tr) = tr := by
  cases tr; rfl

@[simp] theorem ofRefTrack_toRefTrack {F : ShaCompress}
    (tr : KemFailTrackBridge.KemFailTrackState F) :
    ofRefTrack (toRefTrack tr) = tr := by
  cases tr; rfl

@[simp] theorem ofRefTrack_cand {F : ShaCompress} (tr : KemFailTrackState F) :
    (ofRefTrack tr).cand = tr.cand := rfl

@[simp] theorem toRefTrack_cand {F : ShaCompress}
    (tr : KemFailTrackBridge.KemFailTrackState F) :
    (toRefTrack tr).cand = tr.cand := rfl

theorem ofRefTrack_init (F : ShaCompress) (k : BitVec 256) :
    ofRefTrack (initKemFailTrack F k) = KemFailTrackBridge.initKemFailTrack F k := rfl

theorem ofRefTrack_stepSend (F : ShaCompress) (K : MlKem) (tr : KemFailTrackState F)
    (Q : Party) (r : BitVec 512) :
    ofRefTrack (stepKemFailSend F K tr Q r) =
      KemFailTrackBridge.stepKemFailSend F K (ofRefTrack tr) Q r := by
  rcases tr with ⟨e, auth, c, st, sentB, sendCtr, cand⟩
  unfold stepKemFailSend KemFailTrackBridge.stepKemFailSend ofRefTrack
  dsimp only
  have hbp : kemBraidParty Q = KemFailTrackBridge.kemBraidParty Q := by cases Q <;> rfl
  rw [hbp]
  cases (st Q).send K (coinBytes r) with
  | error _ => rfl
  | ok p => rcases p with ⟨out, _⟩; rfl

theorem ofRefTrack_stepDeliver (F : ShaCompress) (K : MlKem) (tr : KemFailTrackState F)
    (Q : Party) (j : ℕ) :
    ofRefTrack (stepKemFailDeliver F K tr Q j) =
      KemFailTrackBridge.stepKemFailDeliver F K (ofRefTrack tr) Q j := by
  rcases tr with ⟨e, auth, c, st, sentB, sendCtr, cand⟩
  unfold stepKemFailDeliver KemFailTrackBridge.stepKemFailDeliver ofRefTrack
  dsimp only
  cases h : sentB[j]? with
  | none => rfl
  | some mb =>
    rcases mb with ⟨m, _⟩
    dsimp only
    cases (st Q).recv K m with
    | error _ => rfl
    | ok out =>
      dsimp only
      split
      · cases c <;> rfl
      · rfl

theorem bridge_stepKemFailSend_cand_sticky {F : ShaCompress} (K : MlKem)
    (tr : KemFailTrackBridge.KemFailTrackState F) (Q : Party) (rq : BitVec 512)
    {p : Seed × EncRand} (hc : tr.cand = some p) :
    (KemFailTrackBridge.stepKemFailSend F K tr Q rq).cand = some p := by
  have h1 := stepKemFailSend_cand_sticky K (toRefTrack tr) Q rq (by simpa using hc)
  have h2 := congrArg (·.cand) (ofRefTrack_stepSend F K (toRefTrack tr) Q rq)
  simpa [ofRefTrack_toRefTrack] using h2.symm.trans h1

theorem bridge_stepKemFailDeliver_cand {F : ShaCompress} (K : MlKem)
    (tr : KemFailTrackBridge.KemFailTrackState F) (Q : Party) (j : ℕ) :
    (KemFailTrackBridge.stepKemFailDeliver F K tr Q j).cand = tr.cand := by
  have h1 := stepKemFailDeliver_cand K (toRefTrack tr) Q j
  have h2 := congrArg (·.cand) (ofRefTrack_stepDeliver F K (toRefTrack tr) Q j)
  simpa [ofRefTrack_toRefTrack] using h2.symm.trans h1

/-! ## Honest wires and post-latch adversary -/

theorem honestWires_reverse_findIdx_eq {α β : Type}
    (f : α → β) (p : β → Bool) (xs : List α) :
    (xs.map f).reverse.findIdx? p = xs.reverse.findIdx? (fun x => p (f x)) := by
  rw [← List.map_reverse, List.findIdx?_map]
  rfl

def honestWiresOf {Pt : Type} (honest : List (List (BitVec 8) × Fig8C Pt)) :
    List (List (BitVec 8) × Party) :=
  honest.map fun wc => (wc.1, Party.senderOf wc.2.1.1)

theorem honestWiresOf_reverse_findIdx_eq {Pt : Type}
    (honest : List (List (BitVec 8) × Fig8C Pt)) (Q : Party) (w : List (BitVec 8)) :
    (honestWiresOf honest).reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) =
      honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) :=
  honestWires_reverse_findIdx_eq
    (fun (wc : List (BitVec 8) × Fig8C Pt) => (wc.1, Party.senderOf wc.2.1.1))
    (fun wp => wp.1 == w && wp.2 == Q.other) honest

def dropSendsImpl (PQ PQC : Type) (ℓ : ℕ) :
    QueryImpl (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :=
  fun t => match t with
  | .inl u =>
    liftM (OracleSpec.query
      (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inl u))
  | .inr (.inl (.inl (.inl (.inl _)))) => pure none
  | .inr (.inl (.inl (.inl (.inr _)))) => pure none
  | .inr (.inl (.inl (.inr qw))) =>
    liftM (OracleSpec.query
      (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (.inr (.inl (.inl (.inr qw)))))
  | .inr (.inl (.inr qw)) =>
    liftM (OracleSpec.query
      (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (.inr (.inl (.inr qw))))
  | .inr (.inr Q) =>
    liftM (OracleSpec.query
      (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (.inr (.inr Q)))

def dropSendsAdv {PQ PQC α : Type} {ℓ : ℕ}
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α) :
    SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α :=
  simulateQ (dropSendsImpl PQ PQC ℓ) oa

theorem isQueryBoundP_dropSendsAdv {PQ PQC α : Type} {ℓ r : ℕ}
    {p : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (hq : oa.IsQueryBoundP p r) :
    (dropSendsAdv oa).IsQueryBoundP p r := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure a =>
    simp only [dropSendsAdv, simulateQ_pure]
    exact hq
  | query_bind t cont ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
    have hlift {β : Type}
        (m : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) β) :
        (liftM m : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) β) = m := rfl
    rcases t with u | (((⟨Q, m, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q <;>
      simp only [dropSendsAdv, simulateQ_query_bind, dropSendsImpl,
        OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM_pure, hlift]
    · rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨hq.1, fun ans => ih ans (hq.2 ans)⟩
    · rw [pure_bind]
      exact (ih none (hq.2 none)).mono (by split <;> omega)
    · rw [pure_bind]
      exact (ih none (hq.2 none)).mono (by split <;> omega)
    · rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨hq.1, fun ans => ih ans (hq.2 ans)⟩
    · rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨hq.1, fun ans => ih ans (hq.2 ans)⟩
    · rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨hq.1, fun ans => ih ans (hq.2 ans)⟩

/-! ## Tracker-halted runners and `CloseByStateCTrack` -/

def eps0EventTrackHalted {PQ Pt : Type} [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (encPt : Pt → List (BitVec 8)) (lam : Pt) (onImage : List (BitVec 8) → Bool) (qep : ℕ)
    (A : LibAdv PQ (BitVec 512) ℓ) : ProbComp Bool := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let ((_, s), _) ← KemFailTrackBridge.runRTrackHalted
    KemFailTrackBridge.libsignalSessionPqrOf P.C.F K
    (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher onImage) b A
  return (decide (0 < s.maxAcc .A 0) || s.win) && !(s.corrs.contains (.B, 0))

def simCNoneWinEventTrackHalted {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, s) ← SM.run sm 3 (qep + 1) SM.Config.h1 b
    (runLibsignalToModularSchemeSimTrackHalted P K Dh encPt encT decT idOf lam qep A)
  return s.win

def stepRTrack {Key St Msg RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType RCoins] (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (SM.spec St Msg (BitVec 512) C).Domain) (s : GameState St Msg C)
    (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    ProbComp (((SM.spec St Msg (BitVec 512) C).Range q × GameState St Msg C) ×
      KemFailTrackBridge.KemFailSessionTrack F C) :=
  ((KemFailTrackBridge.oracleImplRTrackHalted F K sm Δ qep cfg q).run s).run stTr

def runRContTrack {Key St Msg RCoins C α : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType RCoins] (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (oa : SM.AdversaryComp St Msg (BitVec 512) C α) (s : GameState St Msg C)
    (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    ProbComp ((α × GameState St Msg C) × KemFailTrackBridge.KemFailSessionTrack F C) :=
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (KemFailTrackBridge.KemFailSessionTrack F C) ProbComp)) +
    KemFailTrackBridge.oracleImplRTrackHalted F K sm Δ qep cfg
  ((simulateQ impl oa).run s).run stTr

def stepSimCEagerSendTrack {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (_decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (_k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    ProbComp (Option (List (BitVec 8)) ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256))) :=
  if !x.2.1.win && inReceiveOnlyEpoch x.1.base.mir Q &&
      !(x.1.base.stopped || x.1.base.mir.win || !(SM.noBobSendInEpoch0 x.1.base.mir Q)) then
    match x.1.base.mir.epMgmt 3 qep Q r.isSome with
    | some s₁ =>
      if chal.isSome && !(s₁.safeCh 3 Q) then
        pure (none, ((x, tr), ec))
      else
        (match r with | some rq => pure rq | none => ($ᵗ BitVec 512 : ProbComp (BitVec 512))) >>= fun rq =>
        let tr' := stepKemFailSend P.C.F K tr Q rq
        if tr'.cand.isSome then
          pure (none, ((x, { tr with cand := tr'.cand }), ec))
        else
          let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r.isSome s₁ rq (ec Q) x.sim
          let tr'' := if res.1.isSome then tr' else { tr with cand := tr'.cand }
          updateAllEagerCoins x.1.base.mir res.2.1.mir (· == Q) ec >>= fun ec' =>
          pure (res.1, (((cxSend P Dh encPt encT idOf lam Q x.1 res.2.1 res.1, res.2.2, x.2.2), tr''), ec'))
    | none =>
      pure (none, ((x, tr), ec))
  else
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ((simulateQ (fig8ImplH1 fig (qep + 1))
        ((simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run (x.1, tr))).run x.2.1) >>= fun z =>
    let x' : JointC PQ Pt ℓ := (z.1.2.1, z.2, x.2.2)
    let tr' := z.1.2.2
    if z.1.1.isNone then
      pure (z.1.1, ((x', tr'), ec))
    else
      updateAllEagerCoins x.1.base.mir x'.1.base.mir (fun _ => false) ec >>= fun ec' =>
      pure (z.1.1, ((x', tr'), ec'))

def stepSimCEagerDeliverTrack {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    ProbComp (Option (RecvResult (Plain ℓ)) ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256))) :=
  let j? := x.1.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
  stepSimCEagerDeliver P ℓ Dh encPt encT decT idOf lam qep k Q w x ec >>= fun res =>
    let tr' := match res.1, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    pure (res.1, ((res.2.1, tr'), res.2.2))

def stepSimCEagerTrack {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    ProbComp ((SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256))) :=
  match q with
  | .inl (.inl (.inl (.inl (Q, m₀, r)))) =>
    stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ none r x tr ec
  | .inl (.inl (.inl (.inr (Q, m₀, m₁, r)))) =>
    stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ (some m₁) r x tr ec
  | .inl (.inl (.inr (Q, w))) =>
    stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep k Q w x tr ec
  | .inl (.inr (Q, w)) =>
    stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec >>= fun res =>
      pure (res.1, ((res.2.1, tr), res.2.2))
  | .inr Q =>
    stepSimCEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q x ec >>= fun res =>
      pure (res.1, ((res.2.1, tr), res.2.2))

def simEagerImplCTrack {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ) :
    QueryImpl (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      (StateT ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)) ProbComp) :=
  fun q => StateT.mk fun ⟨⟨x, tr⟩, ec⟩ =>
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q x tr ec

def runSimCEagerTrack {PQ Pt α : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    ProbComp (α × ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256))) :=
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)) ProbComp) +
    simEagerImplCTrack P K ℓ Dh encPt encT decT idOf lam qep k
  (simulateQ impl oa).run ((x, tr), ec)

def runWinAtCTrack {PQ Pt α : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool) (idx : ℕ) : ProbComp Bool :=
  match idx with
  | 0 =>
    runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none oa x tr ec >>=
      fun r => pure r.2.1.1.2.1.win
  | j + 1 =>
    if j < x.1.base.amb then
      pure (winBefore j)
    else
      runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some j) oa x tr ec >>=
        fun r => pure (r.2.1.1.1.base.stopped && r.2.1.1.2.1.win)

def runHidCTrack {PQ Pt α : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    ProbComp Bool :=
  runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none oa x tr ec >>=
    fun r => pure r.2.1.1.2.2

structure SimInvCXTrack {PQ Pt : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (Inv : ℕ → PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256) : Prop where
  hcx : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp
  htr : stTrR.1 = ofRefTrack trC
  hhw : stTrR.2 = honestWiresOf sC.base.honest

def CloseByStateCTrack {PQ Pt α : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt]
    [Inhabited PQ] (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (δ : ℝ≥0∞) (post : α → Bool)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool) (ec : Party → BitVec 256) (winBefore : ℕ → Bool) : Prop :=
  CloseByRefinesH (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir))
    (runRContTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) oa s_R stTrR >>=
      fun z => pure (post z.1.1 || z.1.2.win))
    (runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none oa (sC, s_fig8, fl) trC ec >>=
      fun z => pure (post z.1 || z.2.1.1.2.1.win))
    (runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep oa (sC, s_fig8, fl) trC ec winBefore)
    (runRContTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) oa s_R stTrR >>=
      fun z => pure ((decide (0 < z.1.2.maxAcc .A 0) || z.1.2.win) && !(z.1.2.corrs.contains (.B, 0))))
    (runHidCTrack P K ℓ Dh encPt encT decT idOf lam qep oa (sC, s_fig8, fl) trC ec)

/-! ## Step combinators -/

section Combinators

variable {Pt PQ : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] {ℓ : ℕ}

theorem simulateQ_fig8ImplH1_liftM_bind {α β : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qep : ℕ) (c0 : ProbComp α) (k : α → Fig8Comp Pt ℓ β)
    (s_f : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) :
    (simulateQ (fig8ImplH1 fig (qep + 1)) ((liftM c0 : Fig8Comp Pt ℓ α) >>= k)).run s_f =
      (c0 >>= fun a => (simulateQ (fig8ImplH1 fig (qep + 1)) (k a)).run s_f) := by
  induction c0 using OracleComp.inductionOn with
  | pure a =>
    change (simulateQ (fig8ImplH1 fig (qep + 1)) (pure a >>= k)).run s_f = _
    rw [pure_bind, pure_bind]
  | query_bind u cont ih =>
    have hq : (liftM (liftM (OracleSpec.query (spec := unifSpec) u) >>= cont) : Fig8Comp Pt ℓ α) =
        liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
          (Sum.inl u)) >>= fun y => liftM (cont y) := rfl
    rw [hq, bind_assoc]
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
      id_eq, StateT.run_bind]
    have h1 :
        (liftM ((fig8ImplH1 fig (qep + 1)) (Sum.inl u)) :
          StateT _ ProbComp (unifSpec.Range u)).run s_f =
        ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
          pure (y, s_f)) := rfl
    rw [h1]
    simp only [bind_assoc, pure_bind]
    congr 1; funext y
    exact ih y

theorem runRContTrack_pure {Key St Msg RCoins C α : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType RCoins] (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (a : α) (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    runRContTrack F K sm Δ qep cfg (pure a) s stTr = pure ((a, s), stTr) := by
  simp [runRContTrack]

theorem runRContTrack_inl_bind {Key St Msg RCoins C α : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType RCoins] (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u → SM.AdversaryComp St Msg (BitVec 512) C α)
    (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    runRContTrack F K sm Δ qep cfg
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C) (.inl u)) >>= cont)
        s stTr =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        runRContTrack F K sm Δ qep cfg (cont y) s stTr := by
  simp only [runRContTrack, simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
    id_eq, StateT.run_bind]
  have h1 :
      ((liftM (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (GameState St Msg C) (StateT (KemFailTrackBridge.KemFailSessionTrack F C) ProbComp)) +
        KemFailTrackBridge.oracleImplRTrackHalted F K sm Δ qep cfg) (.inl u)) :
        StateT _ (StateT _ ProbComp) (unifSpec.Range u)).run s).run stTr =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        pure ((y, s), stTr)) := by
    simp [StateT.run_lift, bind_assoc]
  rw [h1]
  simp only [bind_assoc, pure_bind]

theorem runRContTrack_inr_bind {Key St Msg RCoins C α : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType RCoins] (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (SM.spec St Msg (BitVec 512) C).Domain)
    (cont : (SM.spec St Msg (BitVec 512) C).Range q → SM.AdversaryComp St Msg (BitVec 512) C α)
    (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    runRContTrack F K sm Δ qep cfg
        (liftM (OracleSpec.query (spec := unifSpec + SM.spec St Msg (BitVec 512) C) (.inr q)) >>= cont)
        s stTr =
      stepRTrack F K sm Δ qep cfg q s stTr >>= fun r =>
        runRContTrack F K sm Δ qep cfg (cont r.1.1) r.1.2 r.2 := by
  simp only [runRContTrack, stepRTrack, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  rfl

theorem runSimCEagerTrack_pure {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (a : α) (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (pure a) x tr ec =
      pure (a, ((x, tr), ec)) := by
  simp [runSimCEagerTrack]

theorem runSimCEagerTrack_inl_bind {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inl u)) >>= cont) x tr ec =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (cont y) x tr ec := by
  simp only [runSimCEagerTrack, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  have h1 :
      (liftM ((QueryImpl.liftTarget
        (StateT ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)) ProbComp)
        (QueryImpl.ofLift unifSpec ProbComp) +
        simEagerImplCTrack P K ℓ Dh encPt encT decT idOf lam qep k) (.inl u)) :
        StateT _ ProbComp (unifSpec.Range u)).run ((x, tr), ec) =
      ((liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        pure (y, ((x, tr), ec))) := rfl
  rw [h1]
  simp only [bind_assoc, pure_bind]

theorem runSimCEagerTrack_inr_bind {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inr q)) >>= cont) x tr ec =
      stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q x tr ec >>= fun r =>
        runSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k (cont r.1) r.2.1.1 r.2.1.2 r.2.2 := by
  simp only [runSimCEagerTrack, simEagerImplCTrack, simulateQ_query_bind, OracleQuery.input_query,
    OracleQuery.cont_query, id_eq, StateT.run_bind]
  rfl

theorem stepSimCEagerTrack_some_eq_none_of_not_div (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep idx : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hidx : idx ≠ x.1.base.amb) :
    stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some idx) q x tr ec =
      stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q x tr ec := by
  have hbase := stepSimCEager_some_eq_none_of_not_div P ℓ Dh encPt encT decT idOf lam qep idx q x ec hidx
  rcases q with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · change stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep (some idx) Q w x tr ec =
      stepSimCEagerDeliverTrack P K ℓ Dh encPt encT decT idOf lam qep none Q w x tr ec
    unfold stepSimCEagerDeliverTrack
    change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) (.inl (.inl (.inr (Q, w)))) x ec >>= _) =
      (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inl (.inr (Q, w)))) x ec >>= _)
    rw [hbase]
  · change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) (.inl (.inr (Q, w))) x ec >>= _) =
      (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inl (.inr (Q, w))) x ec >>= _)
    rw [hbase]
  · change (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) (.inr Q) x ec >>= _) =
      (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none (.inr Q) x ec >>= _)
    rw [hbase]

theorem evalDist_runWinAtCTrack_inl_bind {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inl u)) >>= cont) x tr ec winBefore idx] =
      𝒟[(liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont y) x tr ec winBefore idx] := by
  unfold runWinAtCTrack
  cases idx with
  | zero =>
    simp only [runSimCEagerTrack_inl_bind, bind_assoc]
  | succ j =>
    dsimp only
    split
    · exact (OracleComp.evalDist_bind_const _ _).symm
    · simp only [runSimCEagerTrack_inl_bind, bind_assoc]

theorem runHidCTrack_inl_bind {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (u : unifSpec.Domain)
    (cont : unifSpec.Range u →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256) :
    runHidCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inl u)) >>= cont) x tr ec =
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) >>= fun y =>
        runHidCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont y) x tr ec := by
  unfold runHidCTrack
  simp only [runSimCEagerTrack_inl_bind, bind_assoc]

theorem evalDist_runWinAtCTrack_inr_same_amb_bind {α γ : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (N : ProbComp γ)
    (f : γ → (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hamb : ∀ y, (f y).2.1.1.1.base.amb = x.1.base.amb)
    (hstep : ∀ idx, ¬ idx < x.1.base.amb →
      stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some idx) q x tr ec =
        N >>= fun y => pure (f y))
    (winBefore : ℕ → Bool) (idx : ℕ) :
    𝒟[runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep
        (liftM (OracleSpec.query
          (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
          (.inr q)) >>= cont) x tr ec winBefore idx] =
      𝒟[N >>= fun y =>
        runWinAtCTrack P K ℓ Dh encPt encT decT idOf lam qep (cont (f y).1)
          (f y).2.1.1 (f y).2.1.2 (f y).2.2 winBefore idx] := by
  unfold runWinAtCTrack
  cases idx with
  | zero =>
    have hstep_none : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q x tr ec =
        N >>= fun y => pure (f y) := by
      rw [← stepSimCEagerTrack_some_eq_none_of_not_div P K ℓ Dh encPt encT decT idOf lam qep
            (x.1.base.amb + 1) q x tr ec (by omega)]
      exact hstep (x.1.base.amb + 1) (by omega)
    rw [runSimCEagerTrack_inr_bind, hstep_none]
    simp only [bind_assoc, pure_bind]
  | succ j =>
    dsimp only
    simp only [hamb]
    split
    · exact (OracleComp.evalDist_bind_const _ _).symm
    · rename_i hnot
      rw [runSimCEagerTrack_inr_bind, hstep j hnot]
      simp only [bind_assoc, pure_bind]

theorem stepSimCEagerSendTrack_preserve_fl (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512))
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hfl : x.2.2 = true) :
    ∀ z ∈ support (stepSimCEagerSendTrack P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ chal r x tr ec),
      z.2.1.1.2.2 = true := by
  intro z hz
  unfold stepSimCEagerSendTrack at hz
  split at hz
  · cases hep : x.1.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      rw [hep] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hfl
    | some s₁ =>
      rw [hep] at hz
      dsimp only at hz
      split at hz
      · simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hfl
      · simp only [MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨rq, _, hz⟩
        split at hz
        · simp only [support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hfl
        · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
          rcases hz with ⟨_, _, rfl⟩
          exact hfl
  · simp only [MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨z₀, _, hz⟩
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hfl
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨_, _, rfl⟩
      exact hfl

theorem stepSimCEagerTrack_preserve_fl (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hfl : x.2.2 = true) :
    ∀ z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep k q x tr ec),
      z.2.1.1.2.2 = true := by
  intro z hz
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact stepSimCEagerSendTrack_preserve_fl P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ none r'
      x tr ec hfl z hz
  · exact stepSimCEagerSendTrack_preserve_fl P K ℓ Dh encPt encT decT idOf lam qep k Q m₀ (some m₁) r'
      x tr ec hfl z hz
  · simp only [stepSimCEagerTrack, stepSimCEagerDeliverTrack, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_fl P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inl (.inr (Q, w)))) x ec hfl res hres
  · simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_fl P ℓ Dh encPt encT decT idOf lam qep k
      (.inl (.inr (Q, w))) x ec hfl res hres
  · simp only [stepSimCEagerTrack, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimCEager_preserve_fl P ℓ Dh encPt encT decT idOf lam qep k
      (.inr Q) x ec hfl res hres

theorem evalDist_runHidCTrack_of_fl_true {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (tr : KemFailTrackState P.C.F) (ec : Party → BitVec 256)
    (hfl : x.2.2 = true) :
    𝒟[runHidCTrack P K ℓ Dh encPt encT decT idOf lam qep oa x tr ec] {true} = 1 := by
  unfold runHidCTrack runSimCEagerTrack
  refine Construction.AuthL11.evalDist_bind_eq_one _ _ fun z hz => ?_
  have h := simulateQ_run_preserve (simEagerImplCTrack P K ℓ Dh encPt encT decT idOf lam qep none)
    (fun s => s.1.1.2.2 = true)
    (fun q s hs z hz => stepSimCEagerTrack_preserve_fl P K ℓ Dh encPt encT decT idOf lam qep none
      q s.1.1 s.1.2 s.2 hs z hz) oa ((x, tr), ec) hfl z hz
  simp [h]

theorem closeByStateCTrack_of_fl_true {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post oa s_R stTrR sC trC s_fig8
      true ec winBefore :=
  closeByRefinesH_of_hid_eq_one
    (evalDist_runHidCTrack_of_fl_true P K ℓ Dh encPt encT decT idOf lam qep oa _ trC ec rfl)

theorem closeByStateCTrack_inr_of_fl_step {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hset : ∀ z ∈ support (stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm
      (sC, s_fig8, fl) trC ec), z.2.1.1.2.2 = true) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  refine closeByRefinesH_of_hid_eq_one ?_
  unfold runHidCTrack
  rw [runSimCEagerTrack_inr_bind, bind_assoc]
  refine Construction.AuthL11.evalDist_bind_eq_one _ _ fun z hz => ?_
  have h := evalDist_runHidCTrack_of_fl_true P K ℓ Dh encPt encT decT idOf lam qep (cont z.1)
    z.2.1.1 z.2.1.2 z.2.2 (hset z hz)
  simpa [runHidCTrack] using h

theorem stepRTrack_deliver_eq {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (Q : Party) (w : C)
    (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    stepRTrack F K sm Δ qep cfg (.inl (.inl (.inr (Q, w)))) s stTr =
      stepR sm Δ qep cfg (.inl (.inl (.inr (Q, w)))) s >>= fun res_s =>
        let j? := stTr.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
        let tr' := match res_s.1, j? with
          | some (.accepted _ _ _), some j =>
            KemFailTrackBridge.stepKemFailDeliver F K stTr.1 Q j
          | _, _ => stTr.1
        pure (res_s, (tr', stTr.2)) := by
  change ((KemFailTrackBridge.deliverRTrackHalted F K sm cfg (Q, w)).run s).run stTr = _
  unfold KemFailTrackBridge.deliverRTrackHalted
  rcases stTr with ⟨tr, hw⟩
  have hls : ∀ {σ τ α : Type} (x : StateT σ ProbComp α) (s₀ : σ) (t₀ : τ),
      ((liftStateT (n := StateT τ ProbComp) x).run s₀).run t₀ =
        (x.run s₀ >>= fun a => pure (a, t₀)) := fun _ _ _ => rfl
  have hmod : ∀ {σ : Type} (f : σ → σ) (t₀ : σ),
      (modify f : StateT σ ProbComp PUnit).run t₀ = pure ((), f t₀) := fun _ _ => rfl
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, hls, hmod,
    StateT.run_pure, pure_bind, bind_assoc]
  congr 1; funext res_s
  rcases res_s with ⟨res, s'⟩
  cases res with
  | none => simp [StateT.run_bind, StateT.run_pure]
  | some rr =>
    cases rr with
    | rejected => simp [StateT.run_bind, StateT.run_pure]
    | accepted _ _ _ =>
      cases hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) <;>
        simp [StateT.run_bind, StateT.run_lift, hmod, StateT.run_pure]

theorem stepRTrack_inject_eq {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (Q : Party) (w : C)
    (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    stepRTrack F K sm Δ qep cfg (.inl (.inr (Q, w))) s stTr =
      stepR sm Δ qep cfg (.inl (.inr (Q, w))) s >>= fun res_s => pure (res_s, stTr) := rfl

theorem stepRTrack_corr_eq {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (Q : Party)
    (s : GameState St Msg C) (stTr : KemFailTrackBridge.KemFailSessionTrack F C) :
    stepRTrack F K sm Δ qep cfg (.inr Q) s stTr =
      stepR sm Δ qep cfg (.inr Q) s >>= fun res_s => pure (res_s, stTr) := rfl

theorem stepRTrack_D0_eq_of_simInvC (P : Params PQ (BitVec 512)) (K : MlKem) (Inv : PQ → Prop)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hq : ∀ Qw, q_sm ≠ .inl (.inr Qw)) :
    stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR := by
  have hbase := stepR_D0_eq_of_simInvC P Inv ℓ Dh encPt encT decT lam qep q r x₀ q_sm s_R s s_fig8
    ec winBefore epExp hinv hq
  rcases q_sm with ((((⟨Q, m₀, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · rfl
  · rfl
  · rw [stepRTrack_deliver_eq, stepRTrack_deliver_eq, hbase]
  · exact False.elim (hq (Q, w) rfl)
  · rw [stepRTrack_corr_eq, stepRTrack_corr_eq, hbase]

theorem closeByStateCTrack_pure {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (a : α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (hwin_R : s_R.win = false) (hwin_fig8 : s_fig8.win = false) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (pure a) s_R stTrR sC trC
      s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  rw [runRContTrack_pure, runSimCEagerTrack_pure]
  simp only [pure_bind, hwin_R, hwin_fig8]
  exact closeByRefinesH_of_eq (q + 1) rfl

theorem closeByStateCTrack_inl_bind {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool) (u : unifSpec.Domain)
    (cont : unifSpec.Range u →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (h : ∀ y, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont y) s_R stTrR
      sC trC s_fig8 fl ec winBefore) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inl u)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir))
      (liftM (OracleSpec.query (spec := unifSpec) u) : ProbComp _) h)
  · simp only [runRContTrack_inl_bind, bind_assoc]
  · simp only [runSimCEagerTrack_inl_bind, bind_assoc]
  · intro idx _
    exact evalDist_runWinAtCTrack_inl_bind P K ℓ Dh encPt encT decT idOf lam qep u cont
      (sC, s_fig8, fl) trC ec winBefore idx
  · simp only [runRContTrack_inl_bind, bind_assoc]
  · rw [runHidCTrack_inl_bind]

theorem closeByStateCTrack_inr_same_amb_bind {α γ : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ)
    (fR : γ → ((SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) ×
      KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (fS : γ → (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hans : ∀ y, (fR y).1.1 = (fS y).1)
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      N >>= fun y => pure (fR y))
    (hstepSim : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm
        (sC, s_fig8, fl) trC ec =
      N >>= fun y => pure (fS y))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm
        (sC, s_fig8, fl) trC ec =
        N >>= fun y => pure (fS y))
    (hamb : ∀ y, (fS y).2.1.1.1.base.amb = sC.base.amb)
    (hrem : ∀ y, remWin qep (fS y).2.1.1.1.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ y, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS y).1) (fR y).1.2 (fR y).2 (fS y).2.1.1.1 (fS y).2.1.2 (fS y).2.1.1.2.1
      (fS y).2.1.1.2.2 (fS y).2.2 winBefore) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun y => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem y)) (hcont y)))
  · simp only [runRContTrack_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimCEagerTrack_inr_bind, hstepSim, bind_assoc, pure_bind]
  · intro idx _
    exact evalDist_runWinAtCTrack_inr_same_amb_bind P K ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (sC, s_fig8, fl) trC ec N fS hamb hstepWin winBefore idx
  · simp only [runRContTrack_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSim, bind_assoc, pure_bind]

theorem closeByStateCTrack_inr_same_amb_pure {α : Type} (P : Params PQ (BitVec 512)) (K : MlKem)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC trC' : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm)
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      pure ((ans, s_R'), stTrR'))
    (hstepSim : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm
        (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm
        (sC, s_fig8, fl) trC ec =
        pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hamb : sC'.base.amb = sC.base.amb)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans)
      s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore :=
  closeByStateCTrack_inr_same_amb_bind P K ℓ Dh encPt encT decT idOf lam qep q δ post q_sm cont
    s_R stTrR sC trC s_fig8 fl ec winBefore (pure ())
    (fun _ => ((ans, s_R'), stTrR')) (fun _ => (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (fun _ => rfl) hD0 (by rw [hstepR]; simp) (by rw [hstepSim]; simp)
    (fun idx h => by rw [hstepWin idx h]; simp) (fun _ => hamb) (fun _ => hrem) (fun _ => hcont)

theorem closeByStateCTrack_inr_same_amb_bind_const_R {α γ : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞) (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR stTrR' : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC trC' : KemFailTrackState P.C.F)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl fl' : Bool) (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm)
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      N >>= fun _ => pure ((ans, s_R'), stTrR'))
    (hstepSim : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm
        (sC, s_fig8, fl) trC ec =
      pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm
        (sC, s_fig8, fl) trC ec =
        pure (ans, (((sC', s_fig8', fl'), trC'), ec')))
    (hamb : sC'.base.amb = sC.base.amb)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont ans) s_R' stTrR' sC' trC' s_fig8' fl' ec' winBefore) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) hcont)
  · simp only [runRContTrack_inr_bind, hstepR, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _
  · simp only [runSimCEagerTrack_inr_bind, hstepSim, pure_bind]
  · intro idx _
    have h := evalDist_runWinAtCTrack_inr_same_amb_bind P K ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (sC, s_fig8, fl) trC ec (pure ())
      (fun _ => (ans, (((sC', s_fig8', fl'), trC'), ec')))
      (fun _ => hamb) (fun j hj => by rw [hstepWin j hj, pure_bind]) winBefore idx
    simpa only [pure_bind] using h
  · simp only [runRContTrack_inr_bind, hD0, hstepR, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _
  · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSim, pure_bind]

theorem closeByStateCTrack_inr_same_amb_bind_const_sim {α γ β : Type} (P : Params PQ (BitVec 512))
    (K : MlKem) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞) (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (stTrR : KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (trC : KemFailTrackState P.C.F)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ) (M : ProbComp β)
    (fR : γ → ((SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) ×
      KemFailTrackBridge.KemFailSessionTrack P.C.F (List (BitVec 8)))
    (fS : γ → (SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range q_sm ×
      ((JointC PQ Pt ℓ × KemFailTrackState P.C.F) × (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1.1 = (fS x).1)
    (hD0 : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR)
    (hstepR : stepRTrack P.C.F K (libsignalSessionScheme P ℓ encPt lam) 3 qep
        (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R stTrR =
      N >>= fun x => pure (fR x))
    (hstepSim : stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep none q_sm
        (sC, s_fig8, fl) trC ec =
      N >>= fun x => M >>= fun _ => pure (fS x))
    (hstepWin : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEagerTrack P K ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm
        (sC, s_fig8, fl) trC ec =
        N >>= fun x => M >>= fun _ => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.1.base.amb = sC.base.amb)
    (hrem : ∀ x, remWin qep (fS x).2.1.1.1.base.mir ≤ remWin qep sC.base.mir)
    (hcont : ∀ x, CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS x).1) (fR x).1.2 (fR x).2 (fS x).2.1.1.1 (fS x).2.1.2 (fS x).2.1.1.2.1
      (fS x).2.1.1.2.2 (fS x).2.2 winBefore) :
    CloseByStateCTrack P K ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query
        (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
        (.inr q_sm)) >>= cont)
      s_R stTrR sC trC s_fig8 fl ec winBefore := by
  unfold CloseByStateCTrack
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep sC.base.mir)) N
      (fun x => closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem x)) (hcont x)))
  · simp only [runRContTrack_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimCEagerTrack_inr_bind, hstepSim, bind_assoc, pure_bind]
    refine evalDist_bind_congr N _ _ fun x => ?_
    exact OracleComp.evalDist_bind_const _ _
  · intro idx _
    unfold runWinAtCTrack
    cases idx with
    | zero =>
      rw [runSimCEagerTrack_inr_bind, hstepSim]
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr N _ _ fun x => ?_
      exact OracleComp.evalDist_bind_const _ _
    | succ j =>
      dsimp only
      simp only [hamb]
      split
      · exact (OracleComp.evalDist_bind_const _ _).symm
      · rename_i hnot
        rw [runSimCEagerTrack_inr_bind, hstepWin j hnot]
        simp only [bind_assoc, pure_bind]
        refine evalDist_bind_congr N _ _ fun x => ?_
        exact OracleComp.evalDist_bind_const _ _
  · simp only [runRContTrack_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runHidCTrack, runSimCEagerTrack_inr_bind, hstepSim, bind_assoc, pure_bind]
    refine evalDist_bind_congr N _ _ fun x => ?_
    exact OracleComp.evalDist_bind_const _ _

end Combinators

end CryptoGames.LibsignalSM.Proofs.Refinement
