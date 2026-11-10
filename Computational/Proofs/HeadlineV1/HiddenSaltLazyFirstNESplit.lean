/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltV1
public import Computational.Proofs.HeadlineV1.SignedRefineC
import Computational.Proofs.HeadlineV1.DeliverForgeShifted
import Computational.Proofs.HeadlineV1.HiddenSaltLazyWire
import Computational.Proofs.SignalWireRoundTrip
import ProofLib.SepLogic.WP.StateNorm

/-!
# Sticky-Dead-Ghost `firstNESimImpl'` Split

**Checked by Lean.** Defines the sticky-dead-ghost simulator `firstNESimImpl'`, proves that its
`dead` branch contributes zero probe probability, and splits `kemFailSimImpl` into `firstNESimImpl'`
plus `evictOnlySimImpl'`.
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

/-! ## Sticky-dead-ghost simulator -/

/-- State monad for `firstNESimImpl'` carrying `(sC, (g, fl, dead), tr)`. -/
abbrev KemFailSimM' (PQ Pt : Type) (F : ShaCompress) (ℓ : ℕ) :=
  StateT (LibsignalToModularSchemeSimState PQ Pt ℓ ×
    (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
    KemFailTrackState F) ProbComp

open Classical in
/-- Sticky-dead-ghost simulator setting `fl` on lazy wrong-salt `deliver` probes before `dead` and
transitioning to `dead` on non-lazy probes. -/
noncomputable def firstNESimImpl'
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) :
    QueryImpl
      (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8)))
      (KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ)
  | .inr (.inl (.inl (.inr (Q, w)))) => do
    let ⟨sC, ⟨g, fl, dead⟩, tr⟩ ← get
    let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
    let j? := sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let tr' := match r.1, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    let hlazy := decide (∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    let hprobe := r.2.2.2
    let fl' := fl || (hlazy && hprobe && !dead)
    let dead' := dead || !hlazy
    set (r.2.1, (r.2.2.1, fl', dead'), tr')
    return r.1
  | q_sm => do
    let ⟨sC, ⟨g, fl, dead⟩, tr⟩ ← get
    let (ans, ⟨sC', ⟨g', fl'⟩, tr'⟩) ←
      StateT.lift ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
        (sC, (g, fl), tr))
    set (sC', (g', fl', dead), tr')
    return ans

open Classical in
private noncomputable def evictOnlySimImpl'
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) :
    QueryImpl
      (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8)))
      (KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ)
  | .inr (.inl (.inl (.inr (Q, w)))) => do
    let ⟨sC, ⟨g, fl, dead⟩, tr⟩ ← get
    let r := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
    let j? := sC.base.honest.reverse.findIdx?
      (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let tr' := match r.1, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
      | _, _ => tr
    let hlazy := decide (∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    let hprobe := r.2.2.2
    let fl' := fl || ((!hlazy || dead) && hprobe)
    let dead' := dead || !hlazy
    set (r.2.1, (r.2.2.1, fl', dead'), tr')
    return r.1
  | q_sm => do
    let ⟨sC, ⟨g, fl, dead⟩, tr⟩ ← get
    let (ans, ⟨sC', ⟨g', fl'⟩, tr'⟩) ←
      StateT.lift ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
        (sC, (g, fl), tr))
    set (sC', (g', fl', dead), tr')
    return ans

theorem firstNESimImpl'_inl_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (n : unifSpec.Domain)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (ghd : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool)
    (tr : KemFailTrackState P.C.F) :
    (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inl n)).run
      (sC, ghd, tr) =
      ((OracleSpec.query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, (sC, ghd, tr))) := by
  rcases ghd with ⟨g, fl, dead⟩
  unfold firstNESimImpl'
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  rfl

theorem simulateQ_firstNESimImpl'_inl_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (n : unifSpec.Domain)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inl n) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (st : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
      (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
      KemFailTrackState P.C.F) :
    (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inl n) >>= u)).run st =
    ((OracleSpec.query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
      fun u₁ => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (u u₁)).run st) := by
  rcases st with ⟨sC, ⟨g, fl, dead⟩, tr⟩
  rw [simulateQ_query_bind, StateT.run_bind]
  change ((firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q (.inl n)).run
      (sC, (g, fl, dead), tr) >>=
    fun p => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (u p.1)).run p.2) = _
  rw [firstNESimImpl'_inl_run]
  simp only [bind_assoc, pure_bind]

private theorem firstNESimImpl'_non_deliver_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
      (sC, (g, fl, dead), tr) =
      ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, (g, fl), tr) >>=
        fun x => pure (x.1, (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2))) := by
  have hlift : ∀ {α : Type} (m : ProbComp α),
      (StateT.lift m : KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ α).run (sC, (g, fl, dead), tr) =
        (m >>= fun a => pure (a, (sC, (g, fl, dead), tr))) := fun _ => rfl
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · simp only [firstNESimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]
  · simp only [firstNESimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]
  · simp only [firstNESimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]
  · exact False.elim (hnd Q w rfl)
  · simp only [firstNESimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]
  · simp only [firstNESimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]

private theorem evictOnlySimImpl'_non_deliver_run
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
      (sC, (g, fl, dead), tr) =
      ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, (g, fl), tr) >>=
        fun x => pure (x.1, (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2))) := by
  have hlift : ∀ {α : Type} (m : ProbComp α),
      (StateT.lift m : KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ α).run (sC, (g, fl, dead), tr) =
        (m >>= fun a => pure (a, (sC, (g, fl, dead), tr))) := fun _ => rfl
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · simp only [evictOnlySimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]
  · simp only [evictOnlySimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]
  · simp only [evictOnlySimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]
  · exact False.elim (hnd Q w rfl)
  · simp only [evictOnlySimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]
  · simp only [evictOnlySimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      hlift, bind_assoc, pure_bind]

/-! ## Dead-branch support -/

private theorem firstNESimImpl'_dead_step
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
      (sC, (g, false, true), tr))) :
    z.2.2.1.2.2 = true ∧ z.2.2.1.2.1 = false := by
  have hnd_step :
      ∀ (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))))
        (hfl : ∀ x ∈ support
            ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, (g, false), tr)),
          x.2.2.1.2 = false),
        z.2.2.1.2.2 = true ∧ z.2.2.1.2.1 = false := by
    intro hnd hfl
    rw [firstNESimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm hnd
      sC g false true tr, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨x, hx, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, hfl x hx⟩
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · refine hnd_step (fun _ _ h => nomatch h) (fun x hx => ?_)
    have h := kemFailSimImpl_inl_state_eq P K ℓ Dh encPt encT decT idOf lam qep n
      sC (g, false) tr x hx
    exact congrArg (·.2.1.2) h
  · exact hnd_step (fun _ _ h => nomatch h) (fun x hx =>
      kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
        (.inl (Q, m₀, r)) sC g tr x hx)
  · exact hnd_step (fun _ _ h => nomatch h) (fun x hx =>
      kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
        (.inr (Q, m₀, m₁, r)) sC g tr x hx)
  · simp only [firstNESimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  · exact hnd_step (fun _ _ h => nomatch h) (fun x hx =>
      kemFailSimImpl_inject_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q w sC g tr x hx)
  · exact hnd_step (fun _ _ h => nomatch h) (fun x hx =>
      kemFailSimImpl_corr_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q sC g tr x hx)

private theorem simulateQ_firstNESimImpl'_dead_support {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α) :
    ∀ (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl dead : Bool) (tr : KemFailTrackState P.C.F)
      (z : α × (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
        KemFailTrackState P.C.F)),
      z ∈ support ((simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        oa).run (sC, (g, fl, dead), tr)) →
      dead = true ∧ fl = false →
      z.2.2.1.2.2 = true ∧ z.2.2.1.2.1 = false := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC g fl dead tr z hz hdead
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hdead
  | query_bind q_sm u ih =>
    intro sC g fl dead tr z hz ⟨hdead, hfl⟩
    subst hdead hfl
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u₁, sC₁, ⟨g₁, fl₁, dead₁⟩, tr₁⟩, h₁, h₂⟩
    exact ih u₁ sC₁ g₁ fl₁ dead₁ tr₁ z h₂
      (firstNESimImpl'_dead_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm
        sC g tr (u₁, sC₁, (g₁, fl₁, dead₁), tr₁) h₁)

/-- Once `dead = true` and `fl = false`, `fl` remains `false` along every execution of
`simulateQ (firstNESimImpl' ...) oa`, so `fl && !cand.isSome = true` has probability `0`. -/
theorem fl_false_of_dead_support {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F)
    (hdead : dead = true ∧ fl = false) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, (g, fl, dead), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} = 0 := by
  have hcongr :
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, fl, dead), tr) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] =
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, fl, dead), tr) >>=
        fun _ => (pure false : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    have hz_fl := (simulateQ_firstNESimImpl'_dead_support P K InvPQ ℓ Dh encPt encT decT idOf
      lam qep q oa sC g fl dead tr z hz hdead).2
    simp [hz_fl]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

/-! ## Simulator split and `hiddenSaltTerm` bound -/

open Classical in
private theorem evalDist_simulateQ_kemFailSimImpl_flag_true_eq_firstNE'
    {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (dead : Bool)
    (tr : KemFailTrackState P.C.F) :
    𝒟[(simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) oa).run
        (sC, (g, true), tr) >>=
      fun z => pure (z.2.2.1.2 && !z.2.2.2.cand.isSome)] =
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, (g, true, dead), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] := by
  induction oa using OracleComp.inductionOn generalizing sC g dead tr with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
      PFunctor.Obj.mk, id]
    have hother : ∀ (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w))))),
        𝒟[(kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, (g, true), tr) >>=
          fun x => (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) (u x.1)).run
            x.2 >>= fun z => pure (z.2.2.1.2 && !z.2.2.2.cand.isSome)] =
        𝒟[(firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
            (sC, (g, true, dead), tr) >>=
          fun x => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
            (u x.1)).run x.2 >>= fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] := by
      intro hnd
      rw [firstNESimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm hnd
        sC g true dead tr, bind_assoc]
      simp only [pure_bind]
      refine evalDist_bind_congr_of_support _ _ _ fun z₁ hz₁ => ?_
      have hfl := kemFailSimImpl_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep
        q_sm sC g tr z₁ hz₁
      rw [show z₁.2 = (z₁.2.1, (z₁.2.2.1.1, true), z₁.2.2.2) from
        Prod.ext rfl (Prod.ext (Prod.ext rfl hfl) rfl)]
      exact ih z₁.1 z₁.2.1 z₁.2.2.1.1 dead z₁.2.2.2
    rcases q_sm with n | ((((⟨Q, m₀, r_coin⟩ | ⟨Q, m₀, m₁, r_coin⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
    · exact hother (fun _ _ h => nomatch h)
    · exact hother (fun _ _ h => nomatch h)
    · exact hother (fun _ _ h => nomatch h)
    · let r₀ := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
      let j? := sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      let tr' := match r₀.1, j? with
        | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
        | _, _ => tr
      let hlazy := decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
      have hdel_kem :
          (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, true), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, true), tr')) := by
        have h := kemFailSimImpl_deliver_run P K ℓ Dh encPt encT decT idOf lam qep Q w
          sC (g, true) tr
        dsimp only at h
        rw [simRecvStepC_flag_or P ℓ Dh encPt encT decT idOf lam qep Q w true sC g true,
          Bool.true_or] at h
        exact h
      have hdel_ne' :
          (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, true, dead), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, true, dead || !hlazy), tr')) := by
        simp [firstNESimImpl', r₀, j?, tr', hlazy, StateT.run_bind, StateT.run_get, StateT.run_set]
        rfl
      rw [hdel_kem, hdel_ne', pure_bind, pure_bind]
      exact ih r₀.1 r₀.2.1 r₀.2.2.1 (dead || !hlazy) tr'
    · exact hother (fun _ _ h => nomatch h)
    · exact hother (fun _ _ h => nomatch h)

open Classical in
private theorem evalDist_simulateQ_kemFailSimImpl_flag_true_eq_evictOnly'
    {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (dead : Bool)
    (tr : KemFailTrackState P.C.F) :
    𝒟[(simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) oa).run
        (sC, (g, true), tr) >>=
      fun z => pure (z.2.2.1.2 && !z.2.2.2.cand.isSome)] =
    𝒟[(simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, (g, true, dead), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] := by
  induction oa using OracleComp.inductionOn generalizing sC g dead tr with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
      PFunctor.Obj.mk, id]
    have hother : ∀ (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w))))),
        𝒟[(kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, (g, true), tr) >>=
          fun x => (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) (u x.1)).run
            x.2 >>= fun z => pure (z.2.2.1.2 && !z.2.2.2.cand.isSome)] =
        𝒟[(evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
            (sC, (g, true, dead), tr) >>=
          fun x => (simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
            (u x.1)).run x.2 >>= fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] := by
      intro hnd
      rw [evictOnlySimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm hnd
        sC g true dead tr, bind_assoc]
      simp only [pure_bind]
      refine evalDist_bind_congr_of_support _ _ _ fun z₁ hz₁ => ?_
      have hfl := kemFailSimImpl_flag_true_of_true P K ℓ Dh encPt encT decT idOf lam qep
        q_sm sC g tr z₁ hz₁
      rw [show z₁.2 = (z₁.2.1, (z₁.2.2.1.1, true), z₁.2.2.2) from
        Prod.ext rfl (Prod.ext (Prod.ext rfl hfl) rfl)]
      exact ih z₁.1 z₁.2.1 z₁.2.2.1.1 dead z₁.2.2.2
    rcases q_sm with n | ((((⟨Q, m₀, r_coin⟩ | ⟨Q, m₀, m₁, r_coin⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
    · exact hother (fun _ _ h => nomatch h)
    · exact hother (fun _ _ h => nomatch h)
    · exact hother (fun _ _ h => nomatch h)
    · let r₀ := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
      let j? := sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      let tr' := match r₀.1, j? with
        | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
        | _, _ => tr
      let hlazy := decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
      have hdel_kem :
          (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, true), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, true), tr')) := by
        have h := kemFailSimImpl_deliver_run P K ℓ Dh encPt encT decT idOf lam qep Q w
          sC (g, true) tr
        dsimp only at h
        rw [simRecvStepC_flag_or P ℓ Dh encPt encT decT idOf lam qep Q w true sC g true,
          Bool.true_or] at h
        exact h
      have hdel_ev' :
          (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, true, dead), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, true, dead || !hlazy), tr')) := by
        simp [evictOnlySimImpl', r₀, j?, tr', hlazy, StateT.run_bind, StateT.run_get,
          StateT.run_set]
      rw [hdel_kem, hdel_ev', pure_bind, pure_bind]
      exact ih r₀.1 r₀.2.1 r₀.2.2.1 (dead || !hlazy) tr'
    · exact hother (fun _ _ h => nomatch h)
    · exact hother (fun _ _ h => nomatch h)

open Classical in
private theorem evalDist_simulateQ_kemFailSimImpl_le_firstNE'_add_evictOnly' {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (dead : Bool)
    (tr : KemFailTrackState P.C.F) :
    𝒟[(simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) oa).run
        (sC, (g, false), tr) >>=
      fun z => pure (z.2.2.1.2 && !z.2.2.2.cand.isSome)] {true} ≤
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, (g, false, dead), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} +
    𝒟[(simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT
        idOf lam qep q) oa).run (sC, (g, false, dead), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} := by
  induction oa using OracleComp.inductionOn generalizing sC g dead tr with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
      PFunctor.Obj.mk, id]
    have hnd_step :
        ∀ (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w)))))
          (hfl : ∀ z₁ ∈ support
              ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run
                (sC, (g, false), tr)),
            z₁.2.2.1.2 = false),
        𝒟[(kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep q_sm).run (sC, (g, false), tr) >>=
          fun x => (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) (u x.1)).run
            x.2 >>= fun z => pure (z.2.2.1.2 && !z.2.2.2.cand.isSome)] {true} ≤
        𝒟[(firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
            (sC, (g, false, dead), tr) >>=
          fun x => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
            (u x.1)).run x.2 >>= fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} +
        𝒟[(evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
            (sC, (g, false, dead), tr) >>=
          fun x => (simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
            (u x.1)).run x.2 >>= fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} := by
      intro hnd hfl
      rw [firstNESimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm hnd
        sC g false dead tr,
        evictOnlySimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm hnd
        sC g false dead tr, bind_assoc, bind_assoc]
      simp only [pure_bind]
      refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun z₁ hz₁ => ?_
      have hfl₁ := hfl z₁ hz₁
      rw [show z₁.2 = (z₁.2.1, (z₁.2.2.1.1, false), z₁.2.2.2) from
        Prod.ext rfl (Prod.ext (Prod.ext rfl hfl₁) rfl)]
      exact ih z₁.1 z₁.2.1 z₁.2.2.1.1 dead z₁.2.2.2
    rcases q_sm with n | ((((⟨Q, m₀, r_coin⟩ | ⟨Q, m₀, m₁, r_coin⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
    · refine hnd_step (fun _ _ h => nomatch h) (fun z₁ hz₁ => ?_)
      have h := kemFailSimImpl_inl_state_eq P K ℓ Dh encPt encT decT idOf lam qep n
        sC (g, false) tr z₁ hz₁
      exact congrArg (·.2.1.2) h
    · exact hnd_step (fun _ _ h => nomatch h) (fun z₁ hz₁ =>
        kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
          (.inl (Q, m₀, r_coin)) sC g tr z₁ hz₁)
    · exact hnd_step (fun _ _ h => nomatch h) (fun z₁ hz₁ =>
        kemFailSimImpl_send_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep
          (.inr (Q, m₀, m₁, r_coin)) sC g tr z₁ hz₁)
    · have hdel_kem := kemFailSimImpl_deliver_run P K ℓ Dh encPt encT decT idOf lam qep Q w
        sC (g, false) tr
      dsimp only at hdel_kem
      let r₀ := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
      let j? := sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
      let tr' := match r₀.1, j? with
        | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
        | _, _ => tr
      let hlazy := decide (∃ r_idx w_rem,
        EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
      have hdel_ne' :
          (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, dead), tr) =
          pure (r₀.1, (r₀.2.1,
            (r₀.2.2.1, hlazy && r₀.2.2.2 && !dead, dead || !hlazy), tr')) := by
        simp [firstNESimImpl', r₀, j?, tr', hlazy, StateT.run_bind, StateT.run_get, StateT.run_set]
        rfl
      have hdel_ev' :
          (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, dead), tr) =
          pure (r₀.1, (r₀.2.1,
            (r₀.2.2.1, (!hlazy || dead) && r₀.2.2.2, dead || !hlazy), tr')) := by
        simp [evictOnlySimImpl', r₀, j?, tr', hlazy, StateT.run_bind, StateT.run_get,
          StateT.run_set]
      have hdel_kem' :
          (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false), tr) =
          pure (r₀.1, (r₀.2.1, (r₀.2.2.1, r₀.2.2.2), tr')) := hdel_kem
      rw [hdel_kem', hdel_ne', hdel_ev', pure_bind, pure_bind, pure_bind]
      dsimp only
      cases hr_fl : r₀.2.2.2 with
      | false =>
        simp only [Bool.and_false, Bool.false_and]
        exact ih r₀.1 r₀.2.1 r₀.2.2.1 (dead || !hlazy) tr'
      | true =>
        cases hgood : (hlazy && !dead) with
        | true =>
          have h1 : (hlazy && true && !dead) = true := by simpa using hgood
          rw [h1, evalDist_simulateQ_kemFailSimImpl_flag_true_eq_firstNE' P K InvPQ ℓ Dh encPt encT
            decT idOf lam qep q (u r₀.1) r₀.2.1 r₀.2.2.1 (dead || !hlazy) tr']
          exact le_self_add
        | false =>
          have h2 : ((!hlazy || dead) && true) = true := by
            revert hgood; cases hlazy <;> cases dead <;> decide
          rw [h2, evalDist_simulateQ_kemFailSimImpl_flag_true_eq_evictOnly' P K InvPQ ℓ Dh encPt
            encT decT idOf lam qep q (u r₀.1) r₀.2.1 r₀.2.2.1 (dead || !hlazy) tr']
          exact le_add_self
    · exact hnd_step (fun _ _ h => nomatch h) (fun z₁ hz₁ =>
        kemFailSimImpl_inject_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q w sC g tr
          z₁ hz₁)
    · exact hnd_step (fun _ _ h => nomatch h) (fun z₁ hz₁ =>
        kemFailSimImpl_corr_flag_eq_false P K ℓ Dh encPt encT decT idOf lam qep Q sC g tr z₁ hz₁)

private theorem evictOnlySimImpl'_cand_some_of_some
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (ghd : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool)
    (tr : KemFailTrackState P.C.F)
    (z : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range q_sm ×
      (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
        KemFailTrackState P.C.F))
    (hz : z ∈ support ((evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm).run
      (sC, ghd, tr)))
    (p : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32)
    (hcand : tr.cand = some p) :
    z.2.2.2.cand = some p := by
  rcases ghd with ⟨g, fl, dead⟩
  have hnd_step :
      ∀ (hnd : ∀ Q w, q_sm ≠ .inr (.inl (.inl (.inr (Q, w))))),
        z.2.2.2.cand = some p := by
    intro hnd
    rw [evictOnlySimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm hnd
      sC g fl dead tr, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨x, hx, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact (kemFailSimImpl_cand_valid P K ℓ Dh encPt encT decT idOf lam qep q_sm
      sC (g, fl) tr x hx).2 p hcand
  rcases q_sm with n | ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact hnd_step (fun _ _ h => nomatch h)
  · exact hnd_step (fun _ _ h => nomatch h)
  · exact hnd_step (fun _ _ h => nomatch h)
  · simp only [evictOnlySimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      pure_bind, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    split
    · rw [stepKemFailDeliver_cand_eq, hcand]
    · exact hcand
  · exact hnd_step (fun _ _ h => nomatch h)
  · exact hnd_step (fun _ _ h => nomatch h)

private theorem simulateQ_evictOnlySimImpl'_cand_some_of_some {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α) :
    ∀ (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (ghd : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool)
      (tr : KemFailTrackState P.C.F)
      (z : α × (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ ×
        (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool) ×
        KemFailTrackState P.C.F)),
      z ∈ support ((simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        oa).run (sC, ghd, tr)) →
      ∀ p, tr.cand = some p → z.2.2.2.cand = some p := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC ghd tr z hz p hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hp
  | query_bind q_sm u ih =>
    intro sC ghd tr z hz p hp
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u₁, sC₁, ghd₁, tr₁⟩, h₁, h₂⟩
    exact ih u₁ sC₁ ghd₁ tr₁ z h₂ p
      (evictOnlySimImpl'_cand_some_of_some P K InvPQ ℓ Dh encPt encT decT idOf lam qep q q_sm
        sC ghd tr (u₁, sC₁, ghd₁, tr₁) h₁ p hp)

private theorem evalDist_evictOnlySimImpl'_cand_some_eq_zero {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (ghd : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool × Bool)
    (tr : KemFailTrackState P.C.F)
    {p : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32}
    (hcand : tr.cand = some p) :
    𝒟[(simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
        (sC, ghd, tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} = 0 := by
  have hcongr :
      𝒟[(simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, ghd, tr) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] =
      𝒟[(simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, ghd, tr) >>=
        fun _ => (pure false : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    have hz_cand := simulateQ_evictOnlySimImpl'_cand_some_of_some P K InvPQ ℓ Dh encPt encT decT
      idOf lam qep q oa sC ghd tr z hz p hcand
    simp [hz_cand]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

private theorem simulateQ_evictOnlySimImpl'_cand_none_prob_le_of_evictedSpurHistSimInvLazy
    {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
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
    (hinj : Function.Injective encT)
    (hdec : ∀ T, decT (encT T) = some T)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q : ℕ) (hS : Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (hq32 : q < 2 ^ 32)
    (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    {p : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain → Prop}
    [DecidablePred p]
    (hp_inl : ∀ n, ¬ p (.inl n)) (hp_inr : ∀ q_game, p (.inr q_game))
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α) :
    ∀ (r w_rem : ℕ)
      (_hq : oa.IsQueryBoundP p r)
      (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (tr : KemFailTrackState P.C.F)
      (_hInv : EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r w_rem sC g),
      𝒟[(simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, false, false), tr) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
        spurSlack P encPt Dh q w_rem + ((w_rem : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro r w_rem _ sC g tr _
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    intro r w_rem hq sC g tr hInv
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases hq with ⟨hq0, hu⟩
    rw [simulateQ_query_bind, StateT.run_bind, bind_assoc]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd,
      PFunctor.Obj.mk, id]
    rcases q_sm with n | q_game
    · rw [evictOnlySimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inl n) (fun _ _ h => nomatch h) sC g false false tr, bind_assoc]
      simp only [pure_bind]
      refine evalDist_bind_true_le_of_support _ _ _ fun z₁ h₁ => ?_
      have hz₁ := kemFailSimImpl_inl_state_eq P K ℓ Dh encPt encT decT idOf lam qep n
        sC (g, false) tr z₁ h₁
      have h1 : z₁.2.1 = sC := congrArg (·.1) hz₁
      have h2 : z₁.2.2.1.1 = g := congrArg (·.2.1.1) hz₁
      have h3 : z₁.2.2.1.2 = false := congrArg (·.2.1.2) hz₁
      have h4 : z₁.2.2.2 = tr := congrArg (·.2.2) hz₁
      rw [h1, h2, h3, h4]
      exact ih z₁.1 r w_rem (by simpa [hp_inl n] using hu z₁.1) sC g tr hInv
    · have hr_pos : 0 < r := hq0.resolve_left (not_not.mpr (hp_inr q_game))
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rcases q_game with (((⟨Q, m₀, r_coin⟩ | ⟨Q, m₀, m₁, r_coin⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
      · rw [evictOnlySimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          (.inr (.inl (.inl (.inl (.inl (Q, m₀, r_coin)))))) (fun _ _ h => nomatch h)
          sC g false false tr, bind_assoc]
        simp only [pure_bind]
        exact kemFailSendStep_evictOnly_bound P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT
          idOf hX hD hrt hid lam qep q r' w_rem hS hq32 δ hδ Q m₀ none r_coin sC g tr hInv _
          (fun u₁ sC₁ gh₁ tr₁ p_cand hcand₁ =>
            evalDist_evictOnlySimImpl'_cand_some_eq_zero P K InvPQ ℓ Dh encPt encT decT idOf lam
              qep q (u u₁) sC₁ (gh₁.1, gh₁.2, false) tr₁ hcand₁)
          (fun u₁ sC₁ g₁ tr₁ hInv₁ =>
            ih u₁ r' w_rem (by simpa [hp_inr _] using hu u₁) sC₁ g₁ tr₁ hInv₁)
          (fun w' u₁ sC₁ g₁ tr₁ _ hInv₁ =>
            ih u₁ r' w' (by simpa [hp_inr _] using hu u₁) sC₁ g₁ tr₁ hInv₁)
      · rw [evictOnlySimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r_coin)))))) (fun _ _ h => nomatch h)
          sC g false false tr, bind_assoc]
        simp only [pure_bind]
        exact kemFailSendStep_evictOnly_bound P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT
          idOf hX hD hrt hid lam qep q r' w_rem hS hq32 δ hδ Q m₀ (some m₁) r_coin sC g tr hInv _
          (fun u₁ sC₁ gh₁ tr₁ p_cand hcand₁ =>
            evalDist_evictOnlySimImpl'_cand_some_eq_zero P K InvPQ ℓ Dh encPt encT decT idOf lam
              qep q (u u₁) sC₁ (gh₁.1, gh₁.2, false) tr₁ hcand₁)
          (fun u₁ sC₁ g₁ tr₁ hInv₁ =>
            ih u₁ r' w_rem (by simpa [hp_inr _] using hu u₁) sC₁ g₁ tr₁ hInv₁)
          (fun w' u₁ sC₁ g₁ tr₁ _ hInv₁ =>
            ih u₁ r' w' (by simpa [hp_inr _] using hu u₁) sC₁ g₁ tr₁ hInv₁)
      · let r₀ := simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))
        let j? := sC.base.honest.reverse.findIdx?
          (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
        let tr' := match r₀.1, j? with
          | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
          | _, _ => tr
        have hlazy_true :
            decide (∃ r_idx w_rem,
              EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g) =
              true :=
          decide_eq_true ⟨r' + 1, w_rem, hInv⟩
        have hdel_ev' :
            (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
              (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false, false), tr) =
            pure (r₀.1, (r₀.2.1, (r₀.2.2.1, false, false), tr')) := by
          simp [evictOnlySimImpl', r₀, j?, tr', hlazy_true, StateT.run_bind, StateT.run_get,
            StateT.run_set]
        rw [hdel_ev', pure_bind]
        dsimp only
        cases hcand₁ : tr'.cand with
        | some p_cand =>
          rw [evalDist_evictOnlySimImpl'_cand_some_eq_zero P K InvPQ ℓ Dh encPt encT decT idOf lam
            qep q (u r₀.1) r₀.2.1 (r₀.2.2.1, false, false) tr' hcand₁]
          exact zero_le
        | none =>
          have hmem_kem : (r₀.1, (r₀.2.1, (r₀.2.2.1, r₀.2.2.2), tr')) ∈
              support ((kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep
                (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, (g, false), tr)) := by
            rw [kemFailSimImpl_deliver_run]
            simp only [support_pure, Set.mem_singleton_iff]
            rfl
          have hInv₁ := evictedSpurHistSimInvLazy_deliver_step P K hspqr_eq InvPQ hInv_top ℓ Dh
            encPt encT decT idOf hinj hdec lam qep q r' (r' + 1) w_rem hS (Nat.lt_succ_self r')
            Q w sC g tr hInv (r₀.1, (r₀.2.1, (r₀.2.2.1, r₀.2.2.2), tr')) hmem_kem hcand₁
          exact ih r₀.1 r' w_rem (by simpa [hp_inr _] using hu r₀.1) r₀.2.1 r₀.2.2.1 tr' hInv₁
      · rw [evictOnlySimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          (.inr (.inl (.inr (Q, w)))) (fun _ _ h => nomatch h) sC g false false tr, bind_assoc]
        simp only [pure_bind]
        refine evalDist_bind_true_le_of_support _ _ _ fun ⟨u₁, sC₁, gh₁, tr₁⟩ h₁ => ?_
        dsimp only
        cases hcand₁ : tr₁.cand with
        | some p_cand =>
          rw [evalDist_evictOnlySimImpl'_cand_some_eq_zero P K InvPQ ℓ Dh encPt encT decT idOf lam
            qep q _ sC₁ (gh₁.1, gh₁.2, false) tr₁ hcand₁]
          exact zero_le
        | none =>
          rcases evictedSpurHistSimInvLazy_inject_step P K hspqr_eq InvPQ hInv_top ℓ Dh encPt encT
              decT idOf hinj hid lam qep q r' (r' + 1) w_rem hS (Nat.lt_succ_self r') Q w sC g tr
              hInv (u₁, sC₁, gh₁, tr₁) h₁ hcand₁ with ⟨hfl₁, hInv₁⟩
          rw [hfl₁]
          exact ih u₁ r' w_rem (by simpa [hp_inr _] using hu u₁) sC₁ gh₁.1 tr₁ hInv₁
      · rw [evictOnlySimImpl'_non_deliver_run P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          (.inr (.inr Q)) (fun _ _ h => nomatch h) sC g false false tr, bind_assoc]
        simp only [pure_bind]
        refine evalDist_bind_true_le_of_support _ _ _ fun ⟨u₁, sC₁, gh₁, tr₁⟩ h₁ => ?_
        dsimp only
        cases hcand₁ : tr₁.cand with
        | some p_cand =>
          rw [evalDist_evictOnlySimImpl'_cand_some_eq_zero P K InvPQ ℓ Dh encPt encT decT idOf lam
            qep q _ sC₁ (gh₁.1, gh₁.2, false) tr₁ hcand₁]
          exact zero_le
        | none =>
          rcases evictedSpurHistSimInvLazy_corr_step P K InvPQ hInv_top ℓ Dh encPt encT decT idOf
              lam qep q r' (r' + 1) w_rem hq32 (Nat.le_succ r') Q sC g tr hInv
              (u₁, sC₁, gh₁, tr₁) h₁ hcand₁ with ⟨hfl₁, hInv₁⟩
          rw [hfl₁]
          exact ih u₁ r' w_rem (by simpa [hp_inr _] using hu u₁) sC₁ gh₁.1 tr₁ hInv₁

theorem cand_none_prob_le_add_spuriousStepTerm_of_evictedSpurHistSimInvLazy'
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins P.C.F K)
    {InvPQ : ℕ → List (BitVec 8) → Prop}
    (hInv_top : ∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hdec : ∀ T, decT (encT T) = some T)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : RoundTrip.RtHyp P ℓ)
    (lam : Pt) (qep q : ℕ)
    (hq32 : q < 2 ^ 32)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hS : Proofs.Refinement.SpqrCLocal P.spqr q InvPQ)
    (hcoll0 : ∀ x₀ : BitVec 256, ∃ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base)
    (D δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : LibsignalSM.LibAdv (List (BitVec 8)) (BitVec 512) ℓ)
    (hq : SM.MakesAtMostQueries A q)
    (hfirstNE' :
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
            (sC₀, ghd₀, tr₀)
        return (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤ D) :
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let gh₀ := (SM.initState fig k b, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run (sC₀, gh₀, tr₀)
      return (z.2.2.1.2 && !z.2.2.2.cand.isSome)] {true} ≤
    D + spuriousStepTerm P.C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ := by
  have hunion :
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let gh₀ := (SM.initState fig k b, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run (sC₀, gh₀, tr₀)
        return (z.2.2.1.2 && !z.2.2.2.cand.isSome)] {true} ≤
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
            (sC₀, ghd₀, tr₀)
        return (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} +
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
            (sC₀, ghd₀, tr₀)
        return (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} := by
    refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun b _ => ?_
    refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun k _ => ?_
    refine evalDist_bind_le_add_bool_of_support _ _ _ _ fun pqrKey _ => ?_
    exact evalDist_simulateQ_kemFailSimImpl_le_firstNE'_add_evictOnly' P K InvPQ ℓ Dh encPt encT
      decT idOf lam qep q A
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b)
      false
      (initKemFailTrack P.C.F pqrKey)
  have hevict :
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (evictOnlySimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
            (sC₀, ghd₀, tr₀)
        return (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      spuriousStepTerm P.C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ := by
    refine evalDist_bind_true_le_of_support _ _ _ fun b _ => ?_
    refine evalDist_bind_true_le_of_support _ _ _ fun k _ => ?_
    refine evalDist_bind_true_le_of_support _ _ _ fun pqrKey _ => ?_
    have hstep := simulateQ_evictOnlySimImpl'_cand_none_prob_le_of_evictedSpurHistSimInvLazy
      P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT idOf hX hD hrt hinj hdec hid lam
      qep q hS hq32 δ hδ (fun _ h => nomatch h) (fun _ => rfl) A q qep hq
      (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
      (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b)
      (initKemFailTrack P.C.F pqrKey)
      (EvictedSpurHistSimInv.toLazy hInv_top
        (evictedSpurHistSimInv_init P K InvPQ ℓ Dh encPt encT idOf lam qep q hX hS b k pqrKey
          (hcoll0 k.2)))
    have hcoll_le :
        ((qep : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) ≤
          (qep + 1) * (qep + 2) * δ := by
      calc ((qep : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ)
          ≤ ((qep + 1 : ℕ) : ℝ≥0∞) * (((qep + 2 : ℕ) : ℝ≥0∞) * δ) := by
            gcongr
            exact Nat.le_succ qep
        _ = (qep + 1) * (qep + 2) * δ := by
            push_cast
            ring
    exact hstep.trans (add_le_add (spurSlack_le_spuriousStepTerm P encPt Dh q qep le_rfl) hcoll_le)
  calc _ ≤ D + (spuriousStepTerm P.C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ) :=
      hunion.trans (add_le_add hfirstNE' hevict)
    _ = D + spuriousStepTerm P.C.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ := by
      ring

end CryptoVerification.LibsignalSession.HeadlineV1

namespace CryptoVerification.E2E.Signed

open MeasureTheory
open CryptoGames CryptoGames.SM CryptoGames.SM.Construction CryptoGames.Ratchet
  CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSM.Proofs CryptoVerification.E2E
  CryptoGames.LibsignalSession CryptoGames.CKA LibsignalProtoCodec CryptoGames.LibsignalSM
  CryptoGames.LibsignalSM.Proofs.Refinement CryptoGames.Ratchet.LibsignalSim
  CryptoGames.Ratchet.LibsignalSimC CryptoGames.SM.Construction.DeliverForge
  CryptoVerification.E2E.RefuseCorrB0 CryptoVerification.E2E.HeadlineU
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1Sync.SendTotal
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalSession.HeadlineV1

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

/-- Bounds `hiddenSaltTerm` on `RefuseB0.refuseCorrB0 A` by a cell-sum bound on `firstNESimImpl'`
plus `spuriousStepTerm` and `kemFailFindAdvantage`. -/
theorem hiddenSaltTerm_le_add_spuriousStepTerm_v1_refuseCorrB0_lazy'
    {ℓ : ℕ}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (hK_tot : Encaps1Total K)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hDh : Dh.Commutes) (hX : X25519RealizesDh C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hinj : Function.Injective encT)
    (_hdum : ∀ T, encT T ≠ dummyKey)
    (_hz : ∀ x, Dh.dh x 0 = 0) (hD : ∀ k x, C.D k (C.E k x) = x)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (D δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q)
    (hfirstNE' :
      let P := paramsV1 C K idA idB
      let idOf := idsOf idA idB
      ∀ (InvPQ : ℕ → List (BitVec 8) → Prop),
      Proofs.Refinement.SpqrCLocal P.spqr q InvPQ →
      (∀ n pq, InvPQ n pq → CryptoVerification.SpqrV1Sync.SendTotal.TopState P.C.F K pq) →
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ (BitVec 256 × BitVec 256)
        let pqrKey ← $ᵗ BitVec 256
        let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
        let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
          initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
        let ghd₀ := (SM.initState fig k b, false, false)
        let tr₀ := initKemFailTrack P.C.F pqrKey
        let z ←
          (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
            A.refuseCorrB0).run (sC₀, ghd₀, tr₀)
        return (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤ D) :
    let P := paramsV1 C K idA idB
    let idOf := idsOf idA idB
    hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A.refuseCorrB0 ≤
      D + spuriousStepTerm C.F encPt Dh q qep +
        (qep + 1) * (qep + 2) * δ +
        K.kemFailFindAdvantage
          (Proofs.Refinement.redKemFailHiddenSalt P K ℓ Dh encPt encT decT idOf lam qep
            A.refuseCorrB0) := by
  intro P idOf
  by_cases hcoll0 : ∀ x₀ : BitVec 256, ∃ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base ≠ Dh.dh x₀ Dh.base
  · obtain ⟨InvPQ, hS, hInv_top⟩ := spqrCLocal_and_topState_v1 P K rfl hK_tot q (by omega)
    refine (hiddenSaltTerm_le_cand_none_add_kemFailFindAdvantage P K ℓ Dh encPt encT decT idOf
      lam qep A.refuseCorrB0).trans (add_le_add ?_ le_rfl)
    have hle := cand_none_prob_le_add_spuriousStepTerm_of_evictedSpurHistSimInvLazy'
      P K rfl hInv_top ℓ Dh hDh encPt encT decT hinj idOf ⟨rfl, rfl⟩ hdec hD
      ⟨signalRoundTripShort_proto, lengthsOk_paramsIdsWithSpqr_v1 C K idA idB ℓ hℓ, signalEncodeFits32_proto⟩
      lam qep q (by omega) hX hS hcoll0 D δ hδ A.refuseCorrB0 (refuseCorrB0_queries A q hq)
      (hfirstNE' InvPQ hS hInv_top)
    exact hle.trans (le_of_eq (by simp only [P, paramsV1_C]))
  · have ⟨x₀, hx₀⟩ :
        ∃ x₀ : BitVec 256, ∀ eA₀ : BitVec 256, Dh.dh eA₀ Dh.base = Dh.dh x₀ Dh.base := by
      classical
      simpa only [not_forall, not_exists, not_ne_iff] using hcoll0
    have h1δ : (1 : ℝ≥0∞) ≤ δ := by
      have h := hδ (Dh.dh x₀ Dh.base)
      have huniv : {x : BitVec 256 | Dh.dh x Dh.base = Dh.dh x₀ Dh.base} = Set.univ :=
        Set.eq_univ_of_forall hx₀
      rwa [huniv, evalDist_apply_univ_eq_one] at h
    have hpow : (1 : ℝ≥0∞) ≤ (qep + 1) * (qep + 2) := by
      have hnat : 1 ≤ (qep + 1) * (qep + 2) := by nlinarith
      exact_mod_cast hnat
    have h1_le : (1 : ℝ≥0∞) ≤ (qep + 1) * (qep + 2) * δ := by
      simpa using mul_le_mul' hpow h1δ
    exact (evalDist_apply_le_one _ _).trans (h1_le.trans
      (le_add_of_le_of_nonneg (le_add_of_nonneg_left zero_le) zero_le))

end CryptoVerification.E2E.Signed

end
