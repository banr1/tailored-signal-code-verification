/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimShallow
import VCVio.OracleComp.QueryTracking.SubSpec
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs

/-!
# Query bounds and equal-pub challenges for `sim` and `simWin`

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves query-count preservation (`sim_queries_proof`) and equal-public-challenge preservation
(`simRun_equalPub`) for the libsignal-to-Fig. 8 simulator.
-/

@[expose] public section

open OracleComp OracleSpec

namespace CryptoGames.LibsignalSM.Proofs.QueryBounds

set_option linter.unusedSectionVars false

open CryptoGames Ratchet
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA LibsignalSession LibsignalInst
  LibsignalSim

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}

abbrev FSpec (Pt : Type) (ℓ : ℕ) :=
  unifSpec + SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)

abbrev SimM (PQ Pt : Type) (ℓ : ℕ) := StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ)

section Generic

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

theorem isQueryBoundP_false (oa : OracleComp spec α) (n : ℕ) :
    IsQueryBoundP oa (fun _ => False) n := by
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simp [ih u]⟩

theorem isQueryBoundP_congr {oa : OracleComp spec α} {p q : ι → Prop}
    [DecidablePred p] [DecidablePred q] (hpq : ∀ x, p x ↔ q x) {n : ℕ}
    (h : IsQueryBoundP oa p n) : IsQueryBoundP oa q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    exact ⟨h.1.imp (mt (hpq t).mpr) id, fun u => by
      simpa [hpq t] using ih u (h.2 u)⟩

theorem isQueryBoundP_simulateQ_run_zero {ι' σ : Type} {spec' : OracleSpec.{0, 0} ι'}
    {Q : ι' → Prop} [DecidablePred Q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    (oa : OracleComp spec α)
    (hstep : ∀ t (s : σ), IsQueryBoundP ((impl t).run s) Q 0) (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) Q 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure _ => simp [simulateQ_pure]
  | query_bind t mx ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    have hlift : IsQueryBoundP
        ((liftM (impl t) : StateT σ (OracleComp spec') (spec.Range t)).run s) Q 0 := by
      simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t s
    simpa using isQueryBoundP_bind hlift fun pu _ => ih pu.1 pu.2

end Generic

section QB

variable {Q : (FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] {α β : Type}

/-- Stateful simulator computation `x` makes at most `n` `Q`-queries from every state `s`. -/
def QB (Q : (FSpec Pt ℓ).Domain → Prop) [DecidablePred Q]
    {α : Type} (x : SimM PQ Pt ℓ α) (n : ℕ) : Prop :=
  ∀ s : SimState PQ Pt ℓ, IsQueryBoundP (x.run s) Q n

theorem qb_pure (a : α) (n : ℕ) : QB (PQ := PQ) Q (pure a) n := fun _ => by
  simp

theorem qb_bind {x : SimM PQ Pt ℓ α} {f : α → SimM PQ Pt ℓ β} {n m : ℕ}
    (hx : QB Q x n) (hf : ∀ a, QB Q (f a) m) : QB Q (x >>= f) (n + m) := fun s => by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (hx s) fun p _ => hf p.1 p.2

theorem qb_bind0 {x : SimM PQ Pt ℓ α} {f : α → SimM PQ Pt ℓ β} {m : ℕ}
    (hx : QB Q x 0) (hf : ∀ a, QB Q (f a) m) : QB Q (x >>= f) m := by
  simpa using qb_bind hx hf

theorem qb_bind_r {x : SimM PQ Pt ℓ α} {f : α → SimM PQ Pt ℓ β} {n : ℕ}
    (hx : QB Q x n) (hf : ∀ a, QB Q (f a) 0) : QB Q (x >>= f) n := by
  simpa using qb_bind hx hf

theorem qb_mono {x : SimM PQ Pt ℓ α} {n m : ℕ} (hx : QB Q x n) (hnm : n ≤ m) : QB Q x m :=
  fun s => (hx s).mono hnm

theorem qb_ite {c : Prop} [Decidable c] {x y : SimM PQ Pt ℓ α} {n : ℕ}
    (hx : QB Q x n) (hy : QB Q y n) : QB Q (if c then x else y) n := by
  by_cases hc : c <;> simp [hc, hx, hy]

theorem qb_ite_pure {c : Prop} [Decidable c] {a : α} {y : SimM PQ Pt ℓ α} {n : ℕ}
    (hy : QB Q y n) : QB Q (if c then pure a else y) n :=
  qb_ite (qb_pure a n) hy

theorem qb_map {x : SimM PQ Pt ℓ α} {n : ℕ} (f : α → β) (hx : QB Q x n) :
    QB Q (f <$> x) n := fun s => by
  rw [StateT.run_map]
  exact (isQueryBoundP_map_iff _ _ _).mpr (hx s)

theorem qb_get : QB (PQ := PQ) Q (get : SimM PQ Pt ℓ (SimState PQ Pt ℓ)) 0 := fun _ => by
  simp

theorem qb_set (s' : SimState PQ Pt ℓ) :
    QB Q (set s' : SimM PQ Pt ℓ PUnit) 0 := fun _ => by
  simp

theorem qb_putS (s' : SimState PQ Pt ℓ) : QB Q (putS s') 0 :=
  qb_set s'

theorem qb_modify (f : SimState PQ Pt ℓ → SimState PQ Pt ℓ) :
    QB Q (modify f : SimM PQ Pt ℓ PUnit) 0 := fun _ => by
  simp

theorem qb_liftQ {x : Fig8Comp Pt ℓ α} {n : ℕ} (hx : IsQueryBoundP x Q n) :
    QB (PQ := PQ) Q (liftQ x) n := fun s => by
  show IsQueryBoundP (x >>= fun a => pure (a, s)) Q n
  simpa using isQueryBoundP_bind hx (fun a _ => isQueryBoundP_pure Q (a, s) 0)

theorem qb_liftQ_query {t : (FSpec Pt ℓ).Domain} {d : ℕ} (hd : Q t → 0 < d) :
    QB (PQ := PQ) Q (liftQ (query (spec := FSpec Pt ℓ) t)) d :=
  qb_liftQ ((isQueryBoundP_query_iff Q t d).2 hd)

variable (hQu : ∀ u, ¬ Q (.inl u))
include hQu

theorem isQueryBoundP_liftProb (p : ProbComp α) :
    IsQueryBoundP (liftM p : Fig8Comp Pt ℓ α) Q 0 :=
  IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
    (fun t => ⟨False.elim, fun h => hQu t h⟩) (isQueryBoundP_false p 0)

theorem qb_coin (γ : Type) [SampleableType γ] : QB (PQ := PQ) (ℓ := ℓ) Q (coin γ) 0 :=
  qb_liftQ (isQueryBoundP_liftProb hQu ($ᵗ γ))

end QB

section Ops

variable (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
  (decT : PublicKey → Option Pt) (qep : ℕ)
  {Q : (FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
  (hQu : ∀ u, ¬ Q (.inl u))
  (hQt : ∀ R pm rc, Q (.inr (.inl (.inl (.inl (.inl (R, pm, rc)))))) → 0 < d)
  (hQc : ∀ R pub m₀ m₁ rc, Q (.inr (.inl (.inl (.inl (.inr (R, (pub, m₀), (pub, m₁), rc)))))) → 0 < d)
  (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
  (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
  (hQcorr : ∀ R, Q (.inr (.inr R)) → 0 < d)

include hQu hQt hQc in
theorem qb_simSend (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    QB Q (simSend (P := P) (qep := qep) R m₀ chal r) d := by
  unfold simSend
  refine qb_bind0 qb_get fun s => ?_
  split
  · exact qb_pure none d
  · cases s.mir.epMgmt 3 qep R r.isSome with
    | none => exact qb_pure none d
    | some s₁ =>
      dsimp only
      split
      · exact qb_pure none d
      · cases r with
        | some rq =>
          simp only [pure_bind]
          refine qb_bind0 (qb_map some (qb_coin hQu (BitVec 256))) fun rc => ?_
          split
          · exact qb_pure none d
          · cases chal with
            | none =>
              refine qb_bind_r (qb_liftQ_query (hQt R _ rc)) fun res => ?_
              cases res with
              | none => exact qb_pure none 0
              | some c => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
            | some m₁ =>
              refine qb_bind_r (qb_liftQ_query (hQc R _ m₀ m₁ rc)) fun res => ?_
              cases res with
              | none => exact qb_pure none 0
              | some c => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
        | none =>
          refine qb_bind0 (qb_coin hQu PQC) fun rq => ?_
          simp only [pure_bind]
          split
          · exact qb_pure none d
          · cases chal with
            | none =>
              refine qb_bind_r (qb_liftQ_query (hQt R _ none)) fun res => ?_
              cases res with
              | none => exact qb_pure none 0
              | some c => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
            | some m₁ =>
              refine qb_bind_r (qb_liftQ_query (hQc R _ m₀ m₁ none)) fun res => ?_
              cases res with
              | none => exact qb_pure none 0
              | some c => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0

include hQd hQi in
theorem qb_fwd (R : Party) (c : Fig8C Pt) :
    QB (PQ := PQ) Q (fwd R c) d := by
  unfold fwd
  refine qb_bind0 qb_get fun s => ?_
  dsimp only
  split
  · exact qb_liftQ_query (hQd R c)
  · exact qb_liftQ_query (hQi R c)

theorem qb_onAccept (R : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) :
    QB (Pt := Pt) Q (onAccept (qep := qep) R w isDel t i m ci? T pq') 0 := by
  unfold onAccept
  refine qb_bind0 qb_get fun s => ?_
  dsimp only
  split
  · cases s.mir.inTransit R.other w with
    | none => exact qb_pure none 0
    | some r => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
  · split
    · exact qb_pure (some RecvResult.rejected) 0
    · split
      · exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
      · exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0

theorem qb_onAnswer (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) :
    QB (Pt := Pt) Q (onAnswer (qep := qep) R w isDel ci? T pq' res) 0 := by
  unfold onAnswer
  cases res with
  | none => exact qb_pure (some RecvResult.rejected) 0
  | some rr =>
    cases rr with
    | rejected => exact qb_pure (some RecvResult.rejected) 0
    | accepted t i pm => exact qb_onAccept qep R w isDel t i _ ci? T pq'

include hQcorr in
theorem qb_simCorr (R : Party) :
    QB Q (simCorr (P := P) (Dh := Dh) (encT := encT) R) d := by
  unfold simCorr
  refine qb_bind0 qb_get fun s => ?_
  split
  · exact qb_pure none d
  · refine qb_bind_r (qb_liftQ_query (hQcorr R)) fun res => ?_
    cases res with
    | none => exact qb_pure none 0
    | some st => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0

theorem qb_guard {α : Type} {x : SimM PQ Pt ℓ (Option α)} {n : ℕ} (hx : QB Q x n) :
    QB Q (LibsignalSim.guard x) n := by
  unfold LibsignalSim.guard
  refine qb_bind0 qb_get fun s => ?_
  split
  · exact qb_pure none n
  · exact hx

include hQt hQd hQi in
theorem qb_simRecv (k : Option ℕ) (R : Party) (w : List (BitVec 8)) (isDel : Bool) :
    QB Q (simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) R w isDel)
      (d + d) := by
  unfold simRecv
  refine qb_bind0 qb_get fun s => ?_
  dsimp only
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact qb_pure (some RecvResult.rejected) _
  | some hp =>
    dsimp only
    refine qb_ite_pure ?_
    cases P.spqr.recv (s.pq R) hp.1.pqRatchet with
    | error _ => exact qb_pure (some RecvResult.rejected) _
    | ok ps =>
      dsimp only
      cases (s.chains R).findIdx? (fun g => g.key == some hp.1.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine qb_ite_pure ?_
        exact qb_mono (qb_bind_r (qb_fwd d hQd hQi R _) fun res =>
          qb_onAnswer qep R w isDel _ _ _ res) (by omega)
      | none =>
        dsimp only
        refine qb_ite_pure ?_
        refine qb_ite_pure ?_
        refine qb_ite (qb_bind0 (qb_putS _) fun _ => ?_) ?_ <;>
        · split
          · refine qb_ite ?_ ?_
            · refine qb_ite ?_ (qb_bind0 (qb_modify _) fun _ => qb_pure none (d + d))
              cases decT hp.1.senderRatchetKey with
              | none => exact qb_bind0 (qb_modify _) fun _ => qb_pure none (d + d)
              | some T =>
                refine qb_mono (qb_bind_r (qb_fwd d hQd hQi R _) fun _ => ?_) (by omega)
                exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
            · refine qb_bind (qb_liftQ_query (hQt R _ none)) fun _ => ?_
              cases decT hp.1.senderRatchetKey with
              | none => exact qb_bind0 (qb_modify _) fun _ => qb_pure none d
              | some T =>
                refine qb_bind_r (qb_fwd d hQd hQi R _) fun _ => ?_
                exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
          · refine qb_ite_pure ?_
            cases decT hp.1.senderRatchetKey with
            | none => exact qb_pure (some RecvResult.rejected) (d + d)
            | some T =>
              exact qb_mono (qb_bind_r (qb_fwd d hQd hQi R _) fun res =>
                qb_onAnswer qep R w isDel none _ _ res) (by omega)

include hQd hQi in
theorem qb_simRecv_none (R : Party) (w : List (BitVec 8)) (isDel : Bool) :
    QB Q (simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := none) R w isDel) d := by
  unfold simRecv
  refine qb_bind0 qb_get fun s => ?_
  dsimp only
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact qb_pure (some RecvResult.rejected) d
  | some hp =>
    dsimp only
    refine qb_ite_pure ?_
    cases P.spqr.recv (s.pq R) hp.1.pqRatchet with
    | error _ => exact qb_pure (some RecvResult.rejected) d
    | ok ps =>
      dsimp only
      cases (s.chains R).findIdx? (fun g => g.key == some hp.1.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine qb_ite_pure ?_
        exact qb_bind_r (qb_fwd d hQd hQi R _) fun res =>
          qb_onAnswer qep R w isDel _ _ _ res
      | none =>
        dsimp only
        refine qb_ite_pure ?_
        refine qb_ite_pure ?_
        refine qb_ite (qb_bind0 (qb_putS _) fun _ => ?_) ?_ <;>
        · split
          · rename_i heq; simp at heq
          · refine qb_ite_pure ?_
            cases decT hp.1.senderRatchetKey with
            | none => exact qb_pure (some RecvResult.rejected) d
            | some T =>
              exact qb_bind_r (qb_fwd d hQd hQi R _) fun res =>
                qb_onAnswer qep R w isDel none _ _ res

end Ops

section EqualPub

abbrev QEq (Pt : Type) (ℓ : ℕ) : (FSpec Pt ℓ).Domain → Prop :=
  fun t => SM.unequalPubChall (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
    (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) t = true

theorem hQu_QEq : ∀ u : ℕ, ¬ QEq Pt ℓ (.inl u) := by
  intro _ h; nomatch h

theorem qb_simImpl_QEq (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    QB (QEq Pt ℓ) (simImpl P Dh encT decT qep k t) 0 := by
  have hQt : ∀ R pm rc, QEq Pt ℓ (.inr (.inl (.inl (.inl (.inl (R, pm, rc)))))) → 0 < 0 := by
    intro _ _ _ h; nomatch h
  have hQc : ∀ R pub m₀ m₁ rc,
      QEq Pt ℓ (.inr (.inl (.inl (.inl (.inr (R, (pub, m₀), (pub, m₁), rc)))))) → 0 < 0 := by
    intro _ _ _ _ _ h
    simp [QEq, SM.unequalPubChall] at h
  have hQd : ∀ R c, QEq Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) → 0 < 0 := by
    intro _ _ h; nomatch h
  have hQi : ∀ R c, QEq Pt ℓ (.inr (.inl (.inr (R, c)))) → 0 < 0 := by
    intro _ _ h; nomatch h
  have hQcorr : ∀ R, QEq Pt ℓ (.inr (.inr R)) → 0 < 0 := by
    intro _ h; nomatch h
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
  · exact qb_liftQ_query fun h => absurd h (hQu_QEq n)
  · exact qb_guard (qb_simSend P qep 0 hQu_QEq hQt hQc R m none r)
  · exact qb_guard (qb_simSend P qep 0 hQu_QEq hQt hQc R m₀ (some m₁) r)
  · exact qb_guard (qb_simRecv P encT decT qep 0 hQt hQd hQi k R w true)
  · exact qb_guard (qb_simRecv P encT decT qep 0 hQt hQd hQi k R w false)
  · exact qb_guard (qb_simCorr P Dh encT 0 hQcorr R)

theorem simRun_equalPub (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (simRun P Dh encT decT qep k A) := by
  unfold SM.EqualPubChalls simRun
  change IsQueryBoundP _ (QEq Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QEq ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simImpl P Dh encT decT qep k) A).run
        (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QEq Pt ℓ) 0 :=
    isQueryBoundP_simulateQ_run_zero A (qb_simImpl_QEq P Dh encT decT qep k) _
  rw [StateT.run'_eq, ← Nat.add_zero 0]
  have hmap : IsQueryBoundP
      (Prod.fst <$> (simulateQ (simImpl P Dh encT decT qep k) A).run
        (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QEq Pt ℓ) 0 :=
    (isQueryBoundP_map_iff _ _ _).mpr hsim
  refine isQueryBoundP_bind hmap fun b' _ => ?_
  cases k with
  | none => exact isQueryBoundP_pure _ b' 0
  | some _ => exact isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QEq ($ᵗ Bool)

end EqualPub

section Queries

abbrev QInr (Pt : Type) (ℓ : ℕ) : (FSpec Pt ℓ).Domain → Prop :=
  (· matches .inr _)

theorem hQu_QInr : ∀ u : ℕ, ¬ QInr Pt ℓ (.inl u) := by
  intro _ h; nomatch h

theorem qb_simImpl_none_inr (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (o : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    QB (QInr Pt ℓ) (simImpl P Dh encT decT qep none (.inr o)) 1 := by
  rcases o with ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R)
  · exact qb_guard (qb_simSend P qep 1 hQu_QInr (fun _ _ _ _ => Nat.zero_lt_one)
      (fun _ _ _ _ _ _ => Nat.zero_lt_one) R m none r)
  · exact qb_guard (qb_simSend P qep 1 hQu_QInr (fun _ _ _ _ => Nat.zero_lt_one)
      (fun _ _ _ _ _ _ => Nat.zero_lt_one) R m₀ (some m₁) r)
  · exact qb_guard (qb_simRecv_none P encT decT qep 1
      (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) R w true)
  · exact qb_guard (qb_simRecv_none P encT decT qep 1
      (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) R w false)
  · exact qb_guard (qb_simCorr P Dh encT 1 (fun _ _ => Nat.zero_lt_one) R)

theorem sim_queries_proof (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep q : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (hq : SM.MakesAtMostQueries A q) :
    SM.MakesAtMostQueries (simRun P Dh encT decT qep none A) q := by
  unfold SM.MakesAtMostQueries simRun
  refine isQueryBoundP_congr (p := QInr Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind (isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QInr ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simImpl P Dh encT decT qep none) A).run
        (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QInr Pt ℓ) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp s
      · cases hp
      · exact qb_simImpl_none_inr P Dh encT decT qep o s
    · rintro (n | o) hnp s
      · exact qb_liftQ_query (fun h => absurd h (hQu_QInr n)) s
      · exact absurd rfl hnp
  rw [StateT.run'_eq, ← Nat.add_zero q]
  have hmap : IsQueryBoundP
      (Prod.fst <$> (simulateQ (simImpl P Dh encT decT qep none) A).run
        (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QInr Pt ℓ) q :=
    (isQueryBoundP_map_iff _ _ _).mpr hsim
  exact isQueryBoundP_bind hmap fun _ _ => trivial

end Queries

end CryptoGames.LibsignalSM.Proofs.QueryBounds
