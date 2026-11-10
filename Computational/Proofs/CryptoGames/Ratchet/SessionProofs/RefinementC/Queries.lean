/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Defs
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalRefinesCDefs
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.QueryBounds

/-!
# Query-count and equal-public-challenge bounds for `libsignalToModularSchemeSim`

Proves `simC_queries_proof` and `simC_equalPub_proof`, showing that `libsignalToModularSchemeSim`
makes at most one Fig. 8 query per adversary query and issues equal public parts in `chall` queries.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSectionVars false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

private def a5_QBC {ℓ : ℕ} (Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop) [DecidablePred Q]
    {α : Type} (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) (n : ℕ) : Prop :=
  ∀ sC : LibsignalToModularSchemeSimState PQ Pt ℓ, IsQueryBoundP (x.run sC) Q n

private theorem a5_qbc_pure {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} (a : α) (n : ℕ) : a5_QBC (PQ := PQ) Q (pure a) n := fun _ => by
  simp

private theorem a5_qbc_bind {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {n m : ℕ}
    (hx : a5_QBC Q x n) (hf : ∀ a, a5_QBC Q (f a) m) : a5_QBC Q (x >>= f) (n + m) := fun sC => by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (hx sC) fun p _ => hf p.1 p.2

private theorem a5_qbc_bind0 {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {m : ℕ}
    (hx : a5_QBC Q x 0) (hf : ∀ a, a5_QBC Q (f a) m) : a5_QBC Q (x >>= f) m := by
  simpa using a5_qbc_bind hx hf

private theorem a5_qbc_bind_r {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {n : ℕ}
    (hx : a5_QBC Q x n) (hf : ∀ a, a5_QBC Q (f a) 0) : a5_QBC Q (x >>= f) n := by
  simpa using a5_qbc_bind hx hf

private theorem a5_qbc_ite {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {c : Prop} [Decidable c] {α : Type}
    {x y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hx : a5_QBC Q x n) (hy : a5_QBC Q y n) : a5_QBC Q (if c then x else y) n := by
  by_cases hc : c <;> simp [hc, hx, hy]

private theorem a5_qbc_ite_pure {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {c : Prop} [Decidable c] {α : Type} {a : α}
    {y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hy : a5_QBC Q y n) : a5_QBC Q (if c then pure a else y) n :=
  a5_qbc_ite (a5_qbc_pure a n) hy

private theorem a5_qbc_get {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] :
    a5_QBC (PQ := PQ) Q (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ)) 0 :=
  fun _ => by simp

private theorem a5_qbc_set {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    a5_QBC Q (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit) 0 :=
  fun _ => by simp

private theorem a5_qbc_modify {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    a5_QBC Q (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit) 0 :=
  fun _ => by simp

private theorem a5_qbc_zoomB {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : QueryBounds.SimM PQ Pt ℓ α} {n : ℕ} (hx : QueryBounds.QB Q x n) :
    a5_QBC Q (runOnBaseState idHook x) n := fun sC => by
  show IsQueryBoundP (x.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 })) Q n
  simpa using hx sC.base

private theorem a5_qbc_liftC {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : Fig8Comp Pt ℓ α} {n : ℕ} (hx : IsQueryBoundP x Q n) :
    a5_QBC (PQ := PQ) Q (liftC idHook x) n := fun sC => by
  show IsQueryBoundP (x >>= fun a => pure (a, sC)) Q n
  simpa using isQueryBoundP_bind hx (fun a _ => isQueryBoundP_pure Q (a, sC) 0)

private theorem a5_qbc_liftC_query {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {t : (QueryBounds.FSpec Pt ℓ).Domain} {d : ℕ} (hd : Q t → 0 < d) :
    a5_QBC (PQ := PQ) Q (liftC idHook (query (spec := QueryBounds.FSpec Pt ℓ) t)) d :=
  a5_qbc_liftC ((isQueryBoundP_query_iff Q t d).2 hd)

private theorem a5_qbc_probe {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (R : Party) (c' : Fig8C Pt) (d : ℕ) :
    a5_QBC (PQ := PQ) Q (StateT.lift ((idHook (ℓ := ℓ)).probe R c')) d := fun sC => by
  show IsQueryBoundP (pure () >>= fun a => pure (a, sC)) Q d
  simp

private theorem a5_qbc_simSendC {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQu : ∀ u, ¬ Q (.inl u))
    (hQt : ∀ R pm rc, Q (.inr (.inl (.inl (.inl (.inl (R, pm, rc)))))) → 0 < d)
    (hQc : ∀ R pub m₀ m₁ rc, Q (.inr (.inl (.inl (.inl (.inr (R, (pub, m₀), (pub, m₁), rc)))))) → 0 < d)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    a5_QBC Q (simSendC P qep fig idHook R m₀ chal r) d := by
  unfold simSendC
  refine a5_qbc_bind_r (a5_qbc_zoomB (QueryBounds.qb_simSend P qep d hQu hQt hQc R m₀ chal r)) fun res => ?_
  cases res with
  | none => exact a5_qbc_pure none 0
  | some w =>
    refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
    exact a5_qbc_bind0 (a5_qbc_set _) fun _ => a5_qbc_pure (some w) 0

private theorem a5_qbc_fwdAnswerC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) :
    a5_QBC Q (fwdAnswerC qep fig fs idHook R w isDel ci? T pq' c') d := by
  unfold fwdAnswerC
  refine a5_qbc_bind_r (a5_qbc_zoomB (QueryBounds.qb_fwd d hQd hQi R c')) fun res => ?_
  cases res with
  | none => exact a5_qbc_zoomB (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' none)
  | some rr =>
    cases rr with
    | rejected => exact a5_qbc_zoomB (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' (some .rejected))
    | accepted t i pm =>
      exact a5_qbc_bind0 (a5_qbc_modify _) fun _ =>
        a5_qbc_zoomB (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' (some (.accepted t i pm)))

private theorem a5_qbc_resyncC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    a5_QBC Q (resyncC qep fig fs idHook R w ci? T pq' c r) d := by
  unfold resyncC
  cases r with
  | none => exact a5_qbc_pure (some RecvResult.rejected) d
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine a5_qbc_bind_r (a5_qbc_liftC_query (hQd R c)) fun res => ?_
    cases res with
    | none => exact a5_qbc_pure (some RecvResult.rejected) 0
    | some rr =>
      cases rr with
      | rejected => exact a5_qbc_pure (some RecvResult.rejected) 0
      | accepted _ _ _ =>
        exact a5_qbc_bind0 (a5_qbc_modify _) fun _ =>
          a5_qbc_zoomB (QueryBounds.qb_onAccept qep R w true t i pm.2 ci? T pq')

private theorem a5_qbc_fwdC {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    a5_QBC Q (fwdC P qep fig fs idHook R w isDel ci? T pq' honestC c') d := by
  unfold fwdC
  refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
  cases honestC with
  | none => exact a5_qbc_fwdAnswerC qep fig fs d hQd hQi R w isDel ci? T pq' c'
  | some c =>
    dsimp only
    refine a5_qbc_ite ?_ (a5_qbc_fwdAnswerC qep fig fs d hQd hQi R w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots fig fs P sC R w c c' with
    | some r => exact a5_qbc_resyncC qep fig fs d hQd R w ci? T pq' c r
    | none => exact a5_qbc_bind0 (a5_qbc_probe R c' 0) fun _ => a5_qbc_pure (some RecvResult.rejected) d

private theorem a5_qbc_fwdEvictC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) :
    a5_QBC Q (fwdEvictC qep fig fs idHook R w isDel T pq' c') d := by
  unfold fwdEvictC
  refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
  refine a5_qbc_ite ?_ (a5_qbc_fwdAnswerC qep fig fs d hQd hQi R w isDel none T pq' c')
  exact a5_qbc_bind0 (a5_qbc_probe R c' 0) fun _ => a5_qbc_pure (some RecvResult.rejected) d

private theorem a5_qbc_simRecvC {ℓ : ℕ} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQd : ∀ R c, Q (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, Q (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) :
    a5_QBC Q (simRecvC P encT decT qep fig fs idHook R w isDel) d := by
  unfold simRecvC
  refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
  dsimp only
  refine a5_qbc_ite_pure ?_
  refine a5_qbc_ite_pure ?_
  refine a5_qbc_ite_pure ?_
  refine a5_qbc_ite_pure ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact a5_qbc_pure (some RecvResult.rejected) d
  | some hp =>
    dsimp only
    refine a5_qbc_ite_pure ?_
    refine a5_qbc_ite_pure ?_
    cases P.spqr.recv (sC.base.pq R) hp.1.pqRatchet with
    | error _ => exact a5_qbc_pure (some RecvResult.rejected) d
    | ok ps =>
      dsimp only
      cases (sC.base.chains R).findIdx? (fun g => g.key == some hp.1.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine a5_qbc_ite_pure ?_
        exact a5_qbc_fwdC P qep fig fs d hQd hQi R w isDel (some ci) hp.1.senderRatchetKey ps.1 _ _
      | none =>
        dsimp only
        refine a5_qbc_ite_pure ?_
        refine a5_qbc_ite_pure ?_
        refine a5_qbc_ite (a5_qbc_bind0 (a5_qbc_modify _) fun _ => ?_) ?_ <;>
        · refine a5_qbc_ite_pure ?_
          cases decT hp.1.senderRatchetKey with
          | none => exact a5_qbc_pure (some RecvResult.rejected) d
          | some T =>
            exact a5_qbc_ite
              (a5_qbc_fwdEvictC qep fig fs d hQd hQi R w isDel hp.1.senderRatchetKey ps.1 _)
              (a5_qbc_fwdC P qep fig fs d hQd hQi R w isDel none hp.1.senderRatchetKey ps.1 _ _)

private theorem a5_qbc_simCorrC {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey)
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQcorr : ∀ R, Q (.inr (.inr R)) → 0 < d) (R : Party) :
    a5_QBC Q (simCorrC P encT idHook Dh R) d := by
  unfold simCorrC
  refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
  dsimp only
  refine a5_qbc_ite_pure ?_
  refine a5_qbc_bind_r (a5_qbc_liftC_query (hQcorr R)) fun res => ?_
  cases res with
  | none => exact a5_qbc_pure none 0
  | some st => exact a5_qbc_bind0 (a5_qbc_set _) fun _ => a5_qbc_pure _ 0

private theorem a5_qbc_guardC {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)} {n : ℕ}
    (hx : a5_QBC Q x n) : a5_QBC Q (guardC x) n := by
  unfold guardC
  refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
  split
  · exact a5_qbc_pure none n
  · exact hx

/-- `libsignalToModularSchemeSim` makes at most `q` Fig. 8 queries when `A` makes at most `q` queries. -/
theorem simC_queries_proof (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (A : LibAdv PQ PQC ℓ)
    (hq : SM.MakesAtMostQueries A q) :
    SM.MakesAtMostQueries (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) q := by
  unfold SM.MakesAtMostQueries Refine.libsignalToModularSchemeSim runLibsignalToModularSchemeSim simRunCWith
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  refine QueryBounds.isQueryBoundP_congr (p := QueryBounds.QInr Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) QueryBounds.hQu_QInr ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simImplC P encT decT qep fig fs idHook Dh) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QueryBounds.QInr Pt ℓ) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp sC
      · cases hp
      · rcases o with ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R)
        · exact a5_qbc_guardC (a5_qbc_simSendC P qep fig 1 QueryBounds.hQu_QInr
            (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one) R m none r) sC
        · exact a5_qbc_guardC (a5_qbc_simSendC P qep fig 1 QueryBounds.hQu_QInr
            (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one) R m₀ (some m₁) r) sC
        · exact a5_qbc_guardC (a5_qbc_simRecvC P encT decT qep fig fs 1
            (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) R w true) sC
        · exact a5_qbc_guardC (a5_qbc_simRecvC P encT decT qep fig fs 1
            (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one) R w false) sC
        · exact a5_qbc_guardC (a5_qbc_simCorrC P Dh encT 1 (fun _ _ => Nat.zero_lt_one) R) sC
    · rintro (n | o) hnp sC
      · exact a5_qbc_liftC_query (fun h => absurd h (QueryBounds.hQu_QInr n)) sC
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

/-- `libsignalToModularSchemeSim` issues `chall` queries with identical public message parts. -/
theorem simC_equalPub_proof (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) :
    SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
      (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) := by
  unfold SM.EqualPubChalls Refine.libsignalToModularSchemeSim runLibsignalToModularSchemeSim simRunCWith
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  change IsQueryBoundP _ (QueryBounds.QEq Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) QueryBounds.hQu_QEq ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hQt : ∀ R pm rc, QueryBounds.QEq Pt ℓ (.inr (.inl (.inl (.inl (.inl (R, pm, rc)))))) → 0 < 0 := by
    intro _ _ _ h; nomatch h
  have hQc : ∀ R pub m₀ m₁ rc,
      QueryBounds.QEq Pt ℓ (.inr (.inl (.inl (.inl (.inr (R, (pub, m₀), (pub, m₁), rc)))))) → 0 < 0 := by
    intro _ _ _ _ _ h
    simp [QueryBounds.QEq, SM.unequalPubChall] at h
  have hQd : ∀ R c, QueryBounds.QEq Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) → 0 < 0 := by
    intro _ _ h; nomatch h
  have hQi : ∀ R c, QueryBounds.QEq Pt ℓ (.inr (.inl (.inr (R, c)))) → 0 < 0 := by
    intro _ _ h; nomatch h
  have hQcorr : ∀ R, QueryBounds.QEq Pt ℓ (.inr (.inr R)) → 0 < 0 := by
    intro _ h; nomatch h
  have hsim : IsQueryBoundP
      ((simulateQ (simImplC P encT decT qep fig fs idHook Dh) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QueryBounds.QEq Pt ℓ) 0 := by
    refine QueryBounds.isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
    rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
    · exact a5_qbc_liftC_query (fun h => absurd h (QueryBounds.hQu_QEq n)) sC
    · exact a5_qbc_guardC (a5_qbc_simSendC P qep fig 0 QueryBounds.hQu_QEq hQt hQc R m none r) sC
    · exact a5_qbc_guardC (a5_qbc_simSendC P qep fig 0 QueryBounds.hQu_QEq hQt hQc R m₀ (some m₁) r) sC
    · exact a5_qbc_guardC (a5_qbc_simRecvC P encT decT qep fig fs 0 hQd hQi R w true) sC
    · exact a5_qbc_guardC (a5_qbc_simRecvC P encT decT qep fig fs 0 hQd hQi R w false) sC
    · exact a5_qbc_guardC (a5_qbc_simCorrC P Dh encT 0 hQcorr R) sC
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

end CryptoGames.LibsignalSM.Proofs.Refinement
