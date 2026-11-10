/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.HiddenSaltBound
public import Computational.Proofs.ReductionDsl.Fig8Atomic
public import Computational.Proofs.SessionCostedFig8
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalRefinesCDefs
public import Computational.Specifications.Session.StatementIdsModel
import Computational.Proofs.SpqrV1Sync.SendTotalExtras
import ProofLib.SepLogic.WP.StateNorm
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Short-message and query bounds for the V1 headline simulators

**Checked by Lean.** Proves `LengthsOk` and `AtomicLengthsOk` for `spqrV1SessionUniformCoins`,
together with query-count and short-message bounds for `libsignalToModularSchemeSim`,
`simDeliverForge`, `DeliverForge.challSimDF`, and `DeliverForge.redFSAuthDF`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopStmts spqrV1Send_msg_len_le)
open CryptoVerification.E2E (partyIdentityKey paramsIdsWithSpqr serializedPartyAddresses
  partyAddressName Bytes)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser serviceIdParse utf8 addrBytes)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC CryptoGames.LibsignalSM.Proofs
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

/-! ## `LengthsOk` for `spqrV1SessionUniformCoins` -/

private theorem addrsE_length (uuidParse : UuidParser) (s r : Party) (a : List (BitVec 8))
    (h : serializedPartyAddresses uuidParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : serviceIdParse uuidParse (utf8 (partyAddressName s)) <;>
    cases hr : serviceIdParse uuidParse (utf8 (partyAddressName r)) <;> simp_all [addrBytes]
  subst h
  simp

private theorem lengthsOk_paramsIdsWithSpqr {PQC : Type} (C : Crypto) (spqr : Spqr Bytes PQC)
    (idA idB : IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 2 ^ 31)
    (hLspqr : ∀ st rq st' salt msg, spqr.send st rq = some (st', salt, msg) →
      msg.length < 2 ^ 29) :
    LengthsOk (paramsIdsWithSpqr C spqr idA idB) ℓ := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro st rq st' salt msg h
    exact hLspqr st rq st' salt msg h
  · intro a h
    rw [addrsE_length _ _ _ a h]; decide
  · intro a h
    rw [addrsE_length _ _ _ a h]; decide

/-- `paramsIdsWithSpqr` with `spqrV1SessionUniformCoins` satisfies `LengthsOk` when `ℓ < 10 ^ 6`. -/
theorem lengthsOk_paramsIdsWithSpqr_v1 (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    LengthsOk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ :=
  lengthsOk_paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB ℓ (by omega)
    (fun st r st' salt pm h =>
      Nat.lt_of_le_of_lt (spqrV1Send_msg_len_le C.F K st r st' salt pm h) (by decide))

/-! ## Short-message bounds for `libsignalToModularSchemeSim` -/

private def a5_QBC {ℓ : ℕ} (Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop) [DecidablePred Q]
    {α : Type} (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) (n : ℕ) : Prop :=
  ∀ sC : LibsignalToModularSchemeSimState PQ Pt ℓ, IsQueryBoundP (x.run sC) Q n

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_pure {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} (a : α) (n : ℕ) : a5_QBC (PQ := PQ) Q (pure a) n := fun _ => by
  simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_bind {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {n m : ℕ}
    (hx : a5_QBC Q x n) (hf : ∀ a, a5_QBC Q (f a) m) : a5_QBC Q (x >>= f) (n + m) := fun sC => by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (hx sC) fun p _ => hf p.1 p.2

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_bind0 {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {m : ℕ}
    (hx : a5_QBC Q x 0) (hf : ∀ a, a5_QBC Q (f a) m) : a5_QBC Q (x >>= f) m := by
  simpa using a5_qbc_bind hx hf

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_bind_r {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β} {n : ℕ}
    (hx : a5_QBC Q x n) (hf : ∀ a, a5_QBC Q (f a) 0) : a5_QBC Q (x >>= f) n := by
  simpa using a5_qbc_bind hx hf

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_ite {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {c : Prop} [Decidable c] {α : Type}
    {x y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hx : a5_QBC Q x n) (hy : a5_QBC Q y n) : a5_QBC Q (if c then x else y) n := by
  by_cases hc : c <;> simp [hc, hx, hy]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_ite_pure {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop}
    [DecidablePred Q] {c : Prop} [Decidable c] {α : Type} {a : α}
    {y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hy : a5_QBC Q y n) : a5_QBC Q (if c then pure a else y) n :=
  a5_qbc_ite (a5_qbc_pure a n) hy

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_get {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] :
    a5_QBC (PQ := PQ) Q (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ)) 0 :=
  fun _ => by simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_set {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    a5_QBC Q (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit) 0 :=
  fun _ => by simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_modify {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    a5_QBC Q (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit) 0 :=
  fun _ => by simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_zoomB {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : QueryBounds.SimM PQ Pt ℓ α} {n : ℕ} (hx : QueryBounds.QB Q x n) :
    a5_QBC Q (runOnBaseState idHook x) n := fun sC => by
  show IsQueryBoundP (x.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 })) Q n
  simpa using hx sC.base

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_liftC {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : Fig8Comp Pt ℓ α} {n : ℕ} (hx : IsQueryBoundP x Q n) :
    a5_QBC (PQ := PQ) Q (liftC idHook x) n := fun sC => by
  show IsQueryBoundP (x >>= fun a => pure (a, sC)) Q n
  rw [← Nat.add_zero n]
  exact isQueryBoundP_bind hx (fun a _ => isQueryBoundP_pure Q (a, sC) 0)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_liftC_query {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop}
    [DecidablePred Q] {t : (QueryBounds.FSpec Pt ℓ).Domain} {d : ℕ} (hd : Q t → 0 < d) :
    a5_QBC (PQ := PQ) Q (liftC idHook (query (spec := QueryBounds.FSpec Pt ℓ) t)) d :=
  a5_qbc_liftC ((isQueryBoundP_query_iff Q t d).2 hd)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_probe {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (R : Party) (c' : Fig8C Pt) (d : ℕ) :
    a5_QBC (PQ := PQ) Q (StateT.lift ((idHook (ℓ := ℓ)).probe R c')) d := fun sC => by
  show IsQueryBoundP (pure () >>= fun a => pure (a, sC)) Q d
  simp

omit [SampleableType Pt] in
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
    | rejected =>
      exact a5_qbc_zoomB (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' (some .rejected))
    | accepted t i pm =>
      exact a5_qbc_bind0 (a5_qbc_modify _) fun _ =>
        a5_qbc_zoomB (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' (some (.accepted t i pm)))

omit [SampleableType Pt] in
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

omit [SampleableType Pt] [SampleableType PQC] in
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
    a5_QBC Q (LibsignalSimC.fwdC P qep fig fs idHook R w isDel ci? T pq' honestC c') d := by
  unfold LibsignalSimC.fwdC
  refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
  cases honestC with
  | none => exact a5_qbc_fwdAnswerC qep fig fs d hQd hQi R w isDel ci? T pq' c'
  | some c =>
    dsimp only
    refine a5_qbc_ite ?_ (a5_qbc_fwdAnswerC qep fig fs d hQd hQi R w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots fig fs P sC R w c c' with
    | some r => exact a5_qbc_resyncC qep fig fs d hQd R w ci? T pq' c r
    | none =>
      exact a5_qbc_bind0 (a5_qbc_probe R c' 0) fun _ => a5_qbc_pure (some RecvResult.rejected) d

omit [SampleableType Pt] in
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

omit [SampleableType Pt] [SampleableType PQC] in
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
  unfold LibsignalSimC.simRecvC
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

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a5_qbc_simCorrC {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey)
    {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q] (d : ℕ)
    (hQcorr : ∀ R, Q (.inr (.inr R)) → 0 < d) (R : Party) :
    a5_QBC Q (simCorrC P encT idHook Dh R) d := by
  unfold LibsignalSimC.simCorrC
  refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
  dsimp only
  refine a5_qbc_ite_pure ?_
  refine a5_qbc_bind_r (a5_qbc_liftC_query (hQcorr R)) fun res => ?_
  cases res with
  | none => exact a5_qbc_pure none 0
  | some st => exact a5_qbc_bind0 (a5_qbc_set _) fun _ => a5_qbc_pure _ 0

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a5_qbc_guardC {ℓ : ℕ} {Q : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)} {n : ℕ}
    (hx : a5_QBC Q x n) : a5_QBC Q (guardC x) n := by
  unfold LibsignalSimC.guardC
  refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
  split
  · exact a5_qbc_pure none n
  · exact hx

omit [SampleableType Pt] in
private theorem a5_qbc_simSendC_short {ℓ : ℕ} (P : Params PQ PQC) (hL : LengthsOk P ℓ) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    a5_QBC (Proofs.SessionShort.SimAndSM.QShort Pt ℓ)
      (simSendC P qep fig idHook R m₀ chal r) 0 := by
  unfold LibsignalSimC.simSendC
  refine a5_qbc_bind_r (a5_qbc_zoomB
    (Proofs.SessionShort.SimAndSM.qb_simSend_QShort (Pt := Pt) P hL qep R m₀ chal r)) fun res => ?_
  cases res with
  | none => exact a5_qbc_pure none 0
  | some w =>
    refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
    exact a5_qbc_bind0 (a5_qbc_set _) fun _ => a5_qbc_pure (some w) 0

omit [SampleableType Pt] in
/-- Under `LengthsOk P ℓ`, every `transmit` or `chall` message of `libsignalToModularSchemeSim`
satisfies `shortB`. -/
theorem simC_sendShort (P : Params PQ PQC) (ℓ : ℕ) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    Proofs.SessionShort.SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) := by
  have hmain : IsQueryBoundP (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)
      (Proofs.SessionShort.SimAndSM.QShort Pt ℓ) 0 := by
    unfold Refine.libsignalToModularSchemeSim runLibsignalToModularSchemeSim simRunCWith
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    rw [← Nat.zero_add 0]
    refine isQueryBoundP_bind (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ)
      Proofs.SessionShort.SimAndSM.hQu_QShort ($ᵗ BitVec 256)) fun pqrKey _ => ?_
    have hQd : ∀ R c, Proofs.SessionShort.SimAndSM.QShort Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) →
        0 < 0 := by
      intro _ _ h; nomatch h
    have hQi : ∀ R c, Proofs.SessionShort.SimAndSM.QShort Pt ℓ (.inr (.inl (.inr (R, c)))) →
        0 < 0 := by
      intro _ _ h; nomatch h
    have hQcorr : ∀ R, Proofs.SessionShort.SimAndSM.QShort Pt ℓ (.inr (.inr R)) → 0 < 0 := by
      intro _ h; nomatch h
    have hsim : IsQueryBoundP
        ((simulateQ (simImplC P encT decT qep fig fs idHook Dh) A).run
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
        (Proofs.SessionShort.SimAndSM.QShort Pt ℓ) 0 := by
      refine QueryBounds.isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
      rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
      · exact a5_qbc_liftC_query
          (fun h => absurd h (Proofs.SessionShort.SimAndSM.hQu_QShort n)) sC
      · exact a5_qbc_guardC (a5_qbc_simSendC_short P hL qep fig R m none r) sC
      · exact a5_qbc_guardC (a5_qbc_simSendC_short P hL qep fig R m₀ (some m₁) r) sC
      · exact a5_qbc_guardC (a5_qbc_simRecvC P encT decT qep fig fs 0 hQd hQi R w true) sC
      · exact a5_qbc_guardC (a5_qbc_simRecvC P encT decT qep fig fs 0 hQd hQi R w false) sC
      · exact a5_qbc_guardC (a5_qbc_simCorrC P Dh encT 0 hQcorr R) sC
    rw [StateT.run'_eq]
    exact (isQueryBoundP_map_iff _ _ _).mpr hsim
  unfold Proofs.SessionShort.SendMsgsOk
  exact QueryBounds.isQueryBoundP_congr (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) hmain

section SimCGuarded

open GuardedSafe
open Proofs.SessionShort.SimAndSM
  (smRespShort smRecvLong SimShortInv simShortInv_initSim hQu_smRecvLong
   inTransit_mem_and_ct guardedSafeS_simSend guardedSafeS_fwd
   guardedSafeS_onAccept guardedSafeS_onAnswer)

private abbrev SimCShortInv {ℓ : ℕ} (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : Prop :=
  SimShortInv sC.base

private abbrev SimCSafeS {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) : Prop :=
  GuardedSafeS
    (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (T := Pt))
    (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (T := Pt))
    (SimCShortInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ))
    (fun _ sC => SimCShortInv sC) x

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem simCSafeS_ite {ℓ : ℕ} {α : Type} {c : Prop} [Decidable c]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    (ht : SimCSafeS t) (he : SimCSafeS e) :
    SimCSafeS (if c then t else e) := by
  split
  · exact ht
  · exact he

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem simCSafeS_ite_pure {ℓ : ℕ} {α : Type} {c : Prop} [Decidable c] {a : α}
    {e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    (he : ¬ c → SimCSafeS e) :
    SimCSafeS (if c then pure a else e) := by
  split
  · exact guardedSafeS_pure_true a
  · rename_i hc; exact he hc

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem simCSafeS_zoomB {ℓ : ℕ} {α : Type}
    {x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    (hx : Proofs.SessionShort.SimAndSM.SimSafeS PQ Pt ℓ x) :
    SimCSafeS (runOnBaseState idHook x) := fun sC hsC => by
  show GuardedSafePost _ _ _ (x.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 }))
  exact (hx sC.base hsC).bind fun p hp =>
    GuardedSafePost.pure
      (P := fun r : α × LibsignalToModularSchemeSimState PQ Pt ℓ => SimCShortInv r.2) hp

omit [SampleableType Pt] in
private theorem simCSafeS_simSendC {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    SimCSafeS (simSendC P qep fig idHook R m₀ chal r) := by
  unfold LibsignalSimC.simSendC
  refine guardedSafeS_bind_true (simCSafeS_zoomB (guardedSafeS_simSend P qep R m₀ chal r))
    fun res => ?_
  cases res with
  | none => exact guardedSafeS_pure_true none
  | some w =>
    refine guardedSafeS_get_bind fun _ hsC => ?_
    exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => hsC)
      fun _ => guardedSafeS_pure_true (some w)

omit [SampleableType Pt] [SampleableType PQC] in
private theorem simCSafeS_fwdAnswerC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    SimCSafeS (fwdAnswerC qep fig fs idHook R w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine guardedSafeS_bind_true (simCSafeS_zoomB (guardedSafeS_fwd R c' hc')) fun res => ?_
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact simCSafeS_zoomB (guardedSafeS_onAnswer qep R w isDel ci? T pq' none)
  · exact simCSafeS_zoomB (guardedSafeS_onAnswer qep R w isDel ci? T pq' (some .rejected))
  · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ hsC => hsC) fun _ =>
      simCSafeS_zoomB (guardedSafeS_onAnswer qep R w isDel ci? T pq' (some (.accepted t i pm)))

omit [SampleableType Pt] [SampleableType PQC] in
private theorem simCSafeS_resyncC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (R : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    SimCSafeS (resyncC qep fig fs idHook R w ci? T pq' c r) := by
  unfold resyncC LibsignalSimC.liftC idHook SM.deliverQuery
  dsimp only
  rcases r with _ | ⟨t, i, pm⟩
  · exact guardedSafeS_pure_true (some RecvResult.rejected)
  · refine guardedSafeS_bind_query (Q := smRecvLong) (fun h => h hc) fun res _ => ?_
    rcases res with _ | (_ | ⟨_, _, _⟩)
    · exact guardedSafeS_pure_true (some RecvResult.rejected)
    · exact guardedSafeS_pure_true (some RecvResult.rejected)
    · exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ hsC => hsC) fun _ =>
        simCSafeS_zoomB (guardedSafeS_onAccept qep R w true t i pm.2 ci? T pq')

omit [SampleableType Pt] [SampleableType PQC] in
private theorem simCSafeS_fwdC {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (Fig8C Pt))
    (hhon : ∀ c, honestC = some c → c.2.2.1.1.length < 2 ^ 32)
    (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    SimCSafeS (LibsignalSimC.fwdC P qep fig fs idHook R w isDel ci? T pq' honestC c') := by
  unfold LibsignalSimC.fwdC
  refine guardedSafeS_get_bind fun sC _ => ?_
  cases honestC with
  | none => exact simCSafeS_fwdAnswerC qep fig fs R w isDel ci? T pq' c' hc'
  | some c =>
    dsimp only
    refine simCSafeS_ite ?_ (simCSafeS_fwdAnswerC qep fig fs R w isDel ci? T pq' c' hc')
    cases predictReceiveWithSnapshots fig fs P sC R w c c' with
    | some r => exact simCSafeS_resyncC qep fig fs R w ci? T pq' c (hhon c rfl) r
    | none =>
      dsimp only [idHook]
      exact guardedSafeS_bind_true (guardedSafeS_lift_true (GuardedSafePost.pure trivial))
        fun _ => guardedSafeS_pure_true (some RecvResult.rejected)

omit [SampleableType Pt] [SampleableType PQC] in
private theorem simCSafeS_fwdEvictC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    SimCSafeS (fwdEvictC qep fig fs idHook R w isDel T pq' c') := by
  unfold fwdEvictC
  refine guardedSafeS_get_bind fun _ _ => ?_
  refine simCSafeS_ite ?_ (simCSafeS_fwdAnswerC qep fig fs R w isDel none T pq' c' hc')
  dsimp only [idHook]
  exact guardedSafeS_bind_true (guardedSafeS_lift_true (GuardedSafePost.pure trivial))
    fun _ => guardedSafeS_pure_true (some RecvResult.rejected)

omit [SampleableType Pt] [SampleableType PQC] in
private theorem simCSafeS_simRecvC {ℓ : ℕ} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) :
    SimCSafeS (simRecvC P encT decT qep fig fs idHook R w isDel) := by
  unfold LibsignalSimC.simRecvC
  refine guardedSafeS_get_bind fun sC hsC => ?_
  dsimp only
  refine simCSafeS_ite_pure fun _ => ?_
  refine simCSafeS_ite_pure fun hw2 => ?_
  refine simCSafeS_ite_pure fun hw3 => ?_
  refine simCSafeS_ite_pure fun hw4 => ?_
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, rest⟩
  · exact guardedSafeS_pure_true (some RecvResult.rejected)
  · have hwlen : w.length < 2 ^ 32 := by
      cases isDel with
      | true =>
        rcases htr : sC.base.mir.inTransit R.other w with _ | rec'
        · simp [htr] at hw2
        · obtain ⟨hmem, rfl⟩ := inTransit_mem_and_ct htr
          exact hsC.1 rec' hmem
      | false =>
        simp only [Bool.not_false, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true',
          not_or, Bool.not_eq_false] at hw3
        have hadm := hw3.2
        unfold ratchetKeyAdmissible at hadm
        simp only [hw4, ↓reduceIte, hparse, Bool.and_eq_true, decide_eq_true_eq] at hadm
        exact hadm.1
    have hser : (w.take (w.length - 8)).length < 2 ^ 32 := by
      rw [List.length_take]; omega
    dsimp only
    refine simCSafeS_ite_pure fun _ => ?_
    refine simCSafeS_ite_pure fun _ => ?_
    rcases P.spqr.recv (sC.base.pq R) h.pqRatchet with _ | ⟨pq', salt⟩
    · exact guardedSafeS_pure_true (some RecvResult.rejected)
    · dsimp only
      have hhon : ∀ c : Fig8C Pt,
          (sC.base.honest.find? fun (wc : List (BitVec 8) × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == R.other).map
              (fun (wc : List (BitVec 8) × Fig8C Pt) => wc.2) = some c →
          c.2.2.1.1.length < 2 ^ 32 := by
        intro c hc_eq
        rcases Option.mem_map.mp hc_eq with ⟨wc, hfind, rfl⟩
        exact hsC.2 wc (List.mem_of_find?_eq_some hfind)
      have hmkC : ∀ (t : ℕ) (To : Option Pt),
          (match (sC.base.honest.find? fun (wc : List (BitVec 8) × Fig8C Pt) =>
               wc.1 == w && Party.senderOf wc.2.1.1 == R.other).map
                 (fun (wc : List (BitVec 8) × Fig8C Pt) => wc.2) with
           | some (c : Fig8C Pt) =>
             if c.2.2.2 = effectiveHkdfSalt32 salt then c
             else ((t, To), (h.counter.toNat + 1, ((w.take (w.length - 8),
               bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
           | none =>
             ((t, To), (h.counter.toNat + 1, ((w.take (w.length - 8),
               bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))).2.2.1.1.length <
            2 ^ 32 := by
        intro t To
        rcases hfind : sC.base.honest.find? (fun (wc : List (BitVec 8) × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == R.other) with _ | wc
        · exact hser
        · simp only [Option.map]
          split
          · exact hsC.2 wc (List.mem_of_find?_eq_some hfind)
          · exact hser
      cases (sC.base.chains R).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine simCSafeS_ite_pure fun _ => ?_
        exact simCSafeS_fwdC P qep fig fs R w isDel (some ci) h.senderRatchetKey pq' _ hhon _
          (hmkC _ _)
      | none =>
        dsimp only
        refine simCSafeS_ite_pure fun _ => ?_
        refine simCSafeS_ite_pure fun _ => ?_
        refine simCSafeS_ite
          (guardedSafeS_bind_true
            (guardedSafeS_modify_true _ fun _ hsC' => ⟨hsC'.1, hsC'.2⟩) fun _ => ?_) ?_ <;>
        · refine simCSafeS_ite_pure fun _ => ?_
          cases decT h.senderRatchetKey with
          | none => exact guardedSafeS_pure_true (some RecvResult.rejected)
          | some T =>
            exact simCSafeS_ite
              (simCSafeS_fwdEvictC qep fig fs R w isDel h.senderRatchetKey pq' _ hser)
              (simCSafeS_fwdC P qep fig fs R w isDel none h.senderRatchetKey pq' _ hhon _
                (hmkC _ _))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem simCSafeS_simCorrC {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (R : Party) :
    SimCSafeS (simCorrC P encT (idHook (ℓ := ℓ)) Dh R) := by
  unfold LibsignalSimC.simCorrC LibsignalSimC.liftC idHook SM.corrQuery
  refine guardedSafeS_get_bind fun _ hs0 => ?_
  dsimp only
  refine simCSafeS_ite_pure fun _ => ?_
  refine guardedSafeS_bind_query (Q := smRecvLong) not_false fun res _ => ?_
  cases res with
  | none => exact guardedSafeS_pure_true none
  | some st =>
    exact guardedSafeS_bind_true
      (guardedSafeS_set_true _ fun _ _ => ⟨hs0.1, hs0.2⟩)
      fun _ => guardedSafeS_pure_true _

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem simCSafeS_guardC {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)}
    (hx : SimCSafeS x) :
    GuardedSafeS
      (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (T := Pt))
      (SimCShortInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ))
      (fun _ sC => True ∧ SimCShortInv sC)
      (guardC x) := by
  unfold LibsignalSimC.guardC
  refine guardedSafeS_get_bind fun _ _ => ?_
  split
  · exact guardedSafeS_pure none fun _ hsC => ⟨trivial, hsC⟩
  · exact fun sC hsC => (hx sC hsC).mono fun _ hp => ⟨trivial, hp⟩

omit [SampleableType Pt] in
/-- `libsignalToModularSchemeSim` satisfies `GuardedSMShort`. -/
theorem simC_guardedSMShort (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    Proofs.SessionShort.GuardedSMShort
      (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) := by
  unfold Proofs.SessionShort.SimAndSM.GuardedSMShort
    Refine.libsignalToModularSchemeSim runLibsignalToModularSchemeSim simRunCWith
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  refine (GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ BitVec 256)).bind fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost smRespShort smRecvLong (fun r => SimCShortInv r.2)
      ((simulateQ (simImplC P encT decT qep fig fs idHook Dh) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) := by
    refine GuardedSafePost.simulateQ_run (GuardedSafePost.true_of_false A) ?_
      (simShortInv_initSim _ _)
    rintro (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R)) _
    · exact fun sC hsC =>
        (GuardedSafePost.query (hQu_smRecvLong n)).bind fun _ _ =>
          GuardedSafePost.pure ⟨trivial, hsC⟩
    · exact simCSafeS_guardC (simCSafeS_simSendC P qep fig R m none r)
    · exact simCSafeS_guardC (simCSafeS_simSendC P qep fig R m₀ (some m₁) r)
    · exact simCSafeS_guardC (simCSafeS_simRecvC P encT decT qep fig fs R w true)
    · exact simCSafeS_guardC (simCSafeS_simRecvC P encT decT qep fig fs R w false)
    · exact simCSafeS_guardC (simCSafeS_simCorrC P Dh encT R)
  exact hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial

end SimCGuarded

/-! ## Query and short-message bounds for `DeliverForge` simulators -/

/-- Oracle specification for a Fig. 8 `DeliverForge` adversary. -/
abbrev DFSpec (Pt : Type) (ℓ : ℕ) :=
  unifSpec + DeliverForge.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)

def toDFDom {Pt : Type} {ℓ : ℕ} : (QueryBounds.FSpec Pt ℓ).Domain → (DFSpec Pt ℓ).Domain
  | .inl n => .inl n
  | .inr q => .inr (.inl q)

def badSendMsgDF {St Msg Coins C : Type} (ok : Msg → Bool) :
    (unifSpec + DeliverForge.specDF St Msg Coins C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl (.inl ⟨_, m, _⟩))))) => !ok m
  | .inr (.inl (.inl (.inl (.inl (.inr ⟨_, m₀, m₁, _⟩))))) => !ok m₀ || !ok m₁
  | _ => false

/-- Every `transmit` or `chall` message of `A` satisfies `ok`. -/
def SendMsgsOkDF {St Msg Coins C : Type} (ok : Msg → Bool)
    (A : DeliverForge.AdversaryDF St Msg Coins C) : Prop :=
  A.IsQueryBoundP (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) ok t = true) 0

def unequalPubChallDF {St Msg Coins C Pub : Type} [DecidableEq Pub] (pubOf : Msg → Pub) :
    (unifSpec + DeliverForge.specDF St Msg Coins C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl (.inr ⟨_, m₀, m₁, _⟩))))) => decide (pubOf m₀ ≠ pubOf m₁)
  | _ => false

/-- Every `chall` query of `A` has equal public parts. -/
def EqualPubChallsDF {St Msg Coins C Pub : Type} [DecidableEq Pub] (pubOf : Msg → Pub)
    (A : DeliverForge.AdversaryDF St Msg Coins C) : Prop :=
  A.IsQueryBoundP (fun t => unequalPubChallDF (St := St) (Coins := Coins) (C := C) pubOf t = true) 0

def df_QBC {ℓ : ℕ} (Q : (DFSpec Pt ℓ).Domain → Prop) [DecidablePred Q]
    {α : Type} (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) α)
    (n : ℕ) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt)),
    IsQueryBoundP ((x.run sC).run sent) Q n

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_pure {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type} (a : α) (n : ℕ) : df_QBC (PQ := PQ) Q (pure a) n := fun _ _ => by
  simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_bind {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) β}
    {n m : ℕ} (hx : df_QBC Q x n) (hf : ∀ a, df_QBC Q (f a) m) :
    df_QBC Q (x >>= f) (n + m) := fun sC sent => by
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (hx sC sent) fun p _ => hf p.1.1 p.1.2 p.2

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_bind0 {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) β}
    {m : ℕ} (hx : df_QBC Q x 0) (hf : ∀ a, df_QBC Q (f a) m) :
    df_QBC Q (x >>= f) m := by
  simpa using df_qbc_bind hx hf

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_bind_r {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α β : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) β}
    {n : ℕ} (hx : df_QBC Q x n) (hf : ∀ a, df_QBC Q (f a) 0) :
    df_QBC Q (x >>= f) n := by
  simpa using df_qbc_bind hx hf

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_ite {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {c : Prop} [Decidable c] {α : Type}
    {x y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) α} {n : ℕ}
    (hx : df_QBC Q x n) (hy : df_QBC Q y n) : df_QBC Q (if c then x else y) n := by
  by_cases hc : c <;> simp [hc, hx, hy]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_ite_pure {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {c : Prop} [Decidable c] {α : Type} {a : α}
    {y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) α} {n : ℕ}
    (hy : df_QBC Q y n) : df_QBC Q (if c then pure a else y) n :=
  df_qbc_ite (df_qbc_pure a n) hy

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_get {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q] :
    df_QBC (PQ := PQ) Q
      (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) (LibsignalToModularSchemeSimState PQ Pt ℓ))
      0 :=
  fun _ _ => by simp

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_set {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    df_QBC Q
      (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) PUnit) 0 :=
  fun _ _ => by simp


omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem isQueryBoundP_fig8ToDFImpl_step {ℓ : ℕ}
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (t : (QueryBounds.FSpec Pt ℓ).Domain) (d : ℕ) (hd : Q (toDFDom t) → 0 < d)
    (sent : List (Fig8C Pt)) :
    IsQueryBoundP ((Proofs.Refinement.fig8ToDFImpl Pt ℓ t).run sent) Q d := by
  have hq : IsQueryBoundP (query (spec := DFSpec Pt ℓ) (toDFDom t)) Q d :=
    (isQueryBoundP_query_iff Q (toDFDom t) d).2 hd
  rw [← Nat.add_zero d]
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, c⟩) | ⟨R, c⟩) | R))
  · show IsQueryBoundP (query (spec := DFSpec Pt ℓ) (toDFDom (.inl n)) >>=
      fun a => pure (a, sent)) Q (d + 0)
    exact isQueryBoundP_bind hq fun a _ => isQueryBoundP_pure Q (a, sent) 0
  · unfold Proofs.Refinement.fig8ToDFImpl DeliverForge.transmitQueryDF
    rw [StateT.run_bind]
    have hlift : IsQueryBoundP
        ((StateT.lift (query (spec := DFSpec Pt ℓ)
            (toDFDom (.inr (.inl (.inl (.inl (.inl (R, m, r)))))))) :
          Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) Q d := by
      show IsQueryBoundP (query (spec := DFSpec Pt ℓ) _ >>= fun a => pure (a, sent)) Q d
      rw [← Nat.add_zero d]
      exact isQueryBoundP_bind hq fun a _ => isQueryBoundP_pure Q (a, sent) 0
    refine isQueryBoundP_bind hlift fun p _ => ?_
    rcases p with ⟨res, sent'⟩
    cases res <;> simp
  · unfold Proofs.Refinement.fig8ToDFImpl DeliverForge.challQueryDF
    rw [StateT.run_bind]
    have hlift : IsQueryBoundP
        ((StateT.lift (query (spec := DFSpec Pt ℓ)
            (toDFDom (.inr (.inl (.inl (.inl (.inr (R, m₀, m₁, r)))))))) :
          Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) Q d := by
      show IsQueryBoundP (query (spec := DFSpec Pt ℓ) _ >>= fun a => pure (a, sent)) Q d
      rw [← Nat.add_zero d]
      exact isQueryBoundP_bind hq fun a _ => isQueryBoundP_pure Q (a, sent) 0
    refine isQueryBoundP_bind hlift fun p _ => ?_
    rcases p with ⟨res, sent'⟩
    cases res <;> simp
  · show IsQueryBoundP (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inl (.inl (.inr (R, c)))))) >>= fun a => pure (a, sent)) Q (d + 0)
    exact isQueryBoundP_bind hq fun a _ => isQueryBoundP_pure Q (a, sent) 0
  · show IsQueryBoundP (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inl (.inr (R, c))))) >>= fun a => pure (a, sent)) Q (d + 0)
    exact isQueryBoundP_bind hq fun a _ => isQueryBoundP_pure Q (a, sent) 0
  · show IsQueryBoundP (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inr R))) >>= fun a => pure (a, sent)) Q (d + 0)
    exact isQueryBoundP_bind hq fun a _ => isQueryBoundP_pure Q (a, sent) 0

omit [Zero Pt] [SampleableType Pt] in
private theorem isQueryBoundP_deliverForgeHook_lift {ℓ : ℕ}
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t)
    {α : Type} {x : Fig8Comp Pt ℓ α} {n : ℕ} (hx : IsQueryBoundP x QFig n)
    (sent : List (Fig8C Pt)) :
    IsQueryBoundP (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift x).run sent) Q n := by
  dsimp only [Proofs.Refinement.deliverForgeHook]
  simpa only [Nat.one_mul] using
    ReductionsQueries.simulateQ_run_of_step_mul (k := 1) hx
      (fun t _ s => isQueryBoundP_fig8ToDFImpl_step t 1 (fun _ => Nat.zero_lt_one) s)
      (fun t ht s => isQueryBoundP_fig8ToDFImpl_step t 0 (fun h => absurd ((hQ t).mp h) ht) s)
      sent

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_liftC {ℓ : ℕ}
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t)
    {α : Type} {x : Fig8Comp Pt ℓ α} {n : ℕ} (hx : IsQueryBoundP x QFig n) :
    df_QBC (PQ := PQ) Q (liftC (Proofs.Refinement.deliverForgeHook Pt ℓ) x) n := fun sC sent => by
  show IsQueryBoundP
    (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift x >>= fun a => pure (a, sC)).run sent) Q n
  rw [StateT.run_bind, ← Nat.add_zero n]
  exact isQueryBoundP_bind (isQueryBoundP_deliverForgeHook_lift hQ hx sent)
    fun p _ => isQueryBoundP_pure Q ((p.1, sC), p.2) 0

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_liftC_query {ℓ : ℕ}
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t)
    {t : (QueryBounds.FSpec Pt ℓ).Domain} {d : ℕ} (hd : QFig t → 0 < d) :
    df_QBC (PQ := PQ) Q
      (liftC (Proofs.Refinement.deliverForgeHook Pt ℓ) (query (spec := QueryBounds.FSpec Pt ℓ) t))
      d :=
  df_qbc_liftC hQ ((isQueryBoundP_query_iff QFig t d).2 hd)

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_zoomB {ℓ : ℕ}
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t)
    {α : Type} {x : QueryBounds.SimM PQ Pt ℓ α} {n : ℕ} (hx : QueryBounds.QB QFig x n) :
    df_QBC Q (runOnBaseState (Proofs.Refinement.deliverForgeHook Pt ℓ) x) n := fun sC sent => by
  show IsQueryBoundP
    (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift (x.run sC.base) >>=
      fun p => pure (p.1, { sC with base := p.2 })).run sent) Q n
  rw [StateT.run_bind, ← Nat.add_zero n]
  exact isQueryBoundP_bind (isQueryBoundP_deliverForgeHook_lift hQ (hx sC.base) sent)
    fun p _ => by simp



omit [SampleableType Pt] in
theorem df_qbc_simSendC_short {ℓ : ℕ} (P : Params PQ PQC) (hL : LengthsOk P ℓ) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (hQ : ∀ t, Q (toDFDom t) ↔ Proofs.SessionShort.SimAndSM.QShort Pt ℓ t)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    df_QBC Q (simSendC P qep fig (Proofs.Refinement.deliverForgeHook Pt ℓ) R m₀ chal r) 0 := by
  unfold LibsignalSimC.simSendC
  refine df_qbc_bind_r
    (df_qbc_zoomB hQ
      (Proofs.SessionShort.SimAndSM.qb_simSend_QShort (Pt := Pt) P hL qep R m₀ chal r))
    fun res => ?_
  cases res with
  | none => exact df_qbc_pure none 0
  | some w =>
    refine df_qbc_bind0 df_qbc_get fun sC => ?_
    exact df_qbc_bind0 (df_qbc_set _) fun _ => df_qbc_pure (some w) 0






omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem df_qbc_simCorrC {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey)
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t) (d : ℕ)
    (hQcorr : ∀ R, QFig (.inr (.inr R)) → 0 < d) (R : Party) :
    df_QBC Q (simCorrC P encT (Proofs.Refinement.deliverForgeHook Pt ℓ) Dh R) d := by
  unfold LibsignalSimC.simCorrC
  refine df_qbc_bind0 df_qbc_get fun sC => ?_
  dsimp only
  refine df_qbc_ite_pure ?_
  refine df_qbc_bind_r (df_qbc_liftC_query hQ (hQcorr R)) fun res => ?_
  cases res with
  | none => exact df_qbc_pure none 0
  | some st => exact df_qbc_bind0 (df_qbc_set _) fun _ => df_qbc_pure _ 0

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
theorem df_qbc_guardC {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {α : Type}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) (Option α)} {n : ℕ}
    (hx : df_QBC Q x n) : df_QBC Q (guardC x) n := by
  unfold LibsignalSimC.guardC
  refine df_qbc_bind0 df_qbc_get fun sC => ?_
  split
  · exact df_qbc_pure none n
  · exact hx


abbrev QShortDF (Pt : Type) (ℓ : ℕ) : (DFSpec Pt ℓ).Domain → Prop :=
  fun t => badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
    (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) t = true

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hQ_QShortDF {ℓ : ℕ} (t : (QueryBounds.FSpec Pt ℓ).Domain) :
    QShortDF Pt ℓ (toDFDom t) ↔ Proofs.SessionShort.SimAndSM.QShort Pt ℓ t := by
  rcases t with _ | ((((_ | _) | _) | _) | _) <;> rfl



section ChallSimDF

variable {St Msg Coins C Pub : Type} [DecidableEq C] [DecidableEq Pub]


end ChallSimDF

/-! ## Query bounds and `FsOk` for `DeliverForge.redFSAuthDF` -/

section RedFSAuthDF

open ReductionsQueries

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [DecidableEq Pub] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]



end RedFSAuthDF

/-! ## Atomic short-message bounds -/

section AtomicShort

/-- Tightened length side condition matching `atomicShortPubB`. -/
def AtomicLengthsOk {PQ PQC : Type} (P : Params PQ PQC) (ℓ : ℕ) : Prop :=
  ℓ < 10 ^ 6 ∧
    (∀ st rq st' salt msg, P.spqr.send st rq = some (st', salt, msg) → msg.length ≤ 96) ∧
    (∀ a, P.addrAB = some a → a.length ≤ 128) ∧
    (∀ a, P.addrBA = some a → a.length ≤ 128)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem atomicLengthsOk_imp_lengthsOk {P : Params PQ PQC} {ℓ : ℕ} (h : AtomicLengthsOk P ℓ) :
    LengthsOk P ℓ := by
  have h1 := h.1
  refine ⟨by simp only [Nat.reducePow]; omega, ?_, ?_, ?_⟩
  · intro st rq st' salt msg hs
    have hm := h.2.1 st rq st' salt msg hs
    simp only [Nat.reducePow]; omega
  · intro a ha
    have hm := h.2.2.1 a ha
    simp only [Nat.reducePow]; omega
  · intro a ha
    have hm := h.2.2.2 a ha
    simp only [Nat.reducePow]; omega

/-- `paramsIdsWithSpqr` with `spqrV1SessionUniformCoins` satisfies `AtomicLengthsOk` when `ℓ < 10 ^ 6`. -/
theorem atomicLengthsOk_paramsIdsWithSpqr_v1 (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) :
    AtomicLengthsOk (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ := by
  refine ⟨hℓ, ?_, ?_, ?_⟩
  · intro st rq st' salt msg hs
    exact le_trans (spqrV1Send_msg_len_le C.F K st rq st' salt msg hs) (by omega)
  · intro a ha
    rw [addrsE_length _ _ _ a ha]; omega
  · intro a ha
    rw [addrsE_length _ _ _ a ha]; omega

abbrev QAtomicShort (Pt : Type) (ℓ : ℕ) : (QueryBounds.FSpec Pt ℓ).Domain → Prop :=
  fun t => Proofs.SessionShort.SimAndSM.badSendMsg
    (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
    (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) t = true

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hQu_QAtomicShort {ℓ : ℕ} : ∀ u : ℕ, ¬ QAtomicShort Pt ℓ (.inl u) := by
  intro _ h; nomatch h

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem atomicShortPubB_mkPub {ℓ : ℕ} {P : Params PQ PQC} (hL : AtomicLengthsOk P ℓ)
    (s : SimState PQ Pt ℓ) (R : Party) (rq : PQC) (pn : BitVec 32)
    {pq' : PQ} {pub : LibsignalMsgPublicPart} (hmk : mkPub (P := P) s R rq pn = some (pq', pub)) :
    atomicShortPubB pub = true := by
  unfold mkPub at hmk
  rcases Option.mem_map.mp hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  obtain ⟨_, rfl⟩ := Prod.mk.inj hpair
  have hmsg : msg.length ≤ 96 := hL.2.1 (s.pq R) rq st' salt msg hsend
  have haddr : (if R == Party.A && s.unackA then P.addrAB else none).all
      (fun a => decide (a.length ≤ 128)) = true := by
    split
    · cases hAB : P.addrAB with
      | none => rfl
      | some a =>
        have ha := hL.2.2.1 a hAB
        simp [Option.all, ha]
    · rfl
  unfold atomicShortPubB
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hmsg, haddr⟩

omit [SampleableType Pt] in
theorem qb_simSend_QAtomicShort {ℓ : ℕ} (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ) (qep : ℕ)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    QueryBounds.QB (QAtomicShort Pt ℓ) (LibsignalSim.simSend (P := P) (qep := qep) R m₀ chal r) 0 := by
  unfold LibsignalSim.simSend
  refine QueryBounds.qb_bind0 QueryBounds.qb_get fun s => ?_
  split
  · exact QueryBounds.qb_pure none 0
  · cases s.mir.epMgmt 3 qep R r.isSome with
    | none => exact QueryBounds.qb_pure none 0
    | some s₁ =>
      dsimp only
      split
      · exact QueryBounds.qb_pure none 0
      · cases r with
        | some rq =>
          simp only [pure_bind]
          refine QueryBounds.qb_bind0
            (QueryBounds.qb_map some (QueryBounds.qb_coin hQu_QAtomicShort (BitVec 256))) fun rc => ?_
          cases hmk : mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with
          | none => exact QueryBounds.qb_pure none 0
          | some p =>
            rcases p with ⟨pq', pub⟩
            have hpub := atomicShortPubB_mkPub hL s R rq _ hmk
            dsimp only
            cases chal with
            | none =>
              refine QueryBounds.qb_bind_r (QueryBounds.qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, Proofs.SessionShort.SimAndSM.badSendMsg, hpub] at h
              · cases res with
                | none => exact QueryBounds.qb_pure none 0
                | some c => exact QueryBounds.qb_bind0 (QueryBounds.qb_putS _) fun _ => QueryBounds.qb_pure _ 0
            | some m₁ =>
              refine QueryBounds.qb_bind_r (QueryBounds.qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, Proofs.SessionShort.SimAndSM.badSendMsg, hpub] at h
              · cases res with
                | none => exact QueryBounds.qb_pure none 0
                | some c => exact QueryBounds.qb_bind0 (QueryBounds.qb_putS _) fun _ => QueryBounds.qb_pure _ 0
        | none =>
          refine QueryBounds.qb_bind0 (QueryBounds.qb_coin hQu_QAtomicShort PQC) fun rq => ?_
          simp only [pure_bind]
          cases hmk : mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with
          | none => exact QueryBounds.qb_pure none 0
          | some p =>
            rcases p with ⟨pq', pub⟩
            have hpub := atomicShortPubB_mkPub hL s R rq _ hmk
            dsimp only
            cases chal with
            | none =>
              refine QueryBounds.qb_bind_r (QueryBounds.qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, Proofs.SessionShort.SimAndSM.badSendMsg, hpub] at h
              · cases res with
                | none => exact QueryBounds.qb_pure none 0
                | some c => exact QueryBounds.qb_bind0 (QueryBounds.qb_putS _) fun _ => QueryBounds.qb_pure _ 0
            | some m₁ =>
              refine QueryBounds.qb_bind_r (QueryBounds.qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, Proofs.SessionShort.SimAndSM.badSendMsg, hpub] at h
              · cases res with
                | none => exact QueryBounds.qb_pure none 0
                | some c => exact QueryBounds.qb_bind0 (QueryBounds.qb_putS _) fun _ => QueryBounds.qb_pure _ 0

omit [SampleableType Pt] in
private theorem a5_qbc_simSendC_atomicShort {ℓ : ℕ} (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    a5_QBC (QAtomicShort Pt ℓ) (simSendC P qep fig idHook R m₀ chal r) 0 := by
  unfold LibsignalSimC.simSendC
  refine a5_qbc_bind_r (a5_qbc_zoomB
    (qb_simSend_QAtomicShort (Pt := Pt) P hL qep R m₀ chal r)) fun res => ?_
  cases res with
  | none => exact a5_qbc_pure none 0
  | some w =>
    refine a5_qbc_bind0 a5_qbc_get fun sC => ?_
    exact a5_qbc_bind0 (a5_qbc_set _) fun _ => a5_qbc_pure (some w) 0

omit [SampleableType Pt] in
/-- Under `AtomicLengthsOk P ℓ`, every `transmit` or `chall` message of
`libsignalToModularSchemeSim` satisfies `atomicShortPubB`. -/
theorem simC_sendAtomicShort (P : Params PQ PQC) (ℓ : ℕ) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) := by
  have hmain : IsQueryBoundP
      (Refine.libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)
      (QAtomicShort Pt ℓ) 0 := by
    unfold Refine.libsignalToModularSchemeSim runLibsignalToModularSchemeSim simRunCWith
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    rw [← Nat.zero_add 0]
    refine isQueryBoundP_bind (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ)
      hQu_QAtomicShort ($ᵗ BitVec 256)) fun pqrKey _ => ?_
    have hQd : ∀ R c, QAtomicShort Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) → 0 < 0 := by
      intro _ _ h; nomatch h
    have hQi : ∀ R c, QAtomicShort Pt ℓ (.inr (.inl (.inr (R, c)))) → 0 < 0 := by
      intro _ _ h; nomatch h
    have hQcorr : ∀ R, QAtomicShort Pt ℓ (.inr (.inr R)) → 0 < 0 := by
      intro _ h; nomatch h
    have hsim : IsQueryBoundP
        ((simulateQ (simImplC P encT decT qep fig fs idHook Dh) A).run
          (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
        (QAtomicShort Pt ℓ) 0 := by
      refine QueryBounds.isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
      rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
      · exact a5_qbc_liftC_query (fun h => absurd h (hQu_QAtomicShort n)) sC
      · exact a5_qbc_guardC (a5_qbc_simSendC_atomicShort P hL qep fig R m none r) sC
      · exact a5_qbc_guardC (a5_qbc_simSendC_atomicShort P hL qep fig R m₀ (some m₁) r) sC
      · exact a5_qbc_guardC (a5_qbc_simRecvC P encT decT qep fig fs 0 hQd hQi R w true) sC
      · exact a5_qbc_guardC (a5_qbc_simRecvC P encT decT qep fig fs 0 hQd hQi R w false) sC
      · exact a5_qbc_guardC (a5_qbc_simCorrC P Dh encT 0 hQcorr R) sC
    rw [StateT.run'_eq]
    exact (isQueryBoundP_map_iff _ _ _).mpr hsim
  unfold Proofs.SessionShort.SendMsgsOk
  exact QueryBounds.isQueryBoundP_congr (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) hmain

abbrev QAtomicShortDF (Pt : Type) (ℓ : ℕ) : (DFSpec Pt ℓ).Domain → Prop :=
  fun t => badSendMsgDF (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
    (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) t = true

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hQ_QAtomicShortDF {ℓ : ℕ} (t : (QueryBounds.FSpec Pt ℓ).Domain) :
    QAtomicShortDF Pt ℓ (toDFDom t) ↔ QAtomicShort Pt ℓ t := by
  rcases t with _ | ((((_ | _) | _) | _) | _) <;> rfl

omit [SampleableType Pt] in
theorem df_qbc_simSendC_atomicShort {ℓ : ℕ} (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (hQ : ∀ t, Q (toDFDom t) ↔ QAtomicShort Pt ℓ t)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    df_QBC Q (simSendC P qep fig (Proofs.Refinement.deliverForgeHook Pt ℓ) R m₀ chal r) 0 := by
  unfold LibsignalSimC.simSendC
  refine df_qbc_bind_r
    (df_qbc_zoomB hQ (qb_simSend_QAtomicShort (Pt := Pt) P hL qep R m₀ chal r)) fun res => ?_
  cases res with
  | none => exact df_qbc_pure none 0
  | some w =>
    refine df_qbc_bind0 df_qbc_get fun sC => ?_
    exact df_qbc_bind0 (df_qbc_set _) fun _ => df_qbc_pure (some w) 0

alias simC_sendShortAtomic := simC_sendAtomicShort

abbrev QShortDFAtomic (Pt : Type) (ℓ : ℕ) : (DFSpec Pt ℓ).Domain → Prop :=
  QAtomicShortDF Pt ℓ

alias hQ_QShortDFAtomic := hQ_QAtomicShortDF

alias df_qbc_simSendC_shortAtomic := df_qbc_simSendC_atomicShort


abbrev QShortAtomic (Pt : Type) (ℓ : ℕ) : (QueryBounds.FSpec Pt ℓ).Domain → Prop :=
  QAtomicShort Pt ℓ

alias qb_simSend_QShortAtomic := qb_simSend_QAtomicShort

omit [SampleableType Pt] [SampleableType PQC] in
theorem qb_simRecv_QAtomicShort {ℓ : ℕ} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ) (R : Party)
    (w : List (BitVec 8)) (isDel : Bool) :
    QueryBounds.QB (QAtomicShort Pt ℓ)
      (LibsignalSim.simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) R w isDel)
      0 := by
  have hQd : ∀ R c, QAtomicShort Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) → 0 < 0 := by
    intro _ _ h; nomatch h
  have hQi : ∀ R c, QAtomicShort Pt ℓ (.inr (.inl (.inr (R, c)))) → 0 < 0 := by
    intro _ _ h; nomatch h
  unfold LibsignalSim.simRecv
  refine QueryBounds.qb_bind0 QueryBounds.qb_get fun s => ?_
  dsimp only
  refine QueryBounds.qb_ite_pure ?_
  refine QueryBounds.qb_ite_pure ?_
  refine QueryBounds.qb_ite_pure ?_
  refine QueryBounds.qb_ite_pure ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact QueryBounds.qb_pure (some RecvResult.rejected) 0
  | some hp =>
    dsimp only
    refine QueryBounds.qb_ite_pure ?_
    cases P.spqr.recv (s.pq R) hp.1.pqRatchet with
    | error _ => exact QueryBounds.qb_pure (some RecvResult.rejected) 0
    | ok ps =>
      dsimp only
      cases (s.chains R).findIdx? (fun g => g.key == some hp.1.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine QueryBounds.qb_ite_pure ?_
        exact QueryBounds.qb_bind_r (QueryBounds.qb_fwd 0 hQd hQi R _) fun res =>
          QueryBounds.qb_onAnswer qep R w isDel _ _ _ res
      | none =>
        dsimp only
        refine QueryBounds.qb_ite_pure ?_
        refine QueryBounds.qb_ite_pure ?_
        refine QueryBounds.qb_ite (QueryBounds.qb_bind0 (QueryBounds.qb_putS _) fun _ => ?_) ?_ <;>
        · split
          · refine QueryBounds.qb_ite ?_ ?_
            · refine QueryBounds.qb_ite ?_
                (QueryBounds.qb_bind0 (QueryBounds.qb_modify _) fun _ => QueryBounds.qb_pure none 0)
              cases decT hp.1.senderRatchetKey with
              | none =>
                exact QueryBounds.qb_bind0 (QueryBounds.qb_modify _) fun _ =>
                  QueryBounds.qb_pure none 0
              | some T =>
                refine QueryBounds.qb_bind_r (QueryBounds.qb_fwd 0 hQd hQi R _) fun _ => ?_
                exact QueryBounds.qb_bind0 (QueryBounds.qb_modify _) fun _ =>
                  QueryBounds.qb_pure none 0
            · refine QueryBounds.qb_bind0 (QueryBounds.qb_liftQ_query fun h => ?_) fun _ => ?_
              · simp [QAtomicShort, Proofs.SessionShort.SimAndSM.badSendMsg,
                  atomicShortPubB, Option.all] at h
              · cases decT hp.1.senderRatchetKey with
                | none =>
                  exact QueryBounds.qb_bind0 (QueryBounds.qb_modify _) fun _ =>
                    QueryBounds.qb_pure none 0
                | some T =>
                  refine QueryBounds.qb_bind_r (QueryBounds.qb_fwd 0 hQd hQi R _) fun _ => ?_
                  exact QueryBounds.qb_bind0 (QueryBounds.qb_modify _) fun _ =>
                    QueryBounds.qb_pure none 0
          · refine QueryBounds.qb_ite_pure ?_
            cases decT hp.1.senderRatchetKey with
            | none => exact QueryBounds.qb_pure (some RecvResult.rejected) 0
            | some T =>
              exact QueryBounds.qb_bind_r (QueryBounds.qb_fwd 0 hQd hQi R _) fun res =>
                QueryBounds.qb_onAnswer qep R w isDel none _ _ res

omit [SampleableType Pt] in
theorem qb_simImpl_QAtomicShort {ℓ : ℕ} (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (k : Option ℕ)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    QueryBounds.QB (QAtomicShort Pt ℓ) (LibsignalSim.simImpl P Dh encT decT qep k t) 0 := by
  have hQcorr : ∀ R, QAtomicShort Pt ℓ (.inr (.inr R)) → 0 < 0 := by
    intro _ h; nomatch h
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
  · exact QueryBounds.qb_liftQ_query fun h => absurd h (hQu_QAtomicShort n)
  · exact QueryBounds.qb_guard (qb_simSend_QAtomicShort P hL qep R m none r)
  · exact QueryBounds.qb_guard (qb_simSend_QAtomicShort P hL qep R m₀ (some m₁) r)
  · exact QueryBounds.qb_guard (qb_simRecv_QAtomicShort P encT decT qep k R w true)
  · exact QueryBounds.qb_guard (qb_simRecv_QAtomicShort P encT decT qep k R w false)
  · exact QueryBounds.qb_guard (QueryBounds.qb_simCorr P Dh encT 0 hQcorr R)

omit [SampleableType Pt] in
/-- Under `AtomicLengthsOk P ℓ`, every `transmit` or `chall` message of `LibsignalSim.simRun`
satisfies `atomicShortPubB`. -/
theorem simRun_sendAtomicShort {ℓ : ℕ} (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (k : Option ℕ) (A : LibAdv PQ PQC ℓ) :
    Proofs.SessionShort.SendMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (LibsignalSim.simRun P Dh encT decT qep k A) := by
  have hmain : IsQueryBoundP (LibsignalSim.simRun P Dh encT decT qep k A)
      (QAtomicShort Pt ℓ) 0 := by
    unfold LibsignalSim.simRun
    rw [← Nat.zero_add 0]
    refine isQueryBoundP_bind
      (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QAtomicShort ($ᵗ BitVec 256))
      fun pqrKey _ => ?_
    have hsim : IsQueryBoundP
        ((simulateQ (LibsignalSim.simImpl P Dh encT decT qep k) A).run
          (LibsignalSim.initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
        (QAtomicShort Pt ℓ) 0 :=
      QueryBounds.isQueryBoundP_simulateQ_run_zero A
        (qb_simImpl_QAtomicShort P hL Dh encT decT qep k) _
    rw [StateT.run'_eq, ← Nat.add_zero 0]
    have hmap : IsQueryBoundP
        (Prod.fst <$> (simulateQ (LibsignalSim.simImpl P Dh encT decT qep k) A).run
          (LibsignalSim.initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
        (QAtomicShort Pt ℓ) 0 :=
      (isQueryBoundP_map_iff _ _ _).mpr hsim
    refine isQueryBoundP_bind hmap fun b' _ => ?_
    cases k with
    | none => exact isQueryBoundP_pure _ b' 0
    | some _ =>
      exact QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QAtomicShort ($ᵗ Bool)
  unfold Proofs.SessionShort.SendMsgsOk
  exact QueryBounds.isQueryBoundP_congr (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) hmain

alias simRun_sendShortAtomic := simRun_sendAtomicShort

end AtomicShort

end CryptoVerification.LibsignalSession.HeadlineV1

namespace CryptoVerification.LibsignalSession.HeadlineV1

section MoveCompat

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopStmts spqrV1Send_msg_len_le)
open CryptoVerification.E2E (partyIdentityKey paramsIdsWithSpqr)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB atomicShortPubB_imp_shortB)
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Construction.DeliverForge
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC CryptoGames.LibsignalSM.Proofs
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

section MoveCompatSimDF

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  [Inhabited PQ] [SampleableType PQC]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_modify {ℓ : ℕ} {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    df_QBC Q
      (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) PUnit) 0 :=
  fun _ _ => by simp

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem df_qbc_probe {ℓ : ℕ}
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    (R : Party) (c' : Fig8C Pt) (d : ℕ)
    (hQdf : ∀ R c c', Q (.inr (.inr (R, c, c'))) → 0 < d) :
    df_QBC (PQ := PQ) Q (StateT.lift ((Proofs.Refinement.deliverForgeHook Pt ℓ).probe R c')) d :=
  fun sC sent => by
    show IsQueryBoundP
      (((Proofs.Refinement.deliverForgeHook Pt ℓ).probe R c' >>= fun a => pure (a, sC)).run sent)
      Q d
    unfold Proofs.Refinement.deliverForgeHook
    dsimp only
    rw [StateT.run_bind, StateT.run_bind, StateT.run_get, pure_bind]
    cases sent.find? (fun c => Proofs.Refinement.sameWireFig8 c c') with
    | none => simp
    | some c =>
      dsimp only
      rw [StateT.run_bind, ← Nat.add_zero d]
      have hq : IsQueryBoundP
          (DeliverForge.deliverForgeQuery
            (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
            R c c') Q d :=
        (isQueryBoundP_query_iff Q (.inr (.inr (R, c, c'))) d).2 (hQdf R c c')
      have hlift : IsQueryBoundP
          ((StateT.lift (DeliverForge.deliverForgeQuery
              (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt)
              R c c') : Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) Q d := by
        show IsQueryBoundP (DeliverForge.deliverForgeQuery _ _ _ >>= fun a => pure (a, sent)) Q d
        rw [← Nat.add_zero d]
        exact isQueryBoundP_bind hq fun a _ => isQueryBoundP_pure Q (a, sent) 0
      exact isQueryBoundP_bind hlift fun _ _ => by simp

omit [SampleableType Pt] in
private theorem df_qbc_simSendC {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t) (d : ℕ)
    (hQu : ∀ u, ¬ QFig (.inl u))
    (hQt : ∀ R pm rc, QFig (.inr (.inl (.inl (.inl (.inl (R, pm, rc)))))) → 0 < d)
    (hQc : ∀ R pub m₀ m₁ rc,
      QFig (.inr (.inl (.inl (.inl (.inr (R, (pub, m₀), (pub, m₁), rc)))))) → 0 < d)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    df_QBC Q (simSendC P qep fig (Proofs.Refinement.deliverForgeHook Pt ℓ) R m₀ chal r) d := by
  unfold LibsignalSimC.simSendC
  refine df_qbc_bind_r
    (df_qbc_zoomB hQ (QueryBounds.qb_simSend P qep d hQu hQt hQc R m₀ chal r)) fun res => ?_
  cases res with
  | none => exact df_qbc_pure none 0
  | some w =>
    refine df_qbc_bind0 df_qbc_get fun sC => ?_
    exact df_qbc_bind0 (df_qbc_set _) fun _ => df_qbc_pure (some w) 0

omit [SampleableType Pt] in
private theorem df_qbc_fwdAnswerC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t) (d : ℕ)
    (hQd : ∀ R c, QFig (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, QFig (.inr (.inl (.inr (R, c)))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) :
    df_QBC Q
      (fwdAnswerC qep fig fs (Proofs.Refinement.deliverForgeHook Pt ℓ) R w isDel ci? T pq' c')
      d := by
  unfold fwdAnswerC
  refine df_qbc_bind_r (df_qbc_zoomB hQ (QueryBounds.qb_fwd d hQd hQi R c')) fun res => ?_
  cases res with
  | none => exact df_qbc_zoomB hQ (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' none)
  | some rr =>
    cases rr with
    | rejected =>
      exact df_qbc_zoomB hQ (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' (some .rejected))
    | accepted t i pm =>
      exact df_qbc_bind0 (df_qbc_modify _) fun _ =>
        df_qbc_zoomB hQ (QueryBounds.qb_onAnswer qep R w isDel ci? T pq' (some (.accepted t i pm)))

omit [SampleableType Pt] in
private theorem df_qbc_resyncC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t) (d : ℕ)
    (hQd : ∀ R c, QFig (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    df_QBC Q
      (resyncC qep fig fs (Proofs.Refinement.deliverForgeHook Pt ℓ) R w ci? T pq' c r) d := by
  unfold resyncC
  cases r with
  | none => exact df_qbc_pure (some RecvResult.rejected) d
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine df_qbc_bind_r (df_qbc_liftC_query hQ (hQd R c)) fun res => ?_
    cases res with
    | none => exact df_qbc_pure (some RecvResult.rejected) 0
    | some rr =>
      cases rr with
      | rejected => exact df_qbc_pure (some RecvResult.rejected) 0
      | accepted _ _ _ =>
        exact df_qbc_bind0 (df_qbc_modify _) fun _ =>
          df_qbc_zoomB hQ (QueryBounds.qb_onAccept qep R w true t i pm.2 ci? T pq')

omit [SampleableType Pt] [SampleableType PQC] in
private theorem df_qbc_fwdC {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t) (d : ℕ)
    (hQd : ∀ R c, QFig (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, QFig (.inr (.inl (.inr (R, c)))) → 0 < d)
    (hQdf : ∀ R c c', Q (.inr (.inr (R, c, c'))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    df_QBC Q
      (LibsignalSimC.fwdC P qep fig fs (Proofs.Refinement.deliverForgeHook Pt ℓ) R w isDel ci? T
        pq' honestC c')
      d := by
  unfold LibsignalSimC.fwdC
  refine df_qbc_bind0 df_qbc_get fun sC => ?_
  cases honestC with
  | none => exact df_qbc_fwdAnswerC qep fig fs hQ d hQd hQi R w isDel ci? T pq' c'
  | some c =>
    dsimp only
    refine df_qbc_ite ?_ (df_qbc_fwdAnswerC qep fig fs hQ d hQd hQi R w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots fig fs P sC R w c c' with
    | some r => exact df_qbc_resyncC qep fig fs hQ d hQd R w ci? T pq' c r
    | none =>
      exact df_qbc_bind_r (df_qbc_probe R c' d hQdf) fun _ =>
        df_qbc_pure (some RecvResult.rejected) 0

omit [SampleableType Pt] in
private theorem df_qbc_fwdEvictC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t) (d : ℕ)
    (hQd : ∀ R c, QFig (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, QFig (.inr (.inl (.inr (R, c)))) → 0 < d)
    (hQdf : ∀ R c c', Q (.inr (.inr (R, c, c'))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) :
    df_QBC Q
      (fwdEvictC qep fig fs (Proofs.Refinement.deliverForgeHook Pt ℓ) R w isDel T pq' c')
      d := by
  unfold fwdEvictC
  refine df_qbc_bind0 df_qbc_get fun sC => ?_
  refine df_qbc_ite ?_ (df_qbc_fwdAnswerC qep fig fs hQ d hQd hQi R w isDel none T pq' c')
  exact df_qbc_bind_r (df_qbc_probe R c' d hQdf) fun _ =>
    df_qbc_pure (some RecvResult.rejected) 0

omit [SampleableType Pt] [SampleableType PQC] in
private theorem df_qbc_simRecvC {ℓ : ℕ} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    {Q : (DFSpec Pt ℓ).Domain → Prop} [DecidablePred Q]
    {QFig : (QueryBounds.FSpec Pt ℓ).Domain → Prop} [DecidablePred QFig]
    (hQ : ∀ t, Q (toDFDom t) ↔ QFig t) (d : ℕ)
    (hQd : ∀ R c, QFig (.inr (.inl (.inl (.inr (R, c))))) → 0 < d)
    (hQi : ∀ R c, QFig (.inr (.inl (.inr (R, c)))) → 0 < d)
    (hQdf : ∀ R c c', Q (.inr (.inr (R, c, c'))) → 0 < d)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) :
    df_QBC Q (simRecvC P encT decT qep fig fs (Proofs.Refinement.deliverForgeHook Pt ℓ) R w isDel)
      d := by
  unfold LibsignalSimC.simRecvC
  refine df_qbc_bind0 df_qbc_get fun sC => ?_
  dsimp only
  refine df_qbc_ite_pure ?_
  refine df_qbc_ite_pure ?_
  refine df_qbc_ite_pure ?_
  refine df_qbc_ite_pure ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact df_qbc_pure (some RecvResult.rejected) d
  | some hp =>
    dsimp only
    refine df_qbc_ite_pure ?_
    refine df_qbc_ite_pure ?_
    cases P.spqr.recv (sC.base.pq R) hp.1.pqRatchet with
    | error _ => exact df_qbc_pure (some RecvResult.rejected) d
    | ok ps =>
      dsimp only
      cases (sC.base.chains R).findIdx? (fun g => g.key == some hp.1.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine df_qbc_ite_pure ?_
        exact df_qbc_fwdC P qep fig fs hQ d hQd hQi hQdf R w isDel (some ci)
          hp.1.senderRatchetKey ps.1 _ _
      | none =>
        dsimp only
        refine df_qbc_ite_pure ?_
        refine df_qbc_ite_pure ?_
        refine df_qbc_ite (df_qbc_bind0 (df_qbc_modify _) fun _ => ?_) ?_ <;>
        · refine df_qbc_ite_pure ?_
          cases decT hp.1.senderRatchetKey with
          | none => exact df_qbc_pure (some RecvResult.rejected) d
          | some T =>
            exact df_qbc_ite
              (df_qbc_fwdEvictC qep fig fs hQ d hQd hQi hQdf R w isDel
                hp.1.senderRatchetKey ps.1 _)
              (df_qbc_fwdC P qep fig fs hQ d hQd hQi hQdf R w isDel none
                hp.1.senderRatchetKey ps.1 _ _)

private abbrev QDF (Pt : Type) (ℓ : ℕ) : (DFSpec Pt ℓ).Domain → Prop :=
  (· matches .inr _)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem hQ_QDF {ℓ : ℕ} (t : (QueryBounds.FSpec Pt ℓ).Domain) :
    QDF Pt ℓ (toDFDom t) ↔ QueryBounds.QInr Pt ℓ t := by
  rcases t with _ | _ <;> rfl

omit [SampleableType Pt] in
theorem simDeliverForge_queries (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (A : LibAdv PQ PQC ℓ)
    (hq : SM.MakesAtMostQueries A q) :
    DeliverForge.MakesAtMostQueriesDF
      (Proofs.Refinement.simDeliverForge P ℓ Dh encPt encT decT idOf lam qep A) q := by
  unfold DeliverForge.MakesAtMostQueriesDF Proofs.Refinement.simDeliverForge simRunCWith
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let H := Proofs.Refinement.deliverForgeHook Pt ℓ
  refine QueryBounds.isQueryBoundP_congr (p := QDF Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  rw [StateT.run_bind]
  have hpqr : IsQueryBoundP
      ((H.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)))).run []) (QDF Pt ℓ) 0 :=
    isQueryBoundP_deliverForgeHook_lift hQ_QDF
      (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) QueryBounds.hQu_QInr ($ᵗ BitVec 256))
      []
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind hpqr fun ⟨pqrKey, sent₀⟩ _ => ?_
  dsimp only
  rw [StateT.run'_eq]
  have hsim : ∀ (oa : LibAdv PQ PQC ℓ) q,
      SM.MakesAtMostQueries oa q → ∀ sC sent,
        IsQueryBoundP
          (((simulateQ (simImplC P encT decT qep fig fs H Dh) oa).run sC).run sent)
          (QDF Pt ℓ) q := by
    intro oa
    have hstep_p : ∀ q' : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain,
        ∀ s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt),
          IsQueryBoundP
            ((((simImplC P encT decT qep fig fs H Dh (.inr q')).run s.1).run s.2))
            (QDF Pt ℓ) 1 := by
      rintro ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R) ⟨sC', sent'⟩
      · exact df_qbc_guardC
          (df_qbc_simSendC P qep fig hQ_QDF 1 QueryBounds.hQu_QInr
            (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one)
            R m none r) sC' sent'
      · exact df_qbc_guardC
          (df_qbc_simSendC P qep fig hQ_QDF 1 QueryBounds.hQu_QInr
            (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one)
            R m₀ (some m₁) r) sC' sent'
      · exact df_qbc_guardC
          (df_qbc_simRecvC P encT decT qep fig fs hQ_QDF 1
            (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one)
            (fun _ _ _ _ => Nat.zero_lt_one) R w true) sC' sent'
      · exact df_qbc_guardC
          (df_qbc_simRecvC P encT decT qep fig fs hQ_QDF 1
            (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ => Nat.zero_lt_one)
            (fun _ _ _ _ => Nat.zero_lt_one) R w false) sC' sent'
      · exact df_qbc_guardC
          (df_qbc_simCorrC P Dh encT hQ_QDF 1 (fun _ _ => Nat.zero_lt_one) R) sC' sent'
    have hstep_np : ∀ n : unifSpec.Domain, ∀ s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt),
        IsQueryBoundP
          ((((simImplC P encT decT qep fig fs H Dh (.inl n)).run s.1).run s.2)) (QDF Pt ℓ) 0 := by
      intro n ⟨sC', sent'⟩
      exact df_qbc_liftC_query hQ_QDF (fun h => absurd h (QueryBounds.hQu_QInr n)) sC' sent'
    induction oa using OracleComp.inductionOn with
    | pure x => intro q _ sC sent; simp [simulateQ_pure]
    | query_bind t mx ih =>
      intro q hq₀ sC sent
      unfold SM.MakesAtMostQueries at hq₀
      rw [isQueryBoundP_query_bind_iff] at hq₀
      rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
      rcases t with n | q'
      · have hq' : ∀ x, SM.MakesAtMostQueries (mx x) q :=
          fun x => by simpa [SM.MakesAtMostQueries] using hq₀.2 x
        have h0 : IsQueryBoundP
            (((liftM (simImplC P encT decT qep fig fs H Dh (.inl n)) :
              StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) _).run sC).run sent)
            (QDF Pt ℓ) 0 := by
          simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep_np n (sC, sent)
        rw [← Nat.zero_add q]
        exact isQueryBoundP_bind h0 fun p _ => ih p.1.1 q (hq' p.1.1) p.1.2 p.2
      · have hq0 : 0 < q := by simpa using hq₀.1
        have hq' : ∀ x, SM.MakesAtMostQueries (mx x) (q - 1) :=
          fun x => by simpa [SM.MakesAtMostQueries] using hq₀.2 x
        have h1 : IsQueryBoundP
            (((liftM (simImplC P encT decT qep fig fs H Dh (.inr q')) :
              StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) _).run sC).run sent)
            (QDF Pt ℓ) 1 := by
          simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep_p q' (sC, sent)
        exact (isQueryBoundP_bind h1 fun p _ =>
          ih p.1.1 (q - 1) (hq' p.1.1) p.1.2 p.2).mono (by omega)
  have hrun := hsim A q hq
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) sent₀
  rw [StateT.run_map]
  exact (isQueryBoundP_map_iff _ _ _).mpr hrun

omit [SampleableType Pt] in
theorem simDeliverForge_sendShort (P : Params PQ PQC) (ℓ : ℕ) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) :
    SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (Proofs.Refinement.simDeliverForge P ℓ Dh encPt encT decT idOf lam qep A) := by
  unfold SendMsgsOkDF Proofs.Refinement.simDeliverForge simRunCWith
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let H := Proofs.Refinement.deliverForgeHook Pt ℓ
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  rw [StateT.run_bind]
  have hpqr : IsQueryBoundP
      ((H.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)))).run []) (QShortDF Pt ℓ) 0 :=
    isQueryBoundP_deliverForgeHook_lift hQ_QShortDF
      (QueryBounds.isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ)
        Proofs.SessionShort.SimAndSM.hQu_QShort ($ᵗ BitVec 256))
      []
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind hpqr fun ⟨pqrKey, sent₀⟩ _ => ?_
  rw [StateT.run'_eq, StateT.run_map]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  have hQd : ∀ R c, Proofs.SessionShort.SimAndSM.QShort Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) →
      0 < 0 := by
    intro _ _ h; nomatch h
  have hQi : ∀ R c, Proofs.SessionShort.SimAndSM.QShort Pt ℓ (.inr (.inl (.inr (R, c)))) →
      0 < 0 := by
    intro _ _ h; nomatch h
  have hQdf : ∀ R c c', QShortDF Pt ℓ (.inr (.inr (R, c, c'))) → 0 < 0 := by
    intro _ _ _ h; nomatch h
  have hQcorr : ∀ R, Proofs.SessionShort.SimAndSM.QShort Pt ℓ (.inr (.inr R)) → 0 < 0 := by
    intro _ h; nomatch h
  have hstep : ∀ t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain,
      df_QBC (QShortDF Pt ℓ) (simImplC P encT decT qep fig fs H Dh t) 0 := by
    rintro (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
    · exact df_qbc_liftC_query hQ_QShortDF
        (fun h => absurd h (Proofs.SessionShort.SimAndSM.hQu_QShort n))
    · exact df_qbc_guardC (df_qbc_simSendC_short P hL qep fig hQ_QShortDF R m none r)
    · exact df_qbc_guardC (df_qbc_simSendC_short P hL qep fig hQ_QShortDF R m₀ (some m₁) r)
    · exact df_qbc_guardC
        (df_qbc_simRecvC P encT decT qep fig fs hQ_QShortDF 0 hQd hQi hQdf R w true)
    · exact df_qbc_guardC
        (df_qbc_simRecvC P encT decT qep fig fs hQ_QShortDF 0 hQd hQi hQdf R w false)
    · exact df_qbc_guardC (df_qbc_simCorrC P Dh encT hQ_QShortDF 0 hQcorr R)
  have hsim :
      ∀ (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) Bool)
        sC sent,
        IsQueryBoundP
          (((simulateQ (simImplC P encT decT qep fig fs H Dh) oa).run sC).run sent)
          (QShortDF Pt ℓ) 0 := by
    intro oa
    induction oa using OracleComp.inductionOn with
    | pure x => intro sC sent; simp [simulateQ_pure]
    | query_bind t mx ih =>
      intro sC sent
      rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
      have h0 : IsQueryBoundP
          (((liftM (simImplC P encT decT qep fig fs H Dh t) :
            StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Proofs.Refinement.DeliverForgeM Pt ℓ) _).run sC).run sent)
          (QShortDF Pt ℓ) 0 := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t sC sent
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind h0 fun p _ => ih p.1.1 p.1.2 p.2
  exact hsim A (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)) sent₀

end MoveCompatSimDF

section MoveCompatChallSimDF

variable {St Msg Coins C Pub : Type} [DecidableEq C] [DecidableEq Pub]

omit [DecidableEq C] [DecidableEq Pub] in
private lemma queryDF_eq_liftM (t : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain) :
    (query (spec := unifSpec + DeliverForge.specDF St Msg Coins C) t :
      DeliverForge.AdversaryCompDF St Msg Coins C _) =
      liftM ((unifSpec + DeliverForge.specDF St Msg Coins C).query t) := rfl

private lemma stateT_lift_runDF {m : Type → Type} [Monad m] {σ α : Type} (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

omit [DecidableEq Pub] in
private lemma isQueryBoundP_simOraclesDF (Δ qep : ℕ)
    (o : (DeliverForge.specDF St Msg Coins C).Domain) (s : Mirror Msg C) :
    IsQueryBoundP
      ((DeliverForge.simOraclesDF (St := St) (Coins := Coins) Δ qep o).run s)
      (· matches Sum.inr _) 1 := by
  rcases o with (((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · change IsQueryBoundP
      ((DeliverForge.simTransmitDF (St := St) Δ qep (P, msg, r)).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simTransmitDF DeliverForge.transmitQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF, bind_assoc]
    rw [queryDF_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> cases s.epMgmt Δ qep P r.isSome <;> simp
  · change IsQueryBoundP
      ((DeliverForge.simChallDF (St := St) Δ qep (P, m₀, m₁, r)).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simChallDF DeliverForge.transmitQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases s.epMgmt Δ qep P r.isSome with
    | none => trivial
    | some s₁ =>
      dsimp only
      cases hsafe : s₁.safeCh Δ P
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
        trivial
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          stateT_lift_runDF, bind_assoc, pure_bind]
        rw [queryDF_eq_liftM, isQueryBoundP_query_bind_iff]
        refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
        cases res <;> simp
  · change IsQueryBoundP
      ((DeliverForge.simDeliverDF (St := St) (Coins := Coins) (P, c)).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF, bind_assoc]
    rw [queryDF_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr =>
      cases rr <;> cases s.inTransit P.other c <;> simp
  · change IsQueryBoundP
      ((DeliverForge.simInjectDF (St := St) (Coins := Coins) (P, c)).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simInjectDF DeliverForge.injectQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF, bind_assoc]
    rw [queryDF_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp
  · change IsQueryBoundP
      ((DeliverForge.simCorrDF (St := St) (Msg := Msg) (Coins := Coins) (C := C) P).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simCorrDF DeliverForge.corrQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF, bind_assoc]
    rw [queryDF_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res <;> simp
  · change IsQueryBoundP
      ((DeliverForge.simDeliverForgeDF (St := St) (Coins := Coins) (P, c, c')).run s)
      (· matches Sum.inr _) 1
    unfold DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, stateT_lift_runDF, bind_assoc]
    rw [queryDF_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun res => ?_⟩
    cases res with
    | none => simp
    | some rr => cases rr <;> simp

omit [DecidableEq Pub] in
theorem challSimDF_queries (Δ qep : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) {q : ℕ}
    (hq : DeliverForge.MakesAtMostQueriesDF B q) :
    DeliverForge.MakesAtMostQueriesDF (DeliverForge.challSimDF Δ qep B) q := by
  unfold DeliverForge.MakesAtMostQueriesDF DeliverForge.challSimDF
  have hb : IsQueryBoundP
      (liftM ($ᵗ Bool : ProbComp Bool) : DeliverForge.AdversaryCompDF St Msg Coins C Bool)
      (· matches Sum.inr _) 0 :=
    IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
      (fun _ => ⟨False.elim, fun h => by nomatch h⟩)
      (ReductionsQueries.isQueryBoundP_false ($ᵗ Bool) 0)
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind hb fun b _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (DeliverForge.simImplDF (St := St) (Coins := Coins) Δ qep) B).run
        ({ st := fun _ => (), b } : Mirror Msg C))
      (· matches Sum.inr _) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp s
      · cases hp
      · exact isQueryBoundP_simOraclesDF Δ qep o s
    · rintro (n | o) hnp s
      · change IsQueryBoundP
          ((DeliverForge.simCoinsDF (St := St) (Msg := Msg) (Coins := Coins) (C := C) n).run s)
          (· matches Sum.inr _) 0
        unfold DeliverForge.simCoinsDF
        simp only [stateT_lift_runDF]
        rw [queryDF_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by rintro ⟨⟩), fun u => by simp⟩
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

theorem challSimDF_equalPub (Δ qep : ℕ) (pubOf : Msg → Pub)
    (B : DeliverForge.AdversaryDF St Msg Coins C) :
    EqualPubChallsDF pubOf (DeliverForge.challSimDF Δ qep B) := by
  let Q := fun t : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain =>
    unequalPubChallDF (St := St) (Coins := Coins) (C := C) pubOf t = true
  unfold EqualPubChallsDF DeliverForge.challSimDF
  refine RestrictedReds.SafePost.to_isQueryBoundP (P := fun _ => True) ?_
  refine (RestrictedReds.SafePost.liftComp_unif (fun _ h => by nomatch h) ($ᵗ Bool)).bind
    fun b _ => ?_
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  have hstep : ∀ t : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain, ¬ (fun _ => False) t →
      RestrictedReds.SafeS Q (fun _ : Mirror Msg C => True) (fun _ _ => True)
        (DeliverForge.simImplDF (St := St) Δ qep t) := by
    rintro (n | ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩) _
    · exact RestrictedReds.safeS_lift_query (by simp [Q, unequalPubChallDF])
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simTransmitDF Δ qep (P, msg, r))
      unfold DeliverForge.simTransmitDF DeliverForge.transmitQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res <;> cases s.epMgmt Δ qep P r.isSome
      all_goals first
        | exact RestrictedReds.safeS_pure_true _
        | exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simChallDF Δ qep (P, m₀, m₁, r))
      unfold DeliverForge.simChallDF DeliverForge.transmitQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      cases s.epMgmt Δ qep P r.isSome with
      | none => exact RestrictedReds.safeS_pure_true _
      | some s₁ =>
        dsimp only
        cases s₁.safeCh Δ P
        · exact RestrictedReds.safeS_pure_true _
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
          cases res
          · exact RestrictedReds.safeS_pure_true _
          · exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
              fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simDeliverDF (P, c))
      unfold DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr <;> cases s.inTransit P.other c
        all_goals first
          | exact RestrictedReds.safeS_pure_true _
          | exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
              fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simInjectDF (P, c))
      unfold DeliverForge.simInjectDF DeliverForge.injectQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simCorrDF P)
      unfold DeliverForge.simCorrDF DeliverForge.corrQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res
      · exact RestrictedReds.safeS_pure_true _
      · exact RestrictedReds.safeS_bind_true
          (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
          fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simDeliverForgeDF (P, c, c'))
      unfold DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, unequalPubChallDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
  exact (RestrictedReds.SafePost.simulateQ_run
    (RestrictedReds.SafePost.true_of_false B) hstep trivial).bind
    fun _ _ => RestrictedReds.SafePost.pure trivial

omit [DecidableEq Pub] in
theorem challSimDF_sendOk (Δ qep : ℕ) (ok : Msg → Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) (hB : SendMsgsOkDF ok B) :
    SendMsgsOkDF ok (DeliverForge.challSimDF Δ qep B) := by
  let Q := fun t : (unifSpec + DeliverForge.specDF St Msg Coins C).Domain =>
    badSendMsgDF (St := St) (Coins := Coins) (C := C) ok t = true
  unfold SendMsgsOkDF DeliverForge.challSimDF
  refine RestrictedReds.SafePost.to_isQueryBoundP (P := fun _ => True) ?_
  refine (RestrictedReds.SafePost.liftComp_unif (fun _ h => by nomatch h) ($ᵗ Bool)).bind
    fun b _ => ?_
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  have hstep : ∀ t, ¬ Q t →
      RestrictedReds.SafeS Q (fun _ : Mirror Msg C => True) (fun _ _ => True)
        (DeliverForge.simImplDF Δ qep t) := by
    rintro (n | ((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩) hpt
    · exact RestrictedReds.safeS_lift_query (by simp [Q, badSendMsgDF])
    · have hmsg : ok msg = true := by simpa [Q, badSendMsgDF] using hpt
      change RestrictedReds.SafeS Q _ _ (DeliverForge.simTransmitDF Δ qep (P, msg, r))
      unfold DeliverForge.simTransmitDF DeliverForge.transmitQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF, hmsg]) fun res => ?_
      cases res <;> cases s.epMgmt Δ qep P r.isSome
      all_goals first
        | exact RestrictedReds.safeS_pure_true _
        | exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · have hm : ok m₀ = true ∧ ok m₁ = true := by
        simpa [Q, badSendMsgDF, Bool.or_eq_true] using hpt
      change RestrictedReds.SafeS Q _ _ (DeliverForge.simChallDF Δ qep (P, m₀, m₁, r))
      unfold DeliverForge.simChallDF DeliverForge.transmitQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      cases s.epMgmt Δ qep P r.isSome with
      | none => exact RestrictedReds.safeS_pure_true _
      | some s₁ =>
        dsimp only
        cases s₁.safeCh Δ P
        · exact RestrictedReds.safeS_pure_true _
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hmb : ok (if s.b then m₁ else m₀) = true := by
            split_ifs <;> simp [hm.1, hm.2]
          refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF, hmb]) fun res => ?_
          cases res
          · exact RestrictedReds.safeS_pure_true _
          · exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
              fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simDeliverDF (P, c))
      unfold DeliverForge.simDeliverDF DeliverForge.deliverQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr <;> cases s.inTransit P.other c
        all_goals first
          | exact RestrictedReds.safeS_pure_true _
          | exact RestrictedReds.safeS_bind_true
              (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
              fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simInjectDF (P, c))
      unfold DeliverForge.simInjectDF DeliverForge.injectQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simCorrDF P)
      unfold DeliverForge.simCorrDF DeliverForge.corrQueryDF
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF]) fun res => ?_
      cases res
      · exact RestrictedReds.safeS_pure_true _
      · exact RestrictedReds.safeS_bind_true
          (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
          fun _ => RestrictedReds.safeS_pure_true _
    · change RestrictedReds.SafeS Q _ _ (DeliverForge.simDeliverForgeDF (P, c, c'))
      unfold DeliverForge.simDeliverForgeDF DeliverForge.deliverForgeQuery
      refine RestrictedReds.safeS_get_bind fun s _ => ?_
      refine RestrictedReds.safeS_bind_query (by simp [Q, badSendMsgDF]) fun res => ?_
      cases res with
      | none => exact RestrictedReds.safeS_pure_true _
      | some rr =>
        cases rr
        · exact RestrictedReds.safeS_pure_true _
        · exact RestrictedReds.safeS_bind_true
            (RestrictedReds.safeS_set_true _ (fun _ _ => trivial))
            fun _ => RestrictedReds.safeS_pure_true _
  exact (RestrictedReds.SafePost.simulateQ_run
    (RestrictedReds.SafePost.of_isQueryBoundP hB) hstep trivial).bind
    fun _ _ => RestrictedReds.SafePost.pure trivial

end MoveCompatChallSimDF

section MoveCompatRedFSAuthDF

open ReductionsQueries

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [DecidableEq Pub] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

omit [DecidableEq Pub] [SampleableType KR] [SampleableType KC] in
private theorem qb_deliverForgeE'
    {Q : (RSpec SS RS T M E).Domain → Prop} [DecidablePred Q] (hQu : ∀ u, ¬ Q (.inl u))
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E) × (Header T × E)) :
    QB Q (DeliverForge.deliverForgeE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q)
      2 := by
  rcases q with ⟨P, c, c'⟩
  unfold DeliverForge.deliverForgeE
  refine qb_bind0 qb_get fun es => ?_
  dsimp only
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact qb_pure none 2
    | some r =>
      dsimp only
      by_cases h2 :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [h2, ↓reduceIte]
        exact qb_pure none 2
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine qb_bind_r
          (qb_liftH (qb_vRecv hQu cka prng fs Δcka mo j es.g P (es.g.st P) c' none))
          fun res => ?_
        cases res with
        | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
        | some inner =>
          cases inner with
          | none => exact qb_pure (some RecvResult.rejected) 0
          | some stim =>
            rcases stim with ⟨st', t', i', m'⟩
            dsimp only
            by_cases h3 : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
            · simp only [h3, ↓reduceIte]
              exact qb_pure (some RecvResult.rejected) 0
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              by_cases h4 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
              · simp only [h4, ↓reduceIte]
                refine qb_bind0
                  (qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
                  fun s₁? => ?_
                cases s₁? with
                | none => exact qb_pure none 0
                | some s₁ => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
              · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                split_ifs
                · exact qb_bind0 (qb_modify _) fun _ => qb_pure (some RecvResult.rejected) 0
                · exact qb_pure (some RecvResult.rejected) 0

omit [DecidableEq Pub] [SampleableType KR] [SampleableType KC] in
private theorem qb_deliverForgeE_one'
    {Q : (RSpec SS RS T M E).Domain → Prop} [DecidablePred Q] (hQu : ∀ u, ¬ Q (.inl u))
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E) × (Header T × E)) :
    QB Q (DeliverForge.deliverForgeE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q)
      1 := by
  rcases q with ⟨P, c, c'⟩
  unfold DeliverForge.deliverForgeE
  refine qb_bind0 qb_get fun es => ?_
  dsimp only
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact qb_pure none 1
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact qb_pure none 1
    | some r =>
      dsimp only
      by_cases h2 :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [h2, ↓reduceIte]
        exact qb_pure none 1
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine qb_bind_r
          (qb_liftH (qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c' none))
          fun res => ?_
        cases res with
        | none => exact qb_bind0 qb_abortE fun _ => qb_pure none 0
        | some inner =>
          cases inner with
          | none => exact qb_pure (some RecvResult.rejected) 0
          | some stim =>
            rcases stim with ⟨st', t', i', m'⟩
            dsimp only
            by_cases h3 : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
            · simp only [h3, ↓reduceIte]
              exact qb_pure (some RecvResult.rejected) 0
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              by_cases h4 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
              · simp only [h4, ↓reduceIte]
                refine qb_bind0
                  (qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
                  fun s₁? => ?_
                cases s₁? with
                | none => exact qb_pure none 0
                | some s₁ => exact qb_bind0 (qb_modify _) fun _ => qb_pure _ 0
              · simp only [h4, Bool.false_eq_true, ↓reduceIte]
                split_ifs
                · exact qb_bind0 (qb_modify _) fun _ => qb_pure (some RecvResult.rejected) 0
                · exact qb_pure (some RecvResult.rejected) 0

omit [DecidableEq Pub] in
theorem redFSAuthDF_queries
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j : ℕ)
    (tL : Option ℕ) (tStar : ℕ)
    (B : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) {q : ℕ}
    (hq : DeliverForge.MakesAtMostQueriesDF B q) :
    FSAEAD.MakesAtMostQueries (DeliverForge.redFSAuthDF cka prng fs lam Δcka qep j tL tStar B)
      (2 * q) := by
  let mo : Mode := ⟨true, tL, tStar⟩
  unfold FSAEAD.MakesAtMostQueries DeliverForge.redFSAuthDF
  change IsQueryBoundP
    (DeliverForge.engRunDF (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
      mo.cfg mo.policy (initFS cka prng fs lam mo j) {} false B >>= _)
    _ (2 * q)
  unfold DeliverForge.engRunDF
  refine isQueryBoundP_congr (p := QFS SS RS T M E) (by rintro (_ | _) <;> rfl) ?_
  have hinit : IsQueryBoundP ((initFS cka prng fs lam mo j).run {}) (QFS SS RS T M E) 0 :=
    qb_initFS (hQu_QFS SS RS T M E) cka prng fs lam mo j {}
  have hsim : ∀ es, IsQueryBoundP
      ((simulateQ (DeliverForge.implEDF (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
        mo.cfg mo.policy) B).run es) (QFS SS RS T M E) (2 * q) := by
    intro es
    refine simulateQ_run_of_step_mul hq ?_ ?_ es
    · rintro (u | (t | qdf)) ht s
      · nomatch ht
      · exact qb_implE_inr (hQu_QFS SS RS T M E) cka prng fs Δcka qep mo j t s
      · exact qb_deliverForgeE' (hQu_QFS SS RS T M E) cka prng fs Δcka qep mo j qdf s
    · rintro (u | t) ht s
      · exact qb_coinsE (hQu_QFS SS RS T M E) u s
      · exact absurd rfl ht
  rw [← Nat.add_zero (2 * q), ← Nat.zero_add (2 * q)]
  refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_sampleT (hQu_QFS SS RS T M E) Bool
  refine isQueryBoundP_bind hinit fun ⟨vs, h⟩ _ => ?_
  cases vs with
  | none => exact isQueryBoundP_pure (QFS SS RS T M E) none (2 * q)
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    dsimp only
    rw [← Nat.add_zero (2 * q)]
    exact isQueryBoundP_bind (hsim _) fun res _ =>
      isQueryBoundP_pure (QFS SS RS T M E) (some res) 0

omit [DecidableEq Pub] in
theorem redFSAuthDF_dec_queries
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j : ℕ)
    (tL : Option ℕ) (tStar : ℕ)
    (B : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E) {q : ℕ}
    (hq : DeliverForge.MakesAtMostQueriesDF B q) :
    FSAEAD.MakesAtMostDecQueries (DeliverForge.redFSAuthDF cka prng fs lam Δcka qep j tL tStar B)
      q := by
  let mo : Mode := ⟨true, tL, tStar⟩
  unfold FSAEAD.MakesAtMostDecQueries DeliverForge.redFSAuthDF
  change IsQueryBoundP
    (DeliverForge.engRunDF (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
      mo.cfg mo.policy (initFS cka prng fs lam mo j) {} false B >>= _)
    (QFSDec SS RS T M E) q
  unfold DeliverForge.engRunDF
  have hinit : IsQueryBoundP ((initFS cka prng fs lam mo j).run {}) (QFSDec SS RS T M E) 0 :=
    qb_initFS (hQu_QFSDec SS RS T M E) cka prng fs lam mo j {}
  have hsim : ∀ es, IsQueryBoundP
      ((simulateQ (DeliverForge.implEDF (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip
        mo.cfg mo.policy) B).run es) (QFSDec SS RS T M E) q := by
    intro es
    simpa only [Nat.one_mul] using
      (simulateQ_run_of_step_mul (k := 1) hq
        (fun t ht s => by
          rcases t with u | (t | qdf)
          · nomatch ht
          · exact qb_implE_inr_one (hQu_QFSDec SS RS T M E) (hQt_QFSDec SS RS T M E)
              (hQch_QFSDec SS RS T M E) (hQcs_QFSDec SS RS T M E) (hQcr_QFSDec SS RS T M E)
              cka prng fs Δcka qep mo j t s
          · exact qb_deliverForgeE_one' (hQu_QFSDec SS RS T M E) cka prng fs Δcka qep mo j qdf s)
        (fun t ht s => by
          rcases t with u | t
          · exact qb_coinsE (hQu_QFSDec SS RS T M E) u s
          · exact absurd rfl ht)
        es)
  rw [← Nat.add_zero q, ← Nat.zero_add q]
  refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_sampleT (hQu_QFSDec SS RS T M E) Bool
  refine isQueryBoundP_bind hinit fun ⟨vs, h⟩ _ => ?_
  cases vs with
  | none => exact isQueryBoundP_pure (QFSDec SS RS T M E) none q
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    dsimp only
    rw [← Nat.add_zero q]
    exact isQueryBoundP_bind (hsim _) fun res _ =>
      isQueryBoundP_pure (QFSDec SS RS T M E) (some res) 0

end MoveCompatRedFSAuthDF

end MoveCompat

end CryptoVerification.LibsignalSession.HeadlineV1
