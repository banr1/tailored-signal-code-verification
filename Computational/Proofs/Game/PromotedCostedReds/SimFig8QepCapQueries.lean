/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.GameProofDefs
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalRefinesCDefs
import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimC
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.QueryBounds

/-!
# Query Bound for `libsignalToModularSchemeSim`

Proves that `Refine.libsignalToModularSchemeSim` forwards at most `q` oracle queries to the
underlying Fig. 8 `SM` game when run on a `q`-query session adversary.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8QepCapQueries

open OracleSpec OracleComp
open CryptoGames (Party SMScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFS lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C Fig8Comp SimState)
open CryptoGames.Ratchet.LibsignalSimC
  (LibsignalToModularSchemeSimState idHook runOnBaseState liftC
   simSendC fwdAnswerC resyncC fwdC fwdEvictC simRecvC simCorrC guardC
   simImplC initSimC)
open CryptoGames.LibsignalSM.Refine (libsignalToModularSchemeSim)
open CryptoGames.LibsignalSession (Params IdentityKey PublicKey GhostState)
open CryptoGames.SM (RecvResult)
open CryptoGames.LibsignalSM.Proofs.QueryBounds
  (QInr hQu_QInr isQueryBoundP_congr isQueryBoundP_liftProb QB
   qb_simSend qb_fwd qb_onAccept qb_onAnswer)

noncomputable section

private def QBC {PQ Pt : Type} {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) (n : ℕ) : Prop :=
  ∀ sC : LibsignalToModularSchemeSimState PQ Pt ℓ, IsQueryBoundP (x.run sC) (QInr Pt ℓ) n

private theorem qbc_pure {PQ Pt α : Type} {ℓ : ℕ} (a : α) (n : ℕ) :
    QBC (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (pure a) n := fun _ => by simp

private theorem qbc_bind {PQ Pt α β : Type} {ℓ : ℕ}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β}
    {n m : ℕ} (hx : QBC x n) (hf : ∀ a, QBC (f a) m) : QBC (x >>= f) (n + m) := fun sC => by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (hx sC) fun p _ => hf p.1 p.2

private theorem qbc_bind0 {PQ Pt α β : Type} {ℓ : ℕ}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β}
    {m : ℕ} (hx : QBC x 0) (hf : ∀ a, QBC (f a) m) : QBC (x >>= f) m := by
  simpa using qbc_bind hx hf

private theorem qbc_bind_r {PQ Pt α β : Type} {ℓ : ℕ}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β}
    {n : ℕ} (hx : QBC x n) (hf : ∀ a, QBC (f a) 0) : QBC (x >>= f) n := by
  simpa using qbc_bind hx hf

private theorem qbc_ite {PQ Pt α : Type} {ℓ : ℕ} {c : Prop} [Decidable c]
    {x y : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hx : QBC x n) (hy : QBC y n) : QBC (if c then x else y) n := by
  by_cases hc : c <;> simp [hc, hx, hy]

private theorem qbc_get {PQ Pt : Type} {ℓ : ℕ} :
    QBC (get : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) _) 0 :=
  fun _ => by simp

private theorem qbc_set {PQ Pt : Type} {ℓ : ℕ} (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    QBC (set sC' : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit) 0 :=
  fun _ => by simp

private theorem qbc_modify {PQ Pt : Type} {ℓ : ℕ}
    (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    QBC (modify f : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) PUnit) 0 :=
  fun _ => by simp

private theorem qbc_guardC {PQ Pt α : Type} {ℓ : ℕ}
    {x : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α)} {n : ℕ}
    (hx : QBC x n) : QBC (guardC x) n := by
  unfold guardC
  exact qbc_bind0 qbc_get fun _ => qbc_ite (qbc_pure none n) hx

private theorem qbc_runOnBaseState {PQ Pt α : Type} {ℓ : ℕ}
    {x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α} {n : ℕ}
    (hx : QB (QInr Pt ℓ) x n) : QBC (runOnBaseState idHook x) n := fun sC => by
  show IsQueryBoundP (x.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 })) (QInr Pt ℓ) n
  rw [← Nat.add_zero n]
  exact isQueryBoundP_bind (hx sC.base) fun p _ => isQueryBoundP_pure (QInr Pt ℓ) _ 0

private theorem qbc_liftC_query {PQ Pt : Type} {ℓ : ℕ}
    (t : (CryptoGames.LibsignalSM.Proofs.QueryBounds.FSpec Pt ℓ).Domain) {d : ℕ}
    (hd : QInr Pt ℓ t → 0 < d) :
    QBC (PQ := PQ) (liftC (Pt := Pt) (ℓ := ℓ) idHook
      (query (spec := CryptoGames.LibsignalSM.Proofs.QueryBounds.FSpec Pt ℓ) t)) d := fun sC => by
  show IsQueryBoundP
    ((query (spec := CryptoGames.LibsignalSM.Proofs.QueryBounds.FSpec Pt ℓ) t : Fig8Comp Pt ℓ _) >>=
      fun a => pure (a, sC)) (QInr Pt ℓ) d
  rw [← Nat.add_zero d]
  exact isQueryBoundP_bind ((isQueryBoundP_query_iff (QInr Pt ℓ) t d).2 hd) fun a _ =>
    isQueryBoundP_pure (QInr Pt ℓ) (a, sC) 0

private theorem qbc_probe {PQ Pt : Type} {ℓ : ℕ} (Q : Party) (c' : Fig8C Pt) :
    QBC (PQ := PQ) (StateT.lift ((idHook (Pt := Pt) (ℓ := ℓ)).probe Q c')) 0 := fun sC => by
  show IsQueryBoundP (pure () >>= fun a => pure (a, sC)) (QInr Pt ℓ) 0
  simp

private theorem qbc_simSendC {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    QBC (simSendC (P := P) (qep := qep) (fig := fig) (H := idHook) Q m₀ chal r) 1 := by
  unfold simSendC
  refine qbc_bind_r (qbc_runOnBaseState (qb_simSend P qep 1 hQu_QInr
    (fun _ _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ _ _ => Nat.zero_lt_one) Q m₀ chal r))
    fun res => ?_
  cases res with
  | none => exact qbc_pure none 0
  | some w => exact qbc_bind0 qbc_get fun _ => qbc_bind0 (qbc_set _) fun _ => qbc_pure (some w) 0

private theorem qbc_fwdAnswerC {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : CryptoGames.FSAEADScheme (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (c' : Fig8C Pt) :
    QBC (fwdAnswerC (qep := qep) (fig := fig) (fs := fs) (H := idHook) Q w isDel ci? T pq' c') 1 := by
  unfold fwdAnswerC
  refine qbc_bind_r (qbc_runOnBaseState (qb_fwd 1 (fun _ _ _ => Nat.zero_lt_one)
    (fun _ _ _ => Nat.zero_lt_one) Q c')) fun res => ?_
  rcases res with _ | (_ | _)
  · exact qbc_runOnBaseState (qb_onAnswer qep Q w isDel ci? T pq' none)
  · exact qbc_runOnBaseState (qb_onAnswer qep Q w isDel ci? T pq' (some RecvResult.rejected))
  · exact qbc_bind0 (qbc_modify _) fun _ =>
      qbc_runOnBaseState (qb_onAnswer qep Q w isDel ci? T pq' _)

private theorem qbc_resyncC {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : CryptoGames.FSAEADScheme (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    QBC (resyncC (qep := qep) (fig := fig) (fs := fs) (H := idHook) Q w ci? T pq' c r) 1 := by
  unfold resyncC
  rcases r with _ | ⟨t, i, pm⟩
  · exact qbc_pure (some RecvResult.rejected) 1
  · refine qbc_bind_r (qbc_liftC_query _ (fun _ => Nat.zero_lt_one)) fun res => ?_
    rcases res with _ | (_ | _)
    · exact qbc_pure (some RecvResult.rejected) 0
    · exact qbc_pure (some RecvResult.rejected) 0
    · exact qbc_bind0 (qbc_modify _) fun _ =>
        qbc_runOnBaseState (qb_onAccept qep Q w true t i pm.2 ci? T pq')

private theorem qbc_fwdC {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : CryptoGames.FSAEADScheme (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    QBC (fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := idHook)
      Q w isDel ci? T pq' honestC c') 1 := by
  unfold fwdC
  refine qbc_bind0 qbc_get fun sC => ?_
  rcases honestC with _ | c
  · exact qbc_fwdAnswerC qep fig fs Q w isDel ci? T pq' c'
  · refine qbc_ite ?_ (qbc_fwdAnswerC qep fig fs Q w isDel ci? T pq' c')
    rcases CryptoGames.Ratchet.LibsignalSimC.predictReceiveWithSnapshots (fig := fig) (fs := fs)
        P sC Q w c c' with _ | r
    · exact qbc_bind0 (qbc_probe Q c') fun _ => qbc_pure (some RecvResult.rejected) 1
    · exact qbc_resyncC qep fig fs Q w ci? T pq' c r

private theorem qbc_fwdEvictC {PQ Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : CryptoGames.FSAEADScheme (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    QBC (fwdEvictC (qep := qep) (fig := fig) (fs := fs) (H := idHook) Q w isDel T pq' c') 1 := by
  unfold fwdEvictC
  refine qbc_bind0 qbc_get fun _ => ?_
  exact qbc_ite (qbc_bind0 (qbc_probe Q c') fun _ => qbc_pure (some RecvResult.rejected) 1)
    (qbc_fwdAnswerC qep fig fs Q w isDel none T pq' c')

private theorem qbc_simRecvC {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : CryptoGames.FSAEADScheme (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    QBC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs)
      (H := idHook) Q w isDel) 1 := by
  unfold simRecvC
  refine qbc_bind0 qbc_get fun _ => ?_
  refine qbc_ite (qbc_pure none 1) ?_
  refine qbc_ite (qbc_pure none 1) ?_
  refine qbc_ite (qbc_pure none 1) ?_
  refine qbc_ite (qbc_pure (some RecvResult.rejected) 1) ?_
  dsimp only []
  split
  · exact qbc_pure (some RecvResult.rejected) 1
  · refine qbc_ite (qbc_pure (some RecvResult.rejected) 1) ?_
    refine qbc_ite (qbc_pure (some RecvResult.rejected) 1) ?_
    split
    · exact qbc_pure (some RecvResult.rejected) 1
    · split
      · exact qbc_ite (qbc_pure (some RecvResult.rejected) 1)
          (qbc_fwdC P qep fig fs Q w isDel _ _ _ _ _)
      · refine qbc_ite (qbc_pure (some RecvResult.rejected) 1) ?_
        refine qbc_ite (qbc_pure (some RecvResult.rejected) 1) ?_
        refine qbc_ite (qbc_bind0 (qbc_modify _) fun _ => ?_) ?_
        all_goals
          refine qbc_ite (qbc_pure (some RecvResult.rejected) 1) ?_
          split
          · exact qbc_pure (some RecvResult.rejected) 1
          · exact qbc_ite (qbc_fwdEvictC qep fig fs Q w isDel _ _ _)
              (qbc_fwdC P qep fig fs Q w isDel none _ _ _ _)

private theorem qbc_simCorrC {PQ PQC Pt : Type} [Inhabited PQ] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Q : Party) :
    QBC (Pt := Pt) (ℓ := ℓ) (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q) 1 := by
  unfold simCorrC
  refine qbc_bind0 qbc_get fun _ => ?_
  refine qbc_ite (qbc_pure none 1) ?_
  refine qbc_bind_r (qbc_liftC_query _ (fun _ => Nat.zero_lt_one)) fun res => ?_
  rcases res with _ | st
  · exact qbc_pure none 0
  · exact qbc_bind0 (qbc_set _) fun _ => qbc_pure _ 0

private theorem qbc_simImplC_inr {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : CryptoGames.FSAEADScheme (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    QBC (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := idHook) Dh (.inr t)) 1 := by
  rcases t with ((((⟨Q, msg, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · have h1 : simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := idHook) Dh (.inr (.inl (.inl (.inl (.inl (Q, msg, rc)))))) =
      guardC (simSendC (P := P) (qep := qep) (fig := fig) (H := idHook)
        Q msg none rc) := rfl
    rw [h1]; exact qbc_guardC (qbc_simSendC P qep fig Q msg none rc)
  · have h1 : simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := idHook) Dh (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc)))))) =
      guardC (simSendC (P := P) (qep := qep) (fig := fig) (H := idHook)
        Q m₀ (some m₁) rc) := rfl
    rw [h1]; exact qbc_guardC (qbc_simSendC P qep fig Q m₀ (some m₁) rc)
  · have h1 : simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := idHook) Dh (.inr (.inl (.inl (.inr (Q, w))))) =
      guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs)
        (H := idHook) Q w true) := rfl
    rw [h1]; exact qbc_guardC (qbc_simRecvC P encT decT qep fig fs Q w true)
  · have h1 : simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := idHook) Dh (.inr (.inl (.inr (Q, w)))) =
      guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs)
        (H := idHook) Q w false) := rfl
    rw [h1]; exact qbc_guardC (qbc_simRecvC P encT decT qep fig fs Q w false)
  · have h1 : simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := idHook) Dh (.inr (.inr Q)) =
      guardC (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q) := rfl
    rw [h1]; exact qbc_guardC (qbc_simCorrC P Dh encT Q)

private theorem qbc_simImplC_inl {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (fs : CryptoGames.FSAEADScheme (BitVec 256)
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × CryptoGames.Ratchet.LibsignalInst.LibsignalCiphertextWithSalt32))
    (n : ℕ) :
    QBC (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := idHook) Dh (.inl n)) 0 := by
  have h1 : simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := idHook) Dh (.inl n) =
    liftC (Pt := Pt) (ℓ := ℓ) idHook
      (query (spec := CryptoGames.LibsignalSM.Proofs.QueryBounds.FSpec Pt ℓ) (.inl n)) := rfl
  rw [h1]
  exact qbc_liftC_query (.inl n) (fun h => absurd h (hQu_QInr n))

private theorem simRunCWith_makesAtMostQueries_of_imp {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (initPQ : BitVec 256 → LibsignalToModularSchemeSimState PQ Pt ℓ)
    (imp : QueryImpl
      (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ)))
    (hinl : ∀ n, QBC (imp (.inl n)) 0)
    (hinr : ∀ o, QBC (imp (.inr o)) 1)
    (q : ℕ) (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      (((idHook (Pt := Pt) (ℓ := ℓ)).lift
        (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256)) >>=
        fun pqrKey => (simulateQ imp A).run' (initPQ pqrKey)) : Fig8Comp Pt ℓ Bool) q := by
  unfold CryptoGames.SM.MakesAtMostQueries
  dsimp only [idHook]
  refine isQueryBoundP_congr (p := QInr Pt ℓ) (by rintro (_ | _) <;> rfl) ?_
  rw [← Nat.zero_add q]
  refine isQueryBoundP_bind (isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QInr ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hsim : IsQueryBoundP ((simulateQ imp A).run (initPQ pqrKey)) (QInr Pt ℓ) q := by
    refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ _
    · rintro (n | o) hp sC
      · cases hp
      · exact hinr o sC
    · rintro (n | o) hnp sC
      · exact hinl n sC
      · exact absurd rfl hnp
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

/-- `Refine.libsignalToModularSchemeSim` forwards at most `q` Fig. 8 oracle queries when run on a
`q`-query session adversary `A`. -/
theorem libsignalToModularSchemeSim_queries
    {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) q :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  simRunCWith_makesAtMostQueries_of_imp
    (fun pqrKey => initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := idHook) Dh)
    (qbc_simImplC_inl P Dh encT decT qep fig fs)
    (qbc_simImplC_inr P Dh encT decT qep fig fs)
    q A hq

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8QepCapQueries
