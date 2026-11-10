/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.LibsignalCorrNoInj
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalRefinesDefs
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalRefinesCDefs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux
import Computational.Tests.Sanity.LibsignalSimCFacts

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# Sanity Properties of `LibSimC` and `hiddenSaltTerm`

Sanity checks for the `LibSimC` simulation relation and hidden-salt error term:
- `hiddenSaltTerm_eq_zero_of_saltBinding`: under SPQR salt binding (`SpqrSaltBindingOn`),
  `hiddenSaltTerm` vanishes because honest SPQR messages always yield the sender's salt.
- `libSim_of_libSimC_weak` and `libsignal_refines_weak_of_C`: under `Corr.SpqrWeakCorrect` with no
  SPQR panics, `LibSimC` implies `LibSim`, recovering the `Refine.libsignal_refines_weak` bound
  from `Proofs.Refinement.libsignal_refines_C_proof` assuming `Dh.Commutes` and AES-CBC correctness.
- `hiddenSaltTerm_eq_zero_of_uncompromised`: `hiddenSaltTerm` vanishes when the adversary makes no
  `corr` queries and supplies no send coins.
-/

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA

namespace Refine

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

private theorem a6a_all_pure {α : Type} {a : α} {P : α → Prop} (h : P a) :
    ∀ x ∈ support (pure a : ProbComp α), P x := by
  intro x hx
  rw [support_pure, Set.mem_singleton_iff] at hx
  rwa [hx]

private theorem a6a_all_bind {α β : Type} {oa : ProbComp α} {f : α → ProbComp β}
    {P : α → Prop} {Q : β → Prop}
    (hoa : ∀ a ∈ support oa, P a) (hf : ∀ a, P a → ∀ b ∈ support (f a), Q b) :
    ∀ b ∈ support (oa >>= f), Q b := by
  intro b hb
  rw [MonadAttach.mem_support_bind] at hb
  rcases hb with ⟨a, ha, hb⟩
  exact hf a (hoa a ha) b hb

private theorem a6a_all_bind_const {α β : Type} (oa : ProbComp α) {f : α → ProbComp β}
    {Q : β → Prop} (hf : ∀ a, ∀ b ∈ support (f a), Q b) :
    ∀ b ∈ support (oa >>= f), Q b :=
  a6a_all_bind (fun _ _ => trivial) (fun a _ => hf a)

private theorem a6a_ite_pos {α : Type} {c : Prop} [Decidable c] {t e : α} (h : c) :
    (if c then t else e) = t := by
  split <;> [rfl; contradiction]

private theorem a6a_ite_neg {α : Type} {c : Prop} [Decidable c] {t e : α} (h : ¬c) :
    (if c then t else e) = e := by
  split <;> [contradiction; rfl]

private def a6a_Fig8StInv (Q : Party) (st : LibsignalSim.Fig8St Pt) : Prop :=
  st.id = Q ∧ (st.id.sendsIn (st.tcur + 1) = true ∨ st.vS.isSome = true)

private def a6a_Fig8GameInv {ℓ : ℕ}
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)) : Prop :=
  ∀ Q, a6a_Fig8StInv Q (g.st Q)

omit [DecidableEq Pt] [SampleableType Pt] in
private theorem a6a_fig8GameInv_init (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (maxSkip : ℕ) (lam : Pt)
    (k : BitVec 256 × BitVec 256) (b : Bool) :
    a6a_Fig8GameInv (initState (lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam) k b) := by
  intro Q
  cases Q
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem a6a_fig8GameInv_update_st {ℓ : ℕ}
    {g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)}
    (hg : a6a_Fig8GameInv g) (P : Party) (st' : LibsignalSim.Fig8St Pt)
    (hst' : a6a_Fig8StInv P st') :
    ∀ Q, a6a_Fig8StInv Q (Function.update g.st P st' Q) := by
  intro Q
  by_cases hQ : Q = P
  · subst hQ; simpa [Function.update] using hst'
  · simpa [Function.update, hQ] using hg Q

private theorem a6a_epMgmt_st_eq {St Msg C : Type}
    {s s₁ : SM.GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.st = s.st := by
  unfold SM.GameState.epMgmt at h
  split at h
  · split at h
    · cases h
    · injection h with h; subst h
      dsimp only
      split <;> rfl
  · split at h
    · cases h
    · injection h with h; subst h; rfl

omit [DecidableEq Pt] [SampleableType Pt] in
private theorem a6a_lFig8_send_inv_and_out (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (lam : Pt)
    (Q : Party) (st : LibsignalSim.Fig8St Pt) (hst : a6a_Fig8StInv Q st)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (coins : BitVec 256) :
    let out := (lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam).send st (pub, m) coins
    a6a_Fig8StInv Q out.1 ∧
      ∃ (hdr : Header Pt) (i : ℕ) (seed : BitVec 256),
        out.2 = (hdr, (i, ((lAead C codec ℓ encT idOf).movePubPartToAD (lPubOf codec)).enc
          seed (i, hdr) (pub, m))) := by
  intro out
  rcases hst with ⟨hid, hsends⟩
  unfold out lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG
  dsimp only
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ↓reduceIte]
    exact ⟨⟨hid, Or.inr rfl⟩, _, _, _, rfl⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    rcases hsends with h1 | hvS
    · exact absurd h1 hs
    · cases hv : st.vS with
      | none => simp [hv] at hvS
      | some v =>
        dsimp only
        exact ⟨⟨hid, Or.inr rfl⟩, _, _, _, rfl⟩

omit [DecidableEq Pt] [SampleableType Pt] in
private theorem a6a_lFig8_receive_inv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (lam : Pt)
    (Q : Party) (st st' : LibsignalSim.Fig8St Pt) (c : LibsignalSim.Fig8C Pt)
    (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (hst : a6a_Fig8StInv Q st)
    (hrecv : (lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam).receive st c =
      some (st', t, i, pm)) :
    a6a_Fig8StInv Q st' := by
  rcases hst with ⟨hid, hsends⟩
  unfold lFig8 SM.Construction.scheme SM.Construction.receive at hrecv
  dsimp only at hrecv
  by_cases hbad : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
  · simp only [hbad, ↓reduceIte] at hrecv; cases hrecv
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hrecv
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hbad
    have hnsend : st.id.sendsIn c.1.1 = false := hbad.1
    have hsucc_send : st.id.sendsIn (c.1.1 + 1) = true := by
      rw [hid] at hnsend ⊢
      cases Q <;> simp [Party.sendsIn] at hnsend ⊢ <;> omega
    by_cases ht : c.1.1 = st.tcur + 1
    · simp only [ht, ↓reduceIte] at hrecv
      cases hT : c.1.2 with
      | none => rw [hT] at hrecv; cases hrecv
      | some Tn =>
        rw [hT] at hrecv
        dsimp only at hrecv
        cases hvR : (Function.update st.vR (st.tcur + 1)
            (some ((lFS C codec ℓ encT idOf maxSkip).initReceiver
              ((rootPRNG C.F encPt).up st.root ((dhScheme Dh).receive st.γ Tn).2).2))) (st.tcur + 1) with
        | none => rw [hvR] at hrecv; cases hrecv
        | some v =>
          rw [hvR] at hrecv
          dsimp only at hrecv
          cases hfs : (lFS C codec ℓ encT idOf maxSkip).receive v c.1 c.2 with
          | none => rw [hfs] at hrecv; cases hrecv
          | some vim =>
            rw [hfs] at hrecv
            injection hrecv with hrecv
            injection hrecv with hst' _
            subst hst'
            rw [← ht]
            exact ⟨hid, Or.inl hsucc_send⟩
    · simp only [ht, ↓reduceIte] at hrecv
      cases hvR : st.vR c.1.1 with
      | none => rw [hvR] at hrecv; cases hrecv
      | some v =>
        rw [hvR] at hrecv
        dsimp only at hrecv
        cases hfs : (lFS C codec ℓ encT idOf maxSkip).receive v c.1 c.2 with
        | none => rw [hfs] at hrecv; cases hrecv
        | some vim =>
          rw [hfs] at hrecv
          injection hrecv with hrecv
          injection hrecv with hst' _
          subst hst'
          exact ⟨hid, hsends⟩

omit [SampleableType Pt] in
private theorem a6a_fig8ImplH1_step_inv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (lam : Pt) (qepF : ℕ)
    (q : (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (LibsignalSim.Fig8C Pt)).Domain)
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt))
    (hg : a6a_Fig8GameInv g) :
    ∀ z ∈ support ((LibsignalSimC.fig8ImplH1
      (lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam) qepF q).run g),
      a6a_Fig8GameInv z.2 := by
  set fig := lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam
  rcases q with u | ⟨⟨⟨⟨⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩⟩ | ⟨P, c⟩⟩ | ⟨P, c⟩⟩ | P⟩
  · change ∀ z ∈ support ((StateT.lift (QueryImpl.ofLift unifSpec ProbComp u)).run g), _
    rw [StateT.run_lift]
    exact a6a_all_bind_const _ fun _ => a6a_all_pure hg
  · change ∀ z ∈ support ((SM.transmitImpl fig 3 qepF (P, m, r)).run g), _
    unfold SM.transmitImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hwin : g.win = true
    · simp only [hwin, ↓reduceIte]; exact a6a_all_pure hg
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind]
      refine a6a_all_bind_const _ fun cb => ?_
      cases hepm : g.epMgmt 3 qepF P cb.2 with
      | none => exact a6a_all_pure hg
      | some s₁ =>
        simp only [StateT.run_bind, StateT.run_set, pure_bind]
        refine a6a_all_pure ?_
        have hst_eq := a6a_epMgmt_st_eq hepm
        have hsend := (a6a_lFig8_send_inv_and_out Dh encPt C codec ℓ encT idOf maxSkip lam
          P (s₁.st P) (hst_eq ▸ hg P) m.1 m.2 cb.1).1
        have hgs₁ : a6a_Fig8GameInv s₁ := fun Q => hst_eq ▸ hg Q
        exact a6a_fig8GameInv_update_st hgs₁ P _ hsend
  · change ∀ z ∈ support ((SM.challImpl fig 3 qepF SM.Config.h1 (P, m₀, m₁, r)).run g), _
    unfold SM.challImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hwin : g.win = true
    · simp only [hwin, ↓reduceIte]; exact a6a_all_pure hg
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind]
      refine a6a_all_bind_const _ fun cb => ?_
      cases hepm : g.epMgmt 3 qepF P cb.2 with
      | none => exact a6a_all_pure hg
      | some s₁ =>
        by_cases hok : (!s₁.safeCh 3 P || !(SM.Config.h1 (Msg := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s₁.epoch P)) = true
        · simp only [hok, ↓reduceIte]; exact a6a_all_pure hg
        · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind]
          refine a6a_all_pure ?_
          have hst_eq := a6a_epMgmt_st_eq hepm
          set m := ((SM.Config.h1 (Msg := LibsignalMsgPublicPart × Plain ℓ)).challMsg (s₁.epoch P)).getD (if g.b then m₁ else m₀)
          have hsend := (a6a_lFig8_send_inv_and_out Dh encPt C codec ℓ encT idOf maxSkip lam
            P (s₁.st P) (hst_eq ▸ hg P) m.1 m.2 cb.1).1
          have hgs₁ : a6a_Fig8GameInv s₁ := fun Q => hst_eq ▸ hg Q
          exact a6a_fig8GameInv_update_st hgs₁ P _ hsend
  · change ∀ z ∈ support ((SM.deliverImpl fig SM.Config.h1 (P, c)).run g), _
    unfold SM.deliverImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hwin : g.win = true
    · simp only [hwin, ↓reduceIte]; exact a6a_all_pure hg
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
      cases htr : g.inTransit P.other c with
      | none => exact a6a_all_pure hg
      | some r =>
        dsimp only
        cases hrecv : fig.receive (g.st P) c with
        | none =>
          dsimp only
          split <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] <;>
            exact a6a_all_pure hg
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          dsimp only
          have hst' := a6a_lFig8_receive_inv Dh encPt C codec ℓ encT idOf maxSkip lam
            P (g.st P) st' c t' i' m' (hg P) hrecv
          have hacc : a6a_Fig8GameInv (g.accept P st' r.pos) :=
            a6a_fig8GameInv_update_st hg P st' hst'
          split <;> simp only [StateT.run_bind, StateT.run_set, pure_bind] <;>
            exact a6a_all_pure hacc
  · change ∀ z ∈ support ((SM.injectImpl fig 3 qepF SM.Config.h1 (P, c)).run g), _
    unfold SM.injectImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hguard : (g.win || (g.inTransit P.other c).isSome || !g.safeInj 3) = true
    · simp only [hguard, ↓reduceIte]; exact a6a_all_pure hg
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
      cases hrecv : fig.receive (g.st P) c with
      | none => exact a6a_all_pure hg
      | some res =>
        rcases res with ⟨st', t', i', m'⟩
        dsimp only
        by_cases hcap : qepF + 1 < t'
        · simp only [hcap, ↓reduceIte]; exact a6a_all_pure hg
        · simp only [hcap, ↓reduceIte]
          have hst' := a6a_lFig8_receive_inv Dh encPt C codec ℓ encT idOf maxSkip lam
            P (g.st P) st' c t' i' m' (hg P) hrecv
          have hacc : a6a_Fig8GameInv (g.accept P st' ⟨P.other, t', i'⟩) :=
            a6a_fig8GameInv_update_st hg P st' hst'
          by_cases htriv : g.trivial 3 ⟨P.other, t', i'⟩ = true
          · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind]
            exact a6a_all_pure hacc
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
            split <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] <;>
              exact a6a_all_pure hg
  · change ∀ z ∈ support ((SM.corrImpl P).run g), _
    unfold SM.corrImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact a6a_all_pure hg
    · simp only [StateT.run_bind, StateT.run_set, pure_bind]
      exact a6a_all_pure hg

omit [SampleableType Pt] in
private theorem a6a_simulateQ_fig8ImplH1_inv {α : Type} (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (lam : Pt) (qepF : ℕ)
    (oa : LibsignalSim.Fig8Comp Pt ℓ α)
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt))
    (hg : a6a_Fig8GameInv g) :
    ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1
      (lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam) qepF) oa).run g),
      a6a_Fig8GameInv z.2 := by
  induction oa using OracleComp.inductionOn generalizing g with
  | pure a => exact a6a_all_pure hg
  | query_bind q cont ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    exact a6a_all_bind
      (a6a_fig8ImplH1_step_inv Dh encPt C codec ℓ encT idOf maxSkip lam qepF q g hg)
      (fun z hz => ih z.1 z.2 hz)

omit [SampleableType Pt] in
private theorem a6a_fig8ImplH1_send_out (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) (lam : Pt) (qepF : ℕ)
    (Q : Party) (pub : LibsignalMsgPublicPart) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (rc : Option (BitVec 256))
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt))
    (hg : a6a_Fig8GameInv g) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam
    let q_oa : LibsignalSim.Fig8Comp Pt ℓ (Option (LibsignalSim.Fig8C Pt)) :=
      match chal with
      | none => SM.transmitQuery (St := LibsignalSim.Fig8St Pt) Q (pub, m₀) rc
      | some m₁ => SM.challQuery (St := LibsignalSim.Fig8St Pt) Q (pub, m₀) (pub, m₁) rc
    ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF) q_oa).run g),
      a6a_Fig8GameInv z.2 ∧
        ∀ c, z.1 = some c →
          ∃ (hdr : Header Pt) (i : ℕ) (seed : BitVec 256) (m_eff : Plain ℓ),
            c = (hdr, (i, ((lAead C codec ℓ encT idOf).movePubPartToAD (lPubOf codec)).enc
              seed (i, hdr) (pub, m_eff))) := by
  intro fig q_oa z hz
  refine ⟨a6a_simulateQ_fig8ImplH1_inv Dh encPt C codec ℓ encT idOf maxSkip lam qepF q_oa g hg z hz, ?_⟩
  cases chal with
  | none =>
    change z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF)
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
        (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Q, (pub, m₀), rc))))))))).run g) at hz
    rw [simulateQ_query] at hz
    change z ∈ support ((id <$> SM.transmitImpl fig 3 qepF (Q, (pub, m₀), rc)).run g) at hz
    rw [id_map] at hz
    unfold SM.transmitImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hwin : g.win = true
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; intro c hc; cases hc
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hepm : g.epMgmt 3 qepF Q cb.2 with
      | none =>
        rw [hepm] at hz
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; intro c hc; cases hc
      | some s₁ =>
        rw [hepm] at hz
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        intro c hc
        injection hc with hc; subst hc
        have hst_eq := a6a_epMgmt_st_eq hepm
        rcases (a6a_lFig8_send_inv_and_out Dh encPt C codec ℓ encT idOf maxSkip lam
          Q (s₁.st Q) (hst_eq ▸ hg Q) pub m₀ cb.1).2 with ⟨hdr, i, seed, hout⟩
        exact ⟨hdr, i, seed, m₀, hout⟩
  | some m₁ =>
    change z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF)
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
        (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Q, (pub, m₀), (pub, m₁), rc))))))))).run g) at hz
    rw [simulateQ_query] at hz
    change z ∈ support ((id <$> SM.challImpl fig 3 qepF SM.Config.h1 (Q, (pub, m₀), (pub, m₁), rc)).run g) at hz
    rw [id_map] at hz
    unfold SM.challImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hwin : g.win = true
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; intro c hc; cases hc
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hepm : g.epMgmt 3 qepF Q cb.2 with
      | none =>
        rw [hepm] at hz
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; intro c hc; cases hc
      | some s₁ =>
        rw [hepm] at hz
        by_cases hok : (!s₁.safeCh 3 Q || !(SM.Config.h1 (Msg := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s₁.epoch Q)) = true
        · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; intro c hc; cases hc
        · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          intro c hc
          injection hc with hc; subst hc
          have hst_eq := a6a_epMgmt_st_eq hepm
          have hm_eq : ((SM.Config.h1 (Msg := LibsignalMsgPublicPart × Plain ℓ)).challMsg (s₁.epoch Q)).getD
              (if g.b then (pub, m₁) else (pub, m₀)) =
              (pub, if g.b then m₁ else m₀) := by
            cases g.b <;> rfl
          rw [hm_eq]
          rcases (a6a_lFig8_send_inv_and_out Dh encPt C codec ℓ encT idOf maxSkip lam
            Q (s₁.st Q) (hst_eq ▸ hg Q) pub (if g.b then m₁ else m₀) cb.1).2 with ⟨hdr, i, seed, hout⟩
          exact ⟨hdr, i, seed, if g.b then m₁ else m₀, hout⟩

private def a6a_HonestEntry (P : Params PQ PQC) (Inv : PQ → Prop)
    (wc : List (BitVec 8) × LibsignalSim.Fig8C Pt) : Prop :=
  ∃ h₀ body₀,
    (signalWireCodec P.codec).parse (wc.1.take (wc.1.length - 8)) = some (h₀, body₀) ∧
    ∀ pq_st pq' salt, Inv pq_st → P.spqr.recv pq_st h₀.pqRatchet = .ok (pq', salt) →
      effectiveHkdfSalt32 salt = wc.2.2.2.2

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_honestEntry_of_lAead_enc (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (Q : Party) (hdr : Header Pt) (i : ℕ) (seed : BitVec 256)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg))
    (hsalt : pub.salt = effectiveHkdfSalt32 salt)
    (hpqInv : Inv pq_st) :
    let c : LibsignalSim.Fig8C Pt :=
      (hdr, (i, ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
        seed (i, hdr) (pub, m)))
    a6a_HonestEntry P Inv (LibsignalSim.toWire c, c) := by
  intro c
  set h_hdr := lHeader encT i hdr pub
  set mk := deriveMessageKeys P.C.F (some pub.salt) (keyToBytes32 seed)
  set body := ((cbcPkcs7EncryptOnly P.C.E ℓ).enc (mk.1.1, mk.1.2) m).toList.flatMap blockToBytesLE
  set ser := (signalWireCodec P.codec).encode h_hdr body
  set tag := (hmacScheme P.C.F).tag mk.2 ((lIds idOf hdr.1).toList ++ ser)
  have hc_eq : c = (hdr, (i, ((ser, tag), pub.salt))) := rfl
  set w := LibsignalSim.toWire c
  have hw_eq : w = ser ++ LibsignalSim.tagBytes tag := rfl
  have htag_len : (LibsignalSim.tagBytes tag).length = 8 :=
    Proofs.Refinement.length_tagBytes tag
  have hw_sub : w.length - 8 = ser.length := by
    rw [hw_eq, List.length_append, htag_len]; omega
  have htake : w.take (w.length - 8) = ser := by
    rw [hw_sub, hw_eq, List.take_left]
  have hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h_hdr, body) := by
    rw [htake]
    refine Proofs.RoundTrip.parse_of_rt hrt hL h_hdr body rfl
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (Proofs.RoundTrip.length_cbcBody _)
    change Proofs.RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
  refine ⟨h_hdr, body, hparse, fun pq_st₂ pq₂' salt₂ hpqInv₂ hrecv => ?_⟩
  have hsalt_eq : salt₂ = salt :=
    hW1 pq_st rq pq' salt pub.pqmsg hpqInv hspqr_send pq_st₂ pq₂' salt₂ hpqInv₂ hrecv
  rw [hsalt_eq]
  exact hsalt.symm

private def a6a_BaseInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (s : LibsignalSim.SimState PQ Pt ℓ) : Prop :=
  (∀ Q, Inv (s.pq Q)) ∧ (∀ wc ∈ s.honest, a6a_HonestEntry P Inv wc)

private def a6a_FullInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool) : Prop :=
  a6a_BaseInv P Inv sC.base ∧ a6a_Fig8GameInv gh.1 ∧ gh.2 = false

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_baseInv_update_pq (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    {s : LibsignalSim.SimState PQ Pt ℓ} (hbase : a6a_BaseInv P Inv s)
    (Q : Party) {pq' : PQ} (hpq' : Inv pq') :
    ∀ R, Inv (Function.update s.pq Q pq' R) := by
  intro R
  by_cases hR : R = Q
  · subst hR; simpa [Function.update] using hpq'
  · simpa [Function.update, hR] using hbase.1 R

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6a_mem_support_liftC {α : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (qepF : ℕ) (x : LibsignalSim.Fig8Comp Pt ℓ α)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    {w : (α × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
      (GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)}
    (hw : w ∈ support (((LibsignalSimC.liftC (LibsignalSimC.probeHook fig qepF) x).run sC).run gh)) :
    (w.1.1, w.2.1) ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF) x).run gh.1) ∧
      w.1.2 = sC ∧ w.2.2 = gh.2 := by
  unfold LibsignalSimC.liftC at hw
  rw [StateT.run_lift, StateT.run_bind, LibsignalSimC.probeHook_lift_run] at hw
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hw
  rcases hw with ⟨⟨a, g'⟩, hmem, rfl⟩
  exact ⟨hmem, rfl, rfl⟩

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_liftC_fullInv {α : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qepF : ℕ)
    (Inv : PQ → Prop) (x : LibsignalSim.Fig8Comp Pt ℓ α)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ w ∈ support (((LibsignalSimC.liftC (LibsignalSimC.probeHook fig qepF) x).run sC).run gh),
      a6a_FullInv P Inv w.1.2 w.2 ∧ w.1.2 = sC := by
  intro fig w hw
  rcases hfull with ⟨hbase, hg, hflag⟩
  rcases a6a_mem_support_liftC fig qepF x sC gh hw with ⟨hmem, hsC, hflag'⟩
  refine ⟨⟨hsC ▸ hbase, ?_, hflag'.trans hflag⟩, hsC⟩
  exact a6a_simulateQ_fig8ImplH1_inv Dh encPt P.C P.codec ℓ encT idOf 25000 lam qepF x gh.1 hg _ hmem

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6a_mem_support_zoomB {α : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (qepF : ℕ)
    (x : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    {w : (α × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
      (GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)}
    (hw : w ∈ support (((LibsignalSimC.runOnBaseState (LibsignalSimC.probeHook fig qepF) x).run sC).run gh)) :
    ((w.1.1, w.1.2.base), w.2.1) ∈
      support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF) (x.run sC.base)).run gh.1) ∧
    w.2.2 = gh.2 := by
  change w ∈ support ((((LibsignalSimC.probeHook fig qepF).lift (x.run sC.base)) >>= fun as' =>
    pure (as'.1, { sC with base := as'.2 })).run gh) at hw
  rw [StateT.run_bind, LibsignalSimC.probeHook_lift_run] at hw
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hw
  rcases hw with ⟨⟨⟨a, s'⟩, g'⟩, hmem, rfl⟩
  exact ⟨hmem, rfl⟩

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_zoomB_fullInv {α : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qepF : ℕ)
    (Inv : PQ → Prop)
    (x : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh)
    (hbase_step :
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF) (x.run sC.base)).run gh.1),
        a6a_BaseInv P Inv z.1.2) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ w ∈ support (((LibsignalSimC.runOnBaseState (LibsignalSimC.probeHook fig qepF) x).run sC).run gh),
      a6a_FullInv P Inv w.1.2 w.2 := by
  intro fig w hw
  rcases hfull with ⟨hbase, hg, hflag⟩
  rcases a6a_mem_support_zoomB fig qepF x sC gh hw with ⟨hmem, hflag'⟩
  refine ⟨hbase_step _ hmem, ?_, hflag'.trans hflag⟩
  exact a6a_simulateQ_fig8ImplH1_inv Dh encPt P.C P.codec ℓ encT idOf 25000 lam qepF
    (x.run sC.base) gh.1 hg _ hmem

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_fwd_baseInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : LibsignalSim.Fig8C Pt)
    (s : LibsignalSim.SimState PQ Pt ℓ) (hbase : a6a_BaseInv P Inv s)
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)) :
    ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF)
      ((LibsignalSim.fwd Q c').run s)).run g),
      a6a_BaseInv P Inv z.1.2 := by
  unfold LibsignalSim.fwd LibsignalSim.liftQ
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;>
    simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] <;>
    exact a6a_all_bind_const _ fun _ => a6a_all_pure hbase

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_onAnswer_baseInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (qep qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (hpq' : Inv pq')
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : LibsignalSim.SimState PQ Pt ℓ) (hbase : a6a_BaseInv P Inv s)
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)) :
    ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF)
      ((LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res).run s)).run g),
      a6a_BaseInv P Inv z.1.2 := by
  have hup : a6a_BaseInv P Inv { s with pq := Function.update s.pq Q pq' } :=
    ⟨a6a_baseInv_update_pq P Inv hbase Q hpq', hbase.2⟩
  unfold LibsignalSim.onAnswer LibsignalSim.onAccept LibsignalSim.putS
  cases res with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact a6a_all_pure hbase
  | some r =>
    cases r with
    | rejected =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact a6a_all_pure hbase
    | accepted t i pm =>
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases isDel
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · simp only [StateT.run_pure, simulateQ_pure]
          exact a6a_all_pure hbase
        · split <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
          · exact a6a_all_pure hup
          · exact a6a_all_pure hbase
      · simp only [↓reduceIte]
        cases s.mir.inTransit Q.other w with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure]
          exact a6a_all_pure hbase
        | some rec =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
          exact a6a_all_pure hup

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_fwdAnswerC_fullInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (hpq' : Inv pq') (c' : LibsignalSim.Fig8C Pt)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    ∀ z ∈ support (((LibsignalSimC.fwdAnswerC (qep := qep) (fig := fig) (fs := fs)
      (H := LibsignalSimC.probeHook fig (qep + 1)) Q w isDel ci? T pq' c').run sC).run gh),
      a6a_FullInv P Inv z.1.2 z.2 := by
  intro fig fs
  unfold LibsignalSimC.fwdAnswerC
  simp only [StateT.run_bind]
  refine a6a_all_bind
    (a6a_zoomB_fullInv P Dh encPt encT idOf lam (qep + 1) Inv (LibsignalSim.fwd Q c') sC gh hfull
      (a6a_fwd_baseInv P Inv fig (qep + 1) Q c' sC.base hfull.1 gh.1))
    fun w₁ hw₁ => ?_
  cases hres : w₁.1.1 with
  | none =>
    exact a6a_zoomB_fullInv P Dh encPt encT idOf lam (qep + 1) Inv
      (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' none) w₁.1.2 w₁.2 hw₁
      (a6a_onAnswer_baseInv P Inv fig qep (qep + 1) Q w isDel ci? T pq' hpq' none w₁.1.2.base hw₁.1 w₁.2.1)
  | some r =>
    cases r with
    | rejected =>
      exact a6a_zoomB_fullInv P Dh encPt encT idOf lam (qep + 1) Inv
        (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' (some .rejected)) w₁.1.2 w₁.2 hw₁
        (a6a_onAnswer_baseInv P Inv fig qep (qep + 1) Q w isDel ci? T pq' hpq' (some .rejected) w₁.1.2.base hw₁.1 w₁.2.1)
    | accepted t i pm =>
      simp only [StateT.run_bind, StateT.run_modify, pure_bind]
      exact a6a_zoomB_fullInv P Dh encPt encT idOf lam (qep + 1) Inv
        (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' (some (.accepted t i pm))) _ w₁.2 hw₁
        (a6a_onAnswer_baseInv P Inv fig qep (qep + 1) Q w isDel ci? T pq' hpq' (some (.accepted t i pm)) w₁.1.2.base hw₁.1 w₁.2.1)

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_fwdC_run_eq_fwdAnswerC (P : Params PQ PQC) {ℓ : ℕ}
    (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    {M : Type → Type} [Monad M] [LawfulMonad M] (H : LibsignalSimC.Hook Pt ℓ M)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (LibsignalSim.Fig8C Pt)) (c' : LibsignalSim.Fig8C Pt)
    (hc' : ∀ c, honestC = some c → c = c')
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (LibsignalSimC.fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := H)
      Q w isDel ci? T pq' honestC c').run sC =
    (LibsignalSimC.fwdAnswerC (qep := qep) (fig := fig) (fs := fs) (H := H)
      Q w isDel ci? T pq' c').run sC := by
  unfold LibsignalSimC.fwdC
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases honestC with
  | none => rfl
  | some c =>
    have hcc : c = c' := hc' c rfl
    subst hcc
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_fwdC_fullInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (hpq' : Inv pq') (honestC : Option (LibsignalSim.Fig8C Pt))
    (c' : LibsignalSim.Fig8C Pt) (hc' : ∀ c, honestC = some c → c = c')
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    ∀ z ∈ support (((LibsignalSimC.fwdC (P := P) (qep := qep) (fig := fig) (fs := fs)
      (H := LibsignalSimC.probeHook fig (qep + 1)) Q w isDel ci? T pq' honestC c').run sC).run gh),
      a6a_FullInv P Inv z.1.2 z.2 := by
  intro fig fs
  rw [a6a_fwdC_run_eq_fwdAnswerC P qep fig fs _ Q w isDel ci? T pq' honestC c' hc' sC]
  exact a6a_fwdAnswerC_fullInv P Inv Dh encPt encT idOf lam qep Q w isDel ci? T pq' hpq' c' sC gh hfull

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_honestC_salt_eq (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (s : LibsignalSim.SimState PQ Pt ℓ) (hbase : a6a_BaseInv P Inv s)
    (Q : Party) (w : List (BitVec 8)) (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (pq' : PQ) (salt : HKDF.Salt)
    (hrecv : P.spqr.recv (s.pq Q) h.pqRatchet = .ok (pq', salt))
    (c : LibsignalSim.Fig8C Pt)
    (hhon : ((s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)) = some c) :
    c.2.2.2 = effectiveHkdfSalt32 salt := by
  rw [Option.map_eq_some_iff] at hhon
  rcases hhon with ⟨wc, hfind, rfl⟩
  have hmem : wc ∈ s.honest := List.mem_of_find?_eq_some hfind
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  rcases hbase.2 wc hmem with ⟨h₀, body₀, hparse₀, hsalt⟩
  rw [hpred.1, hparse] at hparse₀
  injection hparse₀ with hpair
  injection hpair with hh _
  subst hh
  exact (hsalt (s.pq Q) pq' salt (hbase.1 Q) hrecv).symm

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_simRecvC_fullInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (hI : Corr.SpqrInvClosed P.spqr Inv)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    ∀ z ∈ support (((LibsignalSimC.simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := LibsignalSimC.probeHook fig (qep + 1)) Q w isDel).run sC).run gh),
      a6a_FullInv P Inv z.1.2 z.2 := by
  intro fig fs
  unfold LibsignalSimC.simRecvC
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  by_cases h1 : sC.base.mir.win = true
  · rw [a6a_ite_pos h1, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
  rw [a6a_ite_neg h1]
  by_cases h2 : (isDel && (sC.base.mir.inTransit Q.other w).isNone) = true
  · rw [a6a_ite_pos h2, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
  rw [a6a_ite_neg h2]
  by_cases h3 : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3)
      || !(ratchetKeyAdmissible P.codec decT encT w))) = true
  · rw [a6a_ite_pos h3, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
  rw [a6a_ite_neg h3]
  by_cases h4 : w.length < 9
  · rw [a6a_ite_pos h4, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
  rw [a6a_ite_neg h4]
  cases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => rw [StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
  | some hbody =>
    rcases hbody with ⟨h, body⟩
    dsimp only
    by_cases h5 : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
    · rw [a6a_ite_pos h5, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
    rw [a6a_ite_neg h5]
    by_cases hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · rw [a6a_ite_pos hpan, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
    rw [a6a_ite_neg hpan]
    cases hrecv : P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => rw [StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
    | ok pqs =>
      rcases pqs with ⟨pq', salt⟩
      dsimp only
      have hpq' : Inv pq' := hI.recv (sC.base.pq Q) h.pqRatchet pq' salt (hfull.1.1 Q) hrecv
      set honestC := (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      set mkC := fun (t : ℕ) (T : Option Pt) =>
        match honestC with
        | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c else
            ((t, T), (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
        | none =>
            ((t, T), (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
      have hmkC (t : ℕ) (T : Option Pt) :
          ∀ c : LibsignalSim.Fig8C Pt, honestC = some c →
            c = mkC t T := by
        intro c hc
        have hsalt := a6a_honestC_salt_eq P Inv sC.base hfull.1 Q w h body hparse pq' salt hrecv c hc
        dsimp only [mkC]
        rw [hc]
        dsimp only
        rw [a6a_ite_pos hsalt]
      cases (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        by_cases hrej : ((sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects (h.counter.toNat + 1) = true
        · rw [a6a_ite_pos hrej, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
        · rw [a6a_ite_neg hrej]
          exact a6a_fwdC_fullInv P Inv Dh encPt encT idOf lam qep Q w isDel (some ci)
            h.senderRatchetKey pq' hpq' honestC _ (hmkC _ _) sC gh hfull
      | none =>
        dsimp only
        by_cases hev : ((honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = true
        ·
          have hcomb : (((honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) &&
              ((honestC.map fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true)) = true := by
            rw [hev, Bool.true_and]
            cases hc : honestC with
            | none => rw [hc] at hev; simp at hev
            | some c =>
              have hsalt := a6a_honestC_salt_eq P Inv sC.base hfull.1 Q w h body hparse pq' salt hrecv c hc
              simp [hsalt]
          rw [a6a_ite_pos hcomb, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
        have hevF : ((honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true) = false :=
          Bool.eq_false_iff.mpr hev
        simp only [hevF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        by_cases hzero : (decT h.senderRatchetKey == some 0) = true
        · rw [a6a_ite_pos hzero, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull
        rw [a6a_ite_neg hzero]
        have hrest (sC₁ : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (hfull₁ : a6a_FullInv P Inv sC₁ gh) :
            ∀ z ∈ support (((if LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q || 25000 < h.counter.toNat + 1 - 1 || 2 ^ 32 ≤ h.counter.toNat + 1 then
              pure (some RecvResult.rejected)
            else
              match decT h.senderRatchetKey with
              | none => pure (some RecvResult.rejected)
              | some T =>
                LibsignalSimC.fwdC (P := P) (qep := qep) (fig := fig) (fs := fs)
                  (H := LibsignalSimC.probeHook fig (qep + 1))
                  Q w isDel none h.senderRatchetKey pq' honestC
                  (mkC (sC.base.mir.epoch Q + 1) (some T))).run sC₁).run gh),
            a6a_FullInv P Inv z.1.2 z.2 := by
          by_cases hwin2 : (LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q || 25000 < h.counter.toNat + 1 - 1 || 2 ^ 32 ≤ h.counter.toNat + 1) = true
          · rw [a6a_ite_pos hwin2, StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull₁
          rw [a6a_ite_neg hwin2]
          cases decT h.senderRatchetKey with
          | none => rw [StateT.run_pure, StateT.run_pure]; exact a6a_all_pure hfull₁
          | some T =>
            exact a6a_fwdC_fullInv P Inv Dh encPt encT idOf lam qep Q w isDel none
              h.senderRatchetKey pq' hpq' honestC _ (hmkC _ _) sC₁ gh hfull₁
        by_cases hamb : (LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
            (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))) = true
        · rw [a6a_ite_pos hamb, StateT.run_bind, StateT.run_modify, pure_bind]
          exact hrest _ hfull
        · rw [a6a_ite_neg hamb]
          exact hrest sC hfull

omit [SampleableType Pt] [Inhabited PQ] in
private theorem a6a_simSend_coins {α : Type} {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (maxSkip : ℕ) (lam : Pt) (qepF : ℕ)
    (r : Option PQC)
    (f : PQC → Option (BitVec 256) → StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α)
    (s : LibsignalSim.SimState PQ Pt ℓ)
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt))
    (hg : a6a_Fig8GameInv g)
    {Q_post : (α × LibsignalSim.SimState PQ Pt ℓ) ×
      GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) → Prop}
    (hf : ∀ rq rc g₁, a6a_Fig8GameInv g₁ →
      ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 (lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam) qepF)
        ((f rq rc).run s)).run g₁), Q_post z) :
    ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 (lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam) qepF)
      ((do
        let rq ← match r with | some rq => pure rq | none => LibsignalSim.coin PQC
        let rc ← match r with | some _ => some <$> LibsignalSim.coin (BitVec 256) | none => pure none
        f rq rc).run s)).run g), Q_post z := by
  cases r with
  | none =>
    dsimp only
    unfold LibsignalSim.coin LibsignalSim.liftQ
    simp only [pure_bind, StateT.run_bind, StateT.run_lift, bind_assoc, simulateQ_bind]
    exact a6a_all_bind
      (a6a_simulateQ_fig8ImplH1_inv Dh encPt C codec ℓ encT idOf maxSkip lam qepF
        (liftM ($ᵗ PQC : ProbComp PQC)) g hg)
      fun w_rq hw_rq => hf w_rq.1 none w_rq.2 hw_rq
  | some rq₀ =>
    dsimp only
    rw [pure_bind, bind_map_left]
    unfold LibsignalSim.coin LibsignalSim.liftQ
    simp only [pure_bind, StateT.run_bind, StateT.run_lift, bind_assoc, simulateQ_bind]
    exact a6a_all_bind
      (a6a_simulateQ_fig8ImplH1_inv Dh encPt C codec ℓ encT idOf maxSkip lam qepF
        (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))) g hg)
      fun w_rc hw_rc => hf rq₀ (some w_rc.1) w_rc.2 hw_rc

omit [SampleableType Pt] [Inhabited PQ] in
private theorem a6a_simSend_baseInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (s : LibsignalSim.SimState PQ Pt ℓ) (hbase : a6a_BaseInv P Inv s)
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt))
    (hg : a6a_Fig8GameInv g) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig (qep + 1))
      ((LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r).run s)).run g),
      a6a_BaseInv P Inv z.1.2 := by
  intro fig
  unfold LibsignalSim.simSend
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  by_cases hwin : (s.mir.win || !noBobSendInEpoch0 s.mir Q) = true
  · rw [a6a_ite_pos hwin, StateT.run_pure, simulateQ_pure]; exact a6a_all_pure hbase
  rw [a6a_ite_neg hwin]; clear hwin
  cases s.mir.epMgmt 3 qep Q r.isSome with
  | none =>
    rw [StateT.run_pure, simulateQ_pure]; exact a6a_all_pure hbase
  | some s₁ =>
    dsimp only
    by_cases hchal_ok : (chal.isSome && !s₁.safeCh 3 Q) = true
    · rw [a6a_ite_pos hchal_ok, StateT.run_pure, simulateQ_pure]; exact a6a_all_pure hbase
    rw [a6a_ite_neg hchal_ok]; clear hchal_ok
    refine a6a_simSend_coins Dh encPt P.C P.codec encT idOf 25000 lam (qep + 1) r _ s g hg
      fun rq rc g₁ hg₁ => ?_
    set pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
    cases hmk : LibsignalSim.mkPub (P := P) s Q rq pn with
    | none =>
      rw [StateT.run_pure, simulateQ_pure]
      exact a6a_all_pure hbase
    | some pq_pub =>
      rcases pq_pub with ⟨pq', pub⟩
      dsimp only
      unfold LibsignalSim.mkPub at hmk
      rw [Option.map_eq_some_iff] at hmk
      rcases hmk with ⟨⟨pq_out, salt, pqmsg⟩, hspqr_send, hpair⟩
      injection hpair with hpq_eq hpub_eq
      dsimp only at hpq_eq hpub_eq
      subst pq_out
      have hspqr_send' : P.spqr.send (s.pq Q) rq = some (pq', salt, pub.pqmsg) := by
        rw [← hpub_eq]; exact hspqr_send
      have hsalt : pub.salt = effectiveHkdfSalt32 salt := by rw [← hpub_eq]
      have haddrs : pub.addrs = if Q == Party.A && s.unackA then P.addrAB else none := by
        rw [← hpub_eq]
      have hpq' : Inv pq' := hI.send (s.pq Q) rq pq' salt pub.pqmsg (hbase.1 Q) hspqr_send'
      set q_oa : LibsignalSim.Fig8Comp Pt ℓ (Option (LibsignalSim.Fig8C Pt)) :=
        match chal with
        | none => SM.transmitQuery (St := LibsignalSim.Fig8St Pt) Q (pub, m₀) rc
        | some m₁ => SM.challQuery (St := LibsignalSim.Fig8St Pt) Q (pub, m₀) (pub, m₁) rc
      suffices ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig (qep + 1))
          ((do
            let res ← LibsignalSim.liftQ q_oa
            match res with
            | none => pure none
            | some c => do
              LibsignalSim.putS
                { s with
                  mir := s₁.record 3 Q () ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, LibsignalSim.toWire c⟩ chal.isSome
                  pq := Function.update s.pq Q pq'
                  pn := Function.update s.pn Q pn
                  honest := (LibsignalSim.toWire c, c) :: s.honest }
              pure (some (LibsignalSim.toWire c))).run s)).run g₁),
          a6a_BaseInv P Inv z.1.2 by
        cases chal <;> exact this
      unfold LibsignalSim.liftQ LibsignalSim.putS
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind]
      refine a6a_all_bind
        (a6a_fig8ImplH1_send_out Dh encPt P.C P.codec ℓ encT idOf 25000 lam (qep + 1)
          Q pub m₀ chal rc g₁ hg₁)
        fun w_q hw_q => ?_
      cases hres : w_q.1 with
      | none =>
        simp only [StateT.run_pure, simulateQ_pure]
        exact a6a_all_pure hbase
      | some c =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure]
        refine a6a_all_pure ?_
        rcases hw_q.2 c hres with ⟨hdr, i, seed, m_eff, rfl⟩
        refine ⟨a6a_baseInv_update_pq P Inv hbase Q hpq', ?_⟩
        intro wc hwc
        simp only [List.mem_cons] at hwc
        rcases hwc with rfl | hwc
        · exact a6a_honestEntry_of_lAead_enc P Inv encT idOf hrt hL hW1 Q hdr i seed pub m_eff
            s.unackA haddrs hspqr_send' hsalt (hbase.1 Q)
        · exact hbase.2 wc hwc

omit [SampleableType Pt] [Inhabited PQ] in
private theorem a6a_simSendC_fullInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ z ∈ support (((LibsignalSimC.simSendC (P := P) (qep := qep) (fig := fig)
      (H := LibsignalSimC.probeHook fig (qep + 1)) Q m₀ chal r).run sC).run gh),
      a6a_FullInv P Inv z.1.2 z.2 := by
  intro fig
  unfold LibsignalSimC.simSendC
  simp only [StateT.run_bind]
  refine a6a_all_bind
    (a6a_zoomB_fullInv P Dh encPt encT idOf lam (qep + 1) Inv
      (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r) sC gh hfull
      (a6a_simSend_baseInv P Inv hI hW1 hrt hL Dh encPt encT idOf lam qep Q m₀ chal r
        sC.base hfull.1 gh.1 hfull.2.1))
    fun w₁ hw₁ => ?_
  cases w₁.1.1 with
  | none =>
    simp only [StateT.run_pure]
    exact a6a_all_pure hw₁
  | some w =>
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
    exact a6a_all_pure hw₁

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_simCorrC_fullInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ z ∈ support (((LibsignalSimC.simCorrC (P := P) (encT := encT)
      (H := LibsignalSimC.probeHook fig (qep + 1)) Dh Q).run sC).run gh),
      a6a_FullInv P Inv z.1.2 z.2 := by
  intro fig
  unfold LibsignalSimC.simCorrC
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  split
  · simp only [StateT.run_pure]; exact a6a_all_pure hfull
  rw [StateT.run_bind, StateT.run_bind]
  refine a6a_all_bind
    (a6a_liftC_fullInv P Dh encPt encT idOf lam (qep + 1) Inv
      (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := LibsignalSim.Fig8C Pt) Q)
      sC gh hfull)
    fun w₁ ⟨hw₁_full, _⟩ => ?_
  cases hst : w₁.1.1 with
  | none =>
    simp only [StateT.run_pure]
    exact a6a_all_pure hw₁_full
  | some st =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    have hnew : a6a_FullInv P Inv
        { sC with
          base :=
            { sC.base with
              mir := sC.base.mir.afterCorr Q
              chains :=
                if Q == Party.B && sC.base.mir.epoch Party.B == 0 then
                  match st.γ with
                  | .exp x =>
                    Function.update sC.base.chains Party.A
                      ((sC.base.chains Party.A).map fun g =>
                        if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
                  | _ => sC.base.chains
                else sC.base.chains }
          kept := Function.update sC.kept Q (LibsignalSimC.Kept.ofSt st) }
        w₁.2 := ⟨hfull.1, hw₁_full.2.1, hw₁_full.2.2⟩
    exact a6a_all_pure hnew

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6a_guardC_fullInv {α : Type} (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSimC.ProbeM Pt ℓ) (Option α))
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh)
    (hx : ∀ z ∈ support ((x.run sC).run gh), a6a_FullInv P Inv z.1.2 z.2) :
    ∀ z ∈ support (((LibsignalSimC.guardC x).run sC).run gh),
      a6a_FullInv P Inv z.1.2 z.2 := by
  unfold LibsignalSimC.guardC
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp only [StateT.run_pure]; exact a6a_all_pure hfull
  · exact hx

omit [SampleableType Pt] [Inhabited PQ] in
private theorem a6a_simImplC_step_fullInv (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    ∀ z ∈ support (((LibsignalSimC.simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := LibsignalSimC.probeHook fig (qep + 1)) Dh q).run sC).run gh),
      a6a_FullInv P Inv z.1.2 z.2 := by
  intro fig fs
  rcases q with u | ⟨⟨⟨⟨⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩⟩ | ⟨Q, w⟩⟩ | ⟨Q, w⟩⟩ | Q⟩
  · intro z hz
    exact (a6a_liftC_fullInv P Dh encPt encT idOf lam (qep + 1) Inv
      (query (spec := unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt)) (.inl u))
      sC gh hfull z hz).1
  · exact a6a_guardC_fullInv P Inv _ sC gh hfull
      (a6a_simSendC_fullInv P Inv hI hW1 hrt hL Dh encPt encT idOf lam qep Q m none r sC gh hfull)
  · exact a6a_guardC_fullInv P Inv _ sC gh hfull
      (a6a_simSendC_fullInv P Inv hI hW1 hrt hL Dh encPt encT idOf lam qep Q m₀ (some m₁) r sC gh hfull)
  · exact a6a_guardC_fullInv P Inv _ sC gh hfull
      (a6a_simRecvC_fullInv P Inv hI Dh encPt encT decT idOf lam qep Q w true sC gh hfull)
  · exact a6a_guardC_fullInv P Inv _ sC gh hfull
      (a6a_simRecvC_fullInv P Inv hI Dh encPt encT decT idOf lam qep Q w false sC gh hfull)
  · exact a6a_guardC_fullInv P Inv _ sC gh hfull
      (a6a_simCorrC_fullInv P Inv Dh encPt encT idOf lam qep Q sC gh hfull)

omit [SampleableType Pt] [Inhabited PQ] in
private theorem a6a_simulateQ_simImplC_fullInv {α : Type} (P : Params PQ PQC) {ℓ : ℕ} (Inv : PQ → Prop)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool)
    (hfull : a6a_FullInv P Inv sC gh) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    ∀ z ∈ support (((simulateQ (LibsignalSimC.simImplC (P := P) (encT := encT) (decT := decT)
      (qep := qep) (fig := fig) (fs := fs) (H := LibsignalSimC.probeHook fig (qep + 1)) Dh) oa).run sC).run gh),
      a6a_FullInv P Inv z.1.2 z.2 := by
  intro fig fs
  induction oa using OracleComp.inductionOn generalizing sC gh with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact a6a_all_pure hfull
  | query_bind q cont ih =>
    rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    exact a6a_all_bind
      (a6a_simImplC_step_fullInv P Inv hI hW1 hrt hL Dh encPt encT decT idOf lam qep q sC gh hfull)
      (fun w hw => ih w.1.1 w.1.2 w.2 hw)

/-- Under `Corr.SpqrSaltBindingOn` on an invariant closed under `init`, `send`, and `recv`,
`hiddenSaltTerm` is `0`. -/
theorem hiddenSaltTerm_eq_zero_of_saltBinding (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hdec : ∀ T, decT (encT T) = some T) (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Inv : PQ → Prop)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (A : LibAdv PQ PQC ℓ) :
    LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A = 0 := by
  have _ := (inferInstance : SampleableType Pt)
  have _ := (inferInstance : Inhabited PQ)
  have _ := hdec
  set fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  set fs := lFS P.C P.codec ℓ encT idOf 25000
  unfold LibsignalSimC.hiddenSaltTerm LibsignalSimC.hiddenSaltGame
  refine SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun b _ => ?_
  refine SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun k _ => ?_
  unfold LibsignalSimC.simRunCWith
  dsimp only
  rw [StateT.run_bind, LibsignalSimC.probeHook_lift_run]
  simp only [bind_assoc, pure_bind]
  refine SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun pk_g hpk_g => ?_
  have hg₀ : a6a_Fig8GameInv pk_g.2 :=
    a6a_simulateQ_fig8ImplH1_inv Dh encPt P.C P.codec ℓ encT idOf 25000 lam (qep + 1)
      (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)))
      (initState fig k b)
      (a6a_fig8GameInv_init Dh encPt P.C P.codec ℓ encT idOf 25000 lam k b)
      pk_g hpk_g
  set sC₀ : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ :=
    LibsignalSimC.initSimC (P.spqr.init .a2b pk_g.1) (P.spqr.init .b2a pk_g.1)
  have hbase₀ : a6a_BaseInv P Inv sC₀.base := by
    refine ⟨fun Q => ?_, ?_⟩
    · cases Q <;> exact hI.init _ _
    · rintro _ ⟨⟩
  have hfull₀ : a6a_FullInv P Inv sC₀ (pk_g.2, false) := ⟨hbase₀, hg₀, rfl⟩
  rw [StateT.run'_eq, StateT.run_map, bind_map_left]
  refine SM.Construction.AuthL11.evalDist_bind_eq_zero _ _ fun z hz => ?_
  have hz_full := a6a_simulateQ_simImplC_fullInv P Inv hI hW1 hrt hL Dh encPt encT decT idOf lam qep
    A sC₀ (pk_g.2, false) hfull₀ z hz
  dsimp only
  rw [hz_full.2.2]
  simp

private def a6b_HonestSalt (P : Params PQ PQC) (Inv : PQ → Prop)
    (wc : List (BitVec 8) × LibsignalSim.Fig8C Pt) : Prop :=
  ∀ h body pq_st pq' salt,
    (signalWireCodec P.codec).parse (wc.1.take (wc.1.length - 8)) = some (h, body) →
    Inv pq_st →
    P.spqr.recv pq_st h.pqRatchet = .ok (pq', salt) →
    wc.2.2.2.2 = effectiveHkdfSalt32 salt

private def a6b_SimStateInv {ℓ : ℕ} (P : Params PQ PQC) (Inv : PQ → Prop)
    (s : LibsignalSim.SimState PQ Pt ℓ) : Prop :=
  (∀ Q, Inv (s.pq Q)) ∧ (∀ wc ∈ s.honest, a6b_HonestSalt P Inv wc)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6b_map_pure {ℓ : ℕ} {α : Type} (a : α)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (pure (a, sC) : LibsignalSim.Fig8Comp Pt ℓ (α × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)) =
    pure (a, sC.base) := by
  simp only [map_pure, Prod.map_apply, id_eq]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6b_zoomB_run {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (LibsignalSimC.runOnBaseState LibsignalSimC.idHook x).run sC =
    x.run sC.base := by
  change Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
    (x.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 })) = x.run sC.base
  simp only [map_bind, a6b_map_pure, Prod.mk.eta, bind_pure]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6b_zoomB_bind {ℓ : ℕ} {α β : Type}
    (x : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α)
    (f : α → StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) β)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (LibsignalSimC.runOnBaseState LibsignalSimC.idHook x >>= f).run sC =
    (x.run sC.base >>= fun p =>
      Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$> (f p.1).run { sC with base := p.2 }) := by
  change Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
    ((x.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 })) >>= fun q => (f q.1).run q.2) = _
  simp only [bind_assoc, pure_bind, map_bind]

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6b_fwdAnswerC_base_eq {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (c' : LibsignalSim.Fig8C Pt) (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (LibsignalSimC.fwdAnswerC (qep := qep) (fig := fig) (fs := fs)
        (H := LibsignalSimC.idHook) Q w isDel ci? T pq' c').run sC =
    (do
      let res ← LibsignalSim.fwd Q c'
      LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res).run sC.base := by
  unfold LibsignalSimC.fwdAnswerC
  rw [a6b_zoomB_bind, StateT.run_bind]
  congr 1
  funext ⟨res, s₁⟩
  rcases res with _ | ⟨_ | ⟨t, i, pm⟩⟩
  · simpa using a6b_zoomB_run _ _
  · simpa using a6b_zoomB_run _ _
  · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
    exact a6b_zoomB_run _ _

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_fwdC_eq_fwdAnswerC (P : Params PQ PQC) {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (LibsignalSim.Fig8C Pt)) (c' : LibsignalSim.Fig8C Pt)
    (hc : ∀ c, honestC = some c → c' = c) :
    LibsignalSimC.fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := LibsignalSimC.idHook)
      Q w isDel ci? T pq' honestC c' =
    LibsignalSimC.fwdAnswerC (qep := qep) (fig := fig) (fs := fs) (H := LibsignalSimC.idHook)
      Q w isDel ci? T pq' c' := by
  funext sC
  rcases honestC with _ | c
  · rfl
  · have hcc : c' = c := hc c rfl
    subst hcc
    simp [LibsignalSimC.fwdC]

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_fwdC_base_eq (P : Params PQ PQC) {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (LibsignalSim.Fig8C Pt)) (c' : LibsignalSim.Fig8C Pt)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hc : ∀ c, honestC = some c → c' = c) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (LibsignalSimC.fwdC (P := P) (qep := qep) (fig := fig) (fs := fs) (H := LibsignalSimC.idHook)
        Q w isDel ci? T pq' honestC c').run sC =
    (do
      let res ← LibsignalSim.fwd Q c'
      LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res).run sC.base := by
  rw [a6b_fwdC_eq_fwdAnswerC P qep fig fs Q w isDel ci? T pq' honestC c' hc]
  exact a6b_fwdAnswerC_base_eq qep fig fs Q w isDel ci? T pq' c' sC

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6b_simSendC_base_eq {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (LibsignalSimC.simSendC (P := P) (qep := qep) (fig := fig) (H := LibsignalSimC.idHook)
        Q m₀ chal r).run sC =
    (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r).run sC.base := by
  unfold LibsignalSimC.simSendC
  rw [a6b_zoomB_bind]
  conv_rhs => rw [← bind_pure ((LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r).run sC.base)]
  congr 1
  funext ⟨res, s₁⟩
  rcases res with _ | w
  · exact a6b_map_pure none { sC with base := s₁ }
  · dsimp only
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind]
    exact a6b_map_pure (some w) _

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_simCorrC_base_eq {ℓ : ℕ} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (Dh : DHFun (BitVec 256) Pt) (Q : Party) (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (LibsignalSimC.simCorrC (P := P) (encT := encT) (H := LibsignalSimC.idHook) Dh Q).run sC =
    (LibsignalSim.simCorr (P := P) (encT := encT) Dh Q).run sC.base := by
  unfold LibsignalSimC.simCorrC LibsignalSim.simCorr
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hif : (sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
      LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp only [hif, ite_true]; exact a6b_map_pure none sC
  · simp only [hif, Bool.false_eq_true, ite_false]
    change Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      ((SM.corrQuery Q >>= fun a => pure (a, sC)) >>= _) =
      ((SM.corrQuery Q >>= fun a => pure (a, sC.base)) >>= _)
    simp only [bind_assoc, pure_bind, map_bind]
    congr 1
    funext res
    rcases res with _ | st
    · exact a6b_map_pure none sC
    · exact a6b_map_pure _ _

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6b_guardC_base_eq {ℓ : ℕ} {α : Type}
    (x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) (Option α))
    (y : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) (Option α))
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hxy : Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$> x.run sC = y.run sC.base) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$> (LibsignalSimC.guardC x).run sC =
      (LibsignalSim.guard y).run sC.base := by
  simp only [LibsignalSimC.guardC, LibsignalSim.guard, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · exact a6b_map_pure none sC
  · exact hxy

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_simRecvC_base_eq {ℓ : ℕ} (P : Params PQ PQC) (Inv : PQ → Prop)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (hinv : a6b_SimStateInv P Inv sC.base)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (LibsignalSimC.simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := fig) (fs := fs) (H := LibsignalSimC.idHook) Q w isDel).run sC =
    (LibsignalSim.simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := none)
      Q w isDel).run sC.base := by
  unfold LibsignalSimC.simRecvC LibsignalSim.simRecv
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases h1 : sC.base.mir.win = true
  · simp only [h1, ite_true]; exact a6b_map_pure none sC
  · simp only [h1, Bool.false_eq_true, ite_false]
    by_cases h2 : (isDel && (sC.base.mir.inTransit Q.other w).isNone) = true
    · simp only [h2, ite_true]; exact a6b_map_pure none sC
    · simp only [h2, Bool.false_eq_true, ite_false]
      by_cases h3 : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3)
          || !(ratchetKeyAdmissible P.codec decT encT w))) = true
      · simp only [h3, ite_true]; exact a6b_map_pure none sC
      · simp only [h3, Bool.false_eq_true, ite_false]
        by_cases h4 : w.length < 9
        · simp only [h4, ite_true]; exact a6b_map_pure (some RecvResult.rejected) sC
        · simp only [h4, ite_false]
          rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, body⟩
          · exact a6b_map_pure (some RecvResult.rejected) sC
          · dsimp only
            by_cases h5 : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
            · simp only [h5, ite_true]; exact a6b_map_pure (some RecvResult.rejected) sC
            · simp only [h5, Bool.false_eq_true, ite_false]
              simp only [hnpR, Bool.false_eq_true, ite_false]
              rcases hrecv : P.spqr.recv (sC.base.pq Q) h.pqRatchet with _ | ⟨pq', salt⟩
              · exact a6b_map_pure (some RecvResult.rejected) sC
              · dsimp only
                have hmkC : ∀ t T c,
                    ((sC.base.honest.find? fun wc =>
                      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)) = some c →
                    (match (sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) with
                      | some c => if c.2.2.2 = effectiveHkdfSalt32 salt then c
                          else ((t, T), (h.counter.toNat + 1,
                            ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
                      | none => ((t, T), (h.counter.toNat + 1,
                          ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))) = c := by
                  intro t T c hc
                  rw [hc]
                  obtain ⟨wc, hfind, rfl⟩ := Option.map_eq_some_iff.mp hc
                  have hmem : wc ∈ sC.base.honest := List.mem_of_find?_eq_some hfind
                  have hpred := List.find?_some hfind
                  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
                  have hsalt : wc.2.2.2.2 = effectiveHkdfSalt32 salt := by
                    apply hinv.2 wc hmem h body (sC.base.pq Q) pq' salt
                    · rw [hpred.1]; exact hparse
                    · exact hinv.1 Q
                    · exact hrecv
                  simp [hsalt]
                rcases hci : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with _ | ci
                · simp only [hci]
                  by_cases h6 : (((sC.base.honest.find? fun wc =>
                      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
                  ·
                    have hsm : ((((sC.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                        fun c => decide (c.2.2.2 = effectiveHkdfSalt32 salt)) == some true) = true := by
                      cases hc : ((sC.base.honest.find? fun wc =>
                          wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)) with
                      | none => rw [hc] at h6; simp at h6
                      | some c =>
                        obtain ⟨wc, hfind, rfl⟩ := Option.map_eq_some_iff.mp hc
                        have hmem : wc ∈ sC.base.honest := List.mem_of_find?_eq_some hfind
                        have hpred := List.find?_some hfind
                        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
                        have hsalt : wc.2.2.2.2 = effectiveHkdfSalt32 salt := by
                          apply hinv.2 wc hmem h body (sC.base.pq Q) pq' salt
                          · rw [hpred.1]; exact hparse
                          · exact hinv.1 Q
                          · exact hrecv
                        simp [hsalt]
                    simp only [h6, hsm, Bool.true_and, ite_true]
                    exact a6b_map_pure (some RecvResult.rejected) sC
                  · simp only [h6, Bool.false_and, Bool.false_eq_true, ite_false]
                    by_cases h7 : (decT h.senderRatchetKey == some 0) = true
                    · simp only [h7, ite_true]; exact a6b_map_pure (some RecvResult.rejected) sC
                    · simp only [h7, Bool.false_eq_true, ite_false]
                      have hnone : ∀ b : Bool, (b && ((none : Option ℕ) == some sC.base.amb)) = false := by
                        intro b; cases b <;> rfl
                      simp only [hnone, Bool.false_eq_true, ite_false]
                      by_cases hamb : (LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
                          (Q == Party.A && (sC.base.chains Q).any (·.key.isNone))) = true
                      · simp only [hamb, ite_true, LibsignalSim.putS, StateT.run_bind,
                          StateT.run_modify, StateT.run_set, pure_bind]
                        split_ifs
                        · exact a6b_map_pure (some RecvResult.rejected) _
                        · rcases hT : decT h.senderRatchetKey with _ | T
                          · exact a6b_map_pure (some RecvResult.rejected) _
                          · apply a6b_fwdC_base_eq P
                            exact hmkC _ _
                      · simp only [Bool.not_eq_true] at hamb
                        simp only [hamb, Bool.false_eq_true, ite_false]
                        split_ifs
                        · exact a6b_map_pure (some RecvResult.rejected) sC
                        · rcases hT : decT h.senderRatchetKey with _ | T
                          · exact a6b_map_pure (some RecvResult.rejected) sC
                          · apply a6b_fwdC_base_eq P
                            exact hmkC _ _
                · simp only [hci]
                  split_ifs
                  · exact a6b_map_pure (some RecvResult.rejected) sC
                  · apply a6b_fwdC_base_eq P
                    exact hmkC _ _

private theorem a6b_simImplC_base_eq {ℓ : ℕ} (P : Params PQ PQC) (Inv : PQ → Prop)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (Dh : DHFun (BitVec 256) Pt)
    (q : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (hinv : a6b_SimStateInv P Inv sC.base)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false) :
    Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (LibsignalSimC.simImplC P encT decT qep fig fs LibsignalSimC.idHook Dh q).run sC =
    (LibsignalSim.simImpl P Dh encT decT qep none q).run sC.base := by
  rcases q with n | ⟨⟨⟨⟨⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩⟩ | ⟨Q, w⟩⟩ | ⟨Q, w⟩⟩ | Q⟩
  · change Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base <$>
      (query (spec := unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (LibsignalSim.Fig8C Pt)) (.inl n) >>= fun a => pure (a, sC)) =
      (query (spec := unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (LibsignalSim.Fig8C Pt)) (.inl n) >>= fun a => pure (a, sC.base))
    simp only [map_bind, a6b_map_pure]
  · exact a6b_guardC_base_eq _ _ sC (a6b_simSendC_base_eq P qep fig Q m none r sC)
  · exact a6b_guardC_base_eq _ _ sC (a6b_simSendC_base_eq P qep fig Q m₀ (some m₁) r sC)
  · exact a6b_guardC_base_eq _ _ sC
      (a6b_simRecvC_base_eq P Inv encT decT qep fig fs Q w true sC hinv hnpR)
  · exact a6b_guardC_base_eq _ _ sC
      (a6b_simRecvC_base_eq P Inv encT decT qep fig fs Q w false sC hinv hnpR)
  · exact a6b_guardC_base_eq _ _ sC (a6b_simCorrC_base_eq P encT Dh Q sC)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_honestSalt_of_lAead_enc {ℓ : ℕ} (P : Params PQ PQC) (Inv : PQ → Prop)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (Q : Party) (hdr : Header Pt) (i : ℕ) (seed : BitVec 256) (pub : LibsignalMsgPublicPart) (m : Plain ℓ)
    (unackA : Bool) (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg))
    (hsalt : pub.salt = effectiveHkdfSalt32 salt) (hpqInv : Inv pq_st) :
    let ct_aead := ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
      seed (i, hdr) (pub, m)
    let c : LibsignalSim.Fig8C Pt := (hdr, (i, ct_aead))
    a6b_HonestSalt P Inv (LibsignalSim.toWire c, c) := by
  intro ct_aead c h body pq_st₂ pq₂' salt₂ hparse hpqInv₂ hrecv
  set h_hdr := lHeader encT i hdr pub
  set mk := deriveMessageKeys P.C.F (some pub.salt) (keyToBytes32 seed)
  set body₀ := ((cbcPkcs7EncryptOnly P.C.E ℓ).enc (mk.1.1, mk.1.2) m).toList.flatMap blockToBytesLE
  set ser := (signalWireCodec P.codec).encode h_hdr body₀
  set w := LibsignalSim.toWire c
  have hw_eq : w = ser ++ _ := rfl
  have hw_sub : w.length - 8 = ser.length := by
    rw [hw_eq, List.length_append, Proofs.Refinement.length_tagBytes]; omega
  have htake : w.take (w.length - 8) = ser := by
    rw [hw_sub, hw_eq, List.take_left]
  have hparse₀ : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h_hdr, body₀) := by
    rw [htake]
    refine Proofs.RoundTrip.parse_of_rt hrt hL h_hdr body₀ rfl
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (Proofs.RoundTrip.length_cbcBody _)
    change Proofs.RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
  have hhb : (h, body) = (h_hdr, body₀) := Option.some.inj (hparse.symm.trans hparse₀)
  rcases Prod.mk.inj hhb with ⟨rfl, _⟩
  have hsalt_eq : salt₂ = salt :=
    hW1 pq_st rq pq' salt pub.pqmsg hpqInv hspqr_send pq_st₂ pq₂' salt₂ hpqInv₂ hrecv
  change pub.salt = effectiveHkdfSalt32 salt₂
  rw [hsalt, hsalt_eq]

private def a6b_SendReady (st : LibsignalSim.Fig8St Pt) : Prop :=
  st.vS.isSome = true ∨ st.id.sendsIn (st.tcur + 1) = true

private def a6b_Fig8GameInv {ℓ : ℕ}
    (g : SM.GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)) : Prop :=
  ∀ Q, a6b_SendReady (g.st Q)

omit [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_initState_fig8Inv {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (k : BitVec 256 × BitVec 256) (b : Bool) :
    a6b_Fig8GameInv (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b) := by
  intro Q
  cases Q
  · exact Or.inr rfl
  · exact Or.inl rfl

omit [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_lFig8_send_ready {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (st : LibsignalSim.Fig8St Pt) (hst : a6b_SendReady st)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (coins : BitVec 256) :
    let res := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) coins
    a6b_SendReady res.1 ∧
    ∃ hdr i seed, res.2 = (hdr, (i,
      ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc seed (i, hdr) (pub, m))) := by
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG
  dsimp only
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ite_true]
    exact ⟨Or.inl rfl, ⟨_, _, _, rfl⟩⟩
  · simp only [hs, Bool.false_eq_true, ite_false]
    rcases hst with hvS | hs'
    · rcases Option.isSome_iff_exists.mp hvS with ⟨vS, hvSeq⟩
      simp only [hvSeq]
      exact ⟨Or.inl rfl, ⟨_, _, _, rfl⟩⟩
    · exact absurd hs' hs

omit [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_lFig8_receive_ready {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (st : LibsignalSim.Fig8St Pt) (hst : a6b_SendReady st)
    (c : LibsignalSim.Fig8C Pt)
    {st' : LibsignalSim.Fig8St Pt} {t' i' : ℕ} {pm : LibsignalMsgPublicPart × Plain ℓ}
    (hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c =
      some (st', t', i', pm)) :
    a6b_SendReady st' := by
  unfold lFig8 SM.Construction.scheme SM.Construction.receive at hrcv
  dsimp only at hrcv
  by_cases hguard : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
  · rw [hguard] at hrcv; cases hrcv
  · simp only [hguard, Bool.false_eq_true, ite_false] at hrcv
    by_cases ht : c.1.1 = st.tcur + 1
    · simp only [ht, ite_true] at hrcv
      rcases hc12 : c.1.2 with _ | Tn
      · rw [hc12] at hrcv; cases hrcv
      · rw [hc12] at hrcv
        dsimp only at hrcv
        split at hrcv
        · cases hrcv
        · split at hrcv
          · cases hrcv
          · injection hrcv with htuple
            rcases Prod.mk.inj htuple with ⟨hst', _⟩
            subst hst'
            exact Or.inl (hst.elim id (fun hs => by
              rw [ht] at hguard
              simp [hs] at hguard))
    · simp only [ht, ite_false] at hrcv
      split at hrcv
      · cases hrcv
      · split at hrcv
        · cases hrcv
        · injection hrcv with htuple
          rcases Prod.mk.inj htuple with ⟨hst', _⟩
          subst hst'
          exact hst

private theorem a6b_simulateQ_query_eq {ι : Type} {spec : OracleSpec ι} {M : Type → Type}
    [Monad M] [LawfulMonad M] (impl : QueryImpl spec M) (q : spec.Domain) :
    simulateQ impl (liftM (OracleSpec.query q)) = impl q := by
  rw [simulateQ_query]
  exact id_map (impl q)

private theorem a6b_mem_support_bind {α β : Type} {mx : ProbComp α} {f : α → ProbComp β} {z : β}
    (h : z ∈ support (mx >>= f)) : ∃ x ∈ support mx, z ∈ support (f x) := by
  simpa only [support_bind, Set.mem_iUnion, exists_prop] using h

private structure a6b_ValidEnv {ℓ : ℕ} {σ : Type} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey)
    (E : QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt)) (StateT σ ProbComp))
    (I : σ → Prop) : Prop where
  preserve : ∀ fq g, I g → ∀ z ∈ support ((E fq).run g), I z.2
  transmit_out : ∀ Q (pub : LibsignalMsgPublicPart) (m₀ : Plain ℓ) rc g, I g →
    ∀ z ∈ support ((E (.inr (.inl (.inl (.inl (.inl (Q, (pub, m₀), rc))))))).run g),
      ∀ c, z.1 = some c →
        ∃ hdr i seed m, c = (hdr, (i,
          ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc seed (i, hdr) (pub, m)))
  chall_out : ∀ Q (pub : LibsignalMsgPublicPart) (m₀ m₁ : Plain ℓ) rc g, I g →
    ∀ z ∈ support ((E (.inr (.inl (.inl (.inl (.inr (Q, (pub, m₀), (pub, m₁), rc))))))).run g),
      ∀ c, z.1 = some c →
        ∃ hdr i seed m, c = (hdr, (i,
          ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc seed (i, hdr) (pub, m)))

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_ValidEnv.simulateQ_preserve {ℓ : ℕ} {σ α : Type} {P : Params PQ PQC}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {E : QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt)) (StateT σ ProbComp)}
    {I : σ → Prop} (hE : a6b_ValidEnv P encT idOf E I)
    (mx : LibsignalSim.Fig8Comp Pt ℓ α) :
    ∀ g, I g → ∀ z ∈ support ((simulateQ E mx).run g), I z.2 := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    intro g hg z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hg
  | query_bind fq f ih =>
    intro g hg z hz
    simp only [simulateQ_bind, a6b_simulateQ_query_eq, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    rcases hz with ⟨w, hw, hz⟩
    exact ih w.1 w.2 (hE.preserve fq g hg w hw) z hz

private theorem a6b_ValidEnv.simSend_inv {ℓ : ℕ} {σ : Type} (P : Params PQ PQC) (Inv : PQ → Prop)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (qep : ℕ)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    {E : QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt)) (StateT σ ProbComp)}
    {I : σ → Prop} (hE : a6b_ValidEnv P encT idOf E I)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (s : LibsignalSim.SimState PQ Pt ℓ) (g : σ)
    (hs : a6b_SimStateInv P Inv s) (hg : I g) :
    ∀ z ∈ support ((simulateQ E ((LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r).run s)).run g),
      a6b_SimStateInv P Inv z.1.2 ∧ I z.2 := by
  intro z hz
  refine ⟨?_, hE.simulateQ_preserve _ g hg z hz⟩
  unfold LibsignalSim.simSend at hz
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
  dsimp only at hz
  by_cases hwin : (s.mir.win || !noBobSendInEpoch0 s.mir Q) = true
  · simp only [hwin, ite_true, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hs
  · simp only [hwin, Bool.false_eq_true, ite_false] at hz
    rcases hs₁ : s.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · rw [hs₁] at hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hs
    · rw [hs₁] at hz
      dsimp only at hz
      by_cases hsafe : (chal.isSome && !s₁.safeCh 3 Q) = true
      · simp only [hsafe, ite_true, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hs
      · simp only [hsafe, Bool.false_eq_true, ite_false] at hz
        let pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
        have hstep : ∃ (rq : PQC) (rc : Option (BitVec 256)) (g₂ : σ),
            I g₂ ∧ z ∈ support ((simulateQ E (((do
              match LibsignalSim.mkPub (P := P) s Q rq pn with
              | none => return none
              | some (pq', pub) =>
                let res ← match chal with
                  | none => LibsignalSim.liftQ (SM.transmitQuery (St := LibsignalSim.Fig8St Pt) Q (pub, m₀) rc)
                  | some m₁ => LibsignalSim.liftQ (SM.challQuery (St := LibsignalSim.Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
                match res with
                | none => return none
                | some c =>
                  let w := LibsignalSim.toWire c
                  let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) :=
                    ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
                  let mir' := s₁.record 3 Q () rec' chal.isSome
                  LibsignalSim.putS
                    { s with mir := mir', pq := Function.update s.pq Q pq',
                             pn := Function.update s.pn Q pn, honest := (w, c) :: s.honest }
                  return some w :
                    StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ)
                      (Option (List (BitVec 8)))).run s))).run g₂) := by
          rcases r with _ | rq
          · dsimp only at hz
            rw [StateT.run_bind, simulateQ_bind, StateT.run_bind] at hz
            rcases a6b_mem_support_bind hz with ⟨⟨⟨rq, s_rq⟩, g₁⟩, hrq, hz⟩
            have hs_rq : s_rq = s := by
              simp only [LibsignalSim.coin, LibsignalSim.liftQ, StateT.run_lift, simulateQ_bind,
                StateT.run_bind, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion,
                support_pure, Set.mem_singleton_iff] at hrq
              rcases hrq with ⟨_, _, hrq⟩; exact (Prod.mk.inj (Prod.mk.inj hrq).1).2
            subst hs_rq
            have hg₁ : I g₁ := hE.simulateQ_preserve _ g hg _ hrq
            dsimp only at hz
            rw [pure_bind] at hz
            exact ⟨rq, none, g₁, hg₁, hz⟩
          · dsimp only at hz
            rw [pure_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind] at hz
            rcases a6b_mem_support_bind hz with ⟨⟨⟨rc, s_rc⟩, g₁⟩, hrc, hz⟩
            have hs_rc : s_rc = s := by
              simp only [StateT.run_map, simulateQ_map, support_map, Set.mem_image] at hrc
              rcases hrc with ⟨⟨⟨c, s_c⟩, g_c⟩, hc, heq⟩
              simp only [LibsignalSim.coin, LibsignalSim.liftQ, StateT.run_lift, simulateQ_bind,
                StateT.run_bind, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion,
                support_pure, Set.mem_singleton_iff] at hc
              rcases hc with ⟨_, _, hceq⟩
              have h1 : s_c = s_rc := (Prod.mk.inj (Prod.mk.inj heq).1).2
              have h2 : s_c = s := (Prod.mk.inj (Prod.mk.inj hceq).1).2
              exact h1.symm.trans h2
            subst hs_rc
            have hg₁ : I g₁ := hE.simulateQ_preserve _ g hg _ hrc
            dsimp only at hz
            exact ⟨rq, rc, g₁, hg₁, hz⟩
        obtain ⟨rq, rc, g₂, hg₂, hz⟩ := hstep
        rcases hmk : LibsignalSim.mkPub (P := P) s Q rq pn with _ | ⟨pq', pub⟩
        · rw [hmk] at hz
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hs
        · rw [hmk] at hz
          unfold LibsignalSim.mkPub at hmk
          rcases Option.map_eq_some_iff.mp hmk with ⟨⟨pq'₀, salt, pqmsg⟩, hsend, hpair⟩
          rcases Prod.mk.inj hpair with ⟨hpq'₀, hpub⟩
          have hpq' : Inv pq' := hpq'₀ ▸ hI.send (s.pq Q) rq pq'₀ salt pqmsg (hs.1 Q) hsend
          have hchal : ∃ (res : Option (LibsignalSim.Fig8C Pt)) (g₃ : σ),
              (∀ c, res = some c →
                ∃ hdr i seed m, c = (hdr, (i,
                  ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc seed (i, hdr) (pub, m)))) ∧
              z ∈ support ((simulateQ E (((do
                match res with
                | none => return none
                | some c =>
                  let w := LibsignalSim.toWire c
                  let rec' : SM.Record (Plain ℓ) (List (BitVec 8)) :=
                    ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
                  let mir' := s₁.record 3 Q () rec' chal.isSome
                  LibsignalSim.putS
                    { s with mir := mir', pq := Function.update s.pq Q pq',
                             pn := Function.update s.pn Q pn, honest := (w, c) :: s.honest }
                  return some w :
                    StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ)
                      (Option (List (BitVec 8)))).run s))).run g₃) := by
            rcases chal with _ | m₁
            · dsimp only at hz ⊢
              rw [StateT.run_bind, simulateQ_bind, StateT.run_bind] at hz
              rcases a6b_mem_support_bind hz with ⟨⟨⟨res, s_res⟩, g₃⟩, hres, hz⟩
              simp only [LibsignalSim.liftQ, SM.transmitQuery, HasQuery.query, StateT.run_lift,
                simulateQ_bind, StateT.run_bind, a6b_simulateQ_query_eq, simulateQ_pure,
                StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hres
              rcases hres with ⟨⟨res', g₃'⟩, hq, heq⟩
              rcases Prod.mk.inj heq with ⟨h1, hg₃⟩
              rcases Prod.mk.inj h1 with ⟨hres', hs_res⟩
              rw [hres', hs_res, hg₃] at hz
              dsimp only at hz
              exact ⟨res', g₃', hE.transmit_out Q pub m₀ rc g₂ hg₂ (res', g₃') hq, hz⟩
            · dsimp only at hz ⊢
              rw [StateT.run_bind, simulateQ_bind, StateT.run_bind] at hz
              rcases a6b_mem_support_bind hz with ⟨⟨⟨res, s_res⟩, g₃⟩, hres, hz⟩
              simp only [LibsignalSim.liftQ, SM.challQuery, HasQuery.query, StateT.run_lift,
                simulateQ_bind, StateT.run_bind, a6b_simulateQ_query_eq, simulateQ_pure,
                StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hres
              rcases hres with ⟨⟨res', g₃'⟩, hq, heq⟩
              rcases Prod.mk.inj heq with ⟨h1, hg₃⟩
              rcases Prod.mk.inj h1 with ⟨hres', hs_res⟩
              rw [hres', hs_res, hg₃] at hz
              dsimp only at hz
              exact ⟨res', g₃', hE.chall_out Q pub m₀ m₁ rc g₂ hg₂ (res', g₃') hq, hz⟩
          obtain ⟨res, g₃, hcout, hz⟩ := hchal
          rcases res with _ | c
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hs
          · dsimp only at hz
            simp only [LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]
            refine ⟨fun R => ?_, fun wc hwc => ?_⟩
            · by_cases hRQ : R = Q
              · subst hRQ; simp [Function.update_self, hpq']
              · simp [Function.update_of_ne hRQ, hs.1 R]
            · rcases List.mem_cons.mp hwc with rfl | hwc
              · obtain ⟨hdr, i, seed, m, rfl⟩ := hcout c rfl
                exact a6b_honestSalt_of_lAead_enc P Inv encT idOf hrt hL hW1 Q hdr i seed pub m
                  s.unackA (by rw [← hpub]) (by rw [← hpub]; exact hsend) (by rw [← hpub]) (hs.1 Q)
              · exact hs.2 wc hwc

private theorem a6b_ValidEnv.simRecv_inv {ℓ : ℕ} {σ : Type} (P : Params PQ PQC) (Inv : PQ → Prop)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (qep : ℕ)
    (hI : Corr.SpqrInvClosed P.spqr Inv)
    {E : QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt)) (StateT σ ProbComp)}
    {I : σ → Prop} (hE : a6b_ValidEnv P encT idOf E I)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (s : LibsignalSim.SimState PQ Pt ℓ) (g : σ)
    (hs : a6b_SimStateInv P Inv s) (hg : I g) :
    ∀ z ∈ support ((simulateQ E ((LibsignalSim.simRecv (P := P) (encT := encT) (decT := decT)
      (qep := qep) (k := none) Q w isDel).run s)).run g),
      a6b_SimStateInv P Inv z.1.2 ∧ I z.2 := by
  intro z hz
  refine ⟨?_, hE.simulateQ_preserve _ g hg z hz⟩
  have honAns : ∀ (s₁ : LibsignalSim.SimState PQ Pt ℓ) (ci? : Option ℕ) (T : PublicKey)
      (pq' : PQ) (c' : LibsignalSim.Fig8C Pt) (g₁ : σ),
      a6b_SimStateInv P Inv s₁ → Inv pq' →
      ∀ z' ∈ support ((simulateQ E ((do
        let res ← LibsignalSim.fwd Q c'
        LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res).run s₁)).run g₁),
        a6b_SimStateInv P Inv z'.1.2 := by
    intro s₁ ci? T pq' c' g₁ hs₁ hpq' z' hz'
    have hupd : a6b_SimStateInv P Inv
        { s₁ with pq := Function.update s₁.pq Q pq' } := by
      refine ⟨fun R => ?_, hs₁.2⟩
      by_cases hRQ : R = Q
      · subst hRQ; simp [Function.update_self, hpq']
      · simp [Function.update_of_ne hRQ, hs₁.1 R]
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind] at hz'
    rcases a6b_mem_support_bind hz' with ⟨⟨⟨res, s₂⟩, g₂⟩, hres, hz'⟩
    have hs₂ : s₂ = s₁ := by
      unfold LibsignalSim.fwd at hres
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hres
      dsimp only at hres
      split_ifs at hres <;> {
        simp only [LibsignalSim.liftQ, SM.deliverQuery, SM.injectQuery, HasQuery.query,
          StateT.run_lift, simulateQ_bind, StateT.run_bind, a6b_simulateQ_query_eq, simulateQ_pure,
          StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hres
        rcases hres with ⟨_, _, heq⟩
        exact (Prod.mk.inj (Prod.mk.inj heq).1).2
      }
    rw [hs₂] at hz'
    dsimp only at hz'
    rcases res with _ | ⟨_ | ⟨t, i, pm⟩⟩
    · simp only [LibsignalSim.onAnswer, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz'
      rw [hz']; exact hs₁
    · simp only [LibsignalSim.onAnswer, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz'
      rw [hz']; exact hs₁
    · unfold LibsignalSim.onAnswer LibsignalSim.onAccept at hz'
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hz'
      by_cases hdel : isDel = true
      · simp only [hdel, ite_true] at hz'
        rcases htr : s₁.mir.inTransit Q.other w with _ | r_tr
        · rw [htr] at hz'
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz'
          rw [hz']; exact hs₁
        · rw [htr] at hz'
          simp only [LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz'
          rw [hz']; exact ⟨hupd.1, hs₁.2⟩
      · simp only [hdel, Bool.false_eq_true, ite_false] at hz'
        split_ifs at hz'
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz'
          rw [hz']; exact hs₁
        · simp only [LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz'
          rw [hz']; exact ⟨hupd.1, hs₁.2⟩
        · simp only [LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz'
          rw [hz']; exact hs₁
  unfold LibsignalSim.simRecv at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases h1 : s.mir.win = true
  · simp only [h1, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hs
  · simp only [h1, Bool.false_eq_true, ite_false] at hz
    by_cases h2 : (isDel && (s.mir.inTransit Q.other w).isNone) = true
    · simp only [h2, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hs
    · simp only [h2, Bool.false_eq_true, ite_false] at hz
      by_cases h3 : (!isDel && ((s.mir.inTransit Q.other w).isSome || !(s.mir.safeInj 3)
          || !(ratchetKeyAdmissible P.codec decT encT w))) = true
      · simp only [h3, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hs
      · simp only [h3, Bool.false_eq_true, ite_false] at hz
        by_cases h4 : w.length < 9
        · simp only [h4, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hs
        · simp only [h4, ite_false] at hz
          rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, body⟩
          · rw [hparse] at hz
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hs
          · rw [hparse] at hz
            dsimp only at hz
            by_cases h5 : (!(addressCheckPasses h.addresses (P.expectedAddrs Q))) = true
            · simp only [h5, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              rw [hz]; exact hs
            · simp only [h5, Bool.false_eq_true, ite_false] at hz
              rcases hrecv : P.spqr.recv (s.pq Q) h.pqRatchet with _ | ⟨pq', salt⟩
              · rw [hrecv] at hz
                simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                rw [hz]; exact hs
              · rw [hrecv] at hz
                have hpq' : Inv pq' := hI.recv (s.pq Q) h.pqRatchet pq' salt (hs.1 Q) hrecv
                dsimp only at hz
                rcases hci : (s.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with _ | ci
                · simp only [hci] at hz
                  by_cases h6 : (((s.honest.find? fun wc =>
                      wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ s.mir.epoch Q + 1)) == some true
                  · simp only [h6, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                    rw [hz]; exact hs
                  · simp only [h6, Bool.false_eq_true, ite_false] at hz
                    by_cases h7 : (decT h.senderRatchetKey == some 0) = true
                    · simp only [h7, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                      rw [hz]; exact hs
                    · simp only [h7, Bool.false_eq_true, ite_false] at hz
                      have hnone : ∀ b : Bool, (b && ((none : Option ℕ) == some s.amb)) = false := by
                        intro b; cases b <;> rfl
                      simp only [hnone, Bool.false_eq_true, ite_false] at hz
                      by_cases hamb : (LibsignalSim.inReceiveOnlyEpoch s.mir Q ||
                          (Q == Party.A && (s.chains Q).any (·.key.isNone))) = true
                      · simp only [hamb, ite_true, LibsignalSim.putS, StateT.run_bind,
                          StateT.run_set, pure_bind] at hz
                        split_ifs at hz
                        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                          rw [hz]; exact hs
                        · rcases hT : decT h.senderRatchetKey with _ | T
                          · simp only [hT, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                            rw [hz]; exact hs
                          · simp only [hT] at hz
                            exact honAns { s with amb := s.amb + 1 } none h.senderRatchetKey pq' _ g hs hpq' z hz
                      · simp only [Bool.not_eq_true] at hamb
                        simp only [hamb, Bool.false_eq_true, ite_false] at hz
                        split_ifs at hz
                        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                          rw [hz]; exact hs
                        · rcases hT : decT h.senderRatchetKey with _ | T
                          · simp only [hT, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                            rw [hz]; exact hs
                          · simp only [hT] at hz
                            exact honAns s none h.senderRatchetKey pq' _ g hs hpq' z hz
                · simp only [hci] at hz
                  split_ifs at hz
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                    rw [hz]; exact hs
                  · exact honAns s (some ci) h.senderRatchetKey pq' _ g hs hpq' z hz

private theorem a6b_ValidEnv.simImpl_inv {ℓ : ℕ} {σ : Type} (P : Params PQ PQC) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (qep : ℕ)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    {E : QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt)) (StateT σ ProbComp)}
    {I : σ → Prop} (hE : a6b_ValidEnv P encT idOf E I)
    (q : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (s : LibsignalSim.SimState PQ Pt ℓ) (g : σ)
    (hs : a6b_SimStateInv P Inv s) (hg : I g) :
    ∀ z ∈ support ((simulateQ E ((LibsignalSim.simImpl P Dh encT decT qep none q).run s)).run g),
      a6b_SimStateInv P Inv z.1.2 ∧ I z.2 := by
  have hguard : ∀ {α : Type} (x : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) (Option α)),
      (∀ z ∈ support ((simulateQ E (x.run s)).run g), a6b_SimStateInv P Inv z.1.2 ∧ I z.2) →
      ∀ z ∈ support ((simulateQ E ((LibsignalSim.guard x).run s)).run g),
        a6b_SimStateInv P Inv z.1.2 ∧ I z.2 := by
    intro α x hx z hz
    unfold LibsignalSim.guard at hz
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hstop : s.stopped = true
    · simp only [hstop, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact ⟨hs, hg⟩
    · simp only [hstop, Bool.false_eq_true, ite_false] at hz
      exact hx z hz
  rcases q with n | ⟨⟨⟨⟨⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩⟩ | ⟨Q, w⟩⟩ | ⟨Q, w⟩⟩ | Q⟩
  · intro z hz
    refine ⟨?_, hE.simulateQ_preserve _ g hg z hz⟩
    change z ∈ support ((simulateQ E ((LibsignalSim.liftQ
      (query (spec := unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
        (LibsignalSim.Fig8C Pt)) (.inl n))).run s)).run g) at hz
    simp only [LibsignalSim.liftQ, HasQuery.query, StateT.run_lift, simulateQ_bind, StateT.run_bind,
      a6b_simulateQ_query_eq, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, hz⟩
    rw [hz]; exact hs
  · exact hguard _ (hE.simSend_inv P Inv encT idOf qep hrt hL hI hW1 Q m none r s g hs hg)
  · exact hguard _ (hE.simSend_inv P Inv encT idOf qep hrt hL hI hW1 Q m₀ (some m₁) r s g hs hg)
  · exact hguard _ (hE.simRecv_inv P Inv encT decT idOf qep hI Q w true s g hs hg)
  · exact hguard _ (hE.simRecv_inv P Inv encT decT idOf qep hI Q w false s g hs hg)
  · apply hguard
    intro z hz
    refine ⟨?_, hE.simulateQ_preserve _ g hg z hz⟩
    unfold LibsignalSim.simCorr at hz
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
    dsimp only at hz
    by_cases hcorr : (s.mir.win || !s.mir.corrAllowed Q || LibsignalSim.inReceiveOnlyEpoch s.mir Q || !noAliceCorrWhileAliceBelowEpoch10 s.mir Q) = true
    · simp only [hcorr, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hs
    · simp only [hcorr, Bool.false_eq_true, ite_false, StateT.run_bind, simulateQ_bind] at hz
      rcases a6b_mem_support_bind hz with ⟨⟨⟨res, s_res⟩, g₁⟩, hres, hz⟩
      have hs_res : s_res = s := by
        simp only [LibsignalSim.liftQ, SM.corrQuery, HasQuery.query, StateT.run_lift,
          simulateQ_bind, StateT.run_bind, a6b_simulateQ_query_eq, simulateQ_pure, StateT.run_pure,
          support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hres
        rcases hres with ⟨_, _, heq⟩
        exact (Prod.mk.inj (Prod.mk.inj heq).1).2
      subst hs_res
      dsimp only at hz
      rcases res with _ | st
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hs
      · dsimp only at hz
        simp only [LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hs

private theorem a6b_bind_congr_support {α β : Type} (mx : ProbComp α) (f₁ f₂ : α → ProbComp β)
    (h : ∀ a ∈ support mx, f₁ a = f₂ a) : mx >>= f₁ = mx >>= f₂ := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind q g ih =>
    simp only [bind_assoc]
    congr 1
    funext u
    refine ih u fun a ha => h a ?_
    simp only [support_bind, Set.mem_iUnion]
    exact ⟨u, by simp, ha⟩

private theorem a6b_ValidEnv.simulateQ_simImplC_eq {ℓ : ℕ} {σ α : Type} (P : Params PQ PQC)
    (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    {E : QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt)) (StateT σ ProbComp)}
    {I : σ → Prop} (hE : a6b_ValidEnv P encT idOf E I)
    (oa : OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) α) :
    ∀ (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (g : σ),
      a6b_SimStateInv P Inv sC.base → I g →
      Prod.map (Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base) id <$>
        ((simulateQ E ((simulateQ (LibsignalSimC.simImplC P encT decT qep fig fs
          LibsignalSimC.idHook Dh) oa).run sC)).run g) =
      ((simulateQ E ((simulateQ (LibsignalSim.simImpl P Dh encT decT qep none) oa).run
        sC.base)).run g) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC g _ _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  | query_bind q f ih =>
    intro sC g hs hg
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, map_bind]
    have hqC : (OracleSpec.query q).cont <$>
        LibsignalSimC.simImplC P encT decT qep fig fs LibsignalSimC.idHook Dh (OracleSpec.query q).input =
        LibsignalSimC.simImplC P encT decT qep fig fs LibsignalSimC.idHook Dh q :=
      id_map _
    have hqS : (OracleSpec.query q).cont <$>
        LibsignalSim.simImpl P Dh encT decT qep none (OracleSpec.query q).input =
        LibsignalSim.simImpl P Dh encT decT qep none q :=
      id_map _
    rw [hqC, hqS]
    have hstep :
        Prod.map (Prod.map id LibsignalSimC.LibsignalToModularSchemeSimState.base) id <$>
          ((simulateQ E ((LibsignalSimC.simImplC P encT decT qep fig fs LibsignalSimC.idHook Dh q).run sC)).run g) =
        ((simulateQ E ((LibsignalSim.simImpl P Dh encT decT qep none q).run sC.base)).run g) := by
      rw [← a6b_simImplC_base_eq P Inv encT decT qep fig fs Dh q sC hs hnpR, simulateQ_map, StateT.run_map]
      rfl
    rw [← hstep]
    simp only [map_eq_bind_pure_comp, bind_assoc]
    apply a6b_bind_congr_support
    intro ⟨⟨a, sC'⟩, g'⟩ hmem
    have hmem' : ((a, sC'.base), g') ∈
        support ((simulateQ E ((LibsignalSim.simImpl P Dh encT decT qep none q).run sC.base)).run g) := by
      rw [← hstep]
      simp only [support_map, Set.mem_image]
      exact ⟨((a, sC'), g'), hmem, rfl⟩
    obtain ⟨hs', hg'⟩ := hE.simImpl_inv P Inv Dh encT decT idOf qep hrt hL hI hW1 q sC.base g hs hg _ hmem'
    simpa [map_eq_bind_pure_comp] using ih a sC' g' hs' hg'

private theorem a6b_ValidEnv.simC_eq_sim {ℓ : ℕ} {σ : Type} (P : Params PQ PQC)
    (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ) (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (hI : Corr.SpqrInvClosed P.spqr Inv) (hW1 : Corr.SpqrSaltBindingOn P.spqr Inv)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    {E : QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt)) (StateT σ ProbComp)}
    {I : σ → Prop} (hE : a6b_ValidEnv P encT idOf E I)
    (A : LibAdv PQ PQC ℓ) (g : σ) (hg : I g) :
    ((simulateQ E (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)).run g) =
      ((simulateQ E (sim P ℓ Dh encT decT qep A)).run g) := by
  unfold libsignalToModularSchemeSim LibsignalSimC.runLibsignalToModularSchemeSim LibsignalSimC.simRunCWith sim LibsignalSim.simRun
  simp only [LibsignalSimC.idHook_lift, StateT.run'_eq, bind_pure, simulateQ_bind, simulateQ_map,
    StateT.run_bind, StateT.run_map]
  apply a6b_bind_congr_support
  intro ⟨pqrKey, g₁⟩ hmem
  have hg₁ : I g₁ := hE.simulateQ_preserve _ g hg _ hmem
  set sC := LibsignalSimC.initSimC (Pt := Pt) (ℓ := ℓ)
    (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  have hsC : a6b_SimStateInv P Inv sC.base := by
    refine ⟨fun Q => ?_, fun _ h => nomatch h⟩
    cases Q
    · exact hI.init .a2b pqrKey
    · exact hI.init .b2a pqrKey
  have heq := congrArg (fun mx => Prod.map Prod.fst id <$> mx)
    (hE.simulateQ_simImplC_eq P Inv Dh encT decT idOf qep
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (lFS P.C P.codec ℓ encT idOf 25000) hrt hL hI hW1 hnpR A sC g₁ hsC hg₁)
  rw [Functor.map_map] at heq
  dsimp only [Prod.map, id] at heq ⊢
  exact heq

private theorem a6b_epMgmt_st {St Msg C : Type} {s s₁ : SM.GameState St Msg C} {Δ qep : ℕ}
    {Q : Party} {bad : Bool} (h : s.epMgmt Δ qep Q bad = some s₁) : s₁.st = s.st := by
  unfold SM.GameState.epMgmt SM.GameState.leak at h
  split_ifs at h with h1 h2 h3 <;> cases h <;> rfl

private abbrev a6b_fig8Env {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qepF : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ)) :
    QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
      (StateT (SM.GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)) ProbComp) +
    SM.oracleImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) qepF cfg

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_validEnv_fig8 {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qepF : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (hcfg : cfg.challMsg = fun _ => none) :
    a6b_ValidEnv P encT idOf (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg) a6b_Fig8GameInv where
  preserve := by
    intro fq g hg z hz
    rcases fq with n | ⟨⟨⟨⟨⟨Q, pm, rc⟩ | ⟨Q, pm₀, pm₁, rc⟩⟩ | ⟨Q, c⟩⟩ | ⟨Q, c⟩⟩ | Q⟩
    · change z ∈ support (((liftM (QueryImpl.ofLift unifSpec ProbComp n) :
        StateT (SM.GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)) ProbComp _)).run g) at hz
      simp only [StateT.run_monadLift, monadLift_self, support_bind, Set.mem_iUnion,
        support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨_, _, hzeq⟩
      rw [hzeq]
      exact hg
    · change z ∈ support ((SM.transmitImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (2 + 1) qepF (Q, pm, rc)).run g) at hz
      unfold SM.transmitImpl at hz
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
      dsimp only at hz
      by_cases hwin : g.win = true
      · simp only [hwin, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hg
      · simp only [hwin, Bool.false_eq_true, ite_false] at hz
        rw [StateT.run_bind, StateT.run_monadLift, monadLift_self] at hz
        rcases a6b_mem_support_bind hz with ⟨⟨⟨coins, bad⟩, g₁⟩, hsam, hz⟩
        simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hsam
        rcases hsam with ⟨_, _, heq⟩
        have hg₁ : g₁ = g := (Prod.mk.inj heq).2
        rw [hg₁] at hz
        dsimp only at hz
        rcases hep : g.epMgmt (2 + 1) qepF Q bad with _ | s₁
        · rw [hep] at hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hg
        · rw [hep] at hz
          dsimp only at hz
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
          have hst₁ : s₁.st = g.st := a6b_epMgmt_st hep
          have hsend := (a6b_lFig8_send_ready P Dh encPt encT idOf lam (s₁.st Q)
            (hst₁ ▸ hg Q) pm.1 pm.2 coins).1
          intro R
          by_cases hRQ : R = Q
          · subst hRQ; simp [SM.GameState.record, Function.update_self, hsend]
          · simp [SM.GameState.record, Function.update_of_ne hRQ, hst₁, hg R]
    · change z ∈ support ((SM.challImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (2 + 1) qepF cfg (Q, pm₀, pm₁, rc)).run g) at hz
      unfold SM.challImpl at hz
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
      dsimp only at hz
      by_cases hwin : g.win = true
      · simp only [hwin, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hg
      · simp only [hwin, Bool.false_eq_true, ite_false] at hz
        rw [StateT.run_bind, StateT.run_monadLift, monadLift_self] at hz
        rcases a6b_mem_support_bind hz with ⟨⟨⟨coins, bad⟩, g₁⟩, hsam, hz⟩
        simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hsam
        rcases hsam with ⟨_, _, heq⟩
        have hg₁ : g₁ = g := (Prod.mk.inj heq).2
        rw [hg₁] at hz
        dsimp only at hz
        rcases hep : g.epMgmt (2 + 1) qepF Q bad with _ | s₁
        · rw [hep] at hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hg
        · rw [hep] at hz
          dsimp only at hz
          by_cases hsafe : (!s₁.safeCh (2 + 1) Q || !cfg.challAllowedIn (s₁.epoch Q)) = true
          · simp only [hsafe, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hg
          · simp only [hsafe, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]
            have hst₁ : s₁.st = g.st := a6b_epMgmt_st hep
            set m := (cfg.challMsg (s₁.epoch Q)).getD (if g.b then pm₁ else pm₀)
            have hsend := (a6b_lFig8_send_ready P Dh encPt encT idOf lam (s₁.st Q)
              (hst₁ ▸ hg Q) m.1 m.2 coins).1
            intro R
            by_cases hRQ : R = Q
            · subst hRQ; simp [SM.GameState.record, Function.update_self, hsend]
            · simp [SM.GameState.record, Function.update_of_ne hRQ, hst₁, hg R]
    · change z ∈ support ((SM.deliverImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        cfg (Q, c)).run g) at hz
      unfold SM.deliverImpl at hz
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
      dsimp only at hz
      by_cases hwin : g.win = true
      · simp only [hwin, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hg
      · simp only [hwin, Bool.false_eq_true, ite_false] at hz
        rcases htr : g.inTransit Q.other c with _ | r
        · rw [htr] at hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hg
        · rw [htr] at hz
          dsimp only at hz
          rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c
            with _ | ⟨st', t', i', m'⟩
          · rw [hrcv] at hz
            dsimp only at hz
            split_ifs at hz <;>
              (simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hz; rw [hz]; exact hg)
          · rw [hrcv] at hz
            dsimp only at hz
            have hst' : a6b_SendReady st' :=
              a6b_lFig8_receive_ready P Dh encPt encT idOf lam (g.st Q) (hg Q) c hrcv
            have hacc : a6b_Fig8GameInv (g.accept Q st' r.pos) := by
              intro R
              by_cases hRQ : R = Q
              · subst hRQ; simp [SM.GameState.accept, SM.GameState.delete, Function.update_self, hst']
              · simp [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne hRQ, hg R]
            by_cases hmust : ((cfg.deliverWin && g.mustBeCorrect
                (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).maxSkip Q r) &&
                !decide ((t', i', m') = (r.pos.epoch, r.pos.idx, r.msg))) = true
            · simp only [hmust, ite_true, StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff] at hz
              rw [hz]; exact hacc
            · simp only [hmust, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_set,
                StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
              rw [hz]; exact hacc
    · change z ∈ support ((SM.injectImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (2 + 1) qepF cfg (Q, c)).run g) at hz
      unfold SM.injectImpl at hz
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
      dsimp only at hz
      by_cases hwin : (g.win || (g.inTransit Q.other c).isSome || !g.safeInj (2 + 1)) = true
      · simp only [hwin, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hg
      · simp only [hwin, Bool.false_eq_true, ite_false] at hz
        rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c
          with _ | ⟨st', t', i', m'⟩
        · rw [hrcv] at hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hg
        · rw [hrcv] at hz
          dsimp only at hz
          have hst' : a6b_SendReady st' :=
            a6b_lFig8_receive_ready P Dh encPt encT idOf lam (g.st Q) (hg Q) c hrcv
          have hacc : ∀ pos, a6b_Fig8GameInv (g.accept Q st' pos) := by
            intro pos R
            by_cases hRQ : R = Q
            · subst hRQ; simp [SM.GameState.accept, SM.GameState.delete, Function.update_self, hst']
            · simp [SM.GameState.accept, SM.GameState.delete, Function.update_of_ne hRQ, hg R]
          split_ifs at hz
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hg
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hacc _
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hg
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hg
    · change z ∈ support ((SM.corrImpl Q).run g) at hz
      unfold SM.corrImpl at hz
      rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
      dsimp only at hz
      split_ifs at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hg
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hg
  transmit_out := by
    intro Q pub m₀ rc g hg z hz c hc
    change z ∈ support ((SM.transmitImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (2 + 1) qepF (Q, (pub, m₀), rc)).run g) at hz
    unfold SM.transmitImpl at hz
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
    dsimp only at hz
    by_cases hwin : g.win = true
    · simp only [hwin, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz] at hc; cases hc
    · simp only [hwin, Bool.false_eq_true, ite_false] at hz
      rw [StateT.run_bind, StateT.run_monadLift, monadLift_self] at hz
      rcases a6b_mem_support_bind hz with ⟨⟨⟨coins, bad⟩, g₁⟩, hsam, hz⟩
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hsam
      rcases hsam with ⟨_, _, heq⟩
      have hg₁ : g₁ = g := (Prod.mk.inj heq).2
      rw [hg₁] at hz
      dsimp only at hz
      rcases hep : g.epMgmt (2 + 1) qepF Q bad with _ | s₁
      · rw [hep] at hz
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz] at hc; cases hc
      · rw [hep] at hz
        dsimp only at hz
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hz
        rw [hz] at hc
        injection hc with hc_eq
        have hst₁ : s₁.st = g.st := a6b_epMgmt_st hep
        obtain ⟨hdr, i, seed, hout⟩ := (a6b_lFig8_send_ready P Dh encPt encT idOf lam (s₁.st Q)
          (hst₁ ▸ hg Q) pub m₀ coins).2
        exact ⟨hdr, i, seed, m₀, hc_eq.symm.trans hout⟩
  chall_out := by
    intro Q pub m₀ m₁ rc g hg z hz c hc
    change z ∈ support ((SM.challImpl (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (2 + 1) qepF cfg (Q, (pub, m₀), (pub, m₁), rc)).run g) at hz
    unfold SM.challImpl at hz
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
    dsimp only at hz
    by_cases hwin : g.win = true
    · simp only [hwin, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz] at hc; cases hc
    · simp only [hwin, Bool.false_eq_true, ite_false] at hz
      rw [StateT.run_bind, StateT.run_monadLift, monadLift_self] at hz
      rcases a6b_mem_support_bind hz with ⟨⟨⟨coins, bad⟩, g₁⟩, hsam, hz⟩
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hsam
      rcases hsam with ⟨_, _, heq⟩
      have hg₁ : g₁ = g := (Prod.mk.inj heq).2
      rw [hg₁] at hz
      dsimp only at hz
      rcases hep : g.epMgmt (2 + 1) qepF Q bad with _ | s₁
      · rw [hep] at hz
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz] at hc; cases hc
      · rw [hep] at hz
        dsimp only at hz
        by_cases hsafe : (!s₁.safeCh (2 + 1) Q || !cfg.challAllowedIn (s₁.epoch Q)) = true
        · simp only [hsafe, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz] at hc; cases hc
        · simp only [hsafe, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
          rw [hz] at hc
          injection hc with hc_eq
          have hst₁ : s₁.st = g.st := a6b_epMgmt_st hep
          have hm : (cfg.challMsg (s₁.epoch Q)).getD (if g.b then (pub, m₁) else (pub, m₀)) =
              (pub, if g.b then m₁ else m₀) := by
            rw [hcfg]
            cases g.b <;> rfl
          rw [hm] at hc_eq
          obtain ⟨hdr, i, seed, hout⟩ := (a6b_lFig8_send_ready P Dh encPt encT idOf lam (s₁.st Q)
            (hst₁ ▸ hg Q) pub (if g.b then m₁ else m₀) coins).2
          exact ⟨hdr, i, seed, if g.b then m₁ else m₀, hc_eq.symm.trans hout⟩

private abbrev a6b_challEnv {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qepF : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ)) :
    QueryImpl (unifSpec + SM.spec (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
      (StateT (Thm1.Mirror (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) ×
        SM.GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)) ProbComp) :=
  fun fq => StateT.mk fun ⟨m, g⟩ => do
    let ((a, m'), g') ←
      ((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg)
        ((Thm1.simImpl (2 + 1) qepF (fun _ => none) none fq).run m)).run g)
    return (a, (m', g'))

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6b_simulateQ_challEnv_eq {ℓ : ℕ} {α : Type} (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qepF : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (oa : LibsignalSim.Fig8Comp Pt ℓ α) :
    ∀ (m : Thm1.Mirror (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt))
      (g : SM.GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)),
      ((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg)
        ((simulateQ (Thm1.simImpl (2 + 1) qepF (fun _ => none) none) oa).run m)).run g) =
      (fun ⟨a, m', g'⟩ => ((a, m'), g')) <$>
        ((simulateQ (a6b_challEnv P Dh encPt encT idOf lam qepF cfg) oa).run (m, g)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro m g
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind fq f ih =>
    intro m g
    simp only [simulateQ_bind, a6b_simulateQ_query_eq, StateT.run_bind, map_bind]
    change (((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg)
        ((Thm1.simImpl (2 + 1) qepF (fun _ => none) none fq).run m)).run g) >>=
        fun p =>
          ((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg)
            ((simulateQ (Thm1.simImpl (2 + 1) qepF (fun _ => none) none) (f p.1.1)).run p.1.2)).run p.2)) =
      ((((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg)
        ((Thm1.simImpl (2 + 1) qepF (fun _ => none) none fq).run m)).run g) >>=
        fun ⟨⟨a, m'⟩, g'⟩ => pure (a, (m', g'))) >>=
        fun a =>
          (fun x => ((x.1, x.2.1), x.2.2)) <$>
            ((simulateQ (a6b_challEnv P Dh encPt encT idOf lam qepF cfg) (f a.1)).run a.2))
    simp only [bind_assoc]
    congr 1
    ext ⟨⟨a, m'⟩, g'⟩
    simp only [pure_bind]
    exact ih a m' g'

private theorem a6b_validEnv_challEnv {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qepF : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (hcfg : cfg.challMsg = fun _ => none) :
    a6b_ValidEnv P encT idOf (a6b_challEnv P Dh encPt encT idOf lam qepF cfg)
      (fun mg => a6b_Fig8GameInv mg.2) where
  preserve := by
    intro fq ⟨m, g⟩ hg z hz
    have hfig := a6b_validEnv_fig8 P Dh encPt encT idOf lam qepF cfg hcfg
    change z ∈ support (((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg)
      ((Thm1.simImpl (2 + 1) qepF (fun _ => none) none fq).run m)).run g) >>=
      fun ⟨⟨a, m'⟩, g'⟩ => pure (a, (m', g'))) at hz
    rcases a6b_mem_support_bind hz with ⟨⟨⟨a, m'⟩, g'⟩, hmem, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hfig.simulateQ_preserve _ g hg ((a, m'), g') hmem
  transmit_out := by
    intro Q pub m₀ rc ⟨m, g⟩ hg z hz c hc
    have hfig := a6b_validEnv_fig8 P Dh encPt encT idOf lam qepF cfg hcfg
    change z ∈ support (((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg)
      ((Thm1.simTransmit (2 + 1) qepF (Q, (pub, m₀), rc)).run m)).run g) >>=
      fun ⟨⟨a, m'⟩, g'⟩ => pure (a, (m', g'))) at hz
    rcases a6b_mem_support_bind hz with ⟨⟨⟨a, m'⟩, g'⟩, hmem, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hc
    subst hc
    unfold Thm1.simTransmit at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    dsimp only at hmem
    rw [StateT.run_bind, StateT.run_lift, simulateQ_bind, StateT.run_bind] at hmem
    rcases a6b_mem_support_bind hmem with ⟨⟨⟨res, m₁⟩, g₁⟩, htr, hmem⟩
    simp only [SM.transmitQuery, HasQuery.query, simulateQ_bind, a6b_simulateQ_query_eq,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at htr
    rcases htr with ⟨⟨res', g₁'⟩, hq, heq⟩
    rcases Prod.mk.inj heq with ⟨h1, hg₁⟩
    rcases Prod.mk.inj h1 with ⟨hres, hm₁⟩
    rw [hres, hm₁, hg₁] at hmem
    dsimp only at hmem
    rcases res' with _ | c'
    · simp only [StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hmem
      rcases Prod.mk.inj (Prod.mk.inj hmem).1 with ⟨hnone, _⟩
      cases hnone
    · rcases hep : m.epMgmt (2 + 1) qepF Q rc.isSome with _ | s₁
      · rw [hep] at hmem
        simp only [StateT.run_pure, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hmem
        rcases Prod.mk.inj (Prod.mk.inj hmem).1 with ⟨hsome, _⟩
        injection hsome with hceq
        subst hceq
        exact hfig.transmit_out Q pub m₀ rc g hg (some c, g₁') hq c rfl
      · rw [hep] at hmem
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hmem
        rcases Prod.mk.inj (Prod.mk.inj hmem).1 with ⟨hsome, _⟩
        injection hsome with hceq
        subst hceq
        exact hfig.transmit_out Q pub m₀ rc g hg (some c, g₁') hq c rfl
  chall_out := by
    intro Q pub m₀ m₁ rc ⟨m, g⟩ hg z hz c hc
    have hfig := a6b_validEnv_fig8 P Dh encPt encT idOf lam qepF cfg hcfg
    change z ∈ support (((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam qepF cfg)
      ((Thm1.simChall (2 + 1) qepF (fun _ => none) none (Q, (pub, m₀), (pub, m₁), rc)).run m)).run g) >>=
      fun ⟨⟨a, m'⟩, g'⟩ => pure (a, (m', g'))) at hz
    rcases a6b_mem_support_bind hz with ⟨⟨⟨a, m'⟩, g'⟩, hmem, hz⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hc
    subst hc
    unfold Thm1.simChall at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    dsimp only at hmem
    rcases hep : m.epMgmt (2 + 1) qepF Q rc.isSome with _ | s₁
    · rw [hep] at hmem
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
      rcases Prod.mk.inj (Prod.mk.inj hmem).1 with ⟨hnone, _⟩
      cases hnone
    · rw [hep] at hmem
      dsimp only at hmem
      by_cases hsafe : (!s₁.safeCh (2 + 1) Q) = true
      · simp only [hsafe, ite_true, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
        rcases Prod.mk.inj (Prod.mk.inj hmem).1 with ⟨hnone, _⟩
        cases hnone
      · simp only [hsafe, Bool.false_eq_true, ite_false] at hmem
        rw [StateT.run_bind, StateT.run_lift, simulateQ_bind, StateT.run_bind] at hmem
        rcases a6b_mem_support_bind hmem with ⟨⟨⟨res, m₂⟩, g₁⟩, htr, hmem⟩
        have hmb : (if m.b then (pub, m₁) else (pub, m₀)) = (pub, if m.b then m₁ else m₀) := by
          cases m.b <;> rfl
        unfold Thm1.simSend at htr
        dsimp only [Option.getD] at htr
        rw [hmb] at htr
        simp only [SM.transmitQuery, HasQuery.query, simulateQ_bind, a6b_simulateQ_query_eq,
          simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion,
          support_pure, Set.mem_singleton_iff] at htr
        rcases htr with ⟨⟨res', g₁'⟩, hq, heq⟩
        rcases Prod.mk.inj heq with ⟨h1, hg₁⟩
        rcases Prod.mk.inj h1 with ⟨hres, hm₂⟩
        rw [hres, hm₂, hg₁] at hmem
        dsimp only at hmem
        rcases res' with _ | c'
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
          rcases Prod.mk.inj (Prod.mk.inj hmem).1 with ⟨hnone, _⟩
          cases hnone
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hmem
          rcases Prod.mk.inj (Prod.mk.inj hmem).1 with ⟨hsome, _⟩
          injection hsome with hceq
          subst hceq
          exact hfig.transmit_out Q pub (if m.b then m₁ else m₀) rc g hg (some c, g₁') hq c rfl

/-- Under `Corr.SpqrWeakCorrect` and `recvPanics = false`, `LibSimC` implies `LibSim`. -/
theorem libSim_of_libSimC_weak (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hdec : ∀ T, decT (encT T) = some T) (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ)
    (hS : Corr.SpqrWeakCorrect P.spqr)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (εcoll : ℝ≥0∞) (h : LibSimC P ℓ Dh encPt encT decT idOf lam qep q εcoll) :
    LibSim P ℓ Dh encPt encT decT idOf lam qep q εcoll := by
  obtain ⟨Inv, hI, _, hW1⟩ := hS
  intro A hq
  have hC := h A hq
  have hzero := hiddenSaltTerm_eq_zero_of_saltBinding P ℓ Dh encPt encT decT hdec hrt hL idOf lam qep Inv hI hW1 A
  rw [hzero, mul_zero, add_zero] at hC
  have hhyb :
      hybridAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) Config.h1
        (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) =
      hybridAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) Config.h1
        (sim P ℓ Dh encT decT qep A) := by
    have hrun : ∀ b,
        SM.run (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) Config.h1 b
          (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A) =
        SM.run (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) Config.h1 b
          (sim P ℓ Dh encT decT qep A) := by
      intro b
      unfold SM.run
      congr 1
      ext k
      have hE := a6b_validEnv_fig8 (ℓ := ℓ) P Dh encPt encT idOf lam (qep + 1) Config.h1 rfl
      exact hE.simC_eq_sim P Inv Dh encPt encT decT idOf lam qep hrt hL hI hW1 hnpR A
        (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b)
        (a6b_initState_fig8Inv P Dh encPt encT idOf lam k b)
    unfold hybridAdvantage SM.game
    simp only [hrun]
  have hauth : ∀ t tL,
      authAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) tL t
        (Thm1.challSim (2 + 1) (qep + 1) (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)) =
      authAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) tL t
        (Thm1.challSim (2 + 1) (qep + 1) (sim P ℓ Dh encT decT qep A)) := by
    intro t tL
    have hrun :
        SM.run (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) (Config.auth t) false
          (Thm1.challSim (2 + 1) (qep + 1) (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A)) =
        SM.run (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) (Config.auth t) false
          (Thm1.challSim (2 + 1) (qep + 1) (sim P ℓ Dh encT decT qep A)) := by
      unfold SM.run
      congr 1
      ext k
      change ((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam (qep + 1) (Config.auth t))
          (Thm1.challSim (2 + 1) (qep + 1) (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep A))).run
          (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k false)) =
        ((simulateQ (a6b_fig8Env P Dh encPt encT idOf lam (qep + 1) (Config.auth t))
          (Thm1.challSim (2 + 1) (qep + 1) (sim P ℓ Dh encT decT qep A))).run
          (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k false))
      unfold Thm1.challSim Thm1.simRun
      simp only [bind_assoc, pure_bind, StateT.run'_eq, simulateQ_bind, simulateQ_map,
        simulateQ_pure, StateT.run_bind, StateT.run_map, StateT.run_pure]
      apply a6b_bind_congr_support
      intro ⟨b, g₁⟩ hmem
      have hfig := a6b_validEnv_fig8 (ℓ := ℓ) P Dh encPt encT idOf lam (qep + 1) (Config.auth t) rfl
      have hg₁ : a6b_Fig8GameInv g₁ :=
        hfig.simulateQ_preserve _
          (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k false)
          (a6b_initState_fig8Inv P Dh encPt encT idOf lam k false) _ hmem
      have hchall := a6b_validEnv_challEnv (ℓ := ℓ) P Dh encPt encT idOf lam (qep + 1) (Config.auth t) rfl
      have heq := hchall.simC_eq_sim P Inv Dh encPt encT decT idOf lam qep hrt hL hI hW1 hnpR A
        ({ st := fun _ => (), b }, g₁) hg₁
      rw [a6b_simulateQ_challEnv_eq, a6b_simulateQ_challEnv_eq, heq]
    unfold authAdvantage SM.authGame
    simp only [hrun]
  simpa [hhyb, hauth] using hC

omit [Inhabited PQ] [SampleableType PQC] in
theorem spqrSendCorrect_of_weak {S : Spqr PQ PQC} (hS : Corr.SpqrWeakCorrect S)
    (hnpS : ∀ st r, S.sendPanics st r = false) :
    Corr.SpqrSendCorrect S := by
  obtain ⟨Inv, hI, h0, _⟩ := hS
  exact ⟨Inv, hI, h0, fun st r _ => hnpS st r⟩

/-- Recovers the `LibSim` bound of `Refine.libsignal_refines_weak` from
`Proofs.Refinement.libsignal_refines_C_proof` under `Corr.SpqrWeakCorrect`, absent SPQR panics,
`Dh.Commutes`, and AES-CBC decryption correctness. -/
theorem libsignal_refines_weak_of_C (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hX : X25519RealizesDh P.C Dh encPt encT)
    (hdec : ∀ T, decT (encT T) = some T) (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (hrt : SignalRoundTripShort P.codec) (hL : LengthsOk P ℓ) (hfit : SignalEncodeFits32 P.codec)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : Corr.SpqrWeakCorrect P.spqr)
    (hnpS : ∀ st r, P.spqr.sendPanics st r = false)
    (hnpR : ∀ st msg, P.spqr.recvPanics st msg = false)
    (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) :
    LibSim P ℓ Dh encPt encT decT idOf lam qep q ((qep + 2) * (q + qep + 2) * δ) :=
  libSim_of_libSimC_weak P ℓ Dh encPt encT decT hdec hrt hL hS hnpR idOf lam qep q _
    (Proofs.Refinement.libsignal_refines_C_proof P ℓ Dh hDh encPt encT decT hX hdec hD hrt hL hfit hinj hdum hz idOf hid lam qep q
      (Corr.spqrSendCorrectQ_of_spqrSendCorrect (spqrSendCorrect_of_weak hS hnpS) q) hq32 δ hδ)

/-- Tests whether a `unifSpec + SM.spec` query belongs to the `corr` summand. -/
def isCorrQuery (Msg Coins C : Type) :
    ℕ ⊕ (((((Party × Msg × Option Coins) ⊕ (Party × Msg × Msg × Option Coins)) ⊕ (Party × C)) ⊕
      (Party × C)) ⊕ Party) → Bool
  | .inr (.inr _) => true
  | _ => false

private theorem a6c_evalDist_eq_zero_of_support_false (oa : ProbComp Bool)
    (h : ∀ z ∈ support oa, z = false) : 𝒟[oa] {true} = 0 := by
  have heq : 𝒟[oa] = 𝒟[(pure false : ProbComp Bool)] := by
    rw [← bind_pure oa, evalDist_bind_congr_of_support oa pure (fun _ => pure false)]
    · exact OracleComp.evalDist_bind_const oa (pure false)
    · intro z hz
      rw [h z hz]
  rw [heq]
  simp

private theorem a6c_epMgmt_tL {St Msg C : Type} {s s₁ : GameState St Msg C} {Δ qep : ℕ}
    {Q : Party} {bad : Bool} (htL : s.tL = none) (h : s.epMgmt Δ qep Q bad = some s₁) :
    s₁.tL = none := by
  unfold GameState.epMgmt GameState.safeCh healedBy at h
  simp only [htL, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
  split_ifs at h <;> cases h <;> first | rfl | exact htL

private def a6c_preservesB {α : Type} {ℓ : ℕ}
    (y : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α) : Prop :=
  ∀ (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (qepF : ℕ) (s : LibsignalSim.SimState PQ Pt ℓ)
    (g : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt)),
    s.mir.tL = none →
    ∀ z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF) (y.run s)).run g),
      z.1.2.mir.tL = none

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_pure {α : Type} {ℓ : ℕ} (a : α) :
    a6c_preservesB (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (pure a) := by
  intro fig qepF s g htL z hz
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact htL

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_bind {α β : Type} {ℓ : ℕ}
    {y : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α}
    {f : α → StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) β}
    (hy : a6c_preservesB y) (hf : ∀ a, a6c_preservesB (f a)) :
    a6c_preservesB (y >>= f) := by
  intro fig qepF s g htL z hz
  simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨⟨a, s₁⟩, g₁⟩, h₁, h₂⟩
  exact hf a fig qepF s₁ g₁ (hy fig qepF s g htL _ h₁) z h₂

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_get_bind {α : Type} {ℓ : ℕ}
    {f : LibsignalSim.SimState PQ Pt ℓ →
      StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α}
    (hf : ∀ s, s.mir.tL = none → a6c_preservesB (f s)) :
    a6c_preservesB (get >>= f) := by
  intro fig qepF s g htL z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact hf s htL fig qepF s g htL z hz

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_putS {ℓ : ℕ} (s' : LibsignalSim.SimState PQ Pt ℓ)
    (htL' : s'.mir.tL = none) :
    a6c_preservesB (LibsignalSim.putS s') := by
  intro fig qepF s g _ z hz
  unfold LibsignalSim.putS at hz
  simp only [StateT.run_set, StateT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst hz
  exact htL'

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_liftQ {α : Type} {ℓ : ℕ} (x : LibsignalSim.Fig8Comp Pt ℓ α) :
    a6c_preservesB (PQ := PQ) (LibsignalSim.liftQ x) := by
  intro fig qepF s g htL z hz
  change z ∈ support ((simulateQ (LibsignalSimC.fig8ImplH1 fig qepF)
    (x >>= fun a => pure (a, s))).run g) at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
  rcases hz with ⟨⟨a, g₁⟩, _, rfl⟩
  exact htL

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_coin {ℓ : ℕ} (α : Type) [SampleableType α] :
    a6c_preservesB (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (LibsignalSim.coin α) :=
  a6c_preservesB_liftQ _

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_fwd {ℓ : ℕ} (Q : Party) (c : LibsignalSim.Fig8C Pt) :
    a6c_preservesB (PQ := PQ) (ℓ := ℓ) (LibsignalSim.fwd Q c) := by
  unfold LibsignalSim.fwd
  refine a6c_preservesB_get_bind fun s _ => ?_
  dsimp only
  split <;> exact a6c_preservesB_liftQ _

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_onAccept {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) :
    a6c_preservesB (Pt := Pt) (LibsignalSim.onAccept (qep := qep) Q w isDel t i m ci? T pq') := by
  unfold LibsignalSim.onAccept
  refine a6c_preservesB_get_bind fun s htL => ?_
  dsimp only
  split
  · cases s.mir.inTransit Q.other w with
    | none => exact a6c_preservesB_pure none
    | some r =>
      exact a6c_preservesB_bind (a6c_preservesB_putS _ htL) fun _ => a6c_preservesB_pure _
  · split
    · exact a6c_preservesB_pure _
    · split
      · exact a6c_preservesB_bind (a6c_preservesB_putS _ htL) fun _ => a6c_preservesB_pure _
      · exact a6c_preservesB_bind (a6c_preservesB_putS _ htL) fun _ => a6c_preservesB_pure _

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preservesB_onAnswer {ℓ : ℕ} (qep : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))) :
    a6c_preservesB (Pt := Pt) (LibsignalSim.onAnswer (qep := qep) Q w isDel ci? T pq' res) := by
  unfold LibsignalSim.onAnswer
  cases res with
  | none => exact a6c_preservesB_pure _
  | some rr =>
    cases rr with
    | rejected => exact a6c_preservesB_pure _
    | accepted t i pm => exact a6c_preservesB_onAccept qep Q w isDel t i _ ci? T pq'

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6c_preservesB_simSend {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    a6c_preservesB (Pt := Pt) (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r) := by
  unfold LibsignalSim.simSend
  refine a6c_preservesB_get_bind fun s htL => ?_
  dsimp only
  split
  · exact a6c_preservesB_pure none
  · cases hep : s.mir.epMgmt 3 qep Q r.isSome with
    | none => exact a6c_preservesB_pure none
    | some s₁ =>
      have htL₁ : s₁.tL = none := a6c_epMgmt_tL htL hep
      dsimp only
      split
      · exact a6c_preservesB_pure none
      · cases r with
        | none =>
          dsimp only
          refine a6c_preservesB_bind (a6c_preservesB_coin PQC) fun rq => ?_
          refine a6c_preservesB_bind (a6c_preservesB_pure none) fun rc => ?_
          cases LibsignalSim.mkPub (P := P) s Q rq _ with
          | none => exact a6c_preservesB_pure none
          | some p =>
            rcases p with ⟨pq', pub⟩
            cases chal with
            | none =>
              dsimp only
              refine a6c_preservesB_bind (a6c_preservesB_liftQ _) fun res => ?_
              cases res with
              | none => exact a6c_preservesB_pure none
              | some c =>
                exact a6c_preservesB_bind (a6c_preservesB_putS _ htL₁) fun _ =>
                  a6c_preservesB_pure _
            | some m₁ =>
              dsimp only
              refine a6c_preservesB_bind (a6c_preservesB_liftQ _) fun res => ?_
              cases res with
              | none => exact a6c_preservesB_pure none
              | some c =>
                exact a6c_preservesB_bind (a6c_preservesB_putS _ htL₁) fun _ =>
                  a6c_preservesB_pure _
        | some rq =>
          dsimp only
          refine a6c_preservesB_bind (a6c_preservesB_pure rq) fun rq' => ?_
          simp only [map_eq_bind_pure_comp]
          refine a6c_preservesB_bind
            (a6c_preservesB_bind (a6c_preservesB_coin (BitVec 256)) fun _ =>
              a6c_preservesB_pure _) fun rc => ?_
          cases LibsignalSim.mkPub (P := P) s Q rq' _ with
          | none => exact a6c_preservesB_pure none
          | some p =>
            rcases p with ⟨pq', pub⟩
            cases chal with
            | none =>
              dsimp only
              refine a6c_preservesB_bind (a6c_preservesB_liftQ _) fun res => ?_
              cases res with
              | none => exact a6c_preservesB_pure none
              | some c =>
                exact a6c_preservesB_bind (a6c_preservesB_putS _ htL₁) fun _ =>
                  a6c_preservesB_pure _
            | some m₁ =>
              dsimp only
              refine a6c_preservesB_bind (a6c_preservesB_liftQ _) fun res => ?_
              cases res with
              | none => exact a6c_preservesB_pure none
              | some c =>
                exact a6c_preservesB_bind (a6c_preservesB_putS _ htL₁) fun _ =>
                  a6c_preservesB_pure _

private def a6c_preserves {α : Type} {ℓ : ℕ}
    (m : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSimC.ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : GameState (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (LibsignalSim.Fig8C Pt) × Bool),
    sC.base.mir.tL = none → gh.2 = false →
    ∀ z ∈ support ((m.run sC).run gh), z.1.2.base.mir.tL = none ∧ z.2.2 = false

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_pure {α : Type} {ℓ : ℕ} (a : α) :
    a6c_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (pure a) := by
  intro sC gh htL hgh z hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨htL, hgh⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_bind {α β : Type} {ℓ : ℕ}
    {m : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSimC.ProbeM Pt ℓ) α}
    {f : α → StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSimC.ProbeM Pt ℓ) β}
    (hm : a6c_preserves m) (hf : ∀ a, a6c_preserves (f a)) :
    a6c_preserves (m >>= f) := by
  intro sC gh htL hgh z hz
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨⟨a, sC₁⟩, gh₁⟩, h₁, h₂⟩
  obtain ⟨htL₁, hgh₁⟩ := hm sC gh htL hgh _ h₁
  exact hf a sC₁ gh₁ htL₁ hgh₁ z h₂

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_get_bind {α : Type} {ℓ : ℕ}
    {f : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ →
      StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSimC.ProbeM Pt ℓ) α}
    (hf : ∀ sC, sC.base.mir.tL = none → a6c_preserves (f sC)) :
    a6c_preserves (get >>= f) := by
  intro sC gh htL hgh z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact hf sC htL sC gh htL hgh z hz

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_set {ℓ : ℕ} (sC' : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (htL' : sC'.base.mir.tL = none) :
    a6c_preserves (set sC' : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSimC.ProbeM Pt ℓ) Unit) := by
  intro sC gh _ hgh z hz
  simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨htL', hgh⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_modify {ℓ : ℕ}
    (f : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (hf : ∀ sC, sC.base.mir.tL = none → (f sC).base.mir.tL = none) :
    a6c_preserves (modify f) := by
  intro sC gh htL hgh z hz
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hf sC htL, hgh⟩

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_liftC {α : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (qepF : ℕ) (x : LibsignalSim.Fig8Comp Pt ℓ α) :
    a6c_preserves (PQ := PQ) (LibsignalSimC.liftC (LibsignalSimC.probeHook fig qepF) x) := by
  intro sC gh htL hgh z hz
  change z ∈ support (((LibsignalSimC.probeHook fig qepF).lift x >>=
    fun a => pure (a, sC)).run gh) at hz
  simp only [StateT.run_bind, LibsignalSimC.probeHook_lift_run, bind_assoc, pure_bind,
    StateT.run_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
  rcases hz with ⟨⟨a, g'⟩, _, rfl⟩
  exact ⟨htL, hgh⟩

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_zoomB {α : Type} {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (qepF : ℕ)
    {y : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α}
    (hy : a6c_preservesB y) :
    a6c_preserves (LibsignalSimC.runOnBaseState (LibsignalSimC.probeHook fig qepF) y) := by
  intro sC gh htL hgh z hz
  change z ∈ support (((LibsignalSimC.probeHook fig qepF).lift (y.run sC.base) >>=
    fun p => pure (p.1, { sC with base := p.2 })).run gh) at hz
  simp only [StateT.run_bind, LibsignalSimC.probeHook_lift_run, bind_assoc, pure_bind,
    StateT.run_pure, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
  rcases hz with ⟨⟨⟨a, s'⟩, g'⟩, h₁, rfl⟩
  exact ⟨hy fig qepF sC.base gh.1 htL _ h₁, hgh⟩

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_fwdAnswerC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : LibsignalSim.Fig8C Pt) :
    a6c_preserves (LibsignalSimC.fwdAnswerC (qep := qep) (fig := fig) (fs := fs)
      (H := LibsignalSimC.probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold LibsignalSimC.fwdAnswerC
  refine a6c_preserves_bind (a6c_preserves_zoomB fig qepF (a6c_preservesB_fwd Q c')) fun res => ?_
  cases res with
  | none =>
    exact a6c_preserves_zoomB fig qepF (a6c_preservesB_onAnswer qep Q w isDel ci? T pq' none)
  | some rr =>
    cases rr with
    | rejected =>
      exact a6c_preserves_zoomB fig qepF
        (a6c_preservesB_onAnswer qep Q w isDel ci? T pq' (some .rejected))
    | accepted t i pm =>
      exact a6c_preserves_bind (a6c_preserves_modify _ fun _ h => h) fun _ =>
        a6c_preserves_zoomB fig qepF
          (a6c_preservesB_onAnswer qep Q w isDel ci? T pq' (some (.accepted t i pm)))

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_fwdC (P : Params PQ PQC) {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (LibsignalSim.Fig8C Pt))
    (c' : LibsignalSim.Fig8C Pt) :
    a6c_preserves (LibsignalSimC.fwdC (P := P) (qep := qep) (fig := fig) (fs := fs)
      (H := LibsignalSimC.probeHook fig qepF) Q w isDel ci? T pq' honestC c') := by
  unfold LibsignalSimC.fwdC
  refine a6c_preserves_get_bind fun sC htL => ?_
  cases honestC with
  | none => exact a6c_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'
  | some c =>
    have hsi : sC.base.mir.safeInj 3 = true := by simp [GameState.safeInj, healedBy, htL]
    simp only [hsi, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact a6c_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_fwdEvictC {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : LibsignalSim.Fig8C Pt) :
    a6c_preserves (LibsignalSimC.fwdEvictC (qep := qep) (fig := fig) (fs := fs)
      (H := LibsignalSimC.probeHook fig qepF) Q w isDel T pq' c') := by
  unfold LibsignalSimC.fwdEvictC
  refine a6c_preserves_get_bind fun sC htL => ?_
  have hsi : sC.base.mir.safeInj 3 = true := by simp [GameState.safeInj, healedBy, htL]
  simp only [hsi, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  exact a6c_preserves_fwdAnswerC qep fig fs qepF Q w isDel none T pq' c'

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_ite {α : Type} {ℓ : ℕ} (c : Prop) [Decidable c]
    {t e : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSimC.ProbeM Pt ℓ) α}
    (ht : a6c_preserves t) (he : a6c_preserves e) :
    a6c_preserves (if c then t else e) := by
  by_cases hc : c <;> simp [hc, ht, he]

omit [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_simRecvC {ℓ : ℕ} (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    a6c_preserves (LibsignalSimC.simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := LibsignalSimC.probeHook fig qepF) Q w isDel) := by
  unfold LibsignalSimC.simRecvC
  refine a6c_preserves_get_bind fun sC _ => ?_
  dsimp only
  refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
  refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
  refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
  refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact a6c_preserves_pure _
  | some hp =>
    rcases hp with ⟨h, _⟩
    dsimp only
    refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
    refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact a6c_preserves_pure _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        exact a6c_preserves_ite _ (a6c_preserves_pure _)
          (a6c_preserves_fwdC P qep fig fs qepF Q w isDel (some ci) h.senderRatchetKey pq' _ _)
      | none =>
        dsimp only
        refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
        refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
        refine a6c_preserves_ite _ ?_ ?_
        · refine a6c_preserves_bind (a6c_preserves_modify _ fun _ h => h) fun _ => ?_
          refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
          cases decT h.senderRatchetKey with
          | none => exact a6c_preserves_pure _
          | some T =>
            exact a6c_preserves_ite _
              (a6c_preserves_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (a6c_preserves_fwdC P qep fig fs qepF Q w isDel none h.senderRatchetKey pq' _ _)
        · refine a6c_preserves_ite _ (a6c_preserves_pure _) ?_
          cases decT h.senderRatchetKey with
          | none => exact a6c_preserves_pure _
          | some T =>
            exact a6c_preserves_ite _
              (a6c_preserves_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (a6c_preserves_fwdC P qep fig fs qepF Q w isDel none h.senderRatchetKey pq' _ _)

omit [Zero Pt] [SampleableType Pt] [Inhabited PQ] in
private theorem a6c_preserves_simSendC {ℓ : ℕ} (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    a6c_preserves (LibsignalSimC.simSendC (P := P) (qep := qep) (fig := fig)
      (H := LibsignalSimC.probeHook fig qepF) Q m₀ chal r) := by
  unfold LibsignalSimC.simSendC
  refine a6c_preserves_bind (a6c_preserves_zoomB fig qepF (a6c_preservesB_simSend P qep Q m₀ chal r))
    fun res => ?_
  cases res with
  | none => exact a6c_preserves_pure none
  | some w =>
    refine a6c_preserves_get_bind fun sC htL => ?_
    exact a6c_preserves_bind (a6c_preserves_set _ htL) fun _ => a6c_preserves_pure (some w)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem a6c_preserves_guardC {α : Type} {ℓ : ℕ}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) (LibsignalSimC.ProbeM Pt ℓ) (Option α)}
    (hx : a6c_preserves x) :
    a6c_preserves (LibsignalSimC.guardC x) := by
  unfold LibsignalSimC.guardC
  refine a6c_preserves_get_bind fun sC _ => ?_
  exact a6c_preserves_ite _ (a6c_preserves_pure none) hx

omit [SampleableType Pt] [Inhabited PQ] in
private theorem a6c_preserves_simImplC {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (ht : ¬ isCorrQuery (Plain ℓ) PQC (List (BitVec 8)) t = true) :
    a6c_preserves (LibsignalSimC.simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := LibsignalSimC.probeHook fig qepF) Dh t) := by
  rcases t with n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact a6c_preserves_liftC fig qepF _
  · exact a6c_preserves_guardC (a6c_preserves_simSendC P qep fig qepF Q m none r)
  · exact a6c_preserves_guardC (a6c_preserves_simSendC P qep fig qepF Q m₀ (some m₁) r)
  · exact a6c_preserves_guardC (a6c_preserves_simRecvC P encT decT qep fig fs qepF Q w true)
  · exact a6c_preserves_guardC (a6c_preserves_simRecvC P encT decT qep fig fs qepF Q w false)
  · exact absurd rfl ht

omit [SampleableType Pt] [Inhabited PQ] in
private theorem a6c_preserves_simulateQ {α : Type} {ℓ : ℕ} (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (hcorr : oa.IsQueryBoundP (fun t => isCorrQuery (Plain ℓ) PQC (List (BitVec 8)) t = true) 0) :
    a6c_preserves (simulateQ (LibsignalSimC.simImplC (P := P) (encT := encT) (decT := decT)
      (qep := qep) (fig := fig) (fs := fs) (H := LibsignalSimC.probeHook fig qepF) Dh) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simpa only [simulateQ_pure] using a6c_preserves_pure a
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hcorr
    rcases hcorr with ⟨ht | h0, hk⟩
    · simp only [simulateQ_query_bind]
      exact a6c_preserves_bind (a6c_preserves_simImplC P Dh encT decT qep fig fs qepF t ht)
        fun u => ih u (by simpa using hk u)
    · exact absurd h0 (Nat.lt_irrefl 0)

/-- An adversary that makes no `corr` queries and never supplies send coins has
`hiddenSaltTerm = 0`, because `mir.tL` remains `none` and `safeInj` holds throughout. -/
theorem hiddenSaltTerm_eq_zero_of_uncompromised (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : LibAdv PQ PQC ℓ) (hcoins : SM.HonestCoins A)
    (hcorr : A.IsQueryBoundP (fun t => isCorrQuery (Plain ℓ) PQC (List (BitVec 8)) t = true) 0) :
    LibsignalSimC.hiddenSaltTerm P ℓ Dh encPt encT decT idOf lam qep A = 0 := by
  let _ := hcoins
  unfold LibsignalSimC.hiddenSaltTerm
  refine a6c_evalDist_eq_zero_of_support_false _ fun z hz => ?_
  unfold LibsignalSimC.hiddenSaltGame LibsignalSimC.simRunCWith at hz
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply, StateT.run_bind,
    StateT.run_pure, LibsignalSimC.probeHook_lift_run, bind_assoc, pure_bind,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
  rcases hz with ⟨b, _, k, _, ⟨pqrKey, g₁⟩, _, ⟨⟨_, sC'⟩, gh'⟩, hsim, hzeq⟩
  rw [hzeq]
  exact (a6c_preserves_simulateQ P Dh encT decT qep
    (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
    (lFS P.C P.codec ℓ encT idOf 25000) (qep + 1) A hcorr
    (LibsignalSimC.initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (g₁, false) rfl rfl _ hsim).2

end Refine

end CryptoGames.LibsignalSM
