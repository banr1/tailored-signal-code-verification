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
# Epoch-Cap Invariance for `SM.run` and `libsignalToModularSchemeSim`

Proves that against any `q`-query adversary, all party, in-transit, and `Fig8St.tcur` epochs remain
at most `q + 1`, so `SM.run` on `lFig8` and `libsignalToModularSchemeSim` are invariant in any
epoch cap `≥ q + 1`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8QepCap

open OracleSpec OracleComp
open CryptoGames (Party SMScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFS lFig8)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C Fig8Comp SimState toWire initSim simSend fwd onAccept onAnswer)
open CryptoGames.Ratchet.LibsignalSimC
  (LibsignalToModularSchemeSimState idHook runOnBaseState liftC predictReceiveWithSnapshots
   simSendC fwdAnswerC resyncC fwdC fwdEvictC simRecvC simCorrC guardC simImplC initSimC)
open CryptoGames.LibsignalSM.Refine (libsignalToModularSchemeSim)
open CryptoGames.LibsignalSession
  (Params Crypto IdentityKey PublicKey GhostState SignalMessageProtoCodec)
open CryptoGames.SM (Pos Record GameState RecvResult)

noncomputable section

private abbrev Fig8G (Pt : Type) (ℓ : ℕ) := GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)
private abbrev FSpec' (Pt : Type) (ℓ : ℕ) :=
  unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)

private theorem epMgmt_eq_of_epoch_lt {St Msg C : Type} (s : GameState St Msg C) (Δ qep₁ qep₂ : ℕ)
    (P : Party) (bad : Bool) (h₁ : s.epoch P + 1 ≤ qep₁) (h₂ : s.epoch P + 1 ≤ qep₂) :
    s.epMgmt Δ qep₁ P bad = s.epMgmt Δ qep₂ P bad := by
  unfold GameState.epMgmt
  have h1a : ¬ (qep₁ < s.epoch P + 1) := by omega
  have h2a : ¬ (qep₂ < s.epoch P + 1) := by omega
  have h1b : ¬ (qep₁ < s.epoch P) := by omega
  have h2b : ¬ (qep₂ < s.epoch P) := by omega
  simp [h1a, h2a, h1b, h2b]

private theorem epMgmt_epoch_trans' {St Msg C : Type} (s s₁ : GameState St Msg C) (Δ qep : ℕ)
    (Q : Party) (bad : Bool) (h : s.epMgmt Δ qep Q bad = some s₁) :
    (∀ R : Party, s₁.epoch R ≤ s.epoch R + 1) ∧ s₁.trans = s.trans ∧ s₁.st = s.st := by
  unfold GameState.epMgmt at h; split_ifs at h with h1 h2 h3 h4 <;> injection h with h <;> subst h
  · refine ⟨fun R => ?_, rfl, rfl⟩; by_cases hR : R = Q <;> simp [hR, GameState.leak]
  · refine ⟨fun R => ?_, rfl, rfl⟩; by_cases hR : R = Q <;> simp [hR]
  · exact ⟨fun _ => Nat.le_add_right _ 1, rfl, rfl⟩

private theorem lFig8_send_tcur_le {Pt : Type} [Zero Pt] {ℓ : ℕ} (C : Crypto) (codec : SignalMessageProtoCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (st : Fig8St Pt) (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256) :
    ((lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send st m coins).1.tcur ≤ st.tcur + 1 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.send]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ↓reduceIte, lFS, CryptoGames.FSAEAD.fromAEADPRG]; omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]; cases st.vS <;> simp

private theorem lFig8_receive_tcur_le {Pt : Type} [Zero Pt] {ℓ : ℕ} (C : Crypto) (codec : SignalMessageProtoCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (st st' : Fig8St Pt) (c : Fig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c = some (st', t, i, pm)) :
    t ≤ st.tcur + 1 ∧ st'.tcur ≤ st.tcur + 1 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.receive] at h
  split at h
  · cases h
  · rename_i h1; simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h1
    split at h
    · cases h
    · rename_i s₁ hs₁
      have hs₁_le : s₁.tcur ≤ st.tcur + 1 := by
        split_ifs at hs₁ with heq
        · rcases hc12 : c.1.2 with _ | Tn <;> rw [hc12] at hs₁
          · cases hs₁
          · injection hs₁ with hs₁; subst hs₁; exact h1.2
        · injection hs₁ with hs₁; subst hs₁; exact Nat.le_add_right _ 1
      split at h
      · cases h
      · rename_i v _
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive v c.1 c.2 with _ | ⟨v₁, i₁, pm₁⟩
        · rw [hfs] at h; cases h
        · rw [hfs] at h; injection h with h; injection h with hst' ht'; injection ht' with ht' _
          subst hst' ht'; exact ⟨h1.2, hs₁_le⟩

private structure Fig8CapInv {Pt : Type} {ℓ : ℕ} (q m : ℕ) (gs : Fig8G Pt ℓ) : Prop where
  hep : ∀ Q : Party, gs.epoch Q + m ≤ q + 1
  htrans : ∀ r ∈ gs.trans, r.pos.epoch + m ≤ q + 1
  htcur : ∀ Q : Party, (gs.st Q).tcur + m ≤ q + 1

private theorem Fig8CapInv.mono {Pt : Type} {ℓ q m₁ m₂ : ℕ} {gs : Fig8G Pt ℓ}
    (hle : m₁ ≤ m₂) (h : Fig8CapInv q m₂ gs) : Fig8CapInv q m₁ gs :=
  ⟨fun Q => by have := h.hep Q; omega, fun r hr => by have := h.htrans r hr; omega,
   fun Q => by have := h.htcur Q; omega⟩

private theorem Fig8CapInv.withWin {Pt : Type} {ℓ q m : ℕ} {gs : Fig8G Pt ℓ}
    (h : Fig8CapInv q m gs) (w : Bool) : Fig8CapInv q m { gs with win := w } := ⟨h.hep, h.htrans, h.htcur⟩

private theorem fig8CapInv_init {Pt : Type} [Zero Pt] {ℓ : ℕ} (C : Crypto) (codec : SignalMessageProtoCodec)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (q : ℕ) (k : BitVec 256 × BitVec 256) (b : Bool) :
    Fig8CapInv q q (CryptoGames.SM.initState (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) k b) where
  hep Q := by dsimp [CryptoGames.SM.initState]; omega
  htrans _ hr := by simp [CryptoGames.SM.initState] at hr
  htcur Q := by
    dsimp only [CryptoGames.SM.initState, lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.initParty]
    cases Q <;> dsimp only [] <;> omega

private def fig8RunImpl {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) :
    QueryImpl (FSpec' Pt ℓ) (StateT (Fig8G Pt ℓ) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Fig8G Pt ℓ) ProbComp) + CryptoGames.SM.oracleImpl fig 3 QEP cfg

private theorem monadLift_prob_run' {σ α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = (p >>= fun a => pure (a, s)) := rfl

private theorem simulateQ_fig8RunImpl_liftProb {Pt α : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (p : ProbComp α) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8RunImpl fig QEP cfg) (liftM p : Fig8Comp Pt ℓ α)).run gs = (p >>= fun a => pure (a, gs)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t mx ih =>
    change (simulateQ (fig8RunImpl fig QEP cfg) (query (spec := FSpec' Pt ℓ) (.inl t) >>= fun u => liftM (mx u))).run gs =
      ((query t >>= mx) >>= fun a => pure (a, gs))
    rw [simulateQ_bind, StateT.run_bind, bind_assoc]
    have hinl : (simulateQ (fig8RunImpl fig QEP cfg) (query (spec := FSpec' Pt ℓ) (.inl t))).run gs =
        (query t >>= fun u => pure (u, gs)) := by
      simp only [query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]; rfl
    rw [hinl]; simp only [bind_assoc, pure_bind]; exact bind_congr fun u => ih u

private theorem fig8CapInv_record {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP : ℕ) (gs s₁ : Fig8G Pt ℓ)
    (Q : Party) (bad isChall : Bool) (msg : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (hfg : Fig8CapInv q (m + 1) gs) (hep : gs.epMgmt 3 QEP Q bad = some s₁) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam
    let out := fig.send (s₁.st Q) msg coins
    Fig8CapInv q m (s₁.record 3 Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, msg, out.2⟩ isChall) := by
  obtain ⟨hep_le, htr, hst⟩ := epMgmt_epoch_trans' gs s₁ 3 QEP Q bad hep
  have htcur' := lFig8_send_tcur_le C codec Dh encPt encT idOf lam (s₁.st Q) msg coins
  have hfg0 := hfg.mono (Nat.le_succ m)
  refine {
    hep := fun R => by dsimp only [GameState.record]; have := hep_le R; have := hfg.hep R; omega
    htrans := fun r hr => by
      dsimp only [GameState.record] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · dsimp only []; have := hep_le Q; have := hfg.hep Q; omega
      · rw [htr] at hr; exact hfg0.htrans r hr
    htcur := fun R => by
      dsimp only [GameState.record]
      by_cases hR : R = Q
      · subst hR; simp only [Function.update_self]; rw [hst] at htcur' ⊢; have := hfg.htcur R; omega
      · simp only [Function.update_of_ne hR, hst]; exact hfg0.htcur R }

private theorem fig8CapInv_accept {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m : ℕ) (gs : Fig8G Pt ℓ) (Q : Party) (c : Fig8C Pt) (st' : Fig8St Pt) (t i : ℕ)
    (pm : LibsignalMsgPublicPart × Plain ℓ) (pos : Pos) (hpos : pos.epoch + m ≤ q + 1)
    (hfg : Fig8CapInv q (m + 1) gs)
    (hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c =
      some (st', t, i, pm)) :
    Fig8CapInv q m (gs.accept Q st' pos) := by
  obtain ⟨_, hst'⟩ := lFig8_receive_tcur_le C codec Dh encPt encT idOf lam (gs.st Q) st' c t i pm hrcv
  have hfg0 := hfg.mono (Nat.le_succ m)
  refine {
    hep := fun R => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hR : R = Q
      · subst hR; simp only [Function.update_self]; have := hfg0.hep R; omega
      · simp only [Function.update_of_ne hR]; exact hfg0.hep R
    htrans := fun r hr => by
      dsimp only [GameState.accept, GameState.delete] at hr
      exact hfg0.htrans r (List.mem_of_mem_filter hr)
    htcur := fun R => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hR : R = Q
      · subst hR; simp only [Function.update_self]; have := hfg.htcur R; omega
      · simp only [Function.update_of_ne hR]; exact hfg0.htcur R }

private theorem transmitImpl_qep_eq_and_inv {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP₁ QEP₂ : ℕ) (hQ₁ : q + 1 ≤ QEP₁) (hQ₂ : q + 1 ≤ QEP₂)
    (Q : Party) (msg : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam
    (CryptoGames.SM.transmitImpl fig 3 QEP₁ (Q, msg, rc)).run gs =
      (CryptoGames.SM.transmitImpl fig 3 QEP₂ (Q, msg, rc)).run gs ∧
    ∀ u gs', (u, gs') ∈ support ((CryptoGames.SM.transmitImpl fig 3 QEP₁ (Q, msg, rc)).run gs) → Fig8CapInv q m gs' := by
  intro fig; have hfg0 := hfg.mono (Nat.le_succ m)
  have hep_eq : ∀ bad, gs.epMgmt 3 QEP₁ Q bad = gs.epMgmt 3 QEP₂ Q bad := fun bad =>
    epMgmt_eq_of_epoch_lt gs 3 QEP₁ QEP₂ Q bad (by have := hfg.hep Q; omega) (by have := hfg.hep Q; omega)
  refine ⟨?_, fun u gs' hmem => ?_⟩
  · unfold CryptoGames.SM.transmitImpl
    by_cases hw : gs.win = true
    · simp [hw]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, monadLift_prob_run', pure_bind, bind_assoc]
      exact bind_congr fun ⟨_, bad⟩ => by rw [hep_eq bad]
  · unfold CryptoGames.SM.transmitImpl at hmem
    by_cases hw : gs.win = true
    · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hfg0
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, monadLift_prob_run', pure_bind, bind_assoc, mem_support_bind_iff] at hmem
      obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
      rcases hep : gs.epMgmt 3 QEP₁ Q bad with _ | s₁ <;>
        simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      · rcases hmem with ⟨_, rfl⟩; exact hfg0
      · rcases hmem with ⟨_, rfl⟩; exact fig8CapInv_record C codec Dh encPt encT idOf lam q m QEP₁ gs s₁ Q bad false msg coins hfg hep

private theorem challImpl_qep_eq_and_inv {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP₁ QEP₂ : ℕ) (hQ₁ : q + 1 ≤ QEP₁) (hQ₂ : q + 1 ≤ QEP₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam
    (CryptoGames.SM.challImpl fig 3 QEP₁ cfg (Q, m₀, m₁, rc)).run gs =
      (CryptoGames.SM.challImpl fig 3 QEP₂ cfg (Q, m₀, m₁, rc)).run gs ∧
    ∀ u gs', (u, gs') ∈ support ((CryptoGames.SM.challImpl fig 3 QEP₁ cfg (Q, m₀, m₁, rc)).run gs) → Fig8CapInv q m gs' := by
  intro fig; have hfg0 := hfg.mono (Nat.le_succ m)
  have hep_eq : ∀ bad, gs.epMgmt 3 QEP₁ Q bad = gs.epMgmt 3 QEP₂ Q bad := fun bad =>
    epMgmt_eq_of_epoch_lt gs 3 QEP₁ QEP₂ Q bad (by have := hfg.hep Q; omega) (by have := hfg.hep Q; omega)
  refine ⟨?_, fun u gs' hmem => ?_⟩
  · unfold CryptoGames.SM.challImpl
    by_cases hw : gs.win = true
    · simp [hw]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, monadLift_prob_run', pure_bind, bind_assoc]
      exact bind_congr fun ⟨_, bad⟩ => by rw [hep_eq bad]
  · unfold CryptoGames.SM.challImpl at hmem
    by_cases hw : gs.win = true
    · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hfg0
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, monadLift_prob_run', pure_bind, bind_assoc, mem_support_bind_iff] at hmem
      obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
      rcases hep : gs.epMgmt 3 QEP₁ Q bad with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hfg0
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh 3 Q) || !(cfg.challAllowedIn (s₁.epoch Q))) = true
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hfg0
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact fig8CapInv_record C codec Dh encPt encT idOf lam q m QEP₁ gs s₁ Q bad true _ coins hfg hep

private theorem deliverImpl_inv {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam
    ∀ u gs', (u, gs') ∈ support ((CryptoGames.SM.deliverImpl fig cfg (Q, c)).run gs) →
      Fig8CapInv q m gs' ∧ ∀ t' i' pm', u = some (RecvResult.accepted t' i' pm') → t' + m ≤ q + 1 := by
  intro fig u gs' hmem; have hfg0 := hfg.mono (Nat.le_succ m)
  unfold CryptoGames.SM.deliverImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact ⟨hfg0, fun _ _ _ hu => by cases hu⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hin : gs.inTransit Q.other c with _ | r
    · simp only [hin, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩; exact ⟨hfg0, fun _ _ _ hu => by cases hu⟩
    · simp only [hin] at hmem
      have hr_ep : r.pos.epoch + m ≤ q + 1 := by have := hfg.htrans r (List.mem_of_find?_eq_some hin); omega
      rcases hrcv : fig.receive (gs.st Q) c with _ | ⟨st', t', i', m'⟩
      · simp only [hrcv] at hmem
        split_ifs at hmem <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;> rcases hmem with ⟨rfl, rfl⟩
        · exact ⟨hfg0.withWin true, fun _ _ _ hu => by cases hu⟩
        · exact ⟨hfg0, fun _ _ _ hu => by cases hu⟩
      · simp only [hrcv] at hmem
        obtain ⟨ht'_le, _⟩ := lFig8_receive_tcur_le C codec Dh encPt encT idOf lam (gs.st Q) st' c t' i' m' hrcv
        have ht'_m : t' + m ≤ q + 1 := by have := hfg.htcur Q; omega
        have hacc := fig8CapInv_accept C codec Dh encPt encT idOf lam q m gs Q c st' t' i' m' r.pos hr_ep hfg hrcv
        split_ifs at hmem
        all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem; rcases hmem with ⟨hu, rfl⟩
        all_goals first
          | exact ⟨hacc.withWin true, fun t₀ i₀ pm₀ hu' => by rw [hu] at hu'; cases hu'; exact ht'_m⟩
          | exact ⟨hacc, fun t₀ i₀ pm₀ hu' => by rw [hu] at hu'; cases hu'; exact ht'_m⟩

private theorem injectImpl_qep_eq_and_inv {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP₁ QEP₂ : ℕ) (hQ₁ : q + 1 ≤ QEP₁) (hQ₂ : q + 1 ≤ QEP₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam
    (CryptoGames.SM.injectImpl fig 3 QEP₁ cfg (Q, c)).run gs = (CryptoGames.SM.injectImpl fig 3 QEP₂ cfg (Q, c)).run gs ∧
    ∀ u gs', (u, gs') ∈ support ((CryptoGames.SM.injectImpl fig 3 QEP₁ cfg (Q, c)).run gs) →
      Fig8CapInv q m gs' ∧ ∀ t' i' pm', u = some (RecvResult.accepted t' i' pm') → t' + m ≤ q + 1 := by
  intro fig; have hfg0 := hfg.mono (Nat.le_succ m)
  refine ⟨?_, fun u gs' hmem => ?_⟩
  · unfold CryptoGames.SM.injectImpl; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hw : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3)) = true
    · simp only [hw, ↓reduceIte]
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      rcases hrcv : fig.receive (gs.st Q) c with _ | ⟨st', t', i', m'⟩
      · rfl
      · obtain ⟨ht'_le, _⟩ := lFig8_receive_tcur_le C codec Dh encPt encT idOf lam (gs.st Q) st' c t' i' m' hrcv
        have ht'_q : t' ≤ q + 1 := by have := hfg.htcur Q; omega
        have h1 : ¬ (QEP₁ + 1 < t') := by omega
        have h2 : ¬ (QEP₂ + 1 < t') := by omega
        simp only [h1, h2, ↓reduceIte]
  · unfold CryptoGames.SM.injectImpl at hmem
    by_cases hw : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3)) = true
    · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩; exact ⟨hfg0, fun _ _ _ hu => by cases hu⟩
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
      rcases hrcv : fig.receive (gs.st Q) c with _ | ⟨st', t', i', m'⟩
      · simp only [hrcv, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩; exact ⟨hfg0, fun _ _ _ hu => by cases hu⟩
      · obtain ⟨ht'_le, _⟩ := lFig8_receive_tcur_le C codec Dh encPt encT idOf lam (gs.st Q) st' c t' i' m' hrcv
        have ht'_m : t' + m ≤ q + 1 := by have := hfg.htcur Q; omega
        have h1 : ¬ (QEP₁ + 1 < t') := by omega
        simp only [hrcv, h1, ↓reduceIte] at hmem
        by_cases htriv : gs.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨hu, rfl⟩
          refine ⟨fig8CapInv_accept C codec Dh encPt encT idOf lam q m gs Q c st' t' i' m' ⟨Q.other, t', i'⟩ ht'_m hfg hrcv, fun t₀ i₀ pm₀ hu' => ?_⟩
          rw [hu] at hu'; cases hu'; exact ht'_m
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;> simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;> rcases hmem with ⟨rfl, rfl⟩
          · exact ⟨hfg0.withWin true, fun _ _ _ hu => by cases hu⟩
          · exact ⟨hfg0, fun _ _ _ hu => by cases hu⟩

private theorem corrImpl_inv {Pt : Type} {ℓ : ℕ}
    (q m : ℕ) (Q : Party) (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    ∀ u gs', (u, gs') ∈ support ((CryptoGames.SM.corrImpl Q).run gs) → Fig8CapInv q m gs' := by
  intro u gs' hmem
  have hfg0 := hfg.mono (Nat.le_succ m)
  unfold CryptoGames.SM.corrImpl at hmem
  by_cases hw : (gs.win || !(gs.corrAllowed Q)) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hfg0
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact ⟨hfg0.hep, hfg0.htrans, hfg0.htcur⟩

private theorem isQueryBoundP_inr_of_makesAtMostQueries {St Msg Coins C : Type}
    {oa : CryptoGames.SM.Adversary St Msg Coins C} {q : ℕ}
    (hq : CryptoGames.SM.MakesAtMostQueries oa q) :
    oa.IsQueryBoundP (fun x => x.isRight = true) q := by
  unfold CryptoGames.SM.MakesAtMostQueries at hq
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr (by rintro (_ | _) <;> simp) hq

/-- `SM.run` on `lFig8` is invariant in the epoch cap `QEP` whenever `q + 1 ≤ QEP₁`, `q + 1 ≤ QEP₂`,
and `oa` makes at most `q` Fig. 8 queries. -/
theorem sm_run_lFig8_qep_eq {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q QEP₁ QEP₂ : ℕ) (hQ₁ : q + 1 ≤ QEP₁) (hQ₂ : q + 1 ≤ QEP₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    (oa : CryptoGames.SM.Adversary (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : CryptoGames.SM.MakesAtMostQueries oa q) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam
    CryptoGames.SM.run fig 3 QEP₁ cfg b oa = CryptoGames.SM.run fig 3 QEP₂ cfg b oa := by
  intro fig
  unfold CryptoGames.SM.run
  refine bind_congr fun k => ?_
  change (simulateQ (fig8RunImpl fig QEP₁ cfg) oa).run (CryptoGames.SM.initState fig k b) =
    (simulateQ (fig8RunImpl fig QEP₂ cfg) oa).run (CryptoGames.SM.initState fig k b)
  suffices h : ∀ {α : Type} (mx : Fig8Comp Pt ℓ α) (m : ℕ),
      mx.IsQueryBoundP (fun x => x.isRight = true) m →
      ∀ gs : Fig8G Pt ℓ, Fig8CapInv q m gs →
      (simulateQ (fig8RunImpl fig QEP₁ cfg) mx).run gs =
      (simulateQ (fig8RunImpl fig QEP₂ cfg) mx).run gs by
    exact h oa q (isQueryBoundP_inr_of_makesAtMostQueries hq) _
      (fig8CapInv_init C codec Dh encPt encT idOf lam q k b)
  intro α mx
  induction mx using OracleComp.inductionOn with
  | pure a => intros; rfl
  | query_bind qry cont ih =>
    intro m hm gs hfg
    have hm' := (isQueryBoundP_query_bind_iff _ qry cont m).mp hm
    rw [simulateQ_query_bind, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rcases qry with n | t
    · change ((query (spec := unifSpec) n >>= fun u => pure (u, gs)) >>= fun p =>
          (simulateQ (fig8RunImpl fig QEP₁ cfg) (cont p.1)).run p.2) =
        ((query (spec := unifSpec) n >>= fun u => pure (u, gs)) >>= fun p =>
          (simulateQ (fig8RunImpl fig QEP₂ cfg) (cont p.1)).run p.2)
      rw [bind_assoc, bind_assoc]
      refine bind_congr fun u => ?_
      rw [pure_bind, pure_bind]
      exact ih u m (by simpa using hm'.2 u) gs hfg
    · rcases m with _ | m'
      · exfalso; simp at hm'
      rcases t with ((((⟨Q, msg, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
      · obtain ⟨hEq, hInv⟩ := transmitImpl_qep_eq_and_inv C codec Dh encPt encT idOf lam
          q m' QEP₁ QEP₂ hQ₁ hQ₂ Q msg rc gs hfg
        change (CryptoGames.SM.transmitImpl fig 3 QEP₁ (Q, msg, rc)).run gs >>= _ =
          (CryptoGames.SM.transmitImpl fig 3 QEP₂ (Q, msg, rc)).run gs >>= _
        rw [hEq]
        exact bind_congr_of_forall_mem_support _ fun x hx =>
          ih x.1 m' (by simpa using hm'.2 x.1) x.2 (hInv x.1 x.2 (by rw [hEq]; exact hx))
      · obtain ⟨hEq, hInv⟩ := challImpl_qep_eq_and_inv C codec Dh encPt encT idOf lam
          q m' QEP₁ QEP₂ hQ₁ hQ₂ cfg Q m₀ m₁ rc gs hfg
        change (CryptoGames.SM.challImpl fig 3 QEP₁ cfg (Q, m₀, m₁, rc)).run gs >>= _ =
          (CryptoGames.SM.challImpl fig 3 QEP₂ cfg (Q, m₀, m₁, rc)).run gs >>= _
        rw [hEq]
        exact bind_congr_of_forall_mem_support _ fun x hx =>
          ih x.1 m' (by simpa using hm'.2 x.1) x.2 (hInv x.1 x.2 (by rw [hEq]; exact hx))
      · have hInv := deliverImpl_inv C codec Dh encPt encT idOf lam q m' cfg Q c gs hfg
        exact bind_congr_of_forall_mem_support _ fun x hx =>
          ih x.1 m' (by simpa using hm'.2 x.1) x.2 (hInv x.1 x.2 hx).1
      · obtain ⟨hEq, hInv⟩ := injectImpl_qep_eq_and_inv C codec Dh encPt encT idOf lam
          q m' QEP₁ QEP₂ hQ₁ hQ₂ cfg Q c gs hfg
        change (CryptoGames.SM.injectImpl fig 3 QEP₁ cfg (Q, c)).run gs >>= _ =
          (CryptoGames.SM.injectImpl fig 3 QEP₂ cfg (Q, c)).run gs >>= _
        rw [hEq]
        exact bind_congr_of_forall_mem_support _ fun x hx =>
          ih x.1 m' (by simpa using hm'.2 x.1) x.2 (hInv x.1 x.2 (by rw [hEq]; exact hx)).1
      · have hInv := corrImpl_inv q m' Q gs hfg
        exact bind_congr_of_forall_mem_support _ fun x hx =>
          ih x.1 m' (by simpa using hm'.2 x.1) x.2 (hInv x.1 x.2 hx)

/-! ## Simulator epoch-cap invariance -/

private structure SimBaseCapInv {PQ Pt : Type} {ℓ : ℕ} (q m : ℕ) (s : SimState PQ Pt ℓ) : Prop where
  hep : ∀ Q : Party, s.mir.epoch Q + m ≤ q + 1
  htrans : ∀ r ∈ s.mir.trans, r.pos.epoch + m ≤ q + 1

private theorem SimBaseCapInv.mono {PQ Pt : Type} {ℓ : ℕ} {q m₁ m₂ : ℕ} {s : SimState PQ Pt ℓ}
    (hle : m₁ ≤ m₂) (h : SimBaseCapInv q m₂ s) : SimBaseCapInv q m₁ s where
  hep Q := by have := h.hep Q; omega
  htrans r hr := by have := h.htrans r hr; omega

private abbrev SimCCapInv {PQ Pt : Type} {ℓ : ℕ} (q m : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) : Prop :=
  SimBaseCapInv q m sC.base

private theorem simCCapInv_init {PQ Pt : Type} {ℓ : ℕ} (q : ℕ) (pqA pqB : PQ) :
    SimCCapInv q q (initSimC (Pt := Pt) (ℓ := ℓ) pqA pqB) where
  hep Q := by dsimp [initSimC, initSim]; omega
  htrans _ hr := by simp [initSimC, initSim] at hr

private theorem fig8RunImpl_lift_unif {Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (mx : ProbComp α) (gs : Fig8G Pt ℓ) :
    ∀ u gs', (u, gs') ∈ support
        ((simulateQ (fig8RunImpl fig QEP cfg) (liftM mx : Fig8Comp Pt ℓ α)).run gs) →
      gs' = gs := by
  intro u gs' hmem
  rw [simulateQ_fig8RunImpl_liftProb] at hmem
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, _, _, rfl⟩; rfl

private theorem onAccept_qep_eq_of_le {PQ Pt : Type} {ℓ : ℕ}
    (qep₁ qep₂ : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (h₁ : t ≤ qep₁ + 1) (h₂ : t ≤ qep₂ + 1) :
    onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep₁) Q w isDel t i m ci? T pq' =
    onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep₂) Q w isDel t i m ci? T pq' := by
  funext s; unfold onAccept
  have h1 : ¬ (qep₁ + 1 < t) := by omega
  have h2 : ¬ (qep₂ + 1 < t) := by omega
  cases isDel <;> simp only [h1, h2, ↓reduceIte]

private theorem onAccept_true_qep_eq {PQ Pt : Type} {ℓ : ℕ}
    (qep₁ qep₂ : ℕ) (Q : Party) (w : List (BitVec 8)) (t i : ℕ) (m : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) :
    onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep₁) Q w true t i m ci? T pq' =
    onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep₂) Q w true t i m ci? T pq' := by
  funext s; unfold onAccept; simp only [↓reduceIte]

private theorem onAccept_simBaseCapInv {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (q m qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (t i : ℕ) (msg : Plain ℓ)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) (hs : SimBaseCapInv q m s)
    (ht : ¬ isDel → t + m ≤ q + 1) (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q m gs) :
    ∀ p gs', (p, gs') ∈ support ((simulateQ (fig8RunImpl fig QEP cfg)
        ((onAccept (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (qep := qep)
          Q w isDel t i msg ci? T pq').run s)).run gs) →
      SimBaseCapInv q m p.2 ∧ Fig8CapInv q m gs' := by
  intro p gs' hmem
  unfold onAccept at hmem
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    have htm := ht (by decide)
    split_ifs at hmem with hcap htriv
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs, hfg⟩
    · simp only [CryptoGames.Ratchet.LibsignalSim.putS, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨_, rfl⟩, rfl⟩
      refine ⟨⟨fun R => ?_, fun r hr => ?_⟩, hfg⟩
      · dsimp only [GameState.accept, GameState.delete]
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self]; have := hs.hep R; omega
        · simp only [Function.update_of_ne hR]; exact hs.hep R
      · dsimp only [GameState.accept, GameState.delete] at hr
        exact hs.htrans r (List.mem_of_mem_filter hr)
    · simp only [CryptoGames.Ratchet.LibsignalSim.putS, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨⟨hs.hep, hs.htrans⟩, hfg⟩
  · simp only [↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hin : s.mir.inTransit Q.other w with _ | r
    · simp only [hin, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs, hfg⟩
    · simp only [hin, CryptoGames.Ratchet.LibsignalSim.putS, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨_, rfl⟩, rfl⟩
      have hrep := hs.htrans r (List.mem_of_find?_eq_some hin)
      refine ⟨⟨fun R => ?_, fun r' hr' => ?_⟩, hfg⟩
      · dsimp only [GameState.accept, GameState.delete]
        by_cases hR : R = Q
        · subst hR; simp only [Function.update_self]; have := hs.hep R; omega
        · simp only [Function.update_of_ne hR]; exact hs.hep R
      · dsimp only [GameState.accept, GameState.delete] at hr'
        exact hs.htrans r' (List.mem_of_mem_filter hr')

private theorem simSend_qep_eq {PQ PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (qep₁ qep₂ : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (r : Option PQC) (s : SimState PQ Pt ℓ)
    (h₁ : s.mir.epoch Q + 1 ≤ qep₁) (h₂ : s.mir.epoch Q + 1 ≤ qep₂) :
    (simSend (P := P) (qep := qep₁) Q m₀ chal r).run s =
    (simSend (P := P) (qep := qep₂) Q m₀ chal r).run s := by
  unfold simSend; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [epMgmt_eq_of_epoch_lt s.mir 3 qep₁ qep₂ Q r.isSome h₁ h₂]

private theorem simSendCoins_mem {PQC Pt α : Type} [DecidableEq Pt] [SampleableType PQC] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    {PQ : Type} (r : Option PQC)
    (k : PQC → Option (BitVec 256) → StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (s : SimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) {p : α × SimState PQ Pt ℓ} {gs' : Fig8G Pt ℓ}
    (hmem : (p, gs') ∈ support ((simulateQ (fig8RunImpl fig QEP cfg)
      ((do
        let rq ← match r with | some rq => pure rq | none => CryptoGames.Ratchet.LibsignalSim.coin PQC
        let rc : Option (BitVec 256) ← match r with
          | some _ => some <$> CryptoGames.Ratchet.LibsignalSim.coin (BitVec 256)
          | none => pure none
        k rq rc).run s)).run gs)) :
    ∃ rq rc, (p, gs') ∈ support ((simulateQ (fig8RunImpl fig QEP cfg) ((k rq rc).run s)).run gs) := by
  cases r with
  | some rq₀ =>
    simp only [StateT.run_bind, CryptoGames.Ratchet.LibsignalSim.coin,
      CryptoGames.Ratchet.LibsignalSim.liftQ, StateT.run_lift, pure_bind, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, simulateQ_bind, support_bind, Set.mem_iUnion] at hmem
    rcases hmem with ⟨⟨rc₀, gs₁⟩, hrc, hcont⟩
    cases fig8RunImpl_lift_unif fig QEP cfg ($ᵗ BitVec 256) gs rc₀ gs₁ hrc
    exact ⟨rq₀, some rc₀, hcont⟩
  | none =>
    simp only [StateT.run_bind, CryptoGames.Ratchet.LibsignalSim.coin,
      CryptoGames.Ratchet.LibsignalSim.liftQ, StateT.run_lift, pure_bind, bind_assoc,
      simulateQ_bind, support_bind, Set.mem_iUnion] at hmem
    rcases hmem with ⟨⟨rq₀, gs₁⟩, hrq, hcont⟩
    cases fig8RunImpl_lift_unif fig QEP cfg ($ᵗ PQC) gs rq₀ gs₁ hrq
    exact ⟨rq₀, none, hcont⟩

private theorem simulateQ_fig8RunImpl_transmitQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (msg : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8RunImpl fig QEP cfg) (CryptoGames.SM.transmitQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q msg rc)).run gs =
      (CryptoGames.SM.transmitImpl fig 3 QEP (Q, msg, rc)).run gs := by
  simp only [CryptoGames.SM.transmitQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8RunImpl_challQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256)) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8RunImpl fig QEP cfg) (CryptoGames.SM.challQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q m₀ m₁ rc)).run gs =
      (CryptoGames.SM.challImpl fig 3 QEP cfg (Q, m₀, m₁, rc)).run gs := by
  simp only [CryptoGames.SM.challQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8RunImpl_deliverQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8RunImpl fig QEP cfg) (CryptoGames.SM.deliverQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c)).run gs =
      (CryptoGames.SM.deliverImpl fig cfg (Q, c)).run gs := by
  simp only [CryptoGames.SM.deliverQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8RunImpl_injectQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (Q : Party) (c : Fig8C Pt) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8RunImpl fig QEP cfg) (CryptoGames.SM.injectQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q c)).run gs =
      (CryptoGames.SM.injectImpl fig 3 QEP cfg (Q, c)).run gs := by
  simp only [CryptoGames.SM.injectQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]; rfl

private theorem simulateQ_fig8RunImpl_corrQuery {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (Q : Party) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8RunImpl fig QEP cfg) (CryptoGames.SM.corrQuery (St := Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)).run gs = (CryptoGames.SM.corrImpl Q).run gs := by
  simp only [CryptoGames.SM.corrQuery, query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]; rfl

private theorem simSend_inv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (q m QEP qep : ℕ) (hQ : q + 1 ≤ QEP)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (s : SimState PQ Pt ℓ) (hs : SimBaseCapInv q (m + 1) s) (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ∀ p gs', (p, gs') ∈ support ((simulateQ (fig8RunImpl fig QEP cfg)
        ((simSend (P := P) (qep := qep) Q m₀ chal r).run s)).run gs) →
      SimBaseCapInv q m p.2 ∧ Fig8CapInv q m gs' := by
  intro fig p gs' hmem
  have hs0 := hs.mono (Nat.le_succ m); have hfg0 := hfg.mono (Nat.le_succ m)
  unfold simSend at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hw : (s.mir.win || !(CryptoGames.SM.noBobSendInEpoch0 s.mir Q)) = true
  · simp only [hw, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs0, hfg0⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hmem
    rcases hep : s.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs0, hfg0⟩
    · simp only [hep] at hmem
      obtain ⟨h_ep₁, h_tr₁, _⟩ := epMgmt_epoch_trans' s.mir s₁ 3 qep Q r.isSome hep
      have hs₁_ep : ∀ R, s₁.epoch R + m ≤ q + 1 := fun R => by have := h_ep₁ R; have := hs.hep R; omega
      by_cases hsc : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hsc, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs0, hfg0⟩
      · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hmem
        obtain ⟨rq, rc, hmem'⟩ := simSendCoins_mem fig QEP cfg r _ s gs hmem
        rcases hmk : CryptoGames.Ratchet.LibsignalSim.mkPub (P := P) s Q rq
            (if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q) with
            _ | ⟨pq', pub⟩ <;> simp only [hmk] at hmem'
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem'
          rcases hmem' with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs0, hfg0⟩
        · rcases chal with _ | m₁
          · simp only [StateT.run_bind, simulateQ_bind, support_bind, Set.mem_iUnion] at hmem'
            rcases hmem' with ⟨⟨⟨res, s_mid⟩, gs_mid⟩, hqmem, hcont⟩
            simp only [CryptoGames.Ratchet.LibsignalSim.liftQ, StateT.run_lift, simulateQ_bind, StateT.run_bind, simulateQ_fig8RunImpl_transmitQuery, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hqmem
            rcases hqmem with ⟨⟨u, gs_m⟩, humem, ⟨rfl, rfl⟩, rfl⟩
            have hfg_mid := (transmitImpl_qep_eq_and_inv P.C P.codec Dh encPt encT idOf lam q m QEP QEP hQ hQ Q (pub, m₀) rc gs hfg).2 _ _ humem
            rcases res with _ | c
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
              rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs0, hfg_mid⟩
            · simp only [CryptoGames.Ratchet.LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
              rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; refine ⟨⟨fun R => hs₁_ep R, fun rec0 hrec0 => ?_⟩, hfg_mid⟩
              rcases List.mem_cons.mp hrec0 with rfl | hrec0'; · exact hs₁_ep Q
              rw [h_tr₁] at hrec0'; exact hs0.htrans rec0 hrec0'
          · simp only [StateT.run_bind, simulateQ_bind, support_bind, Set.mem_iUnion] at hmem'
            rcases hmem' with ⟨⟨⟨res, s_mid⟩, gs_mid⟩, hqmem, hcont⟩
            simp only [CryptoGames.Ratchet.LibsignalSim.liftQ, StateT.run_lift, simulateQ_bind, StateT.run_bind, simulateQ_fig8RunImpl_challQuery, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hqmem
            rcases hqmem with ⟨⟨u, gs_m⟩, humem, ⟨rfl, rfl⟩, rfl⟩
            have hfg_mid := (challImpl_qep_eq_and_inv P.C P.codec Dh encPt encT idOf lam q m QEP QEP hQ hQ cfg Q (pub, m₀) (pub, m₁) rc gs hfg).2 _ _ humem
            rcases res with _ | c
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
              rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs0, hfg_mid⟩
            · simp only [CryptoGames.Ratchet.LibsignalSim.putS, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
              rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; refine ⟨⟨fun R => hs₁_ep R, fun rec0 hrec0 => ?_⟩, hfg_mid⟩
              rcases List.mem_cons.mp hrec0 with rfl | hrec0'; · exact hs₁_ep Q
              rw [h_tr₁] at hrec0'; exact hs0.htrans rec0 hrec0'

private theorem runOnBaseState_idHook_run {PQ Pt α : Type} {ℓ : ℕ}
    (m : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (runOnBaseState (H := idHook) m).run sC = (m.run sC.base >>= fun p => pure (p.1, { sC with base := p.2 })) := rfl

private theorem liftC_idHook_run {PQ Pt α : Type} {ℓ : ℕ} (x : Fig8Comp Pt ℓ α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (liftC (PQ := PQ) (H := idHook) x).run sC = (x >>= fun a => pure (a, sC)) := rfl

private abbrev runStepC {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (act : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) :
    ProbComp ((α × LibsignalToModularSchemeSimState PQ Pt ℓ) × Fig8G Pt ℓ) :=
  (simulateQ (fig8RunImpl fig QEP cfg) (act.run sC)).run gs

private structure StepRunEqAndInv {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (q m QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (r₁ r₂ : Fig8Comp Pt ℓ (α × LibsignalToModularSchemeSimState PQ Pt ℓ)) (gs : Fig8G Pt ℓ) : Prop where
  heq : (simulateQ (fig8RunImpl fig QEP cfg) r₁).run gs = (simulateQ (fig8RunImpl fig QEP cfg) r₂).run gs
  hinv : ∀ p gs', (p, gs') ∈ support ((simulateQ (fig8RunImpl fig QEP cfg) r₁).run gs) → SimCCapInv q m p.2 ∧ Fig8CapInv q m gs'

private abbrev StepCEqAndInv {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (q m QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (act₁ act₂ : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) : Prop :=
  StepRunEqAndInv fig q m QEP cfg (act₁.run sC) (act₂.run sC) gs

private theorem stepRunEqAndInv_pure {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (q m QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (a : α) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (hsC : SimCCapInv q m sC) (hfg : Fig8CapInv q m gs) :
    StepRunEqAndInv fig q m QEP cfg (pure (a, sC)) (pure (a, sC)) gs := by
  refine ⟨rfl, fun p gs' hmem => ?_⟩
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hsC, hfg⟩

private theorem stepCEqAndInv_guardC {PQ Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (q m QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (act₁ act₂ : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (hsC : SimCCapInv q (m + 1) sC) (hfg : Fig8CapInv q (m + 1) gs)
    (h : sC.base.stopped = false → StepCEqAndInv fig q m QEP cfg act₁ act₂ sC gs) :
    StepCEqAndInv fig q m QEP cfg (guardC act₁) (guardC act₂) sC gs := by
  unfold StepCEqAndInv guardC; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hst : sC.base.stopped
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact h hst
  · simp only [↓reduceIte, StateT.run_pure]
    exact stepRunEqAndInv_pure fig q m QEP cfg none sC gs (hsC.mono (Nat.le_succ m)) (hfg.mono (Nat.le_succ m))

private theorem simSendC_stepCEqAndInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP qep₁ qep₂ : ℕ) (hQ : q + 1 ≤ QEP) (hq₁ : q + 1 ≤ qep₁) (hq₂ : q + 1 ≤ qep₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hsC : SimCCapInv q (m + 1) sC)
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    StepCEqAndInv fig q m QEP cfg
      (simSendC (P := P) (qep := qep₁) (fig := fig) (H := idHook) Q m₀ chal r)
      (simSendC (P := P) (qep := qep₂) (fig := fig) (H := idHook) Q m₀ chal r) sC gs := by
  intro fig
  have hep_q : sC.base.mir.epoch Q + 1 ≤ q + 1 := by have := hsC.hep Q; omega
  have hRunEq : (simSendC (P := P) (qep := qep₁) (fig := fig) (H := idHook) Q m₀ chal r).run sC =
      (simSendC (P := P) (qep := qep₂) (fig := fig) (H := idHook) Q m₀ chal r).run sC := by
    unfold simSendC; simp only [StateT.run_bind, runOnBaseState_idHook_run]
    rw [simSend_qep_eq P qep₁ qep₂ Q m₀ chal r sC.base (hep_q.trans hq₁) (hep_q.trans hq₂)]
  refine ⟨by rw [hRunEq], fun p gs' hmem => ?_⟩
  unfold simSendC at hmem
  simp only [StateT.run_bind, runOnBaseState_idHook_run, bind_assoc, pure_bind,
    simulateQ_bind, support_bind, Set.mem_iUnion] at hmem
  rcases hmem with ⟨⟨⟨res, s'⟩, gs_mid⟩, hsend, hcont⟩
  obtain ⟨hs', hfg_mid⟩ := simSend_inv P Dh encPt encT idOf lam q m QEP qep₁ hQ cfg Q m₀ chal r
    sC.base hsC gs hfg (res, s') gs_mid hsend
  rcases res with _ | w
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
    rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs', hfg_mid⟩
  · simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind,
      simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
    rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hs', hfg_mid⟩

private theorem resyncC_stepCEqAndInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP qep₁ qep₂ : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hsC : SimCCapInv q (m + 1) sC)
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam; let fs := lFS C codec ℓ encT idOf 25000
    StepCEqAndInv fig q m QEP cfg
      (resyncC (qep := qep₁) (fig := fig) (fs := fs) (H := idHook) Q w ci? T pq' c r)
      (resyncC (qep := qep₂) (fig := fig) (fs := fs) (H := idHook) Q w ci? T pq' c r) sC gs := by
  intro fig fs
  have hRunEq : (resyncC (qep := qep₁) (fig := fig) (fs := fs) (H := idHook) Q w ci? T pq' c r).run sC =
      (resyncC (qep := qep₂) (fig := fig) (fs := fs) (H := idHook) Q w ci? T pq' c r).run sC := by
    unfold resyncC; rcases r with _ | ⟨t, i, pm⟩
    · rfl
    · simp only [onAccept_true_qep_eq qep₁ qep₂ Q w t i pm.2 ci? T pq']
  refine ⟨by rw [hRunEq], fun p gs' hmem => ?_⟩
  have hsC0 := hsC.mono (Nat.le_succ m); have hfg0 := hfg.mono (Nat.le_succ m)
  unfold resyncC at hmem; rcases r with _ | ⟨t, i, pm⟩
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hsC0, hfg0⟩
  · simp only [StateT.run_bind, liftC_idHook_run, bind_assoc, pure_bind, simulateQ_bind, simulateQ_fig8RunImpl_deliverQuery, support_bind, Set.mem_iUnion] at hmem
    rcases hmem with ⟨⟨res, gs_mid⟩, hdel, hcont⟩
    have hfg_mid := (deliverImpl_inv C codec Dh encPt encT idOf lam q m cfg Q c gs hfg res gs_mid hdel).1
    cases res with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
      rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hsC0, hfg_mid⟩
    | some rr =>
      cases rr with
      | rejected =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
        rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hsC0, hfg_mid⟩
      | accepted t' i' pm' =>
        simp only [StateT.run_bind, StateT.run_modify, runOnBaseState_idHook_run, pure_bind, simulateQ_bind, support_bind, Set.mem_iUnion] at hcont
        rcases hcont with ⟨⟨⟨u, s'⟩, _⟩, hacc, hfin⟩
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
        rcases hfin with ⟨⟨_, rfl⟩, rfl⟩
        exact onAccept_simBaseCapInv fig QEP cfg q m qep₁ Q w true t i pm.2 ci? T pq' sC.base hsC0 (fun h => absurd rfl h) gs_mid hfg_mid (u, s') _ hacc

private theorem fwd_inv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP : ℕ) (hQ : q + 1 ≤ QEP) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (c' : Fig8C Pt) (s : SimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam
    ∀ p gs₁, (p, gs₁) ∈ support ((simulateQ (fig8RunImpl fig QEP cfg) ((fwd Q c').run s)).run gs) →
      p.2 = s ∧ Fig8CapInv q m gs₁ ∧ (∀ t' i' pm', p.1 = some (RecvResult.accepted t' i' pm') → t' + m ≤ q + 1) := by
  intro fig p gs₁ hmem; unfold fwd at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  split_ifs at hmem
  · simp only [CryptoGames.Ratchet.LibsignalSim.liftQ, StateT.run_lift, simulateQ_bind, StateT.run_bind, simulateQ_fig8RunImpl_deliverQuery, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨res, gs_m⟩, hdel, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, deliverImpl_inv C codec Dh encPt encT idOf lam q m cfg Q c' gs hfg _ _ hdel⟩
  · simp only [CryptoGames.Ratchet.LibsignalSim.liftQ, StateT.run_lift, simulateQ_bind, StateT.run_bind, simulateQ_fig8RunImpl_injectQuery, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨res, gs_m⟩, hinj, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, (injectImpl_qep_eq_and_inv C codec Dh encPt encT idOf lam q m QEP QEP hQ hQ cfg Q c' gs hfg).2 _ _ hinj⟩

private theorem fwdAnswerC_stepCEqAndInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP qep₁ qep₂ : ℕ) (hQ : q + 1 ≤ QEP) (hq₁ : q + 1 ≤ qep₁) (hq₂ : q + 1 ≤ qep₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hsC : SimCCapInv q (m + 1) sC)
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam; let fs := lFS C codec ℓ encT idOf 25000
    StepCEqAndInv fig q m QEP cfg
      (fwdAnswerC (qep := qep₁) (fig := fig) (fs := fs) (H := idHook) Q w isDel ci? T pq' c')
      (fwdAnswerC (qep := qep₂) (fig := fig) (fs := fs) (H := idHook) Q w isDel ci? T pq' c') sC gs := by
  intro fig fs; have hsC0 := hsC.mono (Nat.le_succ m)
  refine ⟨?_, fun ⟨ans, sC_out⟩ gs' hmem => ?_⟩
  · unfold fwdAnswerC; simp only [StateT.run_bind, runOnBaseState_idHook_run, bind_assoc, pure_bind, simulateQ_bind]
    refine bind_congr_of_forall_mem_support _ fun ⟨⟨res, s₁⟩, gs₁⟩ hmem => ?_
    obtain ⟨rfl, _, hacc_t⟩ := fwd_inv C codec Dh encPt encT idOf lam q m QEP hQ cfg Q c' sC.base gs hfg (res, s₁) gs₁ hmem
    cases res with
    | none => rfl
    | some rr =>
      cases rr with
      | rejected => rfl
      | accepted t' i' pm' =>
        have ht'_m := hacc_t t' i' pm' rfl
        have h1 : t' ≤ qep₁ + 1 := by omega
        have h2 : t' ≤ qep₂ + 1 := by omega
        have hon : onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) qep₁ Q w isDel ci? T pq' (some (.accepted t' i' pm')) =
            onAnswer (PQ := PQ) (Pt := Pt) (ℓ := ℓ) qep₂ Q w isDel ci? T pq' (some (.accepted t' i' pm')) := by
          dsimp only [onAnswer]
          exact onAccept_qep_eq_of_le qep₁ qep₂ Q w isDel t' i' ((pm'.map (·.2)).getD default) ci? T pq' h1 h2
        rw [hon]
  · unfold fwdAnswerC at hmem
    simp only [StateT.run_bind, runOnBaseState_idHook_run, bind_assoc, pure_bind, simulateQ_bind, support_bind, Set.mem_iUnion] at hmem
    rcases hmem with ⟨⟨⟨res, s₁⟩, gs₁⟩, hfwd, hcont⟩
    obtain ⟨rfl, hfg₁, hacc_t⟩ := fwd_inv C codec Dh encPt encT idOf lam q m QEP hQ cfg Q c'
      sC.base gs hfg (res, s₁) gs₁ hfwd
    cases res with
    | none =>
      simp only [StateT.run_pure, runOnBaseState_idHook_run, onAnswer, pure_bind, simulateQ_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
      rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hsC0, hfg₁⟩
    | some rr =>
      cases rr with
      | rejected =>
        simp only [StateT.run_pure, runOnBaseState_idHook_run, onAnswer, pure_bind, simulateQ_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
        rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hsC0, hfg₁⟩
      | accepted t' i' pm' =>
        have ht'_m := hacc_t t' i' pm' rfl; dsimp only [onAnswer] at hcont
        set kr := CryptoGames.Ratchet.LibsignalSimC.Kept.recv (fig := fig) (fs := fs) c' (sC.kept Q)
        let msg' : Plain ℓ := (pm'.map (fun x : LibsignalMsgPublicPart × Plain ℓ => x.2)).getD default
        have hstep_run : ((do
            modify fun sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ =>
              { sC₀ with kept := Function.update sC₀.kept Q (CryptoGames.Ratchet.LibsignalSimC.Kept.recv (fig := fig) (fs := fs) c' (sC₀.kept Q)) }
            runOnBaseState (H := idHook) (onAccept qep₁ Q w isDel t' i' msg' ci? T pq')).run
            { base := sC.base, kept := sC.kept, sent := sC.sent, snaps := sC.snaps }) =
          ((onAccept qep₁ Q w isDel t' i' msg' ci? T pq').run sC.base >>= fun p =>
            pure (p.1, { base := p.2, kept := Function.update sC.kept Q kr, sent := sC.sent, snaps := sC.snaps })) := rfl
        rw [hstep_run] at hcont
        simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hcont
        rcases hcont with ⟨⟨⟨u, s'⟩, gs₂⟩, hacc, hfin⟩
        have hcap := onAccept_simBaseCapInv fig QEP cfg q m qep₁ Q w isDel t' i' msg' ci? T pq' sC.base hsC0 (fun _ => ht'_m) gs₁ hfg₁ (u, s') gs₂ hacc
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
        rcases hfin with ⟨⟨_, rfl⟩, rfl⟩; exact hcap

private theorem fwdC_stepCEqAndInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP qep₁ qep₂ : ℕ) (hQ : q + 1 ≤ QEP) (hq₁ : q + 1 ≤ qep₁) (hq₂ : q + 1 ≤ qep₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey)
    (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hsC : SimCCapInv q (m + 1) sC)
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam; let fs := lFS P.C P.codec ℓ encT idOf 25000
    StepCEqAndInv fig q m QEP cfg
      (fwdC (P := P) (qep := qep₁) (fig := fig) (fs := fs) (H := idHook) Q w isDel ci? T pq' honestC c')
      (fwdC (P := P) (qep := qep₂) (fig := fig) (fs := fs) (H := idHook) Q w isDel ci? T pq' honestC c') sC gs := by
  intro fig fs; unfold StepCEqAndInv fwdC; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases honestC with _ | c
  · exact fwdAnswerC_stepCEqAndInv P.C P.codec Dh encPt encT idOf lam q m QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w isDel ci? T pq' c' sC hsC gs hfg
  · dsimp only []; split_ifs
    · cases predictReceiveWithSnapshots (fig := fig) (fs := fs) P sC Q w c c' with
      | some r => exact resyncC_stepCEqAndInv P.C P.codec Dh encPt encT idOf lam q m QEP qep₁ qep₂ cfg Q w ci? T pq' c r sC hsC gs hfg
      | none =>
        simp only [StateT.run_bind, idHook, StateT.run_lift, StateT.run_pure, pure_bind]
        exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs (hsC.mono (Nat.le_succ m)) (hfg.mono (Nat.le_succ m))
    · exact fwdAnswerC_stepCEqAndInv P.C P.codec Dh encPt encT idOf lam q m QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w isDel ci? T pq' c' sC hsC gs hfg

private theorem fwdEvictC_stepCEqAndInv {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (C : Crypto) (codec : SignalMessageProtoCodec) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP qep₁ qep₂ : ℕ) (hQ : q + 1 ≤ QEP) (hq₁ : q + 1 ≤ qep₁) (hq₂ : q + 1 ≤ qep₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hsC : SimCCapInv q (m + 1) sC)
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam; let fs := lFS C codec ℓ encT idOf 25000
    StepCEqAndInv fig q m QEP cfg
      (fwdEvictC (qep := qep₁) (fig := fig) (fs := fs) (H := idHook) Q w isDel T pq' c')
      (fwdEvictC (qep := qep₂) (fig := fig) (fs := fs) (H := idHook) Q w isDel T pq' c') sC gs := by
  intro fig fs; unfold StepCEqAndInv fwdEvictC; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_bind, idHook, StateT.run_lift, StateT.run_pure, pure_bind]
    exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs (hsC.mono (Nat.le_succ m)) (hfg.mono (Nat.le_succ m))
  · exact fwdAnswerC_stepCEqAndInv C codec Dh encPt encT idOf lam q m QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w isDel none T pq' c' sC hsC gs hfg

private theorem simRecvC_stepCEqAndInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP qep₁ qep₂ : ℕ) (hQ : q + 1 ≤ QEP) (hq₁ : q + 1 ≤ qep₁) (hq₂ : q + 1 ≤ qep₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hsC : SimCCapInv q (m + 1) sC)
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam; let fs := lFS P.C P.codec ℓ encT idOf 25000
    StepCEqAndInv fig q m QEP cfg
      (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep₁) (fig := fig) (fs := fs) (H := idHook) Q w isDel)
      (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep₂) (fig := fig) (fs := fs) (H := idHook) Q w isDel) sC gs := by
  intro fig fs; have hsC0 := hsC.mono (Nat.le_succ m); have hfg0 := hfg.mono (Nat.le_succ m)
  unfold StepCEqAndInv simRecvC; simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases c1 : sC.base.mir.win = true
  · simp only [c1, ↓reduceIte, StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg none sC gs hsC0 hfg0
  simp only [c1, Bool.false_eq_true, ↓reduceIte]
  by_cases c2 : (isDel && (sC.base.mir.inTransit Q.other w).isNone) = true
  · simp only [c2, ↓reduceIte, StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg none sC gs hsC0 hfg0
  simp only [c2, Bool.false_eq_true, ↓reduceIte]
  by_cases c3 : (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3)
      || !(CryptoGames.Ratchet.LibsignalInst.ratchetKeyAdmissible P.codec decT encT w))) = true
  · simp only [c3, ↓reduceIte, StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg none sC gs hsC0 hfg0
  simp only [c3, Bool.false_eq_true, ↓reduceIte]
  by_cases c4 : w.length < 9
  · simp only [c4, ↓reduceIte, StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
  simp only [c4, ↓reduceIte]
  rcases hparse : (CryptoGames.LibsignalSession.signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
  · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
  · dsimp only []
    by_cases c5 : (!CryptoGames.LibsignalAead.addressCheckPasses h.addresses (P.expectedAddrs Q)) = true
    · simp only [c5, ↓reduceIte, StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
    simp only [c5, Bool.false_eq_true, ↓reduceIte]
    by_cases c6 : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = true
    · simp only [c6, ↓reduceIte, StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
    simp only [c6, Bool.false_eq_true, ↓reduceIte]
    rcases hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet with _ | ⟨pq', salt⟩
    · dsimp only []; simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
    · dsimp only []
      rcases hci : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) with _ | ci <;> simp only [hci]
      · let sC₁ : LibsignalToModularSchemeSimState PQ Pt ℓ := { sC with base := { sC.base with amb := sC.base.amb + 1 } }
        have hsC₁ : SimCCapInv q (m + 1) sC₁ := ⟨hsC.hep, hsC.htrans⟩
        have hsC₁0 : SimCCapInv q m sC₁ := hsC₁.mono (Nat.le_succ m)
        split_ifs
        · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
        · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC₁ gs hsC₁0 hfg0
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; rcases decT h.senderRatchetKey with _ | T
          · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC₁ gs hsC₁0 hfg0
          · exact fwdEvictC_stepCEqAndInv P.C P.codec Dh encPt encT idOf lam q m QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w isDel h.senderRatchetKey pq' _ sC₁ hsC₁ gs hfg
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind]; rcases decT h.senderRatchetKey with _ | T
          · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC₁ gs hsC₁0 hfg0
          · exact fwdC_stepCEqAndInv P Dh encPt encT idOf lam q m QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w isDel none h.senderRatchetKey pq' _ _ sC₁ hsC₁ gs hfg
        · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
        · rcases decT h.senderRatchetKey with _ | T
          · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
          · exact fwdEvictC_stepCEqAndInv P.C P.codec Dh encPt encT idOf lam q m QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w isDel h.senderRatchetKey pq' _ sC hsC gs hfg
        · rcases decT h.senderRatchetKey with _ | T
          · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
          · exact fwdC_stepCEqAndInv P Dh encPt encT idOf lam q m QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w isDel none h.senderRatchetKey pq' _ _ sC hsC gs hfg
      · split_ifs
        · simp only [StateT.run_pure]; exact stepRunEqAndInv_pure fig q m QEP cfg (some RecvResult.rejected) sC gs hsC0 hfg0
        · exact fwdC_stepCEqAndInv P Dh encPt encT idOf lam q m QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w isDel (some ci) h.senderRatchetKey pq' _ _ sC hsC gs hfg

private theorem simCorrC_stepCEqAndInv {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (q m QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (Q : Party) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hsC : SimCCapInv q (m + 1) sC)
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m + 1) gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    StepCEqAndInv fig q m QEP cfg
      (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q)
      (simCorrC (P := P) (encT := encT) (H := idHook) Dh Q) sC gs := by
  intro fig; have hsC0 := hsC.mono (Nat.le_succ m); have hfg0 := hfg.mono (Nat.le_succ m)
  refine ⟨rfl, fun p gs' hmem => ?_⟩
  unfold simCorrC at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases hc : (sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
      CryptoGames.Ratchet.LibsignalSim.inReceiveOnlyEpoch sC.base.mir Q ||
      !(CryptoGames.SM.noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp only [hc, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hsC0, hfg0⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, liftC_idHook_run,
      bind_assoc, pure_bind, simulateQ_bind, simulateQ_fig8RunImpl_corrQuery,
      support_bind, Set.mem_iUnion] at hmem
    rcases hmem with ⟨⟨res, gs_mid⟩, hcorr, hcont⟩
    have hfg_mid := corrImpl_inv q m Q gs hfg res gs_mid hcorr
    rcases res with _ | st
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
      rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨hsC0, hfg_mid⟩
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcont
      rcases hcont with ⟨⟨_, rfl⟩, rfl⟩; exact ⟨⟨hsC0.hep, hsC0.htrans⟩, hfg_mid⟩

private theorem runStepC_bind {PQ Pt α β : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (f : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) β)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) :
    runStepC fig QEP cfg (m >>= f) sC gs =
      (runStepC fig QEP cfg m sC gs >>= fun x => runStepC fig QEP cfg (f x.1.1) x.1.2 x.2) := by
  unfold runStepC; simp only [StateT.run_bind, simulateQ_bind]

private theorem simImplC_inl_runStepC {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (QEP qep : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (n : unifSpec.Domain) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam; let fs := lFS P.C P.codec ℓ encT idOf 25000
    runStepC fig QEP cfg (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs) (H := idHook) Dh (.inl n)) sC gs =
      ((query (spec := unifSpec) n >>= fun v => pure (v, gs)) >>= fun p => pure ((p.1, sC), p.2)) := by
  intro fig fs
  have hinl : simImplC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs) (H := idHook) Dh (.inl n) =
      liftC idHook (query (spec := FSpec' Pt ℓ) (.inl n)) := rfl
  rw [hinl]; unfold runStepC liftC idHook
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]; rfl

private theorem sm_run_eq_fig8RunImpl {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool) (oa : Fig8Comp Pt ℓ Bool) :
    CryptoGames.SM.run fig 3 QEP cfg b oa =
      (($ᵗ (BitVec 256 × BitVec 256)) >>= fun k => (simulateQ (fig8RunImpl fig QEP cfg) oa).run (CryptoGames.SM.initState fig k b)) := rfl

private theorem simImplC_inr_stepCEqAndInv {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (q m' QEP qep₁ qep₂ : ℕ) (hQ : q + 1 ≤ QEP) (hq₁ : q + 1 ≤ qep₁) (hq₂ : q + 1 ≤ qep₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hsC : SimCCapInv q (m' + 1) sC)
    (gs : Fig8G Pt ℓ) (hfg : Fig8CapInv q (m' + 1) gs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam; let fs := lFS P.C P.codec ℓ encT idOf 25000
    StepCEqAndInv fig q m' QEP cfg
      (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep₁) (fig := fig) (fs := fs) (H := idHook) Dh (.inr t))
      (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep₂) (fig := fig) (fs := fs) (H := idHook) Dh (.inr t)) sC gs := by
  intro fig fs
  rcases t with ((((⟨Q, msg, rc⟩ | ⟨Q, m₀, m₁, rc⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact stepCEqAndInv_guardC fig q m' QEP cfg _ _ sC gs hsC hfg fun _ =>
      simSendC_stepCEqAndInv P Dh encPt encT idOf lam q m' QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q msg none rc sC hsC gs hfg
  · exact stepCEqAndInv_guardC fig q m' QEP cfg _ _ sC gs hsC hfg fun _ =>
      simSendC_stepCEqAndInv P Dh encPt encT idOf lam q m' QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q m₀ (some m₁) rc sC hsC gs hfg
  · exact stepCEqAndInv_guardC fig q m' QEP cfg _ _ sC gs hsC hfg fun _ =>
      simRecvC_stepCEqAndInv P Dh encPt encT decT idOf lam q m' QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w true sC hsC gs hfg
  · exact stepCEqAndInv_guardC fig q m' QEP cfg _ _ sC gs hsC hfg fun _ =>
      simRecvC_stepCEqAndInv P Dh encPt encT decT idOf lam q m' QEP qep₁ qep₂ hQ hq₁ hq₂ cfg Q w false sC hsC gs hfg
  · exact stepCEqAndInv_guardC fig q m' QEP cfg _ _ sC gs hsC hfg fun _ =>
      simCorrC_stepCEqAndInv P Dh encPt encT idOf lam q m' QEP cfg Q sC hsC gs hfg

private theorem simulateQ_liftProb_bind_run {Pt α β : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (p : ProbComp α) (f : α → Fig8Comp Pt ℓ β) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8RunImpl fig QEP cfg) ((liftM p : Fig8Comp Pt ℓ α) >>= f)).run gs =
      (p >>= fun a => (simulateQ (fig8RunImpl fig QEP cfg) (f a)).run gs) := by
  rw [simulateQ_bind, StateT.run_bind, simulateQ_fig8RunImpl_liftProb, bind_assoc]; exact bind_congr fun _ => by rw [pure_bind]

private theorem simulateQ_run'_eq_runStepC {PQ Pt α : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ) :
    (simulateQ (fig8RunImpl fig QEP cfg) (m.run' sC)).run gs = (runStepC fig QEP cfg m sC gs >>= fun x => pure (x.1.1, x.2)) := by
  unfold runStepC; simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]

private def isInrQ {α β : Type} : α ⊕ β → Bool | .inl _ => false | .inr _ => true

private theorem isQueryBoundP_isInrQ_of_makesAtMostQueries {St Msg Coins C : Type}
    {oa : CryptoGames.SM.Adversary St Msg Coins C} {q : ℕ} (hq : CryptoGames.SM.MakesAtMostQueries oa q) :
    oa.IsQueryBoundP (fun x => isInrQ x = true) q := by
  unfold CryptoGames.SM.MakesAtMostQueries at hq
  exact CryptoGames.LibsignalSM.Proofs.QueryBounds.isQueryBoundP_congr (by rintro (_ | _) <;> simp [isInrQ]) hq

private theorem runStepC_simulateQ_eq_of_step {PQ PQC Pt α : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (q QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (imp₁ imp₂ : QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ)))
    (hinl : ∀ n sC gs,
      runStepC fig QEP cfg (imp₁ (.inl n)) sC gs = ((query (spec := unifSpec) n >>= fun v => pure (v, gs)) >>= fun p => pure ((p.1, sC), p.2)) ∧
      runStepC fig QEP cfg (imp₂ (.inl n)) sC gs = ((query (spec := unifSpec) n >>= fun v => pure (v, gs)) >>= fun p => pure ((p.1, sC), p.2)))
    (hinr : ∀ m' t sC gs, SimCCapInv q (m' + 1) sC → Fig8CapInv q (m' + 1) gs → StepCEqAndInv fig q m' QEP cfg (imp₁ (.inr t)) (imp₂ (.inr t)) sC gs)
    (mx : OracleComp (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) α)
    (m : ℕ) (hm : mx.IsQueryBoundP (fun x => isInrQ x = true) m)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (gs : Fig8G Pt ℓ)
    (hsC : SimCCapInv q m sC) (hfg : Fig8CapInv q m gs) :
    runStepC fig QEP cfg (simulateQ imp₁ mx) sC gs = runStepC fig QEP cfg (simulateQ imp₂ mx) sC gs := by
  induction mx using OracleComp.inductionOn generalizing m sC gs with
  | pure a => rfl
  | query_bind qry cont ih =>
    have hm' := (isQueryBoundP_query_bind_iff _ qry cont m).mp hm
    rw [simulateQ_query_bind, simulateQ_query_bind]; simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq]
    dsimp only [liftM, monadLift, MonadLiftT.monadLift]; rw [runStepC_bind, runStepC_bind]
    rcases qry with n | t
    · obtain ⟨hi₁, hi₂⟩ := hinl n sC gs; rw [hi₁, hi₂]
      refine bind_congr_of_forall_mem_support _ fun ⟨⟨u, sC'⟩, gs'⟩ hmem => ?_
      rw [bind_assoc] at hmem
      simp only [pure_bind, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨v, _, ⟨⟨rfl, rfl⟩, rfl⟩⟩
      have h0 : isInrQ (Sum.inl n : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) = false := rfl
      exact ih u m (by simpa [h0] using hm'.2 u) sC' gs' hsC hfg
    · rcases m with _ | m'
      · exfalso; simp [isInrQ] at hm'
      obtain ⟨hEq, hInv⟩ := hinr m' t sC gs hsC hfg; dsimp only [runStepC]; rw [hEq]
      refine bind_congr_of_forall_mem_support _ fun ⟨⟨u, sC'⟩, gs'⟩ hx => ?_
      obtain ⟨hsC', hfg'⟩ := hInv (u, sC') gs' (by rw [hEq]; exact hx)
      have h1 : isInrQ (Sum.inr t : (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) = true := rfl
      exact ih u m' (by simpa [h1] using hm'.2 u) sC' gs' hsC' hfg'

private theorem sm_run_simRunCWith_eq_of_imp {PQ PQC Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (QEP : ℕ) (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    (initPQ : BitVec 256 → LibsignalToModularSchemeSimState PQ Pt ℓ)
    (imp₁ imp₂ : QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ)))
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (hEq : ∀ k pqrKey, runStepC fig QEP cfg (simulateQ imp₁ A) (initPQ pqrKey) (CryptoGames.SM.initState fig k b) =
      runStepC fig QEP cfg (simulateQ imp₂ A) (initPQ pqrKey) (CryptoGames.SM.initState fig k b)) :
    CryptoGames.SM.run fig 3 QEP cfg b (((idHook (Pt := Pt) (ℓ := ℓ)).lift
      (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256)) >>=
      fun pqrKey => (simulateQ imp₁ A).run' (initPQ pqrKey)) : Fig8Comp Pt ℓ Bool) =
    CryptoGames.SM.run fig 3 QEP cfg b (((idHook (Pt := Pt) (ℓ := ℓ)).lift
      (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256)) >>=
      fun pqrKey => (simulateQ imp₂ A).run' (initPQ pqrKey)) : Fig8Comp Pt ℓ Bool) := by
  rw [sm_run_eq_fig8RunImpl, sm_run_eq_fig8RunImpl]; refine bind_congr fun k => ?_
  dsimp only [idHook]; rw [simulateQ_liftProb_bind_run, simulateQ_liftProb_bind_run]
  refine bind_congr fun pqrKey => ?_; rw [simulateQ_run'_eq_runStepC, simulateQ_run'_eq_runStepC, hEq k pqrKey]

/-- `Refine.libsignalToModularSchemeSim` has identical `SM.run fig 3 QEP cfg b` distribution at
any two epoch caps `qep₁, qep₂` whenever `q + 1 ≤ QEP`, `q + 1 ≤ qep₁`, `q + 1 ≤ qep₂`, and `A`
makes at most `q` queries. -/
theorem sm_run_libsignalToModularSchemeSim_qep_eq
    {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q QEP qep₁ qep₂ : ℕ) (hQ : q + 1 ≤ QEP) (hq₁ : q + 1 ≤ qep₁) (hq₂ : q + 1 ≤ qep₂)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CryptoGames.SM.run fig 3 QEP cfg b (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep₁ A) =
    CryptoGames.SM.run fig 3 QEP cfg b (libsignalToModularSchemeSim P ℓ Dh encPt encT decT idOf lam qep₂ A) := by
  intro fig
  exact sm_run_simRunCWith_eq_of_imp fig QEP cfg b (fun pqrKey => initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep₁) (fig := fig) (fs := lFS P.C P.codec ℓ encT idOf 25000) (H := idHook) Dh)
    (simImplC (P := P) (encT := encT) (decT := decT) (qep := qep₂) (fig := fig) (fs := lFS P.C P.codec ℓ encT idOf 25000) (H := idHook) Dh)
    A fun k pqrKey => runStepC_simulateQ_eq_of_step fig q QEP cfg _ _
      (fun n sC gs => ⟨simImplC_inl_runStepC P Dh encPt encT decT idOf lam QEP qep₁ cfg n sC gs,
        simImplC_inl_runStepC P Dh encPt encT decT idOf lam QEP qep₂ cfg n sC gs⟩)
      (fun m' t sC gs hsC hfg => simImplC_inr_stepCEqAndInv P Dh encPt encT decT idOf lam q m' QEP qep₁ qep₂ hQ hq₁ hq₂ cfg t sC hsC gs hfg)
      A q (isQueryBoundP_isInrQ_of_makesAtMostQueries hA) _ _ (simCCapInv_init q _ _)
      (fig8CapInv_init P.C P.codec Dh encPt encT idOf lam q k b)

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8QepCap
