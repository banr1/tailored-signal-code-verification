/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECell
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF
import ProofLib.BV.WidthNorm
import VCVio.EvalDist.Monad.Basic

@[expose] public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal
open CryptoVerification.LibsignalSession.HeadlineV1
open CryptoVerification.E2E.Signed
open CryptoGames.SM.Construction.AuthL11
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

namespace CryptoVerification.E2E

section CellClamp

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)

/-- Step-indexed clamp invariant on the cell `GameState` for `m` remaining queries. -/
structure CellGameClampInv (B m : ℕ)
    (gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)) : Prop where
  hmB : m + 3 ≤ B
  htcur : ∀ Q : Party, (gs.st Q).tcur + m + 1 ≤ B
  hvS : ∀ Q : Party, ∀ v, (gs.st Q).vS = some v → v.lastIndex + m + 1 ≤ B

omit [DecidableEq Pt] [Zero Pt] in
theorem CellGameClampInv.mono {B m₁ m₂ : ℕ}
    {gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)}
    (hle : m₁ ≤ m₂) (h : CellGameClampInv B m₂ gs) : CellGameClampInv B m₁ gs where
  hmB := by have := h.hmB; omega
  htcur Q := by have := h.htcur Q; omega
  hvS Q v hv := by have := h.hvS Q v hv; omega

omit [DecidableEq Pt] [Zero Pt] in
theorem CellGameClampInv.withWin {B m : ℕ}
    {gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt)}
    (h : CellGameClampInv B m gs) (w : Bool) :
    CellGameClampInv B m { gs with win := w } :=
  ⟨h.hmB, h.htcur, h.hvS⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem stateT_liftM_probComp_run {σ α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = (p >>= fun a => pure (a, s)) := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem epMgmt_st_eq {St Msg C : Type}
    (s s₁ : GameState St Msg C) (Δ qep : ℕ) (Q : Party) (bad : Bool)
    (h : s.epMgmt Δ qep Q bad = some s₁) :
    s₁.st = s.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> injection h with h <;> subst h <;> rfl

omit [DecidableEq Pt] [SampleableType PQC] in
theorem lFig8_init_bounds (idOf : Party → IdentityKey) (k : Ratchet.RootKey × BitVec 256)
    (b : Bool) (Q : Party) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    ((SM.initState fig k b).st Q).tcur = 0 ∧
    ∀ v, ((SM.initState fig k b).st Q).vS = some v → v.lastIndex = 0 := by
  dsimp only [SM.initState, lFig8, SM.Construction.scheme, SM.Construction.initParty,
    lFS, FSAEAD.fromAEADPRG]
  cases Q <;> refine ⟨rfl, fun v hv => ?_⟩
  · cases hv
  · injection hv with hv; subst hv; rfl

omit [DecidableEq Pt] [SampleableType PQC] in
theorem lFig8_send_bounds (idOf : Party → IdentityKey)
    (st : SimFig8St Pt) (m : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    (fig.send st m coins).1.tcur ≤ st.tcur + 1 ∧
    (fig.send st m coins).2.1.1 ≤ st.tcur + 1 ∧
    (∀ v', (fig.send st m coins).1.vS = some v' →
      v'.lastIndex ≤ 1 ∨ ∃ v, st.vS = some v ∧ v'.lastIndex = v.lastIndex + 1) ∧
    ((fig.send st m coins).2.2.1 ≤ 1 ∨
      ∃ v, st.vS = some v ∧ (fig.send st m coins).2.2.1 = v.lastIndex + 1) := by
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.send]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ↓reduceIte, lFS, FSAEAD.fromAEADPRG]
    refine ⟨le_rfl, le_rfl, fun v' hv' => ?_, Or.inl le_rfl⟩
    injection hv' with hv'; subst hv'
    exact Or.inl le_rfl
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases hv : st.vS with
    | none =>
      refine ⟨Nat.le_add_right _ 1, Nat.le_add_right _ 1, fun v' hv' => ?_,
        Or.inl (Nat.zero_le 1)⟩
      rw [hv] at hv'; cases hv'
    | some v =>
      dsimp only [lFS, FSAEAD.fromAEADPRG]
      refine ⟨Nat.le_add_right _ 1, Nat.le_add_right _ 1, fun v' hv' => ?_, Or.inr ⟨v, rfl, rfl⟩⟩
      injection hv' with hv'; subst hv'
      exact Or.inr ⟨v, rfl, rfl⟩

omit [DecidableEq Pt] [SampleableType PQC] in
theorem lFig8_receive_bounds (idOf : Party → IdentityKey)
    (st st' : SimFig8St Pt) (c : SimFig8C Pt) (t i : ℕ) (m : LibsignalMsgPublicPart × Plain ℓ)
    (h : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c = some (st', t, i, m)) :
    t = c.1.1 ∧ i = c.2.1 ∧ t ≤ st.tcur + 1 ∧ st'.tcur ≤ st.tcur + 1 ∧ st'.vS = st.vS := by
  obtain ⟨rfl, rfl⟩ := lFig8_receive_epoch_index_eq P Dh encPt encT lam idOf st st' c t i m h
  refine ⟨rfl, rfl, ?_⟩
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.receive] at h
  split at h
  · cases h
  · rename_i h1
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at h1
    split at h
    · cases h
    · rename_i s₁ hs₁
      have hs₁_b : s₁.tcur ≤ st.tcur + 1 ∧ s₁.vS = st.vS := by
        split_ifs at hs₁ with heq
        · rcases hc12 : c.1.2 with _ | Tn <;> rw [hc12] at hs₁
          · cases hs₁
          · injection hs₁ with hs₁; subst hs₁
            exact ⟨h1.2, rfl⟩
        · injection hs₁ with hs₁; subst hs₁
          exact ⟨Nat.le_add_right _ 1, rfl⟩
      split at h
      · cases h
      · rename_i v _
        rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c.1 c.2 with
          _ | ⟨v', i', pm'⟩
        · rw [hfs] at h; cases h
        · rw [hfs] at h
          injection h with h
          injection h with hst' _
          subst hst'
          exact ⟨h1.2, hs₁_b.1, hs₁_b.2⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simBaseClampInv_init (B q : ℕ) (pqA pqB : PQ) (hqB : q + 3 ≤ B) :
    SimBaseClampInv B q (initSim (Pt := Pt) (ℓ := ℓ) pqA pqB) where
  hep Q := by dsimp [initSim]; omega
  htrans r hr := by simp [initSim] at hr
  hch Q g hg := by
    cases Q <;> simp [initSim] at hg
    subst hg; dsimp; omega
  hhonest wc hwc := by simp [initSim] at hwc

omit [DecidableEq Pt] [SampleableType PQC] in
theorem cellGameClampInv_init (idOf : Party → IdentityKey) (B q : ℕ)
    (k : Ratchet.RootKey × BitVec 256) (b : Bool) (hqB : q + 3 ≤ B) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CellGameClampInv B q (SM.initState fig k b) where
  hmB := hqB
  htcur Q := by
    rw [(lFig8_init_bounds P Dh encPt encT lam idOf k b Q).1]
    omega
  hvS Q v hv := by
    rw [(lFig8_init_bounds P Dh encPt encT lam idOf k b Q).2 v hv]
    omega

omit [DecidableEq Pt] [SampleableType PQC] in
theorem cellGameClampInv_record (idOf : Party → IdentityKey) (Δ B m qep : ℕ)
    (gs s₁ : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (bad isChall : Bool) (msg : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (hfg : CellGameClampInv B (m + 1) gs)
    (hep : gs.epMgmt Δ qep Q bad = some s₁) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let out := fig.send (s₁.st Q) msg coins
    CellGameClampInv B m
      (s₁.record Δ Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, msg, out.2⟩ isChall) ∧
    out.2.1.1 + m + 1 ≤ B ∧ out.2.2.1 + m + 1 ≤ B := by
  have hst := epMgmt_st_eq gs s₁ Δ qep Q bad hep
  obtain ⟨htcur', hc1, hvS', hc2⟩ := lFig8_send_bounds P Dh encPt encT lam idOf (s₁.st Q) msg coins
  have htQ : (s₁.st Q).tcur + (m + 1) + 1 ≤ B := by rw [hst]; exact hfg.htcur Q
  have hvSQ : ∀ v, (s₁.st Q).vS = some v → v.lastIndex + (m + 1) + 1 ≤ B := by
    rw [hst]; exact hfg.hvS Q
  have hmB := hfg.hmB
  refine ⟨{
    hmB := by omega
    htcur := fun R => by
      dsimp only [GameState.record]
      by_cases hR : R = Q
      · cases hR; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hR, hst]; have := hfg.htcur R; omega
    hvS := fun R v' hv' => by
      dsimp only [GameState.record] at hv'
      by_cases hR : R = Q
      · cases hR; simp only [Function.update_self] at hv'
        rcases hvS' v' hv' with h1 | ⟨v, hv, h2⟩
        · omega
        · have := hvSQ v hv; omega
      · simp only [Function.update_of_ne hR, hst] at hv'
        have := hfg.hvS R v' hv'; omega }, by omega, ?_⟩
  rcases hc2 with h1 | ⟨v, hv, h2⟩
  · omega
  · have := hvSQ v hv; omega

omit [DecidableEq Pt] [SampleableType PQC] in
theorem cellGameClampInv_transmitImpl (idOf : Party → IdentityKey) (Δ B m qep : ℕ)
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (msg : LibsignalMsgPublicPart × Plain ℓ) (rc : Option (BitVec 256))
    (res : Option (SimFig8C Pt))
    (hfg : CellGameClampInv B (m + 1) gs)
    (hmem : (res, gs') ∈ support ((SM.transmitImpl
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Δ qep (Q, msg, rc)).run gs)) :
    CellGameClampInv B m gs' ∧ ∀ c, res = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B := by
  unfold SM.transmitImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftM_probComp_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt Δ qep Q bad with _ | s₁ <;>
      simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hfg.mono (Nat.le_succ m), fun _ hc => by cases hc⟩
    · rcases hmem with ⟨rfl, rfl⟩
      obtain ⟨hfg', hc1, hc2⟩ :=
        cellGameClampInv_record P Dh encPt encT lam idOf Δ B m qep gs s₁ Q bad false msg coins
          hfg hep
      exact ⟨hfg', fun c hc => by injection hc with hc; subst hc; exact ⟨hc1, hc2⟩⟩

omit [DecidableEq Pt] [SampleableType PQC] in
theorem cellGameClampInv_accept (idOf : Party → IdentityKey) (B m : ℕ)
    (gs : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (c : SimFig8C Pt) (st' : SimFig8St Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (pos : SM.Pos)
    (hfg : CellGameClampInv B (m + 1) gs)
    (hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c =
      some (st', t, i, pm)) :
    CellGameClampInv B m (gs.accept Q st' pos) ∧ t + m + 1 ≤ B := by
  obtain ⟨_, _, ht_le, hst'_tcur, hst'_vS⟩ :=
    lFig8_receive_bounds P Dh encPt encT lam idOf (gs.st Q) st' c t i pm hrcv
  have htQ := hfg.htcur Q
  have hmB := hfg.hmB
  refine ⟨{
    hmB := by omega
    htcur := fun R => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hR : R = Q
      · cases hR; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hR]; have := hfg.htcur R; omega
    hvS := fun R v' hv' => by
      dsimp only [GameState.accept, GameState.delete] at hv'
      by_cases hR : R = Q
      · cases hR; simp only [Function.update_self, hst'_vS] at hv'
        have := hfg.hvS Q v' hv'; omega
      · simp only [Function.update_of_ne hR] at hv'
        have := hfg.hvS R v' hv'; omega }, by omega⟩

omit [SampleableType PQC] in
theorem cellGameClampInv_deliverImpl (idOf : Party → IdentityKey) (B m : ℕ)
    (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (c : SimFig8C Pt)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hfg : CellGameClampInv B (m + 1) gs)
    (hmem : (res, gs') ∈ support ((SM.deliverImpl
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) cfg (Q, c)).run gs)) :
    CellGameClampInv B m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
  unfold SM.deliverImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hmem
    rcases htr : gs.inTransit Q.other c with _ | r <;> simp only [htr] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
    · rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
        _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
      · split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          (rcases hmem with ⟨rfl, rfl⟩;
           exact ⟨(hfg.mono (Nat.le_succ m)).withWin _, fun _ _ _ hc => by cases hc⟩)
      · obtain ⟨hfg', ht'⟩ :=
          cellGameClampInv_accept P Dh encPt encT lam idOf B m gs Q c st' t' i' m' r.pos hfg hrcv
        split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          (rcases hmem with ⟨rfl, rfl⟩;
           refine ⟨hfg'.withWin _, fun t i pm hc => ?_⟩;
           injection hc with hc; injection hc with ht _ _; subst ht; exact ht')

omit [SampleableType PQC] in
theorem cellGameClampInv_injectImplCellT (idOf : Party → IdentityKey) (B m qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (c : SimFig8C Pt)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hfg : CellGameClampInv B (m + 1) gs)
    (hmem : (res, gs') ∈ support ((injectImplCellT
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep tL tStar cfg
      (Q, c)).run gs)) :
    CellGameClampInv B m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
  unfold injectImplCellT at hmem
  by_cases hw : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj (cellDelta tL tStar))) =
      true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hmem
    rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
      _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
    · by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hfg.mono (Nat.le_succ m), fun _ _ _ hc => by cases hc⟩
      · simp only [hqep, ↓reduceIte] at hmem
        obtain ⟨hfg', ht'⟩ :=
          cellGameClampInv_accept P Dh encPt encT lam idOf B m gs Q c st' t' i' m'
            ⟨Q.other, t', i'⟩ hfg hrcv
        by_cases htriv : cellTrivialT tL tStar gs ⟨Q.other, t', i'⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          refine ⟨hfg', fun t i pm hc => ?_⟩
          injection hc with hc; injection hc with ht _ _; subst ht; exact ht'
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
            (rcases hmem with ⟨rfl, rfl⟩;
             exact ⟨(hfg.mono (Nat.le_succ m)).withWin _, fun _ _ _ hc => by cases hc⟩)

omit [SampleableType PQC] in
theorem cellGameClampInv_deliverForgeBaseImplCellT (idOf : Party → IdentityKey)
    (B m qep : ℕ) (tL : Option ℕ) (tStar : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ))
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (c c' : SimFig8C Pt)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (hfg : CellGameClampInv B (m + 1) gs)
    (hmem : (res, gs') ∈ support ((deliverForgeBaseImplCellT
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep tL tStar
      SM.Construction.DeliverForge.sameHdrScheme cfg (Q, c, c')).run gs)) :
    CellGameClampInv B m gs' := by
  have hfg0 := hfg.mono (Nat.le_succ m)
  unfold deliverForgeBaseImplCellT at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hfg0
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hmem
    rcases htr : gs.inTransit Q.other c with _ | r <;> simp only [htr] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hfg0
    · by_cases hcnd :
        ((gs.inTransit Q.other c').isSome || gs.comp.contains r.pos ||
          !(SM.Construction.DeliverForge.sameHdrScheme c c')) = true
      · simp only [hcnd, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hfg0
      · simp only [hcnd, Bool.false_eq_true, ↓reduceIte] at hmem
        rcases hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (gs.st Q) c' with
          _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hfg0
        · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hfg0
          · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
            by_cases htriv : cellTrivialT tL tStar gs ⟨Q.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩
              exact (cellGameClampInv_accept P Dh encPt encT lam idOf B m gs Q c' st' t' i'
                m' ⟨Q.other, t', i'⟩ hfg hrcv).1
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              split_ifs at hmem <;>
                simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
                (rcases hmem with ⟨_, rfl⟩; exact hfg0.withWin _)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem _root_.CryptoGames.Ratchet.LibsignalSim.SimBaseClampInv.mono
    {B m₁ m₂ : ℕ} {s : SimState PQ Pt ℓ}
    (hle : m₁ ≤ m₂) (h : SimBaseClampInv B m₂ s) : SimBaseClampInv B m₁ s where
  hep Q := by have := h.hep Q; omega
  htrans r hr := by have := h.htrans r hr; omega
  hch Q g hg := by have := h.hch Q g hg; omega
  hhonest wc hwc := by obtain ⟨h1, h2⟩ := h.hhonest wc hwc; exact ⟨by omega, by omega⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem epMgmt_bounds {St Msg C : Type}
    (s s₁ : GameState St Msg C) (Δ qep : ℕ) (Q : Party) (bad : Bool)
    (h : s.epMgmt Δ qep Q bad = some s₁) :
    (∀ R : Party, s₁.epoch R ≤ s.epoch R + 1) ∧
    s₁.trans = s.trans ∧ s₁.chall = s.chall ∧ s₁.comp = s.comp := by
  unfold GameState.epMgmt at h
  split_ifs at h with h1 h2 h3 h4 <;> injection h with h <;> subst h
  · refine ⟨fun R => ?_, rfl, rfl, rfl⟩
    by_cases hR : R = Q <;> simp [hR, GameState.leak]
  · refine ⟨fun R => ?_, rfl, rfl, rfl⟩
    by_cases hR : R = Q <;> simp [hR]
  · exact ⟨fun _ => Nat.le_add_right _ 1, rfl, rfl, rfl⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem accept_bounds {St Msg C : Type}
    (s : GameState St Msg C) (Q : Party) (st' : St) (pos : SM.Pos) :
    (∀ R : Party, (s.accept Q st' pos).epoch R ≤ max (s.epoch R) pos.epoch) ∧
    (∀ r ∈ (s.accept Q st' pos).trans, r ∈ s.trans) ∧
    (s.accept Q st' pos).trans.length ≤ s.trans.length ∧
    (s.accept Q st' pos).chall.length ≤ s.chall.length ∧
    (s.accept Q st' pos).comp.length ≤ s.comp.length := by
  dsimp only [GameState.accept, GameState.delete]
  refine ⟨fun R => ?_, fun r hr => (List.mem_filter.mp hr).1,
    List.length_filter_le _ _, List.length_filter_le _ _, List.length_filter_le _ _⟩
  by_cases hR : R = Q
  · subst hR; simp
  · simp [hR]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem ghostChain_accept_epoch (g : GhostChain) (i : ℕ) :
    (g.accept i).epoch = g.epoch := by
  unfold GhostChain.accept
  split_ifs <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mem_modify_accept_epoch (cs : List GhostChain) (ci i : ℕ)
    {g' : GhostChain} (hg' : g' ∈ cs.modify ci (·.accept i)) :
    ∃ g ∈ cs, g'.epoch = g.epoch := by
  induction cs generalizing ci with
  | nil => simp at hg'
  | cons g gs ih =>
    cases ci with
    | zero =>
      change g' ∈ g.accept i :: gs at hg'
      rw [List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · exact ⟨g, List.mem_cons_self, ghostChain_accept_epoch g i⟩
      · exact ⟨g', List.mem_cons_of_mem g hg', rfl⟩
    | succ ci =>
      change g' ∈ g :: gs.modify ci (·.accept i) at hg'
      rw [List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · exact ⟨g', List.mem_cons_self, rfl⟩
      · obtain ⟨g₀, hg₀, heq⟩ := ih ci hg'
        exact ⟨g₀, List.mem_cons_of_mem g hg₀, heq⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mem_pushChain (cs : List GhostChain) (g₀ : GhostChain)
    {g' : GhostChain} (hg' : g' ∈ pushChain cs g₀) :
    g' = g₀ ∨ g' ∈ cs := by
  unfold pushChain at hg'
  have h1 := List.mem_of_mem_drop hg'
  rw [List.mem_append, List.mem_singleton] at h1
  exact h1.symm

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mem_trans_of_inTransit {St Msg C : Type} [DecidableEq C]
    (gs : GameState St Msg C) (P : Party) (c : C) (r : Record Msg C)
    (h : gs.inTransit P c = some r) :
    r ∈ gs.trans :=
  List.mem_of_find?_eq_some h

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem onAcceptPure_clampInv (qep B m : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (msg : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (st : SimState PQ Pt ℓ) (hInv : SimBaseClampInv B m st) (ht : t + m + 1 ≤ B) :
    SimBaseClampInv B m (onAcceptPure qep Q w isDel t i msg ci? T pq' st).2 := by
  have hacc : ∀ (pos : SM.Pos), pos.epoch + m + 1 ≤ B →
      SimBaseClampInv B m
        { st with
          chains := Function.update st.chains Q
            (match ci? with
             | some ci => (st.chains Q).modify ci (·.accept i)
             | none => pushChain (st.chains Q) (GhostChain.accept ⟨some T, t, 0, []⟩ i)),
          pq := Function.update st.pq Q pq',
          unackA := st.unackA && Q != Party.A,
          mir := st.mir.accept Q () pos } := by
    intro pos hpos
    obtain ⟨hep_le, _, _, _, _⟩ := accept_bounds st.mir Q () pos
    refine {
      hep := fun R => by
        dsimp only []
        have h1 := hep_le R
        have h2 := hInv.hep R
        omega
      htrans := fun r hr => by
        dsimp only [GameState.accept, GameState.delete] at hr
        exact hInv.htrans r (List.mem_of_mem_filter hr)
      hch := fun R g' hg' => by
        dsimp only [] at hg'
        by_cases hR : R = Q
        · subst hR
          simp only [Function.update_self] at hg'
          rcases ci? with _ | ci
          · rcases mem_pushChain (st.chains R) (GhostChain.accept ⟨some T, t, 0, []⟩ i) hg' with
              rfl | hg'
            · rw [ghostChain_accept_epoch]; exact ht
            · exact hInv.hch R g' hg'
          · obtain ⟨g, hg, heq⟩ := mem_modify_accept_epoch (st.chains R) ci i hg'
            rw [heq]; exact hInv.hch R g hg
        · simp only [Function.update_of_ne hR] at hg'
          exact hInv.hch R g' hg'
      hhonest := hInv.hhonest }
  unfold onAcceptPure
  cases isDel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1 h2
    · exact hInv
    · exact hacc ⟨Q.other, t, i⟩ ht
    · exact ⟨hInv.hep, hInv.htrans, hInv.hch, hInv.hhonest⟩
  · simp only [↓reduceIte]
    rcases hin : st.mir.inTransit Q.other w with _ | r
    · exact hInv
    · exact hacc r.pos (hInv.htrans r (mem_trans_of_inTransit st.mir Q.other w r hin))

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem onAnswerPure_clampInv (qep B m : ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (st : SimState PQ Pt ℓ) (hInv : SimBaseClampInv B m st)
    (hres : ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B) :
    SimBaseClampInv B m (onAnswerPure qep Q w isDel ci? T pq' res st).2 := by
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hInv
  · exact hInv
  · exact onAcceptPure_clampInv qep B m Q w isDel t i ((pm.map (·.2)).getD default) ci? T pq'
      st hInv (hres t i pm rfl)

omit [DecidableEq Pt] [SampleableType PQC] in
theorem scPostSendPure_clampInv {B m : ℕ}
    {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {s₁ : GameState Unit (Plain ℓ) (List (BitVec 8))}
    {Q : Party} {qep : ℕ} {hasCoins : Bool}
    (hep : sC.base.mir.epMgmt 3 qep Q hasCoins = some s₁)
    (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ) (pn : BitVec 32) (c : SimFig8C Pt)
    (hInv : SimBaseClampInv B (m + 1) sC.base)
    (hc : c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B) :
    SimBaseClampInv B m (scPostSendPure P Dh encPt encT lam sC s₁ Q m₀ isChall pq' pn c).base := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  obtain ⟨hep_le, htr_eq, _, _⟩ := epMgmt_bounds sC.base.mir s₁ 3 qep Q hasCoins hep
  refine {
    hep := fun R => by
      dsimp only [scPostSendPure, GameState.record]
      have h1 := hep_le R
      have h2 := hInv.hep R
      omega
    htrans := fun r hr => by
      dsimp only [scPostSendPure, GameState.record] at hr
      rw [List.mem_cons] at hr
      rcases hr with rfl | hr
      · dsimp only []
        have h1 := hep_le Q
        have h2 := hInv.hep Q
        omega
      · rw [htr_eq] at hr
        exact hInv0.htrans r hr
    hch := hInv0.hch
    hhonest := fun wc hwc => by
      dsimp only [scPostSendPure] at hwc
      rw [List.mem_cons] at hwc
      rcases hwc with rfl | hwc
      · exact hc
      · exact hInv0.hhonest wc hwc }

omit [DecidableEq Pt] [SampleableType PQC] in
theorem kept_eval_fig8Clamp_epoch_le (B : ℕ) (idOf : Party → IdentityKey)
    (k : Kept Pt) (c' : SimFig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : Kept.eval
      (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam))
      (fs := fsClampSim B (lFS P.C P.codec ℓ encT idOf 25000))
      c' k = some (some (t, i, pm))) :
    t ≤ c'.1.1 := by
  unfold Kept.eval at h
  rcases hfull : k.full with _ | st <;> simp only [hfull, Option.map] at h
  · rcases hrs : k.rs c'.1.1 with _ | v <;> simp only [hrs] at h
    · cases h
    · rcases hfs : (fsClampSim B (lFS P.C P.codec ℓ encT idOf 25000)).receive v c'.1 c'.2 with
        _ | ⟨v', i', pm'⟩ <;> simp only [hfs] at h
      · cases h
      · injection h with h; injection h with h; injection h with ht _
        omega
  · dsimp only [fig8Clamp] at h
    rcases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive st c' with
      _ | ⟨st', t_out, i_out, pm'⟩ <;> simp only [hfig, Option.map] at h
    · cases h
    · obtain ⟨rfl, _⟩ := lFig8_receive_epoch_index_eq P Dh encPt encT lam idOf st st' c'
        t_out i_out pm' hfig
      injection h with h; injection h with h; injection h with ht _
      omega

omit [Zero Pt] [SampleableType PQC] in
theorem sentEval_epoch_le
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (sent : List (SimFig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    (c c' : SimFig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : sentEval (fs := fs) sent c c' = some (some (t, i, pm))) :
    t ≤ c'.1.1 := by
  unfold sentEval at h
  rcases hfind : sent.find? (fun e => decide (e.1 = c)) with _ | e <;>
    simp only [hfind, Option.map] at h
  · cases h
  · rcases hfs : fs.receive ⟨e.2.chainKey, e.2.lastIndex, []⟩ c'.1 c'.2 with
      _ | ⟨v', i', pm'⟩ <;> simp only [hfs] at h
    · cases h
    · injection h with h; injection h with h; injection h with ht _
      omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem simKDecryptFig8_epoch_le (B : ℕ) (qB : Bool)
    (w : List (BitVec 8)) (c' : SimFig8C Pt) (seed : List (BitVec 8))
    (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : simKDecryptFig8 P ℓ B qB w c' seed = some (t, i, pm)) :
    t ≤ c'.1.1 := by
  dsimp only [simKDecryptFig8, decryptWithKnownSeed] at h
  rcases hl : lPubOf P.codec c'.2.2 with _ | pub <;> simp only [hl] at h
  · cases h
  · rcases htr : SignalMessage.tryFrom P.codec w with _ | msg <;> simp only [htr] at h
    · cases h
    · split_ifs at h <;> try cases h
      all_goals
        rcases hdec : aesCbcDecrypt P.C.D
            (deriveMessageKeys P.C.F (some c'.2.2.2) seed).1.1
            (deriveMessageKeys P.C.F (some c'.2.2.2) seed).1.2 msg.ciphertext with _ | m_raw <;>
          simp only [hdec] at h
        · cases h
        · injection h with h; injection h with ht _
          omega

omit [SampleableType PQC] in
theorem evalCKClamp_epoch_le (B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8))
    (c c' : SimFig8C Pt) (t i : ℕ) (pm : LibsignalMsgPublicPart × Plain ℓ)
    (h : evalCKClamp P Dh encPt encT lam B sC Q w c c' = some (some (t, i, pm))) :
    t ≤ c'.1.1 := by
  unfold evalCKClamp predictReceive at h
  dsimp only [Option.orElse] at h
  rcases hk : Kept.eval
      (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
      (fs := fsClampSim B (lFS P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000))
      c' (sC.kept Q) with _ | r
  · rw [hk] at h
    rcases hs : sentEval
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000))
        sC.sent c c' with _ | r'
    · rw [hs] at h
      rcases hks : snapshotMessageKeySeed P sC.snaps Q c.1.1 w with _ | seed
      · rw [hks] at h; cases h
      · rw [hks] at h
        injection h with h
        exact simKDecryptFig8_epoch_le P B (partyEnc Q) w c' seed t i pm h
    · rw [hs] at h
      exact sentEval_epoch_le _ sC.sent c c' t i pm (hs.trans h)
  · rw [hk] at h
    exact kept_eval_fig8Clamp_epoch_le P Dh encPt encT lam B _ (sC.kept Q) c' t i pm (hk.trans h)

/-- Clamp-invariant preservation conditions on a `SemHook` for `B`-clamped execution. -/
structure SemHookClampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    (B : ℕ) (ExClampInv : ℕ → Ex → Prop)
    (sh : SemHook PQC Pt ℓ T Ex) : Prop where
  mono : ∀ {m₁ m₂ ex}, m₁ ≤ m₂ → ExClampInv m₂ ex → ExClampInv m₁ ex
  onSendCoins_inv : ∀ {m Q rq ex}, ExClampInv m ex →
    ∀ y ∈ support (sh.onSendCoins Q rq ex), ExClampInv m y.1 ∧ ExClampInv m y.2
  onTr_inv : ∀ {m Q msg rc ex}, ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onTr Q msg rc ex),
      ExClampInv m y.2 ∧ ∀ c, y.1 = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B
  onCh_inv : ∀ {m Q m₀ m₁ rc ex}, ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onCh Q m₀ m₁ rc ex),
      ExClampInv m y.2 ∧ ∀ c, y.1 = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B
  onDl_inv : ∀ {m Q c ex}, c.1.1 ≤ B ∧ c.2.1 ≤ B → ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onDl Q c ex),
      ExClampInv m y.2 ∧ ∀ t i pm, y.1 = some (.accepted t i pm) → t + m + 1 ≤ B
  onIj_inv : ∀ {m Q c ex}, c.1.1 ≤ B ∧ c.2.1 ≤ B → ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onIj Q c ex),
      ExClampInv m y.2 ∧ ∀ t i pm, y.1 = some (.accepted t i pm) → t + m + 1 ≤ B
  onCr_inv : ∀ {m Q ex}, ExClampInv (m + 1) ex →
    ∀ y ∈ support (sh.onCr Q ex), ExClampInv m y.2
  onProbe_inv : ∀ {m Q c' ex}, ExClampInv (m + 1) ex →
    ∀ ex' ∈ support (sh.onProbe Q c' ex), ExClampInv m ex'
  onDeliverPost_inv : ∀ {m Q j? rr ex}, ExClampInv m ex →
    ∀ ex' ∈ support (sh.onDeliverPost Q j? rr ex), ExClampInv m ex'

omit [DecidableEq Pt] [SampleableType PQC] in
theorem semSendHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (hBase : SimBaseClampInv B (m + 1) sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semSendHook P Dh encPt encT lam sh qep sC₀ ex₀ Q m₀ chal r),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  have hBase0 := hBase.mono (Nat.le_succ m)
  have hEx0 := h_clamp.mono (Nat.le_succ m) hEx
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semSendHook at hx
  by_cases href : (sC₀.base.stopped || sC₀.base.mir.win || !(noBobSendInEpoch0 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hep : sC₀.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁ <;>
      simp only [hep] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
    · by_cases hch : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hch, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
        obtain ⟨⟨rq, rc⟩, -, ⟨exOk, exFail⟩, hsc, hx⟩ := hx
        obtain ⟨hOk, hFail⟩ := h_clamp.onSendCoins_inv hEx (exOk, exFail) hsc
        have hFail0 := h_clamp.mono (Nat.le_succ m) hFail
        rcases hpub : mkPub P sC₀.base Q rq
          (if s₁.epoch Q ≠ sC₀.base.mir.epoch Q then
            BitVec.ofNat 32 (sC₀.base.mir.idx Q - 1) else sC₀.base.pn Q) with _ | ⟨pq', pub⟩ <;>
          simp only [hpub] at hx
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hFail0⟩
        · simp only [mem_support_bind_iff] at hx
          obtain ⟨⟨res, ex₂⟩, hq, hx⟩ := hx
          have hEx2 : ExClampInv m ex₂ ∧
              ∀ c, res = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 + m + 1 ≤ B := by
            rcases chal with _ | m₁
            · exact h_clamp.onTr_inv hOk (res, ex₂) hq
            · exact h_clamp.onCh_inv hOk (res, ex₂) hq
          rcases res with _ | c <;>
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          · rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hFail0⟩
          · rcases hx with ⟨_, rfl, rfl⟩
            exact ⟨scPostSendPure_clampInv P Dh encPt encT lam hep m₀ chal.isSome pq' _ c
              hBase (hEx2.2 c rfl), hEx2.1⟩

omit [SampleableType PQC] in
theorem semFwdAnswerHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hc' : c'.1.1 ≤ B ∧ c'.2.1 ≤ B)
    (hBase : SimBaseClampInv B m sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semFwdAnswerHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdAnswerHook at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, hq, _, rfl, rfl⟩ := hx
  have hq' : ExClampInv m ex₁ ∧ ∀ t i pm, res = some (.accepted t i pm) → t + m + 1 ≤ B := by
    split_ifs at hq
    · exact h_clamp.onDl_inv hc' hEx (res, ex₁) hq
    · exact h_clamp.onIj_inv hc' hEx (res, ex₁) hq
  exact ⟨onAnswerPure_clampInv qep B m Q w isDel ci? Tpk pq' res sC₀.base hBase hq'.2, hq'.1⟩

omit [DecidableEq Pt] [SampleableType PQC] in
theorem semResyncHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hc : c.1.1 ≤ B ∧ c.2.1 ≤ B)
    (hr : ∀ t i pm, r = some (t, i, pm) → t + m + 1 ≤ B)
    (hBase : SimBaseClampInv B m sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semResyncHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w ci? Tpk pq' c r),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semResyncHook at hx
  rcases r with _ | ⟨t, i, pub, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, rfl⟩
    exact ⟨hBase, h_clamp.mono (Nat.le_succ m) hEx⟩
  · simp only [mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, hdl, hx⟩ := hx
    have hEx' := (h_clamp.onDl_inv hc hEx (res, ex') hdl).1
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase, hEx'⟩
    · rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase, hEx'⟩
    · rcases hx with ⟨_, rfl, rfl⟩
      exact ⟨onAcceptPure_clampInv qep B m Q w true t i m' ci? Tpk pq' sC₀.base
        hBase (hr t i (pub, m') rfl), hEx'⟩

omit [SampleableType PQC] in
theorem semFwdHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hhc : ∀ c, honestC = some c → c.1.1 ≤ B ∧ c.2.1 ≤ B)
    (hc' : c'.1.1 + m + 1 ≤ B ∧ c'.2.1 ≤ B)
    (hBase : SimBaseClampInv B m sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support
        (semFwdHook P Dh encPt encT lam sh qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c'),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  have hc'0 : c'.1.1 ≤ B ∧ c'.2.1 ≤ B := ⟨by omega, hc'.2⟩
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdHook at hx
  rcases hhc_eq : honestC with _ | c <;> simp only [hhc_eq] at hx
  · exact semFwdAnswerHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' hc'0 hBase hEx _ hx
  · split_ifs at hx
    · rcases hev : evalCKClamp P Dh encPt encT lam B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨ex', hpr, _, rfl, rfl⟩ := hx
        exact ⟨hBase, h_clamp.onProbe_inv hEx ex₁ hpr⟩
      · refine semResyncHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
          sC₀ ex₀ Q w ci? Tpk pq' c r (hhc c hhc_eq) (fun t i pm hr => ?_) hBase hEx _ hx
        subst hr
        have htle := evalCKClamp_epoch_le P Dh encPt encT lam B sC₀ Q w c c' t i pm hev
        omega
    · exact semFwdAnswerHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
        sC₀ ex₀ Q w isDel ci? Tpk pq' c' hc'0 hBase hEx _ hx

omit [SampleableType PQC] in
theorem semFwdEvictHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hc' : c'.1.1 ≤ B ∧ c'.2.1 ≤ B)
    (hBase : SimBaseClampInv B m sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semFwdEvictHook P Dh encPt encT lam sh qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdEvictHook at hx
  split_ifs at hx
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨ex', hpr, _, rfl, rfl⟩ := hx
    exact ⟨hBase, h_clamp.onProbe_inv hEx ex₁ hpr⟩
  · exact semFwdAnswerHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
      sC₀ ex₀ Q w isDel none Tpk pq' c' hc' hBase hEx _ hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem _root_.CryptoGames.Ratchet.LibsignalSim.SimBaseClampInv.withAmb
    {B m : ℕ} {s : SimState PQ Pt ℓ}
    (h : SimBaseClampInv B m s) (a : ℕ) :
    SimBaseClampInv B m { s with amb := a } :=
  ⟨h.hep, h.htrans, h.hch, h.hhonest⟩

omit [SampleableType PQC] in
theorem semRecvHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (h232 : 2 ^ 32 ≤ B)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (hBase : SimBaseClampInv B (m + 1) sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semRecvHook P Dh encPt encT decT lam sh qep B sC₀ ex₀ Q w isDel),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  have hBase0 := hBase.mono (Nat.le_succ m)
  have hEx0 := h_clamp.mono (Nat.le_succ m) hEx
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semRecvHook at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hparse] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
    · have hlct : lct.1 ≤ B :=
        (simParseRecvC_bounds P decT (partyEnc Q) (sC₀.base.pq Q) w hparse).2.trans h232
      have hhc : ∀ c,
          (sC₀.base.honest.find? fun wc =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c →
          c.1.1 + m + 1 ≤ B ∧ c.2.1 ≤ B := by
        intro c hc
        rw [Option.map_eq_some_iff] at hc
        rcases hc with ⟨wc, hmem, rfl⟩
        have h1 := hBase.hhonest wc (List.mem_of_find?_eq_some hmem)
        exact ⟨by have := h1.1; omega, by have := h1.2; omega⟩
      have hhc0 : ∀ c,
          (sC₀.base.honest.find? fun wc =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c →
          c.1.1 ≤ B ∧ c.2.1 ≤ B := fun c hc => ⟨by have := (hhc c hc).1; omega, (hhc c hc).2⟩
      have hmkC : ∀ (honestC : Option (SimFig8C Pt)),
          (∀ c, honestC = some c → c.1.1 + m + 1 ≤ B ∧ c.2.1 ≤ B) →
          ∀ (t : ℕ) (T1 : Option Pt), t + m + 1 ≤ B →
          (match honestC with
           | some c => if c.2.2.2 = lct.2.2 then c else ((t, T1), lct)
           | none => ((t, T1), lct)).1.1 + m + 1 ≤ B ∧
          (match honestC with
           | some c => if c.2.2.2 = lct.2.2 then c else ((t, T1), lct)
           | none => ((t, T1), lct)).2.1 ≤ B := by
        intro honestC hhc1 t T1 ht
        rcases honestC with _ | c
        · exact ⟨ht, hlct⟩
        · dsimp only []
          split_ifs
          · exact hhc1 c rfl
          · exact ⟨ht, hlct⟩
      rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hBaseAmb : SimBaseClampInv B m
            (if inReceiveOnlyEpoch sC₀.base.mir Q || (Q == Party.A && (sC₀.base.chains Q).any (·.key.isNone))
             then { sC₀.base with amb := sC₀.base.amb + 1 } else sC₀.base) := by
          split_ifs
          · exact hBase0.withAmb _
          · exact hBase0
        by_cases hc1 :
            ((((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
             (((sC₀.base.honest.find? fun wc =>
                wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBaseAmb, hEx0⟩
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T <;>
                simp only [hT] at hx
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBaseAmb, hEx0⟩
              · have hep1 : (sC₀.base.mir.epoch Q + 1) + m + 1 ≤ B := by
                  have := hBase.hep Q; omega
                by_cases hev_b :
                    ((((sC₀.base.honest.find? fun wc =>
                        wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  exact semFwdEvictHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
                    _ ex₀ Q w isDel pk pq' _ ⟨by dsimp only []; omega, hlct⟩ hBaseAmb hEx _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
                    _ ex₀ Q w isDel none pk pq' _ _ hhc0
                    (hmkC _ hhc (sC₀.base.mir.epoch Q + 1) (some T) hep1) hBaseAmb hEx _ hx
      · by_cases hrej : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          have hgep : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch + m + 1 ≤ B := by
            rw [List.getD_eq_getElem?_getD]
            rcases h : (sC₀.base.chains Q)[ci]? with _ | g
            · dsimp only [Option.getD]; have := hBase.hep Q; omega
            · dsimp only [Option.getD]
              have := hBase.hch Q g (List.mem_of_getElem? h)
              omega
          exact semFwdHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep
            sC₀ ex₀ Q w isDel (some ci) pk pq' _ _ hhc0
            (hmkC _ hhc ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).epoch T? hgep)
            hBase0 hEx _ hx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem semCorrHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m : ℕ) (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hBase : SimBaseClampInv B (m + 1) sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semCorrHook P Dh encT sh sC₀ ex₀ Q),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  have hBase0 := hBase.mono (Nat.le_succ m)
  have hEx0 := h_clamp.mono (Nat.le_succ m) hEx
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semCorrHook at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx0⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, hcr, hx⟩ := hx
    have hEx' := h_clamp.onCr_inv hEx (res, ex') hcr
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, rfl⟩; exact ⟨hBase0, hEx'⟩
    · rcases hx with ⟨_, rfl, rfl⟩
      refine ⟨{
        hep := fun R => by
          dsimp only [GameState.afterCorr, GameState.leak]
          exact hBase0.hep R
        htrans := fun r hr => by
          dsimp only [GameState.afterCorr, GameState.leak] at hr
          exact hBase0.htrans r hr
        hch := fun R g' hg' => by
          dsimp only [] at hg'
          split_ifs at hg'
          · rcases hγ : fig8st.γ with _ | x <;> simp only [hγ] at hg'
            · exact hBase0.hch R g' hg'
            · by_cases hR : R = Party.A
              · subst hR
                simp only [Function.update_self, List.mem_map] at hg'
                obtain ⟨g, hg, hge⟩ := hg'
                have hg_ep : g'.epoch = g.epoch := by split_ifs at hge <;> (subst hge; rfl)
                rw [hg_ep]; exact hBase0.hch Party.A g hg
              · simp only [Function.update_of_ne hR] at hg'
                exact hBase0.hch R g' hg'
          · exact hBase0.hch R g' hg'
        hhonest := hBase0.hhonest }, hEx'⟩

omit [SampleableType PQC] in
theorem semHandleHook_preserves_clampInv {ι : Type} {T : OracleSpec ι} {Ex : Type}
    {B : ℕ} {ExClampInv : ℕ → Ex → Prop}
    {sh : SemHook PQC Pt ℓ T Ex} (h_clamp : SemHookClampInv B ExClampInv sh)
    (m qep : ℕ) (h232 : 2 ^ 32 ≤ B)
    (t : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex)
    (hBase : SimBaseClampInv B (m + 1) sC₀.base)
    (hEx : ExClampInv (m + 1) ex₀) :
    ∀ x ∈ support (semHandleHook P Dh encPt encT decT lam sh qep B t sC₀ ex₀),
      SimBaseClampInv B m x.2.1.base ∧ ExClampInv m x.2.2 := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep sC₀ ex₀ Q m₀ none r
      hBase hEx
  · exact semSendHook_preserves_clampInv P Dh encPt encT lam h_clamp m qep sC₀ ex₀ Q m₀ (some m₁) r
      hBase hEx
  · rintro ⟨_, sC₁, ex₁⟩ hx
    unfold semHandleHook at hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨rr, sC', ex'⟩, hrec, ex₂, hpost, _, rfl, rfl⟩ := hx
    obtain ⟨hB', hE'⟩ := semRecvHook_preserves_clampInv P Dh encPt encT decT lam h_clamp m qep h232
      sC₀ ex₀ Q w true hBase hEx (rr, sC₁, ex') hrec
    exact ⟨hB', h_clamp.onDeliverPost_inv hE' ex₁ hpost⟩
  · exact semRecvHook_preserves_clampInv P Dh encPt encT decT lam h_clamp m qep h232
      sC₀ ex₀ Q w false hBase hEx
  · exact semCorrHook_preserves_clampInv P Dh encT h_clamp m sC₀ ex₀ Q hBase hEx

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem cellGameClampInv_corrImplShiftedPaper (B m l : ℕ)
    (gs gs' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (Q : Party) (res : Option (SimFig8St Pt))
    (hfg : CellGameClampInv B (m + 1) gs)
    (hmem : (res, gs') ∈ support
      ((DeliverForge.corrImplShiftedPaper
        (St := SimFig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (C := SimFig8C Pt) l Q).run gs)) :
    CellGameClampInv B m gs' := by
  have hfg0 := hfg.mono (Nat.le_succ m)
  unfold DeliverForge.corrImplShiftedPaper at hmem
  by_cases hw : (gs.win || !(gs.corrAllowedPaper Q)) = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; exact hfg0
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    have hst : (DeliverForge.afterCorrShifted l gs Q).st = gs.st := by
      unfold DeliverForge.afterCorrShifted
      split_ifs <;> rfl
    exact {
      hmB := hfg0.hmB
      htcur := fun R => by rw [hst]; exact hfg0.htcur R
      hvS := fun R v hv => by rw [hst] at hv; exact hfg0.hvS R v hv }

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem transmitImpl_run_none_eq
    (fig : SMScheme (Ratchet.RootKey × BitVec 256) (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (SimFig8C Pt))
    (d qepF : ℕ) (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (r? : Option (BitVec 256))
    (g g' : GameState (SimFig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (SimFig8C Pt))
    (h : (none, g') ∈ support ((SM.transmitImpl fig d qepF (Q, m, r?)).run g)) :
    g' = g := by
  simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at h
  split_ifs at h with h1
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    exact h.2
  · simp only [StateT.run_bind, stateT_liftM_probComp_run, bind_assoc, pure_bind,
      mem_support_bind_iff] at h
    rcases h with ⟨⟨r, bad⟩, _, h⟩
    split at h
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      exact h.2
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at h

end CellClamp

end CryptoVerification.E2E
