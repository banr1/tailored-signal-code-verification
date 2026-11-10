/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1C
import Computational.Proofs.GameHop.Advantage

/-!
# Hop 2 Terminal Hybrid and Absorbing States

Defines the send-step relation `StSendStep`, the terminal hybrid invariants `Hop2LastDone` and
`Hop2LastActiveAt`, and the absorbing condition `Hop2Absorbed` for `runHop2`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

set_option linter.unusedSectionVars false

section Hop2Coupling

open CryptoGames.CKA CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF MACScheme

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}

/-! ## Send-step relation and `Hop2LastDone` -/

theorem bind_le_of_support {α β : Type} [MeasurableSpace β] (mx : ProbComp α)
    (f : α → ProbComp β) {E : Set β} (hE : MeasurableSet E) {r : ℝ≥0∞}
    (h : ∀ a ∈ support mx, 𝒟[f a] E ≤ r) : 𝒟[mx >>= f] E ≤ r := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply hE Measurable.of_discrete.aemeasurable]
    calc _ ≤ ∫⁻ _u, r ∂𝒟[(OracleSpec.query (spec := unifSpec) t : ProbComp _)] :=
          MeasureTheory.lintegral_mono fun u => ih u fun a ha =>
            h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)
      _ = r := by rw [MeasureTheory.lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem bind_apply_le_add_of_bad {α : Type} (mx : ProbComp α)
    (f : α → ProbComp Bool) (bad : α → Bool) (r : ℝ≥0∞)
    (hgood : ∀ c, bad c = false → 𝒟[f c] {true} ≤ r) :
    𝒟[mx >>= f] {true} ≤
      𝒟[mx >>= fun c => pure (bad c)] {true} + r := by
  refine Computational.Proofs.GameHop.Advantage.evalDist_bind_le_add_prob_of_support mx f
    (fun c => pure (bad c)) (measurableSet_singleton true) fun c _ => ?_
  rcases hbc : bad c
  · exact (hgood c hbc).trans le_add_self
  · simp only [evalDist_pure, MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton true),
      Set.indicator_of_mem (Set.mem_singleton true), Pi.one_apply]
    exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
      ((evalDist_apply_univ_eq_one _).le.trans le_self_add)

theorem bind_apply_le_add_of_eq_on_good {α : Type} (mx : ProbComp α)
    (f g : α → ProbComp Bool) (bad : α → Bool)
    (heq : ∀ c, bad c = false → f c = g c) :
    𝒟[mx >>= f] {true} ≤
      𝒟[mx >>= fun c => pure (bad c)] {true} + 𝒟[mx >>= g] {true} := by
  let : MeasurableSpace α := ⊤
  have h1 : ∀ (k : α → ProbComp Bool),
      𝒟[mx >>= k] {true} = ∫⁻ c, 𝒟[k c] {true} ∂𝒟[mx] := fun k => by
    rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
      Measurable.of_discrete.aemeasurable]
  rw [h1 f, h1 (fun c => pure (bad c)), h1 g,
    ← MeasureTheory.lintegral_add_left Measurable.of_discrete]
  refine MeasureTheory.lintegral_mono fun c => ?_
  rcases hbc : bad c
  · rw [heq c hbc]; exact le_add_self
  · simp only [evalDist_pure, MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton true),
      Set.indicator_of_mem (Set.mem_singleton true), Pi.one_apply]
    exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
      ((evalDist_apply_univ_eq_one _).le.trans le_self_add)

theorem fromSessionState_preserves (record : SessionState PQ) :
    let taken := (Mut.exec OutgoingTripleRatchet.fromSessionState record).2
    taken.remoteIdentity = record.remoteIdentity ∧
    taken.localIdentity = record.localIdentity ∧
    taken.receiverChains = record.receiverChains := by
  unfold OutgoingTripleRatchet.fromSessionState
  rw [Mut_exec_bind, Mut_exec_get]
  dsimp only []
  cases record.senderChain with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some sc =>
    rw [Mut_exec_bind, Mut_exec_takePqRatchetState]
    dsimp only []
    rw [Mut_exec_bind, Mut_exec_get]
    dsimp only []
    split_ifs with hv
    · exact ⟨rfl, rfl, rfl⟩
    · cases record.remoteIdentity <;> exact ⟨rfl, rfl, rfl⟩

omit [SampleableType PQC] in
theorem messageEncrypt_preserves (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
    (addrs : Option (List (BitVec 8))) (ptext : List (BitVec 8)) (coins : PQC)
    (record : SessionState PQ) :
    let s := (SessionState.messageEncrypt C codec spqr addrs ptext coins record).2
    s.remoteIdentity = record.remoteIdentity ∧
    s.localIdentity = record.localIdentity ∧
    s.receiverChains = record.receiverChains := by
  have h1 := fromSessionState_preserves record
  unfold SessionState.messageEncrypt
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState record with ⟨r_from, taken⟩
  rw [hfrom] at h1
  cases r_from with
  | error _ => exact ⟨rfl, rfl, rfl⟩
  | ok session =>
    dsimp only []
    rcases Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext
      (record.encryptAddresses addrs) coins) session with ⟨r_enc, session'⟩
    cases r_enc with
    | error _ => exact ⟨rfl, rfl, rfl⟩
    | ok _ => exact h1

theorem sessionSchemeU_send_props {ℓ : ℕ} (P : Params Bytes PQC)
    (g : GhostState Bytes) (m : CBC.Plain ℓ) (r : PQC) :
    let g' := ((sessionSchemeU P ℓ).send g m r).1
    g'.party = g.party ∧
    g'.chainEpochs = g.chainEpochs ∧
    g'.session.remoteIdentity = g.session.remoteIdentity ∧
    g'.session.localIdentity = g.session.localIdentity ∧
    g'.session.receiverChains = g.session.receiverChains := by
  have hp := messageEncrypt_preserves P.C P.codec P.spqr (P.sendAddrs g.party) m.toList r g.session
  unfold sessionSchemeU Params.send
  dsimp only []
  rcases h :
      SessionState.messageEncrypt P.C P.codec P.spqr (P.sendAddrs g.party) m.toList r g.session
    with ⟨res, s⟩
  rw [h] at hp
  cases res with
  | error _ => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | ok _ => exact ⟨rfl, rfl, hp.1, hp.2.1, hp.2.2⟩

/-- Relation between two SM game states where each party's ghost state is either unchanged or
advanced by a single `(sessionSchemeU P ℓ).send`. -/
def StSendStep {ℓ : ℕ} (P : Params Bytes PQC)
    (s₁ s₂ : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) : Prop :=
  ∀ Q, s₂.st Q = s₁.st Q ∨ ∃ m r, s₂.st Q = ((sessionSchemeU P ℓ).send (s₁.st Q) m r).1

theorem StSendStep.refl {ℓ : ℕ} (P : Params Bytes PQC)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    StSendStep P s s := fun _ => Or.inl rfl

theorem StSendStep.preserves_party_epochs {ℓ : ℕ} (P : Params Bytes PQC)
    {s₁ s₂ : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (h : StSendStep P s₁ s₂) (Q : Party) :
    (s₂.st Q).party = (s₁.st Q).party ∧
    (s₂.st Q).chainEpochs = (s₁.st Q).chainEpochs ∧
    (s₂.st Q).session.remoteIdentity = (s₁.st Q).session.remoteIdentity ∧
    (s₂.st Q).session.localIdentity = (s₁.st Q).session.localIdentity ∧
    (s₂.st Q).session.receiverChains = (s₁.st Q).session.receiverChains := by
  rcases h Q with heq | ⟨m, r, heq⟩
  · rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [heq]; exact sessionSchemeU_send_props P (s₁.st Q) m r

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitR_support_stSendStep {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (x : Party × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    ∀ z ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st),
      StSendStep P st z.2 := by
  rcases x with ⟨Q, m, r⟩
  intro z hz
  unfold SM.transmitR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact StSendStep.refl P st
    · rw [StateT.run_bind] at hz
      simp only [StateT.run_monadLift, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : st.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact StSendStep.refl P st
      | some st1 =>
        simp only [hep, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz
        have hst := (CryptoVerification.E2E.Relabel.GameEq.epMgmt_st_trans hep).1
        intro R
        unfold SM.GameState.record
        dsimp only []
        by_cases hR : R = Q
        · subst hR
          rw [Function.update_self, hst]
          exact Or.inr ⟨m, cb.1, rfl⟩
        · rw [Function.update_of_ne hR, hst]
          exact Or.inl rfl
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact StSendStep.refl P st

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challR_support_stSendStep {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    ∀ z ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st),
      StSendStep P st z.2 := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  intro z hz
  unfold SM.challR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact StSendStep.refl P st
    · rw [StateT.run_bind] at hz
      simp only [StateT.run_monadLift, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz⟩
      cases hep : st.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact StSendStep.refl P st
      | some st1 =>
        simp only [hep] at hz
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact StSendStep.refl P st
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          have hst := (CryptoVerification.E2E.Relabel.GameEq.epMgmt_st_trans hep).1
          intro R
          unfold SM.GameState.record
          dsimp only []
          by_cases hR : R = Q
          · subst hR
            rw [Function.update_self, hst]
            exact Or.inr ⟨_, cb.1, rfl⟩
          · rw [Function.update_of_ne hR, hst]
            exact Or.inl rfl
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact StSendStep.refl P st

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrR_support_stSendStep {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (Q : Party)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    ∀ z ∈ support ((SM.corrR (configRefuseEarlyBobCorr decT encT) Q).run st),
      StSendStep P st z.2 := by
  intro z hz
  unfold SM.corrR at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact StSendStep.refl P st
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact StSendStep.refl P st

theorem sessionSchemeU_receive_party_epochs {ℓ : ℕ} (P : Params Bytes PQC)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st' : GhostState Bytes) (t' i' : ℕ) (m' : CBC.Plain ℓ)
    (hrec : (sessionSchemeU P ℓ).receive g c rc = some (st', t', i', m')) :
    st'.party = g.party ∧
    ((∀ e ∈ g.chainEpochs, 0 < e) → ∀ e ∈ st'.chainEpochs, 0 < e) := by
  unfold sessionSchemeU Params.receive at hrec
  simp only [Option.map_eq_some_iff] at hrec
  rcases hrec with ⟨⟨g1, t1, i1, m1⟩, hy, htuple⟩
  rcases Prod.mk.inj htuple with ⟨rfl, _⟩
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ => rw [htry] at hy; cases hy
  | ok msg =>
    rw [htry] at hy
    dsimp only [] at hy
    rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc g.session with ⟨r_tr, s_out⟩
    rw [htr] at hy
    cases r_tr with
    | error _ => cases hy
    | ok m_plain =>
      dsimp only [] at hy
      injection hy with hy'
      rcases Prod.mk.inj hy' with ⟨rfl, _⟩
      refine ⟨rfl, fun hpos e he => ?_⟩
      have hmem := List.mem_of_mem_drop he
      cases hfind :
          g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey) with
      | some i =>
        rw [hfind] at hmem
        exact hpos e hmem
      | none =>
        rw [hfind] at hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · exact hpos e h1
        · simp only [List.mem_singleton] at h2
          omega

/-- Absorbing terminal invariant ensuring `hop2BadAt` stays `false` once Alice's `chainEpochs` are
all positive. -/
structure Hop2LastDone {ℓ : ℕ} (P : Params Bytes PQC) (s : BitVec 256)
    (st : Hop2State Pt ℓ) : Prop where
  bad_false : st.2.bad = false
  party_A : (st.1.st .A).party = .A
  party_B : (st.1.st .B).party = .B
  pos_epochs_A : ∀ e ∈ (st.1.st .A).chainEpochs, 0 < e

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem Hop2LastDone.of_stSendStep {ℓ : ℕ} {P : Params Bytes PQC} {s : BitVec 256}
    {st : Hop2State Pt ℓ} (h : Hop2LastDone P s st)
    {s₂ : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hstep : StSendStep P st.1 s₂) :
    Hop2LastDone P s (s₂, st.2) where
  bad_false := h.bad_false
  party_A := (hstep.preserves_party_epochs P .A).1.trans h.party_A
  party_B := (hstep.preserves_party_epochs P .B).1.trans h.party_B
  pos_epochs_A := by
    rw [(hstep.preserves_party_epochs P .A).2.1]
    exact h.pos_epochs_A

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem Hop2LastDone.hop2BadAt_eq_false {ℓ : ℕ} {P : Params Bytes PQC} {s : BitVec 256}
    {st : Hop2State Pt ℓ} (h : Hop2LastDone P s st) (Q : Party) (c : Bytes) :
    hop2BadAt P s (st.1.st Q) c = false := by
  cases Q with
  | A => exact hop2BadAt_eq_false_of_pos_epochs P s (st.1.st .A) c h.pos_epochs_A
  | B => exact hop2BadAt_eq_false_of_party_B P s (st.1.st .B) c h.party_B

omit [SampleableType Pt] in
theorem hop2RecvHalf_support_done {ℓ : ℕ} (P : Params Bytes PQC) (h : Hop2Hyb Pt)
    (idx : Option ℕ) (rk : Ratchet.RootKey) (their : PublicKey) (our : PrivateKey) (Q_pt : Pt)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (z : (Option (Option ℕ × Ratchet.RootKey × BitVec 256) × Hop2State Pt ℓ) × List (Pt × BitVec
        256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2RecvHalf P h idx rk their our Q_pt).run st)).run tbl)) :
    z.1.2.1 = st.1 ∧ z.1.2.2.bad = st.2.bad := by
  unfold hop2RecvHalf at hz
  cases idx with
  | none =>
    dsimp only [] at hz
    cases hcc : rootCreateChain P.C rk their our with
    | error _ =>
      rw [hcc] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl⟩
    | ok p =>
      rcases p with ⟨rk', ck⟩
      rw [hcc] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl⟩
  | some t =>
    dsimp only [] at hz
    by_cases hQ0 : Q_pt = 0
    · simp only [hQ0, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl⟩
    · simp only [hQ0, ↓reduceIte] at hz
      by_cases htle : t ≤ h.k
      · simp only [htle, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hz
        cases hmade : st.2.made.lookup (t, Q_pt) with
        | some ck =>
          rw [hmade] at hz
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨rfl, rfl⟩
        | none =>
          rw [hmade] at hz
          unfold hop2Lazy at hz
          simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc] at hz
          cases hlazy : st.2.lazy.lookup (t, Q_pt) with
          | some u =>
            rw [hlazy] at hz
            simp only [StateT.run_pure] at hz
            subst hz; exact ⟨rfl, rfl⟩
          | none =>
            rw [hlazy] at hz
            simp only [stateT_lift_run_hop2, StateT.run_bind, StateT.run_set, StateT.run_pure,
              bind_assoc, pure_bind, simulateQ_bind, simulateQ_lazyImpl_hop2Unif,
              stateT_lift_probComp_run, simulateQ_pure, MonadAttach.mem_support_bind,
              support_pure, Set.mem_singleton_iff] at hz
            rcases hz with ⟨u, _, rfl⟩
            exact ⟨rfl, rfl⟩
      · simp only [htle, ↓reduceIte, stateT_lift_run_hop2, StateT.run_bind, StateT.run_pure,
          bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨⟨u, tbl'⟩, _, rfl⟩
        exact ⟨rfl, rfl⟩

omit [SampleableType Pt] in
theorem hop2DH_support_done {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (h : Hop2Hyb Pt)
    (idx : Option ℕ) (coins : BitVec 256) (g : GhostState Bytes) (msg : SignalMessage)
    (rc : BitVec 256) (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2DH P Dh encT decT h idx coins g msg rc).run st)).run tbl)) :
    z.1.2.1 = st.1 ∧ z.1.2.2.bad = st.2.bad ∧
    ∀ st' t' i' m' u, z.1.1 = some ((st', t', i', m'), u) →
      st'.party = g.party ∧ ((∀ e ∈ g.chainEpochs, 0 < e) → ∀ e ∈ st'.chainEpochs, 0 < e) := by
  unfold hop2DH at hz
  cases hdec : decT msg.senderRatchetKey with
  | none =>
    rw [hdec] at hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
  | some T =>
    rw [hdec] at hz
    dsimp only [] at hz
    by_cases hT : T = 0 ∨ encT T ≠ msg.senderRatchetKey
    · simp only [hT, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
    · simp only [hT, ↓reduceIte] at hz
      cases hsc : g.session.senderChain with
      | none =>
        rw [hsc] at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
      | some sc =>
        rw [hsc] at hz
        simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at hz
        rcases hz with ⟨⟨⟨r1, st1⟩, tbl1⟩, hz1, hz2⟩
        have h1 := hop2RecvHalf_support_done P h idx g.session.rootKey msg.senderRatchetKey
          sc.ratchetKey.privateKey (Dh.dh coins T) st tbl _ hz1
        cases r1 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz2
          subst hz2; exact ⟨h1.1, h1.2, fun _ _ _ _ _ h => by cases h⟩
        | some p1 =>
          rcases p1 with ⟨idx1, rkM, ckR⟩
          simp only [stateT_lift_run_hop2, StateT.run_bind, bind_assoc, pure_bind,
            simulateQ_bind, MonadAttach.mem_support_bind] at hz2
          rcases hz2 with ⟨⟨r2, tbl2⟩, _, hz3⟩
          cases r2 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz3
            subst hz3; exact ⟨h1.1, h1.2, fun _ _ _ _ _ h => by cases h⟩
          | some p2 =>
            rcases p2 with ⟨idx2, rk2, ckS, pend⟩
            dsimp only [] at hz3
            rcases htr : SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
              msg .whisper rc _ with ⟨r_tr, s_out⟩
            rw [htr] at hz3
            cases r_tr with
            | error _ =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hz3
              subst hz3; exact ⟨h1.1, h1.2, fun _ _ _ _ _ h => by cases h⟩
            | ok m_plain =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hz3
              subst hz3
              refine ⟨h1.1, h1.2, fun st' t' i' m' u hsome => ?_⟩
              injection hsome with hpair
              rcases Prod.mk.inj hpair with ⟨h4, _⟩
              rcases Prod.mk.inj h4 with ⟨rfl, _⟩
              refine ⟨rfl, fun hpos e he => ?_⟩
              rcases List.mem_append.mp (List.mem_of_mem_drop he) with he1 | he2
              · exact hpos e he1
              · simp only [List.mem_singleton] at he2; omega

omit [SampleableType Pt] in
theorem hop2Recv_support_done {ℓ : ℕ} (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (h : Hop2Hyb Pt)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT h g c rc).run st)).run tbl)) :
    z.1.2.1 = st.1 ∧ z.1.2.2.bad = st.2.bad ∧
    ∀ st' t' i' m' u, z.1.1 = some ((st', t', i', m'), u) →
      st'.party = g.party ∧ ((∀ e ∈ g.chainEpochs, 0 < e) → ∀ e ∈ st'.chainEpochs, 0 < e) := by
  unfold hop2Recv at hz
  cases htry : SignalMessage.tryFrom P.codec c with
  | error _ =>
    rw [htry] at hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨rfl, rfl, fun _ _ _ _ _ h => by cases h⟩
  | ok msg =>
    rw [htry] at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hidx : st.2.idx g.party with
    | none =>
      rw [hidx] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨rfl, rfl, fun st' t' i' m' u hsome => ?_⟩
      simp only [Option.map_eq_some_iff] at hsome
      rcases hsome with ⟨⟨st1, t1, i1, m1⟩, hrec, hpair⟩
      rcases Prod.mk.inj hpair with ⟨h4, _⟩
      rcases Prod.mk.inj h4 with ⟨rfl, _⟩
      exact sessionSchemeU_receive_party_epochs P g c rc st1 t1 i1 m1 hrec
    | some t =>
      rw [hidx] at hz
      dsimp only [] at hz
      split_ifs at hz with hfind
      · exact hop2DH_support_done P Dh encT decT h (some t) (st.2.coins g.party) g msg rc st tbl z
          hz
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨rfl, rfl, fun st' t' i' m' u hsome => ?_⟩
        simp only [Option.map_eq_some_iff] at hsome
        rcases hsome with ⟨⟨st1, t1, i1, m1⟩, hrec, hpair⟩
        rcases Prod.mk.inj hpair with ⟨h4, _⟩
        rcases Prod.mk.inj h4 with ⟨rfl, _⟩
        exact sessionSchemeU_receive_party_epochs P g c rc st1 t1 i1 m1 hrec

omit [SampleableType Pt] in
theorem hop2RecvWithPost_support_done {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (h : Hop2Hyb Pt) (Q : Party) (c : Bytes)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s Q c (st.1.st Q) post)
    (hdone : Hop2LastDone P s st)
    (z : (Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt)) (do
      let rc ← hop2Unif (Pt := Pt)
      let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st
      return post res.1 res.2)).run tbl)) :
    Hop2LastDone P s z.1.2 := by
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
    stateT_lift_probComp_run, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨rc, _, ⟨⟨r_out, st2⟩, tbl2⟩, hz_rec, hz_pure⟩
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz_pure
  subst hz_pure
  have hrec := hop2Recv_support_done P Dh encT decT h (st.1.st Q) c rc st tbl _ hz_rec
  rcases hrec with ⟨hst1, hbad2, hsome⟩
  cases r_out with
  | none =>
    rw [hpost.on_none]
    exact ⟨hbad2.trans hdone.bad_false, hst1 ▸ hdone.party_A, hst1 ▸ hdone.party_B,
      hst1 ▸ hdone.pos_epochs_A⟩
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    have hp := hpost.on_some st' t' i' m' u st2
    have hbad_next : (post (some ((st', t', i', m'), u)) st2).2.2.bad = false := by
      rw [hp.1, hbad2, hdone.bad_false, hdone.hop2BadAt_eq_false Q c]
      rfl
    have hst' := hsome st' t' i' m' u rfl
    rcases hp.2.2 with ⟨hst_eq, _⟩ | ⟨hst_upd, _⟩
    · exact ⟨hbad_next, hst_eq ▸ hst1 ▸ hdone.party_A, hst_eq ▸ hst1 ▸ hdone.party_B,
        hst_eq ▸ hst1 ▸ hdone.pos_epochs_A⟩
    · refine ⟨hbad_next, ?_, ?_, ?_⟩
      · rw [hst_upd, hst1]
        cases Q with
        | A => rw [Function.update_self]; exact hst'.1.trans hdone.party_A
        | B => rw [Function.update_of_ne (by decide)]; exact hdone.party_A
      · rw [hst_upd, hst1]
        cases Q with
        | A => rw [Function.update_of_ne (by decide)]; exact hdone.party_B
        | B => rw [Function.update_self]; exact hst'.1.trans hdone.party_B
      · rw [hst_upd, hst1]
        cases Q with
        | A => rw [Function.update_self]; exact hst'.2 hdone.pos_epochs_A
        | B => rw [Function.update_of_ne (by decide)]; exact hdone.pos_epochs_A

omit [SampleableType Pt] in
theorem runHop2_unif {ℓ : ℕ} {β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt) (u_q : unifSpec.Domain)
    (k : unifSpec.Range u_q →
      OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Impl P Dh encT decT qep s h (.inl u_q)).run st)).run tbl
      runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2) =
    (do
      let a ← (liftM (OracleSpec.query (spec := unifSpec) u_q) : ProbComp _)
      runHop2 P Dh encT decT qep s h (k a) st tbl) := by
  simp [hop2Impl,
    lazyImpl, QueryImpl.add_apply_inl,
    StateT.run_monadLift, monadLift_self]

omit [SampleableType Pt] in
theorem runHop2_hop2Lift' {ℓ : ℕ} {α β : Type}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (k : α → OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) β)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) :
    (do
      let z ← (simulateQ (lazyImpl (Pt := Pt)) ((hop2Lift m).run st)).run tbl
      runHop2 P Dh encT decT qep s h (k z.1.1) z.1.2 z.2) =
    (do
      let r ← m.run st.1
      runHop2 P Dh encT decT qep s h (k r.1) (r.2, st.2) tbl) := by
  simp []

omit [SampleableType Pt] in
theorem evalDist_runHop2_eq_zero_of_done {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hdone : Hop2LastDone P s st) :
    𝒟[runHop2 P Dh encT decT qep s h oa st tbl] {true} = 0 := by
  refine le_antisymm ?_ zero_le
  induction oa using OracleComp.inductionOn generalizing st tbl with
  | pure a =>
    rw [runHop2_pure, hdone.bad_false]
    simp
  | query_bind t k ih =>
    rw [runHop2_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2_unif]
      exact bind_le_of_support _ _ (measurableSet_singleton _) fun a _ => ih a st tbl hdone
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_le_of_support _ _ (measurableSet_singleton _) fun r hr =>
        ih r.1 (r.2, st.2) tbl (hdone.of_stSendStep
          (transmitR_support_stSendStep P decT encT qep y_tr st.1 r hr))
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_le_of_support _ _ (measurableSet_singleton _) fun r hr =>
        ih r.1 (r.2, st.2) tbl (hdone.of_stSendStep
          (challR_support_stSendStep P decT encT qep y_ch st.1 r hr))
    · dsimp only [hop2Impl]
      refine bind_le_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      by_cases hwin : st.1.win = true
      · unfold hop2Deliver at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ih none st tbl hdone
      · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
        cases hin : st.1.inTransit Q.other c with
        | none =>
          unfold hop2Deliver at hz
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hwinF, Bool.false_eq_true,
            ↓reduceIte, hin, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; exact ih none st tbl hdone
        | some r =>
          rw [hop2Deliver_run_eq_post P Dh encT decT s h Q c st r hwinF hin] at hz
          exact ih z.1.1 z.1.2 z.2 (hop2RecvWithPost_support_done P Dh encT decT s h Q c st tbl _
            (hop2DeliverPost_isHop2Post P s Q c (st.1.st Q) r) hdone z hz)
    · dsimp only [hop2Impl]
      refine bind_le_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
      · unfold hop2Inject at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ih none st tbl hdone
      · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
        rw [hop2Inject_run_eq_post P Dh encT decT qep s h Q c st hgF] at hz
        exact ih z.1.1 z.1.2 z.2 (hop2RecvWithPost_support_done P Dh encT decT s h Q c st tbl _
          (hop2InjectPost_isHop2Post P qep s Q c (st.1.st Q)) hdone z hz)
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_le_of_support _ _ (measurableSet_singleton _) fun r hr =>
        ih r.1 (r.2, st.2) tbl (hdone.of_stSendStep
          (corrR_support_stSendStep P decT encT y_corr st.1 r hr))

/-! ## Terminal hybrid active invariant and bound -/

def hop2HybLast (r : Ratchet.RootKey) (c_chall : BitVec 256) : Hop2Hyb Pt :=
  ⟨spkSwapHybridCount - 1, (r, c_chall), fun I => evalQuery (Input := Pt) (Tag := BitVec 256) I⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem hop2HybLast_k (r : Ratchet.RootKey) (c_chall : BitVec 256) :
    (hop2HybLast (Pt := Pt) r c_chall).k = 8 := rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
@[simp] theorem hop2HybLast_step (r : Ratchet.RootKey) (c_chall : BitVec 256) (I : Pt) :
    (hop2HybLast (Pt := Pt) r c_chall).step I = evalQuery (Input := Pt) (Tag := BitVec 256) I := rfl

inductive Hop2BobState (Dh : DHFun (BitVec 256) Pt) (k_A : ℕ) (aux : Hop2Aux Pt) : Prop
  | offChain :
      aux.idx .B = none →
      Hop2BobState Dh k_A aux
  | atEven :
      aux.idx .B = some (2 * k_A) →
      (∀ Q, aux.made.lookup (2 * k_A + 1, Q) = none) →
      (∀ Q ck, aux.made.lookup (2 * k_A, Q) = some ck →
        Q = Dh.dh (aux.coins .B) (Dh.dh (aux.coins .A) Dh.base)) →
      Hop2BobState Dh k_A aux
  | atNext :
      k_A < 4 →
      aux.idx .B = some (2 * k_A + 2) →
      (∀ Q ck, aux.made.lookup (2 * k_A + 1, Q) = some ck →
        Q = Dh.dh (aux.coins .A) (Dh.dh (aux.coins .B) Dh.base)) →
      Hop2BobState Dh k_A aux

omit [Zero Pt] [SampleableType Pt] in
theorem Hop2BobState.of_eq {Dh : DHFun (BitVec 256) Pt} {k_A : ℕ} {aux aux' : Hop2Aux Pt}
    (h : Hop2BobState Dh k_A aux)
    (hidx : aux'.idx .B = aux.idx .B)
    (hmade : aux'.made = aux.made)
    (hcoins : aux'.coins = aux.coins) :
    Hop2BobState Dh k_A aux' := by
  rcases h with ⟨h1⟩ | ⟨h1, h2, h3⟩ | ⟨hk, h1, h2⟩
  · exact .offChain (hidx.trans h1)
  · exact .atEven (hidx.trans h1) (fun Q => hmade ▸ h2 Q) (fun Q ck hck => by
      rw [hcoins]; exact h3 Q ck (hmade ▸ hck))
  · exact .atNext hk (hidx.trans h1) (fun Q ck hck => by
      rw [hcoins]; exact h2 Q ck (hmade ▸ hck))

/-- Active invariant for the terminal hybrid while Alice has performed `k_A ≤ 4` DH ratchet steps. -/
structure Hop2LastActiveAt {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (s : BitVec 256) (k_A : ℕ)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) : Prop where
  hkA : k_A ≤ 4
  bad_false : st.2.bad = false
  party_A : (st.1.st .A).party = .A
  party_B : (st.1.st .B).party = .B
  rem_A : (st.1.st .A).session.remoteIdentity = some P.idB
  loc_A : (st.1.st .A).session.localIdentity = P.idA
  chains_len_A : (st.1.st .A).session.receiverChains.length = k_A + 1
  epochs_len_A : (st.1.st .A).chainEpochs.length = k_A + 1
  pos_tail_A : ∀ e ∈ (st.1.st .A).chainEpochs.tail, 0 < e
  no_spk_A : NoKeyInChains (KeyPair.generate P.C s).publicKey (st.1.st .A).session.receiverChains
  idx_A : st.2.idx .A = some (2 * k_A + 1)
  lazy_odd : ∀ t Q, t % 2 = 1 → st.2.lazy.lookup (t, Q) = none
  tbl_empty_lt : k_A < 4 → tbl = []
  tbl_fresh : tbl.lookup (Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)) = none
  made_gt : ∀ t, 2 * k_A + 2 ≤ t → ∀ Q, st.2.made.lookup (t, Q) = none
  made_odd : ∀ Q ck, st.2.made.lookup (2 * k_A + 1, Q) = some ck →
    Q ≠ Dh.dh (st.2.coins .A) (Dh.dh s Dh.base)
  bob_state : Hop2BobState Dh k_A st.2

def Hop2LastInv {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (s : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) : Prop :=
  Hop2LastDone P s st ∨ ∃ k_A, Hop2LastActiveAt P Dh s k_A st tbl

omit [Zero Pt] [SampleableType Pt] in
theorem Hop2LastActiveAt.of_stSendStep {ℓ : ℕ} {P : Params Bytes PQC}
    {Dh : DHFun (BitVec 256) Pt} {s : BitVec 256} {k_A : ℕ}
    {st : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)}
    (h : Hop2LastActiveAt P Dh s k_A st tbl)
    {s₂ : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hstep : StSendStep P st.1 s₂) :
    Hop2LastActiveAt P Dh s k_A (s₂, st.2) tbl where
  hkA := h.hkA
  bad_false := h.bad_false
  party_A := (hstep.preserves_party_epochs P .A).1.trans h.party_A
  party_B := (hstep.preserves_party_epochs P .B).1.trans h.party_B
  rem_A := (hstep.preserves_party_epochs P .A).2.2.1.trans h.rem_A
  loc_A := (hstep.preserves_party_epochs P .A).2.2.2.1.trans h.loc_A
  chains_len_A :=
      (congrArg List.length (hstep.preserves_party_epochs P .A).2.2.2.2).trans h.chains_len_A
  epochs_len_A :=
      (congrArg List.length (hstep.preserves_party_epochs P .A).2.1).trans h.epochs_len_A
  pos_tail_A := by
    rw [(hstep.preserves_party_epochs P .A).2.1]
    exact h.pos_tail_A
  no_spk_A := by
    rw [(hstep.preserves_party_epochs P .A).2.2.2.2]
    exact h.no_spk_A
  idx_A := h.idx_A
  lazy_odd := h.lazy_odd
  tbl_empty_lt := h.tbl_empty_lt
  tbl_fresh := h.tbl_fresh
  made_gt := h.made_gt
  made_odd := h.made_odd
  bob_state := h.bob_state

theorem evictReceiverChains_append_length_lt (cs : List ReceiverChain) (x : ReceiverChain)
    (k_A : ℕ) (hlen : cs.length = k_A + 1) (hk : k_A < 4) :
    (RatchetState.evictReceiverChains (cs ++ [x])).length = (k_A + 1) + 1 := by
  unfold RatchetState.evictReceiverChains maxReceiverChains
  simp [List.length_drop, List.length_append, hlen]
  omega

theorem evictReceiverChains_append_length_four (cs : List ReceiverChain) (x : ReceiverChain)
    (hlen : cs.length = 4 + 1) :
    (RatchetState.evictReceiverChains (cs ++ [x])).length = 5 := by
  unfold RatchetState.evictReceiverChains maxReceiverChains
  simp [List.length_append, hlen]

theorem chainEpochs_step_lt (l : List ℕ) (e₀ : ℕ) (k_A : ℕ)
    (hlen : l.length = k_A + 1)
    (htail : ∀ e ∈ l.tail, 0 < e) (he₀ : 0 < e₀) :
    let l' := (l ++ [e₀]).drop ((l.length + 1) - ((k_A + 1) + 1))
    l'.length = (k_A + 1) + 1 ∧ ∀ e ∈ l'.tail, 0 < e := by
  have hsub : (l.length + 1) - ((k_A + 1) + 1) = 0 := by omega
  dsimp only []
  rw [hsub, List.drop_zero]
  refine ⟨by simp [hlen], ?_⟩
  cases l with
  | nil => simp at hlen
  | cons hd tl =>
    simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_singleton] at htail ⊢
    rintro e (he | rfl)
    · exact htail e he
    · exact he₀

theorem chainEpochs_step_four (l : List ℕ) (e₀ : ℕ)
    (hlen : l.length = 4 + 1)
    (htail : ∀ e ∈ l.tail, 0 < e) (he₀ : 0 < e₀) :
    ∀ e ∈ (l ++ [e₀]).drop ((l.length + 1) - 5), 0 < e := by
  have hsub : (l.length + 1) - 5 = 1 := by omega
  rw [hsub]
  cases l with
  | nil => simp at hlen
  | cons hd tl =>
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero,
      List.mem_append, List.mem_singleton] at htail ⊢
    rintro e (he | rfl)
    · exact htail e he
    · exact he₀

omit [Zero Pt] [SampleableType Pt] in
theorem evalQuery_support_lookup_eq_none (Q' Q₀ : Pt) (tbl : List (Pt × BitVec 256))
    (hne : Q' ≠ Q₀) (hlook : tbl.lookup Q₀ = none)
    (z : BitVec 256 × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      (evalQuery (Input := Pt) (Tag := BitVec 256) Q')).run tbl)) :
    z.2.lookup Q₀ = none := by
  rw [simulateQ_lazyImpl_evalQuery] at hz
  unfold lazyStep at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hq : tbl.lookup Q' with
  | some u =>
    rw [hq] at hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hlook
  | none =>
    rw [hq] at hz
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure,
      pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨u, _, rfl⟩
    have hbeq : (Q₀ == Q') = false := beq_eq_false_iff_ne.mpr hne.symm
    simp [List.lookup, hbeq, hlook]

omit [SampleableType Pt] in
theorem hop2Recv_run_at_nine {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (r : Ratchet.RootKey) (c_chall : BitVec 256)
    (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) (st : Hop2State Pt ℓ)
    (msg : SignalMessage) (T : Pt) (sc : SenderChain)
    (hidx : st.2.idx g.party = some 9)
    (htry : SignalMessage.tryFrom P.codec c = .ok msg)
    (hfind :
        (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
        true)
    (hdec : decT msg.senderRatchetKey = some T)
    (hT : ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey))
    (hsc : g.session.senderChain = some sc)
    (hQ0 : Dh.dh (st.2.coins g.party) T ≠ 0) :
    (hop2Recv (ℓ := ℓ) P Dh encT decT (hop2HybLast r c_chall) g c rc).run (withLazy [] st) =
      (fun u => (hop2OffChainOut P ℓ g msg sc rc u, withLazy [] st)) <$>
        evalQuery (Input := Pt) (Tag := BitVec 256) (Dh.dh (st.2.coins g.party) T) := by
  unfold hop2Recv hop2DH hop2RecvHalf hop2SendHalf hop2OffChainOut
  have hidx' : (withLazy [] st).2.idx g.party = some 9 := hidx
  have hcoins' : (withLazy [] st).2.coins g.party = st.2.coins g.party := rfl
  have hnotle : ¬ (9 ≤ (hop2HybLast (Pt := Pt) r c_chall).k) := by simp
  simp only [htry, StateT.run_bind, StateT.run_get, pure_bind, hidx', hfind, ↓reduceIte,
    hdec, hT, hsc, hcoins', hQ0, hnotle, hop2HybLast_step, stateT_lift_run_hop2,
    map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun u => ?_
  dsimp only [Function.comp_apply]
  cases rootCreateChain P.C (Ratchet.rootExpand P.C.F (keyToBytes32 u)).1
    msg.senderRatchetKey (KeyPair.generate P.C rc).privateKey with
  | error _ => simp [StateT.run_pure]
  | ok p2 =>
    rcases p2 with ⟨rk2, ck2⟩
    simp only [pure_bind]
    rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party)
      msg .whisper rc _ with ⟨r_tr, s_out⟩
    cases r_tr <;> simp [StateT.run_pure]

omit [SampleableType Pt] in
theorem hop2RecvHalf_even_support {ℓ : ℕ} (P : Params Bytes PQC)
    (r : Ratchet.RootKey) (c_chall : BitVec 256)
    (idx : Option ℕ) (rk : Ratchet.RootKey) (their : PublicKey) (our : PrivateKey) (Q_B : Pt)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (heven : idx = none ∨ ∃ t, idx = some t ∧ t % 2 = 0 ∧ t ≤ 8)
    (z : (Option (Option ℕ × Ratchet.RootKey × BitVec 256) × Hop2State Pt ℓ) × List (Pt × BitVec
        256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2RecvHalf P (hop2HybLast r c_chall) idx rk their our Q_B).run st)).run tbl)) :
    z.1.2.1 = st.1 ∧
    z.1.2.2.bad = st.2.bad ∧
    z.1.2.2.idx = st.2.idx ∧
    z.1.2.2.coins = st.2.coins ∧
    z.1.2.2.made = st.2.made ∧
    (∀ t' Q', t' % 2 = 1 → z.1.2.2.lazy.lookup (t', Q') = st.2.lazy.lookup (t', Q')) ∧
    z.2 = tbl ∧
    ∀ idx1 rkM ckR, z.1.1 = some (idx1, rkM, ckR) →
      idx1 = none ∨ ∃ t, idx = some t ∧ st.2.made.lookup (t, Q_B) = some ckR ∧ idx1 = some (t +
          1) := by
  unfold hop2RecvHalf at hz
  rcases heven with rfl | ⟨t, rfl, hmod, htle⟩
  · dsimp only [] at hz
    cases hcc : rootCreateChain P.C rk their our with
    | error _ =>
      rw [hcc] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, rfl, fun _ _ _ h => by cases h⟩
    | ok p =>
      rcases p with ⟨rk', ck⟩
      rw [hcc] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, rfl, fun idx1 _ _ h => ?_⟩
      injection h with htuple
      rcases Prod.mk.inj htuple with ⟨rfl, _⟩
      exact Or.inl rfl
  · dsimp only [] at hz
    by_cases hQ0 : Q_B = 0
    · simp only [hQ0, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, rfl, fun _ _ _ h => by cases h⟩
    · have htle' : t ≤ (hop2HybLast (Pt := Pt) r c_chall).k := htle
      simp only [hQ0, ↓reduceIte, htle', StateT.run_bind, StateT.run_get, pure_bind] at hz
      cases hmade : st.2.made.lookup (t, Q_B) with
      | some ck =>
        rw [hmade] at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, rfl, fun idx1 rkM ckR h => ?_⟩
        injection h with htuple
        rcases Prod.mk.inj htuple with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨_, rfl⟩
        exact Or.inr ⟨t, rfl, hmade, rfl⟩
      | none =>
        rw [hmade] at hz
        unfold hop2Lazy at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, bind_assoc] at hz
        cases hlazy : st.2.lazy.lookup (t, Q_B) with
        | some u =>
          rw [hlazy] at hz
          simp only [StateT.run_pure] at hz
          subst hz
          refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, rfl, fun idx1 _ _ h => ?_⟩
          injection h with htuple
          rcases Prod.mk.inj htuple with ⟨rfl, _⟩
          exact Or.inl rfl
        | none =>
          rw [hlazy] at hz
          simp only [stateT_lift_run_hop2, StateT.run_bind, StateT.run_set, StateT.run_pure,
            bind_assoc, pure_bind, simulateQ_bind, simulateQ_lazyImpl_hop2Unif,
            stateT_lift_probComp_run, simulateQ_pure, MonadAttach.mem_support_bind,
            support_pure, Set.mem_singleton_iff] at hz
          rcases hz with ⟨u, _, rfl⟩
          refine ⟨rfl, rfl, rfl, rfl, rfl, fun t' Q' hodd => ?_, rfl, fun idx1 _ _ h => ?_⟩
          · have hne : (t', Q') ≠ (t, Q_B) := by
              intro heq
              rcases Prod.mk.inj heq with ⟨rfl, _⟩
              omega
            have hbeq : ((t', Q') == (t, Q_B)) = false := beq_eq_false_iff_ne.mpr hne
            simp [List.lookup, hbeq]
          · injection h with htuple
            rcases Prod.mk.inj htuple with ⟨rfl, _⟩
            exact Or.inl rfl

omit [SampleableType Pt] in
theorem hop2SendHalf_support {P : Params Bytes PQC}
    (r : Ratchet.RootKey) (c_chall : BitVec 256)
    (idx1 : Option ℕ) (rkM : Ratchet.RootKey) (their : PublicKey) (our' : PrivateKey) (Q' : Pt)
    (tbl : List (Pt × BitVec 256))
    (z : Option (Option ℕ × Ratchet.RootKey × BitVec 256 × Option ((ℕ × Pt) × BitVec 256)) ×
      List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      (hop2SendHalf P (hop2HybLast r c_chall) idx1 rkM their our' Q')).run tbl)) :
    (idx1 = none →
      z.2 = tbl ∧ ∀ idx2 rk2 ckS pend, z.1 = some (idx2, rk2, ckS, pend) →
        idx2 = none ∧ pend = none) ∧
    (∀ j, idx1 = some j → j ≤ 8 →
      z.2 = tbl ∧ ∀ idx2 rk2 ckS pend, z.1 = some (idx2, rk2, ckS, pend) →
        idx2 = some (j + 1) ∧ ∃ ck, pend = some ((j, Q'), ck)) ∧
    (∀ j, idx1 = some j → 8 < j →
      (∀ Q₀, Q' ≠ Q₀ → tbl.lookup Q₀ = none → z.2.lookup Q₀ = none) ∧
      ∀ idx2 rk2 ckS pend, z.1 = some (idx2, rk2, ckS, pend) →
        idx2 = none ∧ pend = none) := by
  refine ⟨fun hnone => ?_, fun j hj hjle => ?_, fun j hj hjgt => ?_⟩
  · subst hnone
    unfold hop2SendHalf at hz
    dsimp only [] at hz
    cases hcc : rootCreateChain P.C rkM their our' with
    | error _ =>
      rw [hcc] at hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, fun _ _ _ _ h => by cases h⟩
    | ok p =>
      rcases p with ⟨rk', ck⟩
      rw [hcc] at hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨rfl, fun idx2 rk2 ckS pend h => ?_⟩
      injection h with htuple
      rcases Prod.mk.inj htuple with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨_, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩
  · subst hj
    unfold hop2SendHalf at hz
    dsimp only [] at hz
    by_cases hQ0 : Q' = 0
    · simp only [hQ0, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, fun _ _ _ _ h => by cases h⟩
    · simp only [hQ0, ↓reduceIte, hop2HybLast_k] at hz
      by_cases hjlt : j < 8
      · simp only [hjlt, ↓reduceIte, simulateQ_bind, simulateQ_lazyImpl_hop2Unif,
          StateT.run_bind, stateT_lift_probComp_run, simulateQ_pure, StateT.run_pure,
          bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
        rcases hz with ⟨ck, _, rfl⟩
        refine ⟨rfl, fun idx2 rk2 ckS pend h => ?_⟩
        injection h with htuple
        rcases Prod.mk.inj htuple with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨_, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨_, rfl⟩
        exact ⟨rfl, ck, rfl⟩
      · have hjeq : j = 8 := by omega
        subst hjeq
        simp only [lt_self_iff_false, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨rfl, fun idx2 rk2 ckS pend h => ?_⟩
        injection h with htuple
        rcases Prod.mk.inj htuple with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨_, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨_, rfl⟩
        exact ⟨rfl, _, rfl⟩
  · subst hj
    unfold hop2SendHalf at hz
    dsimp only [] at hz
    by_cases hQ0 : Q' = 0
    · simp only [hQ0, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨fun _ _ hlook => hlook, fun _ _ _ _ h => by cases h⟩
    · have hjlt : ¬ (j < 8) := by omega
      have hjne : j ≠ 8 := by omega
      simp only [hQ0, ↓reduceIte, hop2HybLast_k, hjlt, hjne, hop2HybLast_step,
        simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨⟨u, tbl2⟩, hz_eval, rfl⟩
      refine ⟨fun Q₀ hne hlook => evalQuery_support_lookup_eq_none Q' Q₀ tbl hne hlook (u,
          tbl2) hz_eval,
        fun idx2 rk2 ckS pend h => ?_⟩
      injection h with htuple
      rcases Prod.mk.inj htuple with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨_, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩

theorem bind_eq_of_support {α β : Type} [MeasurableSpace β] (mx : ProbComp α)
    (f : α → ProbComp β) {E : Set β} (hE : MeasurableSet E) {r : ℝ≥0∞}
    (h : ∀ a ∈ support mx, 𝒟[f a] E = r) : 𝒟[mx >>= f] E = r := by
  refine le_antisymm (bind_le_of_support mx f hE fun a ha => le_of_eq (h a ha)) ?_
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using ge_of_eq (h a (by simp))
  | query_bind t k ih =>
    rw [bind_assoc, evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply hE Measurable.of_discrete.aemeasurable]
    calc r = ∫⁻ _u, r ∂𝒟[(OracleSpec.query (spec := unifSpec) t : ProbComp _)] := by
          rw [MeasureTheory.lintegral_const, evalDist_apply_univ_eq_one, mul_one]
      _ ≤ _ := MeasureTheory.lintegral_mono fun u => ih u fun a ha =>
          h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

theorem bind_le_add_of_support {α : Type} (mx : ProbComp α)
    (f g : α → ProbComp Bool) (d : ℝ≥0∞)
    (h : ∀ a ∈ support mx, 𝒟[f a] {true} ≤ 𝒟[g a] {true} + d) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} + d :=
  Computational.Proofs.GameHop.Advantage.evalDist_bind_le_add_prob_of_support mx f g
    (measurableSet_singleton true) h

omit [SampleableType Pt] in
theorem hop2RecvWithPost_support_bad_true {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (h : Hop2Hyb Pt) (Q : Party) (c : Bytes)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsHop2Post P s Q c (st.1.st Q) post)
    (hbad : st.2.bad = true)
    (z : (Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt)) (do
      let rc ← hop2Unif (Pt := Pt)
      let res ← (hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st
      return post res.1 res.2)).run tbl)) :
    z.1.2.2.bad = true := by
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
    stateT_lift_probComp_run, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨rc, _, ⟨⟨r_out, st2⟩, tbl2⟩, hz_rec, hz_pure⟩
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz_pure
  subst hz_pure
  have hrec := hop2Recv_support_done P Dh encT decT h (st.1.st Q) c rc st tbl _ hz_rec
  cases r_out with
  | none =>
    rw [hpost.on_none]
    exact hrec.2.1.trans hbad
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    have hp := (hpost.on_some st' t' i' m' u st2).1
    rw [hp, hrec.2.1, hbad, Bool.true_or]

omit [SampleableType Pt] in
theorem evalDist_runHop2_eq_one_of_bad_true {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hbad : st.2.bad = true) :
    𝒟[runHop2 P Dh encT decT qep s h oa st tbl] {true} = 1 := by
  induction oa using OracleComp.inductionOn generalizing st tbl with
  | pure a =>
    rw [runHop2_pure, hbad]
    simp
  | query_bind t k ih =>
    rw [runHop2_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2_unif]
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun a _ => ih a st tbl hbad
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r _ => ih r.1 (r.2,
          st.2) tbl hbad
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r _ => ih r.1 (r.2,
          st.2) tbl hbad
    · dsimp only [hop2Impl]
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      by_cases hwin : st.1.win = true
      · unfold hop2Deliver at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ih none st tbl hbad
      · have hwinF : st.1.win = false := Bool.eq_false_iff.mpr hwin
        cases hin : st.1.inTransit Q.other c with
        | none =>
          unfold hop2Deliver at hz
          simp only [StateT.run_bind, StateT.run_get, pure_bind, hwinF, Bool.false_eq_true,
            ↓reduceIte, hin, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; exact ih none st tbl hbad
        | some r =>
          rw [hop2Deliver_run_eq_post P Dh encT decT s h Q c st r hwinF hin] at hz
          exact ih z.1.1 z.1.2 z.2 (hop2RecvWithPost_support_bad_true P Dh encT decT s h Q c st tbl
              _
            (hop2DeliverPost_isHop2Post P s Q c (st.1.st Q) r) hbad z hz)
    · dsimp only [hop2Impl]
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      by_cases hg : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
          !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
      · unfold hop2Inject at hz
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hg, ↓reduceIte,
          StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ih none st tbl hbad
      · have hgF : (st.1.win || (st.1.inTransit Q.other c).isSome || !(st.1.safeInj 3) ||
            !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
        rw [hop2Inject_run_eq_post P Dh encT decT qep s h Q c st hgF] at hz
        exact ih z.1.1 z.1.2 z.2 (hop2RecvWithPost_support_bad_true P Dh encT decT s h Q c st tbl _
          (hop2InjectPost_isHop2Post P qep s Q c (st.1.st Q)) hbad z hz)
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r _ => ih r.1 (r.2,
          st.2) tbl hbad

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitR_support_win_true {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (x : Party × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hwin : st.win = true) :
    ∀ z ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st),
      z.2.win = true := by
  rcases x with ⟨Q, m, r⟩
  intro z hz
  unfold SM.transmitR SM.transmitImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challR_support_win_true {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hwin : st.win = true) :
    ∀ z ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st),
      z.2.win = true := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  intro z hz
  unfold SM.challR SM.challImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrR_support_win_true {ℓ : ℕ}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (Q : Party)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hwin : st.win = true) :
    ∀ z ∈ support ((SM.corrR (configRefuseEarlyBobCorr decT encT) Q).run st),
      z.2.win = true := by
  intro z hz
  unfold SM.corrR at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.true_or, ↓reduceIte,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact hwin

omit [SampleableType Pt] in
theorem evalDist_runHop2_eq_of_win_true {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hwin : st.1.win = true) :
    𝒟[runHop2 P Dh encT decT qep s h oa st tbl] {true} =
      𝒟[(pure st.2.bad : ProbComp Bool)] {true} := by
  induction oa using OracleComp.inductionOn generalizing st tbl with
  | pure a =>
    rw [runHop2_pure]
  | query_bind t k ih =>
    rw [runHop2_bind_query]
    rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
    · rw [runHop2_unif]
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun a _ => ih a st tbl hwin
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr =>
        ih r.1 (r.2, st.2) tbl (transmitR_support_win_true P decT encT qep y_tr st.1 hwin r hr)
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr =>
        ih r.1 (r.2, st.2) tbl (challR_support_win_true P decT encT qep y_ch st.1 hwin r hr)
    · dsimp only [hop2Impl]
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      unfold hop2Deliver at hz
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ih none st tbl hwin
    · dsimp only [hop2Impl]
      refine bind_eq_of_support _ _ (measurableSet_singleton _) fun z hz => ?_
      unfold hop2Inject at hz
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.true_or, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ih none st tbl hwin
    · dsimp only [hop2Impl]
      rw [runHop2_hop2Lift']
      exact bind_eq_of_support _ _ (measurableSet_singleton _) fun r hr =>
        ih r.1 (r.2, st.2) tbl (corrR_support_win_true decT encT y_corr st.1 hwin r hr)

/-- Absorbing state condition under which `runHop2` preserves `st.2.bad` with probability `1`. -/
def Hop2Absorbed {ℓ : ℕ} (st : Hop2State Pt ℓ) : Prop :=
  st.2.bad = true ∨ st.1.win = true ∨
    ((st.1.st .A).party = .A ∧ (st.1.st .B).party = .B ∧
      ∀ e ∈ (st.1.st .A).chainEpochs, 0 < e)

omit [SampleableType Pt] in
theorem evalDist_runHop2_of_absorbed {ℓ : ℕ}
    (P : Params Bytes PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (s : BitVec 256)
    (h : Hop2Hyb Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (habs : Hop2Absorbed st) :
    𝒟[runHop2 P Dh encT decT qep s h oa st tbl] {true} =
      𝒟[(pure st.2.bad : ProbComp Bool)] {true} := by
  rcases habs with hbad | hwin | ⟨hpA, hpB, hpos⟩
  · rw [evalDist_runHop2_eq_one_of_bad_true P Dh encT decT qep s h oa st tbl hbad, hbad]
    simp
  · exact evalDist_runHop2_eq_of_win_true P Dh encT decT qep s h oa st tbl hwin
  · cases hbad : st.2.bad with
    | true =>
      rw [evalDist_runHop2_eq_one_of_bad_true P Dh encT decT qep s h oa st tbl hbad]
      simp
    | false =>
      rw [evalDist_runHop2_eq_zero_of_done P Dh encT decT qep s h oa st tbl ⟨hbad, hpA, hpB, hpos⟩]
      simp

end Hop2Coupling
end CryptoVerification.E2E.SpkHop1
