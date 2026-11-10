/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkHop1F

/-!
# Hop 2 Window Invariant and Phase 2 Coupling

Defines the receiver-chain window invariant `Hop2WindowInv`, proves its preservation across session
steps, and bounds Phase 2 of the Hop 2 hybrid transition (`evalDist_runHop2_phase2_le_createColl`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.E2E.SpkHop1

open CryptoGames CryptoGames.SM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalSession CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Relabel CryptoVerification.E2E.Relabel.GameEq

section Hop2Coupling

open CryptoGames.CKA CryptoGames.LibsignalSM.Proofs.Refinement
open HMAC HKDF MACScheme

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {PQC : Type} [SampleableType PQC]

def Hop2WindowStateA {ℓ : ℕ} (P : Params Bytes PQC)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) : Prop :=
  let csA := (s.st .A).session.receiverChains
  let csB := (s.st .B).session.receiverChains
  let nA := csA.length
  s.epoch .B ≤ 2 * nA - 2 ∧
  (∃ scA, (s.st .A).session.senderChain = some scA ∧
    NoKeyInChains scA.ratchetKey.publicKey csB) ∧
  (∀ r ∈ s.trans, r.pos.sender = .A →
    r.pos.epoch ≤ 2 * nA - 2 ∨
    (∀ msg, SignalMessage.tryFrom P.codec r.ct = .ok msg →
      NoKeyInChains msg.senderRatchetKey csB))

def Hop2WindowStateB {ℓ : ℕ} (P : Params Bytes PQC)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) : Prop :=
  let csA := (s.st .A).session.receiverChains
  let nA := csA.length
  (∃ scB, (s.st .B).session.senderChain = some scB ∧
    NoKeyInChains scB.ratchetKey.publicKey csA) ∧
  (∀ r ∈ s.trans, r.pos.sender = .B →
    r.pos.epoch ≤ 2 * nA - 2 ∨
    (∀ msg, SignalMessage.tryFrom P.codec r.ct = .ok msg →
      NoKeyInChains msg.senderRatchetKey csA))

structure Hop2WindowCore {ℓ : ℕ} (P : Params Bytes PQC)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) : Prop where
  tL_none : s.tL = none
  comp_nil : s.comp = []
  nA_pos : 1 ≤ (s.st .A).session.receiverChains.length
  nA_le : (s.st .A).session.receiverChains.length ≤ 5
  csB_le : (s.st .B).session.receiverChains.length ≤ 5
  epochs_len_A : (s.st .A).chainEpochs.length = (s.st .A).session.receiverChains.length
  pos_tail_A : ∀ e ∈ (s.st .A).chainEpochs.tail, 0 < e
  epA_le : s.epoch .A ≤ 2 * (s.st .A).session.receiverChains.length - 1
  epB_le : s.epoch .B ≤ 2 * (s.st .A).session.receiverChains.length
  trans_le : ∀ r ∈ s.trans, r.pos.epoch ≤ s.epoch r.pos.sender
  phase : Hop2WindowStateA P s ∨ Hop2WindowStateB P s

def Hop2WindowInv {ℓ : ℕ} (P : Params Bytes PQC)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) : Prop :=
  (∀ e ∈ (s.st .A).chainEpochs, 0 < e) ∨ Hop2WindowCore P s

theorem hop2WindowInv_init {ℓ : ℕ} (P : Params Bytes PQC)
    (b : Bool) (rk1 : Ratchet.RootKey) (ck0 x alice pqr ck1 : BitVec 256) :
    let spk := (KeyPair.generate P.C x).publicKey
    let sessA := ((SessionState.new currentVersion P.idA P.idB rk1
      (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
      (KeyPair.generate P.C alice) ⟨ck1, 0⟩
    let stA : GhostState Bytes := ⟨.A, sessA.setUnacknowledgedPreKeyMessage, 0, [0]⟩
    let stB := P.initB ⟨0, ck0, x, alice, pqr⟩
    let initSt : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes :=
      { st := fun Q => match Q with | .A => stA | .B => stB, b := b }
    Hop2WindowInv P initSt := by
  intro spk sessA stA stB initSt
  refine Or.inr ⟨rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
  · exact le_rfl
  · change 1 ≤ 5; decide
  · exact Nat.zero_le 5
  · intro e he; cases he
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · intro r hr; cases hr
  · exact Nat.zero_le _
  · refine ⟨⟨KeyPair.generate P.C alice, ⟨ck1, 0⟩⟩, rfl, ?_⟩
    intro c hc; cases hc
  · intro r hr; cases hr

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrOK_eq_false_of_epoch_A_lt_10 {ℓ : ℕ}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Q : Party) (h : s.epoch .A < 10) :
    (configRefuseEarlyBobCorr decT encT).corrOK s Q = false := by
  dsimp only [configRefuseEarlyBobCorr, configR1OnCurve, SM.configR1]
  cases Q <;> simp [SM.noAliceCorrWhileAliceBelowEpoch10, noBobCorrWhileAliceBelowEpoch10, h]

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem hop2WindowCore_of_not_absorbed {ℓ : ℕ} {P : Params Bytes PQC}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {st : Hop2State Pt ℓ}
    (hinv : Hop2GameInv P decT encT st)
    (hwin : Hop2WindowInv P st.1)
    (hnabs : ¬ Hop2Absorbed st) :
    Hop2WindowCore P st.1 := by
  rcases hwin with hpos | hcore
  · exfalso
    exact hnabs (Or.inr (Or.inr ⟨hinv.party_eq .A, hinv.party_eq .B, hpos⟩))
  · exact hcore

theorem epMgmt_of_tL_none {ℓ : ℕ}
    {s s₁ : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    {qep : ℕ} {Q : Party} {bad : Bool}
    (htL : s.tL = none)
    (hep : s.epMgmt 3 qep Q bad = some s₁) :
    s₁.st = s.st ∧ s₁.tL = none ∧ s₁.comp = s.comp ∧ s₁.trans = s.trans ∧
    (∀ R, s.epoch R ≤ s₁.epoch R) ∧
    (∀ R, R ≠ Q → s₁.epoch R = s.epoch R) ∧
    (s₁.epoch Q = s.epoch Q ∨ (Q.sendsIn (s.epoch Q + 1) = true ∧ s₁.epoch Q = s.epoch Q + 1)) := by
  unfold SM.GameState.epMgmt at hep
  have hsafe : s.safeCh 3 Q = true := by
    unfold SM.GameState.safeCh SM.healedBy; simp [htL]
  by_cases hsends : Q.sendsIn (s.epoch Q + 1) = true
  · simp only [hsends, ↓reduceIte] at hep
    split at hep
    · cases hep
    · simp only [hsafe, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq] at hep
      subst hep
      refine ⟨rfl, htL, rfl, rfl, ?_, ?_, Or.inr ⟨hsends, Function.update_self Q (s.epoch Q +
          1) s.epoch⟩⟩
      · intro R
        dsimp only []
        by_cases hR : R = Q
        · subst hR; rw [Function.update_self]; omega
        · rw [Function.update_of_ne hR]
      · intro R hR
        exact Function.update_of_ne hR (s.epoch Q + 1) s.epoch
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hep
    split at hep
    · cases hep
    · simp only [Option.some.injEq] at hep
      subst hep
      exact ⟨rfl, htL, rfl, rfl, fun _ => le_rfl, fun _ _ => rfl, Or.inl rfl⟩

theorem sendsIn_A_succ_le {e nA : ℕ} (hnA : 1 ≤ nA) (hle : e ≤ 2 * nA - 1)
    (hsends : Party.A.sendsIn (e + 1) = true) :
    e + 1 ≤ 2 * nA - 1 := by
  unfold Party.sendsIn at hsends
  simp only [beq_iff_eq] at hsends
  omega

theorem sendsIn_B_succ_le_even {e m : ℕ} (hle : e ≤ 2 * m)
    (hsends : Party.B.sendsIn (e + 1) = true) :
    e + 1 ≤ 2 * m := by
  unfold Party.sendsIn at hsends
  simp only [beq_iff_eq] at hsends
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem record_send_preserves_hop2WindowInv {ℓ : ℕ} (P : Params Bytes PQC)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {st : Hop2State Pt ℓ}
    (hinv : Hop2GameInv P decT encT st)
    (hwin : Hop2WindowInv P st.1)
    {qep : ℕ} {Q : Party} {m : CBC.Plain ℓ} {coins : PQC} {bad isChall : Bool}
    {s₁ : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes}
    (hep : st.1.epMgmt 3 qep Q bad = some s₁) :
    Hop2WindowInv P
      (s₁.record 3 Q ((sessionSchemeU P ℓ).send (s₁.st Q) m coins).1
        ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, ((sessionSchemeU P ℓ).send (s₁.st Q) m coins).2⟩
        isChall) := by
  rcases hwin with hpos | hcore
  · obtain ⟨hst1, _⟩ := GameEq.epMgmt_st_trans hep
    left
    unfold SM.GameState.record; dsimp only []; rw [hst1]
    by_cases hQ : Party.A = Q
    · subst hQ; rw [Function.update_self, (sessionSchemeU_send_props P (st.1.st .A) m coins).2.1]
      exact hpos
    · rw [Function.update_of_ne hQ]; exact hpos
  · obtain ⟨hst1, htL1, hcomp1, htr1, hep_le, hep_ne, hep_Q⟩ :=
      epMgmt_of_tL_none hcore.tL_none hep
    have hsafe1 : s₁.safeCh 3 Q = true := by
      unfold SM.GameState.safeCh SM.healedBy; simp [htL1]
    set out := (sessionSchemeU P ℓ).send (st.1.st Q) m coins
    set r_new : SM.Record (CBC.Plain ℓ) Bytes := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, out.2⟩
    set s' := s₁.record 3 Q out.1 r_new isChall
    rw [hst1]
    change Hop2WindowInv P s'
    have hrc_eq : ∀ R, (s'.st R).session.receiverChains = (st.1.st R).session.receiverChains := by
      intro R
      dsimp only [s', out, SM.GameState.record]; rw [hst1]
      by_cases hR : R = Q
      · subst hR; rw [Function.update_self]
        exact (sessionSchemeU_send_props P (st.1.st R) m coins).2.2.2.2
      · rw [Function.update_of_ne hR]
    have hce_eq : (s'.st .A).chainEpochs = (st.1.st .A).chainEpochs := by
      dsimp only [s', out, SM.GameState.record]; rw [hst1]
      by_cases hQ : Party.A = Q
      · subst hQ; rw [Function.update_self]
        exact (sessionSchemeU_send_props P (st.1.st .A) m coins).2.1
      · rw [Function.update_of_ne hQ]
    have hepA_s1 : s₁.epoch .A ≤ 2 * (st.1.st .A).session.receiverChains.length - 1 := by
      cases Q with
      | A =>
        rcases hep_Q with heq | ⟨hsends, heq⟩
        · rw [heq]; exact hcore.epA_le
        · rw [heq]; exact sendsIn_A_succ_le hcore.nA_pos hcore.epA_le hsends
      | B =>
        rw [hep_ne .A (by decide)]; exact hcore.epA_le
    have hepB_s1 : s₁.epoch .B ≤ 2 * (st.1.st .A).session.receiverChains.length := by
      cases Q with
      | A =>
        rw [hep_ne .B (by decide)]; exact hcore.epB_le
      | B =>
        rcases hep_Q with heq | ⟨hsends, heq⟩
        · rw [heq]; exact hcore.epB_le
        · rw [heq]; exact sendsIn_B_succ_le_even hcore.epB_le hsends
    right
    refine ⟨htL1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [s', SM.GameState.record]
      simp only [hsafe1, ↓reduceIte, hcomp1, hcore.comp_nil]
    · rw [hrc_eq .A]; exact hcore.nA_pos
    · rw [hrc_eq .A]; exact hcore.nA_le
    · rw [hrc_eq .B]; exact hcore.csB_le
    · rw [hce_eq, hrc_eq .A]; exact hcore.epochs_len_A
    · rw [hce_eq]; exact hcore.pos_tail_A
    · rw [hrc_eq .A]; exact hepA_s1
    · rw [hrc_eq .A]; exact hepB_s1
    · intro r hr
      dsimp only [s', SM.GameState.record] at hr ⊢
      rcases List.mem_cons.mp hr with rfl | hr_old
      · exact le_rfl
      · rw [htr1] at hr_old
        exact (hcore.trans_le r hr_old).trans (hep_le r.pos.sender)
    · rcases hcore.phase with ⟨hB_le, ⟨scA, hscA, hnoA⟩, htrA⟩ | ⟨⟨scB, hscB, hnoB⟩, htrB⟩
      · left
        unfold Hop2WindowStateA; dsimp only []
        rw [hrc_eq .A, hrc_eq .B]
        refine ⟨?_, ?_, ?_⟩
        · change s₁.epoch .B ≤ 2 * (st.1.st .A).session.receiverChains.length - 2
          cases Q with
          | A => rw [hep_ne .B (by decide)]; exact hB_le
          | B =>
            rcases hep_Q with heq | ⟨hsends, heq⟩
            · rw [heq]; exact hB_le
            · rw [heq]
              have h2 : 2 * (st.1.st .A).session.receiverChains.length - 2 =
                  2 * ((st.1.st .A).session.receiverChains.length - 1) := by omega
              rw [h2] at hB_le ⊢
              exact sendsIn_B_succ_le_even hB_le hsends
        · dsimp only [s', out, SM.GameState.record]; rw [hst1]
          cases Q with
          | A =>
            rw [Function.update_self]
            obtain ⟨sck', hsck'⟩ := send_preserves_senderChain_ratchetKey P (st.1.st .A)
              scA.ratchetKey scA.chainKey m.toList coins hscA
            exact ⟨⟨scA.ratchetKey, sck'⟩, hsck', hnoA⟩
          | B =>
            rw [Function.update_of_ne (by decide)]
            exact ⟨scA, hscA, hnoA⟩
        · intro r hr hsender
          dsimp only [s', SM.GameState.record] at hr
          rcases List.mem_cons.mp hr with rfl | hr_old
          · dsimp only [r_new] at hsender ⊢
            subst hsender
            right
            intro msg htry
            obtain ⟨sc, hsc, hkey⟩ :=
              send_tryFrom_senderRatchetKey P hcodec hL (st.1.st .A) (hinv.sender_inv .A).1 m coins
                  msg htry
            rw [hscA] at hsc; injection hsc with hsc_eq; subst hsc_eq
            rw [hkey]; exact hnoA
          · rw [htr1] at hr_old
            exact htrA r hr_old hsender
      · right
        unfold Hop2WindowStateB; dsimp only []
        rw [hrc_eq .A]
        refine ⟨?_, ?_⟩
        · dsimp only [s', out, SM.GameState.record]; rw [hst1]
          cases Q with
          | A =>
            rw [Function.update_of_ne (by decide)]
            exact ⟨scB, hscB, hnoB⟩
          | B =>
            rw [Function.update_self]
            obtain ⟨sck', hsck'⟩ := send_preserves_senderChain_ratchetKey P (st.1.st .B)
              scB.ratchetKey scB.chainKey m.toList coins hscB
            exact ⟨⟨scB.ratchetKey, sck'⟩, hsck', hnoB⟩
        · intro r hr hsender
          dsimp only [s', SM.GameState.record] at hr
          rcases List.mem_cons.mp hr with rfl | hr_old
          · dsimp only [r_new] at hsender ⊢
            subst hsender
            right
            intro msg htry
            obtain ⟨sc, hsc, hkey⟩ :=
              send_tryFrom_senderRatchetKey P hcodec hL (st.1.st .B) (hinv.sender_inv .B).1 m coins
                  msg htry
            rw [hscB] at hsc; injection hsc with hsc_eq; subst hsc_eq
            rw [hkey]; exact hnoB
          · rw [htr1] at hr_old
            exact htrB r hr_old hsender

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem transmitR_support_hop2WindowInv {ℓ : ℕ} (P : Params Bytes PQC)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (x : Party × CBC.Plain ℓ × Option PQC)
    (st : Hop2State Pt ℓ) (hinv : Hop2GameInv P decT encT st)
    (hwin : Hop2WindowInv P st.1) :
    ∀ z ∈ support ((SM.transmitR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st.1),
      Hop2WindowInv P z.2 := by
  rcases x with ⟨Q, m, r_opt⟩
  intro z hz
  unfold SM.transmitR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st.1 Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · rw [StateT.run_bind] at hz
      simp only [StateT.run_monadLift, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz2⟩
      cases hep : st.1.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz2
        subst hz2; exact hwin
      | some s₁ =>
        simp only [hep, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz2
        subst hz2
        have hsend_eq : ∀ s0, ((sessionSchemeU P ℓ).sendPart.send s0 m cb.1) =
            ((sessionSchemeU P ℓ).send s0 m cb.1) := fun _ => rfl
        rw [hsend_eq]
        exact record_send_preserves_hop2WindowInv P hcodec hL hinv hwin hep
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hwin

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem challR_support_hop2WindowInv {ℓ : ℕ} (P : Params Bytes PQC)
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qep : ℕ) (x : Party × CBC.Plain ℓ × CBC.Plain ℓ × Option PQC)
    (st : Hop2State Pt ℓ) (hinv : Hop2GameInv P decT encT st)
    (hwin : Hop2WindowInv P st.1) :
    ∀ z ∈ support ((SM.challR (sessionSchemeU P ℓ) 3 qep (configRefuseEarlyBobCorr decT encT) x).run st.1),
      Hop2WindowInv P z.2 := by
  rcases x with ⟨Q, m₀, m₁, r_opt⟩
  intro z hz
  unfold SM.challR configRefuseEarlyBobCorr configR1OnCurve configR1 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hok : noBobSendInEpoch0 st.1 Q = true
  · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hwin
    · rw [StateT.run_bind] at hz
      simp only [StateT.run_monadLift, bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨cb, _, hz2⟩
      cases hep : st.1.epMgmt 3 qep Q cb.2 with
      | none =>
        simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz2
        subst hz2; exact hwin
      | some s₁ =>
        rw [hep] at hz2
        dsimp only [] at hz2
        split at hz2
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz2
          subst hz2; exact hwin
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hz2
          subst hz2
          have hsend_eq : ∀ s0 msg_ch, ((sessionSchemeU P ℓ).sendPart.send s0 msg_ch cb.1) =
              ((sessionSchemeU P ℓ).send s0 msg_ch cb.1) := fun _ _ => rfl
          rw [hsend_eq]
          exact record_send_preserves_hop2WindowInv P hcodec hL hinv hwin hep
  · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; exact hwin

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem corrR_support_hop2WindowInv {ℓ : ℕ} (P : Params Bytes PQC)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (x : Party)
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (hwin : Hop2WindowInv P s) :
    ∀ z ∈ support ((SM.corrR (configRefuseEarlyBobCorr decT encT) x).run s),
      Hop2WindowInv P z.2 := by
  intro z hz
  unfold SM.corrR at hz
  rcases hwin with hpos | hcore
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl hpos
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact Or.inl hpos
  · have hnA := hcore.nA_le
    have hepA := hcore.epA_le
    have hfalse := corrOK_eq_false_of_epoch_A_lt_10 decT encT s x (by omega)
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hfalse,
      Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact Or.inr hcore

theorem trivial_eq_false_of_tL_none_comp_nil {ℓ : ℕ}
    (s : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Δ : ℕ) (pos : SM.Pos)
    (htL : s.tL = none) (hcomp : s.comp = []) :
    s.trivial Δ pos = false := by
  unfold SM.GameState.trivial SM.healedBy
  simp [htL, hcomp]

omit [SampleableType Pt] in
theorem hop2InjectPost_preserves_hop2WindowInv {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (s : BitVec 256) (h : Hop2Hyb Pt)
    (Q : Party) (c : Bytes) (rc : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hwin : Hop2WindowInv P st.1)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st)).run tbl)) :
    Hop2WindowInv P (hop2InjectPost P qep s Q c (st.1.st Q) z.1.1 z.1.2).2.1 := by
  have hdone := hop2Recv_support_done P Dh encT decT h (st.1.st Q) c rc st tbl z hz
  cases ho : z.1.1 with
  | none =>
    dsimp only [hop2InjectPost]
    rw [hdone.1]; exact hwin
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    dsimp only [hop2InjectPost]
    rw [hdone.1]
    rcases hwin with hpos | hcore
    · split_ifs
      · exact Or.inl hpos
      · left
        dsimp only [SM.GameState.accept, SM.GameState.delete]
        cases Q with
        | A =>
          rw [Function.update_self]
          exact (hdone.2.2 st' t' i' m' u ho).2 hpos
        | B =>
          rw [Function.update_of_ne (by decide)]
          exact hpos
      · exact Or.inl hpos
    · have htriv : st.1.trivial 3 ⟨Q.other, t', i'⟩ = false :=
        trivial_eq_false_of_tL_none_comp_nil st.1 3 _ hcore.tL_none hcore.comp_nil
      by_cases hqep : qep + 1 < t'
      · simp only [hqep, ↓reduceIte]
        exact Or.inr hcore
      · simp only [hqep, htriv, Bool.false_eq_true, ↓reduceIte]
        exact Or.inr ⟨hcore.tL_none, hcore.comp_nil, hcore.nA_pos, hcore.nA_le,
          hcore.csB_le, hcore.epochs_len_A, hcore.pos_tail_A, hcore.epA_le,
          hcore.epB_le, hcore.trans_le, hcore.phase⟩

theorem evictReceiverChains_length_le_five (cs : List ReceiverChain) :
    (RatchetState.evictReceiverChains cs).length ≤ 5 := by
  unfold RatchetState.evictReceiverChains maxReceiverChains
  simp [List.length_drop]
  omega

omit [SampleableType Pt] in
theorem hop2DeliverPost_preserves_hop2WindowInv {ℓ : ℕ} (P : Params Bytes PQC)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (s : BitVec 256) (h : Hop2Hyb Pt)
    (Q : Party) (c : Bytes) (r_rec : SM.Record (CBC.Plain ℓ) Bytes) (rc : BitVec 256)
    (st : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256))
    (hwin : Hop2WindowInv P st.1)
    (hin : st.1.inTransit Q.other c = some r_rec)
    (hgood : hasKeyInChainsBool (KeyPair.generate P.C rc).publicKey
      (st.1.st Q.other).session.receiverChains = false)
    (z : (Hop2Out Pt ℓ × Hop2State Pt ℓ) × List (Pt × BitVec 256))
    (hz : z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
      ((hop2Recv P Dh encT decT h (st.1.st Q) c rc).run st)).run tbl)) :
    Hop2WindowInv P (hop2DeliverPost P s Q c (st.1.st Q) r_rec z.1.1 z.1.2).2.1 := by
  have hdone := hop2Recv_support_done P Dh encT decT h (st.1.st Q) c rc st tbl z hz
  cases ho : z.1.1 with
  | none =>
    dsimp only [hop2DeliverPost]
    rw [hdone.1]; exact hwin
  | some val =>
    rcases val with ⟨⟨st', t', i', m'⟩, u⟩
    dsimp only [hop2DeliverPost]
    rw [hdone.1]
    rcases hwin with hpos | hcore
    · left
      dsimp only [SM.GameState.accept, SM.GameState.delete]
      cases Q with
      | A =>
        rw [Function.update_self]
        exact (hdone.2.2 st' t' i' m' u ho).2 hpos
      | B =>
        rw [Function.update_of_ne (by decide)]
        exact hpos
    · have hr_mem : r_rec ∈ st.1.trans := List.mem_of_find?_eq_some hin
      have hr_pred := List.find?_some hin
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
      rcases hr_pred with ⟨hr_sender, hr_ct⟩
      have hno_rc : NoKeyInChains (KeyPair.generate P.C rc).publicKey
          (st.1.st Q.other).session.receiverChains :=
        noKeyInChains_of_hasKeyInChainsBool_false _ _ hgood
      obtain ⟨msg, htry, hcases⟩ :=
        hop2Recv_support_window_props P Dh encT decT h (st.1.st Q) c rc st tbl z hz st' t' i' m' u
            ho
      set s' := st.1.accept Q st' r_rec.pos
      have htL' : s'.tL = none := hcore.tL_none
      have hcomp' : s'.comp = [] := by
        dsimp only [s', SM.GameState.accept, SM.GameState.delete]
        rw [hcore.comp_nil]; rfl
      have htr_sub : ∀ r' ∈ s'.trans, r' ∈ st.1.trans := by
        intro r' hr'
        dsimp only [s', SM.GameState.accept, SM.GameState.delete] at hr'
        exact (List.mem_filter.mp hr').1
      have hep_le : ∀ R, st.1.epoch R ≤ s'.epoch R := by
        intro R
        dsimp only [s', SM.GameState.accept, SM.GameState.delete]
        by_cases hR : R = Q
        · subst hR; rw [Function.update_self]; exact le_max_left _ _
        · rw [Function.update_of_ne hR]
      have htr_le' : ∀ r' ∈ s'.trans, r'.pos.epoch ≤ s'.epoch r'.pos.sender :=
        fun r' hr' => (hcore.trans_le r' (htr_sub r' hr')).trans (hep_le r'.pos.sender)
      rcases hcases with ⟨idx, hfind, hep_eq, hce_eq, hsc_eq, hlen_eq, hno_imp⟩ |
        ⟨hfind_none, hep_eq, hce_eq, ⟨ckR, hlen_eq⟩, hno_imp, ⟨sck, hsc_eq⟩⟩
      ·
        have hrc_len : ∀ R, (s'.st R).session.receiverChains.length =
            (st.1.st R).session.receiverChains.length := by
          intro R
          dsimp only [s', SM.GameState.accept, SM.GameState.delete]
          by_cases hR : R = Q
          · subst hR; rw [Function.update_self, hlen_eq]
          · rw [Function.update_of_ne hR]
        have hsc_all : ∀ R, (s'.st R).session.senderChain = (st.1.st R).session.senderChain := by
          intro R
          dsimp only [s', SM.GameState.accept, SM.GameState.delete]
          by_cases hR : R = Q
          · subst hR; rw [Function.update_self, hsc_eq]
          · rw [Function.update_of_ne hR]
        have hno_all : ∀ R pk, NoKeyInChains pk (st.1.st R).session.receiverChains →
            NoKeyInChains pk (s'.st R).session.receiverChains := by
          intro R pk hno
          dsimp only [s', SM.GameState.accept, SM.GameState.delete]
          by_cases hR : R = Q
          · subst hR; rw [Function.update_self]; exact hno_imp pk hno
          · rw [Function.update_of_ne hR]; exact hno
        have hce_A : (s'.st .A).chainEpochs = (st.1.st .A).chainEpochs := by
          dsimp only [s', SM.GameState.accept, SM.GameState.delete]
          by_cases hQ : Party.A = Q
          · subst hQ
            rw [Function.update_self, hce_eq, hlen_eq, ← hcore.epochs_len_A,
              Nat.sub_self, List.drop_zero]
          · rw [Function.update_of_ne hQ]
        right
        refine ⟨htL', hcomp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, htr_le', ?_⟩
        · rw [hrc_len .A]; exact hcore.nA_pos
        · rw [hrc_len .A]; exact hcore.nA_le
        · rw [hrc_len .B]; exact hcore.csB_le
        · rw [hce_A, hrc_len .A]; exact hcore.epochs_len_A
        · rw [hce_A]; exact hcore.pos_tail_A
        · rw [hrc_len .A]
          dsimp only [s', SM.GameState.accept, SM.GameState.delete]
          cases Q with
          | A =>
            dsimp only [Party.other] at hr_sender
            rw [Function.update_self]
            have hr_ep : r_rec.pos.epoch ≤ 2 * (st.1.st .A).session.receiverChains.length - 1 := by
              rcases hcore.phase with ⟨hB_le, _⟩ | ⟨_, htrB⟩
              · have := hcore.trans_le r_rec hr_mem
                rw [hr_sender] at this
                have := hcore.nA_pos; omega
              · rcases htrB r_rec hr_mem hr_sender with hle | himp
                · have := hcore.nA_pos; omega
                · have hno' := himp msg (hr_ct.symm ▸ htry)
                  rw [findIdx?_eq_none_of_noKeyInChains _ _ hno'] at hfind
                  cases hfind
            exact max_le hcore.epA_le hr_ep
          | B =>
            rw [Function.update_of_ne (by decide)]; exact hcore.epA_le
        · rw [hrc_len .A]
          dsimp only [s', SM.GameState.accept, SM.GameState.delete]
          cases Q with
          | A =>
            rw [Function.update_of_ne (by decide)]; exact hcore.epB_le
          | B =>
            dsimp only [Party.other] at hr_sender
            rw [Function.update_self]
            have hr_ep : r_rec.pos.epoch ≤ 2 * (st.1.st .A).session.receiverChains.length := by
              have := hcore.trans_le r_rec hr_mem
              rw [hr_sender] at this
              have := hcore.epA_le; omega
            exact max_le hcore.epB_le hr_ep
        · rcases hcore.phase with ⟨hB_le, ⟨scA, hscA, hnoA⟩, htrA⟩ | ⟨⟨scB, hscB, hnoB⟩, htrB⟩
          · left
            refine ⟨?_, ⟨scA, (hsc_all .A).trans hscA, hno_all .B _ hnoA⟩, ?_⟩
            · rw [hrc_len .A]
              dsimp only [s', SM.GameState.accept, SM.GameState.delete]
              cases Q with
              | A => rw [Function.update_of_ne (by decide)]; exact hB_le
              | B =>
                dsimp only [Party.other] at hr_sender
                rw [Function.update_self]
                have hr_ep :
                    r_rec.pos.epoch ≤ 2 * (st.1.st .A).session.receiverChains.length - 2 := by
                  rcases htrA r_rec hr_mem hr_sender with hle | himp
                  · exact hle
                  · have hno' := himp msg (hr_ct.symm ▸ htry)
                    rw [findIdx?_eq_none_of_noKeyInChains _ _ hno'] at hfind
                    cases hfind
                exact max_le hB_le hr_ep
            · intro r' hr' hsender'
              rw [hrc_len .A]
              rcases htrA r' (htr_sub r' hr') hsender' with hle | himp
              · exact Or.inl hle
              · exact Or.inr (fun msg' htry' => hno_all .B _ (himp msg' htry'))
          · right
            refine ⟨⟨scB, (hsc_all .B).trans hscB, hno_all .A _ hnoB⟩, ?_⟩
            intro r' hr' hsender'
            rw [hrc_len .A]
            rcases htrB r' (htr_sub r' hr') hsender' with hle | himp
            · exact Or.inl hle
            · exact Or.inr (fun msg' htry' => hno_all .A _ (himp msg' htry'))
      ·
        cases Q with
        | B =>
          dsimp only [Party.other] at hr_sender hno_rc
          have hstA : s'.st .A = st.1.st .A := by
            dsimp only [s', SM.GameState.accept, SM.GameState.delete]
            rw [Function.update_of_ne (by decide)]
          have hstB : s'.st .B = st' := by
            dsimp only [s', SM.GameState.accept, SM.GameState.delete]
            rw [Function.update_self]
          right
          refine ⟨htL', hcomp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, htr_le', Or.inr ?_⟩
          · rw [hstA]; exact hcore.nA_pos
          · rw [hstA]; exact hcore.nA_le
          · rw [hstB, hlen_eq]; exact evictReceiverChains_length_le_five _
          · rw [hstA]; exact hcore.epochs_len_A
          · rw [hstA]; exact hcore.pos_tail_A
          · rw [hstA]
            dsimp only [s', SM.GameState.accept, SM.GameState.delete]
            rw [Function.update_of_ne (by decide)]; exact hcore.epA_le
          · rw [hstA]
            dsimp only [s', SM.GameState.accept, SM.GameState.delete]
            rw [Function.update_self]
            have hr_ep : r_rec.pos.epoch ≤ 2 * (st.1.st .A).session.receiverChains.length := by
              have := hcore.trans_le r_rec hr_mem
              rw [hr_sender] at this
              have := hcore.epA_le; omega
            exact max_le hcore.epB_le hr_ep
          · unfold Hop2WindowStateB; dsimp only []
            rw [hstA, hstB]
            refine ⟨⟨⟨KeyPair.generate P.C rc, sck⟩, hsc_eq, hno_rc⟩, ?_⟩
            intro r' hr' hsender'
            rcases hcore.phase with ⟨hB_le, _⟩ | ⟨_, htrB⟩
            · have := hcore.trans_le r' (htr_sub r' hr')
              rw [hsender'] at this
              exact Or.inl (this.trans hB_le)
            · exact htrB r' (htr_sub r' hr') hsender'
        | A =>
          dsimp only [Party.other] at hr_sender hno_rc
          have hstA : s'.st .A = st' := by
            dsimp only [s', SM.GameState.accept, SM.GameState.delete]
            rw [Function.update_self]
          have hstB : s'.st .B = st.1.st .B := by
            dsimp only [s', SM.GameState.accept, SM.GameState.delete]
            rw [Function.update_of_ne (by decide)]
          set k_A := (st.1.st .A).session.receiverChains.length - 1
          have hk_len : (st.1.st .A).session.receiverChains.length = k_A + 1 := by
            have := hcore.nA_pos; omega
          have hk_le : k_A ≤ 4 := by
            have := hcore.nA_le; omega
          by_cases hklt : k_A < 4
          · have hlen_new : st'.session.receiverChains.length = (k_A + 1) + 1 := by
              rw [hlen_eq]
              exact evictReceiverChains_append_length_lt _ _ k_A hk_len hklt
            have hce_new := chainEpochs_step_lt (st.1.st .A).chainEpochs ((st.1.st .A).epoch + 1)
              k_A (hcore.epochs_len_A.trans hk_len) hcore.pos_tail_A (Nat.succ_pos _)
            rw [← hlen_new, ← hce_eq] at hce_new
            right
            refine ⟨htL', hcomp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, htr_le', Or.inl ?_⟩
            · rw [hstA, hlen_new]; omega
            · rw [hstA, hlen_new]; omega
            · rw [hstB]; exact hcore.csB_le
            · rw [hstA]; exact hce_new.1
            · rw [hstA]; exact hce_new.2
            · rw [hstA, hlen_new]
              dsimp only [s', SM.GameState.accept, SM.GameState.delete]
              rw [Function.update_self]
              have hr_ep := hcore.trans_le r_rec hr_mem
              rw [hr_sender] at hr_ep
              have hepA := hcore.epA_le
              have hepB := hcore.epB_le
              rw [hk_len] at hepA hepB
              omega
            · rw [hstA, hlen_new]
              dsimp only [s', SM.GameState.accept, SM.GameState.delete]
              rw [Function.update_of_ne (by decide)]
              have hepB := hcore.epB_le
              rw [hk_len] at hepB
              omega
            · unfold Hop2WindowStateA; dsimp only []
              rw [hstA, hstB, hlen_new]
              refine ⟨?_, ⟨⟨KeyPair.generate P.C rc, sck⟩, hsc_eq, hno_rc⟩, ?_⟩
              · dsimp only [s', SM.GameState.accept, SM.GameState.delete]
                rw [Function.update_of_ne (by decide)]
                have hepB := hcore.epB_le
                rw [hk_len] at hepB
                omega
              · intro r' hr' hsender'
                left
                have hr_ep := hcore.trans_le r' (htr_sub r' hr')
                rw [hsender'] at hr_ep
                have hepA := hcore.epA_le
                rw [hk_len] at hepA
                omega
          · have hk4 : k_A = 4 := by omega
            have hlen5 : st'.session.receiverChains.length = 5 := by
              rw [hlen_eq]
              exact evictReceiverChains_append_length_four _ _ (hk_len.trans (by omega))
            have hce_pos := chainEpochs_step_four (st.1.st .A).chainEpochs ((st.1.st .A).epoch + 1)
              (hcore.epochs_len_A.trans (hk_len.trans (by omega))) hcore.pos_tail_A (Nat.succ_pos _)
            rw [← hlen5, ← hce_eq] at hce_pos
            left
            rw [hstA]
            exact hce_pos

theorem evalDist_runHop2_phase2_recv_rc_le {ℓ : ℕ} {P : Params Bytes PQC}
    (hcodec : P.codec = protoSignalCodec)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz : ∀ x, Dh.dh x 0 = 0)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
    {u_chall : BitVec 256} {Q_create : Pt}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    (Q : Party) (c : Bytes) (rc : BitVec 256)
    (horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true)
    (post : Hop2Out Pt ℓ → Hop2State Pt ℓ → Option (SM.RecvResult (CBC.Plain ℓ)) × Hop2State Pt ℓ)
    (hpost : IsDeliverOrInjectPost (Pt := Pt) P qep s Q c (st_R.1.st Q) post)
    (cont_L cont_R : Option (SM.RecvResult (CBC.Plain ℓ)) → Hop2State Pt ℓ →
        List (Pt × BitVec 256) → ProbComp Bool)
    (d : ℝ≥0∞)
    (hcont : ∀ r sL tL sR, Hop2Phase2Rel P decT encT k u_chall Q_create sL tL sR →
      (∃ z ∈ support ((simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
              1) u_chall) (st_R.1.st Q) c rc).run st_R)).run []),
        post z.1.1 z.1.2 = (r, sR)) →
      𝒟[cont_L r sL tL] {true} ≤ 𝒟[cont_R r sR []] {true} + d) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrf k rc_L) (st_L.1.st Q) c rc).run st_L)).run tbl
      cont_L (post z.1.1 z.1.2).1 (post z.1.1 z.1.2).2 z.2)] {true} ≤
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall) (st_R.1.st Q) c rc).run st_R)).run []
      cont_R (post z.1.1 z.1.2).1 (post z.1.1 z.1.2).2 z.2)] {true} + d := by
  rcases party_eq_partyOfParity_or_succ k Q with rfl | rfl
  · obtain ⟨o_L, o_R, hrun_L, hrun_R, hout_eq, hrel'⟩ :=
      hop2Phase2Rel_of_post_pk hcodec hX hz (rc_L := rc_L) hrel rc horc hpost
    have hsupp_R : ((o_R, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
        ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          (st_R.1.st (partyOfParity k)) c rc).run st_R)).run []) := by
      have hrun_R' : (hop2Recv P Dh encT decT (hop2HybPrg P encPt (k + 1) u_chall)
          (st_R.1.st (partyOfParity k)) c rc).run st_R = pure (o_R, st_R) := hrun_R
      rw [hrun_R']; simp [simulateQ_pure, StateT.run_pure]
    rw [hrun_L, hrun_R]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    rw [hout_eq]
    exact hcont _ _ _ _ hrel' ⟨((o_R, st_R), []), hsupp_R, rfl⟩
  · set Q1 := partyOfParity (k + 1)
    set rk_chall := (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).1
    have hidx_ne_k2 : st_R.2.idx Q1 ≠ some (k + 2) := by
      rcases hrel.idx_pk1_R with h0 | h1
      · simp [h0, Q1]
      · simp [h1, Q1]
    have hg_eq : st_L.1.st Q1 = st_R.1.st Q1 := by
      rw [hrel.st1_eq]
      exact patchPartyIdx_of_ne (k + 2) rk_chall (st_R.2.idx Q1) (st_R.1.st Q1) hidx_ne_k2
    have hp_R : (st_R.1.st Q1).party = Q1 := hrel.inv_R.party_eq Q1
    rcases hrel.idx_pk1_R with hnone_R | hsome_R
    · have hidx_R : st_R.2.idx (st_R.1.st Q1).party = none := by rw [hp_R]; exact hnone_R
      have hidx_L : st_L.2.idx (st_L.1.st Q1).party = none := by
        rw [hg_eq, hp_R, hrel.idx_pk1_eq]; exact hnone_R
      have hrun_L :=
          hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrf k rc_L) (st_L.1.st Q1) c rc st_L
          hidx_L
      have hrun_R := hop2Recv_run_of_idx_none P Dh encT decT (hop2HybPrg P encPt (k +
          1) u_chall) (st_R.1.st Q1) c rc st_R hidx_R
      rw [hrun_L, hrun_R, hg_eq]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      set o : Hop2Out Pt ℓ := ((sessionSchemeU P ℓ).receive (st_R.1.st Q1) c rc).map (fun r => (r,
          none))
      have hsupp_R : ((o, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
          ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
              1) u_chall) (st_R.1.st Q1) c rc).run st_R)).run []) := by
        rw [hrun_R]; simp [simulateQ_pure, StateT.run_pure]
      have hinv' : Hop2GameInv P decT encT (post o st_R).2 :=
        hpost.preserves_hop2GameInv hrel.inv_R ((o, st_R), []) hsupp_R
      have ho_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩ := by
        intro x hx
        dsimp only [o] at hx
        simp only [Option.mem_def, Option.map_eq_some_iff] at hx
        rcases hx with ⟨_, _, hpair⟩
        exact Or.inl (Prod.mk.inj hpair).2.symm
      have hpost_rel := hop2Phase2Rel_of_post_pk1 hrel hpost o st_L st_R tbl hinv'
        ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
        hrel.tbl_create hrel.tbl_other ho_upd
      rw [hpost_rel.1]
      exact hcont _ _ _ _ hpost_rel.2 ⟨((o, st_R), []), hsupp_R, rfl⟩
    · set g := st_R.1.st Q1
      have hidx_R : st_R.2.idx g.party = some (k + 1) := by rw [hp_R]; exact hsome_R
      have hidx_L : st_L.2.idx g.party = some (k + 1) := by
        rw [hp_R, hrel.idx_pk1_eq]; exact hsome_R
      have hcoins_eq : st_L.2.coins g.party = st_R.2.coins g.party := by
        rw [hp_R]; exact hrel.coins_pk1 hsome_R
      by_cases hdh : ∃ msg T sc,
          SignalMessage.tryFrom P.codec c = .ok msg ∧
          (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone =
              true ∧
          decT msg.senderRatchetKey = some T ∧
          ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
          g.session.senderChain = some sc ∧
          Dh.dh (st_R.2.coins g.party) T ≠ 0
      · rcases hdh with ⟨msg, T, sc, htry, hfind, hdec, hT, hsc, hQ0_R⟩
        have hQ0_L : Dh.dh (st_L.2.coins g.party) T ≠ 0 := by
          rw [hcoins_eq]; exact hQ0_R
        have hrun_L := hop2Recv_run_at_succ P Dh encT decT k rc_L g c rc st_L msg T sc
          hidx_L htry hfind hdec hT hsc hQ0_L
        rw [hg_eq, hrun_L, hcoins_eq]
        set Q' := Dh.dh (st_R.2.coins g.party) T
        have h_upd : ∀ u : BitVec 256, ∀ x ∈ hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u,
            x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩ := by
          intro u x hx
          rcases x with ⟨⟨st', t', i', m'⟩, upd⟩
          have hp :=
              hop2OffChainOut_some_props P g msg sc rc u (hrel.inv_R.sender_inv Q1) st' t' i' m' upd
              hx
          exact Or.inr ⟨rc, hp.1⟩
        by_cases hQ_eq : Q' = Q_create
        · have hmade_R : st_R.2.made.lookup (k + 1, Dh.dh (st_R.2.coins g.party) T) =
              some (Ratchet.rootExpand P.C.F (keyToBytes32 u_chall)).2 := by
            change st_R.2.made.lookup (k + 1, Q') = _
            rw [hQ_eq]; exact hrel.made_create
          have hrun_R := hop2Recv_run_at_succ_made_some P Dh encPt encT decT hX k u_chall
            g c rc st_R msg T sc hidx_R htry hfind hdec hT hsc hQ0_R hmade_R
          rw [hrun_R, simulateQ_lazyImpl_map_evalQuery]
          have hlook_create : tbl.lookup (Dh.dh (st_R.2.coins g.party) T) = some u_chall := by
            change tbl.lookup Q' = some u_chall
            rw [hQ_eq]; exact hrel.tbl_create
          rw [hlook_create]
          simp only [pure_bind, simulateQ_pure, StateT.run_pure]
          set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u_chall
          have hsupp_R : ((o, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
              ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
                  1) u_chall) g c rc).run st_R)).run []) := by
            rw [hrun_R]; simp [simulateQ_pure, StateT.run_pure]
          have hinv' : Hop2GameInv P decT encT (post o st_R).2 :=
            hpost.preserves_hop2GameInv hrel.inv_R ((o, st_R), []) hsupp_R
          have hpost_rel := hop2Phase2Rel_of_post_pk1 hrel hpost o st_L st_R tbl hinv'
            ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
            hrel.tbl_create hrel.tbl_other (h_upd u_chall)
          rw [hpost_rel.1]
          exact hcont _ _ _ _ hpost_rel.2 ⟨((o, st_R), []), hsupp_R, rfl⟩
        · have hmade_R : st_R.2.made.lookup ((hop2HybPrg P encPt (k + 1) u_chall).k,
            Dh.dh (st_R.2.coins g.party) T) = none :=
            hrel.made_other Q' hQ_eq
          have hrun_R := hop2Recv_run_at_succ_made_none P Dh encT decT
            (hop2HybPrg P encPt (k + 1) u_chall) g c rc st_R msg T sc
            hidx_R htry hfind hdec hT hsc hQ0_R hmade_R
          rw [hrun_R, simulateQ_lazyImpl_map_evalQuery, simulateQ_lazyImpl_map_hop2Lazy]
          simp only [hop2HybPrg_k]
          have hlazy_eq : st_R.2.lazy.lookup (k + 1, Dh.dh (st_R.2.coins g.party) T) =
              tbl.lookup (Dh.dh (st_R.2.coins g.party) T) := (hrel.tbl_other Q' hQ_eq).symm
          rw [hlazy_eq]
          cases hlook : tbl.lookup (Dh.dh (st_R.2.coins g.party) T) with
          | some u0 =>
            simp only [pure_bind]
            set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u0
            have hsupp_R : ((o, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
                ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
                    1) u_chall) g c rc).run st_R)).run []) := by
              rw [hrun_R, simulateQ_lazyImpl_map_hop2Lazy]
              simp only [hop2HybPrg_k, hlazy_eq, hlook, support_pure, Set.mem_singleton_iff]
              rfl
            have hinv' : Hop2GameInv P decT encT (post o st_R).2 :=
              hpost.preserves_hop2GameInv hrel.inv_R ((o, st_R), []) hsupp_R
            have hpost_rel := hop2Phase2Rel_of_post_pk1 hrel hpost o st_L st_R tbl hinv'
              ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
              hrel.tbl_create hrel.tbl_other (h_upd u0)
            rw [hpost_rel.1]
            exact hcont _ _ _ _ hpost_rel.2 ⟨((o, st_R), []), hsupp_R, rfl⟩
          | none =>
            simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind
              ]
            refine bind_evalDist_true_le_add_of_support_window ($ᵗ BitVec 256) _ _ d fun u0 _ => ?_
            set o := hop2OffChainOut (Pt := Pt) P ℓ g msg sc rc u0
            set st2_R : Hop2State Pt ℓ := (st_R.1, { st_R.2 with
                                                     lazy := ((k + 1, Q'), u0) :: st_R.2.lazy })
            have hsupp_R : ((o, st2_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
                ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
                    1) u_chall) g c rc).run st_R)).run []) := by
              rw [hrun_R, simulateQ_lazyImpl_map_hop2Lazy]
              simp only [hop2HybPrg_k, hlazy_eq, hlook, map_eq_bind_pure_comp, Function.comp_apply,
                MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
              exact ⟨u0, by simp, rfl⟩
            have hinv' : Hop2GameInv P decT encT (post o st2_R).2 :=
              hpost.preserves_hop2GameInv hrel.inv_R ((o, st2_R), []) hsupp_R
            have htbl_create' : ((Q', u0) :: tbl).lookup Q_create = some u_chall := by
              have hbeq : (Q_create == Q') = false := beq_eq_false_iff_ne.mpr (Ne.symm hQ_eq)
              simp [List.lookup, hbeq, hrel.tbl_create]
            have htbl_other' : ∀ Q'' ≠ Q_create,
                ((Q', u0) :: tbl).lookup Q'' = st2_R.2.lazy.lookup (k + 1, Q'') := by
              intro Q'' hQ''
              dsimp only [st2_R, List.lookup]
              have hbeq : (((k + 1, Q'') == (k + 1, Q')) : Bool) = (Q'' == Q') := by simp
              rw [hbeq]
              cases Q'' == Q' with
              | true => rfl
              | false => exact hrel.tbl_other Q'' hQ''
            have hpost_rel := hop2Phase2Rel_of_post_pk1 hrel hpost o st_L st2_R ((Q',
                u0) :: tbl) hinv'
              ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
              htbl_create' htbl_other' (h_upd u0)
            rw [hpost_rel.1]
            exact hcont _ _ _ _ hpost_rel.2 ⟨((o, st2_R), []), hsupp_R, rfl⟩
      · have hnot_L : ¬ (∃ msg T sc,
            SignalMessage.tryFrom P.codec c = .ok msg ∧
            (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone
                = true ∧
            decT msg.senderRatchetKey = some T ∧
            ¬ (T = 0 ∨ encT T ≠ msg.senderRatchetKey) ∧
            g.session.senderChain = some sc ∧
            Dh.dh (st_L.2.coins g.party) T ≠ 0) := by
          rw [hcoins_eq]; exact hdh
        have hrun_L := hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrf k rc_L)
          (k + 1) g c rc st_L hidx_L hnot_L
        have hrun_R := hop2Recv_run_of_idx_some_non_dh P Dh encT decT (hop2HybPrg P encPt (k +
            1) u_chall)
          (k + 1) g c rc st_R hidx_R hdh
        rw [hg_eq, hrun_L, hrun_R]
        simp only [simulateQ_pure, StateT.run_pure, pure_bind]
        set o := hop2NonDhOut (Pt := Pt) P ℓ g c rc
        have hsupp_R : ((o, st_R), []) ∈ support ((simulateQ (lazyImpl (Pt := Pt))
            ((hop2Recv P Dh encT decT (hop2HybPrg P encPt (k +
                1) u_chall) g c rc).run st_R)).run []) := by
          rw [hrun_R]; simp [simulateQ_pure, StateT.run_pure]
        have hinv' : Hop2GameInv P decT encT (post o st_R).2 :=
          hpost.preserves_hop2GameInv hrel.inv_R ((o, st_R), []) hsupp_R
        have ho_upd : ∀ x ∈ o, x.2 = none ∨ ∃ rc', x.2 = some ⟨none, rc', none⟩ :=
          fun x hx => Or.inl (hop2NonDhOut_snd_none P g c rc x hx)
        have hpost_rel := hop2Phase2Rel_of_post_pk1 hrel hpost o st_L st_R tbl hinv'
          ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
          hrel.tbl_create hrel.tbl_other ho_upd
        rw [hpost_rel.1]
        exact hcont _ _ _ _ hpost_rel.2 ⟨((o, st_R), []), hsupp_R, rfl⟩

theorem evalDist_runHop2_phase2_deliver_le {ℓ : ℕ} {P : Params Bytes PQC}
    (hcodec : P.codec = protoSignalCodec)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
    {u_chall : BitVec 256} {Q_create : Pt}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    (hcore : Hop2WindowCore P st_R.1)
    (Q : Party) (c : Bytes)
    (cont_L cont_R : Option (SM.RecvResult (CBC.Plain ℓ)) → Hop2State Pt ℓ →
        List (Pt × BitVec 256) → ProbComp Bool)
    (d : ℝ≥0∞)
    (hcont : ∀ r sL tL sR, Hop2Phase2Rel P decT encT k u_chall Q_create sL tL sR →
      Hop2WindowInv P sR.1 →
      𝒟[cont_L r sL tL] {true} ≤ 𝒟[cont_R r sR []] {true} + d) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrf k rc_L) (Q, c)).run st_L)).run tbl
      cont_L z.1.1 z.1.2 z.2)] {true} ≤
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Deliver P Dh encT decT s (hop2HybPrg P encPt (k + 1) u_chall) (Q,
            c)).run st_R)).run []
      cont_R z.1.1 z.1.2 z.2)] {true} + d + (5 : ℝ≥0∞) * hop2GuessUnit Dh := by
  have hwin_eq : st_L.1.win = st_R.1.win := by rw [hrel.st1_eq]; rfl
  have hin_eq : st_L.1.inTransit Q.other c = st_R.1.inTransit Q.other c := by rw [hrel.st1_eq]; rfl
  by_cases hwin : st_R.1.win = true
  · have hwin_L : st_L.1.win = true := hwin_eq.trans hwin
    unfold hop2Deliver
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin_L, hwin, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    exact (hcont none st_L tbl st_R hrel (Or.inr hcore)).trans le_self_add
  · have hwin_R : st_R.1.win = false := Bool.eq_false_iff.mpr hwin
    have hwin_L : st_L.1.win = false := hwin_eq.trans hwin_R
    cases hin_R : st_R.1.inTransit Q.other c with
    | none =>
      have hin_L : st_L.1.inTransit Q.other c = none := hin_eq.trans hin_R
      unfold hop2Deliver
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin_L, hwin_R, Bool.false_eq_true,
        ↓reduceIte, hin_L, hin_R, StateT.run_pure, simulateQ_pure]
      exact (hcont none st_L tbl st_R hrel (Or.inr hcore)).trans le_self_add
    | some r =>
      have hin_L : st_L.1.inTransit Q.other c = some r := hin_eq.trans hin_R
      rw [hop2Deliver_run_eq_post P Dh encT decT s (hop2HybPrf k rc_L) Q c st_L r hwin_L hin_L,
        hop2Deliver_run_eq_post P Dh encT decT s (hop2HybPrg P encPt (k +
            1) u_chall) Q c st_R r hwin_R hin_R]
      have horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true :=
        inTransit_hop2GameInv hrel.inv_R hin_R
      have hpost_eq : hop2DeliverPost (Pt := Pt) P s Q c (st_L.1.st Q) r =
          hop2DeliverPost (Pt := Pt) P s Q c (st_R.1.st Q) r := by
        rw [hrel.st1_eq]
        exact hop2DeliverPost_patchPartyIdx P s Q c (k + 2) _ (st_R.2.idx Q) (st_R.1.st Q) r
      rw [hpost_eq]
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
        stateT_lift_probComp_run, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
      have hcs_le : ((st_R.1.st Q.other).session.receiverChains.length : ℝ≥0∞) ≤ 5 := by
        cases Q.other with
        | A => exact_mod_cast hcore.nA_le
        | B => exact_mod_cast hcore.csB_le
      have hbad_le : 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>=
          fun rc => pure (hasKeyInChainsBool (KeyPair.generate P.C rc).publicKey
            (st_R.1.st Q.other).session.receiverChains)] {true} ≤
          (5 : ℝ≥0∞) * hop2GuessUnit Dh :=
        (hasKeyInChainsBool_prob_le_hop2GuessUnit P Dh encPt decT encT hX hdec _).trans
          (mul_le_mul_of_nonneg_right hcs_le zero_le)
      refine (bind_apply_le_add_of_evalDist_le_on_good_window ($ᵗ BitVec 256) _ _
        (fun rc => hasKeyInChainsBool (KeyPair.generate P.C rc).publicKey
          (st_R.1.st Q.other).session.receiverChains) d (fun rc hgood => ?_)).trans
        (add_le_add_right hbad_le _)
      exact evalDist_runHop2_phase2_recv_rc_le (qep := qep) hcodec hX hz rc_L hrel Q c rc horc
        _ (Or.inl ⟨r, rfl⟩) cont_L cont_R d (fun r' sL tL sR hrel' ⟨z, hz_R, hpost_z⟩ => by
          have hwin' := hop2DeliverPost_preserves_hop2WindowInv P Dh encT decT s
            (hop2HybPrg P encPt (k + 1) u_chall) Q c r rc st_R [] (Or.inr hcore) hin_R hgood z hz_R
          rw [hpost_z] at hwin'
          exact hcont r' sL tL sR hrel' hwin')

theorem evalDist_runHop2_phase2_inject_le {ℓ : ℕ} {P : Params Bytes PQC}
    (hcodec : P.codec = protoSignalCodec)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hz : ∀ x, Dh.dh x 0 = 0)
    {qep : ℕ} {s : BitVec 256} {k : ℕ} (rc_L : Ratchet.RootKey × BitVec 256)
    {u_chall : BitVec 256} {Q_create : Pt}
    {st_L : Hop2State Pt ℓ} {tbl : List (Pt × BitVec 256)} {st_R : Hop2State Pt ℓ}
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    (hwin_inv : Hop2WindowInv P st_R.1)
    (Q : Party) (c : Bytes)
    (cont_L cont_R : Option (SM.RecvResult (CBC.Plain ℓ)) → Hop2State Pt ℓ →
        List (Pt × BitVec 256) → ProbComp Bool)
    (d : ℝ≥0∞)
    (hcont : ∀ r sL tL sR, Hop2Phase2Rel P decT encT k u_chall Q_create sL tL sR →
      Hop2WindowInv P sR.1 →
      𝒟[cont_L r sL tL] {true} ≤ 𝒟[cont_R r sR []] {true} + d) :
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrf k rc_L) (Q, c)).run st_L)).run tbl
      cont_L z.1.1 z.1.2 z.2)] {true} ≤
    𝒟[(do
      let z ← (simulateQ (lazyImpl (Pt := Pt))
        ((hop2Inject P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) (Q,
            c)).run st_R)).run []
      cont_R z.1.1 z.1.2 z.2)] {true} + d := by
  have hg_eq : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) =
      (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) := by
    rw [hrel.st1_eq]; rfl
  by_cases hg : (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
      !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true
  · have hg_L : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = true := hg_eq.trans hg
    unfold hop2Inject
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hg_L, hg, ↓reduceIte,
      StateT.run_pure, simulateQ_pure]
    exact hcont none st_L tbl st_R hrel hwin_inv
  · have hg_R : (st_R.1.win || (st_R.1.inTransit Q.other c).isSome || !(st_R.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := Bool.eq_false_iff.mpr hg
    have hg_L : (st_L.1.win || (st_L.1.inTransit Q.other c).isSome || !(st_L.1.safeInj 3) ||
        !(ratchetKeyAdmissible protoSignalCodec decT encT c)) = false := hg_eq.trans hg_R
    rw [hop2Inject_run_eq_post P Dh encT decT qep s (hop2HybPrf k rc_L) Q c st_L hg_L,
      hop2Inject_run_eq_post P Dh encT decT qep s (hop2HybPrg P encPt (k +
          1) u_chall) Q c st_R hg_R]
    have horc : ratchetKeyAdmissible protoSignalCodec decT encT c = true := by
      cases h : ratchetKeyAdmissible protoSignalCodec decT encT c
      · rw [h] at hg_R; simp at hg_R
      · rfl
    have hpost_eq : hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c (st_L.1.st Q) =
        hop2InjectPost (Pt := Pt) (ℓ := ℓ) P qep s Q c (st_R.1.st Q) := by
      rw [hrel.st1_eq]
      exact hop2InjectPost_patchPartyIdx P qep s Q c (k + 2) _ (st_R.2.idx Q) (st_R.1.st Q)
    rw [hpost_eq]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_lazyImpl_hop2Unif,
      stateT_lift_probComp_run, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
    refine bind_evalDist_true_le_add_of_support_window ($ᵗ BitVec 256) _ _ d fun rc _ => ?_
    exact evalDist_runHop2_phase2_recv_rc_le hcodec hX hz rc_L hrel Q c rc horc
      _ (Or.inr rfl) cont_L cont_R d (fun r' sL tL sR hrel' ⟨z, hz_R, hpost_z⟩ => by
        have hwin' := hop2InjectPost_preserves_hop2WindowInv P Dh encT decT qep s
          (hop2HybPrg P encPt (k + 1) u_chall) Q c rc st_R [] hwin_inv z hz_R
        rw [hpost_z] at hwin'
        exact hcont r' sL tL sR hrel' hwin')

theorem evalDist_runHop2_phase2_le {ℓ : ℕ} {P : Params Bytes PQC}
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : Ratchet.RootKey × BitVec 256)
    (u_chall : BitVec 256) (Q_create : Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem : ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (st_L : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) (st_R : Hop2State Pt ℓ)
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    (hwin_inv : Hop2WindowInv P st_R.1) :
    𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) oa st_L tbl] {true} ≤
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) oa st_R []] {true} +
      ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
  induction oa using OracleComp.inductionOn generalizing rem st_L tbl st_R with
  | pure a =>
    rw [runHop2_pure, runHop2_pure, hrel.bad_eq]
    exact le_self_add
  | query_bind t k_oa ih =>
    by_cases habs_R : Hop2Absorbed st_R
    · have habs_L : Hop2Absorbed st_L :=
        (hop2Absorbed_of_patchGamePartyIdx _ _ st_L st_R hrel.st1_eq hrel.bad_eq).mpr habs_R
      rw [evalDist_runHop2_of_absorbed P Dh encT decT qep s (hop2HybPrf k rc_L) _ st_L tbl habs_L,
        evalDist_runHop2_of_absorbed P Dh encT decT qep s (hop2HybPrg P encPt (k +
            1) u_chall) _ st_R [] habs_R,
        hrel.bad_eq]
      exact le_self_add
    · have hcore : Hop2WindowCore P st_R.1 :=
        hop2WindowCore_of_not_absorbed hrel.inv_R hwin_inv habs_R
      rw [SM.MakesAtMostQueries, isQueryBoundP_query_bind_iff] at hq
      rw [runHop2_bind_query, runHop2_bind_query]
      rcases t with u_q | ((((y_tr | y_ch) | ⟨Q, c⟩) | ⟨Q, c⟩) | y_corr)
      · rw [runHop2_unif, runHop2_unif]
        exact bind_evalDist_true_le_add_of_support_window _ _ _ _ fun a _ =>
          ih a rem (by simpa [SM.MakesAtMostQueries] using hq.2 a) st_L tbl st_R hrel hwin_inv
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        rw [runHop2_hop2Lift', runHop2_hop2Lift', hrel.st1_eq,
          transmitR_patchGamePartyIdx P decT encT qep (k + 2) _ st_R.2.idx st_R.1 y_tr]
        simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, Prod.map]
        have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
          (add_le_add le_rfl hle)
        have hinv' :=
            transmitR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep y_tr st_R
            hrel.inv_R r hr
        have hwin' :=
            transmitR_support_hop2WindowInv P hcodec hL decT encT qep y_tr st_R hrel.inv_R hwin_inv
            r hr
        exact ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
          _ tbl (r.2, st_R.2) (hrel.of_st1_step r.2 hinv') hwin'
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        rw [runHop2_hop2Lift', runHop2_hop2Lift', hrel.st1_eq,
          challR_patchGamePartyIdx P decT encT qep (k + 2) _ st_R.2.idx st_R.1 y_ch]
        simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind, Prod.map]
        have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        refine (bind_evalDist_true_le_add_of_support_window _ _ _ _ fun r hr => ?_).trans
          (add_le_add le_rfl hle)
        have hinv' :=
            challR_support_hop2GameInv P hcodec hL Dh encPt decT encT hX hdec qep y_ch st_R
            hrel.inv_R r hr
        have hwin' :=
            challR_support_hop2WindowInv P hcodec hL decT encT qep y_ch st_R hrel.inv_R hwin_inv r
            hr
        exact ih r.1 (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r.1)
          _ tbl (r.2, st_R.2) (hrel.of_st1_step r.2 hinv') hwin'
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        have hadd : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh + (5 :
            ℝ≥0∞) * hop2GuessUnit Dh =
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh := by
          rw [← add_mul]
          congr 1
          exact_mod_cast (by omega : 5 * (rem - 1) + 5 = 5 * rem)
        refine (evalDist_runHop2_phase2_deliver_le (qep :=
            qep) hcodec hX hdec hz rc_L hrel hcore Q c
          (fun r sL tL => runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL)
          (fun r sR tR => runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR tR)
          (((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh)
          (fun r sL tL sR hrel' hwin' =>
            ih r (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r) sL tL sR hrel'
                hwin')).trans ?_
        rw [add_assoc, hadd]
        exact le_rfl
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        refine (evalDist_runHop2_phase2_inject_le (qep := qep) hcodec hX hz rc_L hrel hwin_inv Q c
          (fun r sL tL => runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) (k_oa r) sL tL)
          (fun r sR tR => runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k +
              1) u_chall) (k_oa r) sR tR)
          (((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh)
          (fun r sL tL sR hrel' hwin' =>
            ih r (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 r) sL tL sR hrel'
                hwin')).trans
          (add_le_add le_rfl hle)
      · have hq0 : 0 < rem := hq.1.resolve_left (by simp)
        dsimp only [hop2Impl]
        rw [runHop2_hop2Lift', runHop2_hop2Lift']
        have hnA := hcore.nA_le
        have hepA := hcore.epA_le
        have hok_R : (configRefuseEarlyBobCorr decT encT).corrOK st_R.1 y_corr = false :=
          corrOK_eq_false_of_epoch_A_lt_10 decT encT st_R.1 y_corr (by omega)
        have hok_L : (configRefuseEarlyBobCorr decT encT).corrOK st_L.1 y_corr = false := by
          rw [hrel.st1_eq]; exact hok_R
        unfold SM.corrR
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hok_L, hok_R,
          Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure, Prod.mk.eta]
        have hle : ((5 * (rem - 1) : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh ≤
            ((5 * rem : ℕ) : ℝ≥0∞) * hop2GuessUnit Dh :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) zero_le
        exact (ih none (rem - 1) (by simpa [SM.MakesAtMostQueries] using hq.2 none)
          st_L tbl st_R hrel hwin_inv).trans (add_le_add le_rfl hle)

theorem evalDist_runHop2_phase2_le_createColl {ℓ : ℕ} {P : Params Bytes PQC}
    (hcodec : P.codec = protoSignalCodec) (hL : LengthsOk P ℓ)
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hz : ∀ x, Dh.dh x 0 = 0)
    (qep : ℕ) (s : BitVec 256) (k : ℕ) (rc_L : Ratchet.RootKey × BitVec 256)
    (u_chall : BitVec 256) (Q_create : Pt)
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) Bool)
    (rem : ℕ) (hq : SM.MakesAtMostQueries oa rem)
    (st_L : Hop2State Pt ℓ) (tbl : List (Pt × BitVec 256)) (st_R : Hop2State Pt ℓ)
    (hrel : Hop2Phase2Rel P decT encT k u_chall Q_create st_L tbl st_R)
    (hwin_inv : Hop2WindowInv P st_R.1) :
    𝒟[runHop2 P Dh encT decT qep s (hop2HybPrf k rc_L) oa st_L tbl] {true} ≤
      𝒟[runHop2 P Dh encT decT qep s (hop2HybPrg P encPt (k + 1) u_chall) oa st_R []] {true} +
      ((5 * rem : ℕ) : ℝ≥0∞) * hop2CreateCollUnit Dh :=
  (evalDist_runHop2_phase2_le hcodec hL hX hdec hz qep s k rc_L u_chall Q_create
    oa rem hq st_L tbl st_R hrel hwin_inv).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (hop2GuessUnit_le_hop2CreateCollUnit P Dh encPt encT hX) zero_le))

end Hop2Coupling
end CryptoVerification.E2E.SpkHop1
