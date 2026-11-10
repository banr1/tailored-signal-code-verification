/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD
public import Computational.Proofs.CryptoGames.FSAEAD.FSAEADProofDefs

/-!
# Pub-to-AD reduction for restricted public parts

**Checked by Lean.**

Proves `pubMsg_red_on`, extending `PubToAD.pubMsg_red` to codecs where public-part read-back holds
only on `ok` public parts (`EncMsgsOk`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM.Proofs.ProstPubToAD

open FSAEAD AEADScheme PubToAD

variable {MK CK AD Pub M C SS RS : Type}

theorem pubRed_encADsOk (ok : Pub → Bool) (pubOf : C → Option Pub)
    (A : Adversary SS RS AD (Pub × M) C) (hA : EncMsgsOk (fun m : Pub × M => ok m.1) A) :
    EncADsOk (fun ap : AD × Pub => ok ap.2) (pubRed pubOf A) := by
  unfold EncADsOk pubRed
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  refine IsQueryBoundP.simulateQ_run_of_step hA ?_ ?_ false
  · rintro (n | o) hp ended
    · simp [encBadMsg] at hp
    · rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · simp [encBadMsg] at hp
      · simp [encBadMsg] at hp
      · simp [encBadMsg] at hp
      · simp [encBadMsg] at hp
  · rintro (n | o) hnp ended
    · unfold pubRedImpl
      simp only [stateT_lift_run]
      rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [encBadAD]), fun _ => by simp⟩
    · rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simpa [encBadAD, encBadMsg] using hnp), fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl ?_, fun _ => by simp⟩
        simp only [encBadMsg, Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hnp
        simp [encBadAD, hnp.1]
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [corruptSenderQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [encBadAD]), fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [StateT.run_bind, stateT_lift_run, bind_assoc]
        rw [corruptReceiverQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl (by simp [encBadAD]), fun r => ?_⟩
        cases r <;> simp
      · unfold pubRedImpl
        dsimp only
        cases pubOf c with
        | none =>
          simp
        | some p =>
          simp only [stateT_lift_run, bind_assoc]
          rw [deliverQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [encBadAD]), fun _ => by simp⟩
      · unfold pubRedImpl
        dsimp only
        cases pubOf c with
        | none =>
          simp [StateT.run_get]
        | some p =>
          simp only [stateT_lift_run, bind_assoc]
          rw [injectQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [encBadAD]), fun _ => by simp⟩

section OnSim

variable (ae : AEADScheme MK ((ℕ × AD) × Pub) M C) (pubOf : C → Option Pub)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (ok : Pub → Bool)

private theorem pubOf_send_on (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (v : RatchetSenderState CK) (a : AD) (p : Pub) (m : M) (hp : ok p = true) :
    pubOf ((fsReassoc ae G maxSkip).send v (a, p) m).2.2 = some p := by
  simp only [fsReassoc, fromAEADPRG, reassoc]
  exact hpub _ _ _ _ hp

private theorem transmit_inv_on
    (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st)
    (a : AD) (p : Pub) (m : M) (hp : ok p = true) :
    Inv pubOf ended (transmit (fsReassoc ae G maxSkip) st (a, p) m).2 := by
  unfold transmit
  split
  · exact hI
  · refine ⟨hI.1, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact pubOf_send_on ae pubOf G maxSkip ok hpub st.senderState a p m hp
    · exact hI.2 r hr

private theorem challenge_inv_on
    (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st)
    (a : AD) (p : Pub) (m₀ m₁ : M) (hp : ok p = true) :
    Inv pubOf ended (challenge (fsReassoc ae G maxSkip) st (a, p) m₀ m₁).2 := by
  unfold challenge
  split
  · exact hI
  · refine ⟨hI.1, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact pubOf_send_on ae pubOf G maxSkip ok hpub st.senderState a p (if st.b then m₁ else m₀) hp
    · exact hI.2 r hr

variable [DecidableEq AD] [DecidableEq Pub] [DecidableEq M] [DecidableEq C]

private theorem step_transmit_on
    (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (a : AD) (pm : Pub × M) (hpm : ok pm.1 = true)
    (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st) :
    ∃ ans ended' st',
      (simulateQ (gameImpl (fsReassoc ae G maxSkip))
        ((pubRedImpl (pubOfPair pubOf) (.inr (.inl (.inl (.inl (.inl (.inl (a, pm)))))))).run ended)).run st =
        pure ((ans, ended'), st') ∧
      (gameImpl (fsPubMsg ae pubOf G maxSkip)
        (.inr (.inl (.inl (.inl (.inl (.inl (a, pm)))))))).run (mapState st) =
        pure (ans, mapState st') ∧
      Inv pubOf ended' st' := by
  refine ⟨(transmit (fsReassoc ae G maxSkip) st (a, pm.1) pm.2).1, ended,
    (transmit (fsReassoc ae G maxSkip) st (a, pm.1) pm.2).2, ?_, ?_,
    transmit_inv_on ae pubOf G maxSkip ok hpub ended st hI a pm.1 pm.2 hpm⟩
  · simp [pubRedImpl, transmitQuery, gameImpl, oracleImpl, transmitImpl, StateT.run_modifyGet]
  · simp only [gameImpl, QueryImpl.add_apply_inr, oracleImpl, QueryImpl.add_apply_inl,
      transmitImpl, StateT.run_modifyGet, transmit_mapState]

private theorem step_challenge_on
    (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (a : AD) (pm₀ pm₁ : Pub × M) (hp : pm₀.1 = pm₁.1) (hok : ok pm₀.1 = true)
    (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st) :
    ∃ ans ended' st',
      (simulateQ (gameImpl (fsReassoc ae G maxSkip))
        ((pubRedImpl (pubOfPair pubOf) (.inr (.inl (.inl (.inl (.inl (.inr (a, pm₀, pm₁)))))))).run ended)).run st =
        pure ((ans, ended'), st') ∧
      (gameImpl (fsPubMsg ae pubOf G maxSkip)
        (.inr (.inl (.inl (.inl (.inl (.inr (a, pm₀, pm₁)))))))).run (mapState st) =
        pure (ans, mapState st') ∧
      Inv pubOf ended' st' := by
  refine ⟨(challenge (fsReassoc ae G maxSkip) st (a, pm₀.1) pm₀.2 pm₁.2).1, ended,
    (challenge (fsReassoc ae G maxSkip) st (a, pm₀.1) pm₀.2 pm₁.2).2, ?_, ?_,
    challenge_inv_on ae pubOf G maxSkip ok hpub ended st hI a pm₀.1 pm₀.2 pm₁.2 hok⟩
  · simp [pubRedImpl, challengeQuery, gameImpl, oracleImpl, challengeImpl, StateT.run_modifyGet]
  · simp only [gameImpl, QueryImpl.add_apply_inr, oracleImpl, QueryImpl.add_apply_inl,
      challengeImpl, StateT.run_modifyGet, challenge_mapState ae pubOf G maxSkip st a pm₀ pm₁ hp]

private theorem step_inr_on
    (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (q : (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD (Pub × M) (ℕ × C)).Domain)
    (hq : ¬ unequalPubChall (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
      (AD := AD) (C := ℕ × C) (.inr q) = true)
    (hok : ¬ encBadMsg (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
      (AD := AD) (C := ℕ × C) (fun m : Pub × M => ok m.1) (.inr q) = true)
    (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st) :
    ∃ ans ended' st',
      (simulateQ (gameImpl (fsReassoc ae G maxSkip))
        ((pubRedImpl (pubOfPair pubOf) (.inr q)).run ended)).run st =
        pure ((ans, ended'), st') ∧
      (gameImpl (fsPubMsg ae pubOf G maxSkip) (.inr q)).run (mapState st) =
        pure (ans, mapState st') ∧
      Inv pubOf ended' st' := by
  rcases q with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
  · have hpm : ok pm.1 = true := by
      simpa [encBadMsg] using hok
    exact step_transmit_on ae pubOf G maxSkip ok hpub a pm hpm ended st hI
  · have hp : pm₀.1 = pm₁.1 := by
      simpa [unequalPubChall] using hq
    have hpm₀ : ok pm₀.1 = true := by
      simp only [encBadMsg, Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hok
      exact hok.1
    exact step_challenge_on ae pubOf G maxSkip ok hpub a pm₀ pm₁ hp hpm₀ ended st hI
  · exact step_corruptSender ae pubOf G maxSkip u ended st hI
  · exact step_corruptReceiver ae pubOf G maxSkip u ended st hI
  · exact step_deliver ae pubOf G maxSkip a c ended st hI
  · exact step_inject ae pubOf G maxSkip a c ended st hI

private theorem run_pubRed_on
    (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    {α : Type}
    (oa : OracleComp
      (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD (Pub × M) (ℕ × C)) α)
    (heq : oa.IsQueryBoundP (fun t =>
      unequalPubChall (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (AD := AD) (C := ℕ × C) t = true) 0)
    (hA : oa.IsQueryBoundP (fun t =>
      encBadMsg (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (AD := AD) (C := ℕ × C) (fun m : Pub × M => ok m.1) t = true) 0) :
    ∀ (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)), Inv pubOf ended st →
      (fun r => (r.1.1, mapState r.2)) <$>
        (simulateQ (gameImpl (fsReassoc ae G maxSkip))
          ((simulateQ (pubRedImpl (pubOfPair pubOf)) oa).run ended)).run st =
      (simulateQ (gameImpl (fsPubMsg ae pubOf G maxSkip)) oa).run (mapState st) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro ended st _
    simp
  | query_bind t k ih =>
    intro ended st hI
    rw [isQueryBoundP_query_bind_iff] at heq hA
    have ht : ¬ unequalPubChall (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (AD := AD) (C := ℕ × C) t = true :=
      heq.1.resolve_right (Nat.not_lt_zero 0)
    have hk : ∀ u, (k u).IsQueryBoundP (fun t =>
        unequalPubChall (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
          (AD := AD) (C := ℕ × C) t = true) 0 := by
      intro u
      simpa [ht] using heq.2 u
    have hok : ¬ encBadMsg (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (AD := AD) (C := ℕ × C) (fun m : Pub × M => ok m.1) t = true :=
      hA.1.resolve_right (Nat.not_lt_zero 0)
    have hkA : ∀ u, (k u).IsQueryBoundP (fun t =>
        encBadMsg (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
          (AD := AD) (C := ℕ × C) (fun m : Pub × M => ok m.1) t = true) 0 := by
      intro u
      simpa [hok] using hA.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | q
    · rw [step_inl, step_inl_pubMsg, bind_assoc, bind_assoc]
      refine bind_congr fun u => ?_
      rw [pure_bind, pure_bind]
      exact ih u (hk u) (hkA u) ended st hI
    · obtain ⟨ans, ended', st', h1, h2, hI'⟩ :=
        step_inr_on ae pubOf G maxSkip ok hpub q ht hok ended st hI
      rw [h1, h2, pure_bind, pure_bind]
      exact ih ans (hk ans) (hkA ans) ended' st' hI'

private theorem game_pubMsg_eq_on [SampleableType CK]
    (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (A : RatchetAdversary CK MK AD (Pub × M) C)
    (heq : EqualPubChallenges A)
    (hA : EncMsgsOk (fun m : Pub × M => ok m.1) A) :
    game (fsPubMsg ae pubOf G maxSkip) A =
      game (fsReassoc ae G maxSkip) (pubRed (pubOfPair pubOf) A) := by
  unfold game pubRed
  refine bind_congr fun b => bind_congr fun k => ?_
  dsimp only
  change (do
      let (b', st) ← (simulateQ (gameImpl (fsPubMsg ae pubOf G maxSkip)) A).run
        (initState (fsPubMsg ae pubOf G maxSkip) k b)
      return b == b' || st.win) =
    (do
      let (b', st) ← (simulateQ (gameImpl (fsReassoc ae G maxSkip))
        ((simulateQ (pubRedImpl (pubOfPair pubOf)) A).run' false)).run
        (initState (fsReassoc ae G maxSkip) k b)
      return b == b' || st.win)
  rw [← mapState_initState ae pubOf G maxSkip k b,
    ← run_pubRed_on ae pubOf G maxSkip ok hpub A heq hA false (initState (fsReassoc ae G maxSkip) k b)
      (inv_initState ae pubOf G maxSkip k b)]
  simp [StateT.run'_eq, map_eq_bind_pure_comp, mapState]

end OnSim

theorem advantage_pubMsg_le_on [DecidableEq AD] [DecidableEq Pub] [DecidableEq M] [DecidableEq C]
    [SampleableType CK] (ae : AEADScheme MK ((ℕ × AD) × Pub) M C) (pubOf : C → Option Pub)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) (ok : Pub → Bool)
    (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (A : RatchetAdversary CK MK AD (Pub × M) C) (heq : EqualPubChallenges A)
    (hA : EncMsgsOk (fun m : Pub × M => ok m.1) A) :
    advantage (fsPubMsg ae pubOf G maxSkip) A ≤
      advantage (fsReassoc ae G maxSkip) (pubRed (pubOfPair pubOf) A) := by
  unfold advantage
  rw [game_pubMsg_eq_on ae pubOf G maxSkip ok hpub A heq hA]

/-- Pub-to-AD reduction under restricted public-part recovery `hpub` and `EncMsgsOk`. -/
theorem pubMsg_red_on [DecidableEq AD] [DecidableEq Pub] [DecidableEq M] [DecidableEq C]
    [SampleableType CK] (ae : AEADScheme MK ((ℕ × AD) × Pub) M C) (pubOf : C → Option Pub)
    (ok : Pub → Bool) (hpub : ∀ k a p m, ok p = true → pubOf (ae.enc k (a, p) m) = some p)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) {κ : Type} [DecidableEq κ] (cls : AD → κ)
    (A : FSAEAD.RatchetAdversary CK MK AD (Pub × M) C) (q : ℕ)
    (hq : FSAEAD.MakesAtMostQueries A q) (heq : FSAEAD.EqualPubChallenges A)
    (hcls : FSAEAD.AllQueriesInOneADClass cls A) (hA : EncMsgsOk (fun m : Pub × M => ok m.1) A) :
    FSAEAD.MakesAtMostQueries (FSAEAD.pubRed (fun c : ℕ × C => pubOf c.2) A) q ∧
      FSAEAD.AllQueriesInOneADClass (fun ap : AD × Pub => cls ap.1)
        (FSAEAD.pubRed (fun c : ℕ × C => pubOf c.2) A) ∧
      EncADsOk (fun ap : AD × Pub => ok ap.2) (FSAEAD.pubRed (fun c : ℕ × C => pubOf c.2) A) ∧
      FSAEAD.advantage (FSAEAD.fromAEADPRG (ae.movePubPartToAD pubOf) G maxSkip) A ≤
        FSAEAD.advantage (FSAEAD.fromAEADPRG (reassoc ae) G maxSkip)
          (FSAEAD.pubRed (fun c : ℕ × C => pubOf c.2) A) :=
  ⟨pubRed_makesAtMostQueries (fun c : ℕ × C => pubOf c.2) A hq,
    pubRed_adClassConst cls (fun c : ℕ × C => pubOf c.2) A hcls,
    pubRed_encADsOk ok (fun c : ℕ × C => pubOf c.2) A hA,
    advantage_pubMsg_le_on ae pubOf G maxSkip ok hpub A heq hA⟩

end CryptoGames.LibsignalSM.Proofs.ProstPubToAD
