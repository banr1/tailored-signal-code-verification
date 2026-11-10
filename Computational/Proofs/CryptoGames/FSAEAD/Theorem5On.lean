/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.FSAEAD.AeadRedBound
public import Computational.Proofs.CryptoGames.FSAEAD.HybridLazy
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start
import Computational.Proofs.CryptoGames.FSAEAD.HybridOTReal
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Final
public import Computational.Proofs.CryptoGames.FSAEAD.FSAEADProofDefs

/-!
# ACD19 Theorem 5 with Restricted AEAD Correctness

**Checked by Lean.**

Proves the two-stage FS-AEAD bound `theorem5With_on_multi` for `fromAEADPRG` when AEAD decryption
correctness holds only on associated data satisfying `ok` (`AEADScheme.CorrectOn`), combining
`slotCount maxSkip q` chain-PRG hops at `t = 0` with one multi-slot OT-CCA reduction per chain.

**DEV-FS18 (libsignal): AEAD correctness only on some ADs.** Because libsignal's protobuf wire codec
round-trips only bounded-length public headers, correctness is assumed only on ADs satisfying `ok`
for adversaries whose encryption queries satisfy `FSAEAD.EncADsOk ok A`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.FSAEAD.Thm5On

open CryptoGames.FSAEAD.Thm5 CryptoGames.FSAEAD.Thm5.Ends

variable {CK MK AD M C : Type}

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C
local notation "SP" => StateT (HSt CK MK AD M C) ProbComp
local notation "RState" => FSAEAD.State (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)
local notation "GameM" => StateT RState ProbComp

/-- Every in-transit record carries associated data satisfying `ok`. -/
def InTransitOk (ok : AD → Bool) (st : HS) : Prop :=
  ∀ r ∈ st.inTransit, ok r.ad = true

theorem inTransitOk_hInit (ok : AD → Bool) (b : Bool) (sl : Slot CK MK) :
    InTransitOk ok (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b sl).1 := by
  intro r hr
  simp [hInit] at hr

theorem inTransitOk_removeFromTransit {ok : AD → Bool} {st : HS}
    (hok : InTransitOk ok st) (i : ℕ) :
    InTransitOk ok (st.removeFromTransit i) := by
  intro r hr
  simp only [HState.removeFromTransit, List.mem_filter] at hr
  exact hok r hr.1

section Steps

variable [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

theorem pure_eq_iff {α : Type} {x y : α} :
    (pure x : ProbComp α) = pure y ↔ x = y := by
  constructor
  · intro h
    have hx : x ∈ support (pure y : ProbComp α) := by rw [← h]; simp
    simpa using hx
  · rintro rfl; rfl

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem inTransitOk_of_transmitH {ok : AD → Bool} {k : CK} {s s' : St} {q : AD × M} {u : Option (ℕ × C)}
    (hs : WFSeed G k s) (hok : InTransitOk ok s.1) (hq : ok q.1 = true)
    (hM : (transmitHWith ideal ae G (hp 0 0 false) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) q).run s = pure (u, s')) :
    InTransitOk ok s'.1 := by
  rw [transmitH_run_of_wfSeed ideal ae G false hs q] at hM
  split_ifs at hM
  · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    exact hok
  · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hq
    · exact hok r hr

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem inTransitOk_of_challengeH {ok : AD → Bool} {k : CK} {s s' : St} {q : AD × M × M} {u : Option (ℕ × C)}
    (hs : WFSeed G k s) (hok : InTransitOk ok s.1) (hq : ok q.1 = true)
    (hM : (challengeHWith ideal ae G (hp 0 0 false) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) q).run s = pure (u, s')) :
    InTransitOk ok s'.1 := by
  rw [challengeH_run_of_wfSeed ideal ae G false hs q] at hM
  split at hM
  · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    exact hok
  · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hq
    · exact hok r hr

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem inTransitOk_of_corruptSenderH {ok : AD → Bool} {k : CK} {stR : RState} {s s' : St}
    {q : Unit} {u : Option (RatchetSenderState CK)}
    (hsync : SyncRM ae G k stR s) (hok : InTransitOk ok s.1)
    (hM : (corruptSenderH G (hp 0 0 false) q : SP _).run s = pure (u, s')) :
    InTransitOk ok s'.1 := by
  unfold corruptSenderH at hM
  simp only [StateT.run_bind, getH_run, pure_bind, hp_la, Bool.false_eq_true, ↓reduceIte] at hM
  cases hend : s.1.ended
  · simp only [hend, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      senderKey_run_of_wfSeed G hsync.wf_seed hsync.wf_state.keys_eq_sent_of_uncorr
        hsync.wf_state.corr_inv,
      pure_bind, modifyH_run, StateT.run_pure] at hM
    obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    exact hok
  · simp only [hend, ↓reduceIte, StateT.run_pure] at hM
    obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    exact hok

omit [SampleableType MK] [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem inTransitOk_of_corruptReceiverH {ok : AD → Bool} {k : CK} {stR : RState} {s s' : St}
    {q : Unit} {u : Option (RatchetSenderState CK × RatchetReceiverState CK MK)}
    (hsync : SyncRM ae G k stR s) (hok : InTransitOk ok s.1)
    (hM : (corruptReceiverH G (hp 0 0 false) q : SP _).run s = pure (u, s')) :
    InTransitOk ok s'.1 := by
  unfold corruptReceiverH at hM
  simp only [StateT.run_bind, getH_run, pure_bind, hp_la, Bool.false_eq_true, ↓reduceIte] at hM
  split_ifs at hM
  · simp only [StateT.run_pure] at hM
    obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    exact hok
  · simp only [StateT.run_bind,
      senderKey_run_of_wfSeed G hsync.wf_seed hsync.wf_state.keys_eq_sent_of_uncorr
        hsync.wf_state.corr_inv,
      pure_bind, getH_run, modifyH_run, StateT.run_pure] at hM
    obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    exact hok

theorem deliver_syncRM_on {ok : AD → Bool} (hae : ae.CorrectOn fun ia => ok ia.2)
    {k : CK} {stR : RState} {sM : St}
    (hsync : SyncRM ae G k stR sM) (hok : InTransitOk ok sM.1) (q : AD × (ℕ × C)) :
    ∃ u stR' sM',
      (deliverImpl (fromAEADPRG ae G maxSkip) q).run stR = pure (u, stR') ∧
      (deliverH ae G maxSkip (hp 0 0 false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sM = pure (u, sM') ∧
      SyncRM ae G k stR' sM' ∧
      InTransitOk ok sM'.1 ∧
      sM'.1.senderCorruptedAt = sM.1.senderCorruptedAt ∧
      sM'.1.ended = sM.1.ended := by
  rcases q with ⟨a, i, e⟩
  rw [deliverH_run_of_wfSeed ae G maxSkip (hp 0 0 false) (DG G) hsync.wf_seed
    hsync.wf_state.inTransit_valid hsync.wf_state.sent_le_keys a i e]
  have hstR := hsync.stR_eq; subst hstR
  cases hend : sM.1.ended
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hfind : sM.1.inTransit.find? (fun r => r.ad == a && r.ct == (i, e)) with
    | none =>
      refine ⟨none, mkRState G k sM.1, sM, ?_, rfl, hsync, hok, rfl, hend⟩
      simp only [deliverImpl, modifyGet_run, FSAEAD.deliver, mkRState, hend, Bool.false_eq_true,
        ↓reduceIte, beq_nat_prod_eq, hfind]
    | some r =>
      have hr_mem : r ∈ sM.1.inTransit := List.mem_of_find?_eq_some hfind
      have hr_pred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hr_pred
      rcases hsync.wf_state.inTransit_valid r hr_mem with ⟨hi1, hisent, hct⟩
      have hidx : r.idx = i := (congrArg Prod.fst (hr_pred.2.symm.trans hct)).symm
      have he_eq : e = ae.enc (keyAt G k (i - 1)) (i, a) r.msg := by
        have := congrArg Prod.snd (hr_pred.2.symm.trans hct)
        simpa [hidx, hr_pred.1] using this
      have hoka : ok a = true := hr_pred.1 ▸ hok r hr_mem
      have hdec : ae.dec (keyAt G k (i - 1)) (i, a) e = some r.msg := by
        rw [he_eq]; exact hae (keyAt G k (i - 1)) (i, a) r.msg hoka
      by_cases hcont : i ∈ sM.1.skipped
      · simp only [hcont, ↓reduceIte]
        have hmax : max sM.1.receiverIdx i = sM.1.receiverIdx :=
          Nat.max_eq_left (le_of_lt (hsync.wf_state.skipped_bounds i hcont).2)
        refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_modifyH G hsync.wf_seed rfl, ?_, rfl⟩,
          inTransitOk_removeFromTransit hok r.idx, rfl, hend⟩
        · simp only [deliverImpl, modifyGet_run, FSAEAD.deliver, mkRState, hend, Bool.false_eq_true,
            ↓reduceIte, beq_nat_prod_eq, hfind,
            receive_real_of_contains ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont,
            hdec]
          simp [hidx, HState.removeFromTransit, State.removeFromTransit, hmax]
        · rw [hidx]
          exact wfState_accept_contains ae G hsync.wf_state hcont (sM.1.win || false)
            sM.1.ended sM.1.lf
      · simp only [hcont, ↓reduceIte]
        by_cases hout : i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1
        · simp only [hout, ↓reduceIte]
          refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_modifyH G hsync.wf_seed rfl, ?_, rfl⟩, hok, rfl, hend⟩
          · simp only [deliverImpl, modifyGet_run, FSAEAD.deliver, mkRState, hend,
              Bool.false_eq_true, ↓reduceIte, beq_nat_prod_eq, hfind,
              receive_real_of_out_of_window ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont hout]
            rfl
          · exact ⟨hsync.wf_state.sent_le_keys, hsync.wf_state.rcv_le_keys,
              hsync.wf_state.keys_eq_sent_of_uncorr, hsync.wf_state.rcv_le_sent_of_uncorr,
              hsync.wf_state.corr_inv, hsync.wf_state.skipped_bounds,
              hsync.wf_state.inTransit_valid, hsync.wf_state.pending_inTransit⟩
        · simp only [hout, ↓reduceIte]
          have hlt : sM.1.receiverIdx < i := by omega
          have hmax : max sM.1.receiverIdx i = i := Nat.max_eq_right (le_of_lt hlt)
          have hsent_keys := hsync.wf_state.sent_le_keys
          have hisent' : i ≤ sM.1.lastSentIdx := hidx ▸ hisent
          refine ⟨_, _, _, ?_, rfl, ⟨wfSeed_modifyH G hsync.wf_seed rfl, ?_, rfl⟩,
            inTransitOk_removeFromTransit hok r.idx, rfl, hend⟩
          · simp only [deliverImpl, modifyGet_run, FSAEAD.deliver, mkRState, hend,
              Bool.false_eq_true, ↓reduceIte, beq_nat_prod_eq, hfind,
              receive_real_of_in_window ae G maxSkip k sM.1.receiverIdx sM.1.skipped a i e hcont hout,
              hdec]
            simp [hidx, HState.removeFromTransit, State.removeFromTransit, hmax]
          · rw [hidx]
            have hwf' := wfState_accept_in_window ae G hsync.wf_state (n := sM.1.keys.length)
              hlt le_rfl (by omega)
              (fun huncorr => ⟨hsync.wf_state.keys_eq_sent_of_uncorr huncorr, hisent'⟩)
              (sM.1.win || false) sM.1.ended sM.1.lf
            simpa [← hsync.wf_seed.keys_eq] using hwf'
  · simp only [↓reduceIte]
    refine ⟨none, mkRState G k sM.1, sM, ?_, rfl, hsync, hok, rfl, hend⟩
    simp [deliverImpl, FSAEAD.deliver, mkRState, hend]

omit [DecidableEq M] in
theorem inTransitOk_of_injectH_not_lookahead {ok : AD → Bool} {k : CK} {stR : RState} {sM sM' : St}
    {q : AD × (ℕ × C)} {u : Option (ReceiveResult M)}
    (hsync : SyncRM ae G k stR sM) (hok : InTransitOk ok sM.1)
    (hlook : sM.1.ended = false →
      (sM.1.inTransit.any (fun r => r.ad == q.1 && r.ct == q.2)) = false →
      q.2.1 ∉ sM.1.skipped →
      ¬ (q.2.1 ≤ sM.1.receiverIdx ∨ maxSkip < q.2.1 - sM.1.receiverIdx - 1) →
      sM.1.senderCorruptedAt = none → q.2.1 ≤ sM.1.lastSentIdx)
    (hM : (injectH ae G maxSkip (hp 0 0 false) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) q).run sM = pure (u, sM')) :
    InTransitOk ok sM'.1 := by
  rcases q with ⟨a, i, e⟩
  have hcomp : sM.1.ended = false →
      (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false →
      i ∉ sM.1.skipped →
      ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1) →
      sM.1.lastSentIdx < i → sM.1.isCompromised i = true := by
    intro hend hany hcont hout hlt
    have hcorr : sM.1.senderCorruptedAt.isSome = true := by
      cases h : sM.1.senderCorruptedAt with
      | none =>
        have := hlook hend hany hcont hout h
        dsimp only at this
        omega
      | some c => rfl
    exact isCompromised_of_corr_lt_sent ae G hsync.wf_state hlt hcorr
  have hsk_comp : ∀ j ∈ sM.1.skipped, sM.1.lastSentIdx < j → sM.1.isCompromised j = true := by
    intro j hj hlt
    exact isCompromised_of_wfState_lt ae G hsync.wf_state
      (le_of_lt (hsync.wf_state.skipped_bounds j hj).2) hlt
  rw [injectH_run_of_wfSeed_not_lookahead ae G maxSkip false hsync.wf_seed
    hsync.wf_state.skipped_bounds hsync.wf_state.rcv_le_keys hsk_comp a i e hcomp] at hM
  split_ifs at hM
  · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    exact hok
  · cases hdec : ae.dec (keyAt G k (i - 1)) (i, a) e <;> simp only [hdec] at hM
    · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
      exact hok
    · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
      exact inTransitOk_removeFromTransit hok i
  · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
    exact hok
  · dsimp only at hM
    cases hdec : ae.dec (keyAt G k (i - 1)) (i, a) e <;> simp only [hdec] at hM
    · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
      exact hok
    · obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
      exact inTransitOk_removeFromTransit hok i

omit [DecidableEq M] in
theorem inTransitOk_of_injectH_lookahead_none {ok : AD → Bool} {sM sM' : St}
    (a : AD) (i : ℕ) (e : C) {u : Option (ReceiveResult M)}
    (hok : InTransitOk ok sM.1)
    (hend : sM.1.ended = false)
    (hany : (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false)
    (hcont : i ∉ sM.1.skipped)
    (hout : ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1))
    (hlt : sM.1.lastSentIdx < i)
    (huncorr : sM.1.senderCorruptedAt = none)
    (hM : (injectH ae G maxSkip (hp 0 0 false) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) (a, i, e)).run sM = pure (u, sM')) :
    InTransitOk ok sM'.1 := by
  have huncompM : sM.1.isCompromised i = false := by
    simp [HState.isCompromised, huncorr]
  have hM0 : (injectH ae G maxSkip (hp 0 0 false) (DG G)
      (none : Option (SpecialOps AD M C ProbComp)) (a, i, e)).run sM =
      pure (some .rejected, sM) := by
    unfold injectH
    simp only [StateT.run_bind, getH_run, pure_bind, hend, hany, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte,
      receiveH_none_run_of_lookahead_reject ae G maxSkip (hp 0 0 false) (DG G) a i e hcont hout
        ⟨⟨rfl, hlt⟩, huncompM⟩,
      StateT.run_pure]
  rw [hM0] at hM
  obtain ⟨_, rfl⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM).symm
  exact hok

theorem simulateQ_run_of_syncRM_corrupted_or_ended_on {ok : AD → Bool}
    (hae : ae.CorrectOn fun ia => ok ia.2)
    {α β : Type}
    (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α)
    (hoa : oa.IsQueryBoundP (fun t => encBadAD (SS := RatchetSenderState CK)
      (RS := RatchetReceiverState CK MK) (Msg := M) (C := ℕ × C) ok t = true) 0)
    {k : CK} {stR : RState} {sM : St}
    (fR : α × RState → ProbComp β) (fM : α × St → ProbComp β)
    (hf : ∀ a stR' sM', SyncRM ae G k stR' sM' → fR (a, stR') = fM (a, sM'))
    (hsync : SyncRM ae G k stR sM) (hok : InTransitOk ok sM.1)
    (hce : sM.1.senderCorruptedAt.isSome = true ∨ sM.1.ended = true) :
    ((simulateQ (implR ae G maxSkip) oa).run stR >>= fR) =
      ((simulateQ (implH ideal ae G maxSkip false) oa).run sM >>= fM) := by
  induction oa using OracleComp.inductionOn generalizing stR sM with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hf a stR sM hsync
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have hnp : ¬ (encBadAD (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (Msg := M) (C := ℕ × C) ok t = true) :=
      hoa.1.resolve_right (Nat.lt_irrefl 0)
    have hcont : ∀ u, (cont u).IsQueryBoundP (fun t => encBadAD (SS := RatchetSenderState CK)
        (RS := RatchetReceiverState CK MK) (Msg := M) (C := ℕ × C) ok t = true) 0 :=
      fun u => by simpa [hnp] using hoa.2 u
    simp only [simulateQ_query_bind]
    rcases t with n | (((((q | q) | q) | q) | q) | q)
    · exact state_bind_eq_of_liftM (query (spec := unifSpec) n) fun u =>
        ih u (hcont u) hsync hok hce
    · have hq : ok q.1 = true := by simpa [encBadAD] using hnp
      rcases transmit_syncRM ideal ae G maxSkip hsync q with ⟨u, stR', sM', hR, hM, hsync', hca, hend⟩
      have hok' := inTransitOk_of_transmitH ideal ae G hsync.wf_seed hok hq hM
      exact state_bind_eq_of_pure hR hM
        (ih u (hcont u) hsync' hok' (by rcases hce with h | h <;> [left; right] <;> simpa [hca, hend] using h))
    · have hq : ok q.1 = true := by simpa [encBadAD] using hnp
      rcases challenge_syncRM ideal ae G maxSkip hsync q with ⟨u, stR', sM', hR, hM, hsync', hca, hend⟩
      have hok' := inTransitOk_of_challengeH ideal ae G hsync.wf_seed hok hq hM
      exact state_bind_eq_of_pure hR hM
        (ih u (hcont u) hsync' hok' (by rcases hce with h | h <;> [left; right] <;> simpa [hca, hend] using h))
    · rcases corruptSender_syncRM ae G hsync q with ⟨u, stR', sM', hR, hM, hsync', hce'⟩
      have hok' := inTransitOk_of_corruptSenderH ae G hsync hok hM
      exact state_bind_eq_of_pure hR hM (ih u (hcont u) hsync' hok' hce')
    · rcases corruptReceiver_syncRM ae G hsync q with ⟨u, stR', sM', hR, hM, hsync', hce', _⟩
      have hok' := inTransitOk_of_corruptReceiverH ae G hsync hok hM
      exact state_bind_eq_of_pure hR hM (ih u (hcont u) hsync' hok' (hce' hce))
    · rcases deliver_syncRM_on ae G maxSkip hae hsync hok q with
        ⟨u, stR', sM', hR, hM, hsync', hok', hca, hend⟩
      exact state_bind_eq_of_pure hR hM
        (ih u (hcont u) hsync' hok' (by rcases hce with h | h <;> [left; right] <;> simpa [hca, hend] using h))
    · have hlook : sM.1.ended = false →
          (sM.1.inTransit.any (fun r => r.ad == q.1 && r.ct == q.2)) = false →
          q.2.1 ∉ sM.1.skipped →
          ¬ (q.2.1 ≤ sM.1.receiverIdx ∨ maxSkip < q.2.1 - sM.1.receiverIdx - 1) →
          sM.1.senderCorruptedAt = none → q.2.1 ≤ sM.1.lastSentIdx := by
        intro hend _ _ _ huncorr
        rcases hce with h | h
        · simp [huncorr] at h
        · rw [hend] at h; exact absurd h Bool.false_ne_true
      rcases inject_syncRM_of_not_lookahead ae G maxSkip hsync q hlook with
        ⟨u, stR', sM', hR, hM, hsync', hca, hend, _, _⟩
      have hok' := inTransitOk_of_injectH_not_lookahead ae G maxSkip hsync hok hlook hM
      exact state_bind_eq_of_pure hR hM
        (ih u (hcont u) hsync' hok' (by rcases hce with h | h <;> [left; right] <;> simpa [hca, hend] using h))

theorem deliver_syncRML_on {ok : AD → Bool} (hae : ae.CorrectOn fun ia => ok ia.2)
    {k : CK} {stR : RState} {sM sL : St}
    (hsync : SyncRML ae G k stR sM sL) (hok : InTransitOk ok sM.1) (q : AD × (ℕ × C)) :
    ∃ u stR' sM' sL',
      (deliverImpl (fromAEADPRG ae G maxSkip) q).run stR = pure (u, stR') ∧
      (deliverH ae G maxSkip (hp 0 0 false) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sM = pure (u, sM') ∧
      (deliverH ae G maxSkip (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sL = pure (u, sL') ∧
      SyncRML ae G k stR' sM' sL' ∧
      InTransitOk ok sM'.1 := by
  rcases deliver_syncRM_on ae G maxSkip hae hsync.syncRM hok q with
    ⟨u, stR', sM', hR, hM, hsyncRM', hok', hca, hend⟩
  have hL_and_keys :
      (deliverH ae G maxSkip (hp 0 0 true) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q).run sL =
        pure (u, ({ sM'.1 with keys := sL.1.keys }, sL.2)) ∧
      sM'.1.keys = sM.1.keys := by
    rcases q with ⟨a, i, e⟩
    let K := sL.1.keys
    have hsL1 : sL.1 = { sM.1 with keys := K } := hsync.sL_eq
    have hvalidL : ∀ r ∈ sL.1.inTransit,
        1 ≤ r.idx ∧ r.idx ≤ sL.1.lastSentIdx ∧
        r.ct = (r.idx, ae.enc (keyAt G k (r.idx - 1)) (r.idx, r.ad) r.msg) := by
      rw [hsL1]; exact hsync.syncRM.wf_state.inTransit_valid
    have hkeysL : sL.1.lastSentIdx ≤ sL.1.keys.length := by
      have := hsync.syncRM.wf_state.sent_le_keys.trans hsync.keys_le
      rw [hsL1]; exact this
    have hM' := hM
    rw [deliverH_run_of_wfSeed ae G maxSkip (hp 0 0 false) (DG G) hsync.syncRM.wf_seed
      hsync.syncRM.wf_state.inTransit_valid hsync.syncRM.wf_state.sent_le_keys a i e] at hM'
    rw [deliverH_run_of_wfSeed ae G maxSkip (hp 0 0 true) (DG G) hsync.wf_seedL
      hvalidL hkeysL a i e]
    have hcomp_eq : ∀ idx, ({ sM.1 with keys := K } : HS).isCompromised idx =
        sM.1.isCompromised idx := fun _ => rfl
    have hsL_pair : sL = ({ sM.1 with keys := K }, sL.2) := Prod.ext hsL1 rfl
    simp only [hsL1, hcomp_eq]
    cases hend0 : sM.1.ended
    · simp only [hend0, Bool.false_eq_true, ↓reduceIte] at hM' ⊢
      cases hfind : sM.1.inTransit.find? (fun r => r.ad == a && r.ct == (i, e)) with
      | none =>
        simp only [hfind] at hM' ⊢
        injection hM' with hM'; injection hM' with hu hsM'; subst hu hsM'
        exact ⟨by rw [← hsL_pair], rfl⟩
      | some r =>
        simp only [hfind] at hM' ⊢
        by_cases hcont : i ∈ sM.1.skipped
        · simp only [hcont, ↓reduceIte] at hM' ⊢
          injection hM' with hM'; injection hM' with hu hsM'; subst hu hsM'
          exact ⟨by simp [HState.removeFromTransit], rfl⟩
        · by_cases hout : i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1
          · simp only [hcont, hout, ↓reduceIte] at hM' ⊢
            injection hM' with hM'; injection hM' with hu hsM'; subst hu hsM'
            exact ⟨rfl, rfl⟩
          · simp only [hcont, hout, ↓reduceIte] at hM' ⊢
            injection hM' with hM'; injection hM' with hu hsM'; subst hu hsM'
            exact ⟨by simp [HState.removeFromTransit], rfl⟩
    · simp only [hend0, ↓reduceIte] at hM' ⊢
      injection hM' with hM'; injection hM' with hu hsM'; subst hu hsM'
      exact ⟨by rw [← hsL_pair], rfl⟩
  refine ⟨u, stR', sM', ({ sM'.1 with keys := sL.1.keys }, sL.2), hR, hM, hL_and_keys.1,
    ⟨hsyncRM', wfSeed_modifyH G hsync.wf_seedL rfl, rfl, ?_, ?_, ?_⟩, hok'⟩
  · rw [hL_and_keys.2]; exact hsync.keys_le
  · rw [hca]; exact hsync.uncorr
  · rw [hend]; exact hsync.not_ended

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
private lemma closeBy_state_bind_of_eq {α β : Type}
    {mR : StateT RState ProbComp α} {mM mL : StateT St ProbComp α}
    {stR : RState} {sM sL : St} {u : α} {stR' : RState} {sM' : St}
    (hR : mR.run stR = pure (u, stR'))
    (hM : mM.run sM = pure (u, sM'))
    {kR : α → StateT RState ProbComp β}
    {kM kL : α → StateT St ProbComp β}
    {fR : β × RState → ProbComp Bool}
    {fM fL : β × St → ProbComp Bool}
    (heq : ((kR u).run stR' >>= fR) = ((kM u).run sM' >>= fM)) :
    CloseBy (((mR >>= kR).run stR) >>= fR)
            (((mM >>= kM).run sM) >>= fM)
            (((mL >>= kL).run sL) >>= fL) :=
  closeBy_of_eq (state_bind_eq_of_pure hR hM heq)

omit [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
private lemma closeBy_state_bind_of_evalDist_eq_one {α β : Type}
    {mR : StateT RState ProbComp α} {mM mL : StateT St ProbComp α}
    {stR : RState} {sM sL : St} {u : α} {sL' : St}
    (hL : mL.run sL = pure (u, sL'))
    {kR : α → StateT RState ProbComp β}
    {kM kL : α → StateT St ProbComp β}
    {fR : β × RState → ProbComp Bool}
    {fM fL : β × St → ProbComp Bool}
    (hone : 𝒟[(kL u).run sL' >>= fL] {true} = 1) :
    CloseBy (((mR >>= kR).run stR) >>= fR)
            (((mM >>= kM).run sM) >>= fM)
            (((mL >>= kL).run sL) >>= fL) := by
  apply closeBy_of_evalDist_eq_one
  rw [StateT.run_bind, hL, pure_bind]
  exact hone

theorem closeBy_simulateQ_of_syncRML_on {ok : AD → Bool} (hae : ae.CorrectOn fun ia => ok ia.2)
    {α : Type} {k : CK}
    (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α)
    (hoa : oa.IsQueryBoundP (fun t => encBadAD (SS := RatchetSenderState CK)
      (RS := RatchetReceiverState CK MK) (Msg := M) (C := ℕ × C) ok t = true) 0)
    (fR : α × RState → ProbComp Bool) (fM fL : α × St → ProbComp Bool)
    (hfRM : ∀ a stR sM, SyncRM ae G k stR sM → fR (a, stR) = fM (a, sM))
    (hfL : ∀ z : α × St, z.2.1.lf = true → 𝒟[fL z] = 𝒟[(pure true : ProbComp Bool)]) :
    ∀ {stR : RState} {sM sL : St},
      SyncRML ae G k stR sM sL →
      InTransitOk ok sM.1 →
      CloseBy
        ((simulateQ (implR ae G maxSkip) oa).run stR >>= fR)
        ((simulateQ (implH ideal ae G maxSkip false) oa).run sM >>= fM)
        ((simulateQ (implH ideal ae G maxSkip true) oa).run sL >>= fL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro stR sM sL hsync _
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact closeBy_of_eq (hfRM a stR sM hsync.syncRM)
  | query_bind t r ih =>
    intro stR sM sL hsync hok
    rw [isQueryBoundP_query_bind_iff] at hoa
    have hnp : ¬ (encBadAD (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (Msg := M) (C := ℕ × C) ok t = true) :=
      hoa.1.resolve_right (Nat.lt_irrefl 0)
    have hcont : ∀ u, (r u).IsQueryBoundP (fun t => encBadAD (SS := RatchetSenderState CK)
        (RS := RatchetReceiverState CK MK) (Msg := M) (C := ℕ × C) ok t = true) 0 :=
      fun u => by simpa [hnp] using hoa.2 u
    rw [simulateQ_query_bind, simulateQ_query_bind, simulateQ_query_bind]
    rcases t with n | (((((q | q) | q) | q) | q) | q)
    · exact closeBy_state_bind_of_liftM (query (spec := unifSpec) n) fun u =>
        ih u (hcont u) hsync hok
    · have hq : ok q.1 = true := by simpa [encBadAD] using hnp
      rcases transmit_syncRML ideal ae G maxSkip hsync q with
        ⟨u, stR', sM', sL', hR, hM, hL, hsync'⟩
      have hok' := inTransitOk_of_transmitH ideal ae G hsync.syncRM.wf_seed hok hq hM
      exact closeBy_state_bind_of_pure hR hM hL (ih u (hcont u) hsync' hok')
    · have hq : ok q.1 = true := by simpa [encBadAD] using hnp
      rcases challenge_syncRML ideal ae G maxSkip hsync q with
        ⟨u, stR', sM', sL', hR, hM, hL, hsync'⟩
      have hok' := inTransitOk_of_challengeH ideal ae G hsync.syncRM.wf_seed hok hq hM
      exact closeBy_state_bind_of_pure hR hM hL (ih u (hcont u) hsync' hok')
    · rcases corruptSender_syncRM ae G hsync.syncRM q with
        ⟨u, stR', sM', hR, hM, hsyncRM', hcorr'⟩
      have hok' := inTransitOk_of_corruptSenderH ae G hsync.syncRM hok hM
      exact closeBy_state_bind_of_eq hR hM
        (simulateQ_run_of_syncRM_corrupted_or_ended_on ideal ae G maxSkip hae
          (r u) (hcont u) fR fM hfRM hsyncRM' hok' hcorr')
    · rcases corruptReceiver_syncRML ae G hsync q with
        ⟨u, stR', sM', sL', hR, hM, hL, hsync'⟩ | ⟨u, stR', sM', hR, hM, hsyncRM', hcorr'⟩
      · have hok' := inTransitOk_of_corruptReceiverH ae G hsync.syncRM hok hM
        exact closeBy_state_bind_of_pure hR hM hL (ih u (hcont u) hsync' hok')
      · have hok' := inTransitOk_of_corruptReceiverH ae G hsync.syncRM hok hM
        exact closeBy_state_bind_of_eq hR hM
          (simulateQ_run_of_syncRM_corrupted_or_ended_on ideal ae G maxSkip hae
            (r u) (hcont u) fR fM hfRM hsyncRM' hok' hcorr')
    · rcases deliver_syncRML_on ae G maxSkip hae hsync hok q with
        ⟨u, stR', sM', sL', hR, hM, hL, hsync', hok'⟩
      exact closeBy_state_bind_of_pure hR hM hL (ih u (hcont u) hsync' hok')
    · rcases q with ⟨a, i, e⟩
      by_cases hcond : sM.1.ended = false ∧
          (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false ∧
          i ∉ sM.1.skipped ∧
          ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1) ∧
          sM.1.lastSentIdx < i
      · rcases hcond with ⟨hend, hany, hcont_sk, hout, hlt⟩
        cases hdec : ae.dec (keyAt G k (i - 1)) (i, a) e with
        | none =>
          rcases inject_syncRML_of_lookahead_none ae G maxSkip hsync a i e
              hend hany hcont_sk hout hlt hdec with
            ⟨u, stR', sM', sL', hR, hM, hL, hsync'⟩
          have hok' := inTransitOk_of_injectH_lookahead_none ae G maxSkip a i e hok
            hend hany hcont_sk hout hlt hsync.uncorr hM
          exact closeBy_state_bind_of_pure hR hM hL (ih u (hcont u) hsync' hok')
        | some msg =>
          rcases injectL_lookahead_some ae G maxSkip hsync a i e msg
              hend hany hcont_sk hout hlt hdec with
            ⟨u, sL', hL, hendL', hlfL'⟩
          exact closeBy_state_bind_of_evalDist_eq_one hL
            (evalDist_runL_eq_one_of_ended_lf ideal ae G maxSkip (hp 0 0 true) (DG G) (r u) fL hfL
              hendL' hlfL')
      · have hlook : sM.1.ended = false →
            (sM.1.inTransit.any (fun r => r.ad == (a, (i, e)).1 && r.ct == (a, (i, e)).2)) = false →
            (a, (i, e)).2.1 ∉ sM.1.skipped →
            ¬ ((a, (i, e)).2.1 ≤ sM.1.receiverIdx ∨ maxSkip < (a, (i, e)).2.1 - sM.1.receiverIdx - 1) →
            sM.1.senderCorruptedAt = none → (a, (i, e)).2.1 ≤ sM.1.lastSentIdx := by
          intro hend hany hcont_sk hout _
          by_contra hlt
          exact hcond ⟨hend, hany, hcont_sk, hout, Nat.lt_of_not_le hlt⟩
        rcases inject_syncRML_of_not_lookahead ae G maxSkip hsync (a, i, e) hlook with
          ⟨u, stR', sM', sL', hR, hM, hL, hsync'⟩
        have hok' := inTransitOk_of_injectH_not_lookahead ae G maxSkip hsync.syncRM hok hlook hM
        exact closeBy_state_bind_of_pure hR hM hL (ih u (hcont u) hsync' hok')

theorem start_on (A : RatchetAdversary CK MK AD M C) (ok : AD → Bool)
    (hae : ae.CorrectOn fun ia => ok ia.2) (hA : EncADsOk ok A) :
    advantage (fromAEADPRG ae G maxSkip) A ≤
      2 * ENNReal.absDiff (𝒟[hybridA ideal ae G maxSkip 0 false A] {true}) (1 / 2) +
        2 * 𝒟[hybridA ideal ae G maxSkip 0 true A] {true} := by
  have hclose : CloseBy
      (($ᵗ Bool) >>= fun b => ($ᵗ CK) >>= fun k =>
        (simulateQ (implR ae G maxSkip) A).run (initState (fromAEADPRG ae G maxSkip) k b) >>=
          fun z => pure ((z.2.b == z.1) || z.2.win))
      (($ᵗ Bool) >>= fun b => ($ᵗ CK) >>= fun k =>
        (simulateQ (implH ideal ae G maxSkip false) A).run (hInit b (.seed k)) >>=
          fun z => pure (hOut false z))
      (($ᵗ Bool) >>= fun b => ($ᵗ CK) >>= fun k =>
        (simulateQ (implH ideal ae G maxSkip true) A).run (hInit b (.seed k)) >>=
          fun z => pure (hOut true z)) := by
    refine closeBy_bind ($ᵗ Bool) fun b => closeBy_bind ($ᵗ CK) fun k => ?_
    refine closeBy_simulateQ_of_syncRML_on ideal ae G maxSkip hae A hA _ _ _ ?_ ?_
      (syncRML_init ae G maxSkip k b) (inTransitOk_hInit ok b (.seed k))
    · intro a stR sM hsync
      rw [hsync.stR_eq]
      rfl
    · intro z hlf
      simp [hOut, hlf]
  have hcb := hclose {true}
  rw [← game_evalDist_eq ae G maxSkip A,
      ← hybA_zero_evalDist ideal ae G maxSkip false A,
      ← hybA_zero_evalDist ideal ae G maxSkip true A] at hcb
  have hdiff : ENNReal.absDiff
      (𝒟[game (fromAEADPRG ae G maxSkip) A] {true})
      (𝒟[hybridA ideal ae G maxSkip 0 false A] {true}) ≤
      𝒟[hybridA ideal ae G maxSkip 0 true A] {true} :=
    ENNReal.absDiff_le_iff.mpr hcb
  have htri : ENNReal.absDiff (𝒟[game (fromAEADPRG ae G maxSkip) A] {true}) (1 / 2) ≤
      ENNReal.absDiff (𝒟[hybridA ideal ae G maxSkip 0 false A] {true}) (1 / 2) +
        𝒟[hybridA ideal ae G maxSkip 0 true A] {true} := by
    calc ENNReal.absDiff (𝒟[game (fromAEADPRG ae G maxSkip) A] {true}) (1 / 2)
        ≤ ENNReal.absDiff (𝒟[game (fromAEADPRG ae G maxSkip) A] {true})
            (𝒟[hybridA ideal ae G maxSkip 0 false A] {true}) +
          ENNReal.absDiff (𝒟[hybridA ideal ae G maxSkip 0 false A] {true}) (1 / 2) :=
          ENNReal.absDiff_triangle _ _ _
      _ ≤ 𝒟[hybridA ideal ae G maxSkip 0 true A] {true} +
          ENNReal.absDiff (𝒟[hybridA ideal ae G maxSkip 0 false A] {true}) (1 / 2) := by
          gcongr
      _ = ENNReal.absDiff (𝒟[hybridA ideal ae G maxSkip 0 false A] {true}) (1 / 2) +
          𝒟[hybridA ideal ae G maxSkip 0 true A] {true} := add_comm _ _
  unfold advantage
  rw [MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure, ← mul_add]
  gcongr

end Steps

end CryptoGames.FSAEAD.Thm5On

namespace CryptoGames.FSAEAD.Thm5

open MeasureTheory CryptoGames.Lazy

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]

/-! ## Cumulative chain-PRG hops at `t = 0` -/

section Stage1PRG

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

local notation "St" => HSt CK MK AD M C
local notation "SP" => StateT (HSt CK MK AD M C) ProbComp

variable (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

theorem rc_genStep_L2_gen (k t₀ : ℕ) (la : Bool) :
    RC (seedFill (k + 1)) (genStep G (hp (k + 1) t₀ la) (DG G) : SP Unit)
      (genStep G (hp k t₀ la) DU) := by
  refine ⟨?_, comm_genStep_seed G _ (k + 1) le_rfl⟩
  rintro ⟨h, sl⟩
  cases sl with
  | seed w =>
    simp only [fillSt, fillOut, seedFill, genStep_run_seed, map_pure, pure_bind]
    exact DEq.refl _
  | mat pos mt =>
    by_cases hlt : h.keys.length < pos
    · simp only [fillSt, fillOut, seedFill, genStep_run_mat_lt _ _ _ _ _ _ hlt, map_pure,
        pure_bind, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]
      exact DEq.refl _
    · simp only [fillSt, fillOut, seedFill, genStep_run_mat_ge _ _ _ _ _ _ hlt, map_pure,
        pure_bind]
      exact DEq.refl _
  | unknown =>
    by_cases hg : k + 1 ≤ h.keys.length
    · have h1 : ¬ h.keys.length < (hp k t₀ la).j := by simp [hp]; omega
      simp only [fillSt, fillOut, seedFill, hg, ite_true, genStep_run_seed,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      exact DEq.refl _
    · by_cases hk : h.keys.length < k
      · have h1 : h.keys.length < (hp k t₀ la).j := by simp [hp]; omega
        have h2 : h.keys.length < (hp (k + 1) t₀ la).j := by simp [hp]; omega
        have h3 : ¬ k + 1 ≤ h.keys.length + 1 := by omega
        simp only [fillSt, fillOut, seedFill, hg, ite_false, genStep_run_unknown_lt _ _ _ _ h1,
          genStep_run_unknown_lt _ _ _ _ h2, map_pure, pure_bind, map_eq_bind_pure_comp,
          bind_assoc, Function.comp_apply, List.length_append, List.length_singleton, h3]
        exact DEq.refl _
      · have h1 : ¬ h.keys.length < (hp k t₀ la).j := by simp [hp]; omega
        have h2 : h.keys.length < (hp (k + 1) t₀ la).j := by simp [hp]; omega
        have h3 : k + 1 ≤ h.keys.length + 1 := by omega
        simp only [fillSt, fillOut, seedFill, hg, ite_false, genStep_run_unknown_lt _ _ _ _ h2,
          genStep_run_unknown_ge _ _ _ _ h1, map_pure, pure_bind, map_eq_bind_pure_comp,
          bind_assoc, Function.comp_apply, List.length_append, List.length_singleton, h3,
          ite_true, DU]
        exact DEq.swap _ _ _

section L2Gen

variable (k t₀ : ℕ) (la : Bool)
  (hI : Idem (seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1)))
  (hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length →
    seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1) h =
      seedFill (k + 1) h')
include hI hK

theorem rc_encIdx_L2_gen (i : ℕ) (a : AD) (msg : M) :
    RC (seedFill (k + 1))
      (encIdxWith ideal ae (hp (k + 1) t₀ la) (none : Option (SpecialOps AD M C ProbComp)) i a msg :
        SP C)
      (encIdxWith ideal ae (hp k t₀ la) none i a msg) := by
  unfold encIdxWith
  refine RC.bind (rc_getH hI) fun st => ?_
  rw [kind_hp la k (k + 1) t₀ st i]
  split
  · exact rc_sampleH hI _
  · exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
  · split
    · exact RC.pure hI _
    · exact rc_sampleH hI _

theorem rc_genN_L2_gen (n : ℕ) :
    RC (seedFill (k + 1)) (genN G (hp (k + 1) t₀ la) (DG G) n : SP Unit)
      (genN G (hp k t₀ la) DU n) := by
  induction n with
  | zero => exact RC.pure hI _
  | succ n ih => exact RC.bind (rc_genStep_L2_gen G k t₀ la) fun _ => ih

theorem rc_genUpTo_L2_gen (i : ℕ) :
    RC (seedFill (k + 1)) (genUpTo G (hp (k + 1) t₀ la) (DG G) i : SP Unit)
      (genUpTo G (hp k t₀ la) DU i) :=
  RC.bind (rc_getH hI) fun _ => rc_genN_L2_gen G k t₀ la hI hK _

theorem rc_transmitH_L2_gen (q : AD × M) :
    RC (seedFill (k + 1))
      (transmitHWith ideal ae G (hp (k + 1) t₀ la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q)
      (transmitHWith ideal ae G (hp k t₀ la) DU none q) := by
  unfold transmitHWith
  refine RC.bind (rc_getH hI) fun st => ?_
  split
  · exact RC.pure hI _
  · refine RC.bind (rc_genUpTo_L2_gen G k t₀ la hI hK _) fun _ => ?_
    refine RC.bind (rc_encIdx_L2_gen ideal ae k t₀ la hI hK _ _ _) fun e => ?_
    exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _

theorem rc_challengeH_L2_gen (q : AD × M × M) :
    RC (seedFill (k + 1))
      (challengeHWith ideal ae G (hp (k + 1) t₀ la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q)
      (challengeHWith ideal ae G (hp k t₀ la) DU none q) := by
  unfold challengeHWith
  refine RC.bind (rc_getH hI) fun st => ?_
  split
  · exact RC.pure hI _
  · refine RC.bind (rc_genUpTo_L2_gen G k t₀ la hI hK _) fun _ => ?_
    refine RC.bind (rc_encIdx_L2_gen ideal ae k t₀ la hI hK _ _ _) fun e => ?_
    exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _

theorem rc_decIdx_L2_gen (hint : Option M) (i : ℕ) (a : AD) (e : C) :
    RC (seedFill (k + 1))
      (decIdx ae (hp (k + 1) t₀ la) (none : Option (SpecialOps AD M C ProbComp)) hint i a e :
        SP (Option M))
      (decIdx ae (hp k t₀ la) none hint i a e) := by
  unfold decIdx
  split
  · exact RC.pure hI _
  · refine RC.bind (rc_getH hI) fun st => ?_
    rw [kind_hp la k (k + 1) t₀ st i]
    split
    · exact RC.pure hI _
    · exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
    · exact RC.pure hI _

theorem rc_receiveH_L2_gen (hint : Option M) (a : AD) (c : ℕ × C) :
    RC (seedFill (k + 1))
      (receiveH ae G maxSkip (hp (k + 1) t₀ la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) hint a c)
      (receiveH ae G maxSkip (hp k t₀ la) DU none hint a c) := by
  obtain ⟨i, e⟩ := c
  unfold receiveH
  refine RC.bind (rc_getH hI) fun st => ?_
  split
  · refine RC.bind (rc_decIdx_L2_gen ae k t₀ la hI hK _ _ _ _) fun r => ?_
    split
    · exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _
    · exact RC.pure hI _
  · split
    · exact RC.pure hI _
    · refine rc_ite _ (fun _ => ?_) (fun _ => ?_)
      · exact RC.pure hI _
      · refine RC.bind (rc_genUpTo_L2_gen G k t₀ la hI hK _) fun _ => ?_
        refine RC.bind (rc_decIdx_L2_gen ae k t₀ la hI hK _ _ _ _) fun r => ?_
        split
        · exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _
        · exact RC.pure hI _

theorem rc_corruptSenderH_L2_gen (u : Unit) :
    RC (seedFill (k + 1))
      (corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G (hp (k + 1) t₀ la) u)
      (corruptSenderH G (hp k t₀ la) u) := by
  unfold corruptSenderH
  refine RC.bind (rc_getH hI) fun st => ?_
  split
  · exact RC.pure hI _
  · refine rc_ite _ (fun _ => ?_) (fun _ => ?_)
    · exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _
    · refine RC.bind (rc_senderKey_L2 G k hI hK) fun w => ?_
      exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _

theorem rc_corruptReceiverH_L2_gen (u : Unit) :
    RC (seedFill (k + 1))
      (corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G
        (hp (k + 1) t₀ la) u)
      (corruptReceiverH G (hp k t₀ la) u) := by
  unfold corruptReceiverH
  refine RC.bind (rc_getH hI) fun st => ?_
  split
  · exact RC.pure hI _
  · refine rc_ite _ (fun _ => ?_) (fun _ => ?_)
    · exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _
    · refine RC.bind (rc_senderKey_L2 G k hI hK) fun w => ?_
      refine RC.bind (rc_getH hI) fun st' => ?_
      exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _

theorem rc_deliverH_L2_gen (q : AD × (ℕ × C)) :
    RC (seedFill (k + 1))
      (deliverH ae G maxSkip (hp (k + 1) t₀ la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q)
      (deliverH ae G maxSkip (hp k t₀ la) DU none q) := by
  unfold deliverH
  refine RC.bind (rc_getH hI) fun st => ?_
  split
  · exact RC.pure hI _
  · split
    · exact RC.pure hI _
    · refine RC.bind (rc_receiveH_L2_gen ae G maxSkip k t₀ la hI hK _ _ _) fun r => ?_
      split
      · exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _
      · exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _

theorem rc_injectH_L2_gen (q : AD × (ℕ × C)) :
    RC (seedFill (k + 1))
      (injectH ae G maxSkip (hp (k + 1) t₀ la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) q)
      (injectH ae G maxSkip (hp k t₀ la) DU none q) := by
  unfold injectH
  refine RC.bind (rc_getH hI) fun st => ?_
  split
  · exact RC.pure hI _
  · refine RC.bind (rc_receiveH_L2_gen ae G maxSkip k t₀ la hI hK _ _ _) fun r => ?_
    split
    · exact RC.pure hI _
    · exact RC.bind (rc_modifyH hI hK _ fun _ => rfl) fun _ => RC.pure hI _

theorem rc_impl_L2_gen (t : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
    AD M (ℕ × C)).Domain) :
    RC (seedFill (k + 1))
      (implWith ideal ae G maxSkip (hp (k + 1) t₀ la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) t)
      (implWith ideal ae G maxSkip (hp k t₀ la) DU none t) := by
  rcases t with n | ((((((q | q) | u) | u) | q) | q))
  · exact rc_sampleH hI _
  · exact rc_transmitH_L2_gen ideal ae G k t₀ la hI hK q
  · exact rc_challengeH_L2_gen ideal ae G k t₀ la hI hK q
  · exact rc_corruptSenderH_L2_gen G k t₀ la hI hK u
  · exact rc_corruptReceiverH_L2_gen G k t₀ la hI hK u
  · exact rc_deliverH_L2_gen ae G maxSkip k t₀ la hI hK q
  · exact rc_injectH_L2_gen ae G maxSkip k t₀ la hI hK q

end L2Gen

theorem hOut_L2_gen (A : RatchetAdversary CK MK AD M C) (k t₀ : ℕ) (la : Bool) (b : Bool) :
    DEq (hOut la <$> (simulateQ (implWith ideal ae G maxSkip (hp k t₀ la) DU
        (none : Option (SpecialOps AD M C ProbComp))) A).run (hInit b .unknown))
      (hOut la <$> (simulateQ (implWith ideal ae G maxSkip (hp (k + 1) t₀ la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp))) A).run (hInit b .unknown)) := by
  have hI := seedFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1)
  have hK : ∀ h h' : HState CK MK AD M C, h.keys.length = h'.keys.length →
      seedFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (k + 1) h =
        seedFill (k + 1) h' := by
    intro h h' hl; funext sl; cases sl <;> simp [seedFill, hl]
  have hr := Rel.simulateQ hI (fun t => (rc_impl_L2_gen ideal ae G maxSkip k t₀ la hI hK t).1)
    (fun t => (rc_impl_L2_gen ideal ae G maxSkip k t₀ la hI hK t).2) A (hInit b .unknown)
  have h0 : fillSt (seedFill (k + 1)) (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
      b .unknown) = pure (hInit b .unknown) := by
    simp [fillSt, seedFill, hInit]
  rw [h0, pure_bind, pure_bind] at hr
  rw [hOut_eq]
  exact (DEq.map hr _).trans (map_fillOut (fill := seedFill (k + 1))
    (fun (a : Bool) (h : HState CK MK AD M C) => if la then h.lf else (h.b == a || h.win)) _)

/-- Observational agreement of two `SP` computations from states with `s.2 ≠ .unknown`, preserving `s.2 ≠ .unknown`. -/
def EqKnown {α : Type} (m₁ m₂ : SP α) : Prop :=
  ∀ {β : Type} (s : St) (g₁ g₂ : α × St → ProbComp β),
    s.2 ≠ .unknown →
    (∀ z : α × St, z.2.2 ≠ .unknown → g₁ z = g₂ z) →
    (m₁.run s >>= g₁) = (m₂.run s >>= g₂)

theorem EqKnown.pure {α : Type} (a : α) : EqKnown (pure a : SP α) (pure a) := by
  intro β s g₁ g₂ hs hg
  simp only [StateT.run_pure, pure_bind]
  exact hg (a, s) hs

theorem EqKnown.bind {α γ : Type} {m₁ m₂ : SP α} {k₁ k₂ : α → SP γ}
    (hm : EqKnown m₁ m₂) (hk : ∀ a, EqKnown (k₁ a) (k₂ a)) :
    EqKnown (m₁ >>= k₁) (m₂ >>= k₂) := by
  intro β s g₁ g₂ hs hg
  simp only [StateT.run_bind, bind_assoc]
  exact hm s _ _ hs fun ⟨a, s'⟩ hs' => hk a s' g₁ g₂ hs' hg

theorem eqKnown_getH : EqKnown (getH : SP (HState CK MK AD M C)) getH := by
  intro β s g₁ g₂ hs hg
  simp only [getH_run, pure_bind]
  exact hg (s.1, s) hs

theorem eqKnown_modifyH (f : HState CK MK AD M C → HState CK MK AD M C) :
    EqKnown (modifyH f : SP Unit) (modifyH f) := by
  intro β s g₁ g₂ hs hg
  simp only [modifyH_run, pure_bind]
  exact hg ((), (f s.1, s.2)) hs

theorem eqKnown_sampleH {α : Type} (p : ProbComp α) :
    EqKnown (sampleH p : SP α) (sampleH p) := by
  intro β s g₁ g₂ hs hg
  simp only [sampleH_run, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  exact bind_congr fun a => hg (a, s) hs

theorem eqKnown_reveal : EqKnown (reveal : SP CK) reveal := by
  intro β ⟨h, sl⟩ g₁ g₂ hs hg
  cases sl with
  | seed w =>
    simp only [reveal_run_seed, pure_bind]
    exact hg _ (by simp)
  | mat pos mt =>
    simp only [reveal_run_mat, bind_assoc, pure_bind]
    exact bind_congr fun u => hg _ (by simp)
  | unknown => exact absurd rfl hs

theorem eqKnown_genStep (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK)) :
    EqKnown (genStep G P D₁ : SP Unit) (genStep G P D₂) := by
  intro β ⟨h, sl⟩ g₁ g₂ hs hg
  cases sl with
  | seed w =>
    simp only [genStep_run_seed, pure_bind]
    exact hg _ (by simp)
  | mat pos mt =>
    by_cases hlt : h.keys.length < pos
    · simp only [genStep_run_mat_lt _ _ _ _ _ _ hlt, bind_assoc, pure_bind]
      exact bind_congr fun K => hg _ (by simp)
    · simp only [genStep_run_mat_ge _ _ _ _ _ _ hlt, pure_bind]
      exact hg _ (by simp)
  | unknown => exact absurd rfl hs

theorem eqKnown_genN (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK)) (n : ℕ) :
    EqKnown (genN G P D₁ n : SP Unit) (genN G P D₂ n) := by
  induction n with
  | zero => exact EqKnown.pure ()
  | succ n ih => exact EqKnown.bind (eqKnown_genStep G P D₁ D₂) fun _ => ih

theorem eqKnown_genUpTo (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK)) (i : ℕ) :
    EqKnown (genUpTo G P D₁ i : SP Unit) (genUpTo G P D₂ i) :=
  EqKnown.bind eqKnown_getH fun _ => eqKnown_genN G P D₁ D₂ _

theorem eqKnown_encIdx (P : Params) (i : ℕ) (a : AD) (msg : M) :
    EqKnown (encIdxWith ideal ae P (none : Option (SpecialOps AD M C ProbComp)) i a msg : SP C)
      (encIdxWith ideal ae P none i a msg) := by
  unfold encIdxWith
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · exact eqKnown_sampleH _
  · exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
  · split
    · exact EqKnown.pure _
    · exact eqKnown_sampleH _

theorem eqKnown_decIdx (P : Params) (hint : Option M) (i : ℕ) (a : AD) (e : C) :
    EqKnown (decIdx ae P (none : Option (SpecialOps AD M C ProbComp)) hint i a e : SP (Option M))
      (decIdx ae P none hint i a e) := by
  unfold decIdx
  split
  · exact EqKnown.pure _
  · refine EqKnown.bind eqKnown_getH fun st => ?_
    split
    · exact EqKnown.pure _
    · exact absurd ‹(none : Option (SpecialOps AD M C ProbComp)) = some _› (by simp)
    · exact EqKnown.pure _

theorem eqKnown_receiveH (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK))
    (hint : Option M) (a : AD) (c : ℕ × C) :
    EqKnown (receiveH ae G maxSkip P D₁ (none : Option (SpecialOps AD M C ProbComp)) hint a c)
      (receiveH ae G maxSkip P D₂ none hint a c) := by
  obtain ⟨i, e⟩ := c
  unfold receiveH
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · refine EqKnown.bind (eqKnown_decIdx ae P _ _ _ _) fun r => ?_
    split
    · exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _
    · exact EqKnown.pure _
  · split
    · exact EqKnown.pure _
    · split
      · exact EqKnown.pure _
      · refine EqKnown.bind (eqKnown_genUpTo G P D₁ D₂ _) fun _ => ?_
        refine EqKnown.bind (eqKnown_decIdx ae P _ _ _ _) fun r => ?_
        split
        · exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _
        · exact EqKnown.pure _

theorem eqKnown_senderKey : EqKnown (senderKey G : SP CK) (senderKey G) := by
  unfold senderKey
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · exact EqKnown.pure _
  · exact eqKnown_reveal

theorem eqKnown_transmitH (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK)) (q : AD × M) :
    EqKnown (transmitHWith ideal ae G P D₁ (none : Option (SpecialOps AD M C ProbComp)) q)
      (transmitHWith ideal ae G P D₂ none q) := by
  unfold transmitHWith
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · exact EqKnown.pure _
  · refine EqKnown.bind (eqKnown_genUpTo G P D₁ D₂ _) fun _ => ?_
    refine EqKnown.bind (eqKnown_encIdx ideal ae P _ _ _) fun e => ?_
    exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _

theorem eqKnown_challengeH (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK)) (q : AD × M × M) :
    EqKnown (challengeHWith ideal ae G P D₁ (none : Option (SpecialOps AD M C ProbComp)) q)
      (challengeHWith ideal ae G P D₂ none q) := by
  unfold challengeHWith
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · exact EqKnown.pure _
  · refine EqKnown.bind (eqKnown_genUpTo G P D₁ D₂ _) fun _ => ?_
    refine EqKnown.bind (eqKnown_encIdx ideal ae P _ _ _) fun e => ?_
    exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _

theorem eqKnown_corruptSenderH (P : Params) (u : Unit) :
    EqKnown (corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G P u)
      (corruptSenderH G P u) := by
  unfold corruptSenderH
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · exact EqKnown.pure _
  · split
    · exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _
    · refine EqKnown.bind (eqKnown_senderKey G) fun w => ?_
      exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _

theorem eqKnown_corruptReceiverH (P : Params) (u : Unit) :
    EqKnown (corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G P u)
      (corruptReceiverH G P u) := by
  unfold corruptReceiverH
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · exact EqKnown.pure _
  · split
    · exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _
    · refine EqKnown.bind (eqKnown_senderKey G) fun w => ?_
      refine EqKnown.bind eqKnown_getH fun st' => ?_
      exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _

theorem eqKnown_deliverH (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK)) (q : AD × (ℕ × C)) :
    EqKnown (deliverH ae G maxSkip P D₁ (none : Option (SpecialOps AD M C ProbComp)) q)
      (deliverH ae G maxSkip P D₂ none q) := by
  unfold deliverH
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · exact EqKnown.pure _
  · split
    · exact EqKnown.pure _
    · refine EqKnown.bind (eqKnown_receiveH ae G maxSkip P D₁ D₂ _ _ _) fun r => ?_
      split
      · exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _
      · exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _

theorem eqKnown_injectH (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK)) (q : AD × (ℕ × C)) :
    EqKnown (injectH ae G maxSkip P D₁ (none : Option (SpecialOps AD M C ProbComp)) q)
      (injectH ae G maxSkip P D₂ none q) := by
  unfold injectH
  refine EqKnown.bind eqKnown_getH fun st => ?_
  split
  · exact EqKnown.pure _
  · refine EqKnown.bind (eqKnown_receiveH ae G maxSkip P D₁ D₂ _ _ _) fun r => ?_
    split
    · exact EqKnown.pure _
    · exact EqKnown.bind (eqKnown_modifyH _) fun _ => EqKnown.pure _

theorem eqKnown_impl (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK))
    (t : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)).Domain) :
    EqKnown (implWith ideal ae G maxSkip P D₁ (none : Option (SpecialOps AD M C ProbComp)) t)
      (implWith ideal ae G maxSkip P D₂ none t) := by
  rcases t with n | ((((((q | q) | u) | u) | q) | q))
  · exact eqKnown_sampleH _
  · exact eqKnown_transmitH ideal ae G P D₁ D₂ q
  · exact eqKnown_challengeH ideal ae G P D₁ D₂ q
  · exact eqKnown_corruptSenderH G P u
  · exact eqKnown_corruptReceiverH G P u
  · exact eqKnown_deliverH ae G maxSkip P D₁ D₂ q
  · exact eqKnown_injectH ae G maxSkip P D₁ D₂ q

theorem eqKnown_simulateQ (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK)) {α : Type}
    (oa : AdversaryComp (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C) α) :
    EqKnown (simulateQ (implWith ideal ae G maxSkip P D₁
        (none : Option (SpecialOps AD M C ProbComp))) oa)
      (simulateQ (implWith ideal ae G maxSkip P D₂ none) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [simulateQ_pure]
    exact EqKnown.pure a
  | query_bind t cont ih =>
    simp only [simulateQ_query_bind]
    exact EqKnown.bind (eqKnown_impl ideal ae G maxSkip P D₁ D₂ t) ih

theorem hRunWith_mat_eq (P : Params) (D₁ D₂ : ℕ → ProbComp (CK × MK))
    (A : RatchetAdversary CK MK AD M C) (pos : ℕ) (mt : CK × MK) :
    hRunWith ideal ae G maxSkip P D₁ (none : Option (SpecialOps AD M C ProbComp)) A (.mat pos mt) =
      hRunWith ideal ae G maxSkip P D₂ (none : Option (SpecialOps AD M C ProbComp)) A (.mat pos mt) := by
  unfold hRunWith
  refine bind_congr fun b => ?_
  exact eqKnown_simulateQ ideal ae G maxSkip P D₁ D₂ A (hInit b (.mat pos mt)) _ _
    (by simp [hInit]) (fun _ _ => rfl)

theorem hybZero_eq_prgReal (A : RatchetAdversary CK MK AD M C) (j : ℕ) :
    𝒟[hRunWith ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) A .unknown] =
      𝒟[(G (j / 2)).prgRealExperiment (cumulativeChainPrgReduction ideal ae G maxSkip j A)] := by
  refine DEq.evalDist_eq ?_
  unfold PRGScheme.prgRealExperiment cumulativeChainPrgReduction
  simp only [hRun_eq]
  refine DEq.symm ((DEq.swap _ _ _).trans (DEq.bind_right _ fun b => ?_))
  set P := hp (j / 2) 0 (isLookaheadHop j)
  have hI := matFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (j / 2) (DG G)
  have h := hOut_fill ideal ae G maxSkip A P (DG G) hI (matFill_keys _ _)
    (comm_genStep_mat G P (DG G)) (comm_reveal_mat (j / 2) (DG G)) (hInit b .unknown)
  refine DEq.trans ?_ h
  simp only [fillSt, matFill, hInit, DG, List.length_nil, Nat.max_zero, map_eq_bind_pure_comp,
    bind_assoc, Function.comp_apply, pure_bind]
  exact DEq.refl _

theorem prgIdeal_eq_hybZero_succ (A : RatchetAdversary CK MK AD M C) (j : ℕ) :
    𝒟[PRGScheme.prgIdealExperiment (cumulativeChainPrgReduction ideal ae G maxSkip j A)] =
      𝒟[hRunWith ideal ae G maxSkip (hp (j / 2 + 1) 0 (isLookaheadHop j)) (DG G)
          (none : Option (SpecialOps AD M C ProbComp)) A .unknown] := by
  refine DEq.evalDist_eq ?_
  unfold PRGScheme.prgIdealExperiment cumulativeChainPrgReduction
  have heq : ∀ mt,
      hRunWith ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G)
          (none : Option (SpecialOps AD M C ProbComp)) A (.mat (j / 2) mt) =
        hRunWith ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) DU
          (none : Option (SpecialOps AD M C ProbComp)) A (.mat (j / 2) mt) :=
    hRunWith_mat_eq ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G) DU A (j / 2)
  simp only [heq, hRun_eq]
  refine (DEq.swap _ _ _).trans (DEq.bind_right _ fun b => ?_)
  set k := j / 2
  set la := isLookaheadHop j
  set P := hp k 0 la
  have hI := matFill_idem (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) k DU
  have hfill := hOut_fill ideal ae G maxSkip A P DU hI (matFill_keys _ _)
    (comm_genStep_mat G P DU) (comm_reveal_mat k DU) (hInit b .unknown)
  have hprod : ($ᵗ (CK × MK) : ProbComp (CK × MK)) =
      (do let w ← $ᵗ CK; let K ← $ᵗ MK; pure (w, K)) := by
    simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_apply]
    rfl
  have hfill' : DEq
      (($ᵗ (CK × MK)) >>= fun x =>
        hOut P.la <$> (simulateQ (implWith ideal ae G maxSkip P DU none) A).run (hInit b (.mat k x)))
      (hOut P.la <$> (simulateQ (implWith ideal ae G maxSkip P DU none) A).run (hInit b .unknown)) := by
    refine DEq.trans ?_ hfill
    rw [hprod]
    simp only [fillSt, matFill, hInit, DU, List.length_nil, Nat.max_zero, map_eq_bind_pure_comp,
      bind_assoc, Function.comp_apply, pure_bind]
    exact DEq.refl _
  exact hfill'.trans (hOut_L2_gen ideal ae G maxSkip A k 0 la b)

/-- Single chain-PRG hop distance bound at `t = 0`. -/
theorem hop_prg_zero_le (A : RatchetAdversary CK MK AD M C) (j : ℕ) :
    𝒟[hRunWith ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) A .unknown].boolDist
      𝒟[hRunWith ideal ae G maxSkip (hp (j / 2 + 1) 0 (isLookaheadHop j)) (DG G)
          (none : Option (SpecialOps AD M C ProbComp)) A .unknown] ≤
      (G (j / 2)).prgAdvantage (cumulativeChainPrgReduction ideal ae G maxSkip j A) := by
  rw [hybZero_eq_prgReal ideal ae G maxSkip A j,
    ← prgIdeal_eq_hybZero_succ ideal ae G maxSkip A j,
    PRGScheme.prgAdvantage]

/-- Cumulative distance bound across `N` chain-PRG hops at `t = 0`. -/
theorem chain_prg_zero_le (A : RatchetAdversary CK MK AD M C) (la : Bool) (N : ℕ) :
    𝒟[hybridA ideal ae G maxSkip 0 la A].boolDist
      𝒟[hRunWith ideal ae G maxSkip (hp N 0 la) (DG G)
          (none : Option (SpecialOps AD M C ProbComp)) A .unknown] ≤
      ∑ k ∈ Finset.range N,
        (G ((2 * k + la.toNat) / 2)).prgAdvantage
          (cumulativeChainPrgReduction ideal ae G maxSkip (2 * k + la.toNat) A) := by
  unfold hybridA
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[hRunWith ideal ae G maxSkip (hp k 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) A .unknown]) N).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : (2 * k + la.toNat) / 2 = k := by
    cases la <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have h2 : isLookaheadHop (2 * k + la.toNat) = la := by
    cases la <;> simp [isLookaheadHop, Nat.add_mod]
  have := hop_prg_zero_le ideal ae G maxSkip A (2 * k + la.toNat)
  rw [h1, h2] at this
  rw [h1]
  exact this

end Stage1PRG

/-! ## Multi-slot OT-CCA reduction -/

section MultiSlotOTCCA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable (ideal : (ℕ × AD) → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK))
  (maxSkip : ℕ)

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C
local notation "SP" => StateT (HSt CK MK AD M C) ProbComp
local notation "SO" => StateT (HSt CK MK AD M C) (OracleComp (IndexedOtccaSpec AD M C))

def slotLiftOtcca {S : Type}
    (impl : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp)) :
    QueryImpl (AEADScheme.otccaSpec (ℕ × AD) M C) (StateT (ℕ → S) ProbComp)
  | .inl (h, msg) => StateT.mk fun σ => do
      let (r, s') ← (impl (.inr (.inl (h, msg)))).run (σ h.1)
      pure (r, Function.update σ h.1 s')
  | .inr (h, e) => StateT.mk fun σ => do
      let (r, s') ← (impl (.inr (.inr (h, e)))).run (σ h.1)
      pure (r, Function.update σ h.1 s')

/-- Lifts a single-slot `IndexedOtccaSpec` implementation to `ℕ → S` by dispatching on the header index. -/
def slotLift {S : Type}
    (impl : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp)) :
    QueryImpl (IndexedOtccaSpec AD M C) (StateT (ℕ → S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (ℕ → S) ProbComp)
    + slotLiftOtcca impl

@[simp] theorem length_mem_support_sampleKeys {n : ℕ} {ks : List MK}
    (h : ks ∈ support (sampleKeys (MK := MK) n)) : ks.length = n := by
  induction n generalizing ks with
  | zero =>
    simp only [sampleKeys, support_pure, Set.mem_singleton_iff] at h
    subst h; rfl
  | succ n ih =>
    simp only [sampleKeys, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨K, -, ks', hks', rfl⟩ := h
    simp [ih hks']

@[simp] theorem initOStM_b (b : Bool) (K₀ : MK) (ks : List MK) (i : ℕ) :
    (initOStM (AD := AD) (C := C) b K₀ ks i).b = b := rfl

@[simp] theorem initOStM_chal (b : Bool) (K₀ : MK) (ks : List MK) (i : ℕ) :
    (initOStM (AD := AD) (C := C) b K₀ ks i).chal = none := rfl

theorem update_initOStM (b : Bool) (K₀ : MK) (ks : List MK) (k : ℕ) (key : MK)
    (hk : k < ks.length) :
    Function.update (initOStM (AD := AD) (C := C) b K₀ ks) (k + 1) ⟨key, b, none⟩ =
      initOStM b K₀ (ks.set k key) := by
  ext i : 1
  by_cases hi : i = k + 1
  · subst hi; simp [initOStM, hk]
  · rw [Function.update_of_ne hi]
    by_cases h0 : i = 0
    · subst h0; simp [initOStM]
    · have hne : k ≠ i - 1 := by omega
      simp [initOStM, h0, List.getElem?_set_ne hne]

theorem sampleKeys_set_deq {α : Type} {n k : ℕ} (hk : k < n) (f : List MK → ProbComp α) :
    DEq ($ᵗ MK >>= fun key => sampleKeys n >>= fun ks => f (ks.set k key))
      (sampleKeys n >>= f) := by
  induction n generalizing k f with
  | zero => omega
  | succ n ih =>
    simp only [sampleKeys, bind_assoc, pure_bind]
    cases k with
    | zero =>
      simp only [List.set_cons_zero]
      exact DEq.bind_right ($ᵗ MK) fun key => DEq.bind_const ($ᵗ MK) _
    | succ k =>
      have hk' : k < n := by omega
      simp only [List.set_cons_succ]
      refine (DEq.swap ($ᵗ MK) ($ᵗ MK) _).trans ?_
      exact DEq.bind_right ($ᵗ MK) fun K => ih hk' fun ks => f (K :: ks)

/-- Multi-slot OT-CCA experiment with hidden bit `b` and `N` pre-sampled slot keys. -/
def multiOtBranch (b : Bool) (N : ℕ) (B : AEADScheme.OTCCAAdversary (ℕ × AD) M C) :
    ProbComp Bool := do
  let K₀ ← $ᵗ MK
  let ks ← sampleKeys N
  Prod.fst <$> (simulateQ (slotLift (otImpl ideal ae)) B).run (initOStM b K₀ ks)

/-- Joint state pairing the hybrid state with per-slot OT-CCA states. -/
abbrev JStM (CK MK AD M C : Type) := HSt CK MK AD M C × (ℕ → IndexedOtccaState MK AD C)

def YM {α : Type} (y : SO α) (σ : JStM CK MK AD M C) : ProbComp (α × JStM CK MK AD M C) :=
  (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (slotLift (otImpl ideal ae)) (y.run σ.1)).run σ.2

@[simp] theorem YM_pure {α : Type} (a : α) (σ : JStM CK MK AD M C) :
    YM ideal ae (pure a : SO α) σ = pure (a, σ) := by
  simp [YM]

theorem YM_bind {α β : Type} (y : SO α) (h : α → SO β) (σ : JStM CK MK AD M C) :
    YM ideal ae (y >>= h) σ = YM ideal ae y σ >>= fun r => YM ideal ae (h r.1) r.2 := by
  simp [YM, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

@[simp] theorem YM_getH (σ : JStM CK MK AD M C) :
    YM ideal ae (getH : SO HS) σ = pure (σ.1.1, σ) := by
  simp [YM, getH, onH]

@[simp] theorem YM_modifyH (g : HS → HS) (σ : JStM CK MK AD M C) :
    YM ideal ae (modifyH g : SO Unit) σ = pure ((), ((g σ.1.1, σ.1.2), σ.2)) := by
  simp [YM, modifyH, onH]

@[simp] theorem YM_sampleH {α : Type} (p : ProbComp α) (σ : JStM CK MK AD M C) :
    YM ideal ae (sampleH p : SO α) σ = (fun a => (a, σ)) <$> p := by
  simp [YM, sampleH, slotLift, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

theorem YM_lift {α : Type} (o : OracleComp (IndexedOtccaSpec AD M C) α) (σ : JStM CK MK AD M C) :
    YM ideal ae (liftM o : SO α) σ =
      (fun r => (r.1, (σ.1, r.2))) <$> (simulateQ (slotLift (otImpl ideal ae)) o).run σ.2 := by
  simp [YM]

/-- Relational judgment coupling a left computation on `S` with a right computation in `SO` via projection `f`. -/
def JM {S : Type} (f : JStM CK MK AD M C → S) {α : Type}
    (P : JStM CK MK AD M C → Prop) (x : StateT S ProbComp α) (y : SO α)
    (Q : α → JStM CK MK AD M C → Prop) : Prop :=
  ∀ σ, P σ → DEq (x.run (f σ)) ((fun r => (r.1, f r.2)) <$> YM ideal ae y σ) ∧
    ∀ r ∈ support (YM ideal ae y σ), Q r.1 r.2

section JMCombinators

variable {ideal ae} {S : Type} {f : JStM CK MK AD M C → S}

theorem JM.bind {α β : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} {R : β → JStM CK MK AD M C → Prop}
    {x : StateT S ProbComp α} {y : SO α} {g : α → StateT S ProbComp β} {h : α → SO β}
    (hxy : JM ideal ae f P x y Q) (hgh : ∀ a, JM ideal ae f (Q a) (g a) (h a) R) :
    JM ideal ae f P (x >>= g) (y >>= h) R := by
  intro σ hP
  obtain ⟨h1, h2⟩ := hxy σ hP
  rw [YM_bind]
  constructor
  · rw [StateT.run_bind]
    refine (DEq.bind_left h1 _).trans ?_
    rw [bind_map_left, map_bind]
    exact DEq.bind_right_supp _ fun r hr => (hgh r.1 r.2 (h2 r hr)).1
  · intro r hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨r', hr', hr⟩ := hr
    exact (hgh r'.1 r'.2 (h2 r' hr')).2 r hr

theorem JM.pure {α : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} (a : α) (h : ∀ σ, P σ → Q a σ) :
    JM ideal ae f P (pure a : StateT S ProbComp α) (pure a : SO α) Q := by
  intro σ hP
  simp only [YM_pure, StateT.run_pure, map_pure]
  exact ⟨DEq.refl _, by simpa using h σ hP⟩

theorem JM.mono {α : Type} {P P' : JStM CK MK AD M C → Prop}
    {Q Q' : α → JStM CK MK AD M C → Prop} {x : StateT S ProbComp α} {y : SO α}
    (hj : JM ideal ae f P x y Q) (hP : ∀ σ, P' σ → P σ)
    (hQ : ∀ a σ, Q a σ → Q' a σ) : JM ideal ae f P' x y Q' := fun σ h =>
  ⟨(hj σ (hP σ h)).1, fun r hr => hQ _ _ ((hj σ (hP σ h)).2 r hr)⟩

theorem JM.ofExact {α : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} {x : StateT S ProbComp α} {y : SO α}
    (h : ∀ σ, P σ → JM ideal ae f (· = σ) x y Q) : JM ideal ae f P x y Q :=
  fun σ hP => h σ hP σ rfl

theorem JM.ite {α : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} (c : Prop) {d₁ d₂ : Decidable c}
    {a₁ b₁ : StateT S ProbComp α} {a₂ b₂ : SO α}
    (h₁ : c → JM ideal ae f P a₁ a₂ Q) (h₂ : ¬c → JM ideal ae f P b₁ b₂ Q) :
    JM ideal ae f P (@ite _ c d₁ a₁ b₁) (@ite _ c d₂ a₂ b₂) Q := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h₁ hc
  · simp only [hc, ite_false]; exact h₂ hc

theorem JM.simulateQ {ι : Type} {spec : OracleSpec ι} {I : JStM CK MK AD M C → Prop}
    {implL : QueryImpl spec (StateT S ProbComp)} {implR : QueryImpl spec SO}
    (himpl : ∀ t, JM ideal ae f I (implL t) (implR t) fun _ => I)
    {α : Type} (oa : OracleComp spec α) :
    JM ideal ae f I (simulateQ implL oa) (simulateQ implR oa) fun _ => I := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simpa only [simulateQ_pure] using
      JM.pure (ideal := ideal) (ae := ae) (f := f) (P := I) (Q := fun _ => I) a fun _ h => h
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map]
    exact JM.bind (himpl t) ih

end JMCombinators

section JMOnHSt

variable {ideal ae} {f : JStM CK MK AD M C → HSt CK MK AD M C}

theorem JM.read {α : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} {g : HS → SP α} {h : HS → SO α}
    (hgh : ∀ σ, P σ → JM ideal ae f (fun σ' => σ' = σ) (g (f σ).1) (h σ.1.1) Q) :
    JM ideal ae f P (getH >>= g) (getH >>= h) Q := by
  intro σ hP
  have := hgh σ hP σ rfl
  rw [YM_bind, YM_getH, pure_bind, StateT.run_bind, getH_run, pure_bind]
  exact this

theorem JM.readEq {α : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} {g : HS → SP α} {h : HS → SO α}
    (hf : ∀ σ, P σ → (f σ).1 = σ.1.1)
    (hgh : ∀ st, JM ideal ae f P (g st) (h st) Q) :
    JM ideal ae f P (getH >>= g) (getH >>= h) Q :=
  JM.read fun σ hP => by
    rw [hf σ hP]
    exact (hgh σ.1.1).mono (fun σ' h' => h' ▸ hP) fun _ _ h => h

theorem JM.modify {P : JStM CK MK AD M C → Prop} {Q : Unit → JStM CK MK AD M C → Prop}
    (gL gR : HS → HS)
    (hf : ∀ σ, P σ → f ((gR σ.1.1, σ.1.2), σ.2) = (gL (f σ).1, (f σ).2))
    (hQ : ∀ σ, P σ → Q () ((gR σ.1.1, σ.1.2), σ.2)) :
    JM ideal ae f P (modifyH gL : SP Unit) (modifyH gR : SO Unit) Q := by
  intro σ hP
  simp only [YM_modifyH, modifyH_run, map_pure, hf σ hP]
  exact ⟨DEq.refl _, by simpa using hQ σ hP⟩

theorem JM.sample {α : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} (p : ProbComp α) (hQ : ∀ σ a, P σ → Q a σ) :
    JM ideal ae f P (sampleH p : SP α) (sampleH p : SO α) Q := by
  intro σ hP
  simp only [YM_sampleH, sampleH_run, Functor.map_map]
  refine ⟨DEq.refl _, fun r hr => ?_⟩
  rw [support_map] at hr
  obtain ⟨a, -, rfl⟩ := hr
  exact hQ σ a hP

end JMOnHSt

/-! ### Multi-slot ideal world (`b = true`) -/

def IdIM (σ : JStM CK MK AD M C) : Prop := ∀ i, (σ.2 i).b = true

theorem jm_enc_ideal (h : ℕ × AD) (msg : M) :
    JM ideal ae Prod.fst IdIM
      (sampleH (ideal h) : SP C)
      (liftM ((otOpsWith ideal).enc h msg) : SO C) fun _ => IdIM := by
  rintro ⟨s, σ⟩ hb
  have hbi : (σ h.1).b = true := hb h.1
  rw [YM_lift]
  rcases hslot : σ h.1 with ⟨key, b, chal⟩
  rw [hslot] at hbi
  dsimp only at hbi
  subst hbi
  cases chal <;>
    simp [otOpsWith, slotLift, slotLiftOtcca, otImpl, hslot, AEADScheme.otccaEncryptAdIdeal,
      QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]
  · refine ⟨DEq.refl _, fun a ha j => ?_⟩
    by_cases hj : j = h.1
    · subst hj; simp
    · simp [Function.update_of_ne hj]; exact hb j
  · refine ⟨DEq.refl _, fun a ha j => ?_⟩
    by_cases hj : j = h.1
    · subst hj; simp
    · simp [Function.update_of_ne hj]; exact hb j

theorem jm_dec_ideal (h : ℕ × AD) (e : C) :
    JM ideal ae Prod.fst IdIM
      (pure none : SP (Option M))
      (liftM ((otOpsWith ideal).dec h e) : SO (Option M)) fun _ => IdIM := by
  rintro ⟨s, σ⟩ hb
  have hbi : (σ h.1).b = true := hb h.1
  simp [YM_lift, otOpsWith, slotLift, slotLiftOtcca, otImpl, AEADScheme.otccaDecrypt, hbi]
  refine ⟨DEq.refl _, fun j => ?_⟩
  by_cases hj : j = h.1
  · subst hj; simp [hbi]
  · simp [Function.update_of_ne hj]; exact hb j

theorem jm_modify_ideal (g : HS → HS) :
    JM ideal ae Prod.fst IdIM (modifyH g : SP Unit) (modifyH g : SO Unit) fun _ => IdIM :=
  JM.modify _ _ (fun _ _ => rfl) fun _ h => h

theorem jm_genStep_ideal (PL PR : Params) (hj : PL.j = PR.j) (D : ℕ → ProbComp (CK × MK)) :
    JM ideal ae Prod.fst IdIM (genStep G PL D : SP Unit) (genStep G PR D : SO Unit) fun _ => IdIM := by
  rintro ⟨⟨h, sl⟩, σ⟩ hb
  cases sl with
  | seed w =>
    simp [YM, genStep]
    exact ⟨DEq.refl _, hb⟩
  | mat pos mt =>
    by_cases hlt : h.keys.length < pos <;>
    simp [YM, genStep, hlt, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget,
      slotLift] <;>
    exact ⟨DEq.refl _, by intros; subst_vars; exact hb⟩
  | unknown =>
    by_cases hlt : h.keys.length < PR.j <;>
    simp [YM, genStep, hlt, hj, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget,
      slotLift] <;>
    exact ⟨DEq.refl _, by intros; subst_vars; exact hb⟩

theorem jm_reveal_ideal :
    JM ideal ae Prod.fst IdIM (reveal : SP CK) (reveal : SO CK) fun _ => IdIM := by
  rintro ⟨⟨h, sl⟩, σ⟩ hb
  cases sl <;>
    simp [YM, reveal, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget,
      slotLift] <;>
    exact ⟨DEq.refl _, by intros; subst_vars; exact hb⟩

theorem jm_genN_ideal (PL PR : Params) (hj : PL.j = PR.j) (D : ℕ → ProbComp (CK × MK)) (n : ℕ) :
    JM ideal ae Prod.fst IdIM (genN G PL D n : SP Unit) (genN G PR D n : SO Unit) fun _ => IdIM := by
  induction n with
  | zero => exact JM.pure _ fun _ h => h
  | succ n ih => exact JM.bind (jm_genStep_ideal ideal ae G PL PR hj D) fun _ => ih

theorem jm_genUpTo_ideal (PL PR : Params) (hj : PL.j = PR.j) (D : ℕ → ProbComp (CK × MK)) (i : ℕ) :
    JM ideal ae Prod.fst IdIM (genUpTo G PL D i : SP Unit) (genUpTo G PR D i : SO Unit) fun _ => IdIM :=
  JM.readEq (fun _ _ => rfl) fun _ => jm_genN_ideal ideal ae G PL PR hj D _

theorem jm_encIdx_ideal (N : ℕ) (la : Bool) (i : ℕ) (a : AD) (msg : M) :
    JM ideal ae Prod.fst IdIM
      (encIdxWith ideal ae (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) i a msg : SP C)
      (multiEncIdxWith ideal ae 0 N (some (otOpsWith ideal)) i a msg : SO C) fun _ => IdIM := by
  unfold encIdxWith multiEncIdxWith
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  by_cases hc : st.isCompromised i = true
  · have h1 : kind (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) st i = .real := by
      simp [kind, hc]
    have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) st i = .real := by
      simp [multiKind, hc]
    rw [h1, h2]
    dsimp only
    cases st.keys[i - 1]? with
    | some K => exact JM.pure _ fun _ h => h
    | none => exact JM.sample _ fun _ _ h => h
  · simp only [Bool.not_eq_true] at hc
    by_cases hiN : i ≤ N
    · have h1 : kind (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) st i = .ideal := by
        simp [kind, hp, hc, hiN]
      rw [h1]
      dsimp only
      by_cases hi0 : i ≤ 0
      · have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) st i = .ideal := by
          simp [multiKind, hc, hi0]
        rw [h2]
        exact JM.sample _ fun _ _ h => h
      · have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) st i = .special := by
          simp [multiKind, hc, hi0, hiN]
        rw [h2]
        exact jm_enc_ideal ideal ae (i, a) msg
    · have h1 : kind (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) st i = .real := by
        simp [kind, hp, hc, hiN]
      have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) st i = .real := by
        have hi0 : ¬ i ≤ 0 := by omega
        simp [multiKind, hc, hi0, hiN]
      rw [h1, h2]
      dsimp only
      cases st.keys[i - 1]? with
      | some K => exact JM.pure _ fun _ h => h
      | none => exact JM.sample _ fun _ _ h => h

theorem jm_decIdx_ideal (N : ℕ) (la : Bool) (hint : Option M) (i : ℕ) (a : AD) (e : C) :
    JM ideal ae Prod.fst IdIM
      (decIdx ae (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) hint i a e : SP (Option M))
      (multiDecIdx ae 0 N (some (otOpsWith ideal)) hint i a e : SO (Option M)) fun _ => IdIM := by
  cases hint with
  | some msg => exact JM.pure _ fun _ h => h
  | none =>
    unfold decIdx multiDecIdx
    refine JM.readEq (fun _ _ => rfl) fun st => ?_
    by_cases hc : st.isCompromised i = true
    · have h1 : kind (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) st i = .real := by
        simp [kind, hc]
      have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) st i = .real := by
        simp [multiKind, hc]
      rw [h1, h2]
      exact JM.pure _ fun _ h => h
    · simp only [Bool.not_eq_true] at hc
      by_cases hiN : i ≤ N
      · have h1 : kind (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) st i = .ideal := by
          simp [kind, hp, hc, hiN]
        rw [h1]
        dsimp only
        by_cases hi0 : i ≤ 0
        · have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) st i = .ideal := by
            simp [multiKind, hc, hi0]
          rw [h2]
          exact JM.pure _ fun _ h => h
        · have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) st i = .special := by
            simp [multiKind, hc, hi0, hiN]
          rw [h2]
          exact jm_dec_ideal ideal ae (i, a) e
      · have h1 : kind (hp N N la) (none : Option (SpecialOps AD M C ProbComp)) st i = .real := by
          simp [kind, hp, hc, hiN]
        have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) st i = .real := by
          have hi0 : ¬ i ≤ 0 := by omega
          simp [multiKind, hc, hi0, hiN]
        rw [h1, h2]
        exact JM.pure _ fun _ h => h

theorem jm_receiveH_ideal (N : ℕ) (la : Bool) (hint : Option M) (a : AD) (c : ℕ × C) :
    JM ideal ae Prod.fst IdIM
      (receiveH ae G maxSkip (hp N N la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) hint a c)
      (multiReceiveH ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) hint a c)
      fun _ => IdIM := by
  unfold receiveH multiReceiveH
  simp only [hp]
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  refine JM.ite _ (fun _ => ?_) fun _ => ?_
  · refine JM.bind (jm_decIdx_ideal ideal ae N la hint c.1 a c.2) fun r => ?_
    cases r with
    | none => exact JM.pure _ fun _ h => h
    | some msg => exact JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h
  · refine JM.ite _ (fun _ => JM.pure _ fun _ h => h) fun _ => ?_
    refine JM.ite _ (fun _ => JM.pure _ fun _ h => h) fun _ => ?_
    refine JM.bind (jm_genUpTo_ideal ideal ae G ⟨N, some N, la⟩ ⟨N, some 0, la⟩ rfl (DG G) c.1) fun _ => ?_
    refine JM.bind (jm_decIdx_ideal ideal ae N la hint c.1 a c.2) fun r => ?_
    cases r with
    | none => exact JM.pure _ fun _ h => h
    | some msg => exact JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h

theorem jm_senderKey_ideal :
    JM ideal ae Prod.fst IdIM (senderKey G : SP CK) (senderKey G : SO CK) fun _ => IdIM := by
  unfold senderKey
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  split
  · exact JM.pure _ fun _ h => h
  · exact jm_reveal_ideal ideal ae

theorem jm_transmitH_ideal (N : ℕ) (la : Bool) (q : AD × M) :
    JM ideal ae Prod.fst IdIM
      (transmitHWith ideal ae G (hp N N la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q)
      (multiTransmitHWith ideal ae G (hp N 0 la) N (DG G) (some (otOpsWith ideal)) q)
      fun _ => IdIM := by
  unfold transmitHWith multiTransmitHWith
  simp only [hp]
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  refine JM.ite _ (fun _ => JM.pure _ fun _ h => h) fun _ => ?_
  refine JM.bind (jm_genUpTo_ideal ideal ae G ⟨N, some N, la⟩ ⟨N, some 0, la⟩ rfl (DG G) _) fun _ => ?_
  refine JM.bind (jm_encIdx_ideal ideal ae N la _ q.1 q.2) fun e => ?_
  exact JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h

theorem jm_challengeH_ideal (N : ℕ) (la : Bool) (q : AD × M × M) :
    JM ideal ae Prod.fst IdIM
      (challengeHWith ideal ae G (hp N N la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q)
      (multiChallengeHWith ideal ae G (hp N 0 la) N (DG G) (some (otOpsWith ideal)) q)
      fun _ => IdIM := by
  unfold challengeHWith multiChallengeHWith
  simp only [hp]
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  refine JM.ite _ (fun _ => JM.pure _ fun _ h => h) fun _ => ?_
  refine JM.bind (jm_genUpTo_ideal ideal ae G ⟨N, some N, la⟩ ⟨N, some 0, la⟩ rfl (DG G) _) fun _ => ?_
  refine JM.bind (jm_encIdx_ideal ideal ae N la _ q.1 _) fun e => ?_
  exact JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h

theorem jm_corruptSenderH_ideal (N : ℕ) (la : Bool) (u : Unit) :
    JM ideal ae Prod.fst IdIM
      (corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G (hp N N la) u)
      (corruptSenderH (m := OracleComp (IndexedOtccaSpec AD M C)) G (hp N 0 la) u) fun _ => IdIM := by
  unfold corruptSenderH
  simp only [hp]
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  refine JM.ite _ (fun _ => JM.pure _ fun _ h => h) fun _ => ?_
  refine JM.ite _ (fun _ => JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h)
    fun _ => ?_
  exact JM.bind (jm_senderKey_ideal ideal ae G) fun _ =>
    JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h

theorem jm_corruptReceiverH_ideal (N : ℕ) (la : Bool) (u : Unit) :
    JM ideal ae Prod.fst IdIM
      (corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G (hp N N la) u)
      (corruptReceiverH (m := OracleComp (IndexedOtccaSpec AD M C)) G (hp N 0 la) u) fun _ => IdIM := by
  unfold corruptReceiverH
  simp only [hp]
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  refine JM.ite _ (fun _ => JM.pure _ fun _ h => h) fun _ => ?_
  refine JM.ite _ (fun _ => JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h)
    fun _ => ?_
  refine JM.bind (jm_senderKey_ideal ideal ae G) fun _ => ?_
  refine JM.readEq (fun _ _ => rfl) fun _ => ?_
  exact JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h

theorem jm_deliverH_ideal (N : ℕ) (la : Bool) (q : AD × (ℕ × C)) :
    JM ideal ae Prod.fst IdIM
      (deliverH ae G maxSkip (hp N N la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q)
      (multiDeliverH ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) q)
      fun _ => IdIM := by
  unfold deliverH multiDeliverH
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  refine JM.ite _ (fun _ => JM.pure _ fun _ h => h) fun _ => ?_
  cases st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
  | none => exact JM.pure _ fun _ h => h
  | some r =>
    dsimp only
    refine JM.bind (jm_receiveH_ideal ideal ae G maxSkip N la (some r.msg) q.1 q.2) fun res => ?_
    cases res with
    | none => exact JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h
    | some p => exact JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h

theorem jm_injectH_ideal (N : ℕ) (la : Bool) (q : AD × (ℕ × C)) :
    JM ideal ae Prod.fst IdIM
      (injectH ae G maxSkip (hp N N la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q)
      (multiInjectH ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) q)
      fun _ => IdIM := by
  unfold injectH multiInjectH
  simp only [hp]
  refine JM.readEq (fun _ _ => rfl) fun st => ?_
  refine JM.ite _ (fun _ => JM.pure _ fun _ h => h) fun _ => ?_
  refine JM.bind (jm_receiveH_ideal ideal ae G maxSkip N la none q.1 q.2) fun res => ?_
  cases res with
  | none => exact JM.pure _ fun _ h => h
  | some p => exact JM.bind (jm_modify_ideal ideal ae _) fun _ => JM.pure _ fun _ h => h

theorem jm_impl_ideal (N : ℕ) (la : Bool)
    (t : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M
      (ℕ × C)).Domain) :
    JM ideal ae Prod.fst IdIM
      (implWith ideal ae G maxSkip (hp N N la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) t)
      (multiImplWith ideal ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t)
      fun _ => IdIM := by
  rcases t with n | ((((((q | q) | u) | u) | q) | q))
  · exact JM.sample _ fun _ _ h => h
  · exact jm_transmitH_ideal ideal ae G N la q
  · exact jm_challengeH_ideal ideal ae G N la q
  · exact jm_corruptSenderH_ideal ideal ae G N la u
  · exact jm_corruptReceiverH_ideal ideal ae G N la u
  · exact jm_deliverH_ideal ideal ae G maxSkip N la q
  · exact jm_injectH_ideal ideal ae G maxSkip N la q

/-- Running `multiSlotOtccaReduction` against the multi-slot OT-CCA ideal world (`b = true`) matches `hybridA ideal ae G maxSkip N la A`. -/
theorem multiOtBranch_true_eq_hybAWith (N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    𝒟[multiOtBranch ideal ae true N (multiSlotOtccaReduction ideal ae G maxSkip N la A)] =
      𝒟[hybridA ideal ae G maxSkip N la A] := by
  refine DEq.evalDist_eq ?_
  unfold multiOtBranch multiSlotOtccaReduction multiRunWith hybridA
  simp only [hp_la, hRun_eq, simulateQ_bind, simulateQ_pure, slotLift,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, StateT.run_bind,
    StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind]
  have hsim : ∀ (K₀ : MK) (ks : List MK) (b : Bool),
      DEq
        ((simulateQ (slotLift (otImpl ideal ae))
          ((simulateQ (multiImplWith ideal ae G maxSkip (hp N 0 la) N (DG G)
            (some (otOpsWith ideal))) A).run (hInit b .unknown))).run
            (initOStM true K₀ ks) >>= fun x => pure (hOut la x.1))
        ((simulateQ (implWith ideal ae G maxSkip (hp N N la) (DG G) none) A).run
          (hInit b .unknown) >>= fun z => pure (hOut la z)) := by
    intro K₀ ks b
    have hJ := (JM.simulateQ (jm_impl_ideal ideal ae G maxSkip N la) A
      (hInit b .unknown, initOStM true K₀ ks) (fun _ => rfl)).1
    have hmap := DEq.map hJ.symm (hOut la)
    simpa only [YM, Functor.map_map, map_eq_bind_pure_comp, Function.comp_def,
      Function.comp_apply, bind_assoc, pure_bind] using hmap
  refine (DEq.bind_right _ fun K₀ => DEq.bind_right _ fun ks =>
    DEq.bind_right _ fun b => hsim K₀ ks b).trans ?_
  exact (DEq.bind_const _ _).trans (DEq.bind_const _ _)

/-! ### Lazy-to-eager message-key sampling -/

/-- Hybrid state paired with an optional queue of pre-sampled message keys for positions `< N`. -/
abbrev HStK (CK MK AD M C : Type) := HSt CK MK AD M C × Option (List MK)

local notation "SPK" => StateT (HStK CK MK AD M C) ProbComp

def liftK {α : Type} (x : SP α) : SPK α :=
  StateT.mk fun s => (fun z => (z.1, (z.2, s.2))) <$> x.run s.1

/-- Eagerly samples the remaining `N - h.keys.length` message keys when the slot is `.unknown` and the queue is `none`. -/
def keysFill (N : ℕ) (hst : HSt CK MK AD M C) :
    Option (List MK) → ProbComp (Option (List MK))
  | none =>
    match hst.2 with
    | .unknown => some <$> sampleKeys (N - hst.1.keys.length)
    | _ => pure none
  | some ks =>
    match hst.2 with
    | .unknown => pure (some ks)
    | _ => pure none

theorem idem_keysFill (N : ℕ) : Idem (keysFill (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) N) := by
  rintro ⟨h, sl⟩ opt
  cases opt <;> cases sl <;>
    simp [keysFill, pure_bind, map_eq_bind_pure_comp, bind_assoc] <;>
    exact DEq.refl _

theorem keysFill_modify {N : ℕ} {g : HS → HS}
    (hg : ∀ h, (g h).keys = h.keys) (h : HS) (sl : Slot CK MK) (opt : Option (List MK)) :
    keysFill N (g h, sl) opt = keysFill N (h, sl) opt := by
  cases opt <;> cases sl <;> simp [keysFill, hg h]

theorem comm_getHK (N : ℕ) :
    Comm (keysFill N) (liftK (getH : SP HS)) := by
  rintro ⟨⟨h, sl⟩, opt⟩
  simp only [fillSt, fillOut, liftK, getH_run, StateT.run_mk,
    map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  simpa only [bind_assoc] using
    DEq.bind_left (idem_keysFill N (h, sl) opt) fun opt' => pure (h, (h, sl), opt')

theorem comm_sampleHK (N : ℕ) {α : Type} (p : ProbComp α) :
    Comm (keysFill N) (liftK (sampleH p : SP α)) := by
  rintro ⟨⟨h, sl⟩, opt⟩
  simp only [fillSt, fillOut, liftK, sampleH, StateT.run_monadLift, monadLift_self,
    StateT.run_mk, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  refine (DEq.swap (keysFill N (h, sl) opt) p
    (fun opt₁ a => keysFill N (h, sl) opt₁ >>= fun opt₂ => pure (a, (h, sl), opt₂))).trans ?_
  refine DEq.bind_right p fun a => ?_
  simpa only [bind_assoc] using
    DEq.bind_left (idem_keysFill N (h, sl) opt) fun opt₂ => pure (a, (h, sl), opt₂)

theorem comm_modifyHK (N : ℕ) (g : HS → HS) (hg : ∀ h, (g h).keys = h.keys) :
    Comm (keysFill N) (liftK (modifyH g : SP Unit)) := by
  rintro ⟨⟨h, sl⟩, opt⟩
  simp only [fillSt, fillOut, liftK, modifyH_run, StateT.run_mk, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind, keysFill_modify hg]
  simpa only [bind_assoc] using
    DEq.bind_left (idem_keysFill N (h, sl) opt) fun opt' => pure ((), (g h, sl), opt')

def genStepK (P : Params) (D : ℕ → ProbComp (CK × MK)) : SPK Unit :=
  StateT.mk fun ⟨⟨h, sl⟩, opt⟩ =>
    match sl with
    | .seed w =>
      pure ((), (({ h with keys := h.keys ++ [((G h.keys.length).gen w).2] },
        .seed ((G h.keys.length).gen w).1), none))
    | .mat pos mt =>
      if h.keys.length < pos then do
        let K ← ($ᵗ MK : ProbComp MK)
        pure ((), (({ h with keys := h.keys ++ [K] }, .mat pos mt), none))
      else
        pure ((), (({ h with keys := h.keys ++ [mt.2] }, .seed mt.1), none))
    | .unknown =>
      if h.keys.length < P.j then
        match opt with
        | some (K :: ks) => pure ((), (({ h with keys := h.keys ++ [K] }, .unknown), some ks))
        | some [] => do
          let K ← ($ᵗ MK : ProbComp MK)
          pure ((), (({ h with keys := h.keys ++ [K] }, .unknown), some []))
        | none => do
          let K ← ($ᵗ MK : ProbComp MK)
          pure ((), (({ h with keys := h.keys ++ [K] }, .unknown), none))
      else do
        let mt ← D h.keys.length
        pure ((), (({ h with keys := h.keys ++ [mt.2] }, .seed mt.1), none))

def genNK (P : Params) (D : ℕ → ProbComp (CK × MK)) : ℕ → SPK Unit
  | 0 => pure ()
  | n + 1 => do genStepK G P D; genNK P D n

def genUpToK (P : Params) (D : ℕ → ProbComp (CK × MK)) (i : ℕ) : SPK Unit := do
  let st ← liftK getH
  genNK G P D (i - st.keys.length)

def revealK : SPK CK :=
  StateT.mk fun ⟨s, _⟩ => (fun z => (z.1, (z.2, none))) <$> (reveal : SP CK).run s

def senderKeyK : SPK CK := do
  let st ← liftK getH
  match st.senderCorruptedAt, st.corrKey with
  | some c, some w => pure (chainFrom G c w (st.lastSentIdx - c))
  | _, _ => revealK

def receiveHK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (hint : Option M) (a : AD) (c : ℕ × C) :
    SPK (Option (ℕ × M)) := do
  let (i, e) := c
  let st ← liftK getH
  if st.skipped.contains i then
    match ← liftK (decIdx ae P ops hint i a e) with
    | some msg =>
      liftK (modifyH fun st => { st with skipped := st.skipped.filter (· != i) })
      pure (some (i, msg))
    | none => pure none
  else if i ≤ st.receiverIdx ∨ maxSkip < i - st.receiverIdx - 1 then pure none
  else if !P.la && st.lastSentIdx < i && !st.isCompromised i then pure none
  else do
    genUpToK G P D i
    match ← liftK (decIdx ae P ops hint i a e) with
    | some msg =>
      liftK (modifyH fun st' => { st' with skipped := newSkipped st.receiverIdx i ++ st'.skipped })
      pure (some (i, msg))
    | none => pure none

def transmitHWithK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (q : AD × M) : SPK (Option (ℕ × C)) := do
  let st ← liftK getH
  if st.ended then pure none else
  let i := st.lastSentIdx + 1
  genUpToK G P D i
  let e ← liftK (encIdxWith ideal ae P ops i q.1 q.2)
  liftK (modifyH fun st => { st with lastSentIdx := i,
                                     inTransit := ⟨i, q.1, q.2, (i, e)⟩ :: st.inTransit })
  pure (some (i, e))

def challengeHWithK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (q : AD × M × M) : SPK (Option (ℕ × C)) := do
  let st ← liftK getH
  if st.ended || st.senderCorruptedAt.isSome then pure none else
  let (a, m0, m1) := q
  let msg := if st.b then m1 else m0
  let i := st.lastSentIdx + 1
  genUpToK G P D i
  let e ← liftK (encIdxWith ideal ae P ops i a msg)
  liftK (modifyH fun st => { st with lastSentIdx := i,
                                     inTransit := ⟨i, a, msg, (i, e)⟩ :: st.inTransit,
                                     challengesInTransit := i :: st.challengesInTransit })
  pure (some (i, e))

def corruptSenderHK (P : Params) (_ : Unit) : SPK (Option (RatchetSenderState CK)) := do
  let st ← liftK getH
  if st.ended then pure none
  else if P.la then do liftK (modifyH fun st => { st with ended := true }); pure none
  else do
  let w ← senderKeyK G
  liftK (modifyH fun st' => { st' with senderCorruptedAt := some (st.senderCorruptedAt.getD st.lastSentIdx),
                                       corrKey := some (st.corrKey.getD w) })
  pure (some ⟨w, st.lastSentIdx⟩)

def corruptReceiverHK (P : Params) (_ : Unit) :
    SPK (Option (RatchetSenderState CK × RatchetReceiverState CK MK)) := do
  let st ← liftK getH
  if st.ended || !st.challengesInTransit.isEmpty ||
      st.inTransit.any (fun r => !st.isCompromised r.idx) then pure none
  else if P.la then do liftK (modifyH fun st => { st with ended := true }); pure none
  else do
  let wA ← senderKeyK G
  let st ← liftK getH
  let wB := match st.senderCorruptedAt, st.corrKey with
    | some c, some w => chainFrom G c w (st.receiverIdx - c)
    | _, _ => wA
  let D := (st.skipped.filter st.isCompromised).filterMap fun i => (st.keys[i - 1]?).map (i, ·)
  liftK (modifyH fun st => { st with ended := true })
  pure (some (⟨wA, st.lastSentIdx⟩, ⟨wB, st.receiverIdx, D⟩))

def deliverHK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (q : AD × (ℕ × C)) :
    SPK (Option (ReceiveResult M)) := do
  let st ← liftK getH
  if st.ended then pure none else
  match st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
  | none => pure none
  | some r =>
    let inWindow := decide (r.idx ≤ st.receiverIdx + maxSkip + 1)
    let mustBeCorrect := !st.isCompromised r.idx && inWindow
    match ← receiveHK ae G maxSkip P D ops (some r.msg) q.1 q.2 with
    | none =>
      liftK (modifyH fun st' => { st' with win := st'.win || mustBeCorrect })
      pure (some .rejected)
    | some (i', m') =>
      let incorrect := mustBeCorrect && (i' != r.idx || m' != r.msg)
      let out := if st.challengesInTransit.contains r.idx then none else some m'
      liftK (modifyH fun st' => ({ st' with receiverIdx := max st'.receiverIdx i',
                                            win := st'.win || incorrect }).removeFromTransit r.idx)
      pure (some (.accepted i' out))

def injectHK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (q : AD × (ℕ × C)) :
    SPK (Option (ReceiveResult M)) := do
  let st ← liftK getH
  if st.ended || st.inTransit.any (fun r => r.ad == q.1 && r.ct == q.2) then pure none else
  match ← receiveHK ae G maxSkip P D ops none q.1 q.2 with
  | none => pure (some .rejected)
  | some (i', m') =>
    let forged := !st.isCompromised i'
    let lfNow := forged && decide (st.lastSentIdx < i')
    liftK (modifyH fun st' => ({ st' with receiverIdx := max st'.receiverIdx i',
                                          win := st'.win || forged, lf := st'.lf || lfNow,
                                          ended := st'.ended || (P.la && lfNow) }).removeFromTransit i')
    pure (some (.accepted i' (some m')))

def implWithK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) :
    QueryImpl (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      SPK
  | .inl n => liftK (sampleH ($ᵗ Fin (n + 1)))
  | .inr (.inl (.inl (.inl (.inl (.inl q))))) => transmitHWithK ideal ae G P D ops q
  | .inr (.inl (.inl (.inl (.inl (.inr q))))) => challengeHWithK ideal ae G P D ops q
  | .inr (.inl (.inl (.inl (.inr u)))) => corruptSenderHK G P u
  | .inr (.inl (.inl (.inr u))) => corruptReceiverHK G P u
  | .inr (.inl (.inr q)) => deliverHK ae G maxSkip P D ops q
  | .inr (.inr q) => injectHK ae G maxSkip P D ops q

@[simp] theorem liftK_pure {α : Type} (a : α) :
    liftK (pure a : SP α) = pure a := by
  ext ⟨s, opt⟩; simp [liftK]

@[simp] theorem liftK_bind {α β : Type} (x : SP α) (k : α → SP β) :
    liftK (x >>= k) = liftK x >>= fun a => liftK (k a) := by
  ext ⟨s, opt⟩
  simp [liftK, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc, pure_bind]

theorem comm_genStepK (P : Params) (D : ℕ → ProbComp (CK × MK)) :
    Comm (keysFill P.j) (genStepK G P D : SPK Unit) := by
  rintro ⟨⟨h, sl⟩, opt⟩
  cases sl with
  | seed w =>
    cases opt <;>
      simp [fillSt, fillOut, keysFill, genStepK, map_eq_bind_pure_comp, bind_assoc, pure_bind] <;>
      exact DEq.refl _
  | mat pos mt =>
    by_cases hlt : h.keys.length < pos <;> cases opt <;>
      simp [fillSt, fillOut, keysFill, genStepK, hlt, map_eq_bind_pure_comp, bind_assoc, pure_bind] <;>
      exact DEq.refl _
  | unknown =>
    by_cases hlt : h.keys.length < P.j
    · cases opt with
      | none =>
        have hsub : P.j - h.keys.length = (P.j - (h.keys.length + 1)) + 1 := by omega
        simp [fillSt, fillOut, keysFill, genStepK, hlt, hsub, sampleKeys,
          map_eq_bind_pure_comp, bind_assoc, pure_bind]
        exact DEq.refl _
      | some ks =>
        cases ks <;>
          simp [fillSt, fillOut, keysFill, genStepK, hlt, map_eq_bind_pure_comp, bind_assoc, pure_bind] <;>
          exact DEq.refl _
    · have hsub : P.j - h.keys.length = 0 := by omega
      cases opt <;>
        simp [fillSt, fillOut, keysFill, genStepK, hlt, hsub, sampleKeys,
          map_eq_bind_pure_comp, bind_assoc, pure_bind] <;>
        exact DEq.refl _

theorem comm_genNK (P : Params) (D : ℕ → ProbComp (CK × MK)) (n : ℕ) :
    Comm (keysFill P.j) (genNK G P D n : SPK Unit) := by
  induction n with
  | zero => exact Comm.pure (idem_keysFill P.j) ()
  | succ n ih => exact Comm.bind (comm_genStepK G P D) fun _ => ih

theorem comm_genUpToK (P : Params) (D : ℕ → ProbComp (CK × MK)) (i : ℕ) :
    Comm (keysFill P.j) (genUpToK G P D i : SPK Unit) :=
  Comm.bind (comm_getHK P.j) fun st => comm_genNK G P D (i - st.keys.length)

theorem comm_revealK (N : ℕ) :
    Comm (keysFill N) (revealK : SPK CK) := by
  rintro ⟨s, opt⟩
  simp only [fillSt, revealK, StateT.run_mk, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind]
  exact DEq.bind_const _ _

theorem comm_senderKeyK (N : ℕ) :
    Comm (keysFill N) (senderKeyK G : SPK CK) := by
  unfold senderKeyK
  refine Comm.bind (comm_getHK N) fun st => ?_
  split
  · exact Comm.pure (idem_keysFill N) _
  · exact comm_revealK N

theorem comm_encIdxWithK (P : Params) (i : ℕ) (a : AD) (msg : M) :
    Comm (keysFill (CK := CK) P.j)
      (liftK (encIdxWith (CK := CK) ideal ae P (none : Option (SpecialOps AD M C ProbComp)) i a msg)) := by
  unfold encIdxWith
  change Comm (keysFill P.j) (liftK (getH >>= _))
  rw [liftK_bind]
  refine Comm.bind (comm_getHK P.j) fun st => ?_
  split
  · exact comm_sampleHK P.j _
  · next h => cases h
  · split
    · rw [liftK_pure]; exact Comm.pure (idem_keysFill P.j) _
    · exact comm_sampleHK P.j _

theorem comm_decIdxK (P : Params) (hint : Option M) (i : ℕ) (a : AD) (e : C) :
    Comm (keysFill (CK := CK) P.j)
      (liftK (decIdx (CK := CK) ae P (none : Option (SpecialOps AD M C ProbComp)) hint i a e)) := by
  cases hint with
  | some msg =>
    unfold decIdx
    rw [liftK_pure]
    exact Comm.pure (idem_keysFill P.j) _
  | none =>
    unfold decIdx
    change Comm (keysFill P.j) (liftK (getH >>= _))
    rw [liftK_bind]
    refine Comm.bind (comm_getHK P.j) fun st => ?_
    split
    · rw [liftK_pure]; exact Comm.pure (idem_keysFill P.j) _
    · next h => cases h
    · rw [liftK_pure]; exact Comm.pure (idem_keysFill P.j) _

theorem comm_receiveHK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (hint : Option M) (a : AD) (c : ℕ × C) :
    Comm (keysFill P.j)
      (receiveHK ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) hint a c) := by
  unfold receiveHK
  refine Comm.bind (comm_getHK P.j) fun st => ?_
  split
  · refine Comm.bind (comm_decIdxK ae P hint c.1 a c.2) fun r => ?_
    cases r with
    | none => exact Comm.pure (idem_keysFill P.j) _
    | some msg =>
      exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
        Comm.pure (idem_keysFill P.j) _
  · split
    · exact Comm.pure (idem_keysFill P.j) _
    · split
      · exact Comm.pure (idem_keysFill P.j) _
      · refine Comm.bind (comm_genUpToK G P D c.1) fun _ => ?_
        refine Comm.bind (comm_decIdxK ae P hint c.1 a c.2) fun r => ?_
        cases r with
        | none => exact Comm.pure (idem_keysFill P.j) _
        | some msg =>
          exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
            Comm.pure (idem_keysFill P.j) _

theorem comm_transmitHWithK (P : Params) (D : ℕ → ProbComp (CK × MK)) (q : AD × M) :
    Comm (keysFill P.j)
      (transmitHWithK ideal ae G P D (none : Option (SpecialOps AD M C ProbComp)) q) := by
  unfold transmitHWithK
  refine Comm.bind (comm_getHK P.j) fun st => ?_
  split
  · exact Comm.pure (idem_keysFill P.j) _
  · refine Comm.bind (comm_genUpToK G P D _) fun _ => ?_
    refine Comm.bind (comm_encIdxWithK ideal ae P _ q.1 q.2) fun e => ?_
    exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
      Comm.pure (idem_keysFill P.j) _

theorem comm_challengeHWithK (P : Params) (D : ℕ → ProbComp (CK × MK)) (q : AD × M × M) :
    Comm (keysFill P.j)
      (challengeHWithK ideal ae G P D (none : Option (SpecialOps AD M C ProbComp)) q) := by
  unfold challengeHWithK
  refine Comm.bind (comm_getHK P.j) fun st => ?_
  split
  · exact Comm.pure (idem_keysFill P.j) _
  · refine Comm.bind (comm_genUpToK G P D _) fun _ => ?_
    refine Comm.bind (comm_encIdxWithK ideal ae P _ q.1 _) fun e => ?_
    exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
      Comm.pure (idem_keysFill P.j) _

theorem comm_corruptSenderHK (P : Params) (u : Unit) :
    Comm (keysFill P.j) (corruptSenderHK (AD := AD) (M := M) (C := C) (MK := MK) G P u) := by
  unfold corruptSenderHK
  refine Comm.bind (comm_getHK P.j) fun st => ?_
  split
  · exact Comm.pure (idem_keysFill P.j) _
  · split
    · exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
        Comm.pure (idem_keysFill P.j) _
    · refine Comm.bind (comm_senderKeyK G P.j) fun w => ?_
      exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
        Comm.pure (idem_keysFill P.j) _

theorem comm_corruptReceiverHK (P : Params) (u : Unit) :
    Comm (keysFill P.j) (corruptReceiverHK (AD := AD) (M := M) (C := C) (MK := MK) G P u) := by
  unfold corruptReceiverHK
  refine Comm.bind (comm_getHK P.j) fun st => ?_
  split
  · exact Comm.pure (idem_keysFill P.j) _
  · split
    · exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
        Comm.pure (idem_keysFill P.j) _
    · refine Comm.bind (comm_senderKeyK G P.j) fun wA => ?_
      refine Comm.bind (comm_getHK P.j) fun st' => ?_
      exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
        Comm.pure (idem_keysFill P.j) _

theorem comm_deliverHK (P : Params) (D : ℕ → ProbComp (CK × MK)) (q : AD × (ℕ × C)) :
    Comm (keysFill P.j)
      (deliverHK ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) q) := by
  unfold deliverHK
  refine Comm.bind (comm_getHK P.j) fun st => ?_
  split
  · exact Comm.pure (idem_keysFill P.j) _
  · cases st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
    | none => exact Comm.pure (idem_keysFill P.j) _
    | some r =>
      dsimp only
      refine Comm.bind (comm_receiveHK ae G maxSkip P D (some r.msg) q.1 q.2) fun res => ?_
      cases res with
      | none =>
        exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
          Comm.pure (idem_keysFill P.j) _
      | some p =>
        exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
          Comm.pure (idem_keysFill P.j) _

theorem comm_injectHK (P : Params) (D : ℕ → ProbComp (CK × MK)) (q : AD × (ℕ × C)) :
    Comm (keysFill P.j)
      (injectHK ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) q) := by
  unfold injectHK
  refine Comm.bind (comm_getHK P.j) fun st => ?_
  split
  · exact Comm.pure (idem_keysFill P.j) _
  · refine Comm.bind (comm_receiveHK ae G maxSkip P D none q.1 q.2) fun res => ?_
    cases res with
    | none => exact Comm.pure (idem_keysFill P.j) _
    | some p =>
      exact Comm.bind (comm_modifyHK P.j _ fun _ => rfl) fun _ =>
        Comm.pure (idem_keysFill P.j) _

theorem comm_implWithK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (t : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M
      (ℕ × C)).Domain) :
    Comm (keysFill P.j)
      (implWithK ideal ae G maxSkip P D (none : Option (SpecialOps AD M C ProbComp)) t) := by
  rcases t with n | ((((((q | q) | u) | u) | q) | q))
  · exact comm_sampleHK P.j _
  · exact comm_transmitHWithK ideal ae G P D q
  · exact comm_challengeHWithK ideal ae G P D q
  · exact comm_corruptSenderHK G P u
  · exact comm_corruptReceiverHK G P u
  · exact comm_deliverHK ae G maxSkip P D q
  · exact comm_injectHK ae G maxSkip P D q

def EqNone {α : Type} (x : SP α) (y : SPK α) : Prop :=
  ∀ s, y.run (s, none) = (liftK x).run (s, none)

theorem EqNone.lift {α : Type} (x : SP α) : EqNone x (liftK x) := fun _ => rfl

theorem EqNone.pure {α : Type} (a : α) : EqNone (pure a : SP α) (pure a : SPK α) := fun _ => rfl

theorem EqNone.bind {α β : Type} {x : SP α} {y : SPK α} {f : α → SP β} {g : α → SPK β}
    (hx : EqNone x y) (hf : ∀ a, EqNone (f a) (g a)) :
    EqNone (x >>= f) (y >>= g) := by
  intro s
  simp only [StateT.run_bind, hx s, liftK, StateT.run_mk, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind]
  congr 1; ext z
  simpa only [liftK, StateT.run_mk, map_eq_bind_pure_comp] using hf z.1 z.2

theorem EqNone.simulateQ {ι : Type} {ospec : OracleSpec ι} {α : Type}
    {impl : QueryImpl ospec SP} {implK : QueryImpl ospec SPK}
    (himpl : ∀ t, EqNone (impl t) (implK t)) (oa : OracleComp ospec α) :
    EqNone (simulateQ impl oa) (simulateQ implK oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact EqNone.pure a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map]
    exact EqNone.bind (himpl t) ih

theorem eqNone_genStepK (P : Params) (D : ℕ → ProbComp (CK × MK)) :
    EqNone (genStep G P D : SP Unit) (genStepK G P D : SPK Unit) := by
  rintro ⟨h, sl⟩
  cases sl with
  | seed w => rfl
  | mat pos mt =>
    by_cases hlt : h.keys.length < pos <;>
      simp [genStepK, liftK, genStep, hlt, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  | unknown =>
    by_cases hlt : h.keys.length < P.j <;>
      simp [genStepK, liftK, genStep, hlt, map_eq_bind_pure_comp, bind_assoc, pure_bind]

theorem eqNone_genNK (P : Params) (D : ℕ → ProbComp (CK × MK)) (n : ℕ) :
    EqNone (genN G P D n : SP Unit) (genNK G P D n : SPK Unit) := by
  induction n with
  | zero => exact EqNone.pure ()
  | succ n ih => exact EqNone.bind (eqNone_genStepK G P D) fun _ => ih

theorem eqNone_genUpToK (P : Params) (D : ℕ → ProbComp (CK × MK)) (i : ℕ) :
    EqNone (genUpTo G P D i : SP Unit) (genUpToK G P D i : SPK Unit) :=
  EqNone.bind (EqNone.lift getH) fun st => eqNone_genNK G P D (i - st.keys.length)

theorem eqNone_revealK : EqNone (reveal : SP CK) (revealK : SPK CK) := fun _ => rfl

theorem eqNone_senderKeyK : EqNone (senderKey G : SP CK) (senderKeyK G : SPK CK) := by
  unfold senderKey senderKeyK
  refine EqNone.bind (EqNone.lift getH) fun st => ?_
  cases st.senderCorruptedAt <;> cases st.corrKey
  · exact eqNone_revealK
  · exact eqNone_revealK
  · exact eqNone_revealK
  · exact EqNone.pure _

theorem eqNone_receiveHK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (hint : Option M) (a : AD) (c : ℕ × C) :
    EqNone (receiveH ae G maxSkip P D ops hint a c)
      (receiveHK ae G maxSkip P D ops hint a c) := by
  unfold receiveH receiveHK
  refine EqNone.bind (EqNone.lift getH) fun st => ?_
  split
  · refine EqNone.bind (EqNone.lift _) fun r => ?_
    cases r with
    | none => exact EqNone.pure _
    | some msg => exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _
  · split
    · exact EqNone.pure _
    · split
      · exact EqNone.pure _
      · refine EqNone.bind (eqNone_genUpToK G P D c.1) fun _ => ?_
        refine EqNone.bind (EqNone.lift _) fun r => ?_
        cases r with
        | none => exact EqNone.pure _
        | some msg => exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _

theorem eqNone_transmitHWithK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (q : AD × M) :
    EqNone (transmitHWith ideal ae G P D ops q) (transmitHWithK ideal ae G P D ops q) := by
  unfold transmitHWith transmitHWithK
  refine EqNone.bind (EqNone.lift getH) fun st => ?_
  split
  · exact EqNone.pure _
  · refine EqNone.bind (eqNone_genUpToK G P D _) fun _ => ?_
    refine EqNone.bind (EqNone.lift _) fun e => ?_
    exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _

theorem eqNone_challengeHWithK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (q : AD × M × M) :
    EqNone (challengeHWith ideal ae G P D ops q) (challengeHWithK ideal ae G P D ops q) := by
  unfold challengeHWith challengeHWithK
  refine EqNone.bind (EqNone.lift getH) fun st => ?_
  split
  · exact EqNone.pure _
  · refine EqNone.bind (eqNone_genUpToK G P D _) fun _ => ?_
    refine EqNone.bind (EqNone.lift _) fun e => ?_
    exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _

theorem eqNone_corruptSenderHK (P : Params) (u : Unit) :
    EqNone (corruptSenderH (m := ProbComp) (AD := AD) (M := M) (C := C) G P u)
      (corruptSenderHK G P u) := by
  unfold corruptSenderH corruptSenderHK
  refine EqNone.bind (EqNone.lift getH) fun st => ?_
  split
  · exact EqNone.pure _
  · split
    · exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _
    · refine EqNone.bind (eqNone_senderKeyK G) fun w => ?_
      exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _

theorem eqNone_corruptReceiverHK (P : Params) (u : Unit) :
    EqNone (corruptReceiverH (m := ProbComp) (AD := AD) (M := M) (C := C) (MK := MK) G P u)
      (corruptReceiverHK G P u) := by
  unfold corruptReceiverH corruptReceiverHK
  refine EqNone.bind (EqNone.lift getH) fun st => ?_
  split
  · exact EqNone.pure _
  · split
    · exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _
    · refine EqNone.bind (eqNone_senderKeyK G) fun wA => ?_
      refine EqNone.bind (EqNone.lift getH) fun st' => ?_
      exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _

theorem eqNone_deliverHK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (q : AD × (ℕ × C)) :
    EqNone (deliverH ae G maxSkip P D ops q) (deliverHK ae G maxSkip P D ops q) := by
  unfold deliverH deliverHK
  refine EqNone.bind (EqNone.lift getH) fun st => ?_
  split
  · exact EqNone.pure _
  · cases st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
    | none => exact EqNone.pure _
    | some r =>
      dsimp only
      refine EqNone.bind (eqNone_receiveHK ae G maxSkip P D ops (some r.msg) q.1 q.2) fun res => ?_
      cases res with
      | none => exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _
      | some p => exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _

theorem eqNone_injectHK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp)) (q : AD × (ℕ × C)) :
    EqNone (injectH ae G maxSkip P D ops q) (injectHK ae G maxSkip P D ops q) := by
  unfold injectH injectHK
  refine EqNone.bind (EqNone.lift getH) fun st => ?_
  split
  · exact EqNone.pure _
  · refine EqNone.bind (eqNone_receiveHK ae G maxSkip P D ops none q.1 q.2) fun res => ?_
    cases res with
    | none => exact EqNone.pure _
    | some p => exact EqNone.bind (EqNone.lift _) fun _ => EqNone.pure _

theorem eqNone_implWithK (P : Params) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C ProbComp))
    (t : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M
      (ℕ × C)).Domain) :
    EqNone (implWith ideal ae G maxSkip P D ops t) (implWithK ideal ae G maxSkip P D ops t) := by
  rcases t with n | ((((((q | q) | u) | u) | q) | q))
  · exact EqNone.lift _
  · exact eqNone_transmitHWithK ideal ae G P D ops q
  · exact eqNone_challengeHWithK ideal ae G P D ops q
  · exact eqNone_corruptSenderHK G P u
  · exact eqNone_corruptReceiverHK G P u
  · exact eqNone_deliverHK ae G maxSkip P D ops q
  · exact eqNone_injectHK ae G maxSkip P D ops q

/-- Pre-sampling `sampleKeys N` for `implWithK` matches `hRunWith` at `hp N 0 la`. -/
theorem eagerKeys_deq_hRunWith (N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    DEq
      (do
        let ks ← sampleKeys N
        let b ← $ᵗ Bool
        let z ← (simulateQ (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none) A).run
          (hInit b .unknown, some ks)
        pure (hOut la (z.1, z.2.1)))
      (hRunWith ideal ae G maxSkip (hp N 0 la) (DG G) none A .unknown) := by
  unfold hRunWith
  simp only [hp_la, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  refine (DEq.swap (sampleKeys N) ($ᵗ Bool) _).trans ?_
  refine DEq.bind_right ($ᵗ Bool) fun b => ?_
  have hcomm := Comm.simulateQ (idem_keysFill N)
    (comm_implWithK ideal ae G maxSkip (hp N 0 la) (DG G)) A (hInit b .unknown, none)
  have hfill1 := (Lazy.map_fillOut (fill := keysFill N) (fun a h => hOut la (a, h))
    (fillSt (keysFill N) (hInit b .unknown, none) >>=
      (simulateQ (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none) A).run)).symm
  have hfill2 := Lazy.map_fillOut (fill := keysFill N) (fun a h => hOut la (a, h))
    ((simulateQ (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none) A).run
      (hInit b .unknown, none))
  have hchain := (hfill1.trans (DEq.map hcomm (fun a => hOut la (a.1, a.2.1)))).trans hfill2
  have heq := EqNone.simulateQ (eqNone_implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none)
    A (hInit b .unknown)
  have hfillInit : fillSt (keysFill N) (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
      b .unknown, none) = (fun ks => (hInit b .unknown, some ks)) <$> sampleKeys N := by
    simp [fillSt, keysFill, hInit, Functor.map_map]
  rw [hfillInit, heq] at hchain
  simpa only [liftK, StateT.run_mk, map_eq_bind_pure_comp, Function.comp_def,
    Function.comp_apply, bind_assoc, pure_bind] using hchain

/-! ### Multi-slot real world (`b = false`) -/

section JMOnHStK

variable {ideal ae} {f : JStM CK MK AD M C → HStK CK MK AD M C}

theorem JM.readK {α : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} {g : HS → SPK α} {h : HS → SO α}
    (hgh : ∀ σ, P σ → JM ideal ae f (fun σ' => σ' = σ) (g (f σ).1.1) (h σ.1.1) Q) :
    JM ideal ae f P (liftK getH >>= g) (getH >>= h) Q := by
  intro σ hP
  have := hgh σ hP σ rfl
  simp only [YM_bind, YM_getH, pure_bind, StateT.run_bind, liftK, StateT.run_mk,
    getH_run, map_pure]
  exact this

theorem JM.modifyK {P : JStM CK MK AD M C → Prop} {Q : Unit → JStM CK MK AD M C → Prop}
    (gL gR : HS → HS)
    (hf : ∀ σ, P σ → f ((gR σ.1.1, σ.1.2), σ.2) = ((gL (f σ).1.1, (f σ).1.2), (f σ).2))
    (hQ : ∀ σ, P σ → Q () ((gR σ.1.1, σ.1.2), σ.2)) :
    JM ideal ae f P (liftK (modifyH gL) : SPK Unit) (modifyH gR : SO Unit) Q := by
  intro σ hP
  simp only [YM_modifyH, liftK, StateT.run_mk, modifyH_run, map_pure, hf σ hP]
  exact ⟨DEq.refl _, by simpa using hQ σ hP⟩

theorem JM.sampleK {α : Type} {P : JStM CK MK AD M C → Prop}
    {Q : α → JStM CK MK AD M C → Prop} (p : ProbComp α) (hQ : ∀ σ a, P σ → Q a σ) :
    JM ideal ae f P (liftK (sampleH p) : SPK α) (sampleH p : SO α) Q := by
  intro σ hP
  simp only [YM_sampleH, liftK, StateT.run_mk, sampleH_run, Functor.map_map]
  refine ⟨DEq.refl _, fun r hr => ?_⟩
  rw [support_map] at hr
  obtain ⟨a, -, rfl⟩ := hr
  exact hQ σ a hP

end JMOnHStK

def fixKeysAux (N : ℕ) (σ : ℕ → IndexedOtccaState MK AD C) (cmp : ℕ → Bool) (ks : List MK) : List MK :=
  (List.range ks.length).map fun k =>
    match ks[k]? with
    | some K => if k < N && !cmp (k + 1) then (σ (k + 1)).key else K
    | none => (σ 0).key

def fixKeys (N : ℕ) (σ : ℕ → IndexedOtccaState MK AD C) (h : HState CK MK AD M C) : List MK :=
  fixKeysAux N σ h.isCompromised h.keys

def fixHM (N : ℕ) (σ : ℕ → IndexedOtccaState MK AD C) (h : HState CK MK AD M C) : HState CK MK AD M C :=
  { h with keys := fixKeys N σ h }

def remKeys (N : ℕ) (σ : ℕ → IndexedOtccaState MK AD C) (len : ℕ) : List MK :=
  ((List.range N).drop len).map fun k => (σ (k + 1)).key

def fRM (N : ℕ) (σ : JStM CK MK AD M C) : HStK CK MK AD M C :=
  ((fixHM N σ.2 σ.1.1, σ.1.2),
    match σ.1.2 with
    | .unknown => some (remKeys N σ.2 σ.1.1.keys.length)
    | _ => none)

section ProjM

variable {N : ℕ} (σ : ℕ → IndexedOtccaState MK AD C) (h : HState CK MK AD M C)

@[simp] theorem fixHM_b : (fixHM N σ h).b = h.b := rfl
@[simp] theorem fixHM_lastSentIdx : (fixHM N σ h).lastSentIdx = h.lastSentIdx := rfl
@[simp] theorem fixHM_senderCorruptedAt : (fixHM N σ h).senderCorruptedAt = h.senderCorruptedAt := rfl
@[simp] theorem fixHM_receiverIdx : (fixHM N σ h).receiverIdx = h.receiverIdx := rfl
@[simp] theorem fixHM_ended : (fixHM N σ h).ended = h.ended := rfl
@[simp] theorem fixHM_win : (fixHM N σ h).win = h.win := rfl
@[simp] theorem fixHM_inTransit : (fixHM N σ h).inTransit = h.inTransit := rfl
@[simp] theorem fixHM_challengesInTransit :
    (fixHM N σ h).challengesInTransit = h.challengesInTransit := rfl
@[simp] theorem fixHM_corrKey : (fixHM N σ h).corrKey = h.corrKey := rfl
@[simp] theorem fixHM_skipped : (fixHM N σ h).skipped = h.skipped := rfl
@[simp] theorem fixHM_lf : (fixHM N σ h).lf = h.lf := rfl
@[simp] theorem fixHM_isCompromised (i : ℕ) : (fixHM N σ h).isCompromised i = h.isCompromised i := rfl
@[simp] theorem fixHM_isCompromised' : (fixHM N σ h).isCompromised = h.isCompromised := rfl
@[simp] theorem fixHM_length : (fixHM N σ h).keys.length = h.keys.length := by
  simp [fixHM, fixKeys, fixKeysAux]

theorem fixKeysAux_getElem? (cmp : ℕ → Bool) (ks : List MK) (i : ℕ) :
    (fixKeysAux N σ cmp ks)[i]? =
      ks[i]?.map fun K => if i < N && !cmp (i + 1) then (σ (i + 1)).key else K := by
  simp only [fixKeysAux, List.getElem?_map, List.getElem?_range]
  by_cases hi : i < ks.length
  · simp [hi, List.getElem?_eq_getElem hi]
  · simp [hi, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

theorem fixHM_getElem?_of (i : ℕ) (hi : ¬ i < N ∨ h.isCompromised (i + 1) = true) :
    (fixHM N σ h).keys[i]? = h.keys[i]? := by
  simp only [fixHM, fixKeys, fixKeysAux_getElem?]
  rcases hi with hi | hi <;> simp [hi]

theorem fixHM_getElem?_self (i : ℕ) (hiN : i < N) (hl : i < h.keys.length)
    (hc : h.isCompromised (i + 1) = false) :
    (fixHM N σ h).keys[i]? = some (σ (i + 1)).key := by
  simp [fixHM, fixKeys, fixKeysAux_getElem?, List.getElem?_eq_getElem hl, hiN, hc]

theorem fixHM_key_congr {σ' : ℕ → IndexedOtccaState MK AD C} (hkey : ∀ i, (σ' i).key = (σ i).key) :
    fixHM N σ' h = fixHM N σ h := by
  have hk : fixKeys N σ' h = fixKeys N σ h := by
    ext i K
    simp [fixKeys, fixKeysAux_getElem?, hkey]
  simp [fixHM, hk]

theorem remKeys_key_congr {σ' : ℕ → IndexedOtccaState MK AD C} (hkey : ∀ i, (σ' i).key = (σ i).key) (len : ℕ) :
    remKeys N σ' len = remKeys N σ len := by
  unfold remKeys
  congr 1; ext k; exact hkey (k + 1)

theorem fRM_key_congr {s : HSt CK MK AD M C} {σ' : ℕ → IndexedOtccaState MK AD C}
    (hkey : ∀ i, (σ' i).key = (σ i).key) :
    fRM N (s, σ') = fRM N (s, σ) := by
  unfold fRM
  rw [fixHM_key_congr σ s.1 hkey, remKeys_key_congr σ hkey]

theorem fixHM_upd' (g : HState CK MK AD M C → HState CK MK AD M C)
    (hk : ∀ h', (g h').keys = h'.keys)
    (hfc : ∀ k < N, k < h.keys.length → (g h).isCompromised (k + 1) = h.isCompromised (k + 1))
    (hg : ∀ ks, g { h with keys := ks } = { g h with keys := ks }) :
    fixHM N σ (g h) = g (fixHM N σ h) := by
  have hkeys : fixKeys N σ (g h) = fixKeys N σ h := by
    apply List.ext_getElem?
    intro i
    simp only [fixKeys, fixKeysAux_getElem?, hk]
    cases hi : h.keys[i]? with
    | none => rfl
    | some K₀ =>
      have hlt : i < h.keys.length := (List.getElem?_eq_some_iff.1 hi).1
      by_cases hiN : i < N
      · simp [hiN, hfc i hiN hlt]
      · simp [hiN]
  unfold fixHM
  rw [hkeys, hg (fixKeys N σ h)]

theorem fixHM_app_comp (y : MK)
    (hs : h.keys.length < N → h.isCompromised (h.keys.length + 1) = true) :
    fixHM N σ { h with keys := h.keys ++ [y] } =
      { fixHM N σ h with keys := (fixHM N σ h).keys ++ [y] } := by
  have hkeys : fixKeys N σ { h with keys := h.keys ++ [y] } = fixKeys N σ h ++ [y] := by
    apply List.ext_getElem?
    intro i
    dsimp only [fixKeys, HState.isCompromised]
    simp only [fixKeysAux_getElem?]
    by_cases hi : i < h.keys.length
    · have hi' : i < (fixKeysAux N σ h.isCompromised h.keys).length := by simp [fixKeysAux, hi]
      rw [List.getElem?_append_left hi, List.getElem?_append_left hi', fixKeysAux_getElem?]
      rfl
    · by_cases heq : i = h.keys.length
      · subst heq
        have hlen : (fixKeysAux N σ h.isCompromised h.keys).length = h.keys.length := by
          simp [fixKeysAux]
        rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right hlen.le]
        simp only [Nat.sub_self, hlen, List.getElem?_cons_zero, Option.map_some]
        by_cases hlt : h.keys.length < N
        · have hs' := hs hlt
          cases h
          simp_all [HState.isCompromised]
        · simp [hlt]
      · have hgt : (h.keys ++ [y]).length ≤ i := by simp; omega
        have hgt' : (fixKeysAux N σ h.isCompromised h.keys ++ [y]).length ≤ i := by
          simp [fixKeysAux]; omega
        rw [List.getElem?_eq_none hgt, List.getElem?_eq_none hgt', Option.map_none]
  simp [fixHM, hkeys]

theorem fixHM_app_unk (y : MK) (hlt : h.keys.length < N) (hc : h.senderCorruptedAt = none) :
    fixHM N σ { h with keys := h.keys ++ [y] } =
      { fixHM N σ h with keys := (fixHM N σ h).keys ++ [(σ (h.keys.length + 1)).key] } := by
  have hkeys : fixKeys N σ { h with keys := h.keys ++ [y] } =
      fixKeys N σ h ++ [(σ (h.keys.length + 1)).key] := by
    apply List.ext_getElem?
    intro i
    dsimp only [fixKeys, HState.isCompromised]
    simp only [fixKeysAux_getElem?]
    by_cases hi : i < h.keys.length
    · have hi' : i < (fixKeysAux N σ h.isCompromised h.keys).length := by simp [fixKeysAux, hi]
      rw [List.getElem?_append_left hi, List.getElem?_append_left hi', fixKeysAux_getElem?]
      rfl
    · by_cases heq : i = h.keys.length
      · subst heq
        have hlen : (fixKeysAux N σ h.isCompromised h.keys).length = h.keys.length := by
          simp [fixKeysAux]
        rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right hlen.le]
        simp [Nat.sub_self, hlen, hlt, HState.isCompromised, hc]
      · have hgt : (h.keys ++ [y]).length ≤ i := by simp; omega
        have hgt' : (fixKeysAux N σ h.isCompromised h.keys ++ [(σ (h.keys.length + 1)).key]).length ≤ i := by
          simp [fixKeysAux]; omega
        rw [List.getElem?_eq_none hgt, List.getElem?_eq_none hgt', Option.map_none]
  simp [fixHM, hkeys]

theorem fixHM_app_ge (y : MK) (hge : ¬ h.keys.length < N) :
    fixHM N σ { h with keys := h.keys ++ [y] } =
      { fixHM N σ h with keys := (fixHM N σ h).keys ++ [y] } :=
  fixHM_app_comp σ h y fun hlt => absurd hlt hge

theorem remKeys_lt {len : ℕ} (hlt : len < N) :
    remKeys N σ len = (σ (len + 1)).key :: remKeys N σ (len + 1) := by
  unfold remKeys
  have hlt' : len < (List.range N).length := by simp [hlt]
  rw [List.drop_eq_getElem_cons hlt']
  simp

theorem remKeys_ge {len : ℕ} (hge : ¬ len < N) :
    remKeys N σ len = [] := by
  simp [remKeys, Nat.le_of_not_lt hge]

theorem remKeys_init (K₀ : MK) (ks : List MK) :
    remKeys ks.length (initOStM (AD := AD) (C := C) false K₀ ks) 0 = ks := by
  apply List.ext_getElem?
  intro i
  simp only [remKeys, List.drop_zero, List.getElem?_map, List.getElem?_range]
  by_cases hi : i < ks.length
  · simp [hi, initOStM, List.getElem?_eq_getElem hi]
  · simp [hi, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

end ProjM

section InvM

variable (N : ℕ)

/-- Oracle-boundary state invariant for the multi-slot real world (`b = false`). -/
structure CoreM (σ : JStM CK MK AD M C) : Prop where
  b : ∀ i, (σ.2 i).b = false
  noMat : ∀ p mt, σ.1.2 ≠ .mat p mt
  unk : σ.1.2 = .unknown → σ.1.1.senderCorruptedAt = none
  skip : ∀ x ∈ σ.1.1.skipped, 1 ≤ x ∧ x ≤ σ.1.1.keys.length
  chalSent : ∀ i, (σ.2 i).chal.isSome → i ≤ σ.1.1.lastSentIdx
  ct : ∀ r ∈ σ.1.1.inTransit, r.ct.1 = r.idx
  chal : ∀ i i0 a e, (σ.2 i).chal = some ((i0, a), e) → i0 = i ∧
    ((∃ r ∈ σ.1.1.inTransit, r.idx = i ∧ r.ad = a ∧ r.ct = (i, e)) ∨
      (i ≤ σ.1.1.receiverIdx ∧ i ∉ σ.1.1.skipped))
  seed : ∀ w, σ.1.2 = .seed w → ∀ k < N, σ.1.1.keys.length ≤ k →
    σ.1.1.isCompromised (k + 1) = true ∨ σ.1.1.ended = true

/-- Length invariant relating generated keys, `lastSentIdx`, and `senderCorruptedAt`. -/
def LenInvM (la : Bool) (σ : JStM CK MK AD M C) : Prop :=
  (σ.1.1.senderCorruptedAt = none → la = false → σ.1.1.keys.length = σ.1.1.lastSentIdx) ∧
    ∀ c, σ.1.1.senderCorruptedAt = some c → c ≤ σ.1.1.keys.length

def KeyExtM (σ σ' : JStM CK MK AD M C) : Prop :=
  σ'.2 = σ.2 ∧ σ'.1.1 = { σ.1.1 with keys := σ'.1.1.keys }

variable {N}

theorem CoreM.app {h : HS} {sl : Slot CK MK} {ot : ℕ → IndexedOtccaState MK AD C} {y : MK}
    {sl' : Slot CK MK} (hc : CoreM N ((h, sl), ot))
    (hm : ∀ p mt, sl' ≠ .mat p mt)
    (hu : sl' = .unknown → h.senderCorruptedAt = none)
    (hs : ∀ w, sl' = .seed w → ∀ k < N, h.keys.length + 1 ≤ k →
      h.isCompromised (k + 1) = true ∨ h.ended = true) :
    CoreM N (({ h with keys := h.keys ++ [y] }, sl'), ot) where
  b := hc.b
  noMat := hm
  unk := hu
  skip x hx := by
    have := hc.skip x hx
    dsimp only at this ⊢
    simp only [List.length_append, List.length_singleton]
    omega
  chalSent := hc.chalSent
  ct := hc.ct
  chal := hc.chal
  seed w e k hk hl := by simpa using hs w e k hk (by simpa using hl)

theorem KeyExtM.trans {σ σ' σ'' : JStM CK MK AD M C} (h1 : KeyExtM σ σ') (h2 : KeyExtM σ' σ'') :
    KeyExtM σ σ'' := by
  refine ⟨h2.1.trans h1.1, ?_⟩
  rw [h2.2, h1.2]

theorem KeyExtM.refl (σ : JStM CK MK AD M C) : KeyExtM σ σ := ⟨rfl, rfl⟩

theorem KeyExtM.field {σ σ' : JStM CK MK AD M C} (h : KeyExtM σ σ') {β : Type}
    (F : HS → β) (hF : ∀ h ks, F { h with keys := ks } = F h) :
    F σ'.1.1 = F σ.1.1 := by
  rw [h.2, hF]

theorem CoreM.ofEq {h h' : HS} {sl sl' : Slot CK MK} {ot : ℕ → IndexedOtccaState MK AD C}
    (hc : CoreM N ((h, sl), ot)) (hk : h'.keys = h.keys)
    (hsk : ∀ x ∈ h'.skipped, x ∈ h.skipped ∨ (h.receiverIdx < x ∧ x ≤ h.keys.length))
    (hls : h'.lastSentIdx = h.lastSentIdx) (hit : h'.inTransit = h.inTransit)
    (hri : h'.receiverIdx = h.receiverIdx)
    (hm : ∀ p mt, sl' ≠ .mat p mt)
    (hu : sl' = .unknown → h'.senderCorruptedAt = none)
    (hseed : ∀ w, sl' = .seed w → ∀ k < N, h'.keys.length ≤ k →
      h'.isCompromised (k + 1) = true ∨ h'.ended = true) :
    CoreM N ((h', sl'), ot) where
  b := hc.b
  noMat := hm
  unk := hu
  skip x hx := by
    dsimp only at hx ⊢
    rw [hk]
    rcases hsk x hx with hx | hx
    · exact hc.skip x hx
    · omega
  chalSent i := by dsimp only; rw [hls]; exact hc.chalSent i
  ct := by dsimp only; rw [hit]; exact hc.ct
  chal i i0 a e hch := by
    obtain ⟨h0, hr⟩ := hc.chal i i0 a e hch
    refine ⟨h0, ?_⟩
    dsimp only
    rw [hit, hri]
    rcases hr with hr | ⟨h1, h2⟩
    · exact Or.inl hr
    · dsimp only at h1 h2
      refine Or.inr ⟨h1, fun hx => ?_⟩
      rcases hsk _ hx with hx | hx
      · exact h2 hx
      · omega
  seed := hseed

theorem CoreM.ofEq' {h h' : HS} {sl : Slot CK MK} {ot : ℕ → IndexedOtccaState MK AD C}
    (hc : CoreM N ((h, sl), ot)) (hk : h'.keys = h.keys) (hsk : h'.skipped = h.skipped)
    (hls : h'.lastSentIdx = h.lastSentIdx) (hit : h'.inTransit = h.inTransit)
    (hri : h'.receiverIdx = h.receiverIdx) (hcor : h'.senderCorruptedAt = h.senderCorruptedAt)
    (hen : h.ended = true → h'.ended = true) : CoreM N ((h', sl), ot) :=
  hc.ofEq hk (fun x hx => Or.inl (hsk ▸ hx)) hls hit hri hc.noMat
    (fun hu => by rw [hcor]; exact hc.unk hu)
    fun w e k hk' hl => by
      rw [isCompromised_congr hcor]
      rw [hk] at hl
      rcases hc.seed w e k hk' hl with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (hen h1)

theorem LenInvM.ofEq {la : Bool} {h h' : HS} {sl sl' : Slot CK MK}
    {ot ot' : ℕ → IndexedOtccaState MK AD C} (hl : LenInvM la ((h, sl), ot)) (hk : h'.keys = h.keys)
    (hls : h'.lastSentIdx = h.lastSentIdx) (hcor : h'.senderCorruptedAt = h.senderCorruptedAt) :
    LenInvM la ((h', sl'), ot') := by
  unfold LenInvM at hl ⊢
  dsimp only at hl ⊢
  rw [hk, hls, hcor]
  exact hl

theorem CoreM.recv {h h' : HS} {sl : Slot CK MK} {ot : ℕ → IndexedOtccaState MK AD C}
    (hc : CoreM N ((h, sl), ot)) (j : ℕ) (hk : h'.keys = h.keys) (hsk : h'.skipped = h.skipped)
    (hls : h'.lastSentIdx = h.lastSentIdx) (hcor : h'.senderCorruptedAt = h.senderCorruptedAt)
    (hen : h.ended = true → h'.ended = true)
    (hit : h'.inTransit = h.inTransit.filter (·.idx != j))
    (hri : h.receiverIdx ≤ h'.receiverIdx)
    (hj : j ≤ h'.receiverIdx ∧ j ∉ h.skipped) :
    CoreM N ((h', sl), ot) where
  b := hc.b
  noMat := hc.noMat
  unk hu := by dsimp only; rw [hcor]; exact hc.unk hu
  skip x hx := by
    dsimp only at hx ⊢
    rw [hsk] at hx
    rw [hk]
    exact hc.skip x hx
  chalSent i := by dsimp only; rw [hls]; exact hc.chalSent i
  ct r hr := by
    dsimp only at hr
    rw [hit] at hr
    exact hc.ct r (List.mem_filter.1 hr).1
  chal i i0 a e hch := by
    obtain ⟨h0, hr⟩ := hc.chal i i0 a e hch
    refine ⟨h0, ?_⟩
    dsimp only
    rw [hit, hsk]
    rcases hr with ⟨r, hr, h1, h2, h3⟩ | ⟨h1, h2⟩
    · by_cases hrj : r.idx = j
      · subst hrj; subst h1; exact Or.inr hj
      · exact Or.inl ⟨r, List.mem_filter.2 ⟨hr, by simp [hrj]⟩, h1, h2, h3⟩
    · dsimp only at h1; exact Or.inr ⟨by omega, h2⟩
  seed w e k hk' hl := by
    dsimp only at hl ⊢
    rw [isCompromised_congr hcor]
    rw [hk] at hl
    rcases hc.seed w e k hk' hl with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hen h1)

end InvM

section OraclesM

variable (N : ℕ) (la : Bool)

def InvM (σ : JStM CK MK AD M C) : Prop := CoreM N σ ∧ LenInvM la σ

theorem jmr_genStep (σ : JStM CK MK AD M C)
    (hc : CoreM N σ) (he : σ.1.1.ended = false) :
    JM ideal ae (fRM N) (· = σ)
      (genStepK G (hp N 0 la) (DG G) : SPK Unit)
      (genStep G (hp N 0 la) (DG G) : SO Unit)
      fun _ σ' => CoreM N σ' ∧ KeyExtM σ σ' ∧ σ'.1.1.keys.length = σ.1.1.keys.length + 1 := by
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  dsimp only at he
  rintro _ rfl
  cases sl with
  | seed w =>
    have hs : h.keys.length < N → h.isCompromised (h.keys.length + 1) = true := fun hlt => by
      rcases hc.seed w rfl h.keys.length hlt (le_refl _) with h' | h'
      · exact h'
      · simp_all
    simp [YM, genStepK, genStep, fRM, fixHM_app_comp ot h _ hs]
    refine ⟨DEq.refl _, hc.app (by simp) (by simp) fun w' e k hk hl => ?_, ⟨rfl, rfl⟩⟩
    exact hc.seed w rfl k hk (by dsimp only; omega)
  | mat p mt => exact absurd rfl (hc.noMat p mt)
  | unknown =>
    have hunk : h.senderCorruptedAt = none := hc.unk rfl
    by_cases hlt : h.keys.length < N
    · have hrem : remKeys N ot h.keys.length =
          (ot (h.keys.length + 1)).key :: remKeys N ot (h.keys.length + 1) :=
        remKeys_lt ot hlt
      simp [YM, genStepK, genStep, hp, hlt, fRM, hrem, fixHM_app_unk ot h _ hlt hunk,
        QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, slotLift,
        map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine ⟨(DEq.bind_const ($ᵗ MK) _).symm, fun _ =>
        ⟨hc.app (by simp) (fun _ => hunk) (by simp), rfl, rfl⟩⟩
    · simp [YM, genStepK, genStep, hp, hlt, fRM, remKeys_ge ot hlt, fixHM_app_ge ot h _ hlt,
        QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, slotLift,
        map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine ⟨DEq.refl _, by
        rintro _ _ _ _ _ _ rfl rfl rfl
        exact ⟨hc.app (by simp) (by simp) fun _ _ k hk hl => by omega, ⟨rfl, rfl⟩, by simp⟩⟩

theorem jmr_genN (n : ℕ) : ∀ (σ : JStM CK MK AD M C), CoreM N σ → σ.1.1.ended = false →
    JM ideal ae (fRM N) (· = σ)
      (genNK G (hp N 0 la) (DG G) n : SPK Unit)
      (genN G (hp N 0 la) (DG G) n : SO Unit)
      fun _ σ' => CoreM N σ' ∧ KeyExtM σ σ' ∧ σ'.1.1.keys.length = σ.1.1.keys.length + n := by
  induction n with
  | zero =>
    intro σ hc _
    exact JM.pure _ fun σ' h => by subst h; exact ⟨hc, KeyExtM.refl _, rfl⟩
  | succ n ih =>
    intro σ hc he
    refine JM.bind (jmr_genStep ideal ae G N la σ hc he) fun _ =>
      JM.ofExact fun σ' ⟨hc', hx, hl⟩ => ?_
    have he' : σ'.1.1.ended = false := (hx.field HState.ended fun _ _ => rfl).trans he
    refine (ih σ' hc' he').mono (fun _ h => h) fun _ σ'' ⟨c, x, l⟩ => ⟨c, hx.trans x, by omega⟩

theorem jmr_genUpTo (i : ℕ) (σ : JStM CK MK AD M C) (hc : CoreM N σ) (he : σ.1.1.ended = false) :
    JM ideal ae (fRM N) (· = σ)
      (genUpToK G (hp N 0 la) (DG G) i : SPK Unit)
      (genUpTo G (hp N 0 la) (DG G) i : SO Unit)
      fun _ σ' => CoreM N σ' ∧ KeyExtM σ σ' ∧ σ'.1.1.keys.length = max σ.1.1.keys.length i := by
  unfold genUpToK genUpTo
  refine JM.readK fun σ0 h0 => ?_
  subst h0
  simp only [fRM, fixHM_length]
  refine (jmr_genN ideal ae G N la _ _ hc he).mono (fun _ h => h) fun _ σ' ⟨c, x, l⟩ =>
    ⟨c, x, by omega⟩

def RevPostM (σ σ' : JStM CK MK AD M C) : Prop :=
  σ'.2 = σ.2 ∧ σ'.1.1 = σ.1.1 ∧ ∃ u, σ'.1.2 = .seed u

theorem jmr_reveal (σ : JStM CK MK AD M C) :
    JM ideal ae (fRM N) (· = σ) (revealK : SPK CK) (reveal : SO CK) fun _ σ' => RevPostM σ σ' := by
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  rintro _ rfl
  cases sl <;>
    simp [YM, revealK, reveal, fRM, RevPostM, QueryImpl.simulateQ_add_liftM_left,
      simulateQ_liftTarget, slotLift] <;>
    exact DEq.refl _

theorem jmr_senderKey (σ : JStM CK MK AD M C) (hc : CoreM N σ) :
    JM ideal ae (fRM N) (· = σ) (senderKeyK G : SPK CK) (senderKey G : SO CK)
      fun _ σ' => RevPostM σ σ' := by
  unfold senderKeyK senderKey
  refine JM.readK fun σ0 h0 => ?_
  subst h0
  dsimp only [fRM, fixHM]
  cases hcs : σ0.1.1.senderCorruptedAt <;> cases hck : σ0.1.1.corrKey <;> dsimp only
  · exact jmr_reveal ideal ae N _
  · exact jmr_reveal ideal ae N _
  · exact jmr_reveal ideal ae N _
  · refine JM.pure _ fun σ' h => ?_
    subst h
    refine ⟨rfl, rfl, ?_⟩
    cases hsl : σ'.1.2 with
    | seed u => exact ⟨u, rfl⟩
    | mat p mt => exact absurd hsl (hc.noMat p mt)
    | unknown =>
      have := hc.unk hsl
      simp [this] at hcs

def EncPostM (i : ℕ) (a : AD) (σ : JStM CK MK AD M C) (e : C) (σ' : JStM CK MK AD M C) : Prop :=
  σ'.1 = σ.1 ∧ (σ'.2 = σ.2 ∨ (1 ≤ i ∧ i ≤ N ∧ σ.1.1.isCompromised i = false ∧
    (σ.2 i).chal = none ∧ σ'.2 = Function.update σ.2 i { σ.2 i with chal := some ((i, a), e) }))

theorem jmr_encIdx (i : ℕ) (a : AD) (msg : M) (σ : JStM CK MK AD M C) (hc : CoreM N σ)
    (hl : i ≤ σ.1.1.keys.length) (hi : i = σ.1.1.lastSentIdx + 1) :
    JM ideal ae (fRM N) (· = σ)
      (liftK (encIdxWith ideal ae (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp)) i a msg) : SPK C)
      (multiEncIdxWith ideal ae 0 N (some (otOpsWith ideal)) i a msg : SO C)
      (EncPostM N i a σ) := by
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  dsimp only at hl hi
  unfold encIdxWith multiEncIdxWith
  change JM ideal ae (fRM N) (· = ((h, sl), ot)) (liftK (getH >>= _)) (getH >>= _) _
  rw [liftK_bind]
  refine JM.readK fun σ0 h0 => ?_
  subst h0
  simp only [fRM]
  have hpure : ∀ c : C, JM ideal ae (fRM N) (· = ((h, sl), ot)) (liftK (pure c) : SPK C) (pure c : SO C)
      (EncPostM N i a ((h, sl), ot)) := fun c => by
    rw [liftK_pure]
    exact JM.pure _ fun σ' e => by subst e; exact ⟨rfl, Or.inl rfl⟩
  have hsamp : JM ideal ae (fRM N) (· = ((h, sl), ot)) (liftK (sampleH (ideal (i, a))) : SPK C)
      (sampleH (ideal (i, a)) : SO C) (EncPostM N i a ((h, sl), ot)) :=
    JM.sampleK _ fun σ' _ e => by subst e; exact ⟨rfl, Or.inl rfl⟩
  have hi0 : ¬ i ≤ 0 := by omega
  by_cases hcmp : h.isCompromised i = true
  · have h1 : kind (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp)) (fixHM N ot h) i =
        .real := by simp [kind, hcmp]
    have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) h i = .real := by
      simp [multiKind, hcmp]
    rw [h1, h2]
    dsimp only
    rw [fixHM_getElem?_of ot h (i - 1) (Or.inr (by rw [show i - 1 + 1 = i by omega]; exact hcmp))]
    cases h.keys[i - 1]? <;> dsimp only
    · exact hsamp
    · exact hpure _
  · simp only [Bool.not_eq_true] at hcmp
    by_cases hiN : i ≤ N
    · have h1 : kind (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp)) (fixHM N ot h) i =
          .real := by simp [kind, hcmp, hp, hi0]
      have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) h i =
          .special := by simp [multiKind, hcmp, hi0, hiN]
      rw [h1, h2]
      dsimp only
      rw [fixHM_getElem?_self ot h (i - 1) (by omega) (by omega)
        (by rw [show i - 1 + 1 = i by omega]; exact hcmp)]
      dsimp only
      have hch : (ot i).chal = none := by
        cases hh : (ot i).chal with
        | none => rfl
        | some c => have := hc.chalSent i (by simp [hh]); dsimp only at this; omega
      have hb : (ot i).b = false := hc.b i
      rintro σ' rfl
      rw [YM_lift, liftK_pure]
      rcases hslot : ot i with ⟨key, b, chal⟩
      rw [hslot] at hch hb
      dsimp only at hch hb
      subst hch hb
      have hkey_upd : ∀ j, (Function.update ot i
          ({ key := key, b := false, chal := some ((i, a), ae.enc key (i, a) msg) } : IndexedOtccaState MK AD C) j).key =
          (ot j).key := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [hslot]
        · simp [Function.update_of_ne hj]
      simp [otOpsWith, slotLift, slotLiftOtcca, otImpl, hslot, AEADScheme.otccaEncryptAdIdeal,
        EncPostM, hcmp, hiN, show 1 ≤ i by omega, show i - 1 + 1 = i by omega,
        fRM_key_congr ot hkey_upd]
      exact DEq.refl _
    · have h1 : kind (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp)) (fixHM N ot h) i =
          .real := by simp [kind, hcmp, hp, hi0]
      have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) h i =
          .real := by simp [multiKind, hcmp, hi0, hiN]
      rw [h1, h2]
      dsimp only
      rw [fixHM_getElem?_of ot h (i - 1) (Or.inl (by omega))]
      cases h.keys[i - 1]? <;> dsimp only
      · exact hsamp
      · exact hpure _

theorem jmr_decIdx (hint : Option M) (i : ℕ) (a : AD) (e : C) (σ : JStM CK MK AD M C)
    (hc : CoreM N σ) (hi : 1 ≤ i)
    (hch : hint = none → (σ.2 i).chal ≠ some ((i, a), e))
    (hk : i ≤ N → σ.1.1.isCompromised i = false → i - 1 < σ.1.1.keys.length) :
    JM ideal ae (fRM N) (· = σ)
      (liftK (decIdx ae (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp)) hint i a e) : SPK (Option M))
      (multiDecIdx ae 0 N (some (otOpsWith ideal)) hint i a e : SO (Option M))
      fun _ σ' => σ' = σ := by
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  dsimp only at hch hk
  have hpure : ∀ c : Option M, JM ideal ae (fRM N) (· = ((h, sl), ot))
      (liftK (pure c) : SPK (Option M)) (pure c : SO (Option M))
      fun _ σ' => σ' = ((h, sl), ot) := fun c => by
    rw [liftK_pure]
    exact JM.pure _ fun σ' e => e
  cases hint with
  | some m => exact hpure _
  | none =>
    unfold decIdx multiDecIdx
    have hhint : (none : Option M) = none := rfl
    change JM ideal ae (fRM N) (· = ((h, sl), ot)) (liftK (getH >>= _)) (getH >>= _) _
    rw [liftK_bind]
    refine JM.readK fun σ0 h0 => ?_
    subst h0
    simp only [fRM]
    have hi0 : ¬ i ≤ 0 := by omega
    by_cases hcmp : h.isCompromised i = true
    · have h1 : kind (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp)) (fixHM N ot h) i =
          .real := by simp [kind, hcmp]
      have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) h i = .real := by
        simp [multiKind, hcmp]
      rw [h1, h2]
      dsimp only
      rw [fixHM_getElem?_of ot h (i - 1) (Or.inr (by rw [show i - 1 + 1 = i by omega]; exact hcmp))]
      exact hpure _
    · simp only [Bool.not_eq_true] at hcmp
      by_cases hiN : i ≤ N
      · have h1 : kind (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp)) (fixHM N ot h) i =
            .real := by simp [kind, hcmp, hp, hi0]
        have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) h i =
            .special := by simp [multiKind, hcmp, hi0, hiN]
        rw [h1, h2]
        dsimp only
        rw [fixHM_getElem?_self ot h (i - 1) (by omega) (hk hiN hcmp)
          (by rw [show i - 1 + 1 = i by omega]; exact hcmp)]
        have hb : (ot i).b = false := hc.b i
        have hne := hch hhint
        rintro σ' rfl
        rw [YM_lift, liftK_pure]
        rcases hslot : ot i with ⟨key, b, chal⟩
        rw [hslot] at hb hne
        dsimp only at hb hne
        subst hb
        have hupd : Function.update ot i ({ key := key, b := false, chal := chal } : IndexedOtccaState MK AD C) = ot := by
          rw [← hslot, Function.update_eq_self]
        simp [otOpsWith, slotLift, slotLiftOtcca, otImpl, hslot, AEADScheme.otccaDecrypt,
          hne, hupd, show i - 1 + 1 = i by omega]
        exact DEq.refl _
      · have h1 : kind (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp)) (fixHM N ot h) i =
            .real := by simp [kind, hcmp, hp, hi0]
        have h2 : multiKind 0 N (some (otOpsWith (AD := AD) (M := M) (C := C) ideal)) h i =
            .real := by simp [multiKind, hcmp, hi0, hiN]
        rw [h1, h2]
        dsimp only
        rw [fixHM_getElem?_of ot h (i - 1) (Or.inl (by omega))]
        exact hpure _

theorem jmr_modify' (g : HS → HS) (σ : JStM CK MK AD M C) (hk : ∀ h, (g h).keys = h.keys)
    (hfc : ∀ k < N, k < σ.1.1.keys.length → (g σ.1.1).isCompromised (k + 1) = σ.1.1.isCompromised (k + 1))
    (hg : ∀ ks, g { σ.1.1 with keys := ks } = { g σ.1.1 with keys := ks })
    {Q : Unit → JStM CK MK AD M C → Prop} (hQ : Q () ((g σ.1.1, σ.1.2), σ.2)) :
    JM ideal ae (fRM N) (· = σ) (liftK (modifyH g) : SPK Unit) (modifyH g : SO Unit) Q :=
  JM.modifyK g g (fun σ' e => by
    subst e
    simp only [fRM, hk]
    rw [fixHM_upd' _ _ g hk hfc hg])
    fun σ' e => e ▸ hQ

theorem jmr_modify (g : HS → HS) (σ : JStM CK MK AD M C) (hk : ∀ h, (g h).keys = h.keys)
    (hc : ∀ h, (g h).senderCorruptedAt = h.senderCorruptedAt)
    (hg : ∀ h ks, g { h with keys := ks } = { g h with keys := ks })
    {Q : Unit → JStM CK MK AD M C → Prop} (hQ : Q () ((g σ.1.1, σ.1.2), σ.2)) :
    JM ideal ae (fRM N) (· = σ) (liftK (modifyH g) : SPK Unit) (modifyH g : SO Unit) Q :=
  jmr_modify' ideal ae N g σ hk (fun _ _ _ => by simp [HState.isCompromised, hc]) (hg σ.1.1) hQ

theorem jmr_send (σ : JStM CK MK AD M C) (hc : CoreM N σ) (hl : LenInvM la σ)
    (he : σ.1.1.ended = false) (a : AD) (msg : M) (g : C → HS → HS)
    (hk : ∀ e h, (g e h).keys = h.keys)
    (hcor : ∀ e h, (g e h).senderCorruptedAt = h.senderCorruptedAt)
    (hg : ∀ e h ks, g e { h with keys := ks } = { g e h with keys := ks })
    (hF : ∀ e h, (g e h).lastSentIdx = σ.1.1.lastSentIdx + 1 ∧
      (g e h).inTransit = ⟨σ.1.1.lastSentIdx + 1, a, msg, (σ.1.1.lastSentIdx + 1, e)⟩ :: h.inTransit ∧
      (g e h).receiverIdx = h.receiverIdx ∧ (g e h).skipped = h.skipped ∧
      (g e h).ended = h.ended) :
    JM ideal ae (fRM N) (· = σ)
      (do
        genUpToK G (hp N 0 la) (DG G) (σ.1.1.lastSentIdx + 1)
        let e ← liftK (encIdxWith ideal ae (hp N 0 la) (none : Option (SpecialOps AD M C ProbComp))
          (σ.1.1.lastSentIdx + 1) a msg)
        liftK (modifyH (g e))
        pure (some (σ.1.1.lastSentIdx + 1, e)) : SPK (Option (ℕ × C)))
      (do
        genUpTo G (hp N 0 la) (DG G) (σ.1.1.lastSentIdx + 1)
        let e ← multiEncIdxWith ideal ae 0 N (some (otOpsWith ideal)) (σ.1.1.lastSentIdx + 1) a msg
        modifyH (g e)
        pure (some (σ.1.1.lastSentIdx + 1, e)) : SO (Option (ℕ × C)))
      fun _ σ' => InvM N la σ' := by
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  dsimp only at he hF ⊢
  refine JM.bind (jmr_genUpTo ideal ae G N la _ _ hc he) fun _ =>
    JM.ofExact fun σ1 ⟨hc1, hx1, hl1⟩ => ?_
  obtain ⟨⟨h1, sl1⟩, ot1⟩ := σ1
  obtain ⟨hot, hh1⟩ := hx1
  dsimp only at hot hh1 hl1 hc1
  subst hot
  obtain ⟨ks, rfl⟩ : ∃ ks, h1 = { h with keys := ks } := ⟨_, hh1⟩
  dsimp only at hl1
  refine JM.bind (jmr_encIdx ideal ae N la _ _ _ _ hc1 (by dsimp only; omega) rfl) fun e =>
    JM.ofExact fun σ2 ⟨h21, h22⟩ => ?_
  obtain ⟨⟨h2, sl2⟩, ot2⟩ := σ2
  dsimp only at h21 h22
  simp only [Prod.mk.injEq] at h21
  obtain ⟨rfl, rfl⟩ := h21
  refine JM.bind (jmr_modify ideal ae N (g e) _ (hk e) (hcor e) (hg e)
    (Q := fun _ σ' => InvM N la σ') ?_) fun _ => JM.pure _ fun _ h => h
  dsimp only
  obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := hF e { h with keys := ks }
  have hcor' := hcor e { h with keys := ks }
  have hk' := hk e { h with keys := ks }
  dsimp only at hF3 hF4 hF5 hcor' hk'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    rcases h22 with rfl | ⟨-, -, -, -, rfl⟩
    · exact hc.b j
    · by_cases hj : j = h.lastSentIdx + 1
      · subst hj; simp only [Function.update_self]; exact hc.b _
      · simp only [Function.update_of_ne hj]; exact hc.b j
  · exact hc1.noMat
  · intro hu
    dsimp only at hu ⊢
    rw [hcor']
    exact hc1.unk hu
  · intro x hx
    dsimp only at hx ⊢
    rw [hF4] at hx
    rw [hk']
    exact hc1.skip x hx
  · intro j
    dsimp only
    rw [hF1]
    rcases h22 with rfl | ⟨-, -, -, -, rfl⟩
    · intro hs
      have := hc.chalSent j hs
      dsimp only at this
      omega
    · by_cases hj : j = h.lastSentIdx + 1
      · subst hj; intro _; omega
      · simp only [Function.update_of_ne hj]
        intro hs
        have := hc.chalSent j hs
        dsimp only at this
        omega
  · intro r hr
    dsimp only at hr
    rw [hF2] at hr
    rcases List.mem_cons.1 hr with rfl | hr
    · rfl
    · exact hc.ct r hr
  · intro j i0 a' e' hch
    dsimp only at hch ⊢
    rw [hF2, hF3, hF4]
    rcases h22 with rfl | ⟨-, -, -, -, rfl⟩
    · obtain ⟨h0, hr⟩ := hc.chal j i0 a' e' hch
      refine ⟨h0, ?_⟩
      rcases hr with ⟨r, hr, h1, h2, h3⟩ | hr
      · exact Or.inl ⟨r, List.mem_cons_of_mem _ hr, h1, h2, h3⟩
      · exact Or.inr hr
    · by_cases hj : j = h.lastSentIdx + 1
      · subst hj
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hch
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hch
        exact ⟨rfl, Or.inl ⟨_, List.mem_cons_self .., rfl, rfl, rfl⟩⟩
      · simp only [Function.update_of_ne hj] at hch
        obtain ⟨h0, hr⟩ := hc.chal j i0 a' e' hch
        refine ⟨h0, ?_⟩
        rcases hr with ⟨r, hr, h1, h2, h3⟩ | hr
        · exact Or.inl ⟨r, List.mem_cons_of_mem _ hr, h1, h2, h3⟩
        · exact Or.inr hr
  · intro w e' k hkN hl'
    dsimp only at e' hl' ⊢
    rw [hk'] at hl'
    rw [isCompromised_congr hcor', hF5]
    exact hc1.seed w e' k hkN hl'
  · intro hn hla
    dsimp only at hn ⊢
    rw [hcor'] at hn
    rw [hk', hF1]
    have := hl.1 hn hla
    dsimp only at this
    omega
  · intro c hcs
    dsimp only at hcs ⊢
    rw [hcor'] at hcs
    rw [hk']
    have := hl.2 c hcs
    dsimp only at this
    omega

theorem jmr_transmitH (q : AD × M) :
    JM ideal ae (fRM N) (InvM N la)
      (transmitHWithK ideal ae G (hp N 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q)
      (multiTransmitHWith ideal ae G (hp N 0 la) N (DG G) (some (otOpsWith ideal)) q)
      fun _ => InvM N la := by
  unfold transmitHWithK multiTransmitHWith
  refine JM.readK fun σ ⟨hc, hl⟩ => ?_
  dsimp only [fRM, fixHM, hp]
  refine JM.ite _ (fun _ => JM.pure _ fun σ' e => e ▸ ⟨hc, hl⟩) fun he => ?_
  exact jmr_send ideal ae G N la σ hc hl (Bool.eq_false_iff.2 he) q.1 q.2 _
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem jmr_challengeH (q : AD × M × M) :
    JM ideal ae (fRM N) (InvM N la)
      (challengeHWithK ideal ae G (hp N 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q)
      (multiChallengeHWith ideal ae G (hp N 0 la) N (DG G) (some (otOpsWith ideal)) q)
      fun _ => InvM N la := by
  unfold challengeHWithK multiChallengeHWith
  refine JM.readK fun σ ⟨hc, hl⟩ => ?_
  dsimp only [fRM, fixHM, hp]
  refine JM.ite _ (fun _ => JM.pure _ fun σ' e => e ▸ ⟨hc, hl⟩) fun he => ?_
  have he' : σ.1.1.ended = false := (Bool.or_eq_false_iff.1 (Bool.eq_false_iff.2 he)).1
  exact jmr_send ideal ae G N la σ hc hl he' q.1 _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem jmr_receiveH (hint : Option M) (a : AD) (c : ℕ × C) (σ : JStM CK MK AD M C)
    (hc : CoreM N σ) (hl : LenInvM la σ) (he : σ.1.1.ended = false)
    (hnm : hint = none → ∀ r ∈ σ.1.1.inTransit, ¬(r.ad = a ∧ r.ct = c)) :
    JM ideal ae (fRM N) (· = σ)
      (receiveHK ae G maxSkip (hp N 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) hint a c)
      (multiReceiveH ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) hint a c)
      fun res σ' => InvM N la σ' ∧ ∀ i' m, res = some (i', m) → i' = c.1 ∧ c.1 ∉ σ'.1.1.skipped := by
  obtain ⟨i, e⟩ := c
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  dsimp only at he hnm ⊢
  unfold receiveHK multiReceiveH
  simp only [hp_la]
  refine JM.readK fun σ0 h0 => ?_
  subst h0
  dsimp only [fRM, fixHM, HState.isCompromised, hp]
  have hchal : (i ∈ h.skipped ∨ h.receiverIdx < i) → hint = none → (ot i).chal ≠ some ((i, a), e) := by
    intro hcase hn hce
    obtain ⟨h0, hr⟩ := hc.chal i _ _ _ hce
    rcases hr with ⟨r, hr, -, h2, h3⟩ | ⟨h1, h2⟩
    · exact hnm hn r hr ⟨h2, by rw [h3]⟩
    · dsimp only at h1 h2
      rcases hcase with hcase | hcase
      · exact h2 hcase
      · omega
  have hnone : ∀ σ', σ' = ((h, sl), ot) → InvM N la σ' ∧
      ∀ i' m, (none : Option (ℕ × M)) = some (i', m) → i' = i ∧ i ∉ σ'.1.1.skipped :=
    fun σ' e' => e' ▸ ⟨⟨hc, hl⟩, by simp⟩
  refine JM.ite _ (fun hs => ?_) fun hs => ?_
  · have hsm : i ∈ h.skipped := by simpa using hs
    have hsk := hc.skip i hsm
    dsimp only at hsk
    refine JM.bind (jmr_decIdx ideal ae N la hint i a e _ hc hsk.1 (hchal (Or.inl hsm))
      fun _ _ => by dsimp only; omega) fun r => ?_
    rcases r with _ | msg
    · exact JM.pure _ hnone
    · refine JM.bind (jmr_modify ideal ae N _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl)
        (Q := fun _ σ' => InvM N la σ' ∧ i ∉ σ'.1.1.skipped) ?_) fun _ =>
          JM.pure _ fun σ' ⟨h1, h2⟩ => ⟨h1, fun i' m hh => by
            simp only [Option.some.injEq, Prod.mk.injEq] at hh
            exact ⟨hh.1.symm, h2⟩⟩
      dsimp only
      refine ⟨⟨hc.ofEq rfl (fun x hx => Or.inl (List.mem_filter.1 hx).1) rfl rfl rfl
        hc.noMat hc.unk (fun w e' k hk' hl' => hc.seed w e' k hk' hl'),
        LenInvM.ofEq hl rfl rfl rfl⟩, by simp⟩
  · refine JM.ite _ (fun _ => JM.pure _ hnone) fun hw => ?_
    refine JM.ite _ (fun _ => JM.pure _ hnone) fun hg => ?_
    have hri : h.receiverIdx < i := by rcases not_or.1 hw with ⟨h1, -⟩; omega
    have hgi : h.senderCorruptedAt = none → la = false → i ≤ h.lastSentIdx := by
      intro hn hla
      simp only [HState.isCompromised, hp, hn, hla, Bool.not_false, Bool.true_and,
        Bool.and_true] at hg
      exact Nat.le_of_not_lt fun hlt => hg (decide_eq_true hlt)
    refine JM.bind (jmr_genUpTo ideal ae G N la i _ hc he) fun _ =>
      JM.ofExact fun σ1 ⟨hc1, hx1, hl1⟩ => ?_
    obtain ⟨⟨h1, sl1⟩, ot1⟩ := σ1
    obtain ⟨hot, hh1⟩ := hx1
    dsimp only at hot hh1 hl1 hc1
    subst ot1
    obtain ⟨ks, rfl⟩ : ∃ ks, h1 = { h with keys := ks } := ⟨_, hh1⟩
    dsimp only at hl1
    have hl1' : LenInvM la (({ h with keys := ks }, sl1), ot) := by
      refine ⟨fun hn hla => ?_, fun c hcs => ?_⟩
      · dsimp only at hn ⊢
        have h1 := hl.1 hn hla
        have h2 := hgi hn hla
        dsimp only at h1
        omega
      · dsimp only at hcs ⊢
        have := hl.2 c hcs
        dsimp only at this
        omega
    have hnone1 : ∀ σ', σ' = (({ h with keys := ks }, sl1), ot) → InvM N la σ' ∧
        ∀ i' m, (none : Option (ℕ × M)) = some (i', m) → i' = i ∧ i ∉ σ'.1.1.skipped :=
      fun σ' e' => e' ▸ ⟨⟨hc1, hl1'⟩, by simp⟩
    refine JM.bind (jmr_decIdx ideal ae N la hint i a e _ hc1 (by omega) (hchal (Or.inr hri))
      fun _ _ => by dsimp only; omega) fun r => ?_
    rcases r with _ | msg
    · exact JM.pure _ hnone1
    · refine JM.bind (jmr_modify ideal ae N _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl)
        (Q := fun _ σ' => InvM N la σ' ∧ i ∉ σ'.1.1.skipped) ?_) fun _ =>
          JM.pure _ fun σ' ⟨h1, h2⟩ => ⟨h1, fun i' m hh => by
            simp only [Option.some.injEq, Prod.mk.injEq] at hh
            exact ⟨hh.1.symm, h2⟩⟩
      dsimp only
      refine ⟨⟨hc1.ofEq rfl (fun x hx => ?_) rfl rfl rfl hc1.noMat hc1.unk
        (fun w e' k hk' hl' => hc1.seed w e' k hk' hl'), LenInvM.ofEq hl1' rfl rfl rfl⟩, fun hx => ?_⟩
      · rcases List.mem_append.1 hx with hx | hx
        · have := mem_newSkipped hx
          dsimp only
          exact Or.inr ⟨this.1, by omega⟩
        · exact Or.inl hx
      · rcases List.mem_append.1 hx with hx | hx
        · have := mem_newSkipped hx
          omega
        · exact hs (by simpa using hx)

theorem jmr_deliverH (q : AD × (ℕ × C)) :
    JM ideal ae (fRM N) (InvM N la)
      (deliverHK ae G maxSkip (hp N 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q)
      (multiDeliverH ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) q)
      fun _ => InvM N la := by
  unfold deliverHK multiDeliverH
  refine JM.readK fun σ ⟨hc, hl⟩ => ?_
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  dsimp only [fRM, fixHM, HState.isCompromised]
  refine JM.ite _ (fun _ => JM.pure _ fun σ' e => e ▸ ⟨hc, hl⟩) fun he => ?_
  have he' : h.ended = false := Bool.eq_false_iff.2 he
  cases hr : h.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
  | none => exact JM.pure _ fun σ' e => e ▸ ⟨hc, hl⟩
  | some r =>
    dsimp only
    have hmem := List.mem_of_find?_eq_some hr
    have hpr := List.find?_some hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hpr
    have hidx : r.idx = q.2.1 := by rw [← hc.ct r hmem, hpr.2]
    refine JM.bind (jmr_receiveH ideal ae G maxSkip N la (some r.msg) q.1 q.2 _ hc hl he'
      (by intro hn; cases hn))
      fun res => JM.ofExact fun σ' ⟨⟨hc', hl'⟩, hres⟩ => ?_
    obtain ⟨⟨h', sl'⟩, ot'⟩ := σ'
    rcases res with _ | ⟨i', m'⟩
    · exact JM.bind (jmr_modify ideal ae N _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl)
        (Q := fun _ => InvM N la) ⟨hc'.ofEq' rfl rfl rfl rfl rfl rfl id,
          LenInvM.ofEq hl' rfl rfl rfl⟩) fun _ => JM.pure _ fun _ h => h
    · obtain ⟨hi', hns⟩ := hres i' m' rfl
      dsimp only at hi' hns
      exact JM.bind (jmr_modify ideal ae N _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl)
        (Q := fun _ => InvM N la) ⟨hc'.recv r.idx rfl rfl rfl rfl id rfl (le_max_left _ _)
          ⟨by show r.idx ≤ max h'.receiverIdx i'; omega, by rw [hidx]; exact hns⟩,
          LenInvM.ofEq hl' rfl rfl rfl⟩) fun _ => JM.pure _ fun _ h => h

theorem jmr_injectH (q : AD × (ℕ × C)) :
    JM ideal ae (fRM N) (InvM N la)
      (injectHK ae G maxSkip (hp N 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) q)
      (multiInjectH ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) q)
      fun _ => InvM N la := by
  unfold injectHK multiInjectH
  simp only [hp_la]
  refine JM.readK fun σ ⟨hc, hl⟩ => ?_
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  dsimp only [fRM, fixHM, HState.isCompromised, hp]
  refine JM.ite _ (fun _ => JM.pure _ fun σ' e => e ▸ ⟨hc, hl⟩) fun hcond => ?_
  obtain ⟨he, hany⟩ := Bool.or_eq_false_iff.1 (Bool.eq_false_iff.2 hcond)
  have hnm : (none : Option M) = none → ∀ r ∈ h.inTransit, ¬(r.ad = q.1 ∧ r.ct = q.2) :=
    fun _ r hr ⟨h1, h2⟩ => by
      have := List.any_eq_false.1 hany r hr
      simp [h1, h2] at this
  refine JM.bind (jmr_receiveH ideal ae G maxSkip N la none q.1 q.2 _ hc hl he hnm)
    fun res => JM.ofExact fun σ' ⟨⟨hc', hl'⟩, hres⟩ => ?_
  obtain ⟨⟨h', sl'⟩, ot'⟩ := σ'
  rcases res with _ | ⟨i', m'⟩
  · exact JM.pure _ fun σ'' e => e ▸ ⟨hc', hl'⟩
  · obtain ⟨hi', hns⟩ := hres i' m' rfl
    dsimp only at hi' hns
    exact JM.bind (jmr_modify ideal ae N _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (Q := fun _ => InvM N la) ⟨hc'.recv i' rfl rfl rfl rfl
        (fun hh => by simp [HState.removeFromTransit, hh]) rfl (le_max_left _ _)
        ⟨by show i' ≤ max h'.receiverIdx i'; omega, by rw [hi']; exact hns⟩,
        LenInvM.ofEq hl' rfl rfl rfl⟩) fun _ => JM.pure _ fun _ h => h

theorem jmr_corruptSenderH (u : Unit) :
    JM ideal ae (fRM N) (InvM N la)
      (corruptSenderHK (AD := AD) (M := M) (C := C) (MK := MK) G (hp N 0 la) u)
      (corruptSenderH (m := OracleComp (IndexedOtccaSpec AD M C)) G (hp N 0 la) u)
      fun _ => InvM N la := by
  unfold corruptSenderHK corruptSenderH
  simp only [hp_la]
  refine JM.readK fun σ ⟨hc, hl⟩ => ?_
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  simp only [fRM, fixHM_ended, fixHM_senderCorruptedAt, fixHM_lastSentIdx, fixHM_corrKey]
  refine JM.ite _ (fun _ => JM.pure _ fun σ' e => e ▸ ⟨hc, hl⟩) fun he => ?_
  refine JM.ite _ (fun _ => JM.bind (jmr_modify ideal ae N _ _ (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (Q := fun _ => InvM N la) ⟨hc.ofEq' rfl rfl rfl rfl rfl rfl fun _ => rfl,
      LenInvM.ofEq hl rfl rfl rfl⟩) fun _ => JM.pure _ fun _ h => h) fun hla => ?_
  have hla' : la = false := by simpa using hla
  have hcb : ∀ c, (h.senderCorruptedAt.getD h.lastSentIdx) = c → c ≤ h.keys.length := by
    intro c hc'
    subst hc'
    cases hcs : h.senderCorruptedAt with
    | none =>
      have := hl.1 hcs hla'
      dsimp only at this
      simp only [Option.getD_none]
      omega
    | some c0 =>
      have := hl.2 c0 hcs
      dsimp only at this
      simp only [Option.getD_some]
      omega
  refine JM.bind (jmr_senderKey ideal ae G N _ hc) fun w =>
    JM.ofExact fun σ1 ⟨hot, hh, u0, hsl1⟩ => ?_
  obtain ⟨⟨h1, sl1⟩, ot1⟩ := σ1
  dsimp only at hot hh hsl1
  subst ot1 h1 hsl1
  refine JM.bind (jmr_modify' ideal ae N _ _ (by intros; rfl) ?_ (by intros; rfl)
    (Q := fun _ => InvM N la) ?_) fun _ => JM.pure _ fun _ h => h
  · intro k hkN hlt
    dsimp only at hlt ⊢
    cases hcs : h.senderCorruptedAt with
    | none =>
      have := hl.1 hcs hla'
      dsimp only at this
      simp [HState.isCompromised, hcs]
      omega
    | some c0 => simp [HState.isCompromised, hcs]
  · dsimp only
    refine ⟨hc.ofEq rfl (fun x hx => Or.inl hx) rfl rfl rfl (by simp) (by simp)
      (fun w' _ k hkN hl' => Or.inl ?_), ⟨fun hn => absurd hn (by simp),
        fun c hcs => ?_⟩⟩
    · have := hcb _ rfl
      dsimp only at hl' ⊢
      simp only [HState.isCompromised, decide_eq_true_eq]
      omega
    · dsimp only at hcs ⊢
      simp only [Option.some.injEq] at hcs
      exact hcb c hcs

theorem jmr_corruptReceiverH (u : Unit) :
    JM ideal ae (fRM N) (InvM N la)
      (corruptReceiverHK (AD := AD) (M := M) (C := C) (MK := MK) G (hp N 0 la) u)
      (corruptReceiverH (m := OracleComp (IndexedOtccaSpec AD M C)) G (hp N 0 la) u)
      fun _ => InvM N la := by
  unfold corruptReceiverHK corruptReceiverH
  simp only [hp_la]
  refine JM.readK fun σ ⟨hc, hl⟩ => ?_
  obtain ⟨⟨h, sl⟩, ot⟩ := σ
  simp only [fRM, fixHM_ended, fixHM_challengesInTransit, fixHM_inTransit, fixHM_isCompromised,
    fixHM_isCompromised']
  refine JM.ite _ (fun _ => JM.pure _ fun σ' e => e ▸ ⟨hc, hl⟩) fun he => ?_
  refine JM.ite _ (fun _ => JM.bind (jmr_modify ideal ae N _ _ (by intros; rfl) (by intros; rfl)
    (by intros; rfl) (Q := fun _ => InvM N la) ⟨hc.ofEq' rfl rfl rfl rfl rfl rfl fun _ => rfl,
      LenInvM.ofEq hl rfl rfl rfl⟩) fun _ => JM.pure _ fun _ h => h) fun hla => ?_
  refine JM.bind (jmr_senderKey ideal ae G N _ hc) fun w =>
    JM.ofExact fun σ1 ⟨hot, hh, u0, hsl1⟩ => ?_
  obtain ⟨⟨h1, sl1⟩, ot1⟩ := σ1
  dsimp only at hot hh hsl1
  subst ot1 h1 hsl1
  refine JM.readK fun σ2 h2 => ?_
  subst h2
  simp only [fRM, fixHM_senderCorruptedAt, fixHM_corrKey, fixHM_receiverIdx, fixHM_skipped,
    fixHM_isCompromised', fixHM_lastSentIdx]
  have hD : ((h.skipped.filter h.isCompromised).filterMap fun i =>
      ((fixHM N ot h).keys[i - 1]?).map (i, ·)) =
      (h.skipped.filter h.isCompromised).filterMap fun i => (h.keys[i - 1]?).map (i, ·) := by
    refine List.filterMap_congr fun i hi => ?_
    have hsk := hc.skip i (List.mem_filter.1 hi).1
    have hci := (List.mem_filter.1 hi).2
    dsimp only at hsk
    rw [fixHM_getElem?_of ot h (i - 1) (Or.inr ?_)]
    rw [show i - 1 + 1 = i by omega]
    exact hci
  rw [hD]
  exact JM.bind (jmr_modify ideal ae N _ _ (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (Q := fun _ => InvM N la) ⟨hc.ofEq rfl (fun x hx => Or.inl hx) rfl rfl rfl
      (by simp) (by simp) (fun _ _ _ _ _ => Or.inr rfl),
      LenInvM.ofEq hl rfl rfl rfl⟩) fun _ => JM.pure _ fun _ h => h

theorem jmr_impl
    (t : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M
      (ℕ × C)).Domain) :
    JM ideal ae (fRM N) (InvM N la)
      (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) (none : Option (SpecialOps AD M C ProbComp)) t)
      (multiImplWith ideal ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t)
      fun _ => InvM N la := by
  rcases t with n | ((((((q | q) | u) | u) | q) | q))
  · exact JM.sampleK _ fun _ _ h => h
  · exact jmr_transmitH ideal ae G N la q
  · exact jmr_challengeH ideal ae G N la q
  · exact jmr_corruptSenderH ideal ae G N la u
  · exact jmr_corruptReceiverH ideal ae G N la u
  · exact jmr_deliverH ideal ae G maxSkip N la q
  · exact jmr_injectH ideal ae G maxSkip N la q

end OraclesM

theorem invM_init (N : ℕ) (la : Bool) (b : Bool) (K₀ : MK) (ks : List MK) :
    InvM (CK := CK) (AD := AD) (M := M) (C := C) N la
      (hInit b .unknown, initOStM false K₀ ks) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i; simp [initOStM]
  · simp [hInit]
  · intro _; rfl
  · simp [hInit]
  · intro i h; simp [initOStM] at h
  · simp [hInit]
  · intro i i0 a e h; simp [initOStM] at h
  · simp [hInit]
  · intro _ _; rfl
  · intro c h; simp [hInit] at h

theorem fRM_init (b : Bool) (K₀ : MK) (ks : List MK) :
    fRM ks.length (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown,
      initOStM false K₀ ks) = (hInit b .unknown, some ks) := by
  simp [fRM, fixHM, fixKeys, fixKeysAux, hInit, remKeys_init]

theorem hOut_fRM (N : ℕ) (la : Bool) (a : Bool) (σ : JStM CK MK AD M C) :
    hOut la (a, (fRM N σ).1) = hOut la (a, σ.1) := by
  cases la <;> simp [hOut, fRM]

/-- Running `multiSlotOtccaReduction` against the multi-slot OT-CCA real world (`b = false`) matches `hRunWith ideal ae G maxSkip (hp N 0 la) (DG G) none A .unknown`. -/
theorem multiOtBranch_false_eq_hRunWith (N : ℕ) (la : Bool)
    (A : RatchetAdversary CK MK AD M C) :
    𝒟[multiOtBranch ideal ae false N (multiSlotOtccaReduction ideal ae G maxSkip N la A)] =
      𝒟[hRunWith ideal ae G maxSkip (hp N 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) A .unknown] := by
  refine DEq.evalDist_eq ?_
  refine DEq.trans ?_ (eagerKeys_deq_hRunWith ideal ae G maxSkip N la A)
  unfold multiOtBranch multiSlotOtccaReduction multiRunWith
  simp only [hp_la, simulateQ_bind, simulateQ_pure, slotLift,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, StateT.run_bind,
    StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind]
  have hsim : ∀ (K₀ : MK) (ks : List MK), ks ∈ support (sampleKeys N) → ∀ (b : Bool),
      DEq
        ((simulateQ (slotLift (otImpl ideal ae))
          ((simulateQ (multiImplWith ideal ae G maxSkip (hp N 0 la) N (DG G)
            (some (otOpsWith ideal))) A).run (hInit b .unknown))).run
            (initOStM false K₀ ks) >>= fun x => pure (hOut la x.1))
        ((simulateQ (implWithK ideal ae G maxSkip (hp N 0 la) (DG G) none) A).run
          (hInit b .unknown, some ks) >>= fun z => pure (hOut la (z.1, z.2.1))) := by
    intro K₀ ks hks b
    have hlen : ks.length = N := length_mem_support_sampleKeys hks
    have hJ := (JM.simulateQ (jmr_impl ideal ae G maxSkip N la) A
      (hInit b .unknown, initOStM false K₀ ks) (invM_init N la b K₀ ks)).1
    have hinit : fRM N (hInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) b .unknown,
        initOStM false K₀ ks) = (hInit b .unknown, some ks) := by
      rw [← hlen, fRM_init]
    rw [hinit] at hJ
    have hmap := DEq.map hJ.symm (fun z => hOut la (z.1, z.2.1))
    simpa only [YM, Functor.map_map, map_eq_bind_pure_comp, Function.comp_def,
      Function.comp_apply, bind_assoc, pure_bind, hOut_fRM] using hmap
  refine (DEq.bind_right ($ᵗ MK) fun K₀ =>
    DEq.bind_right_supp (sampleKeys N) fun ks hks =>
      DEq.bind_right ($ᵗ Bool) fun b => hsim K₀ ks hks b).trans ?_
  exact DEq.bind_const ($ᵗ MK) _

/-! ### Multi-slot query bounds -/

def multiOffRange (N : ℕ) : (IndexedOtccaSpec AD M C).Domain → Bool
  | .inl _ => false
  | .inr (.inl ⟨h, _⟩) => !decide (1 ≤ h.1 ∧ h.1 ≤ N)
  | .inr (.inr ⟨h, _⟩) => !decide (1 ≤ h.1 ∧ h.1 ≤ N)

def hybSlotOtcca {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    (k : ℕ) : QueryImpl (AEADScheme.otccaSpec (ℕ × AD) M C)
      (StateT ((ℕ → SL) × (ℕ → SR)) ProbComp)
  | .inl ⟨h, m⟩ =>
    if 1 ≤ h.1 ∧ h.1 ≤ k then
      StateT.mk fun s => (fun r => (r.1, (s.1, Function.update s.2 h.1 r.2))) <$>
        (implR (.inr (.inl ⟨h, m⟩))).run (s.2 h.1)
    else
      StateT.mk fun s => (fun r => (r.1, (Function.update s.1 h.1 r.2, s.2))) <$>
        (implL (.inr (.inl ⟨h, m⟩))).run (s.1 h.1)
  | .inr ⟨h, e⟩ =>
    if 1 ≤ h.1 ∧ h.1 ≤ k then
      StateT.mk fun s => (fun r => (r.1, (s.1, Function.update s.2 h.1 r.2))) <$>
        (implR (.inr (.inr ⟨h, e⟩))).run (s.2 h.1)
    else
      StateT.mk fun s => (fun r => (r.1, (Function.update s.1 h.1 r.2, s.2))) <$>
        (implL (.inr (.inr ⟨h, e⟩))).run (s.1 h.1)

/-- `k`-slot hybrid implementation of `IndexedOtccaSpec AD M C`, running `implR` on slots `1 ≤ i ≤ k` and `implL` elsewhere. -/
def hybSlot {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    (k : ℕ) : QueryImpl (IndexedOtccaSpec AD M C) (StateT ((ℕ → SL) × (ℕ → SR)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT ((ℕ → SL) × (ℕ → SR)) ProbComp)
    + hybSlotOtcca implL implR k

@[simp] theorem hybSlot_inl {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp)) (k n : ℕ) :
    hybSlot implL implR k (.inl n) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT ((ℕ → SL) × (ℕ → SR)) ProbComp) n :=
  rfl

@[simp] theorem hybSlot_inr {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp)) (k : ℕ)
    (q : (AEADScheme.otccaSpec (ℕ × AD) M C).Domain) :
    hybSlot implL implR k (.inr q) = hybSlotOtcca implL implR k q :=
  rfl

@[simp] theorem slotLift_inl {S : Type}
    (impl : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp)) (n : ℕ) :
    slotLift impl (.inl n) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (ℕ → S) ProbComp) n :=
  rfl

@[simp] theorem slotLift_inr {S : Type}
    (impl : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
    (q : (AEADScheme.otccaSpec (ℕ × AD) M C).Domain) :
    slotLift impl (.inr q) = slotLiftOtcca impl q :=
  rfl

theorem simulateQ_liftM_run_of_inl {S : Type}
    (impl : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
    (h_inl : ∀ n (s : S), (impl (.inl n)).run s =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, s))
    {β : Type} (p : ProbComp β) (s : S) :
    (simulateQ impl (liftM p : OracleComp (IndexedOtccaSpec AD M C) β)).run s =
      (fun a => (a, s)) <$> p := by
  have heq : impl = (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) +
      fun q => impl (.inr q) := by
    ext ⟨n | q⟩ s' <;> simp [h_inl]
  rw [heq]
  simp [QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

theorem hybSlot_zero {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    {α : Type} (oa : OracleComp (IndexedOtccaSpec AD M C) α)
    (sL : ℕ → SL) (sR : ℕ → SR) :
    (simulateQ (hybSlot implL implR 0) oa).run (sL, sR) =
      (fun z => (z.1, (z.2, sR))) <$> (simulateQ (slotLift implL) oa).run sL := by
  induction oa using OracleComp.inductionOn generalizing sL sR with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨h, m⟩ | ⟨h, e⟩
    · simp only [hybSlot_inl, slotLift_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u sL sR
    · have hcond : ¬ (1 ≤ h.1 ∧ h.1 ≤ 0) := by omega
      simp only [hybSlot_inr, hybSlotOtcca, slotLift_inr, slotLiftOtcca,
        hcond, ↓reduceIte, StateT.run_mk, bind_map_left, Function.comp_def,
        bind_assoc, pure_bind]
      congr 1; ext z
      exact ih z.1 (Function.update sL h.1 z.2) sR
    · have hcond : ¬ (1 ≤ h.1 ∧ h.1 ≤ 0) := by omega
      simp only [hybSlot_inr, hybSlotOtcca, slotLift_inr, slotLiftOtcca,
        hcond, ↓reduceIte, StateT.run_mk, bind_map_left, Function.comp_def,
        bind_assoc, pure_bind]
      congr 1; ext z
      exact ih z.1 (Function.update sL h.1 z.2) sR

theorem hybSlot_eq_slotLift_of_offRange {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    (N : ℕ) {α : Type} (oa : OracleComp (IndexedOtccaSpec AD M C) α)
    (hoff : oa.IsQueryBoundP (fun t => multiOffRange N t = true) 0)
    (sL : ℕ → SL) (sR : ℕ → SR) :
    (simulateQ (hybSlot implL implR N) oa).run (sL, sR) =
      (fun z => (z.1, (sL, z.2))) <$> (simulateQ (slotLift implR) oa).run sR := by
  induction oa using OracleComp.inductionOn generalizing sL sR with
  | pure a => simp
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at hoff
    have hnp : ¬ (multiOffRange N t = true) := hoff.1.resolve_right (Nat.lt_irrefl 0)
    have hcont : ∀ u, (r u).IsQueryBoundP (fun t => multiOffRange N t = true) 0 :=
      fun u => by simpa [hnp] using hoff.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨h, m⟩ | ⟨h, e⟩
    · simp only [hybSlot_inl, slotLift_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u (hcont u) sL sR
    · have hcond : 1 ≤ h.1 ∧ h.1 ≤ N := by
        simp only [multiOffRange, Bool.not_eq_true', decide_eq_false_iff_not] at hnp
        omega
      simp only [hybSlot_inr, hybSlotOtcca, slotLift_inr, slotLiftOtcca,
        hcond, and_self, ↓reduceIte, StateT.run_mk, bind_map_left, Function.comp_def,
        bind_assoc, pure_bind]
      congr 1; ext z
      exact ih z.1 (hcont z.1) sL (Function.update sR h.1 z.2)
    · have hcond : 1 ≤ h.1 ∧ h.1 ≤ N := by
        simp only [multiOffRange, Bool.not_eq_true', decide_eq_false_iff_not] at hnp
        omega
      simp only [hybSlot_inr, hybSlotOtcca, slotLift_inr, slotLiftOtcca,
        hcond, and_self, ↓reduceIte, StateT.run_mk, bind_map_left, Function.comp_def,
        bind_assoc, pure_bind]
      congr 1; ext z
      exact ih z.1 (hcont z.1) sL (Function.update sR h.1 z.2)

theorem hybSlot_step_left {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    (hL_inl : ∀ n (s : SL), (implL (.inl n)).run s =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, s))
    (k : ℕ) {α : Type} (oa : OracleComp (IndexedOtccaSpec AD M C) α)
    (sL : ℕ → SL) (sR : ℕ → SR) (s_ext : SL) :
    (fun z => (z.1.1, (Function.update z.1.2.1 (k + 1) z.2, z.1.2.2))) <$>
      (simulateQ implL ((simulateQ (slotRedImpl implL implR k) oa).run (sL, sR))).run s_ext =
    (simulateQ (hybSlot implL implR k) oa).run (Function.update sL (k + 1) s_ext, sR) := by
  have hL_lift : ∀ {β : Type} (p : ProbComp β) (s : SL),
      (simulateQ implL (liftM p : OracleComp (IndexedOtccaSpec AD M C) β)).run s =
        (fun a => (a, s)) <$> p :=
    fun p s => simulateQ_liftM_run_of_inl (AD := AD) (M := M) (C := C) implL hL_inl p s
  induction oa using OracleComp.inductionOn generalizing sL sR s_ext with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨h, m⟩ | ⟨h, e⟩
    · simp only [slotRedImpl, hybSlot_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_lift, StateT.run_monadLift, monadLift_self,
        simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, hL_inl n s_ext, map_bind, bind_assoc, pure_bind,
        simulateQ_pure, StateT.run_pure]
      exact bind_congr fun u => ih u sL sR s_ext
    · by_cases heq : h.1 = k + 1
      · have hnot : ¬ (1 ≤ k + 1 ∧ k + 1 ≤ k) := by omega
        simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hnot,
          ↓reduceIte, StateT.run_lift, StateT.run_mk, simulateQ_bind, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
          Function.update_self, Function.update_idem, bind_map_left, map_bind,
          Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
        congr 1; ext z
        exact ih z.1 sL sR z.2
      · by_cases hle : 1 ≤ h.1 ∧ h.1 ≤ k
        · simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle,
            and_self, ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind, hL_lift,
            bind_map_left, map_bind, Functor.map_map, Function.comp_def, bind_assoc, pure_bind]
          congr 1; ext z
          exact ih z.1 sL (Function.update sR h.1 z.2) s_ext
        · simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle,
            ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind, hL_lift,
            Function.update_of_ne heq, bind_map_left, map_bind, Functor.map_map,
            Function.comp_def, bind_assoc, pure_bind]
          congr 1; ext z
          rw [Function.update_comm (Ne.symm heq)]
          exact ih z.1 (Function.update sL h.1 z.2) sR s_ext
    · by_cases heq : h.1 = k + 1
      · have hnot : ¬ (1 ≤ k + 1 ∧ k + 1 ≤ k) := by omega
        simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hnot,
          ↓reduceIte, StateT.run_lift, StateT.run_mk, simulateQ_bind, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
          Function.update_self, Function.update_idem, bind_map_left, map_bind,
          Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
        congr 1; ext z
        exact ih z.1 sL sR z.2
      · by_cases hle : 1 ≤ h.1 ∧ h.1 ≤ k
        · simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle,
            and_self, ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind, hL_lift,
            bind_map_left, map_bind, Functor.map_map, Function.comp_def, bind_assoc, pure_bind]
          congr 1; ext z
          exact ih z.1 sL (Function.update sR h.1 z.2) s_ext
        · simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle,
            ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind, hL_lift,
            Function.update_of_ne heq, bind_map_left, map_bind, Functor.map_map,
            Function.comp_def, bind_assoc, pure_bind]
          congr 1; ext z
          rw [Function.update_comm (Ne.symm heq)]
          exact ih z.1 (Function.update sL h.1 z.2) sR s_ext

theorem hybSlot_step_right {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    (hR_inl : ∀ n (s : SR), (implR (.inl n)).run s =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, s))
    (k : ℕ) {α : Type} (oa : OracleComp (IndexedOtccaSpec AD M C) α)
    (sL : ℕ → SL) (sR : ℕ → SR) (s_ext : SR) :
    (fun z => (z.1.1, (z.1.2.1, Function.update z.1.2.2 (k + 1) z.2))) <$>
      (simulateQ implR ((simulateQ (slotRedImpl implL implR k) oa).run (sL, sR))).run s_ext =
    (simulateQ (hybSlot implL implR (k + 1)) oa).run (sL, Function.update sR (k + 1) s_ext) := by
  have hR_lift : ∀ {β : Type} (p : ProbComp β) (s : SR),
      (simulateQ implR (liftM p : OracleComp (IndexedOtccaSpec AD M C) β)).run s =
        (fun a => (a, s)) <$> p :=
    fun p s => simulateQ_liftM_run_of_inl (AD := AD) (M := M) (C := C) implR hR_inl p s
  induction oa using OracleComp.inductionOn generalizing sL sR s_ext with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | ⟨h, m⟩ | ⟨h, e⟩
    · simp only [slotRedImpl, hybSlot_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_lift, StateT.run_monadLift, monadLift_self,
        simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, hR_inl n s_ext, map_bind, bind_assoc, pure_bind,
        simulateQ_pure, StateT.run_pure]
      exact bind_congr fun u => ih u sL sR s_ext
    · by_cases heq : h.1 = k + 1
      · have hle1 : 1 ≤ k + 1 ∧ k + 1 ≤ k + 1 := by omega
        simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle1,
          and_self, ↓reduceIte, StateT.run_lift, StateT.run_mk, simulateQ_bind, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
          Function.update_self, Function.update_idem, bind_map_left, map_bind,
          Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
        congr 1; ext z
        exact ih z.1 sL sR z.2
      · by_cases hle : 1 ≤ h.1 ∧ h.1 ≤ k
        · have hle1 : 1 ≤ h.1 ∧ h.1 ≤ k + 1 := by omega
          simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle, hle1,
            and_self, ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind, hR_lift,
            Function.update_of_ne heq, bind_map_left, map_bind, Functor.map_map,
            Function.comp_def, bind_assoc, pure_bind]
          congr 1; ext z
          rw [Function.update_comm (Ne.symm heq)]
          exact ih z.1 sL (Function.update sR h.1 z.2) s_ext
        · have hle1 : ¬ (1 ≤ h.1 ∧ h.1 ≤ k + 1) := by omega
          simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle, hle1,
            ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind, hR_lift,
            bind_map_left, map_bind, Functor.map_map, Function.comp_def, bind_assoc, pure_bind]
          congr 1; ext z
          exact ih z.1 (Function.update sL h.1 z.2) sR s_ext
    · by_cases heq : h.1 = k + 1
      · have hle1 : 1 ≤ k + 1 ∧ k + 1 ≤ k + 1 := by omega
        simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle1,
          and_self, ↓reduceIte, StateT.run_lift, StateT.run_mk, simulateQ_bind, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
          Function.update_self, Function.update_idem, bind_map_left, map_bind,
          Function.comp_def, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
        congr 1; ext z
        exact ih z.1 sL sR z.2
      · by_cases hle : 1 ≤ h.1 ∧ h.1 ≤ k
        · have hle1 : 1 ≤ h.1 ∧ h.1 ≤ k + 1 := by omega
          simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle, hle1,
            and_self, ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind, hR_lift,
            Function.update_of_ne heq, bind_map_left, map_bind, Functor.map_map,
            Function.comp_def, bind_assoc, pure_bind]
          congr 1; ext z
          rw [Function.update_comm (Ne.symm heq)]
          exact ih z.1 sL (Function.update sR h.1 z.2) s_ext
        · have hle1 : ¬ (1 ≤ h.1 ∧ h.1 ≤ k + 1) := by omega
          simp only [slotRedImpl, hybSlot_inr, hybSlotOtcca, heq, hle, hle1,
            ↓reduceIte, StateT.run_mk, simulateQ_bind, StateT.run_bind, hR_lift,
            bind_map_left, map_bind, Functor.map_map, Function.comp_def, bind_assoc, pure_bind]
          congr 1; ext z
          exact ih z.1 (Function.update sL h.1 z.2) sR s_ext

theorem slotRedImpl_isQueryBoundP {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    (k : ℕ) {Q : (IndexedOtccaSpec AD M C).Domain → Prop} [DecidablePred Q]
    (hQu : ∀ u, ¬ Q (.inl u)) {α : Type} (oa : OracleComp (IndexedOtccaSpec AD M C) α)
    (s : (ℕ → SL) × (ℕ → SR)) {n : ℕ} (hn : oa.IsQueryBoundP Q n) :
    ((simulateQ (slotRedImpl implL implR k) oa).run s).IsQueryBoundP Q n := by
  refine IsQueryBoundP.simulateQ_run_of_step hn (fun t ht s => ?_) (fun t ht s => ?_) s
  · rcases t with u | ⟨h, m⟩ | ⟨h, e⟩
    · exact absurd ht (hQu u)
    · dsimp only [slotRedImpl]
      split_ifs with heq hle
      · rw [StateT.run_lift]
        exact (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · exact (isQueryBoundP_liftProb hQu _).mono (Nat.zero_le 1)
      · exact (isQueryBoundP_liftProb hQu _).mono (Nat.zero_le 1)
    · dsimp only [slotRedImpl]
      split_ifs with heq hle
      · rw [StateT.run_lift]
        exact (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · exact (isQueryBoundP_liftProb hQu _).mono (Nat.zero_le 1)
      · exact (isQueryBoundP_liftProb hQu _).mono (Nat.zero_le 1)
  · rcases t with u | ⟨h, m⟩ | ⟨h, e⟩
    · dsimp only [slotRedImpl]
      rw [StateT.run_lift]
      exact (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inl (hQu u), fun _ => by simp⟩
    · dsimp only [slotRedImpl]
      split_ifs with heq hle
      · rw [StateT.run_lift]
        exact (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inl ht, fun _ => by simp⟩
      · exact isQueryBoundP_liftProb hQu _
      · exact isQueryBoundP_liftProb hQu _
    · dsimp only [slotRedImpl]
      split_ifs with heq hle
      · rw [StateT.run_lift]
        exact (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inl ht, fun _ => by simp⟩
      · exact isQueryBoundP_liftProb hQu _
      · exact isQueryBoundP_liftProb hQu _

theorem slotRedImpl_zero_of_slot {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    (k : ℕ) {Q : (IndexedOtccaSpec AD M C).Domain → Prop} [DecidablePred Q]
    (hQu : ∀ u, ¬ Q (.inl u))
    (hQe : ∀ a m, ¬ Q (.inr (.inl ((k + 1, a), m))))
    (hQd : ∀ a e, ¬ Q (.inr (.inr ((k + 1, a), e))))
    {α : Type} (oa : OracleComp (IndexedOtccaSpec AD M C) α)
    (s : (ℕ → SL) × (ℕ → SR)) :
    ((simulateQ (slotRedImpl implL implR k) oa).run s).IsQueryBoundP Q 0 := by
  refine IsQueryBoundP.simulateQ_run_of_step (isQueryBoundP_false oa 0)
    (fun _ h => h.elim) (fun t _ s => ?_) s
  rcases t with u | ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, e⟩
  · dsimp only [slotRedImpl]
    rw [StateT.run_lift]
    exact (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inl (hQu u), fun _ => by simp⟩
  · dsimp only [slotRedImpl]
    split_ifs with heq hle
    · subst heq
      rw [StateT.run_lift]
      exact (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inl (hQe a m), fun _ => by simp⟩
    · exact isQueryBoundP_liftProb hQu _
    · exact isQueryBoundP_liftProb hQu _
  · dsimp only [slotRedImpl]
    split_ifs with heq hle
    · subst heq
      rw [StateT.run_lift]
      exact (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inl (hQd a e), fun _ => by simp⟩
    · exact isQueryBoundP_liftProb hQu _
    · exact isQueryBoundP_liftProb hQu _

theorem multiKind_special {m : Type → Type} {N : ℕ} {ops : Option (SpecialOps AD M C m)}
    {st : HState CK MK AD M C} {i : ℕ} (h : multiKind 0 N ops st i = .special) :
    1 ≤ i ∧ i ≤ N := by
  unfold multiKind at h
  split_ifs at h with h1 h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  have hnc : (!st.isCompromised i) = true := h2.2
  simp only [hnc, and_true] at h1
  exact ⟨by omega, h2.1.2⟩

section MultiQB

variable {Q : (RSpec AD M C).Domain → Prop} [DecidablePred Q] (hQu : ∀ u, ¬ Q (.inl u))
include hQu

theorem qb_multiEncIdx_at (N : ℕ) (i : ℕ) (a : AD) (msg : M)
    (hQe : 1 ≤ i → i ≤ N → ¬ Q (.inr (.inl ((i, a), msg)))) :
    QB Q (multiEncIdxWith ideal ae 0 N (some (otOpsWith ideal)) i a msg :
      RM CK MK AD M C C) 0 := by
  unfold multiEncIdxWith
  refine qb_bind0 qb_getH fun st => ?_
  split
  · exact qb_sampleH hQu _
  · rename_i heq hops
    obtain rfl := Option.some.inj hops
    obtain ⟨hi1, hiN⟩ := multiKind_special heq
    refine qb_liftOM _ ?_
    simp only [otOpsWith]
    refine (isQueryBoundP_query_bind_iff Q _ _ _).2 ⟨Or.inl (hQe hi1 hiN), fun r => ?_⟩
    cases r
    · simpa [hQe hi1 hiN] using isQueryBoundP_liftProb hQu (ideal (i, a))
    · simp
  · split
    · exact qb_pure _ _
    · exact qb_sampleH hQu _

omit hQu in
theorem qb_multiDecIdx_at (N : ℕ) (hint : Option M) (i : ℕ) (a : AD) (e : C)
    (hQd : hint = none → 1 ≤ i → i ≤ N → ¬ Q (.inr (.inr ((i, a), e)))) :
    QB Q (multiDecIdx ae 0 N (some (otOpsWith ideal)) hint i a e :
      RM CK MK AD M C (Option M)) 0 := by
  unfold multiDecIdx
  split
  · exact qb_pure _ _
  · refine qb_bind0 qb_getH fun st => ?_
    split
    · exact qb_pure _ _
    · rename_i heq hops
      obtain rfl := Option.some.inj hops
      obtain ⟨hi1, hiN⟩ := multiKind_special heq
      refine qb_liftOM _ ?_
      exact (isQueryBoundP_query_iff Q _ _).2 fun hQ => absurd hQ (hQd rfl hi1 hiN)
    · exact qb_pure _ _

omit hQu in
theorem qb_multiDecIdx (N : ℕ) (d : ℕ)
    (hQd : ∀ i a c, 1 ≤ i → i ≤ N → Q (.inr (.inr ((i, a), c))) → 0 < d)
    (hint : Option M) (i : ℕ) (a : AD) (e : C) :
    QB Q (multiDecIdx ae 0 N (some (otOpsWith ideal)) hint i a e :
      RM CK MK AD M C (Option M)) d := by
  unfold multiDecIdx
  split
  · exact qb_pure _ _
  · refine qb_bind0 qb_getH fun st => ?_
    split
    · exact qb_pure _ _
    · rename_i heq hops
      obtain rfl := Option.some.inj hops
      obtain ⟨hi1, hiN⟩ := multiKind_special heq
      refine qb_liftOM _ ?_
      exact (isQueryBoundP_query_iff Q _ _).2 (hQd i a e hi1 hiN)
    · exact qb_pure _ _

theorem qb_multiReceiveH_at (P : Params) (N : ℕ) (hP0 : P.t.getD 0 = 0)
    (D : ℕ → ProbComp (CK × MK)) (hint : Option M) (a : AD) (c : ℕ × C)
    (hQd : hint = none → 1 ≤ c.1 → c.1 ≤ N → ¬ Q (.inr (.inr ((c.1, a), c.2)))) :
    QB Q (multiReceiveH ae G maxSkip P N D (some (otOpsWith ideal)) hint a c :
      RM CK MK AD M C _) 0 := by
  rcases c with ⟨i, e⟩
  unfold multiReceiveH
  rw [hP0]
  refine qb_bind0 qb_getH fun st => ?_
  split_ifs
  · refine qb_bind_r (qb_multiDecIdx_at ideal ae N hint i a e hQd) fun r => ?_
    cases r
    · exact qb_pure _ _
    · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  · exact qb_pure _ _
  · exact qb_pure _ _
  · refine qb_bind0 (qb_genUpTo hQu G P D i) fun _ => ?_
    refine qb_bind_r (qb_multiDecIdx_at ideal ae N hint i a e hQd) fun r => ?_
    cases r
    · exact qb_pure _ _
    · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _

theorem qb_multiReceiveH (P : Params) (N : ℕ) (hP0 : P.t.getD 0 = 0)
    (D : ℕ → ProbComp (CK × MK)) (d : ℕ)
    (hQd : ∀ i a c, 1 ≤ i → i ≤ N → Q (.inr (.inr ((i, a), c))) → 0 < d)
    (hint : Option M) (a : AD) (c : ℕ × C) :
    QB Q (multiReceiveH ae G maxSkip P N D (some (otOpsWith ideal)) hint a c :
      RM CK MK AD M C _) d := by
  rcases c with ⟨i, e⟩
  unfold multiReceiveH
  rw [hP0]
  refine qb_bind0 qb_getH fun st => ?_
  split_ifs
  · refine qb_bind_r (qb_multiDecIdx ideal ae N d hQd hint i a e) fun r => ?_
    cases r
    · exact qb_pure _ _
    · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  · exact qb_pure _ _
  · exact qb_pure _ _
  · refine qb_bind0 (qb_genUpTo hQu G P D i) fun _ => ?_
    refine qb_bind_r (qb_multiDecIdx ideal ae N d hQd hint i a e) fun r => ?_
    cases r
    · exact qb_pure _ _
    · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _

theorem multiRedWith_zero_of_zero
    {P_A : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
      AD M (ℕ × C)).Domain → Prop} [DecidablePred P_A]
    (N : ℕ) (la : Bool) (A : RatchetAdversary CK MK AD M C)
    (hA : A.IsQueryBoundP P_A 0)
    (hQe_tx : ∀ a m, ¬ P_A (.inr (.inl (.inl (.inl (.inl (.inl (a, m))))))) →
      ∀ i, 1 ≤ i → i ≤ N → ¬ Q (.inr (.inl ((i, a), m))))
    (hQe_ch : ∀ a m₀ m₁, ¬ P_A (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁))))))) →
      ∀ i, 1 ≤ i → i ≤ N → ∀ m, ¬ Q (.inr (.inl ((i, a), m))))
    (hQd_inj : ∀ a i e, ¬ P_A (.inr (.inr (a, (i, e)))) →
      1 ≤ i → i ≤ N → ¬ Q (.inr (.inr ((i, a), e)))) :
    (multiSlotOtccaReduction ideal ae G maxSkip N la A).IsQueryBoundP Q 0 := by
  set P := hp N 0 la
  have hstep_np : ∀ t, ¬ P_A t → ∀ (s : HSt CK MK AD M C), IsQueryBoundP
      ((multiImplWith ideal ae G maxSkip P N (DG G) (some (otOpsWith ideal)) t).run s)
      Q 0 := by
    intro t hnp s
    rcases t with u | (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, i, e⟩)
    · exact qb_sampleH hQu _ s
    · change IsQueryBoundP
        ((multiTransmitHWith ideal ae G P N (DG G) (some (otOpsWith ideal)) (a, m)).run s) Q 0
      unfold multiTransmitHWith
      refine (qb_bind0 qb_getH fun st => ?_) s
      split_ifs
      · exact qb_pure _ _
      · refine qb_bind0 (qb_genUpTo hQu G P (DG G) _) fun _ => ?_
        refine qb_bind0 (qb_multiEncIdx_at ideal ae hQu N _ a m (hQe_tx a m hnp _)) fun _ => ?_
        exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
    · change IsQueryBoundP
        ((multiChallengeHWith ideal ae G P N (DG G) (some (otOpsWith ideal)) (a, m₀, m₁)).run s) Q 0
      unfold multiChallengeHWith
      refine (qb_bind0 qb_getH fun st => ?_) s
      split_ifs
      · exact qb_pure _ _
      all_goals
        refine qb_bind0 (qb_genUpTo hQu G P (DG G) _) fun _ => ?_
        refine qb_bind0 (qb_multiEncIdx_at ideal ae hQu N _ a _
          (fun h1 hN => hQe_ch a m₀ m₁ hnp _ h1 hN _)) fun _ => ?_
        exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
    · exact qb_corruptSenderH hQu G P u s
    · exact qb_corruptReceiverH hQu G P u s
    · change IsQueryBoundP
        ((multiDeliverH ae G maxSkip P N (DG G) (some (otOpsWith ideal)) (a, c)).run s) Q 0
      unfold multiDeliverH
      refine (qb_bind0 qb_getH fun st => ?_) s
      split_ifs
      · exact qb_pure _ _
      · split
        · exact qb_pure _ _
        · refine qb_bind_r (qb_multiReceiveH_at ideal ae G maxSkip hQu P N rfl (DG G) _ a c
            (fun h => nomatch h)) fun r => ?_
          cases r <;> exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
    · change IsQueryBoundP
        ((multiInjectH ae G maxSkip P N (DG G) (some (otOpsWith ideal)) (a, (i, e))).run s) Q 0
      unfold multiInjectH
      refine (qb_bind0 qb_getH fun st => ?_) s
      split_ifs
      · exact qb_pure _ _
      · refine qb_bind_r (qb_multiReceiveH_at ideal ae G maxSkip hQu P N rfl (DG G) none a (i, e)
          (fun _ => hQd_inj a i e hnp)) fun r => ?_
        cases r
        · exact qb_pure _ _
        · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  have hsim : ∀ {α : Type} (oa : OracleComp _ α) (hoa : oa.IsQueryBoundP P_A 0)
      (s : HSt CK MK AD M C), IsQueryBoundP
      ((simulateQ (multiImplWith ideal ae G maxSkip P N (DG G) (some (otOpsWith ideal))) oa).run s)
      Q 0 := by
    intro α oa hoa s
    induction oa using OracleComp.inductionOn generalizing s with
    | pure a => simp
    | query_bind t r ih =>
      rw [isQueryBoundP_query_bind_iff] at hoa
      have hnp : ¬ P_A t := hoa.1.resolve_right (Nat.lt_irrefl 0)
      have hcont : ∀ u, (r u).IsQueryBoundP P_A 0 := fun u => by simpa [hnp] using hoa.2 u
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      simpa using isQueryBoundP_bind (hstep_np t hnp s) fun z _ => ih z.1 (hcont z.1) z.2
  unfold multiSlotOtccaReduction multiRunWith
  simpa using isQueryBoundP_bind (isQueryBoundP_liftProb hQu _) fun b _ =>
    isQueryBoundP_bind (hsim A hA _) fun z _ => isQueryBoundP_pure Q _ 0

theorem multiRedWith_le_of_step
    {P_A : (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK)
      AD M (ℕ × C)).Domain → Prop} [DecidablePred P_A]
    (N : ℕ) (la : Bool) (A : RatchetAdversary CK MK AD M C)
    (qd : ℕ) (hqd : A.IsQueryBoundP P_A qd)
    (hQe : ∀ i a m, 1 ≤ i → i ≤ N → ¬ Q (.inr (.inl ((i, a), m))))
    (hP_inl : ∀ u, ¬ P_A (.inl u))
    (hP_tx : ∀ a m, ¬ P_A (.inr (.inl (.inl (.inl (.inl (.inl (a, m))))))))
    (hP_ch : ∀ a m₀ m₁, ¬ P_A (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁))))))))
    (hP_cs : ∀ u, ¬ P_A (.inr (.inl (.inl (.inl (.inr u))))))
    (hP_cr : ∀ u, ¬ P_A (.inr (.inl (.inl (.inr u)))))
    (hP_del : ∀ a c, P_A (.inr (.inl (.inr (a, c)))))
    (hP_inj : ∀ a c, P_A (.inr (.inr (a, c)))) :
    (multiSlotOtccaReduction ideal ae G maxSkip N la A).IsQueryBoundP Q qd := by
  set P := hp N 0 la
  have hsim : ∀ (s : HSt CK MK AD M C), IsQueryBoundP
      ((simulateQ (multiImplWith ideal ae G maxSkip P N (DG G) (some (otOpsWith ideal))) A).run s)
      Q qd := by
    intro s
    refine IsQueryBoundP.simulateQ_run_of_step hqd (fun t ht s => ?_) (fun t hnt s => ?_) s
    · rcases t with u | (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
      · exact absurd ht (hP_inl u)
      · exact absurd ht (hP_tx a m)
      · exact absurd ht (hP_ch a m₀ m₁)
      · exact absurd ht (hP_cs u)
      · exact absurd ht (hP_cr u)
      · change IsQueryBoundP
          ((multiDeliverH ae G maxSkip P N (DG G) (some (otOpsWith ideal)) (a, c)).run s) Q 1
        unfold multiDeliverH
        refine (qb_bind0 qb_getH fun st => ?_) s
        split_ifs
        · exact qb_pure _ _
        · split
          · exact qb_pure _ _
          · refine qb_bind_r (qb_multiReceiveH ideal ae G maxSkip hQu P N rfl (DG G) 1
              (fun _ _ _ _ _ _ => Nat.zero_lt_one) _ a c) fun r => ?_
            cases r <;> exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
      · change IsQueryBoundP
          ((multiInjectH ae G maxSkip P N (DG G) (some (otOpsWith ideal)) (a, c)).run s) Q 1
        unfold multiInjectH
        refine (qb_bind0 qb_getH fun st => ?_) s
        split_ifs
        · exact qb_pure _ _
        · refine qb_bind_r (qb_multiReceiveH ideal ae G maxSkip hQu P N rfl (DG G) 1
            (fun _ _ _ _ _ _ => Nat.zero_lt_one) none a c) fun r => ?_
          cases r
          · exact qb_pure _ _
          · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
    · rcases t with u | (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
      · exact qb_sampleH hQu _ s
      · change IsQueryBoundP
          ((multiTransmitHWith ideal ae G P N (DG G) (some (otOpsWith ideal)) (a, m)).run s) Q 0
        unfold multiTransmitHWith
        refine (qb_bind0 qb_getH fun st => ?_) s
        split_ifs
        · exact qb_pure _ _
        · refine qb_bind0 (qb_genUpTo hQu G P (DG G) _) fun _ => ?_
          refine qb_bind0 (qb_multiEncIdx_at ideal ae hQu N _ a m (hQe _ a m)) fun _ => ?_
          exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
      · change IsQueryBoundP
          ((multiChallengeHWith ideal ae G P N (DG G) (some (otOpsWith ideal)) (a, m₀, m₁)).run s) Q 0
        unfold multiChallengeHWith
        refine (qb_bind0 qb_getH fun st => ?_) s
        split_ifs
        · exact qb_pure _ _
        all_goals
          refine qb_bind0 (qb_genUpTo hQu G P (DG G) _) fun _ => ?_
          refine qb_bind0 (qb_multiEncIdx_at ideal ae hQu N _ a _ (hQe _ a _)) fun _ => ?_
          exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
      · exact qb_corruptSenderH hQu G P u s
      · exact qb_corruptReceiverH hQu G P u s
      · exact absurd (hP_del a c) hnt
      · exact absurd (hP_inj a c) hnt
  unfold multiSlotOtccaReduction multiRunWith
  simpa using isQueryBoundP_bind (isQueryBoundP_liftProb hQu _) fun b _ =>
    isQueryBoundP_bind (hsim _) fun z _ => isQueryBoundP_pure Q _ 0

end MultiQB

theorem multiRedWith_offRange (N : ℕ) (la : Bool) (A : RatchetAdversary CK MK AD M C) :
    (multiSlotOtccaReduction ideal ae G maxSkip N la A).IsQueryBoundP
      (fun t => multiOffRange N t = true) 0 :=
  multiRedWith_zero_of_zero ideal ae G maxSkip (fun u => by simp [multiOffRange]) N la A
    (isQueryBoundP_false A 0)
    (fun _ _ _ _ h1 hN => by simp [multiOffRange, h1, hN])
    (fun _ _ _ _ _ h1 hN _ => by simp [multiOffRange, h1, hN])
    (fun _ _ _ _ h1 hN => by simp [multiOffRange, h1, hN])

end MultiSlotOTCCA

theorem sum_range_hopIdx (f : ℕ → ℝ≥0∞) (maxSkip q : ℕ) :
    ∑ j ∈ Finset.range (slotCount maxSkip q), f (slotToHybridHopIndex q j) =
      ∑ k ∈ Finset.range q, f (2 * k) +
        ∑ k ∈ Finset.range (q + (maxSkip + 1)), f (2 * k + 1) := by
  unfold slotCount
  rw [Finset.sum_range_add, Finset.sum_range_add (fun k => f (2 * k + 1)) q (maxSkip + 1),
    ← add_assoc]
  congr 1
  · rw [← sum_range_two_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp [slotToHybridHopIndex, hj]
  · refine Finset.sum_congr rfl fun d _ => ?_
    have hlt : ¬ (2 * q + d < 2 * q) := by omega
    have hsub : 2 * q + d - q = q + d := by omega
    simp [slotToHybridHopIndex, hlt, hsub]

/-- Two-stage FS-AEAD bound for `fromAEADPRG` under restricted AEAD correctness (`AEADScheme.CorrectOn`), decomposing into `slotCount maxSkip q` chain-PRG hops at `t = 0` and two multi-slot OT-CCA experiments. -/
theorem theorem5With_on_multi (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip : ℕ) (ok : AD → Bool) (hae : ae.CorrectOn fun ia => ok ia.2)
    (ideal : ℕ × AD → ProbComp C) (A : RatchetAdversary CK MK AD M C) (q : ℕ)
    (hq : MakesAtMostQueries A q) (hA : EncADsOk ok A) :
    advantage (fromAEADPRG ae G maxSkip) A ≤
      2 * ∑ j ∈ Finset.range (slotCount maxSkip q),
        (G (slotToHybridHopIndex q j / 2)).prgAdvantage
          (cumulativeChainPrgReduction ideal ae G maxSkip (slotToHybridHopIndex q j) A) +
      2 * (𝒟[multiOtBranch ideal ae true q
            (multiSlotOtccaReduction ideal ae G maxSkip q false A)].boolDist
          𝒟[multiOtBranch ideal ae false q
            (multiSlotOtccaReduction ideal ae G maxSkip q false A)] +
        𝒟[multiOtBranch ideal ae true (q + (maxSkip + 1))
            (multiSlotOtccaReduction ideal ae G maxSkip (q + (maxSkip + 1)) true A)].boolDist
          𝒟[multiOtBranch ideal ae false (q + (maxSkip + 1))
            (multiSlotOtccaReduction ideal ae G maxSkip (q + (maxSkip + 1)) true A)]) := by
  set fP : ℕ → ℝ≥0∞ := fun j =>
    (G (j / 2)).prgAdvantage (cumulativeChainPrgReduction ideal ae G maxSkip j A)
  have hchain : ∀ (N : ℕ) (la : Bool),
      𝒟[hybridA ideal ae G maxSkip 0 la A].boolDist
        𝒟[hybridA ideal ae G maxSkip N la A] ≤
      (∑ k ∈ Finset.range N, fP (2 * k + la.toNat)) +
        𝒟[multiOtBranch ideal ae true N
            (multiSlotOtccaReduction ideal ae G maxSkip N la A)].boolDist
          𝒟[multiOtBranch ideal ae false N
            (multiSlotOtccaReduction ideal ae G maxSkip N la A)] := by
    intro N la
    refine (MeasureTheory.Measure.boolDist_triangle
      𝒟[hybridA ideal ae G maxSkip 0 la A]
      𝒟[hRunWith ideal ae G maxSkip (hp N 0 la) (DG G)
        (none : Option (SpecialOps AD M C ProbComp)) A .unknown]
      𝒟[hybridA ideal ae G maxSkip N la A]).trans ?_
    refine add_le_add (chain_prg_zero_le ideal ae G maxSkip A la N) ?_
    rw [← multiOtBranch_false_eq_hRunWith,
      ← multiOtBranch_true_eq_hybAWith,
      MeasureTheory.Measure.boolDist_comm]
  have hmain := hchain q false
  have hla := hchain (q + (maxSkip + 1)) true
  simp only [Bool.toNat_false, add_zero, Bool.toNat_true] at hmain hla
  rw [MeasureTheory.Measure.boolDist, Ends.final_main_idx ideal ae G maxSkip A q hq] at hmain
  rw [MeasureTheory.Measure.boolDist, Ends.final_la_idx ideal ae G maxSkip A q hq,
    ENNReal.absDiff_zero_right] at hla
  calc advantage (fromAEADPRG ae G maxSkip) A
      ≤ 2 * ENNReal.absDiff (𝒟[hybridA ideal ae G maxSkip 0 false A] {true}) (1 / 2) +
          2 * 𝒟[hybridA ideal ae G maxSkip 0 true A] {true} :=
        Thm5On.start_on ideal ae G maxSkip A ok hae hA
    _ ≤ 2 * ((∑ k ∈ Finset.range q, fP (2 * k)) +
          𝒟[multiOtBranch ideal ae true q
              (multiSlotOtccaReduction ideal ae G maxSkip q false A)].boolDist
            𝒟[multiOtBranch ideal ae false q
              (multiSlotOtccaReduction ideal ae G maxSkip q false A)]) +
        2 * ((∑ k ∈ Finset.range (q + (maxSkip + 1)), fP (2 * k + 1)) +
          𝒟[multiOtBranch ideal ae true (q + (maxSkip + 1))
              (multiSlotOtccaReduction ideal ae G maxSkip (q + (maxSkip + 1)) true A)].boolDist
            𝒟[multiOtBranch ideal ae false (q + (maxSkip + 1))
              (multiSlotOtccaReduction ideal ae G maxSkip (q + (maxSkip + 1)) true A)]) := by
        gcongr
    _ = _ := by
        rw [sum_range_hopIdx fP maxSkip q]
        ring

end CryptoGames.FSAEAD.Thm5

