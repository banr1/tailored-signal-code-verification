/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompI0Laws
export Symbolic.Swarm.CREF.TR (proj_inj_eq at?_append_of_lt at?_append_self at?_append_eq at?_append_eq_of_proj newIndices_nil_append newRandoms_append_aux newRandoms_append_rnd newRandoms_append_nonRnd Runs Runs.pure Runs.getEntry Runs.appendEntry Runs.guard Runs.genRand Runs.sendMessage Runs.storeLocalState Runs.getKey Runs.requireTracePredicate setupTr1 setupTr2 setupTr3 setupTr4 setupTr5 runs_registerIdentity_a not_isRegisteredB_setupTr1 runs_registerIdentity_b setupTr2_at?_9 setupTr3_at?_9 runs_genSignedPrekey runs_genPQPrekey runs_genOneTimePrekey newRandoms_setupTr1 newRandoms_setupTr2 newRandoms_setupTr3 newRandoms_setupTr4 newRandoms_setupTr5 runs_setupAct setupTrace_eq)
theorem setupRandoms_eq (r : Records) (hNe : r.alice ≠ r.bob) : setupRandoms r = if r.withOpk then [randTerm 0 32, randTerm 5 32, randTerm 10 32, randTerm 11 64, randTerm 16 64, randTerm 17 64, randTerm 22 32] else [randTerm 0 32, randTerm 5 32, randTerm 10 32, randTerm 11 64, randTerm 16 64, randTerm 17 64] := by
  rw [setupRandoms, setupTrace_eq r hNe]
  cases r.withOpk <;> simp only [Bool.false_eq_true, ↓reduceIte, newRandoms_setupTr4, newRandoms_setupTr5] <;> rfl
theorem setupSecret_0 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 0 = randTerm 0 32 := by rw [setupSecret, setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupSecret_1 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 1 = randTerm 5 32 := by rw [setupSecret, setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupSecret_2 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 2 = randTerm 10 32 := by rw [setupSecret, setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupSecret_4 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 4 = randTerm 16 64 := by rw [setupSecret, setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupPublic_2 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 2 = DY.DiffieHellman.dhPk (randTerm 5 32) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.setupPublic_2_bridge r hNe
theorem setupPublic_4 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 4 = DY.DiffieHellman.dhPk (randTerm 10 32) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.setupPublic_4_bridge r hNe
theorem setupPublic_6 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 6 = DY.PQKem.kemPk (randTerm 16 64) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.setupPublic_6_bridge r hNe
theorem memoInjGt_setupSecret {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {k : Nat} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hk : k < 32) (idx : Nat) : MemoInjGt i S g k (setupSecret r idx) := by
  have hk64 : k < 64 := by omega
  unfold setupSecret; rw [setupRandoms_eq r hwf.1]
  rcases idx with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | idx⟩⟩⟩⟩⟩⟩
  · cases r.withOpk <;> exact memoInjGt_setup_randTerm hcompat hwf hk (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp)
  · cases r.withOpk <;> exact memoInjGt_setup_randTerm hcompat hwf hk (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp)
  · cases r.withOpk <;> exact memoInjGt_setup_randTerm hcompat hwf hk (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp)
  · cases r.withOpk <;> exact memoInjGt_setup_randTerm hcompat hwf hk64 (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp)
  · cases r.withOpk <;> exact memoInjGt_setup_randTerm hcompat hwf hk64 (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp)
  · cases r.withOpk <;> exact memoInjGt_setup_randTerm hcompat hwf hk64 (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp)
  · cases hopk : r.withOpk
    · exact memoInjGt_randTerm (.inl rfl)
    · exact memoInjGt_setup_randTerm hcompat hwf hk (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp [hopk])
  · cases r.withOpk <;> exact memoInjGt_randTerm (.inl rfl)
@[simp] theorem length_append_entry {T : Type} [ExecTraceTypes.Has T] (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq tr x
theorem at?_append_eq_of_eq {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S] (tr : ExecTrace) (x : S) {i : Nat} (hi : i = tr.length) : ((tr.append x).at? i : Option T) = TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) := by
  subst hi; exact Symbolic.Swarm.CREF.at?_append_length tr x
local macro "at?_iniAliceStartTr_tac" : tactic =>
  `(tactic| (dsimp only [iniAliceStartTr]; repeat (rw [at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp [length_append_entry]; try omega)]; rfl))
theorem newIndices_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : newIndices tr (iniAliceStartTr tr a b o) = [tr.length, tr.length + 1, tr.length + 2, tr.length + 3, tr.length + 4, tr.length + 5, tr.length + 6, tr.length + 7, tr.length + 8] := by
  unfold newIndices
  have hlen : (iniAliceStartTr tr a b o).length = tr.length + 9 := by dsimp only [iniAliceStartTr]; simp only [length_append_entry]
  rw [hlen, Nat.add_sub_cancel_left]; simp [List.range', Nat.add_assoc]
theorem newRandoms_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : newRandoms tr (iniAliceStartTr tr a b o) = [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) 32, 32), (randTerm (tr.length + 2) 32, 32)] := by
  unfold newRandoms; rw [newIndices_iniAliceStartTr]
  have h0 : ((iniAliceStartTr tr a b o).at? tr.length : Option DY.Random.ExecEntryT) = some (RndE 32) := (by at?_iniAliceStartTr_tac); have h1 : ((iniAliceStartTr tr a b o).at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (RndE 32) := (by at?_iniAliceStartTr_tac); have h2 : ((iniAliceStartTr tr a b o).at? (tr.length + 2) : Option DY.Random.ExecEntryT) = some (RndE 32) := (by at?_iniAliceStartTr_tac); have h3 : ((iniAliceStartTr tr a b o).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := (by at?_iniAliceStartTr_tac); have h4 : ((iniAliceStartTr tr a b o).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := (by at?_iniAliceStartTr_tac); have h5 : ((iniAliceStartTr tr a b o).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := (by at?_iniAliceStartTr_tac); have h6 : ((iniAliceStartTr tr a b o).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := (by at?_iniAliceStartTr_tac); have h7 : ((iniAliceStartTr tr a b o).at? (tr.length + 7) : Option DY.Random.ExecEntryT) = none := (by at?_iniAliceStartTr_tac); have h8 : ((iniAliceStartTr tr a b o).at? (tr.length + 8) : Option DY.Random.ExecEntryT) = none := (by at?_iniAliceStartTr_tac)
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, RndE]
theorem getEventAt_pq_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : let tr' := iniAliceStartTr tr a b o; tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent tr.length = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 1) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 2) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 3) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 4) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 5) = some (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 6) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 7) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((iniAliceStartTr tr a b o).at? tr.length : Option PQXDHEntry) = none := (by at?_iniAliceStartTr_tac); have h1 : ((iniAliceStartTr tr a b o).at? (tr.length + 1) : Option PQXDHEntry) = none := (by at?_iniAliceStartTr_tac); have h2 : ((iniAliceStartTr tr a b o).at? (tr.length + 2) : Option PQXDHEntry) = none := (by at?_iniAliceStartTr_tac); have h3 : ((iniAliceStartTr tr a b o).at? (tr.length + 3) : Option PQXDHEntry) = none := (by at?_iniAliceStartTr_tac); have h4 : ((iniAliceStartTr tr a b o).at? (tr.length + 4) : Option PQXDHEntry) = none := (by at?_iniAliceStartTr_tac); have h5 : ((iniAliceStartTr tr a b o).at? (tr.length + 5) : Option PQXDHEntry) = some (PQEvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)) := (by at?_iniAliceStartTr_tac); have h6 : ((iniAliceStartTr tr a b o).at? (tr.length + 6) : Option PQXDHEntry) = none := (by at?_iniAliceStartTr_tac); have h7 : ((iniAliceStartTr tr a b o).at? (tr.length + 7) : Option PQXDHEntry) = none := (by at?_iniAliceStartTr_tac); have h8 : ((iniAliceStartTr tr a b o).at? (tr.length + 8) : Option PQXDHEntry) = none := (by at?_iniAliceStartTr_tac)
  simp [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at?, h0, h1, h2, h3, h4, h5, h6, h7, h8, PQEvE]
theorem eventIdx_isAliceDone_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : eventIdx isAliceDone tr (iniAliceStartTr tr a b o) = some (tr.length + 5) := by unfold eventIdx; rw [newIndices_iniAliceStartTr]; obtain ⟨h0, h1, h2, h3, h4, h5, _, _, _⟩ := getEventAt_pq_iniAliceStartTr tr a b o; simp [h0, h1, h2, h3, h4, h5, isAliceDone]
theorem aliceVis_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hb : DY.Libsignal.PQXDH.BundleHandles) : aliceVis tr (iniAliceStartTr tr a b o) hb = { kind := .recv, terms := received tr ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList), layout := .bundle, anchor := none } :: rngEntry (randTerm tr.length 32) :: (kyberCoinEntries (randTerm (tr.length + 1) 32) ++ [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by simp [aliceVis, aliceDraws, newRandoms_iniAliceStartTr, eventIdx_isAliceDone_iniAliceStartTr]
theorem forall2_exists_left {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} (h : List.Forall₂ R as bs) {b : β} (hb : b ∈ bs) : ∃ a ∈ as, R a b := by
  induction h with
  | nil => cases hb
  | cons hhead _ ih =>
    rcases List.mem_cons.mp hb with rfl | hmem
    · exact ⟨_, List.mem_cons_self .., hhead⟩
    · obtain ⟨a, ha, hr⟩ := ih hmem; exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩
private theorem event_eq_rng_of_matches_rng {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ev : MachineEvent} {ts : List DY.Bytes} {lay : Layout} {anc : Option Nat} (hem : EventMatchesEntry i r S g ev { kind := .rng, terms := ts, layout := lay, anchor := anc }) : ∃ b : HwBytes, ev = .rng b := by have hk := hem.1; cases ev <;> simp [eventKind] at hk; exact ⟨_, rfl⟩
private theorem memoInjGt_randTerm_of_single_rng {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {k : Nat} {b : HwBytes} {ts sz : Nat} {anc : Option Nat} (hem : EventMatchesEntry i r S g (.rng b) { kind := .rng, terms := [randTerm ts sz], layout := .single, anchor := anc }) (hb : k < b.length) : MemoInjGt i S g k (randTerm ts sz) := by
  by_cases hsz : sz = 0
  · exact memoInjGt_randTerm (.inl hsz)
  · obtain ⟨_, hmap⟩ := hem; dsimp only [List.map, DY.Libsignal.Composed.Refinement.eventBytes] at hmap
    injection hmap with hγ; unfold gamma at hγ; rw [gamma'_randTerm i S g ts sz hsz] at hγ
    dsimp only at hγ; exact memoInjGt_randTerm (.inr (hγ.symm ▸ hb))
private theorem memoInjGt_randTerm_of_kyberCoin {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {k : Nat} {ev : MachineEvent} {ts j : Nat} {anc : Option Nat} (hk : k < 32) (hem : EventMatchesEntry i r S g ev { kind := .rng, terms := [randTerm ts 32], layout := .kyberCoin j, anchor := anc }) : MemoInjGt i S g k (randTerm ts 32) := by
  obtain ⟨_, _, t, ht, hlen, _⟩ := hem; injection ht with ht_eq; subst ht_eq; unfold gamma at hlen
  rw [gamma'_randTerm i S g ts 32 (by decide)] at hlen; dsimp only at hlen; exact memoInjGt_randTerm (.inr (hlen.symm ▸ hk))
private theorem forall2_append_drop_exists_left {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys zs : List β}, List.Forall₂ R xs (ys ++ zs) → ∀ z ∈ zs, ∃ x ∈ xs.drop ys.length, R x z
  | _, [], _, h, _, hz => forall2_exists_left h hz
  | _ :: _, _ :: _, _, .cons _ h, _, hz => forall2_append_drop_exists_left h _ hz
private theorem kyberCoinEntries_length (t : DY.Bytes) : (kyberCoinEntries t).length = 32 := by unfold kyberCoinEntries; simp
theorem memoInjGt_draws_of_aliceVis {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {k : Nat} {tr₁ : ExecTrace} {a b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {hb : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} (hk : k < 32) (hm₀ : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a b o) hb)) (hrs_ek : ∀ b : HwBytes, .rng b ∈ rs.take 1 → k < b.length) (hrs_dhs : ∀ b : HwBytes, .rng b ∈ rs.drop 33 → k < b.length) : MemoInjGt i S g k (randTerm tr₁.length 32) ∧ MemoInjGt i S g k (randTerm (tr₁.length + 1) 32) ∧ MemoInjGt i S g k (randTerm (tr₁.length + 2) 32) := by
  rw [aliceVis_iniAliceStartTr] at hm₀
  cases hm₀ with
  | cons _ hm₁ =>
    cases hm₁ with
    | cons hem_ek hm_rest =>
      rename_i ev_ek rs_tail; obtain ⟨b_ek, rfl⟩ := event_eq_rng_of_matches_rng hem_ek; have hek := memoInjGt_randTerm_of_single_rng hem_ek (hrs_ek b_ek (by simp))
      have hmem_ent : ({ kind := .rng, terms := [randTerm (tr₁.length + 1) 32], layout := .kyberCoin 0, anchor := none } : VisEntry) ∈
          kyberCoinEntries (randTerm (tr₁.length + 1) 32) ++
            [{ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) }] := by
        refine List.mem_append_left _ ?_; unfold kyberCoinEntries; exact List.mem_map.mpr ⟨0, by decide, rfl⟩
      obtain ⟨_, _, hem_ent⟩ := forall2_exists_left hm_rest hmem_ent; have hent := memoInjGt_randTerm_of_kyberCoin hk hem_ent
      obtain ⟨ev_dhs, hev_dhs_mem, hem_dhs⟩ := forall2_append_drop_exists_left hm_rest
        ({ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } : VisEntry) (List.mem_singleton_self _)
      rw [kyberCoinEntries_length] at hev_dhs_mem; obtain ⟨b_dhs, rfl⟩ := event_eq_rng_of_matches_rng hem_dhs; exact ⟨hek, hent, memoInjGt_randTerm_of_single_rng hem_dhs (hrs_dhs b_dhs hev_dhs_mem)⟩
attribute [local irreducible] setupPublic setupSecret
theorem memoInjGt_iniAliceStartState_of_aliceVis {r : Records} {S : Sem} {g : Ghost} {k : Nat} {tr₁ : ExecTrace} {a : Participant} {ikA : DY.Bytes} {hb : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hk : k < 32) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb)) (hrs_ek : ∀ e ∈ rs.take 1, k < (Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, k < (Census443Defs.eventBytes e).length) : MemoInjGt compI0 S g k (Comparse.serialize (⟨a, iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  have hNe : r.alice ≠ r.bob := hwf.1; let o := iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none;
  obtain ⟨hek_draw, hent_draw, hdhs_draw⟩ := memoInjGt_draws_of_aliceVis hk hm₀_vis
    (fun b hb => hrs_ek (.rng b) hb) (fun b hb => hrs_dhs (.rng b) hb)
  have hsec := memoInjGt_setupSecret hcompat hwf hk
  have hikA_gt : MemoInjGt compI0 S g k ikA := by rcases hid with rfl | rfl; exacts [hsec 0, hsec 1]
  have hikA_pk : MemoInjGt compI0 S g k o.ikA := memoInjGt_dhPk_compI0 hk hikA_gt; have hikB_pk : MemoInjGt compI0 S g k o.ikB := (by change MemoInjGt compI0 S g k (setupPublic r 2); rw [setupPublic_2 hNe, ← setupSecret_1 hNe]; exact memoInjGt_dhPk_compI0 hk (hsec 1)); have hspk_pk : MemoInjGt compI0 S g k o.spk := (by change MemoInjGt compI0 S g k (setupPublic r 4); rw [setupPublic_4 hNe, ← setupSecret_2 hNe]; exact memoInjGt_dhPk_compI0 hk (hsec 2)); have hspk_key : MemoInjGt compI0 S g k (DY.X25519.x25519Key o.spk) := (by change MemoInjGt compI0 S g k (DY.X25519.normalizeX25519Key (setupPublic r 4)); rw [setupPublic_4 hNe, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq, ← setupSecret_2 hNe]; exact memoInjGt_dhPk_compI0 hk (hsec 2)); have hikB_key : MemoInjGt compI0 S g k (DY.X25519.x25519Key (setupPublic r 2)) := (by change MemoInjGt compI0 S g k (DY.X25519.normalizeX25519Key (setupPublic r 2)); rw [setupPublic_2 hNe, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq, ← setupSecret_1 hNe]; exact memoInjGt_dhPk_compI0 hk (hsec 1))
  have hpq_pk : MemoInjGt compI0 S g k (setupPublic r 6) := by rw [setupPublic_6 hNe, ← setupSecret_4 hNe]; exact memoInjGt_kemPk (hsec 4)
  have hkdf := memoInjGt_pqxdhKdf_none hk (memoInjGt_dh_compI0 hk hspk_key hikA_gt)
    (memoInjGt_dh_compI0 hk hikB_key hek_draw) (memoInjGt_dh_compI0 hk hspk_key hek_draw)
    (memoInjGt_kemEncap_snd_compI0 hk hpq_pk hent_draw)
  exact memoInjGt_iniAliceStartState tr₁ a r.bob o hk hikA_pk hikB_pk hspk_pk hspk_key hkdf.1 hkdf.2.1 hkdf.2.2 hdhs_draw
def IniPrefixStateSecretsInv (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (bun : HwBytes) (rs : List MachineEvent) : Prop := (∀ j : Nat, ∀ e : PQXDHStEntry, ((runTraceMoves r ms).at? j : Option PQXDHStEntry) = some e → e.st.state.sk = setupSecret r 0 ∨ e.st.state.sk = setupSecret r 1 ∨ e.st.state.sk = setupSecret r 2 ∨ e.st.state.sk = setupSecret r 4 ∨ (r.withOpk = true ∧ e.st.state.sk = randTerm 22 32)) ∧ (∀ ls ∈ storedStates r (runTraceMoves r ms), ∃ (tr₁ : ExecTrace) (a : Participant) (ikA : DY.Bytes) (hb : DY.Libsignal.PQXDH.BundleHandles), (ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb) ∧ ls = ⟨a, iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)⟩)
theorem memoInjGt_storedSecrets_of_inv {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {k : Nat} {tr : ExecTrace} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hk : k < 32) (hsec : ∀ j : Nat, ∀ e : PQXDHStEntry, (tr.at? j : Option PQXDHStEntry) = some e → e.st.state.sk = setupSecret r 0 ∨ e.st.state.sk = setupSecret r 1 ∨ e.st.state.sk = setupSecret r 2 ∨ e.st.state.sk = setupSecret r 4 ∨ (r.withOpk = true ∧ e.st.state.sk = randTerm 22 32)) : ∀ u ∈ storedSecrets tr, MemoInjGt i S g k u := by
  intro u hu; unfold storedSecrets DY.ExecTrace.getLocalStateAt at hu; simp only [Option.map_map, Function.comp_def, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hu; obtain ⟨j, _, e, hat, rfl⟩ := hu; refine memoInjGt_serialize_local_pqxdh ?_
  rcases hsec j e hat with h0 | h1 | h2 | h4 | ⟨hopk, h22⟩
  · rw [h0]; exact memoInjGt_setupSecret hcompat hwf hk 0
  · rw [h1]; exact memoInjGt_setupSecret hcompat hwf hk 1
  · rw [h2]; exact memoInjGt_setupSecret hcompat hwf hk 2
  · rw [h4]; exact memoInjGt_setupSecret hcompat hwf hk 4
  · rw [h22]; exact memoInjGt_setup_randTerm hcompat hwf hk (by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; simp [hopk])
theorem memoInjGt_prefixTerms_of_matchedPrefix_ini_of {r : Records} {S : Sem} {who : List Participant} {g : Ghost} {k : Nat} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} (hwf : RecordsWF r) (hmp : MatchedPrefix compI0 r S who g ms (.recv bun :: rs)) (hinv : IniPrefixStateSecretsInv r S g ms bun rs) (hk : k < 32) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) (hrs_ek : ∀ e ∈ rs.take 1, k < (Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, k < (Census443Defs.eventBytes e).length) : ∀ u ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), MemoInjGt compI0 S g k u := by
  have hcompat : Compat compI0 r S g := hmp.1; refine memoInjGt_prefixTerms ?_ ?_ (memoInjGt_storedSecrets_of_inv hcompat hwf hk hinv.1) ?_
  · intro v hv hv_kind; obtain ⟨e, he, hem⟩ := forall2_exists_left hmp.2.2.2.2.2 hv; have he_kind : eventKind e = .send := hem.1.trans hv_kind
    rcases List.mem_cons.mp he with rfl | hrs_mem <;> [cases he_kind; (rw [hrs_kind e hrs_mem] at he_kind; cases he_kind)]
  · intro ls hls; obtain ⟨tr₁, a, ikA, hb, hid, hm₀_vis, rfl⟩ := hinv.2 ls hls; exact memoInjGt_iniAliceStartState_of_aliceVis hcompat hwf hk hid hm₀_vis hrs_ek hrs_dhs
  · intro v hv hv_kind; obtain ⟨e, he, hem⟩ := forall2_exists_left hmp.2.2.2.2.2 hv; have he_kind : eventKind e = .pt := hem.1.trans hv_kind
    rcases List.mem_cons.mp he with rfl | hrs_mem <;> [cases he_kind; (rw [hrs_kind e hrs_mem] at he_kind; cases he_kind)]
end Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
