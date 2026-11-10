/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.COMPOSED.CompInv
public import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.Swarm.CREF Symbolic.Swarm.CREF.TR Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation)
private theorem evAt_mono {Ev : Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT Ev)] {tr tr' : ExecTrace} (hle : tr ≤ tr') {ev : Ev} {i : Nat} (h : tr.EventLoggedAt ev i) : tr'.EventLoggedAt ev i := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at?] at h ⊢
  exact at?_le_some hle h
theorem eventLoggedAt_of_noSessionEffect {tr : ExecTrace} {m : Move} (h : NoSessionEffect tr m) {ev : DY.Libsignal.PQXDH.PQXDHEvent} {j : Nat} (hb : Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.isBreakPQEv ev = false := by rfl) : (m.next tr).EventLoggedAt ev j ↔ tr.EventLoggedAt ev j := by
  refine ⟨fun hev => ?_, evAt_mono ((Move.act m).run tr).2.property⟩
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at?] at hev ⊢
  have hjlt : j < (m.next tr).length := Symbolic.Swarm.CREF.XplSteps.xlt_of_at?_some hev
  by_cases hj : j < tr.length
  · have hle : tr ≤ m.next tr := ((Move.act m).run tr).2.property
    have hat : ((m.next tr).at? j : Option (ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = tr.at? j := Symbolic.Swarm.CREF.XplSteps.xat?_le_eq hle hj
    rwa [← hat]
  · have hnone := (h j (by simp only [newIndices, List.mem_range'_1]; omega)).2.1
    have hb' := hnone ⟨ev⟩ hev; rw [hb] at hb'; cases hb'
theorem eventLoggedAt_of_movesFrom_noSessionEffect {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom NoSessionEffect tr δ) {ev : DY.Libsignal.PQXDH.PQXDHEvent} {j : Nat} (hb : Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.isBreakPQEv ev = false := by rfl) : (runMoves δ tr).1.EventLoggedAt ev j ↔ tr.EventLoggedAt ev j := by
  induction δ generalizing tr with
  | nil => rfl
  | cons m δ ih => simp only [runMoves]; rw [ih hδ.2, eventLoggedAt_of_noSessionEffect (hb := hb) hδ.1]
theorem eventLoggedAt_of_movesFrom_invisibleNoEffect {tr : ExecTrace} {δ : List Move} (hδ : MovesFrom InvisibleNoEffect tr δ) {ev : DY.Libsignal.PQXDH.PQXDHEvent} {j : Nat} (hb : Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.isBreakPQEv ev = false := by rfl) : (runMoves δ tr).1.EventLoggedAt ev j ↔ tr.EventLoggedAt ev j :=
  eventLoggedAt_of_movesFrom_noSessionEffect (hb := hb) (movesFrom_mono (fun _ _ h => h.2) tr δ hδ)
open XplSteps in
private theorem leak_next_eq_of_exposures_nil {m : Move} {tr : ExecTrace} (hk : LeakKind m) (hex : exposures tr (m.next tr) = []) : m.next tr = tr ∨ (∃ t : DY.Bytes, m.next tr = tr.append (⟨t⟩ : Network.ExecEntryT)) ∨ (∃ ev : DY.Libsignal.PQXDH.PQXDHEvent, m.next tr = tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) :=
  (xpl_leak_shape hk tr).elim Or.inl (fun h => absurd hex (xpl_exposures_ne_nil h))
open XplSteps in
theorem next_of_isSetup_false_vis_nil {m : Move} {tr : ExecTrace} (hs : m.isSetup = false) (ha : m.Anchored tr) (hv : m.vis tr = []) : m.next tr = tr ∨ (∃ t : DY.Bytes, m.next tr = tr.append (⟨t⟩ : Network.ExecEntryT)) ∨ (∃ ev : DY.Libsignal.PQXDH.PQXDHEvent, m.next tr = tr.append (⟨ev⟩ : ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) := by
  rw [xpl_vis_eq, List.append_eq_nil_iff] at hv; obtain ⟨hown, hex⟩ := hv; cases m
  case setup => cases hs
  case aliceStart a b i j h shown =>
    obtain ⟨hsh, -⟩ := ha; obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩; simp [xpl_ownVis, aliceVis] at hown
  case bobStart b a kh i mh pq sp shown =>
    obtain ⟨hsh, -⟩ := ha; obtain ⟨k, rfl⟩ : ∃ k, shown = k + 1 := ⟨shown - 1, by omega⟩; simp [xpl_ownVis, bobVis] at hown
  case encrypt me si cl pq w =>
    rcases xpl_encrypt_next (me := me) (stateIdx := si) (coinsLen := cl) (pqIdx := pq) (w := w) tr with h | h
    · exact Or.inl h
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h; simp [xpl_ownVis, encVis, hx, encDraws] at hown
  case encryptAbort me si =>
    rcases xpl_encryptAbort_next (me := me) (stateIdx := si) tr with h | h
    · exact Or.inl h
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h; simp [xpl_ownVis, encVis, hx, encDraws] at hown
  case encryptFail me si cl =>
    rcases xpl_encryptFail_next (me := me) (stateIdx := si) (coinsLen := cl) tr with h | h
    · exact Or.inl h
    · obtain ⟨⟨m0, n0⟩, rest, hx⟩ := xpl_newRandoms_cons h; simp [xpl_ownVis, encVis, hx, encDraws] at hown
  case decrypt me si mi pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · exact Or.inl (xpl_decrypt_next hm)
    · simp [xpl_ownVis, decVis, hm] at hown
  case decryptSkipped me si mi k pq sp w =>
    rcases hm : tr.getMessageSentAt mi with _ | b
    · exact Or.inl (xpl_decryptSkipped_next hm)
    · simp [xpl_ownVis, decVis, hm] at hown
  case reject draws => simp [xpl_ownVis] at hown
  case attackerSend t =>
    refine Or.inr (Or.inl ⟨t, ?_⟩)
    unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit]
    exact (TR.Runs.sendMessage tr t).2
  case brkDH =>
    refine Or.inr (Or.inr ⟨.BrokenDH, ?_⟩)
    unfold Move.next Move.act DY.Libsignal.PQXDH.breakDH
    exact (TR.Runs.logEvent tr .BrokenDH).2
  case brkKEM =>
    refine Or.inr (Or.inr ⟨.BrokenKEM, ?_⟩)
    unfold Move.next Move.act DY.Libsignal.PQXDH.breakKEM
    exact (TR.Runs.logEvent tr .BrokenKEM).2
  all_goals exact leak_next_eq_of_exposures_nil trivial hex
abbrev at?_append_other_eq {E E' : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E'] := @CompPrefixInvAlice.at?_append_other_eq E E'
theorem pqxdhStoredAt_of_isSetup_false_vis_nil {m : Move} {tr : ExecTrace} (hs : m.isSetup = false) (ha : m.Anchored tr) (hv : m.vis tr = []) {p : Participant} {st : DY.Libsignal.PQXDH.PQXDHState} {j : Nat} : PQXDHStoredAt (m.next tr) p st j ↔ PQXDHStoredAt tr p st j := by
  unfold PQXDHStoredAt
  rcases next_of_isSetup_false_vis_nil hs ha hv with h | ⟨t, h⟩ | ⟨ev, h⟩
  · rw [h]
  · rw [h, at?_append_other_eq tr (⟨t⟩ : Network.ExecEntryT) rfl j]
  · rw [h, at?_append_other_eq tr (⟨ev⟩ : ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent) rfl j]
theorem pqxdhStoredAt_of_movesFrom_invisible {tr : ExecTrace} {δ : List Move} (hs : ∀ m ∈ δ, m.isSetup = false) (ha : MovesAnchored δ tr) (hδ : MovesFrom InvisibleNoEffect tr δ) {p : Participant} {st : DY.Libsignal.PQXDH.PQXDHState} {j : Nat} : PQXDHStoredAt (runMoves δ tr).1 p st j ↔ PQXDHStoredAt tr p st j := by
  induction δ generalizing tr with
  | nil => rfl
  | cons m δ ih =>
    simp only [runMoves]; rw [ih (fun m' hm' => hs m' (List.mem_cons_of_mem _ hm')) ha.2 hδ.2, pqxdhStoredAt_of_isSetup_false_vis_nil (hs m (List.mem_cons_self ..)) ha.1 hδ.1.1]
export Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy ( setupSecret_0 setupSecret_1 setupSecret_2 setupSecret_4 setupPublic_0 setupPublic_1 setupPublic_2 setupPublic_3 setupPublic_4 setupPublic_6 setupTrace_eventLoggedAt_cases)
theorem setupSecret_3 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 3 = randTerm 11 64 := by rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupSecret_5 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 5 = randTerm 17 64 := by rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupPublic_5 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 5 = DY.Signature.sign (randTerm 5 32) (randTerm 11 64) (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.setupPublic_5_bridge r hNe
theorem setupPublic_7 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 7 = DY.Signature.sign (randTerm 5 32) (randTerm 17 64) (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64))) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.setupPublic_7_bridge r hNe
private theorem setupTr1_pqst_id {a p : Participant} {sk : DY.Bytes} {j : Nat} (h : PQXDHStoredAt (TR.setupTr1 a) p { kind := .identity, sk } j) : j = 4 ∧ p = a ∧ sk = randTerm 0 32 := by
  unfold TR.setupTr1 at h
  rcases pqxdhStoredAt_append_same h with ⟨_, h⟩ | ⟨rfl, rfl, hst⟩
  · have hnil := pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl h)))
    unfold PQXDHStoredAt at hnil
    rw [Symbolic.Swarm.CREF.at?_ge_length Trace.nil (by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_nil_eq]; omega)] at hnil
    cases hnil
  · injection hst with _ hsk
    exact ⟨by simp [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_nil_eq], rfl, hsk.symm⟩
private theorem setupTr2_pqst_id {a b p : Participant} {sk : DY.Bytes} {j : Nat} (h : PQXDHStoredAt (TR.setupTr2 a b) p { kind := .identity, sk } j) : (j = 4 ∧ p = a ∧ sk = randTerm 0 32) ∨ (j = 9 ∧ p = b ∧ sk = randTerm 5 32) := by
  unfold TR.setupTr2 at h
  rcases pqxdhStoredAt_append_same h with ⟨_, h⟩ | ⟨rfl, rfl, hst⟩
  · exact Or.inl (setupTr1_pqst_id (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl h)))))
  · injection hst with _ hsk
    exact Or.inr ⟨by simp [TR.setupTr1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_nil_eq], rfl, hsk.symm⟩
private theorem setupTr3_pqst_id {a b p : Participant} {sk : DY.Bytes} {j : Nat} (h : PQXDHStoredAt (TR.setupTr3 a b) p { kind := .identity, sk } j) : (j = 4 ∧ p = a ∧ sk = randTerm 0 32) ∨ (j = 9 ∧ p = b ∧ sk = randTerm 5 32) := by
  unfold TR.setupTr3 at h
  rcases pqxdhStoredAt_append_same (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl h)) with ⟨_, h⟩ | ⟨_, _, hst⟩
  · exact setupTr2_pqst_id (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl h)))
  · cases hst
private theorem setupTr4_pqxdhStoredAt_identity {a b p : Participant} {sk : DY.Bytes} {j : Nat} (h : PQXDHStoredAt (TR.setupTr4 a b) p { kind := .identity, sk } j) : (j = 4 ∧ p = a ∧ sk = randTerm 0 32) ∨ (j = 9 ∧ p = b ∧ sk = randTerm 5 32) := by
  unfold TR.setupTr4 at h
  rcases pqxdhStoredAt_append_same (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl h)) with ⟨_, h⟩ | ⟨_, _, hst⟩
  · exact setupTr3_pqst_id (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl h)))
  · cases hst
theorem setupTrace_pqxdhStoredAt_identity {r : Records} (hNe : r.alice ≠ r.bob) {p : Participant} {sk : DY.Bytes} {j : Nat} (h : PQXDHStoredAt (setupTrace r) p { kind := .identity, sk } j) : (j = 4 ∧ p = r.alice ∧ sk = setupSecret r 0) ∨ (j = 9 ∧ p = r.bob ∧ sk = setupSecret r 1) := by
  rw [TR.setupTrace_eq r hNe] at h; rw [setupSecret_0 hNe, setupSecret_1 hNe]
  cases hw : r.withOpk <;> rw [hw] at h
  · exact setupTr4_pqxdhStoredAt_identity h
  · unfold TR.setupTr5 at h
    rcases pqxdhStoredAt_append_same (pqxdhStoredAt_append_other rfl h) with ⟨_, h⟩ | ⟨_, _, hst⟩
    · exact setupTr4_pqxdhStoredAt_identity (pqxdhStoredAt_append_other rfl (pqxdhStoredAt_append_other rfl h))
    · cases hst
theorem getMessageSentAt_of_netMsgAt {tr : ExecTrace} {i : Nat} {b : DY.Bytes} (h : NetMsgAt b i tr) : tr.getMessageSentAt i = some b := CompPrefixInvAlice.getMessageSentAt_of_netMsgAt h
theorem ecKey_inj {a b : HwBytes} (h : ecKey a = ecKey b) : a = b := by simpa [ecKey] using congrArg List.tail h
theorem kyberKey_inj {a b : HwBytes} (h : kyberKey a = kyberKey b) : a = b := by simpa [kyberKey] using congrArg List.tail h
abbrev aliceStartState (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : DY.Libsignal.TripleRatchet.TRState := CompPrefixInvAlice.iniAliceStartState tr b o
abbrev aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : ExecTrace := CompPrefixInvAlice.iniAliceStartTr tr a b o
theorem aliceStart_next_cases (a b : DY.Participant) (idStateIdx regIdxB : Nat) (bh : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) (tr : ExecTrace) : (Move.aliceStart a b idStateIdx regIdxB bh shown).next tr = tr ∨ (Move.aliceStart a b idStateIdx regIdxB bh shown).next tr = tr.append (TR.RndE 32) ∨ ∃ (ikA ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (honest : Bool), PQXDHStoredAt tr a { kind := .identity, sk := ikA } idStateIdx ∧ tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regIdxB ∧ NetMsgAt spk bh.spk tr ∧ NetMsgAt spkSig bh.spkSig tr ∧ NetMsgAt pqpk bh.pqpk tr ∧ NetMsgAt pqpkSig bh.pqpkSig tr ∧ DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spk) spkSig = true ∧ DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqpk) pqpkSig = true ∧ ((bh.opk = none ∧ opk = none) ∨ (∃ idx u, bh.opk = some idx ∧ opk = some u ∧ NetMsgAt u idx tr)) ∧ (Move.aliceStart a b idStateIdx regIdxB bh shown).next tr = aliceStartTrOfOut tr a b (aliceOut tr ikA ikB spk pqpk opk) := by
  let Inv : ExecTrace → Prop := fun tr' =>
    tr' = tr ∨ tr' = tr.append (TR.RndE 32) ∨ ∃ (ikA ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (honest : Bool), PQXDHStoredAt tr a { kind := .identity, sk := ikA } idStateIdx ∧ tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regIdxB ∧ NetMsgAt spk bh.spk tr ∧ NetMsgAt spkSig bh.spkSig tr ∧ NetMsgAt pqpk bh.pqpk tr ∧ NetMsgAt pqpkSig bh.pqpkSig tr ∧ DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spk) spkSig = true ∧ DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqpk) pqpkSig = true ∧ ((bh.opk = none ∧ opk = none) ∨ (∃ idx u, bh.opk = some idx ∧ opk = some u ∧ NetMsgAt u idx tr)) ∧ tr' = aliceStartTrOfOut tr a b (aliceOut tr ikA ikB spk pqpk opk);
  change Inv ((Move.aliceStart a b idStateIdx regIdxB bh shown).next tr)
  unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine CompPrefixInvAlice.bind_aliceHandshake_at' (Inv := Inv) a b idStateIdx regIdxB bh tr (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_; intro ikA ikB vkB spk spkSig pqpk pqpkSig opk honest hstA hregB hspk hspkSig hpq hpqSig hv1 hv2 hopk _ _; exact Or.inr (Or.inr ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest, hstA, hregB, hspk, hspkSig, hpq, hpqSig, hv1, hv2, hopk, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.aliceStart_cont_run_snd_eq tr a b (aliceOut tr ikA ikB spk pqpk opk)⟩)
theorem setupTrace_eventLoggedAt_identityRegistered {r : Records} (hNe : r.alice ≠ r.bob) {b : Participant} {ikB vkB : DY.Bytes} {honest : Bool} {j : Nat} (h : (setupTrace r).EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) j) : (j = 1 ∧ b = r.alice ∧ ikB = setupPublic r 0 ∧ vkB = setupPublic r 1 ∧ honest = true) ∨ (j = 6 ∧ b = r.bob ∧ ikB = setupPublic r 2 ∧ vkB = setupPublic r 3 ∧ honest = true) := by
  rcases setupTrace_eventLoggedAt_cases hNe h with ⟨rfl, hev⟩ | ⟨rfl, hev⟩ | ⟨_, hev⟩ | ⟨_, hev⟩ | ⟨_, _, hev⟩
  · injection hev with hb hik hvk hhon; exact Or.inl ⟨rfl, hb, hik, hvk, hhon⟩
  · injection hev with hb hik hvk hhon; exact Or.inr ⟨rfl, hb, hik, hvk, hhon⟩
  all_goals cases hev
theorem pia_bundle_inv {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {pre : List Move} {a b : Participant} {idS regB : Nat} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat} {bun : HwBytes} {rs : List MachineEvent} (hNe : r.alice ≠ r.bob) (hnb : CompSetupSecrecy.NoBrk r pre) (hs_pre : ∀ m ∈ pre, m.isSetup = false) (ha_pre : MovesAnchored pre (setupTrace r)) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hreach₁ : (runMoves pre (setupTrace r)).1.Reachable reachability) (hdone : (eventIdx isAliceDone (runMoves pre (setupTrace r)).1 ((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1)).isSome = true) (hm₀_vis : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis (runMoves pre (setupTrace r)).1 ((Move.aliceStart a b idS regB hb shown).next (runMoves pre (setupTrace r)).1) hb)) (hbun4 : bun[4]? ≠ some 1#8) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart a b idS regB hb shown;
    regB = 6 ∧ b = r.bob ∧ hb.opk = none ∧ bun[4]? = some 0#8 ∧ ∃ (ikA spkSig pqpkSig : DY.Bytes), ((idS = 4 ∧ a = r.alice ∧ ikA = setupSecret r 0) ∨ (idS = 9 ∧ a = r.bob ∧ ikA = setupSecret r 1)) ∧ NetMsgAt (setupPublic r 4) hb.spk tr₁ ∧ NetMsgAt spkSig hb.spkSig tr₁ ∧ NetMsgAt (setupPublic r 6) hb.pqpk tr₁ ∧ NetMsgAt pqpkSig hb.pqpkSig tr₁ ∧ DY.Signature.verify (setupPublic r 3) (DY.Libsignal.PQXDH.encodeEC (setupPublic r 4)) spkSig = true ∧ DY.Signature.verify (setupPublic r 3) (DY.Libsignal.PQXDH.encodeKEM (setupPublic r 6)) pqpkSig = true ∧ BundleCore i S g bun (setupPublic r 4) spkSig (setupPublic r 6) pqpkSig ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ a r.bob
          (aliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) := by
  obtain ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest, hstA, hregB, hspk, hspkSig, hpq, hpqSig, hv1, hv2, hopk, _, _, hnext⟩ := CompPrefixInvAlice.aliceStart_inv_of_isAliceDone hdone; have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable _ hreach₁
  have hpin : regB = 6 ∧ b = r.bob ∧ ikB = setupPublic r 2 ∧ vkB = setupPublic r 3 ∧ honest = true ∧
      spk = setupPublic r 4 ∧ pqpk = setupPublic r 6 := by
    rcases Symbolic.Swarm.COMPOSED.CompInv.bundleOK_of_verify hinv hregB
        hspkSig.attackerKnows hpqSig.attackerKnows hv1 hv2 (Nat.le_refl _) with
      ⟨_, _, _, _, _, ⟨_, _, _, _, hspk_ev⟩, rfl, ⟨_, _, _, _, hpq_ev⟩, rfl⟩ | ⟨j, hj, _⟩ | ⟨j, hj, _⟩
    · rcases setupTrace_eventLoggedAt_cases hNe ((eventLoggedAt_of_movesFrom_invisibleNoEffect hpre).mp hspk_ev) with
        ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, hev⟩ | ⟨_, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
      injection hev with hb_eq hspk_eq; subst hb_eq
      rcases setupTrace_eventLoggedAt_cases hNe ((eventLoggedAt_of_movesFrom_invisibleNoEffect hpre).mp hpq_ev) with
        ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, hev2⟩ | ⟨_, _, ⟨⟩⟩
      injection hev2 with _ hpq_eq
      rcases setupTrace_eventLoggedAt_identityRegistered hNe ((eventLoggedAt_of_movesFrom_invisibleNoEffect hpre).mp hregB) with
        ⟨_, hb_eq, _, _, _⟩ | ⟨rfl, _, hikB_eq, hvkB_eq, hhon_eq⟩
      · exact absurd hb_eq.symm hNe
      · exact ⟨rfl, rfl, hikB_eq, hvkB_eq, hhon_eq, hspk_eq, hpq_eq⟩
    · rcases setupTrace_eventLoggedAt_cases hNe ((eventLoggedAt_of_movesFrom_invisibleNoEffect hpre).mp hj) with
        ⟨_, hev⟩ | ⟨_, hev⟩ | ⟨_, hev⟩ | ⟨_, hev⟩ | ⟨_, _, hev⟩ <;> cases hev
    · exact absurd ⟨j, by simpa only [xpl_runTrace_eq] using hj⟩ hnb.1
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpin
  have hid := setupTrace_pqxdhStoredAt_identity hNe
    ((pqxdhStoredAt_of_movesFrom_invisible hs_pre ha_pre hpre).mp hstA)
  have hbh_rec : received (runMoves pre (setupTrace r)).1 ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList) =
      [setupPublic r 4, spkSig, setupPublic r 6, pqpkSig] ++ opk.toList := by
    have hs1 := getMessageSentAt_of_netMsgAt hspk; have hs2 := getMessageSentAt_of_netMsgAt hspkSig; have hs3 := getMessageSentAt_of_netMsgAt hpq; have hs4 := getMessageSentAt_of_netMsgAt hpqSig
    rcases hopk with ⟨hb_none, ho_none⟩ | ⟨idx, o, hb_some, ho_some, ho_net⟩
    · subst ho_none; simp [received, hb_none, hs1, hs2, hs3, hs4]
    · subst ho_some; simp [received, hb_some, hs1, hs2, hs3, hs4, getMessageSentAt_of_netMsgAt ho_net]
  cases hm₀_vis with
  | cons hhead _ =>
    have hbm : BundleMatches i S g bun
        (received (runMoves pre (setupTrace r)).1 ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList)) := hhead.2
    rw [hbh_rec] at hbm
    have hopk_none : opk = none := by
      cases opk with
      | none => rfl
      | some u => simp only [Option.toList, List.cons_append, List.nil_append] at hbm; exact absurd hbm.2.1 hbun4
    subst hopk_none
    have hbh_none : hb.opk = none := by rcases hopk with ⟨h1, _⟩ | ⟨_, _, _, h2, _⟩ <;> [exact h1; cases h2]
    dsimp only [Option.toList, List.append_nil, BundleMatches] at hbm; exact ⟨rfl, rfl, hbh_none, hbm.2, ikA, spkSig, pqpkSig, hid, hspk, hspkSig, hpq, hpqSig, hv1, hv2, hbm.1, hnext⟩
private theorem movesAnchored_append_left : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), MovesAnchored (ms₁ ++ ms₂) tr → MovesAnchored ms₁ tr
  | [], _, _, _ => trivial
  | m :: ms₁, ms₂, tr, ⟨hm, hrest⟩ => ⟨hm, movesAnchored_append_left ms₁ ms₂ (m.next tr) hrest⟩
private theorem runMoves_le : ∀ (δ : List Move) (tr : ExecTrace), tr ≤ (runMoves δ tr).1
  | [], tr => Trace.le_refl tr
  | m :: δ, tr => Trace.le_trans _ _ _ (m.le_next tr) (runMoves_le δ (m.next tr))
theorem matchedPrefix_ini_send_bundle_legacy {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} {pt c w : HwBytes} (hNe : r.alice ≠ r.bob) (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms ((.recv bun :: rs) ++ [.pt pt, .rng c, .send w])) (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng) (hbun4 : bun[4]? ≠ some 1#8) (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) : ∃ pre a idS hb shown mid me sIdx cl pq wr post ikA spkSig pqpkSig, ms = pre ++ .aliceStart a r.bob idS 6 hb shown :: mid ++ .encrypt me sIdx cl pq (some wr) :: post ∧ let tr₁ := (runMoves pre (setupTrace r)).1;
      let o := aliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart a r.bob idS 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let m₁ := Move.encrypt me sIdx cl pq (some wr);
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) post ∧
      35 ≤ shown ∧ hb.opk = none ∧ bun[4]? = some 0#8 ∧ ((idS = 4 ∧ a = r.alice ∧ ikA = setupSecret r 0) ∨ (idS = 9 ∧ a = r.bob ∧ ikA = setupSecret r 1)) ∧ NetMsgAt (setupPublic r 4) hb.spk tr₁ ∧ NetMsgAt spkSig hb.spkSig tr₁ ∧ NetMsgAt (setupPublic r 6) hb.pqpk tr₁ ∧ NetMsgAt pqpkSig hb.pqpkSig tr₁ ∧ BundleCore i S g bun (setupPublic r 4) spkSig (setupPublic r 6) pqpkSig ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ a r.bob o ∧
      lastSent tr₂ (m₁.next tr₂) ≠ none ∧
      List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (m₀.next tr₁) hb) ∧
      List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w]
        (encVis tr₂ (m₁.next tr₂) (some wr) true) := by
  obtain ⟨pre, a, b, idS, regB, hb, shown, mid, me, sIdx, cl, pq, wr, post, hms, hpre, hmid, hpost, hshown, hdone, hls, hm₀_vis, hm₁_vis⟩ := matchedPrefix_ini_send_struct hmp hrs_len hrs_kind hw
  have hms_split : ms = pre ++ (.aliceStart a b idS regB hb shown :: mid ++
      .encrypt me sIdx cl pq (some wr) :: post) := by simp [hms, List.append_assoc]
  have hreach₁ : (runMoves pre (setupTrace r)).1.Reachable reachability := by rw [← xpl_runTrace_eq]; exact matchedPrefix6_prefix_reachable hmp pre _ hms_split
  have hnb_pre : CompSetupSecrecy.NoBrk r pre :=
    CompSetupSecrecy.noBrk_of_le (by rw [hms_split, xpl_runTrace_eq, xpl_runTrace_eq, runMoves_append_fst]; exact runMoves_le _ _) hnb
  have hs_pre : ∀ m ∈ pre, m.isSetup = false :=
    fun m hm => hmp.2.1.2.1 m (by rw [hms_split]; exact List.mem_append_left _ hm)
  have ha_pre : MovesAnchored pre (setupTrace r) := (by have ha_all := hmp.2.1.2.2.1.2.1; rw [hms_split] at ha_all; exact movesAnchored_append_left pre _ (setupTrace r) ha_all); obtain ⟨rfl, rfl, hhb_opk, hbun0, ikA, spkSig, pqpkSig, hid, hspk, hspkSig, hpq, hpqSig, _, _, hcore, hnext⟩ := pia_bundle_inv hNe hnb_pre hs_pre ha_pre hpre hreach₁ hdone hm₀_vis hbun4; exact ⟨pre, a, idS, hb, shown, mid, me, sIdx, cl, pq, wr, post, ikA, spkSig, pqpkSig, hms, hpre, hmid, hpost, hshown, hhb_opk, hbun0, hid, hspk, hspkSig, hpq, hpqSig, hcore, hnext, hls, hm₀_vis, hm₁_vis⟩
end Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
