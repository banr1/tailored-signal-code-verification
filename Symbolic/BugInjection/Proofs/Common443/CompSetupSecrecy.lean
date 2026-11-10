/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompInv
public import Symbolic.Proofs.Swarm.COMPOSED.CompPresBob
public import Symbolic.Proofs.Swarm.CREF.TRView
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
public import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Swarm.CREF.Xpl.Steps
public import Symbolic.Proofs.Swarm.CREF.Xpl.StepsMix
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecordsBridgePure
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0

@[expose] public section
set_option autoImplicit false
abbrev DY.Libsignal.Composed.Refinement.Records.setupMove := DY.Libsignal.Composed.Refinement.ProtocolSetup.setupMove
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.Swarm.CREF Symbolic.Swarm.CREF.TR Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation)
def NoNewPQEv (P : DY.Libsignal.PQXDH.PQXDHEvent → Bool) (tr₀ tr : ExecTrace) : Prop := ∀ ev j, P ev = true → tr.EventLoggedAt ev j → tr₀.EventLoggedAt ev j
theorem noNewPQEv_refl (P : DY.Libsignal.PQXDH.PQXDHEvent → Bool) (tr₀ : ExecTrace) : NoNewPQEv P tr₀ tr₀ := fun _ _ _ h => h
theorem noNewPQEv_append_other {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ tr : ExecTrace} (hInv : NoNewPQEv P tr₀ tr) {E : Type} [ExecTraceTypes.Has E] (e : E) (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none) : NoNewPQEv P tr₀ (tr.append e) :=
  fun ev j hp hj => hInv ev j hp (CompTrace.eventLoggedAt_append_other hnone hj)
theorem noNewPQEv_append_pq {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ tr : ExecTrace} (hInv : NoNewPQEv P tr₀ tr) (ev₀ : DY.Libsignal.PQXDH.PQXDHEvent) (hne : P ev₀ = false) : NoNewPQEv P tr₀ (tr.append (CompTrace.PQEvE ev₀)) := by
  intro ev j hp hj
  rcases CompTrace.eventLoggedAt_append_same hj with ⟨_, hj⟩ | ⟨_, rfl⟩
  · exact hInv ev j hp hj
  · rw [hne] at hp; cases hp
@[reducible] def isNonMovePQEv : DY.Libsignal.PQXDH.PQXDHEvent → Bool
  | .IdentityRegistered .. | .SignedPrekeyPublished .. | .PQPrekeyPublished ..
  | .OneTimePrekeyPublished .. => true
  | _ => false
private theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type} (p : α × β) (f : α → β → Traceful γ) (hf : ∀ a b, CompTrace.Preserves Inv (f a b)) : CompTrace.Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b
private theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α) (noneCase : Traceful β) (someCase : α → Traceful β) (hn : CompTrace.Preserves Inv noneCase) (hs : ∀ a, CompTrace.Preserves Inv (someCase a)) : CompTrace.Preserves Inv (Option.casesOn o noneCase someCase) := by rcases o with _ | a; exact hn; exact hs a
private theorem preserves_genRand {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (n : Nat) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr hInv => (TR.Runs.genRand tr n).2.symm ▸ noNewPQEv_append_other hInv (CompTrace.RndE n) rfl
private theorem preserves_sendMessage {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (m : DY.Bytes) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.Network.sendMessage m) :=
  fun tr hInv => (TR.Runs.sendMessage tr m).2.symm ▸ noNewPQEv_append_other hInv (CompTrace.NetE m) rfl
private theorem preserves_storeLocalState_tr {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (p : Participant) (st : DY.Libsignal.TripleRatchet.TRState) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => by rw [storeLocalState_tr_snd_eq]; exact noNewPQEv_append_other hInv (CompTrace.TRStE p st) rfl
private theorem preserves_storeLocalState_pq {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => (TR.Runs.storeLocalState tr p st).2.symm ▸ noNewPQEv_append_other hInv (CompTrace.PQStE p st) rfl
private theorem preserves_logEventPQ {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (ev : DY.Libsignal.PQXDH.PQXDHEvent) (hne : P ev = false) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => (TR.Runs.logEvent tr ev).2.symm ▸ noNewPQEv_append_pq hInv ev hne
private theorem preserves_logEventC {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (ev : CEvent) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPQEv_append_other hInv (CompTrace.CEvE ev) rfl
private theorem preserves_logEventTR {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (ev : DY.Libsignal.TripleRatchet.TREvent) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPQEv_append_other hInv (CompTrace.TREvE ev) rfl
private theorem preserves_getKey {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.Libsignal.PQXDH.getKey p h kind) :=
  CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p h) fun _ =>
    CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
private theorem preserves_lookupIdentity {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (p : Participant) (h : Nat) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry h) fun _ => ?_
  split
  · exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure
private theorem preserves_logMessageKeyAndStore {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (me : Participant) (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (r par : Nat) (st : DY.Libsignal.TripleRatchet.TRState) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  CompTrace.Preserves.bind (preserves_logEventTR _) fun _ => preserves_storeLocalState_tr _ _
private theorem preserves_dhRatchetStep {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (st : DY.Libsignal.TripleRatchet.TRState) (pk : DY.Bytes) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ =>
    CompTrace.Preserves.bind (preserves_genRand 32) fun _ => CompTrace.Preserves.pure _
private theorem preserves_ensureReceiverChain {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (st : DY.Libsignal.TripleRatchet.TRState) (pk : DY.Bytes) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.bind (preserves_dhRatchetStep st pk) fun _ => CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure
private theorem preserves_logSkippedKeys {P : DY.Libsignal.PQXDH.PQXDHEvent → Bool} {tr₀ : ExecTrace} (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) : CompTrace.Preserves (NoNewPQEv P tr₀) (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact CompTrace.Preserves.pure _
  | succ k ih => exact CompTrace.Preserves.bind (preserves_logEventTR _) fun _ => ih _ _
local macro "noNonMovePQ_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply CompTrace.Preserves.bind | with_reducible apply preserves_prodCasesOn | with_reducible apply preserves_optionCasesOn
  | with_reducible apply CompTrace.Preserves.pure | with_reducible apply CompTrace.Preserves.failure | with_reducible apply preserves_genRand
  | with_reducible apply preserves_storeLocalState_tr | with_reducible apply preserves_storeLocalState_pq | with_reducible apply preserves_sendMessage
  | with_reducible apply CompTrace.Preserves.getLocalState_tr | with_reducible apply CompTrace.Preserves.getLocalState_pq | with_reducible apply preserves_getKey
  | with_reducible apply preserves_lookupIdentity | with_reducible apply CompTrace.Preserves.receiveMessage | with_reducible apply CompTrace.Preserves.getEntry
  | with_reducible apply CompTrace.Preserves.receiveSignalMsg | with_reducible apply CompTrace.Preserves.verifyMacAndDecrypt | with_reducible apply preserves_dhRatchetStep
  | with_reducible apply preserves_ensureReceiverChain | with_reducible apply preserves_logSkippedKeys | with_reducible apply CompTrace.Preserves.guardP
  | with_reducible apply CompTrace.Preserves.monadLiftErr | with_reducible apply CompTrace.Preserves.guardTrace | with_reducible apply CompTrace.Preserves.requireTracePredicate
  | with_reducible apply CompTrace.Preserves.traceLength | with_reducible apply preserves_logMessageKeyAndStore | with_reducible apply preserves_logEventPQ _ (by rfl)
  | with_reducible apply preserves_logEventC | with_reducible apply preserves_logEventTR | split | with_reducible intro))
private theorem preserves_aliceHandshake_noNewNonMovePQEv {tr₀ : ExecTrace} (a b : Participant) (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) : CompTrace.Preserves (NoNewPQEv isNonMovePQEv tr₀) (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by unfold DY.Libsignal.PQXDH.aliceHandshake; noNonMovePQ_tac
private theorem preserves_bobHandshake_noNewNonMovePQEv {tr₀ : ExecTrace} (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) : CompTrace.Preserves (NoNewPQEv isNonMovePQEv tr₀) (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by unfold DY.Libsignal.PQXDH.bobHandshake; noNonMovePQ_tac
private theorem preserves_move_noNewNonMovePQEv {tr₀ : ExecTrace} {m : Move} (hs : m.isSetup = false) : CompTrace.Preserves (NoNewPQEv isNonMovePQEv tr₀) (Move.act m) := by
  cases m
  case setup => cases hs
  case aliceStart a b idStateIdx regIdxB h _ =>
    unfold Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine CompTrace.Preserves.bind (CompTrace.Preserves.bind
      (preserves_aliceHandshake_noNewNonMovePQEv a b idStateIdx regIdxB h) fun _ => ?_) fun _ => ?_ <;> noNonMovePQ_tac
  case bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ =>
    unfold Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
    refine CompTrace.Preserves.bind (CompTrace.Preserves.bind
      (preserves_bobHandshake_noNewNonMovePQEv b a kh regIdxA mh.ek mh.ct) fun _ => ?_) fun _ => ?_ <;> noNonMovePQ_tac
  all_goals (
    dsimp only [Move.act, DY.Libsignal.TripleRatchet.messageEncrypt, DY.Libsignal.TripleRatchet.messageEncryptAbort, DY.Libsignal.TripleRatchet.messageDecryptSkipped, DY.Libsignal.PQXDH.compromiseIK, DY.Libsignal.PQXDH.compromiseSPK, DY.Libsignal.PQXDH.compromisePQSPK, DY.Libsignal.PQXDH.compromiseOPK, DY.Libsignal.TripleRatchet.exposeKey, DY.Libsignal.TripleRatchet.exposeSpqr, DY.Libsignal.TripleRatchet.exposeSkipped, DY.Libsignal.PQXDH.breakDH, DY.Libsignal.PQXDH.breakKEM]
    try rw [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    noNonMovePQ_tac)
private theorem noNewNonMovePQEv_runMoves {tr₀ : ExecTrace} : ∀ (ms : List Move) (tr : ExecTrace), (∀ m ∈ ms, m.isSetup = false) → NoNewPQEv isNonMovePQEv tr₀ tr → NoNewPQEv isNonMovePQEv tr₀ (runMoves ms tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hns, htr =>
    noNewNonMovePQEv_runMoves ms (m.next tr) (fun m' hm' => hns m' (List.mem_cons_of_mem _ hm')) (preserves_move_noNewNonMovePQEv (hns m List.mem_cons_self) tr htr)
theorem noNewNonMovePQEv_runTrace (r : Records) (ms : List Move) (hns : ∀ m ∈ ms, m.isSetup = false) : NoNewPQEv isNonMovePQEv (setupTrace r) (runTraceMoves r ms) := noNewNonMovePQEv_runMoves ms (setupTrace r) hns (noNewPQEv_refl _ _)
theorem at?_eq_of_le_of_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace} (hle : tr ≤ tr') {j : Nat} (hj : j < tr.length) : (tr'.at? j : Option E) = (tr.at? j : Option E) := XplSteps.xat?_le_eq hle hj
private theorem noNewLeakPQEv_move {tr₀ tr : ExecTrace} {m : Move} (htr : NoNewPQEv XplSteps.xplPqLeakEv tr₀ tr) (hnoleak : ∀ v ∈ m.vis tr, v.kind ≠ .leak) : NoNewPQEv XplSteps.xplPqLeakEv tr₀ (m.next tr) := by
  intro ev j hp hev
  have hle : tr ≤ m.next tr := XplSteps.xrun_le (Move.act m) tr
  have hj_next : j < (m.next tr).length := XplSteps.xlt_of_at?_some (by rwa [← eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent)])
  by_cases hj : j < tr.length
  · apply htr ev j hp; rw [eventLoggedAt_eq_at?] at hev ⊢; rwa [← at?_eq_of_le_of_lt hle hj]
  · exfalso
    have hmem : j ∈ newIndices tr (m.next tr) :=
      List.mem_range'.2 ⟨j - tr.length, by omega, by omega⟩
    have hget : (m.next tr).getEventAt DY.Libsignal.PQXDH.PQXDHEvent j = some ev := by rw [getEventAt_eq_at?]; rw [eventLoggedAt_eq_at?] at hev; rw [hev]
    obtain ⟨v, hv⟩ : ∃ v, pqExposureAt (m.next tr) j = some v := by unfold pqExposureAt; rw [hget]; revert hp; cases ev <;> simp [XplSteps.xplPqLeakEv]
    have hexp : v ∈ exposures tr (m.next tr) := List.mem_append_left _ (List.mem_filterMap.2 ⟨j, hmem, hv⟩); exact hnoleak v (by rw [xpl_vis_eq]; exact List.mem_append_right _ hexp) (xpl_exposures_kind hexp)
theorem noNewLeakPQEv_runMoves {tr₀ : ExecTrace} : ∀ (ms : List Move) (tr : ExecTrace), (∀ v ∈ (runMoves ms tr).2, v.kind ≠ .leak) → NoNewPQEv XplSteps.xplPqLeakEv tr₀ tr → NoNewPQEv XplSteps.xplPqLeakEv tr₀ (runMoves ms tr).1
  | [], _, _, htr => htr
  | m :: ms, tr, hnoleak, htr =>
    noNewLeakPQEv_runMoves ms (m.next tr) (fun v hv => hnoleak v (List.mem_append_right _ hv))
      (noNewLeakPQEv_move htr (fun v hv => hnoleak v (List.mem_append_left _ hv)))
theorem setupSecret_0 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 0 = randTerm 0 32 := by rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupSecret_1 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 1 = randTerm 5 32 := by rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupSecret_2 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 2 = randTerm 10 32 := by rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupSecret_4 {r : Records} (hNe : r.alice ≠ r.bob) : setupSecret r 4 = randTerm 16 64 := by rw [setupSecret, TR.setupRandoms_eq r hNe]; cases r.withOpk <;> rfl
theorem setupPublic_0 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 0 = DY.DiffieHellman.dhPk (randTerm 0 32) := setupPublic_0_bridge r hNe
theorem setupPublic_1 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 1 = DY.Signature.vk (randTerm 0 32) := setupPublic_1_bridge r hNe
theorem setupPublic_2 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 2 = DY.DiffieHellman.dhPk (randTerm 5 32) := setupPublic_2_bridge r hNe
theorem setupPublic_3 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 3 = DY.Signature.vk (randTerm 5 32) := setupPublic_3_bridge r hNe
theorem setupPublic_4 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 4 = DY.DiffieHellman.dhPk (randTerm 10 32) := setupPublic_4_bridge r hNe
theorem setupPublic_6 {r : Records} (hNe : r.alice ≠ r.bob) : setupPublic r 6 = DY.PQKem.kemPk (randTerm 16 64) := setupPublic_6_bridge r hNe
private theorem setupTr1_events {a : Participant} {ev : DY.Libsignal.PQXDH.PQXDHEvent} {j : Nat} (h : (TR.setupTr1 a).EventLoggedAt ev j) : j = 1 ∧ ev = .IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32)) (DY.Signature.vk (randTerm 0 32)) true := by
  unfold TR.setupTr1 at h; have h := CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl h))
  rcases CompTrace.eventLoggedAt_append_same h with ⟨_, h⟩ | ⟨rfl, hev⟩
  · exact (not_eventLoggedAt_nil (CompTrace.eventLoggedAt_append_other rfl h)).elim
  · exact ⟨by simp, hev.symm⟩
private theorem setupTr2_events {a b : Participant} {ev : DY.Libsignal.PQXDH.PQXDHEvent} {j : Nat} (h : (TR.setupTr2 a b).EventLoggedAt ev j) : (j = 1 ∧ ev = .IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32)) (DY.Signature.vk (randTerm 0 32)) true) ∨ (j = 6 ∧ ev = .IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32)) (DY.Signature.vk (randTerm 5 32)) true) := by
  unfold TR.setupTr2 at h; have h := CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl h))
  rcases CompTrace.eventLoggedAt_append_same h with ⟨_, h⟩ | ⟨rfl, hev⟩
  · exact Or.inl (setupTr1_events (CompTrace.eventLoggedAt_append_other rfl h))
  · exact Or.inr ⟨by simp [TR.setupTr1], hev.symm⟩
private theorem setupTr3_events {a b : Participant} {ev : DY.Libsignal.PQXDH.PQXDHEvent} {j : Nat} (h : (TR.setupTr3 a b).EventLoggedAt ev j) : (j = 1 ∧ ev = .IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32)) (DY.Signature.vk (randTerm 0 32)) true) ∨ (j = 6 ∧ ev = .IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32)) (DY.Signature.vk (randTerm 5 32)) true) ∨ (j = 12 ∧ ev = .SignedPrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 10 32))) := by
  unfold TR.setupTr3 at h; have h := CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl h))
  rcases CompTrace.eventLoggedAt_append_same h with ⟨_, h⟩ | ⟨rfl, hev⟩
  · rcases setupTr2_events (CompTrace.eventLoggedAt_append_other rfl
      (CompTrace.eventLoggedAt_append_other rfl h)) with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨by simp [TR.setupTr1, TR.setupTr2], hev.symm⟩)
private theorem setupTr4_events {a b : Participant} {ev : DY.Libsignal.PQXDH.PQXDHEvent} {j : Nat} (h : (TR.setupTr4 a b).EventLoggedAt ev j) : (j = 1 ∧ ev = .IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32)) (DY.Signature.vk (randTerm 0 32)) true) ∨ (j = 6 ∧ ev = .IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32)) (DY.Signature.vk (randTerm 5 32)) true) ∨ (j = 12 ∧ ev = .SignedPrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 10 32))) ∨ (j = 18 ∧ ev = .PQPrekeyPublished b (DY.PQKem.kemPk (randTerm 16 64))) := by
  unfold TR.setupTr4 at h; have h := CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl h))
  rcases CompTrace.eventLoggedAt_append_same h with ⟨_, h⟩ | ⟨rfl, hev⟩
  · rcases setupTr3_events (CompTrace.eventLoggedAt_append_other rfl
      (CompTrace.eventLoggedAt_append_other rfl h)) with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr ⟨by simp [TR.setupTr1, TR.setupTr2, TR.setupTr3], hev.symm⟩))
theorem setupTrace_eventLoggedAt_cases {r : Records} (hNe : r.alice ≠ r.bob) {ev : DY.Libsignal.PQXDH.PQXDHEvent} {j : Nat} (h : (setupTrace r).EventLoggedAt ev j) : (j = 1 ∧ ev = .IdentityRegistered r.alice (setupPublic r 0) (setupPublic r 1) true) ∨ (j = 6 ∧ ev = .IdentityRegistered r.bob (setupPublic r 2) (setupPublic r 3) true) ∨ (j = 12 ∧ ev = .SignedPrekeyPublished r.bob (setupPublic r 4)) ∨ (j = 18 ∧ ev = .PQPrekeyPublished r.bob (setupPublic r 6)) ∨ (r.withOpk = true ∧ j = 23 ∧ ev = .OneTimePrekeyPublished r.bob (DY.DiffieHellman.dhPk (randTerm 22 32))) := by
  rw [TR.setupTrace_eq r hNe] at h; rw [setupPublic_0 hNe, setupPublic_1 hNe, setupPublic_2 hNe, setupPublic_3 hNe, setupPublic_4 hNe, setupPublic_6 hNe]
  cases hw : r.withOpk <;> rw [hw] at h
  · rcases setupTr4_events h with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · unfold TR.setupTr5 at h; have h := CompTrace.eventLoggedAt_append_other rfl (CompTrace.eventLoggedAt_append_other rfl h)
    rcases CompTrace.eventLoggedAt_append_same h with ⟨_, h⟩ | ⟨rfl, hev⟩
    · rcases setupTr4_events (CompTrace.eventLoggedAt_append_other rfl h) with h1 | h2 | h3 | h4
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by simp [TR.setupTr1, TR.setupTr2, TR.setupTr3, TR.setupTr4], hev.symm⟩)))
def NoBrk (r : Records) (ms : List Move) : Prop :=
  ¬ (runTraceMoves r ms).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH ∧
  ¬ (runTraceMoves r ms).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM
theorem eventLogged_mono {E : Type} [ExecTraceTypes.Has (DY.ProtocolEvent.ExecEntryT E)] {tr tr' : ExecTrace} (hle : tr ≤ tr') {ev : E} (h : tr.EventLogged ev) : tr'.EventLogged ev := by
  obtain ⟨j, hj⟩ := h
  have hjlt : j < tr.length := XplSteps.xlt_of_at?_some (by rwa [← eventLoggedAt_eq_at? (E := E)])
  refine ⟨j, ?_⟩
  rw [eventLoggedAt_eq_at?, at?_eq_of_le_of_lt hle hjlt, ← eventLoggedAt_eq_at?]
  exact hj
theorem noBrk_of_le {r : Records} {ms : List Move} {tr : ExecTrace} (hle : runTraceMoves r ms ≤ tr) (h : ¬ tr.EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH ∧ ¬ tr.EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM) : NoBrk r ms :=
  ⟨fun h1 => h.1 (eventLogged_mono hle h1), fun h2 => h.2 (eventLogged_mono hle h2)⟩
theorem noBrk_of_eq {r : Records} {ms ms' : List Move} (heq : runTraceMoves r ms' = runTraceMoves r ms) (h : NoBrk r ms) : NoBrk r ms' := by
  unfold NoBrk at *; rwa [heq]
theorem not_compromised_of_no_leak {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) : (∀ p ik, ¬ (runTraceMoves r ms).EventLogged (DY.Libsignal.PQXDH.PQXDHEvent.CompromisedIK p ik)) ∧ (∀ b spk, ¬ (runTraceMoves r ms).EventLogged (DY.Libsignal.PQXDH.PQXDHEvent.CompromisedSPK b spk)) ∧ (∀ b pqpk, ¬ (runTraceMoves r ms).EventLogged (DY.Libsignal.PQXDH.PQXDHEvent.CompromisedPQSPK b pqpk)) ∧ (∀ b opk, ¬ (runTraceMoves r ms).EventLogged (DY.Libsignal.PQXDH.PQXDHEvent.CompromisedOPK b opk)) := by
  have hleak := noNewLeakPQEv_runMoves ms (setupTrace r)
    (fun v hv => hnoleak v (List.mem_append_right _ hv)) (noNewPQEv_refl _ _)
  have hlk : ∀ {ev j}, XplSteps.xplPqLeakEv ev = true → ¬ (setupTrace r).EventLoggedAt ev j := by
    intro ev j hp h; rcases setupTrace_eventLoggedAt_cases hNe h with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> cases hp
  exact ⟨fun _ _ ⟨j, hj⟩ => hlk rfl (hleak _ j rfl hj),
    fun _ _ ⟨j, hj⟩ => hlk rfl (hleak _ j rfl hj),
    fun _ _ ⟨j, hj⟩ => hlk rfl (hleak _ j rfl hj),
    fun _ _ ⟨j, hj⟩ => hlk rfl (hleak _ j rfl hj)⟩
theorem not_compromised_or_brokenDH_of_no_leak {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (_hns : ∀ m ∈ ms, m.isSetup = false) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) (hnb : NoBrk r ms) : (∀ p ik, ¬ (runTraceMoves r ms).EventLogged (DY.Libsignal.PQXDH.PQXDHEvent.CompromisedIK p ik)) ∧ (∀ b spk, ¬ (runTraceMoves r ms).EventLogged (DY.Libsignal.PQXDH.PQXDHEvent.CompromisedSPK b spk)) ∧ (∀ b pqpk, ¬ (runTraceMoves r ms).EventLogged (DY.Libsignal.PQXDH.PQXDHEvent.CompromisedPQSPK b pqpk)) ∧ (∀ b opk, ¬ (runTraceMoves r ms).EventLogged (DY.Libsignal.PQXDH.PQXDHEvent.CompromisedOPK b opk)) ∧ ¬ (runTraceMoves r ms).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenDH ∧ ¬ (runTraceMoves r ms).EventLogged DY.Libsignal.PQXDH.PQXDHEvent.BrokenKEM := by
  have hc := not_compromised_of_no_leak hNe hnoleak
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hnb.1, hnb.2⟩
theorem ikAt_cases_of_no_setup {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms, m.isSetup = false) {p : Participant} {s : DY.Bytes} (h : IKAt (runTraceMoves r ms) p s) : (p = r.alice ∧ s = setupSecret r 0 ∧ DY.DiffieHellman.dhPk s = setupPublic r 0) ∨ (p = r.bob ∧ s = setupSecret r 1 ∧ DY.DiffieHellman.dhPk s = setupPublic r 2) := by
  obtain ⟨t, rfl, _, hev⟩ := h
  rcases setupTrace_eventLoggedAt_cases hNe (noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev) with
    ⟨ht, heq⟩ | ⟨ht, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, _, heq⟩
  · obtain rfl : t = 0 := by omega
    injection heq with hp _ _ _; exact Or.inl ⟨hp, (setupSecret_0 hNe).symm, (setupPublic_0 hNe).symm⟩
  · obtain rfl : t = 5 := by omega
    injection heq with hp _ _ _; exact Or.inr ⟨hp, (setupSecret_1 hNe).symm, (setupPublic_2 hNe).symm⟩
  all_goals cases heq
theorem spkAt_eq_of_no_setup {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms, m.isSetup = false) {b : Participant} {sS : DY.Bytes} (h : SPKAt (runTraceMoves r ms) b sS) : b = r.bob ∧ sS = setupSecret r 2 ∧ DY.DiffieHellman.dhPk sS = setupPublic r 4 := by
  obtain ⟨t, rfl, _, _, hev⟩ := h
  rcases setupTrace_eventLoggedAt_cases hNe (noNewNonMovePQEv_runTrace r ms hns _ (t + 2) rfl hev) with
    ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨ht, heq⟩ | ⟨_, heq⟩ | ⟨_, _, heq⟩
  · cases heq
  · cases heq
  · obtain rfl : t = 10 := by omega
    injection heq with hb _; exact ⟨hb, (setupSecret_2 hNe).symm, (setupPublic_4 hNe).symm⟩
  all_goals cases heq
theorem pqAt_eq_of_no_setup {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms, m.isSetup = false) {b : Participant} {sQ : DY.Bytes} (h : PQAt (runTraceMoves r ms) b sQ) : b = r.bob ∧ sQ = setupSecret r 4 ∧ DY.PQKem.kemPk sQ = setupPublic r 6 := by
  obtain ⟨t, rfl, _, _, hev⟩ := h
  rcases setupTrace_eventLoggedAt_cases hNe (noNewNonMovePQEv_runTrace r ms hns _ (t + 2) rfl hev) with
    ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨ht, heq⟩ | ⟨_, _, heq⟩
  · cases heq
  · cases heq
  · cases heq
  · obtain rfl : t = 16 := by omega
    injection heq with hb _; exact ⟨hb, (setupSecret_4 hNe).symm, (setupPublic_6 hNe).symm⟩
  · cases heq
theorem bobDone_ek_dhPk_of_no_leak {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) (hnb : NoBrk r ms) {b a : Participant} {ikB ikA spk pqpk : DY.Bytes} {opk : Option DY.Bytes} {ek ct : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys} {i : Nat} (hBob : (runTraceMoves r ms).EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i) : DY.Libsignal.PQXDH.isCanonicalKey ek = true ∧ ∃ t a' b' spk' opk', t + 5 < i ∧ AliceSlot (runTraceMoves r ms) t ∧ (runTraceMoves r ms).EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a' b' ikA ikB spk' pqpk opk' ek ct keys) (t + 5) ∧ ek = DY.DiffieHellman.dhPk (randTerm t 32) := by
  have hinv := spqrInv_of_reachable (runTraceMoves r ms) hreach; have hno := not_compromised_or_brokenDH_of_no_leak hNe hns hnoleak hnb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcan, _, _, _,
    ⟨j, a', b', spk', opk', hj, hAlice⟩ | ⟨jc, hjc, _⟩ | ⟨jc, hjc, _⟩ | ⟨jd, hjd, _⟩⟩ :=
    hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys i hBob
  · obtain ⟨t, _, rfl, hslot, _, _, hek, _, _⟩ := hinv.aliceDone a' b' ikA ikB spk' pqpk opk' ek ct keys j hAlice; exact ⟨hcan, t, a', b', spk', opk', hj, hslot, hAlice, hek⟩
  · exact absurd ⟨jc, hjc⟩ (hno.1 a ikA)
  · exact absurd ⟨jc, hjc⟩ (hno.2.1 b spk)
  · exact absurd ⟨jd, hjd⟩ hno.2.2.2.2.1
theorem crit_noleak_of_forall2 {interpretation : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} : ∀ {τ : List DY.Libsignal.HwEvents.MachineEvent} {vis : List VisEntry}, (∀ e ∈ τ, eventKind e ≠ .leak) → List.Forall₂ (EventMatchesEntry interpretation r S g) τ vis → ∀ v ∈ vis, v.kind ≠ .leak
  | _, _, _, .nil, _, hv => by cases hv
  | e :: _, _ :: _, hτ, .cons hev hrest, _, hw => by
    rcases List.mem_cons.1 hw with rfl | hw
    · rw [← hev.1]; exact hτ e List.mem_cons_self
    · exact crit_noleak_of_forall2 (fun e' he' => hτ e' (List.mem_cons_of_mem _ he')) hrest _ hw
theorem crit_hyps_of_matchedPrefix_legacy {interpretation : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ : List DY.Libsignal.HwEvents.MachineEvent} (hmp : Compat interpretation r S g ∧ ModelRun r ms ∧ List.Forall₂ (EventMatchesEntry interpretation r S g) τ (runVis r ms)) (hτ : ∀ e ∈ τ, eventKind e ≠ .leak) : (∀ m ∈ ms, m.isSetup = false) ∧ (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability ∧ (∀ v ∈ runVis r ms, v.kind ≠ .leak) := ⟨hmp.2.1.2.1, hmp.2.1.2.2.1.1, crit_noleak_of_forall2 hτ hmp.2.2⟩
private theorem setupTrace_eq_of_alice_eq_bob (r : Records) (hEq : r.alice = r.bob) : setupTrace r = setupTr1 r.alice :=
  Symbolic.Swarm.CREF.CliPure.setupTrace_eq_self r hEq
theorem alice_ne_bob_of_modelRun {r : Records} {ms : List Move} (hrun : ModelRun r ms) : r.alice ≠ r.bob := by
  intro hEq; have hlen := hrun.1; rw [setupRandoms, setupTrace_eq_of_alice_eq_bob r hEq, newRandoms_setupTr1] at hlen
  cases h : r.withOpk <;> simp [h] at hlen
def StOpt (tr : ExecTrace) (me : Participant) : Option Nat → Option DY.Bytes → Prop
  | none, none => True
  | some i, some o => tr.at? i = some (TR.StE me { kind := .oneTimePrekey, sk := o })
  | _, _ => False
structure BobStartOk (tr : ExecTrace) (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) where
  (ikB spk pqsk ikAPk vkA ek ct raw spqr' key seed pqSalt m : DY.Bytes)
  opk : Option DY.Bytes
  honest : Bool
  keys : DY.Libsignal.PQXDH.HandshakeKeys
  msg : DY.Libsignal.TripleRatchet.TRSignalMsg
  c' : DY.Libsignal.TripleRatchet.RecvChain
  hik : tr.at? kh.ik = some (TR.StE b { kind := .identity, sk := ikB })
  hspk : tr.at? kh.spk = some (TR.StE b { kind := .signedPrekey, sk := spk })
  hpq : tr.at? kh.pqspk = some (TR.StE b { kind := .pqPrekey, sk := pqsk })
  hopk : StOpt tr b kh.opk opk
  hreg : tr.at? regA = some (TR.EvE (.IdentityRegistered a ikAPk vkA honest))
  hek : tr.at? mh.ek = some (TR.NetE ek)
  hct : tr.at? mh.ct = some (TR.NetE ct)
  hcan : DY.Libsignal.PQXDH.isCanonicalKey ek = true
  hagree : DY.Libsignal.PQXDH.bobAgreement ikB spk pqsk opk ikAPk ek ct = some keys
  hmsg : tr.at? mh.msg = some (TR.NetE raw)
  hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg
  hver : msg.version = DY.Libsignal.TripleRatchet.messageVersion
  hlow : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey = false
  hcons : DY.Libsignal.TripleRatchet.consumeMessageKey (CompPresBob.bobRatchetedChain keys msg.ratchetKey spk) msg.counter = some (seed, c')
  hspqr : DY.Spqr.spqrRecv (CompPresBob.bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey (randTerm tr.length 32)).spqr msg.pqRatchet spqrMsgIdx = some (spqr', key)
  hpqSalt : ((tr.append (TR.RndE 32)).append (TR.NetE key)).at? pqIdx = some (TR.NetE pqSalt)
  hmac : msg.mac = DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey (CompPresBob.bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey (randTerm tr.length 32)).peerIk (CompPresBob.bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey (randTerm tr.length 32)).myIk msg.wire
  hdec : DY.Libsignal.PQXDH.errToOption (DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m
  hused : ∀ o, opk = some o → DY.Libsignal.PQXDH.opkUsedB ((tr.append (TR.RndE 32)).append (TR.NetE key)) b (DY.DiffieHellman.dhPk o) = false
private theorem ensureReceiverChain_bobInitSt {tr : ExecTrace} {a : Participant} {ikB ikA : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys} {sS rt : DY.Bytes} (hlo : DY.Libsignal.TripleRatchet.x25519LowOrder rt = false) : Runs (DY.Libsignal.TripleRatchet.ensureReceiverChain (CompPresBob.bobInitSt a ikB ikA keys sS rt) rt) tr (CompPresBob.bobRatchetedSt a ikB ikA keys sS rt (randTerm tr.length 32), CompPresBob.bobRatchetedChain keys rt sS, true) (tr.append (TR.RndE 32)) := by simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold DY.Libsignal.TripleRatchet.recvChainFor DY.Libsignal.TripleRatchet.findRecvChain; dsimp only [CompPresBob.bobInitSt, List.find?_nil]; simp only [hlo, Bool.false_eq_true, ↓reduceIte]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; exact Runs.bind (Runs.bind (Runs.guard _ (by simp [hlo])) (Runs.bind (Runs.genRand tr 32) (Runs.pure _ _))) (Runs.pure _ _)
private theorem at?_of_getMessageSentAt {tr : ExecTrace} {i : Nat} {b : DY.Bytes} (h : tr.getMessageSentAt i = some b) : tr.at? i = some (TR.NetE b) := by
  rw [getMessageSentAt_eq_at?] at h
  rcases hat : (tr.at? i : Option DY.Network.ExecEntryT) with _ | ⟨m⟩ <;> rw [hat] at h
  · cases h
  · injection h with h; subst h; rfl
private theorem receiveMessage_fst (idx : Nat) (tr : ExecTrace) : ((DY.Network.receiveMessage idx).run tr).1 = tr.getMessageSentAt idx := receiveMessage_fst_eq idx tr
private theorem receiveSignalMsg_some {msgIdx : Nat} {tr : ExecTrace} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} (h : ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr).1 = some msg) : ∃ t, tr.at? msgIdx = some (TR.NetE t) ∧ DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg ∧ msg.version = DY.Libsignal.TripleRatchet.messageVersion := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg at h; rw [run_bind_fst, receiveMessage_fst, CompTrace.receiveMessage_snd] at h
  rcases hmsg : tr.getMessageSentAt msgIdx with _ | t <;> rw [hmsg] at h
  · cases h
  · dsimp only at h
    rcases hp : DY.Libsignal.TripleRatchet.parseTrSignalMsg t with _ | m <;> rw [hp] at h
    · rw [traceful_run_failure_fst] at h; cases h
    · dsimp only at h
      by_cases hv : m.version = DY.Libsignal.TripleRatchet.messageVersion <;>
        simp only [_root_.guard, hv, ↓reduceIte, run_bind_fst, traceful_run_pure_fst, traceful_run_failure_fst] at h
      · injection h with h; subst h; exact ⟨t, at?_of_getMessageSentAt hmsg, hp, hv⟩
      · cases h
private theorem verifyMacAndDecrypt_some {st : DY.Libsignal.TripleRatchet.TRState} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} {pqSalt seed ptTerm : DY.Bytes} {tr : ExecTrace} (h : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed).run tr).1 = some ptTerm) : msg.mac = DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire ∧ DY.Libsignal.PQXDH.errToOption (DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some ptTerm := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt at h
  by_cases hm : msg.mac = DY.Libsignal.TripleRatchet.computeMac
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire <;>
    simp only [_root_.guard, hm, ↓reduceIte, run_bind_fst, traceful_run_pure_fst, traceful_run_failure_fst, monadLift_err_fst_eq] at h
  · exact ⟨hm, h⟩
  · cases h
private theorem bobStart_inv_of_receivedPlaintext {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat} {pt : DY.Bytes} (hpt : receivedPlaintext tr ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr) = some pt) : Nonempty (BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) := by
  suffices H : ∀ pt', receivedPlaintext tr ((DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrMsgIdx).run tr).2.val =
        some pt' → Nonempty (BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) by
    refine H pt ?_; unfold Move.next Move.act at hpt; rw [run_bind_snd] at hpt
    rcases hr : ((DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrMsgIdx).run tr).1 with _ | n <;>
      simp only [hr, traceful_run_pure_snd] at hpt <;> exact hpt
  have hnone : ∀ {E : Type} [ExecTraceTypes.Has E] (t : ExecTrace) (e : E), tr.length ≤ t.length → receivedPlaintext tr t = none → (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)) = none → receivedPlaintext tr (t.append e) = none :=
    fun t e hle h0 hproj => by rw [receivedPlaintext_append_of_proj hle e hproj, h0]
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bind_bobHandshake_at
    (Inv := fun t => ∀ pt', receivedPlaintext tr t = some pt' → Nonempty (BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx))
    b a kh regA mh.ek mh.ct tr (fun pt' h => by rw [receivedPlaintext_self] at h; cases h)
    fun ikB spkSk pqsk opkSk ikA vkA ek ct honest keys hik hspk hpq hopk hreg hek hct hcan
      hagree pt' hpt' => ?_
  rw [run_bind_snd, CompTrace.Preserves.receiveSignalMsg (Inv := fun t => t = tr) mh.msg tr rfl] at hpt'
  rcases hmsg0 : ((DY.Libsignal.TripleRatchet.receiveSignalMsg mh.msg).run tr).1 with _ | msg
  · rw [hmsg0, receivedPlaintext_self] at hpt'; cases hpt'
  rw [hmsg0] at hpt'; dsimp only at hpt'; obtain ⟨raw, hmsg, hparse, hver⟩ := receiveSignalMsg_some hmsg0
  rcases hlow : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey with _ | _
  swap
  · have hens0 : ((DY.Libsignal.TripleRatchet.ensureReceiverChain (CompPresBob.bobInitSt a (DY.DiffieHellman.dhPk ikB) ikA keys spkSk msg.ratchetKey) msg.ratchetKey).run tr).1 = none ∧ ((DY.Libsignal.TripleRatchet.ensureReceiverChain (CompPresBob.bobInitSt a (DY.DiffieHellman.dhPk ikB) ikA keys spkSk msg.ratchetKey)
        msg.ratchetKey).run tr).2.val = tr := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold DY.Libsignal.TripleRatchet.recvChainFor DY.Libsignal.TripleRatchet.findRecvChain; dsimp only [CompPresBob.bobInitSt, List.find?_nil]; simp only [hlow, ↓reduceIte, traceful_run_failure_fst, traceful_run_failure_snd]; exact ⟨trivial, trivial⟩
    rw [run_bind_snd] at hpt'; erw [hens0.1, hens0.2] at hpt'; dsimp only at hpt'; rw [receivedPlaintext_self] at hpt'; cases hpt'
  have hens := ensureReceiverChain_bobInitSt (tr := tr) (a := a)
    (ikB := DY.DiffieHellman.dhPk ikB) (ikA := ikA) (keys := keys) (sS := spkSk) hlow
  rw [run_bind_snd] at hpt'; erw [hens.1, hens.2] at hpt'; dsimp only at hpt'; have hle1 : tr.length ≤ (tr.append (TR.RndE 32)).length := by simp
  have hr0 : receivedPlaintext tr (tr.append (TR.RndE 32)) = none := hnone tr _ (Nat.le_refl _) (receivedPlaintext_self tr) rfl
  rcases hcons : DY.Libsignal.TripleRatchet.consumeMessageKey
      (CompPresBob.bobRatchetedChain keys msg.ratchetKey spkSk) msg.counter with _ | ⟨seed, c'⟩
  · simp only [hcons, traceful_run_failure_snd, hr0] at hpt'; cases hpt'
  rw [hcons] at hpt'; dsimp only at hpt'
  rcases hsp : DY.Spqr.spqrRecv (CompPresBob.bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikA keys spkSk msg.ratchetKey
        (randTerm tr.length 32)).spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
  · simp only [hsp, traceful_run_failure_snd, hr0] at hpt'; cases hpt'
  rw [hsp] at hpt'; dsimp only at hpt'; have hk0 : receivedPlaintext tr ((tr.append (TR.RndE 32)).append (TR.NetE key)) = none := hnone _ _ hle1 hr0 rfl
  have hsend := TR.Runs.sendMessage (tr.append (TR.RndE 32)) key
  rw [run_bind_snd, hsend.1, hsend.2] at hpt'; dsimp only at hpt'; rw [run_bind_snd, CompTrace.receiveMessage_snd] at hpt'
  rcases hpq0 : ((DY.Network.receiveMessage pqIdx).run
      ((tr.append (TR.RndE 32)).append (TR.NetE key))).1 with _ | pqSalt
  · rw [hpq0, hk0] at hpt'; cases hpt'
  rw [hpq0] at hpt'; dsimp only at hpt'; rw [receiveMessage_fst] at hpq0; have hpqSalt := at?_of_getMessageSentAt hpq0; rw [run_bind_snd, CompTrace.verifyMacAndDecrypt_trace] at hpt'
  rcases hv0 : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt (CompPresBob.bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikA keys spkSk msg.ratchetKey (randTerm tr.length 32)) msg pqSalt seed).run
      ((tr.append (TR.RndE 32)).append (TR.NetE key))).1 with _ | m
  · rw [hv0, hk0] at hpt'; cases hpt'
  rw [hv0] at hpt'; dsimp only at hpt'; obtain ⟨hmac, hdec⟩ := verifyMacAndDecrypt_some hv0
  rcases opkSk with _ | o
  · refine ⟨BobStartOk.mk ikB spkSk pqsk ikA vkA ek ct raw spqr' key seed pqSalt m none honest keys msg c' hik hspk hpq ?_ ((eventLoggedAt_iff_at? _ _ _ _).mp hreg) hek hct hcan hagree hmsg hparse hver hlow hcons hsp hpqSalt
      hmac hdec (fun _ h => by cases h)⟩
    rcases hopk with ⟨h1, -⟩ | ⟨idx, o, -, h2, -⟩; · rw [h1]; trivial
    · cases h2
  · rcases hu : DY.Libsignal.PQXDH.opkUsedB ((tr.append (TR.RndE 32)).append (TR.NetE key)) b
        (DY.DiffieHellman.dhPk o) with _ | _
    · refine ⟨BobStartOk.mk ikB spkSk pqsk ikA vkA ek ct raw spqr' key seed pqSalt m (some o) honest keys msg c' hik hspk hpq ?_ ((eventLoggedAt_iff_at? _ _ _ _).mp hreg) hek hct hcan hagree hmsg hparse hver hlow hcons hsp
        hpqSalt hmac hdec (fun o' h => by cases h; exact hu)⟩
      rcases hopk with ⟨-, h2⟩ | ⟨idx, o', h1, h2, h3⟩; · cases h2
      · cases h2; rw [h1]; exact h3
    · exfalso; dsimp only [Option.map] at hpt'
      have hg1 : ((DY.Libsignal.PQXDH.guardTrace fun t => !DY.Libsignal.PQXDH.opkUsedB t b
          (DY.DiffieHellman.dhPk o)).run ((tr.append (TR.RndE 32)).append (TR.NetE key))).1 = none := by
        rw [(requireTracePredicate_run_eq _ _).1]; simp [hu]
      have hg2 : ((DY.Libsignal.PQXDH.guardTrace fun t => !DY.Libsignal.PQXDH.opkUsedB t b
          (DY.DiffieHellman.dhPk o)).run ((tr.append (TR.RndE 32)).append (TR.NetE key))).2.val =
          (tr.append (TR.RndE 32)).append (TR.NetE key) :=
        (requireTracePredicate_run_eq _ _).2
      rw [run_bind_snd, hg1, hg2, hk0] at hpt'; cases hpt'
theorem bobStart_accept_ok {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat} {v : VisEntry} (hv : v ∈ (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr) (hkind : v.kind = .accept) : Nonempty (BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) := by
  rcases hpt : receivedPlaintext tr
      ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr) with _ | pt
  · exfalso; rw [xpl_vis_eq, List.mem_append] at hv
    rcases hv with hv | hv
    · have hv' := List.mem_of_mem_take hv; simp only [bobVis, hpt, Option.map_none, Option.toList_none, List.append_nil, List.mem_cons, List.mem_map] at hv'
      rcases hv' with rfl | ⟨_, _, rfl⟩ <;> simp [rngEntry] at hkind
    · rw [xpl_exposures_kind hv] at hkind; cases hkind
  · exact bobStart_inv_of_receivedPlaintext hpt
theorem BobStartOk.aliceMatch_and_ek_dhPk_of_no_leak {r : Records} {ms : List Move} (hNe : r.alice ≠ r.bob) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) (hnoleak : ∀ v ∈ runVis r ms, v.kind ≠ .leak) (hnb : NoBrk r ms) {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} (w : BobStartOk (runTraceMoves r ms) b a kh regA mh pqIdx spqrMsgIdx) : AliceMatch (runTraceMoves r ms) w.ikAPk (DY.DiffieHellman.dhPk w.ikB) (DY.PQKem.kemPk w.pqsk) w.ek w.ct w.keys (runTraceMoves r ms).length ∧ ∃ t a' b' spk' opk' j, j < (runTraceMoves r ms).length ∧ AliceSlot (runTraceMoves r ms) t ∧ (runTraceMoves r ms).EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a' b' w.ikAPk (DY.DiffieHellman.dhPk w.ikB) spk' (DY.PQKem.kemPk w.pqsk) opk' w.ek w.ct w.keys) j ∧ w.ek = DY.DiffieHellman.dhPk (randTerm t 32) := by
  have hinv := spqrInv_of_reachable (runTraceMoves r ms) hreach; have hno := not_compromised_or_brokenDH_of_no_leak hNe hns hnoleak hnb; obtain ⟨e, hdec, hkeys⟩ := CompPresBob.kemDecap_of_bobAgreement w.hagree; have hmac : w.msg.mac.AttackerKnows (runTraceMoves r ms) := (CompPresBob.attackerKnows_of_parseTrSignalMsg hinv (NetMsgAt.attackerKnows w.hmsg) w.hparse).1
  rcases CompPresBob.comp_mac_origin hinv (cikOK_of_reachable hreach hinv) (hinv.stOK b { kind := .identity, sk := w.ikB } kh.ik w.hik) (hinv.stOK b { kind := .signedPrekey, sk := w.spk } kh.spk w.hspk) (hinv.stOK b { kind := .pqPrekey, sk := w.pqsk } kh.pqspk w.hpq)
      ((eventLoggedAt_iff_at? _ _ _ _).mpr w.hreg) w.hcan hdec hmac (by rw [← hkeys]; exact w.hcons) w.hmac with
    hmatch | hcik_ev | hcspk | hbdh
  · rw [← hkeys] at hmatch; have ⟨j, a', b', spk', opk', hj, hAlice⟩ := hmatch; obtain ⟨t, _, rfl, hslot, _, _, hek, _, _⟩ := hinv.aliceDone a' b' w.ikAPk (DY.DiffieHellman.dhPk w.ikB) spk' (DY.PQKem.kemPk w.pqsk) opk' w.ek w.ct w.keys j hAlice; exact ⟨hmatch, t, a', b', spk', opk', t + 5, hj, hslot, hAlice, hek⟩
  · exact absurd hcik_ev (hno.1 a w.ikAPk)
  · exact absurd hcspk (hno.2.1 b (DY.DiffieHellman.dhPk w.spk))
  · exact absurd hbdh hno.2.2.2.2.1
private theorem getMessageSentAt_of_at? {tr : ExecTrace} {i : Nat} {x : DY.Bytes} (h : tr.at? i = some (TR.NetE x)) : tr.getMessageSentAt i = some x := by rw [getMessageSentAt_eq_at?, h]
theorem BobStartOk.preKeyRecvMatches_of_vis {interpretation : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32} {shown : Nat} {wire : HwBytes} {v₀ : VisEntry} {vs : List VisEntry} (w : BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) (hvis : (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr = v₀ :: vs) (hno : ∀ v ∈ v₀ :: vs, v.kind ≠ .leak) (hm0 : EventMatchesEntry interpretation r S g (.recv wire) v₀) : PreKeyRecvMatches interpretation r S g wire [w.ek, w.ct, w.raw] := by
  have hexp : exposures tr ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr) = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun v hv => hno v
      (by rw [← hvis, xpl_vis_eq]; exact List.mem_append_right _ hv) (xpl_exposures_kind hv)
  rw [xpl_vis_eq, hexp, List.append_nil] at hvis
  cases shown with
  | zero => simp [xpl_ownVis] at hvis
  | succ k =>
    simp only [xpl_ownVis, bobVis, List.cons_append, List.take_succ_cons, List.cons.injEq] at hvis
    rcases hvis with ⟨rfl, _⟩
    have hrecv := hm0.2; have hrec : received tr [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := (by simp only [received, List.filterMap_cons, List.filterMap_nil, getMessageSentAt_of_at? w.hek, getMessageSentAt_of_at? w.hct, getMessageSentAt_of_at? w.hmsg]); change PreKeyRecvOpkMatches interpretation r S g wire (received tr [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr).toList) at hrecv; rw [hrec] at hrecv
    cases ho : bobOpkPk b kh tr <;> rw [ho] at hrecv <;> exact hrecv.1
end Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
