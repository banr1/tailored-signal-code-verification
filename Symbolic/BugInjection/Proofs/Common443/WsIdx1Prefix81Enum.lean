/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumAux
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a (at?_append_other_eq' at?_append_same_eq' bobFinalSt bobStartTr bobStart_next_eq at?_trSt_bobStartTr at?_rnd_bobStartTr length_lt_bobStartTr gamma_rng_of_bobVis_forall2)
open Symbolic.Swarm.COMPOSED.CompInv.CompPresBob (bobInitSt bobRatchetedChain bobRatchetedSt)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core (rngAt acceptAt wireAt40_canon not_gamma_encOut_ns0_at1 decomp45_raw seg40_shape take40_split_not_knownBaseKey split81_no_leak)
attribute [local irreducible] setupPublic setupSecret
theorem at?_pqEv_encNextTr (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq j : Nat) : ((encNextTr tr₂ me sIdx stA cl pq).at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = (tr₂.at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) := by
  unfold encNextTr encPreSaltTr; dsimp only
  rw [at?_append_other_eq' _ (NetE _) rfl, at?_append_other_eq' _ (TRStE _ _) rfl, at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (TREvE _) rfl, at?_append_other_eq' _ (NetE _) rfl, at?_append_other_eq' _ (RndE _) rfl, at?_append_other_eq' _ (RndE _) rfl]
theorem at?_pqEv_iniAliceStartTr (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) : ((iniAliceStartTr tr a b o).at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = if j = tr.length + 5 then some ⟨DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys⟩ else (tr.at? j : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) := by
  unfold iniAliceStartTr; dsimp only
  rw [at?_append_other_eq' _ (TRStE _ _) rfl, at?_append_other_eq' _ (CEvE _) rfl, at?_append_other_eq' _ (TREvE _) rfl, at?_append_same_eq', at?_append_other_eq' _ (NetE _) rfl, at?_append_other_eq' _ (NetE _) rfl, at?_append_other_eq' _ (RndE _) rfl, at?_append_other_eq' _ (RndE _) rfl, at?_append_other_eq' _ (RndE _) rfl]; simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_append_entry_eq]
theorem aliceDone_tr_bob_pin {r : Records} {pre₀ mid₁ mid₂ mid₃ : List Move} {m₁ m₂ : Move} {tr₁ tr₂ tr₃ tr_bob : ExecTrace} {a₀ b₀ : Participant} {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {me₁ me₂ : Participant} {s₁ cl₁ pq₁ s₂ cl₂ pq₂ : Nat} {stA₁ stA₁' : DY.Libsignal.TripleRatchet.TRState} {a' b' : Participant} {ikA ikB spk pqpk : DY.Bytes} {opk : Option DY.Bytes} {ek ct : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys} {j : Nat} (hNe : r.alice ≠ r.bob) (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀) (htr₂ : tr₂ = (runMoves mid₁ (iniAliceStartTr tr₁ a₀ b₀ o₁)).1) (hmid₁ : MovesFrom InvisibleNoEffect (iniAliceStartTr tr₁ a₀ b₀ o₁) mid₁) (hm₁ : m₁.next tr₂ = encNextTr tr₂ me₁ s₁ stA₁ cl₁ pq₁) (htr₃ : tr₃ = (runMoves mid₂ (m₁.next tr₂)).1) (hmid₂ : MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂) (hm₂ : m₂.next tr₃ = encNextTr tr₃ me₂ s₂ stA₁' cl₂ pq₂) (htr_bob : tr_bob = (runMoves mid₃ (m₂.next tr₃)).1) (hmid₃ : MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃) (hEv : tr_bob.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a' b' ikA ikB spk pqpk opk ek ct keys) j) : j = tr₁.length + 5 ∧ a' = a₀ ∧ b' = b₀ ∧ ikA = o₁.ikA ∧ ikB = o₁.ikB ∧ spk = o₁.spk ∧ pqpk = o₁.pqpk ∧ opk = o₁.opk ∧ ek = o₁.ek ∧ ct = o₁.ct ∧ keys = o₁.keys := by
  rw [htr_bob, eventLoggedAt_of_movesFrom_invisibleNoEffect hmid₃, hm₂] at hEv
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent), at?_pqEv_encNextTr, ← Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent)] at hEv
  rw [htr₃, eventLoggedAt_of_movesFrom_invisibleNoEffect hmid₂, hm₁] at hEv
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent), at?_pqEv_encNextTr, ← Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent)] at hEv
  rw [htr₂, eventLoggedAt_of_movesFrom_invisibleNoEffect hmid₁] at hEv
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent), at?_pqEv_iniAliceStartTr] at hEv
  split at hEv
  · next hjeq => cases hEv; exact ⟨hjeq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [← Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent)] at hEv
    rw [htr₁, eventLoggedAt_of_movesFrom_invisibleNoEffect hpre₀] at hEv; exfalso
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hNe hEv with
      ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
theorem allSentNet_tr_bob {tr₁ tr₂ tr₃ tr_bob : ExecTrace} {a b : Participant} {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {mid₁ mid₂ mid₃ : List Move} {me₁ me₂ : Participant} {s₁ cl₁ pq₁ s₂ cl₂ pq₂ : Nat} {wr₁ wr₂ : Option (Nat × Nat)} {stA₁ stA₁' : DY.Libsignal.TripleRatchet.TRState} (htr₂ : tr₂ = (runMoves mid₁ (iniAliceStartTr tr₁ a b o₁)).1) (hmid₁ : MovesFrom InvisibleNoEffect (iniAliceStartTr tr₁ a b o₁) mid₁) (hm₁ : (Move.encrypt me₁ s₁ cl₁ pq₁ wr₁).next tr₂ = encNextTr tr₂ me₁ s₁ stA₁ cl₁ pq₁) (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt me₁ s₁ cl₁ pq₁ wr₁).next tr₂)).1) (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt me₁ s₁ cl₁ pq₁ wr₁).next tr₂) mid₂) (hm₂ : (Move.encrypt me₂ s₂ cl₂ pq₂ wr₂).next tr₃ = encNextTr tr₃ me₂ s₂ stA₁' cl₂ pq₂) (htr_bob : tr_bob = (runMoves mid₃ ((Move.encrypt me₂ s₂ cl₂ pq₂ wr₂).next tr₃)).1) (hmid₃ : MovesFrom InvisibleNoEffect ((Move.encrypt me₂ s₂ cl₂ pq₂ wr₂).next tr₃) mid₃) : AllSentNet tr₁.length (fun raw => raw = encOut tr₂ stA₁ cl₁ pq₁ ∨ raw = encOut tr₃ stA₁' cl₂ pq₂) tr_bob := by
  let P := fun raw => raw = encOut tr₂ stA₁ cl₁ pq₁ ∨ raw = encOut tr₃ stA₁' cl₂ pq₂
  have h1 : AllSentNet tr₁.length P (iniAliceStartTr tr₁ a b o₁) := by
    dsimp only [iniAliceStartTr]
    exact allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_of_xnoSent (Trace.append_le _ _) (allSentNet_self _ _) (xnoSent_append_other _ (CompTrace.RndE 32) rfl)) (xnoSent_append_other _ (CompTrace.RndE 32) rfl)) (xnoSent_append_other _ (CompTrace.RndE 32) rfl)) (xnoSent_append_other _ (CompTrace.NetE o₁.ek) rfl)) (xnoSent_append_other _ (CompTrace.NetE o₁.ct) rfl)) (xnoSent_append_other _ (CompTrace.PQEvE _) rfl)) (xnoSent_append_tr _ _ rfl)) (xnoSent_append_other _ (CompTrace.CEvE _) rfl)) (xnoSent_append_other _ (CompTrace.TRStE a _) rfl)
  have h2 : AllSentNet tr₁.length P tr₂ := by have h := allSentNet_runMoves_of_movesFrom hmid₁ h1; rw [← htr₂] at h; exact h
  have h3 : AllSentNet tr₁.length P ((Move.encrypt me₁ s₁ cl₁ pq₁ wr₁).next tr₂) :=
    allSentNet_encrypt me₁ s₁ cl₁ pq₁ wr₁ tr₂ h2 (fun raw hraw => by
      rw [hm₁, lastSent_encNextTr] at hraw; exact Or.inl (Option.some.inj hraw).symm)
  have h4 : AllSentNet tr₁.length P tr₃ := by have h := allSentNet_runMoves_of_movesFrom hmid₂ h3; rw [← htr₃] at h; exact h
  have h5 : AllSentNet tr₁.length P ((Move.encrypt me₂ s₂ cl₂ pq₂ wr₂).next tr₃) :=
    allSentNet_encrypt me₂ s₂ cl₂ pq₂ wr₂ tr₃ h4 (fun raw hraw => by
      rw [hm₂, lastSent_encNextTr] at hraw; exact Or.inr (Option.some.inj hraw).symm)
  rw [htr_bob]; exact allSentNet_runMoves_of_movesFrom hmid₃ h5
private theorem encParsedMsg_counter_stA₁' (tr₁ tr₂ tr₃ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl₁ cl₂ pq : Nat) : (CompRFaithfulInner.encParsedMsg tr₃ (encSt tr₂ (iniAliceStartState tr₁ b o) cl₁) cl₂ pq).counter = 1 := rfl
private theorem encParsedMsg_ratchetKey_stA₁' (tr₁ tr₂ tr₃ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl₁ cl₂ pq : Nat) : (CompRFaithfulInner.encParsedMsg tr₃ (encSt tr₂ (iniAliceStartState tr₁ b o) cl₁) cl₂ pq).ratchetKey = DY.DiffieHellman.dhPk (iniAliceStartState tr₁ b o).dhs := rfl
private theorem encParsedMsg_pqRatchet (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : (CompRFaithfulInner.encParsedMsg tr stA cl pq).pqRatchet = (DY.Spqr.spqrSend stA.spqr (randTerm (tr.length + 1) cl)).2.2 := rfl
theorem bobStart_call3_pin
    {r : Records} {S : Sem} {g : Ghost} {pre₀ mid₁ mid₂ mid₃ ms_bob : List Move}
    {tr₁ tr₂ tr₃ tr_bob : ExecTrace} {hb₁ : DY.Libsignal.PQXDH.BundleHandles} {sh₁ s₁ cl₁ s₂ cl₂ : Nat}
    {w₁ w₂ : Option (Nat × Nat)} {b_bob a_bob : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx₂ : UInt32} {sh_bob : Nat}
    (hNe : r.alice ≠ r.bob) (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1)
    (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁ =
      iniAliceStartTr tr₁ r.alice r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none))
    (htr₂ : tr₂ = (runMoves mid₁ ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁)).1)
    (hmid₁ : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁).next tr₁) mid₁)
    (hm₁ : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂ =
      encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2))
    (htr₃ : tr₃ = (runMoves mid₂ ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂)).1)
    (hmid₂ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂) mid₂)
    (hm₂ : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃ =
      encNextTr tr₃ r.alice s₂ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2))
    (htr_bob : tr_bob = (runMoves mid₃ ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃)).1)
    (hmid₃ : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃) mid₃)
    (htr_bob_run : runTraceMoves r ms_bob = tr_bob) (hns_bob : ∀ m ∈ ms_bob, m.isSetup = false)
    (hreach_bob : (runTraceMoves r ms_bob).Reachable DY.Libsignal.Composed.reachability)
    (hnb_bob : CompSetupSecrecy.NoBrk r ms_bob)
    (hnoleak_bob : ∀ v ∈ runVis r ms_bob, v.kind ≠ .leak)
    (hm₃_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).vis tr_bob)) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let stA₁' := encSt tr₂ stA₁ cl₁
    ∃ spqr₂' : DY.Bytes, (∀ j : Nat,
        (((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).at? j : Option TRStEntry) =
          if j = ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).length - 1
          then some (TRStE r.bob (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1))
          else (tr_bob.at? j : Option TRStEntry)) ∧
      gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes ∧
      (DY.Spqr.spqrRecv (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A)
        (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂' := by
  dsimp only
  obtain ⟨o₁, ho₁⟩ : ∃ o₁, o₁ = iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none := ⟨_, rfl⟩
  obtain ⟨stA₁, hstA₁⟩ : ∃ stA₁, stA₁ = iniAliceStartState tr₁ r.bob o₁ := ⟨_, rfl⟩
  obtain ⟨stA₁', hstA₁'⟩ : ∃ stA₁', stA₁' = encSt tr₂ stA₁ cl₁ := ⟨_, rfl⟩
  rw [← ho₁] at hm₀ hm₁ hm₂ ⊢; rw [← hstA₁] at hm₁ hm₂ ⊢; rw [← hstA₁'] at hm₂ ⊢
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  obtain ⟨w_bob, -, hγ_raw⟩ := Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull.bobStartOk_of_rpk_forall2 hp40 hm₃_vis
  have hsent_mac : ∃ t me peer dhs ns m_pt, t + 6 < tr_bob.length ∧ tr_bob.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.Sent me peer dhs ns m_pt) (t + 3) ∧ Symbolic.Swarm.COMPOSED.CompInv.NetAt tr_bob w_bob.raw (t + 6) ∧ Symbolic.Swarm.COMPOSED.CompInv.AliceMatch tr_bob w_bob.ikAPk (DY.DiffieHellman.dhPk w_bob.ikB) (DY.PQKem.kemPk w_bob.pqsk) w_bob.ek w_bob.ct w_bob.keys t := by
    subst htr_bob_run; exact BobStartOk.sentMac_of_no_leak hNe hns_bob hreach_bob hnb_bob hnoleak_bob w_bob
  have hspk_run : (runTraceMoves r ms_bob).at? kh.spk = some (TR.StE b_bob { kind := .signedPrekey, sk := w_bob.spk }) := by
    rw [htr_bob_run]; exact w_bob.hspk
  have hS : Symbolic.Swarm.COMPOSED.CompInv.SPKAt (runTraceMoves r ms_bob) b_bob w_bob.spk := (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable _ hreach_bob).stOK b_bob
      { kind := .signedPrekey, sk := w_bob.spk } kh.spk hspk_run
  obtain ⟨hb_bob, hspk_eq, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hNe hns_bob hS
  obtain ⟨t, me, peer, dhs, ns, m_pt, _, hsent_ev, hnet_raw, j, a', b', spk', opk', hjt, hAlice_ev⟩ := hsent_mac
  have htr₂' : tr₂ = (runMoves mid₁ (iniAliceStartTr tr₁ r.alice r.bob o₁)).1 := by rw [← hm₀]; exact htr₂
  have hmid₁' : MovesFrom InvisibleNoEffect (iniAliceStartTr tr₁ r.alice r.bob o₁) mid₁ := by rw [← hm₀]; exact hmid₁
  have hm₁_raw : (Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) w₁).next tr₂ =
      encNextTr tr₂ r.alice s₁ (iniAliceStartState tr₁ r.bob o₁) cl₁ (tr₂.length + 2) := by rw [← hstA₁]; exact hm₁
  have hm₂_raw : (Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) w₂).next tr₃ =
      encNextTr tr₃ r.alice s₂ (encSt tr₂ (iniAliceStartState tr₁ r.bob o₁) cl₁) cl₂ (tr₃.length + 2) := by
    rw [← hstA₁, ← hstA₁']; exact hm₂
  obtain ⟨hj_eq, _, _, hikA_eq, hikB_eq, _, _, _, _, _, hkeys_eq⟩ := aliceDone_tr_bob_pin hNe htr₁ hpre₀ htr₂' hmid₁' hm₁_raw htr₃ hmid₂ hm₂_raw htr_bob hmid₃ hAlice_ev
  have hikA_pub : o₁.ikA = setupPublic r 0 := by
    rw [ho₁]; dsimp only [iniAliceOut]; rw [CompSetupSecrecy.setupSecret_0 hNe, CompSetupSecrecy.setupPublic_0 hNe]
  have hikB_pub : o₁.ikB = setupPublic r 2 := by rw [ho₁]; rfl
  have ha_bob : a_bob = r.alice := by
    have hreg_run : (runTraceMoves r ms_bob).EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered a_bob w_bob.ikAPk w_bob.vkA w_bob.honest) regIdxA := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent), htr_bob_run]; exact w_bob.hreg
    have hreg_setup := CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms_bob hns_bob _ regIdxA rfl hreg_run
    rcases CompPrefixInvBundle.setupTrace_eventLoggedAt_identityRegistered hNe hreg_setup with
      ⟨_, ha_eq, _, _, _⟩ | ⟨_, _, hik_bob, _, _⟩
    · exact ha_eq
    · exfalso
      have h02 : setupPublic r 0 = setupPublic r 2 := by rw [← hikA_pub, ← hikA_eq, hik_bob]
      rw [CompSetupSecrecy.setupPublic_0 hNe, CompSetupSecrecy.setupPublic_2 hNe] at h02
      exact nomatch (CompTrace.mkRand_inj (Symbolic.Swarm.COMPOSED.CompTermAlgebra.dhPk_inj h02)).1
  have hget_sent : tr_bob.getEventAt DY.Libsignal.TripleRatchet.TREvent (t + 3) = some (DY.Libsignal.TripleRatchet.TREvent.Sent me peer dhs ns m_pt) := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getEventAt_eq_at?,
      (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at? _ _ _ _).mp hsent_ev]
  have hSent_bob := allSentNet_tr_bob htr₂' hmid₁' hm₁_raw htr₃ hmid₂ hm₂_raw htr_bob hmid₃
  obtain ⟨raw', _, hnet_raw', hraw'_cases⟩ := hSent_bob (t + 3) _ (by omega) hget_sent rfl
  rw [← hstA₁, ← hstA₁'] at hraw'_cases
  have hraw_eq_raw' : w_bob.raw = raw' := by
    unfold Symbolic.Swarm.COMPOSED.CompInv.NetAt at hnet_raw hnet_raw'
    rw [show t + 3 + 3 = t + 6 by omega, hnet_raw] at hnet_raw'; cases hnet_raw'; rfl
  have hraw_eq : w_bob.raw = encOut tr₃ stA₁' cl₂ (tr₃.length + 2) := by
    rw [← hraw_eq_raw'] at hraw'_cases
    rcases hraw'_cases with hraw₁ | hraw₂
    · exfalso; rw [hraw₁] at hγ_raw
      exact not_gamma_encOut_ns0_at1 S g tr₂ stA₁ cl₁ (tr₂.length + 2) p40
        (by rw [hstA₁]; rfl) (by rw [hstA₁]; rfl) hγ_raw (wireAt40_canon hp40)
    · exact hraw₂
  have hmsg_eq : w_bob.msg = CompRFaithfulInner.encParsedMsg tr₃ stA₁' cl₂ (tr₃.length + 2) := by
    have hp := w_bob.hparse; rw [hraw_eq, ← census_encOut_eq, CompRFaithfulInner.parseTrSignalMsg_encOut] at hp
    exact (Option.some.inj hp).symm
  have hcnt1 : w_bob.msg.counter = 1 := by rw [hmsg_eq, hstA₁', hstA₁, encParsedMsg_counter_stA₁']
  have hrk_eq : w_bob.msg.ratchetKey = DY.DiffieHellman.dhPk stA₁.dhs := by
    rw [hmsg_eq, hstA₁', hstA₁, encParsedMsg_ratchetKey_stA₁']
  have hpq_eq : w_bob.msg.pqRatchet = (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.2 := by
    rw [hmsg_eq, encParsedMsg_pqRatchet]
  have hnext_bob := bobStart_next_eq (sh := sh_bob) w_bob
  have hm₃_vis' : List.Forall₂ (EventMatchesEntry compI0 r S g) [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)]
      ((bobVis tr_bob ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob)
        mh (bobOpkPk b_bob kh tr_bob)).take sh_bob) := by rw [← bobStart_vis_eq]; exact hm₃_vis
  have hsh3 : 3 ≤ sh_bob := by
    have hlen := (xpl_forall₂_length hm₃_vis').symm
    rw [List.length_take] at hlen; simp only [List.length_cons, List.length_nil] at hlen; omega
  have hlt_bob : tr_bob.length <
      ((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).length := by
    rw [hnext_bob]; exact length_lt_bobStartTr w_bob
  have hrnd_bob : (((Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob).next tr_bob).at? tr_bob.length :
      Option DY.Random.ExecEntryT) = some (TR.RndE 32) := by rw [hnext_bob, at?_rnd_bobStartTr w_bob]; simp
  have hγ_rng41 : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes := gamma_rng_of_bobVis_forall2 hsh3 hlt_bob hrnd_bob hm₃_vis'
  have hc'_eq : w_bob.c' =
      { ratchetKey := w_bob.msg.ratchetKey,
        chainKey := (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk w_bob.msg.ratchetKey (setupSecret r 2)).2 (1 : UInt32).toNat)).1,
        index := (1 : UInt32) + 1, rIdx := 2 } := by
    have hc := w_bob.hcons; rw [hcnt1, hkeys_eq, hspk_eq] at hc
    unfold DY.Libsignal.TripleRatchet.consumeMessageKey at hc
    split at hc
    · cases hc
    · split at hc
      · cases hc
      · split at hc
        · cases hc
        · exact (congrArg Prod.snd (Option.some.inj hc)).symm
  obtain ⟨spqr₂', hspqr₂'_eq⟩ : ∃ spqr₂', w_bob.spqr' = spqr₂' := ⟨_, rfl⟩
  have hset : DY.Libsignal.TripleRatchet.setRecvChain (bobRatchetedSt a_bob (DY.DiffieHellman.dhPk w_bob.ikB) w_bob.ikAPk w_bob.keys w_bob.spk w_bob.msg.ratchetKey (randTerm tr_bob.length 32)).recv w_bob.c' = [w_bob.c'] := by
    unfold DY.Libsignal.TripleRatchet.setRecvChain bobRatchetedSt bobRatchetedChain; rw [hc'_eq]; simp
  have hst_eq : bobFinalSt tr_bob a_bob w_bob = bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1 := by
    unfold bobFinalSt bobSt81; dsimp only; rw [hset]; dsimp only [bobRatchetedSt]
    rw [hspqr₂'_eq, hikB_eq, hikB_pub, hikA_eq, hikA_pub, hkeys_eq, hspk_eq, hc'_eq, hrk_eq, ha_bob]
  refine ⟨spqr₂', fun j => ?_, hγ_rng41, ?_⟩
  · rw [hnext_bob, at?_trSt_bobStartTr w_bob, ← hnext_bob, hst_eq]
    split
    · rw [hb_bob]
    · rfl
  · have hsp := w_bob.hspqr; rw [hkeys_eq, hpq_eq, hspqr₂'_eq] at hsp
    dsimp only [bobRatchetedSt] at hsp; rw [hsp]; rfl
abbrev Split81PrefixAtomGen (r : Records) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace)
    (cl₁ cl₂ cl₅ : Nat) (PBob : DY.Bytes → Prop) (u : DY.Bytes) : Prop :=
  let o₁ := Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := Census443Defs.iniAliceStartState tr₁ r.bob o₁
  let stA₁' := Census443Defs.encSt tr₂ stA₁ cl₁
  let o₂ := Census443Defs.iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₂ := Census443Defs.iniAliceStartState tr₄ r.bob o₂
  u = o₁.ek ∨ u = o₁.ct ∨ u = Census443Defs.encOut tr₂ stA₁ cl₁ (tr₂.length + 2) ∨ u = Census443Defs.encOut tr₃ stA₁' cl₂ (tr₃.length + 2) ∨ u = o₂.ek ∨ u = o₂.ct ∨ u = Census443Defs.encOut tr₅ stA₂ cl₅ (tr₅.length + 2) ∨ u = randTerm tr₂.length 32 ∨ u = randTerm tr₃.length 32 ∨ u = randTerm tr₅.length 32 ∨ u = serAlice r stA₁ ∨ u = serAlice r stA₁' ∨ u = serAlice r (Census443Defs.encSt tr₃ stA₁' cl₂) ∨ u = serAlice r stA₂ ∨ u = serAlice r (Census443Defs.encSt tr₅ stA₂ cl₅) ∨ PBob u
theorem split81PrefixEnum_gen_of_mp_links {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {b1 b2 b5 : List MachineEvent} (PBob : ExecTrace → DY.Bytes → Prop) (hBob : ∀ (tr_bob : ExecTrace) (spqrMsgIdx₂ : UInt32) (spqr₂' : DY.Bytes), gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes → (DY.Spqr.spqrRecv (DY.Spqr.spqrInit (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂' → PBob tr_bob (serBob r (bobSt81 r (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) tr_bob (DY.DiffieHellman.dhPk (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)).dhs) spqr₂' 1))) (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1) (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2) (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] b5) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms' (((((seg 0 35 ++ b1) ++ b2) ++ seg 40 3) ++ seg 43 35) ++ b5)) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : ∃ (tr_bob : ExecTrace), gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes ∧ ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), Split81PrefixAtomGen r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ (PBob tr_bob) u ∨ u ∈ storedSecrets (runTraceMoves r ms') := by
  obtain ⟨ms₄₃, pre₄, mid₅, post₅, m₄, me₅, sIdx₅, cl₅', pq₅, e₅, c₅, tr₄', tr₅',
    hms, hmp₄₃, htr₄_raw, htr₅', _, _, hpre₄, hmid₅, hpost₅, _, _, _⟩ := decomp45_raw hc5 hmp
  have hmp₄₃' : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₄₃ (((seg 0 35 ++ b1) ++ b2) ++ [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)]) := by
    rwa [← seg40_shape]
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  obtain ⟨ms₄₀, pre₃, post₃, b_bob, a_bob, kh, regIdxA, mh, pqIdx, spqrMsgIdx₂, sh_bob,
    hms₄₃, hmp₄₀, _, hpre₃, hpost₃, _, hm₃_vis⟩ :=
    Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone.matchedPrefix_rpk_bobStart_only compI0 r S g _ (wireAt 40) (rngAt 41) (acceptAt 42) ms₄₃ p40 wireAt40_head? hp40
      (fun _ hmp₀ => take40_split_not_knownBaseKey hc1 hc2 hmp₀) hmp₄₃'
  obtain ⟨pre₀, mid₁, mid₂, post₂, m₀, m₁, m₂, hms₄₀, hpre₀, hmid₁, hmid₂, hpost₂, _, _, _⟩ := decomp40_moves hc1 hc2 hmp₄₀
  let m₃ := Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx₂ sh_bob
  obtain ⟨m₅, hm₅_def⟩ : ∃ m₅, m₅ = Move.encrypt me₅ sIdx₅ cl₅' pq₅ (some (e₅, c₅)) := ⟨_, rfl⟩; rw [← hm₅_def] at hms hpost₅
  let mid₃ := post₂ ++ pre₃; let mid₄ := post₃ ++ pre₄
  let tr_bob := (runMoves mid₃ (m₂.next (runMoves mid₂
    (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1
  have hrun_ms₄₀ : runTraceMoves r ms₄₀ = (runMoves post₂ (m₂.next (runMoves mid₂
      (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1 := by
    rw [hms₄₀, xpl_runTrace_eq]; simp only [List.append_assoc, List.cons_append, runMoves_append_fst, runMoves]
  have htr_bob_eq : (runMoves pre₃ (runTraceMoves r ms₄₀)).1 = tr_bob := by dsimp only [tr_bob, mid₃]; rw [hrun_ms₄₀, runMoves_append_fst]
  rw [htr_bob_eq] at hpost₃ hm₃_vis
  have hmid₃ : MovesFrom InvisibleNoEffect (m₂.next (runMoves mid₂
      (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1) mid₃ := by
    dsimp only [mid₃]; rw [movesFrom_append, ← hrun_ms₄₀]; exact ⟨hpost₂, hpre₃⟩
  have hrun_ms₄₃ : runTraceMoves r ms₄₃ = (runMoves post₃ (m₃.next tr_bob)).1 := by rw [hms₄₃, xpl_runTrace_eq, runMoves_append_fst, runMoves_append_fst, ← xpl_runTrace_eq r ms₄₀, runMoves, htr_bob_eq]
  have htr₄'_eq : tr₄' = (runMoves mid₄ (m₃.next tr_bob)).1 := by dsimp only [mid₄]; rw [htr₄_raw, hrun_ms₄₃, runMoves_append_fst]
  rw [htr₄'_eq] at hmid₅ htr₅'; rw [htr₅'] at hpost₅
  have hmid₄ : MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄ := by dsimp only [mid₄]; rw [movesFrom_append, ← hrun_ms₄₃]; exact ⟨hpost₃, hpre₄⟩
  have hms' : ms' = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅ := by dsimp only [mid₃, mid₄, m₃]; rw [hms, hms₄₃, hms₄₀]; simp only [List.append_assoc, List.cons_append]
  obtain ⟨hb₁, hb₂, sh₁, sh₂, s₁, s₂, s₅, rfl, rfl, rfl, rfl, rfl, htr₁, htr₂, htr₃, htr₄, htr₅,
    hm₀, hm₁, hm₂, hm₄, hm₅⟩ := decomp81_links_pin hms' hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅
    (fun _ _ _ _ _ _ h => by dsimp only [m₃] at h; cases h)
    (fun _ _ _ _ _ h => by dsimp only [m₃] at h; cases h) hlinks
  have htr_bob_pin : tr_bob = (runMoves mid₃ ((Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2)
      (some (tr₁.length + 3, tr₁.length + 4))).next tr₃)).1 := by
    dsimp only [tr_bob]; rw [← htr₁, ← htr₂, ← htr₃]
  rw [← htr₁] at hmid₁; rw [← htr₁, ← htr₂] at hmid₂; rw [← htr₁, ← htr₂, ← htr₃] at hmid₃; rw [← htr_bob_pin] at htr₄; rw [← htr₄] at hmid₅ hpost₅; rw [← htr₅] at hpost₅
  let ms_bob := pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁ ++ Move.encrypt r.alice s₁ cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂ ++ Move.encrypt r.alice s₂ cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₃
  have htr_bob_run : runTraceMoves r ms_bob = tr_bob := by dsimp only [ms_bob]; rw [xpl_runTrace_eq]; simp only [List.append_assoc, List.cons_append, runMoves_append_fst, runMoves, ← htr₁, ← htr₂, ← htr₃, ← htr_bob_pin]
  have hms'_split : ms' = ms_bob ++ (m₃ :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅ ++ Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4)) :: post₅) := by
    dsimp only [ms_bob]; rw [hms']; simp only [List.append_assoc, List.cons_append]
  have ⟨hNe, hns_bob, hreach_bob, hnb_bob, hnoleak_bob⟩ := Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull.prefix_clean_hyps_of_matchedPrefix
      (ms₁ := ms_bob)
      (ms₂ := m₃ :: mid₄ ++ Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅ ++ Move.encrypt r.alice s₅ cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4)) :: post₅) hmp hlinks.1
      (split81_no_leak hc1 hc2 hc5)
      hms'_split
  obtain ⟨spqr₂', hm₃, hγ_bob, hspqr_bob⟩ := bobStart_call3_pin hNe htr₁ hpre₀ hm₀ htr₂ hmid₁ hm₁ htr₃ hmid₂ hm₂ htr_bob_pin hmid₃ htr_bob_run hns_bob hreach_bob hnb_bob hnoleak_bob hm₃_vis
  refine ⟨tr_bob, hγ_bob, ?_⟩
  rw [hms']; exact split81PrefixEnumOn_of_shape_gen hNe htr₁ htr₂ htr₃ htr_bob_pin htr₄ htr₅ hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅ hm₀ hm₁ hm₂ hm₃ hm₄ hm₅ (hBob tr_bob spqrMsgIdx₂ spqr₂' hγ_bob hspqr_bob)
theorem split81PrefixEnumOn_of_mp_links {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {b1 b2 b5 : List MachineEvent} (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1) (hc2 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2) (hc5 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] b5) (hmp : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms' (((((seg 0 35 ++ b1) ++ b2) ++ seg 40 3) ++ seg 43 35) ++ b5)) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : Split81PrefixEnumOn r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := by
  let o₁ := Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := Census443Defs.iniAliceStartState tr₁ r.bob o₁
  let stA₁' := Census443Defs.encSt tr₂ stA₁ cl₁
  obtain ⟨_, _, h⟩ := split81PrefixEnum_gen_of_mp_links
    (fun _ u => ∃ (tr_bob : ExecTrace) (spqrMsgIdx₂ : UInt32) (spqr₂' : DY.Bytes),
      gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes ∧
      (DY.Spqr.spqrRecv (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂' ∧
      u = serBob r (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' 1))
    (fun tr_bob spqrMsgIdx₂ spqr₂' hγ hspqr => ⟨tr_bob, spqrMsgIdx₂, spqr₂', hγ,
      by dsimp only [o₁, stA₁, stA₁']; rw [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq]; exact hspqr,
      by dsimp only [o₁, stA₁]; rw [census_iniAliceOut_eq, census_iniAliceStartState_eq]⟩) hc1 hc2 hc5 hmp hlinks
  exact h
theorem split81PrefixEnum : Split81PrefixEnum := by
  intro r S g _ ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ _ _ hinv hlinks
  obtain ⟨b1, b2, b5, hc1, hc2, hc5, hmp⟩ := hinv.mp.2.2.2.2.2
  exact split81PrefixEnumOn_of_mp_links hc1 hc2 hc5 (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp) hlinks
theorem split81PrefixEnum_of_pre {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hpre : WS81Idx1Pre r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : Split81PrefixEnumOn r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := by
  obtain ⟨b1, b2, b5, hc1, hc2, hc5, hmp⟩ := hpre.mp.2.2.2.2.2
  exact split81PrefixEnumOn_of_mp_links hc1 hc2 hc5 (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp) hpre.links
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum
