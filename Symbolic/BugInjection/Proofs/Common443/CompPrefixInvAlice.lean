/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED.CompTrace Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
abbrev _root_.DY.Libsignal.Composed.Refinement.BundleCore := DY.Libsignal.Composed.Refinement.BundleSignedKeysMatch
abbrev _root_.DY.Libsignal.Composed.Refinement.BundleMatches := DY.Libsignal.Composed.Refinement.PreKeyBundleLayoutMatches
def iniAliceOut (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : DY.Libsignal.PQXDH.AliceHandshakeOut :=
  let ek := randTerm tr.length 32; let e := randTerm (tr.length + 1) 32;
  { ikA := DY.DiffieHellman.dhPk ikA, ikB := ikBPk, spk := spkPk, pqpk := pqPk, opk, ek := DY.DiffieHellman.dhPk ek, ct := (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikBPk spkPk pqPk opk e).1, keys := (DY.Libsignal.PQXDH.aliceAgreement ikA ek ikBPk spkPk pqPk opk e).2 }
def iniAliceStartState (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : DY.Libsignal.TripleRatchet.TRState :=
  let dhsA := randTerm (tr.length + 2) 32; let (rkA, cksA) := DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk dhsA;
  { peer := b, myIk := DY.Libsignal.PQXDH.serializedIk o.ikA, peerIk := DY.Libsignal.PQXDH.serializedIk o.ikB, rk := rkA, dhs := dhsA, cks := cksA, ns := 0, pn := 0, sid := Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk, initiator := true, rIdx := 1, recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }], spqr := DY.Spqr.spqrInit o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B }
def iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : ExecTrace :=
  let dhsA := randTerm (tr.length + 2) 32; let stA := iniAliceStartState tr b o;
  ((((((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append (NetE o.ek)).append (NetE o.ct)).append (PQEvE (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))).append (TREvE (DY.Libsignal.TripleRatchet.TREvent.InitSession a b (DY.DiffieHellman.dhPk dhsA) o.spk))).append (CEvE (DY.Libsignal.Composed.ComposedEvent.HandshakeSession (stA.sessionInfo a) (tr.length + 5)))).append (TRStE a stA)
theorem eventIdx_isAliceDone_self (tr : ExecTrace) : eventIdx isAliceDone tr tr = none := by simp [eventIdx, newIndices]
theorem eventIdx_isAliceDone_append_rnd (tr : ExecTrace) (n : Nat) : eventIdx isAliceDone tr (tr.append (RndE n)) = none := by
  have hni : newIndices tr (tr.append (RndE n)) = [tr.length] := by
    unfold newIndices; rw [length_append_entry_eq, Nat.add_sub_cancel_left]; rfl
  have hge : ((tr.append (RndE n)).getEventAt DY.Libsignal.PQXDH.PQXDHEvent tr.length) = none := by
    rw [getEventAt_eq_at?, Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj tr (RndE n) rfl none rfl]
  simp [eventIdx, hni, hge]
theorem bind_aliceHandshake_at' {Inv : ExecTrace → Prop} {α : Type} (a b : Participant) (idStateIdx regIdxB : Nat) (bh : DY.Libsignal.PQXDH.BundleHandles) {f : DY.Libsignal.PQXDH.AliceHandshakeOut → Traceful α} (tr : ExecTrace) (hInv : Inv tr) (habort : Inv (tr.append (RndE 32))) (hf : ∀ (ikA ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (honest : Bool), PQXDHStoredAt tr a { kind := .identity, sk := ikA } idStateIdx → tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regIdxB → NetMsgAt spk bh.spk tr → NetMsgAt spkSig bh.spkSig tr → NetMsgAt pqpk bh.pqpk tr → NetMsgAt pqpkSig bh.pqpkSig tr → DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spk) spkSig = true → DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqpk) pqpkSig = true → ((bh.opk = none ∧ opk = none) ∨ (∃ idx o, bh.opk = some idx ∧ opk = some o ∧ NetMsgAt o idx tr)) → DY.Libsignal.PQXDH.x25519LowOrder spk = false → (opk.all fun o => !DY.Libsignal.PQXDH.x25519LowOrder o) = true → Inv ((f (iniAliceOut tr ikA ikB spk pqpk opk)).run ((tr.append (RndE 32)).append (RndE 32))).2.val) : Inv (((DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB bh >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; rw [run_bind_assoc_snd]; apply bind_getKey_at a idStateIdx .identity tr hInv; intro ikA hstA; rw [run_bind_assoc_snd]; apply bind_lookupIdentity_at b regIdxB tr hInv; intro ikB vkB honest hregB; rw [run_bind_assoc_snd]; apply bind_receiveMessage_at bh.spk tr hInv; intro spk hspk _; rw [run_bind_assoc_snd]; apply bind_receiveMessage_at bh.spkSig tr hInv; intro spkSig hspkSig _; rw [run_bind_assoc_snd]; apply bind_receiveMessage_at bh.pqpk tr hInv; intro pqpk hpq _; rw [run_bind_assoc_snd]; apply bind_receiveMessage_at bh.pqpkSig tr hInv; intro pqpkSig hpqSig _; rw [run_bind_assoc_snd]; apply bind_guardP_at _ tr hInv; intro hv1; rw [run_bind_assoc_snd]; apply bind_guardP_at _ tr hInv; intro hv2
  rcases hbh : bh.opk with _ | opkIdx
  · change Inv ((((Pure.pure none : Traceful (Option DY.Bytes)) >>= aliceHandshakeJp ikA ikB spk pqpk >>= f).run tr).2.val); rw [run_bind_assoc_snd, run_pure_bind_snd]
    exact bind_aliceHandshakeJp_at ikA ikB spk pqpk none tr habort fun hlow _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig none honest hstA hregB hspk hspkSig hpq hpqSig hv1 hv2 (.inl ⟨hbh, rfl⟩) hlow rfl
  · change Inv ((((Network.receiveMessage opkIdx >>= fun o => (Pure.pure (some o) : Traceful (Option DY.Bytes)) >>= aliceHandshakeJp ikA ikB spk pqpk) >>= f).run tr).2.val); rw [run_bind_assoc_snd]; apply bind_receiveMessage_at opkIdx tr hInv; intro o hopk _; rw [run_bind_assoc_snd, run_pure_bind_snd]
    exact bind_aliceHandshakeJp_at ikA ikB spk pqpk (some o) tr habort fun hlow hlo2 =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig (some o) honest hstA hregB hspk hspkSig hpq hpqSig hv1 hv2 (.inr ⟨opkIdx, o, hbh, rfl, hopk⟩) hlow hlo2
theorem aliceStart_inv_of_isAliceDone {tr : ExecTrace} {a b : Participant} {idS regB : Nat} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat} (hdone : (eventIdx isAliceDone tr ((Move.aliceStart a b idS regB hb shown).next tr)).isSome = true) : ∃ (ikA ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (honest : Bool), PQXDHStoredAt tr a { kind := .identity, sk := ikA } idS ∧ tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regB ∧ NetMsgAt spk hb.spk tr ∧ NetMsgAt spkSig hb.spkSig tr ∧ NetMsgAt pqpk hb.pqpk tr ∧ NetMsgAt pqpkSig hb.pqpkSig tr ∧ DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spk) spkSig = true ∧ DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqpk) pqpkSig = true ∧ ((hb.opk = none ∧ opk = none) ∨ (∃ idx o, hb.opk = some idx ∧ opk = some o ∧ NetMsgAt o idx tr)) ∧ DY.Libsignal.PQXDH.x25519LowOrder spk = false ∧ (opk.all fun o => !DY.Libsignal.PQXDH.x25519LowOrder o) = true ∧ (Move.aliceStart a b idS regB hb shown).next tr = iniAliceStartTr tr a b (iniAliceOut tr ikA ikB spk pqpk opk) := by
  let P : ExecTrace → Prop := fun t => (eventIdx isAliceDone tr t).isSome = true →
    ∃ (ikA ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (honest : Bool), PQXDHStoredAt tr a { kind := .identity, sk := ikA } idS ∧ tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regB ∧ NetMsgAt spk hb.spk tr ∧ NetMsgAt spkSig hb.spkSig tr ∧ NetMsgAt pqpk hb.pqpk tr ∧ NetMsgAt pqpkSig hb.pqpkSig tr ∧ DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeEC spk) spkSig = true ∧ DY.Signature.verify vkB (DY.Libsignal.PQXDH.encodeKEM pqpk) pqpkSig = true ∧ ((hb.opk = none ∧ opk = none) ∨ (∃ idx o, hb.opk = some idx ∧ opk = some o ∧ NetMsgAt o idx tr)) ∧
      DY.Libsignal.PQXDH.x25519LowOrder spk = false ∧ (opk.all fun o => !DY.Libsignal.PQXDH.x25519LowOrder o) = true ∧
      t = iniAliceStartTr tr a b (iniAliceOut tr ikA ikB spk pqpk opk);
  suffices hP : P ((Move.aliceStart a b idS regB hb shown).next tr) from hP hdone
  unfold Move.next Move.act; rw [XplSteps.xrun_bind_unit]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at' a b idS regB hb tr
    (fun h => by rw [eventIdx_isAliceDone_self] at h; cases h)
    (fun h => by rw [eventIdx_isAliceDone_append_rnd] at h; cases h)
    fun ikA ikB vkB spk spkSig pqpk pqpkSig opk honest hstA hregB hspk hspkSig hpq hpqSig hv1 hv2 hopk hlow hlo2 _ =>
      ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest, hstA, hregB, hspk, hspkSig, hpq, hpqSig, hv1, hv2, hopk, hlow, hlo2,
        aliceStart_cont_run_snd_eq tr a b (iniAliceOut tr ikA ikB spk pqpk opk)⟩
open XplSteps in
theorem at?_append_other_eq {E E' : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E'] (tr : ExecTrace) (e : E) (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E') = none) (j : Nat) : ((tr.append e).at? j : Option E') = (tr.at? j : Option E') := by
  by_cases hj : j < tr.length
  · exact at?_append_of_lt tr e hj
  · by_cases hjeq : j = tr.length
    · subst hjeq; rw [Symbolic.Swarm.CREF.at?_append_length, hnone, Symbolic.Swarm.CREF.at?_ge_length tr (Nat.le_refl _)]
    · rw [Symbolic.Swarm.CREF.at?_ge_length (tr.append e) (by rw [length_append_entry_eq]; omega),
        Symbolic.Swarm.CREF.at?_ge_length tr (by omega)]
@[simp] private theorem length_append_entry {T : Type} [ExecTraceTypes.Has T] (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 :=
  length_append_entry_eq tr x
private theorem at?_append_eq_of_eq {T S : Type} [ExecTraceTypes.Has T] [ExecTraceTypes.Has S] (tr : ExecTrace) (x : S) {i : Nat} (hi : i = tr.length) : ((tr.append x).at? i : Option T) = TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) := by
  subst hi; exact Symbolic.Swarm.CREF.at?_append_length tr x
local macro "at?_iniAliceStartTr_tac" : tactic =>
  `(tactic| (dsimp only [iniAliceStartTr]; repeat (rw [at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp [length_append_entry]; try omega)]; rfl))
theorem newIndices_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : newIndices tr (iniAliceStartTr tr a b o) = [tr.length, tr.length + 1, tr.length + 2, tr.length + 3, tr.length + 4, tr.length + 5, tr.length + 6, tr.length + 7, tr.length + 8] := by
  unfold newIndices
  have hlen : (iniAliceStartTr tr a b o).length = tr.length + 9 := by
    dsimp only [iniAliceStartTr]; simp only [length_append_entry]
  rw [hlen, Nat.add_sub_cancel_left]; simp [List.range', Nat.add_assoc]
theorem newRandoms_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : newRandoms tr (iniAliceStartTr tr a b o) = [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) 32, 32), (randTerm (tr.length + 2) 32, 32)] := by
  unfold newRandoms; rw [newIndices_iniAliceStartTr]
  have h0 : ((iniAliceStartTr tr a b o).at? tr.length : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_iniAliceStartTr_tac
  have h1 : ((iniAliceStartTr tr a b o).at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_iniAliceStartTr_tac
  have h2 : ((iniAliceStartTr tr a b o).at? (tr.length + 2) : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_iniAliceStartTr_tac
  have h3 : ((iniAliceStartTr tr a b o).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by at?_iniAliceStartTr_tac
  have h4 : ((iniAliceStartTr tr a b o).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by at?_iniAliceStartTr_tac
  have h5 : ((iniAliceStartTr tr a b o).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by at?_iniAliceStartTr_tac
  have h6 : ((iniAliceStartTr tr a b o).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by at?_iniAliceStartTr_tac
  have h7 : ((iniAliceStartTr tr a b o).at? (tr.length + 7) : Option DY.Random.ExecEntryT) = none := by at?_iniAliceStartTr_tac
  have h8 : ((iniAliceStartTr tr a b o).at? (tr.length + 8) : Option DY.Random.ExecEntryT) = none := by at?_iniAliceStartTr_tac
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, RndE]
theorem getEventAt_pq_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : let tr' := iniAliceStartTr tr a b o; tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent tr.length = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 1) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 2) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 3) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 4) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 5) = some (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 6) = none ∧ tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 7) = none ∧
    tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((iniAliceStartTr tr a b o).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by at?_iniAliceStartTr_tac
  have h1 : ((iniAliceStartTr tr a b o).at? (tr.length + 1) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by at?_iniAliceStartTr_tac
  have h2 : ((iniAliceStartTr tr a b o).at? (tr.length + 2) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by at?_iniAliceStartTr_tac
  have h3 : ((iniAliceStartTr tr a b o).at? (tr.length + 3) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by at?_iniAliceStartTr_tac
  have h4 : ((iniAliceStartTr tr a b o).at? (tr.length + 4) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by at?_iniAliceStartTr_tac
  have h5 : ((iniAliceStartTr tr a b o).at? (tr.length + 5) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) =
      some (PQEvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)) := by at?_iniAliceStartTr_tac
  have h6 : ((iniAliceStartTr tr a b o).at? (tr.length + 6) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by at?_iniAliceStartTr_tac
  have h7 : ((iniAliceStartTr tr a b o).at? (tr.length + 7) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by at?_iniAliceStartTr_tac
  have h8 : ((iniAliceStartTr tr a b o).at? (tr.length + 8) : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none := by at?_iniAliceStartTr_tac
  simp [getEventAt_eq_at?, h0, h1, h2, h3, h4, h5, h6, h7, h8, PQEvE]
theorem eventIdx_isAliceDone_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : eventIdx isAliceDone tr (iniAliceStartTr tr a b o) = some (tr.length + 5) := by unfold eventIdx; rw [newIndices_iniAliceStartTr]; obtain ⟨h0, h1, h2, h3, h4, h5, _, _, _⟩ := getEventAt_pq_iniAliceStartTr tr a b o; simp [h0, h1, h2, h3, h4, h5, isAliceDone]
theorem aliceVis_iniAliceStartTr (tr : ExecTrace) (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hb : DY.Libsignal.PQXDH.BundleHandles) : aliceVis tr (iniAliceStartTr tr a b o) hb = { kind := .recv, terms := received tr ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList), layout := .bundle, anchor := none } :: rngEntry (randTerm tr.length 32) :: (kyberCoinEntries (randTerm (tr.length + 1) 32) ++ [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by simp [aliceVis, aliceDraws, newRandoms_iniAliceStartTr, eventIdx_isAliceDone_iniAliceStartTr]
theorem netMsgAt_ek_iniAliceStartTr (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : NetMsgAt o.ek (tr.length + 3) (iniAliceStartTr tr a b o) := by unfold NetMsgAt; at?_iniAliceStartTr_tac
theorem netMsgAt_ct_iniAliceStartTr (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : NetMsgAt o.ct (tr.length + 4) (iniAliceStartTr tr a b o) := by unfold NetMsgAt; at?_iniAliceStartTr_tac
theorem trStateStoredAt_iniAliceStartTr (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : TRStateStoredAt a (iniAliceStartState tr b o) (tr.length + 8) (iniAliceStartTr tr a b o) := by
  unfold iniAliceStartTr TRStateStoredAt; dsimp only
  exact Symbolic.Swarm.CREF.TR.at?_append_eq _ _ (by simp only [length_append_entry]; try omega)
theorem at?_trSt_iniAliceStartTr (tr : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) : ((iniAliceStartTr tr a b o).at? j : Option TRStEntry) = if j = tr.length + 8 then some (TRStE a (iniAliceStartState tr b o)) else (tr.at? j : Option TRStEntry) := by
  by_cases hj : j = tr.length + 8
  · subst hj; simp only [↓reduceIte]; exact trStateStoredAt_iniAliceStartTr tr a b o
  · simp only [hj, ↓reduceIte]; unfold iniAliceStartTr; dsimp only
    by_cases hlt : j < tr.length + 8
    · rw [at?_append_of_lt _ _ (by simp only [length_append_entry]; omega), at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by simp only [length_append_entry]; omega),
          Symbolic.Swarm.CREF.at?_ge_length tr (by omega)]
theorem at?_trSt_iniAliceStartTr_of_noTRState {tr : ExecTrace} (htr : NoTRState tr) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) : ((iniAliceStartTr tr a b o).at? j : Option TRStEntry) = if j = tr.length + 8 then some (TRStE a (iniAliceStartState tr b o)) else none := by rw [at?_trSt_iniAliceStartTr, htr j]
theorem getMessageSentAt_of_netMsgAt {tr : ExecTrace} {idx : Nat} {m : DY.Bytes} (h : NetMsgAt m idx tr) : tr.getMessageSentAt idx = some m := by
  rw [getMessageSentAt_eq_at?]; unfold NetMsgAt at h; rw [h]
theorem hb_opk_eq_none_of_bun_byte4 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr : ExecTrace} {hb : DY.Libsignal.PQXDH.BundleHandles} {spk spkSig pqpk pqpkSig : DY.Bytes} {opk : Option DY.Bytes} {bun : HwBytes} {rs : List MachineEvent} {tr' : ExecTrace} (hspk : NetMsgAt spk hb.spk tr) (hspkSig : NetMsgAt spkSig hb.spkSig tr) (hpq : NetMsgAt pqpk hb.pqpk tr) (hpqSig : NetMsgAt pqpkSig hb.pqpkSig tr) (hopk : (hb.opk = none ∧ opk = none) ∨ (∃ idx o, hb.opk = some idx ∧ opk = some o ∧ NetMsgAt o idx tr)) (hm : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr tr' hb)) (hbun4 : bun[4]? ≠ some 1#8) : hb.opk = none ∧ opk = none ∧ BundleCore i S g bun spk spkSig pqpk pqpkSig ∧ bun[4]? = some 0#8 := by
  cases hm with
  | cons hhead _ =>
    have hbm : BundleMatches i S g bun (received tr ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList)) := hhead.2
    rcases hopk with ⟨h1, h2⟩ | ⟨idx, o, h1, _, ho⟩
    · have hrec : received tr ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList) = [spk, spkSig, pqpk, pqpkSig] := by rw [h1]; change received tr [hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] = [spk, spkSig, pqpk, pqpkSig]; simp only [received, List.filterMap_cons, List.filterMap_nil, getMessageSentAt_of_netMsgAt hspk, getMessageSentAt_of_netMsgAt hspkSig, getMessageSentAt_of_netMsgAt hpq, getMessageSentAt_of_netMsgAt hpqSig]
      rw [hrec] at hbm; exact ⟨h1, h2, hbm.1, hbm.2⟩
    · exfalso; have hrec : received tr ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList) = [spk, spkSig, pqpk, pqpkSig, o] := (by rw [h1]; change received tr [hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig, idx] = [spk, spkSig, pqpk, pqpkSig, o]; simp only [received, List.filterMap_cons, List.filterMap_nil, getMessageSentAt_of_netMsgAt hspk, getMessageSentAt_of_netMsgAt hspkSig, getMessageSentAt_of_netMsgAt hpq, getMessageSentAt_of_netMsgAt hpqSig, getMessageSentAt_of_netMsgAt ho]); rw [hrec] at hbm; exact hbun4 hbm.2.1
end Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
