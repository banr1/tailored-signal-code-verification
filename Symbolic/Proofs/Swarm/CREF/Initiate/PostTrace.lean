/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BobKyberNone
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.SpecLemmas.ProofHubsPure
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.Ghosts -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Session Initiation Trace and Postcondition Lemmas

Trace evaluation and visible-entry lemmas for `aliceStart`, concretization of `aliceAgreement`
under `gamma`, pending-record serialization (`recordBytes_sessionToRecordRecPending`), and the
initial state invariants `aliceStart_stateRel_pending` and `trKeyShape_aliceStartState`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.COMPOSED

/-! ## `aliceStart` trace evaluation and visible entries -/

/-- Initial `TRState` stored by `aliceStart` at `tr.length + 8` after `aliceHandshake` returns `o`. -/
def aliceStartState (tr : ExecTrace) (b : DY.Participant) (o : PQXDH.AliceHandshakeOut) :
    TripleRatchet.TRState :=
  let dhsA := randTerm (tr.length + 2) 32
  let (rkA, cksA) := DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk dhsA
  { peer := b,
    myIk := PQXDH.serializedIk o.ikA,
    peerIk := PQXDH.serializedIk o.ikB,
    rk := rkA,
    dhs := dhsA,
    cks := cksA,
    ns := 0,
    pn := 0,
    sid := Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk,
    initiator := true,
    rIdx := 1,
    recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
    spqr := DY.Spqr.spqrInit o.keys.pqr TripleRatchet.spqrA2B }

/-- The 9-entry extension produced by `aliceStart a b idStateIdx regIdxB h` on `tr` when
`aliceHandshake` returns `some o`. -/
def aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant) (o : PQXDH.AliceHandshakeOut) :
    ExecTrace :=
  let dhsA := randTerm (tr.length + 2) 32
  let stA := aliceStartState tr b o
  ((((((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append
    (NetE o.ek)).append
    (NetE o.ct)).append
    (EvE (PQXDH.PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))).append
    (DY.ProtocolEvent.ExecEntryT.mk
      (TripleRatchet.TREvent.InitSession a b (DY.DiffieHellman.dhPk dhsA) o.spk))).append
    (DY.ProtocolEvent.ExecEntryT.mk
      (ComposedEvent.HandshakeSession (stA.sessionInfo a) (tr.length + 5)))).append
    (DY.PersistentGlobalState.State.ExecEntryT.mk
      ({ participant := a, state := stA } : DY.PersistentLocalState.LocalState TripleRatchet.TRState))

theorem length_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    (aliceStartTrOfOut tr a b o).length = tr.length + 9 := by
  unfold aliceStartTrOfOut
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem bind_aliceHandshake_at' {Inv : ExecTrace → Prop} {α : Type}
    (a b : DY.Participant) (idStateIdx regIdxB : Nat) (bh : PQXDH.BundleHandles)
    {f : PQXDH.AliceHandshakeOut → Traceful α}
    (tr : ExecTrace) (hInv : Inv tr)
    (habort : Inv (tr.append (RndE 32)))
    (hf : ∀ (ikA ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes)
      (opk : Option DY.Bytes) (honest : Bool),
      CompTrace.PQXDHStoredAt tr a { kind := .identity, sk := ikA } idStateIdx →
      tr.EventLoggedAt (PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regIdxB →
      CompTrace.NetMsgAt spk bh.spk tr →
      CompTrace.NetMsgAt spkSig bh.spkSig tr →
      CompTrace.NetMsgAt pqpk bh.pqpk tr →
      CompTrace.NetMsgAt pqpkSig bh.pqpkSig tr →
      ((bh.opk = none ∧ opk = none) ∨
        (∃ idx u, bh.opk = some idx ∧ opk = some u ∧ CompTrace.NetMsgAt u idx tr)) →
      Inv ((f (CompTrace.aliceOut tr ikA ikB spk pqpk opk)).run
        ((tr.append (RndE 32)).append (RndE 32))).2.val) :
    Inv (((PQXDH.aliceHandshake a b idStateIdx regIdxB bh >>= f).run tr).2.val) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_getKey_at a idStateIdx .identity tr hInv; intro ikA hstA
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_lookupIdentity_at b regIdxB tr hInv; intro ikB vkB honest hregB
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_receiveMessage_at bh.spk tr hInv; intro spk hspk _
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_receiveMessage_at bh.spkSig tr hInv; intro spkSig hspkSig _
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_receiveMessage_at bh.pqpk tr hInv; intro pqpk hpq _
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_receiveMessage_at bh.pqpkSig tr hInv; intro pqpkSig hpqSig _
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_guardP_at _ tr hInv; intro _
  rw [CompTrace.run_bind_assoc_snd]
  apply CompTrace.bind_guardP_at _ tr hInv; intro _
  rcases hbh : bh.opk with _ | opkIdx
  · change Inv ((((Pure.pure none : Traceful (Option DY.Bytes)) >>=
      CompTrace.aliceHandshakeJp ikA ikB spk pqpk >>= f).run tr).2.val)
    rw [CompTrace.run_bind_assoc_snd, CompTrace.run_pure_bind_snd]
    exact CompTrace.bind_aliceHandshakeJp_at ikA ikB spk pqpk none tr habort fun _ _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig none honest hstA hregB
        hspk hspkSig hpq hpqSig (Or.inl ⟨hbh, rfl⟩)
  · change Inv ((((DY.Network.receiveMessage opkIdx >>= fun o =>
        (Pure.pure (some o) : Traceful (Option DY.Bytes)) >>=
          CompTrace.aliceHandshakeJp ikA ikB spk pqpk) >>= f).run tr).2.val)
    rw [CompTrace.run_bind_assoc_snd]
    apply CompTrace.bind_receiveMessage_at opkIdx tr hInv; intro u hopk _
    rw [CompTrace.run_bind_assoc_snd, CompTrace.run_pure_bind_snd]
    exact CompTrace.bind_aliceHandshakeJp_at ikA ikB spk pqpk (some u) tr habort fun _ _ =>
      hf ikA ikB vkB spk spkSig pqpk pqpkSig (some u) honest hstA hregB
        hspk hspkSig hpq hpqSig (Or.inr ⟨opkIdx, u, hbh, rfl, hopk⟩)

theorem aliceStart_next_cases (a b : DY.Participant) (idStateIdx regIdxB : Nat)
    (bh : PQXDH.BundleHandles) (shown : Nat) (tr : ExecTrace) :
    (Move.aliceStart a b idStateIdx regIdxB bh shown).next tr = tr ∨
    (Move.aliceStart a b idStateIdx regIdxB bh shown).next tr = tr.append (RndE 32) ∨
    ∃ (ikA ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (honest : Bool),
      CompTrace.PQXDHStoredAt tr a { kind := .identity, sk := ikA } idStateIdx ∧
      tr.EventLoggedAt (PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regIdxB ∧
      CompTrace.NetMsgAt spk bh.spk tr ∧
      CompTrace.NetMsgAt spkSig bh.spkSig tr ∧
      CompTrace.NetMsgAt pqpk bh.pqpk tr ∧
      CompTrace.NetMsgAt pqpkSig bh.pqpkSig tr ∧
      ((bh.opk = none ∧ opk = none) ∨
        (∃ idx u, bh.opk = some idx ∧ opk = some u ∧ CompTrace.NetMsgAt u idx tr)) ∧
      (Move.aliceStart a b idStateIdx regIdxB bh shown).next tr =
        aliceStartTrOfOut tr a b (CompTrace.aliceOut tr ikA ikB spk pqpk opk) := by
  let Inv : ExecTrace → Prop := fun tr' =>
    tr' = tr ∨ tr' = tr.append (RndE 32) ∨
    ∃ (ikA ikB vkB spk spkSig pqpk pqpkSig : DY.Bytes) (opk : Option DY.Bytes) (honest : Bool),
      CompTrace.PQXDHStoredAt tr a { kind := .identity, sk := ikA } idStateIdx ∧
      tr.EventLoggedAt (PQXDH.PQXDHEvent.IdentityRegistered b ikB vkB honest) regIdxB ∧
      CompTrace.NetMsgAt spk bh.spk tr ∧
      CompTrace.NetMsgAt spkSig bh.spkSig tr ∧
      CompTrace.NetMsgAt pqpk bh.pqpk tr ∧
      CompTrace.NetMsgAt pqpkSig bh.pqpkSig tr ∧
      ((bh.opk = none ∧ opk = none) ∨
        (∃ idx u, bh.opk = some idx ∧ opk = some u ∧ CompTrace.NetMsgAt u idx tr)) ∧
      tr' = aliceStartTrOfOut tr a b (CompTrace.aliceOut tr ikA ikB spk pqpk opk)
  change Inv ((Move.aliceStart a b idStateIdx regIdxB bh shown).next tr)
  rw [b5_aliceStart_next]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
  refine bind_aliceHandshake_at' (Inv := Inv) a b idStateIdx regIdxB bh tr (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_
  intro ikA ikB vkB spk spkSig pqpk pqpkSig opk honest hstA hregB hspk hspkSig hpq hpqSig hopk
  refine Or.inr (Or.inr ⟨ikA, ikB, vkB, spk, spkSig, pqpk, pqpkSig, opk, honest,
    hstA, hregB, hspk, hspkSig, hpq, hpqSig, hopk, ?_⟩)
  dsimp only [aliceStartTrOfOut, aliceStartState, TripleRatchet.traceLength, randTerm]
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure,
    Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
    Nat.add_assoc]

private theorem at?_append_of_some_pt {E E' : Type} [ExecTraceTypes.Has E] [ExecTraceTypes.Has E']
    {tr : ExecTrace} {e : E'} {i : Nat} {res : E} (h : tr.at? i = some res) :
    (tr.append e).at? i = some res := by
  have hle := Trace.at?_le (EntryT := E) tr (tr.append e) i (Trace.append_le tr e); rw [h] at hle; exact hle

theorem getMessageSentAt_ek_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    (aliceStartTrOfOut tr a b o).getMessageSentAt (tr.length + 3) = some o.ek := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  have h0 : ((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append (NetE o.ek)).at? (tr.length + 3) = some (NetE o.ek) := by
    convert Trace.at?_append (((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)) (NetE o.ek) using 2
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have h5 : (aliceStartTrOfOut tr a b o).at? (tr.length + 3) = some (NetE o.ek) :=
    at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt h0))))
  rw [h5]

theorem getMessageSentAt_ct_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    (aliceStartTrOfOut tr a b o).getMessageSentAt (tr.length + 4) = some o.ct := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  have h0 : (((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append (NetE o.ek)).append (NetE o.ct)).at? (tr.length + 4) = some (NetE o.ct) := by
    convert Trace.at?_append ((((tr.append (RndE 32)).append (RndE 32)).append (RndE 32)).append (NetE o.ek)) (NetE o.ct) using 2
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have h4 : (aliceStartTrOfOut tr a b o).at? (tr.length + 4) = some (NetE o.ct) :=
    at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt h0)))
  rw [h4]

theorem getLocalState_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    ((DY.PersistentLocalState.getLocalState a (tr.length + 8) :
      Traceful TripleRatchet.TRState).run (aliceStartTrOfOut tr a b o)).1 =
      some (aliceStartState tr b o) := by
  have hat : ((aliceStartTrOfOut tr a b o).at? (tr.length + 8) : Option CompTrace.TRStEntry) =
      some (CompTrace.TRStE a (aliceStartState tr b o)) := by
    unfold aliceStartTrOfOut; dsimp only
    convert Trace.at?_append _ (CompTrace.TRStE a (aliceStartState tr b o)) using 2
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [CompTrace.getLocalState_tr_fst, hat]; simp

theorem isCurrentSnapshot_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    TripleRatchet.isCurrentSnapshot (aliceStartTrOfOut tr a b o) (tr.length + 8) = true := by
  let stA := aliceStartState tr b o
  let eA := DY.PersistentGlobalState.State.ExecEntryT.mk
    ({ participant := a, state := stA } : DY.PersistentLocalState.LocalState TripleRatchet.TRState)
  have hat : (aliceStartTrOfOut tr a b o).at? (tr.length + 8) = some eA := by
    unfold aliceStartTrOfOut; dsimp only
    convert Trace.at?_append _ eA using 2
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hsub : (aliceStartTrOfOut tr a b o).length - (tr.length + 8 + 1) = 0 := by
    rw [length_aliceStartTrOfOut]; omega
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]; rw [hat, hsub]; rfl

@[simp] private theorem length_append_entry {T : Type} [ExecTraceTypes.Has T]
    (tr : ExecTrace) (x : T) : (tr.append x).length = tr.length + 1 := by
  simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem newIndices_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    newIndices tr (aliceStartTrOfOut tr a b o) =
      [tr.length, tr.length + 1, tr.length + 2, tr.length + 3, tr.length + 4,
       tr.length + 5, tr.length + 6, tr.length + 7, tr.length + 8] := by
  unfold newIndices; rw [length_aliceStartTrOfOut, Nat.add_sub_cancel_left]
  simp [List.range', Nat.add_assoc]

local macro "at?_tr9_tac" : tactic =>
  `(tactic| (dsimp only [aliceStartTrOfOut]
             repeat (rw [at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp [length_append_entry])]; rfl))

theorem newRandoms_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    newRandoms tr (aliceStartTrOfOut tr a b o) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) 32, 32), (randTerm (tr.length + 2) 32, 32)] := by
  unfold newRandoms; rw [newIndices_aliceStartTrOfOut]
  have h0 : ((aliceStartTrOfOut tr a b o).at? tr.length : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_tr9_tac
  have h1 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_tr9_tac
  have h2 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 2) : Option DY.Random.ExecEntryT) = some (RndE 32) := by at?_tr9_tac
  have h3 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by at?_tr9_tac
  have h4 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by at?_tr9_tac
  have h5 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by at?_tr9_tac
  have h6 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by at?_tr9_tac
  have h7 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 7) : Option DY.Random.ExecEntryT) = none := by at?_tr9_tac
  have h8 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 8) : Option DY.Random.ExecEntryT) = none := by at?_tr9_tac
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, RndE]

theorem getEventAt_pq_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    let tr' := aliceStartTrOfOut tr a b o
    tr'.getEventAt PQXDH.PQXDHEvent tr.length = none ∧
    tr'.getEventAt PQXDH.PQXDHEvent (tr.length + 1) = none ∧
    tr'.getEventAt PQXDH.PQXDHEvent (tr.length + 2) = none ∧
    tr'.getEventAt PQXDH.PQXDHEvent (tr.length + 3) = none ∧
    tr'.getEventAt PQXDH.PQXDHEvent (tr.length + 4) = none ∧
    tr'.getEventAt PQXDH.PQXDHEvent (tr.length + 5) =
      some (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) ∧
    tr'.getEventAt PQXDH.PQXDHEvent (tr.length + 6) = none ∧
    tr'.getEventAt PQXDH.PQXDHEvent (tr.length + 7) = none ∧
    tr'.getEventAt PQXDH.PQXDHEvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((aliceStartTrOfOut tr a b o).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by at?_tr9_tac
  have h1 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 1) : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by at?_tr9_tac
  have h2 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 2) : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by at?_tr9_tac
  have h3 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 3) : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by at?_tr9_tac
  have h4 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 4) : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by at?_tr9_tac
  have h5 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 5) : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) =
      some (EvE (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)) := by at?_tr9_tac
  have h6 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 6) : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by at?_tr9_tac
  have h7 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 7) : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by at?_tr9_tac
  have h8 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 8) : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by at?_tr9_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8, EvE]

theorem getEventAt_tr_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    let tr' := aliceStartTrOfOut tr a b o
    tr'.getEventAt TripleRatchet.TREvent tr.length = none ∧
    tr'.getEventAt TripleRatchet.TREvent (tr.length + 1) = none ∧
    tr'.getEventAt TripleRatchet.TREvent (tr.length + 2) = none ∧
    tr'.getEventAt TripleRatchet.TREvent (tr.length + 3) = none ∧
    tr'.getEventAt TripleRatchet.TREvent (tr.length + 4) = none ∧
    tr'.getEventAt TripleRatchet.TREvent (tr.length + 5) = none ∧
    tr'.getEventAt TripleRatchet.TREvent (tr.length + 6) =
      some (.InitSession a b (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)) o.spk) ∧
    tr'.getEventAt TripleRatchet.TREvent (tr.length + 7) = none ∧
    tr'.getEventAt TripleRatchet.TREvent (tr.length + 8) = none := by
  dsimp only
  have h0 : ((aliceStartTrOfOut tr a b o).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by at?_tr9_tac
  have h1 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 1) : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by at?_tr9_tac
  have h2 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 2) : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by at?_tr9_tac
  have h3 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 3) : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by at?_tr9_tac
  have h4 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 4) : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by at?_tr9_tac
  have h5 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 5) : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by at?_tr9_tac
  have h6 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 6) : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) =
      some (DY.ProtocolEvent.ExecEntryT.mk (TripleRatchet.TREvent.InitSession a b (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)) o.spk)) := by at?_tr9_tac
  have h7 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 7) : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by at?_tr9_tac
  have h8 : ((aliceStartTrOfOut tr a b o).at? (tr.length + 8) : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by at?_tr9_tac
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, h0, h1, h2, h3, h4, h5, h6, h7, h8]

theorem eventIdx_isAliceDone_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    eventIdx isAliceDone tr (aliceStartTrOfOut tr a b o) = some (tr.length + 5) := by
  unfold eventIdx; rw [newIndices_aliceStartTrOfOut]
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _, _⟩ := getEventAt_pq_aliceStartTrOfOut tr a b o
  simp [h0, h1, h2, h3, h4, h5, isAliceDone]

theorem exposures_aliceStartTrOfOut (tr : ExecTrace) (a b : DY.Participant)
    (o : PQXDH.AliceHandshakeOut) :
    exposures tr (aliceStartTrOfOut tr a b o) = [] := by
  unfold exposures pqExposureAt trExposureAt; rw [newIndices_aliceStartTrOfOut]
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := getEventAt_pq_aliceStartTrOfOut tr a b o
  obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8⟩ := getEventAt_tr_aliceStartTrOfOut tr a b o
  simp [hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8]

theorem vis_aliceStart_35 {a b : DY.Participant} {idStateIdx regIdxB : Nat}
    {h : PQXDH.BundleHandles} {tr : ExecTrace} {o : PQXDH.AliceHandshakeOut}
    (hnext : (Move.aliceStart a b idStateIdx regIdxB h 35).next tr = aliceStartTrOfOut tr a b o) :
    (Move.aliceStart a b idStateIdx regIdxB h 35).vis tr =
      (⟨.recv, received tr ([h.spk, h.spkSig, h.pqpk, h.pqpkSig] ++ h.opk.toList), .bundle, none⟩ : VisEntry) ::
        (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
          [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by
  dsimp only [Move.vis]
  rw [hnext, exposures_aliceStartTrOfOut, List.append_nil]
  unfold aliceVis
  rw [newRandoms_aliceStartTrOfOut, eventIdx_isAliceDone_aliceStartTrOfOut]
  dsimp only [List.take, List.map, aliceDraws]
  have hlen : (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
      [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]).length = 34 := by
    simp [kyberCoinEntries]
  rw [List.take_of_length_le (Nat.le_of_eq hlen)]

theorem forall₂_append_cancel_left {α β : Type _} {R : α → β → Prop}
    {xs₁ ys₁ : List α} {xs₂ ys₂ : List β}
    (h : List.Forall₂ R (xs₁ ++ ys₁) (xs₂ ++ ys₂)) (hlen : xs₁.length = xs₂.length) :
    List.Forall₂ R ys₁ ys₂ := by
  induction xs₁ generalizing xs₂ with
  | nil => cases xs₂ with | nil => exact h | cons _ _ => simp at hlen
  | cons x xs₁ ih =>
    cases xs₂ with
    | nil => simp at hlen
    | cons y xs₂ =>
      simp only [List.cons_append] at h
      cases h with | cons _ htail => exact ih htail (by simp at hlen; omega)

theorem forall₂_append_suffix_of_length_eq {α β : Type _} {R : α → β → Prop}
    {xs₁ ys₁ : List α} {xs₂ ys₂ : List β}
    (h : List.Forall₂ R (xs₁ ++ ys₁) (xs₂ ++ ys₂)) (hlen : ys₁.length = ys₂.length) :
    List.Forall₂ R ys₁ ys₂ := by
  have htot := h.length_eq; simp only [List.length_append] at htot
  exact forall₂_append_cancel_left h (by omega)

/-! ## Setup trace lookup and `aliceStart` visible-entry matching -/

theorem setupSecret_0_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) : setupSecret r 0 = randTerm 0 32 :=
  (setupSecret_eq r hNe).1

theorem setupPublic_2_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupPublic r 2 = DY.DiffieHellman.dhPk (randTerm 5 32) := by
  rw [(setupPublic_eq r hNe).2.1, (setupSecret_eq r hNe).2.1]

private def pt_Runs {α : Type} (x : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (x.run tr).1 = some a ∧ (x.run tr).2.val = tr'

private theorem pt_Runs.bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    {tr tr1 tr2 : ExecTrace} {a : α} {b : β}
    (h1 : pt_Runs x tr a tr1) (h2 : pt_Runs (f a) tr1 b tr2) :
    pt_Runs (x >>= f) tr b tr2 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  rcases hx : x.run tr with ⟨o, t, ht⟩
  rw [hx] at h1a h1b; cases h1a; cases h1b
  rcases hf : (f a).run t with ⟨o', t', ht'⟩
  rw [hf] at h2a h2b; cases h2a; cases h2b
  refine ⟨?_, ?_⟩ <;> rw [Traceful.run_bind, hx] <;> dsimp only <;> rw [hf]

private theorem pt_Runs.pure {α : Type} (a : α) (tr : ExecTrace) :
    pt_Runs (Pure.pure a : Traceful α) tr a tr := by
  simp [pt_Runs, DY.Traceful.run_pure]

section PtSetupStepping

attribute [local irreducible] Bind.bind

private theorem pt_Runs.getEntry {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {i : Nat} {e : E}
    (h : tr.at? i = some e) : pt_Runs (DY.getEntry i : Traceful E) tr e tr := by
  simp [pt_Runs, Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk, h]

private theorem pt_Runs.appendEntry {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    pt_Runs (DY.appendEntry e) tr tr.length (tr.append e) := by
  simp [pt_Runs, Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]

private theorem pt_Runs.guard {p : Prop} [Decidable p] (tr : ExecTrace) (h : p) :
    pt_Runs (_root_.guard p : Traceful Unit) tr () tr := by
  simp [pt_Runs, _root_.guard, h, DY.Traceful.run_pure]

private theorem pt_Runs.logEvent (tr : ExecTrace) (ev : PQXDH.PQXDHEvent) :
    pt_Runs (DY.ProtocolEvent.logEvent ev) tr () (tr.append (EvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact pt_Runs.bind (pt_Runs.appendEntry tr _) (pt_Runs.pure _ _)

private theorem pt_Runs.genRand (tr : ExecTrace) (n : Nat) :
    pt_Runs (DY.Random.genRand n) tr (randTerm tr.length n) (tr.append (RndE n)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact pt_Runs.bind (pt_Runs.appendEntry tr _) (pt_Runs.pure _ _)

private theorem pt_Runs.sendMessage (tr : ExecTrace) (b : DY.Bytes) :
    pt_Runs (DY.Network.sendMessage b) tr tr.length (tr.append (NetE b)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact pt_Runs.appendEntry _ _

private theorem pt_Runs.storeLocalState (tr : ExecTrace) (me : DY.Participant)
    (st : PQXDH.PQXDHState) :
    pt_Runs (DY.PersistentLocalState.storeLocalState me st) tr tr.length (tr.append (StE me st)) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact pt_Runs.appendEntry _ _

private theorem pt_Runs.getKey {tr : ExecTrace} {me : DY.Participant} {h : Nat}
    {kind : PQXDH.KeyKind} {sk : DY.Bytes}
    (hst : tr.at? h = some (StE me { kind, sk })) :
    pt_Runs (PQXDH.getKey me h kind) tr sk tr := by
  (unfold PQXDH.getKey; simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1])
  refine pt_Runs.bind (pt_Runs.bind (pt_Runs.bind (pt_Runs.getEntry hst) (pt_Runs.pure _ _))
    (pt_Runs.bind (pt_Runs.guard _ rfl) (pt_Runs.pure _ _))) ?_
  exact pt_Runs.bind (pt_Runs.guard _ rfl) (pt_Runs.pure _ _)

private theorem pt_Runs.requireTracePredicate {p : ExecTrace → Bool} {tr : ExecTrace} (h : p tr = true) :
    pt_Runs (PQXDH.guardTrace p) tr () tr := by
  unfold pt_Runs PQXDH.guardTrace
  simp only [Traceful.run_mk, h, ↓reduceIte]
  exact ⟨trivial, trivial⟩

private def pt_setupTr1 (a : DY.Participant) : ExecTrace :=
  ((((Trace.nil.append (RndE 32)).append
    (EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
      (DY.Signature.vk (randTerm 0 32)) true))).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 0 32)))).append
    (NetE (DY.Signature.vk (randTerm 0 32)))).append
    (StE a { kind := .identity, sk := randTerm 0 32 })

private def pt_setupTr2 (a b : DY.Participant) : ExecTrace :=
  (((((pt_setupTr1 a).append (RndE 32)).append
    (EvE (.IdentityRegistered b (DY.DiffieHellman.dhPk (randTerm 5 32))
      (DY.Signature.vk (randTerm 5 32)) true))).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 5 32)))).append
    (NetE (DY.Signature.vk (randTerm 5 32)))).append
    (StE b { kind := .identity, sk := randTerm 5 32 })

private def pt_setupTr3 (a b : DY.Participant) : ExecTrace :=
  ((((((pt_setupTr2 a b).append (RndE 32)).append (RndE 64)).append
    (EvE (.SignedPrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 10 32))))).append
    (StE b { kind := .signedPrekey, sk := randTerm 10 32 })).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 10 32)))).append
    (NetE (DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
      (PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32)))))

private def pt_setupTr4 (a b : DY.Participant) : ExecTrace :=
  ((((((pt_setupTr3 a b).append (RndE 64)).append (RndE 64)).append
    (EvE (.PQPrekeyPublished b (DY.PQKem.kemPk (randTerm 16 64))))).append
    (StE b { kind := .pqPrekey, sk := randTerm 16 64 })).append
    (NetE (DY.PQKem.kemPk (randTerm 16 64)))).append
    (NetE (DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
      (PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64)))))

private def pt_setupTr5 (a b : DY.Participant) : ExecTrace :=
  ((((pt_setupTr4 a b).append (RndE 32)).append
    (EvE (.OneTimePrekeyPublished b (DY.DiffieHellman.dhPk (randTerm 22 32))))).append
    (StE b { kind := .oneTimePrekey, sk := randTerm 22 32 })).append
    (NetE (DY.DiffieHellman.dhPk (randTerm 22 32)))

private theorem pt_runs_registerIdentity_a (a : DY.Participant) :
    pt_Runs (PQXDH.registerIdentity a) Trace.nil 4 (pt_setupTr1 a) := by
  unfold PQXDH.registerIdentity
  have hpred : (!PQXDH.isRegisteredB Trace.nil a) = true := by
    unfold PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
    simp [Symbolic.DYBridge.DY.Trace.length_eq_1]
  refine pt_Runs.bind (pt_Runs.requireTracePredicate hpred) ?_
  refine pt_Runs.bind (pt_Runs.genRand _ _) ?_
  refine pt_Runs.bind (pt_Runs.logEvent _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  convert pt_Runs.storeLocalState _ a { kind := .identity, sk := randTerm Trace.nil.length 32 } using 1 <;>
    simp [pt_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem pt_not_isRegisteredB_setupTr1 {a b : DY.Participant} (hNe : a ≠ b) :
    (!PQXDH.isRegisteredB (pt_setupTr1 a) b) = true := by
  have hbeq : (a == b) = false := beq_false_of_ne hNe
  have h0 : (pt_setupTr1 a).length = 5 := by
    simp [pt_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hat0 : ((pt_setupTr1 a).at? 0 : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by
    simp [pt_setupTr1, Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
  have hat1 : ((pt_setupTr1 a).at? 1 : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) =
    some (EvE (.IdentityRegistered a (DY.DiffieHellman.dhPk (randTerm 0 32))
      (DY.Signature.vk (randTerm 0 32)) true)) := by
    simp [pt_setupTr1, Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
  have hat2 : ((pt_setupTr1 a).at? 2 : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by
    simp [pt_setupTr1, Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
  have hat3 : ((pt_setupTr1 a).at? 3 : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by
    simp [pt_setupTr1, Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
  have hat4 : ((pt_setupTr1 a).at? 4 : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by
    simp [pt_setupTr1, Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.at_eq_2]; rfl
  unfold PQXDH.isRegisteredB; rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  rw [h0]
  simp [List.range_succ, hat0, hat1, hat2, hat3, hat4, hbeq]

private theorem pt_setupTr2_idB (a b : DY.Participant) :
    (pt_setupTr2 a b).at? 9 = some (StE b { kind := .identity, sk := randTerm 5 32 }) := by
  unfold pt_setupTr2
  convert Trace.at?_append _ (StE b { kind := .identity, sk := randTerm 5 32 }) using 2
  simp [pt_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem pt_setupTr3_idB (a b : DY.Participant) :
    (pt_setupTr3 a b).at? 9 = some (StE b { kind := .identity, sk := randTerm 5 32 }) := by
  unfold pt_setupTr3
  exact at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt
    (at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt (pt_setupTr2_idB a b))))))

private theorem pt_runs_registerIdentity_b {a b : DY.Participant} (hNe : a ≠ b) :
    pt_Runs (PQXDH.registerIdentity b) (pt_setupTr1 a) 9 (pt_setupTr2 a b) := by
  unfold PQXDH.registerIdentity
  refine pt_Runs.bind (pt_Runs.requireTracePredicate (pt_not_isRegisteredB_setupTr1 hNe)) ?_
  refine pt_Runs.bind (pt_Runs.genRand _ _) ?_
  refine pt_Runs.bind (pt_Runs.logEvent _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  convert pt_Runs.storeLocalState _ b { kind := .identity, sk := randTerm (pt_setupTr1 a).length 32 } using 1 <;>
    simp [pt_setupTr2, pt_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem pt_runs_genSignedPrekey (a b : DY.Participant) :
    pt_Runs (PQXDH.genSignedPrekey b 9) (pt_setupTr2 a b) 13 (pt_setupTr3 a b) := by
  unfold PQXDH.genSignedPrekey
  refine pt_Runs.bind (pt_Runs.getKey (pt_setupTr2_idB a b)) ?_
  refine pt_Runs.bind (pt_Runs.genRand _ _) ?_
  refine pt_Runs.bind (pt_Runs.genRand _ _) ?_
  refine pt_Runs.bind (pt_Runs.logEvent _ _) ?_
  refine pt_Runs.bind (pt_Runs.storeLocalState _ _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  convert pt_Runs.pure
      ((((pt_setupTr2 a b).append (RndE 32)).append (RndE 64)).append
        (EvE (.SignedPrekeyPublished b (DY.DiffieHellman.dhPk (randTerm (pt_setupTr2 a b).length 32))))).length
      _ using 1 <;>
    simp [pt_setupTr3, pt_setupTr2, pt_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem pt_runs_genPQPrekey (a b : DY.Participant) :
    pt_Runs (PQXDH.genPQPrekey b 9) (pt_setupTr3 a b) 19 (pt_setupTr4 a b) := by
  unfold PQXDH.genPQPrekey
  refine pt_Runs.bind (pt_Runs.getKey (pt_setupTr3_idB a b)) ?_
  refine pt_Runs.bind (pt_Runs.genRand _ _) ?_
  refine pt_Runs.bind (pt_Runs.genRand _ _) ?_
  refine pt_Runs.bind (pt_Runs.logEvent _ _) ?_
  refine pt_Runs.bind (pt_Runs.storeLocalState _ _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  convert pt_Runs.pure
      ((((pt_setupTr3 a b).append (RndE 64)).append (RndE 64)).append
        (EvE (.PQPrekeyPublished b (DY.PQKem.kemPk (randTerm (pt_setupTr3 a b).length 64))))).length
      _ using 1 <;>
    simp [pt_setupTr4, pt_setupTr3, pt_setupTr2, pt_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem pt_runs_genOneTimePrekey (a b : DY.Participant) :
    pt_Runs (PQXDH.genOneTimePrekey b) (pt_setupTr4 a b) 24 (pt_setupTr5 a b) := by
  unfold PQXDH.genOneTimePrekey
  refine pt_Runs.bind (pt_Runs.genRand _ _) ?_
  refine pt_Runs.bind (pt_Runs.logEvent _ _) ?_
  refine pt_Runs.bind (pt_Runs.storeLocalState _ _ _) ?_
  refine pt_Runs.bind (pt_Runs.sendMessage _ _) ?_
  convert pt_Runs.pure
      (((pt_setupTr4 a b).append (RndE 32)).append
        (EvE (.OneTimePrekeyPublished b (DY.DiffieHellman.dhPk (randTerm (pt_setupTr4 a b).length 32))))).length
      _ using 1 <;>
    simp [pt_setupTr5, pt_setupTr4, pt_setupTr3, pt_setupTr2, pt_setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem pt_setupTrace_eq (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) :
    setupTrace r = if r.withOpk then pt_setupTr5 r.alice r.bob else pt_setupTr4 r.alice r.bob := by
  unfold setupTrace
  have h : pt_Runs (setupAct r.alice r.bob r.withOpk) Trace.nil ()
      (if r.withOpk then pt_setupTr5 r.alice r.bob else pt_setupTr4 r.alice r.bob) := by
    unfold setupAct
    refine pt_Runs.bind (pt_runs_registerIdentity_a r.alice) ?_
    refine pt_Runs.bind (pt_runs_registerIdentity_b hNe) ?_
    refine pt_Runs.bind (pt_runs_genSignedPrekey r.alice r.bob) ?_
    refine pt_Runs.bind (pt_runs_genPQPrekey r.alice r.bob) ?_
    cases r.withOpk with
    | false => exact pt_Runs.pure () _
    | true => exact pt_Runs.bind (pt_runs_genOneTimePrekey r.alice r.bob) (pt_Runs.pure () _)
  exact h.2

end PtSetupStepping

private theorem at?_setupTr2_of_setupTr1 {T : Type} [ExecTraceTypes.Has T]
    {a b : DY.Participant} {i : Nat} {e : T} (h : (pt_setupTr1 a).at? i = some e) :
    (pt_setupTr2 a b).at? i = some e := by
  unfold pt_setupTr2
  exact at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt
    (at?_append_of_some_pt (at?_append_of_some_pt h))))

private theorem at?_setupTr3_of_setupTr2 {T : Type} [ExecTraceTypes.Has T]
    {a b : DY.Participant} {i : Nat} {e : T} (h : (pt_setupTr2 a b).at? i = some e) :
    (pt_setupTr3 a b).at? i = some e := by
  unfold pt_setupTr3
  exact at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt
    (at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt h)))))

private theorem at?_setupTr4_of_setupTr3 {T : Type} [ExecTraceTypes.Has T]
    {a b : DY.Participant} {i : Nat} {e : T} (h : (pt_setupTr3 a b).at? i = some e) :
    (pt_setupTr4 a b).at? i = some e := by
  unfold pt_setupTr4
  exact at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt
    (at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt h)))))

private theorem at?_setupTr5_of_setupTr4 {T : Type} [ExecTraceTypes.Has T]
    {a b : DY.Participant} {i : Nat} {e : T} (h : (pt_setupTr4 a b).at? i = some e) :
    (pt_setupTr5 a b).at? i = some e := by
  unfold pt_setupTr5
  exact at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt h)))

private theorem setupTrace_of_setupTr4 {T : Type} [ExecTraceTypes.Has T] (r : ProtocolSetup)
    (hNe : r.alice ≠ r.bob) {i : Nat} {e : T} (h4 : (pt_setupTr4 r.alice r.bob).at? i = some e) :
    (setupTrace r).at? i = some e := by
  rw [pt_setupTrace_eq r hNe]; cases r.withOpk; exact h4; exact at?_setupTr5_of_setupTr4 h4

theorem at?_4_of_le (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) {tr : ExecTrace} (hle : setupTrace r ≤ tr) :
    (tr.at? 4 : Option CompTrace.PQXDHStEntry) =
      some (StE r.alice { kind := .identity, sk := setupSecret r 0 }) := by
  have hat1 : ((pt_setupTr1 r.alice).at? 4 : Option CompTrace.PQXDHStEntry) =
      some (StE r.alice { kind := .identity, sk := randTerm 0 32 }) := by
    unfold pt_setupTr1
    convert Trace.at?_append _ (StE r.alice { kind := .identity, sk := randTerm 0 32 }) using 2
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hat0 : ((setupTrace r).at? 4 : Option CompTrace.PQXDHStEntry) =
      some (StE r.alice { kind := .identity, sk := randTerm 0 32 }) :=
    setupTrace_of_setupTr4 r hNe (at?_setupTr4_of_setupTr3
      (at?_setupTr3_of_setupTr2 (at?_setupTr2_of_setupTr1 hat1)))
  have hat := CompTrace.at?_le_some hle hat0
  rwa [← setupSecret_0_eq r hNe] at hat

theorem at?_6_of_le (r : ProtocolSetup) (hNe : r.alice ≠ r.bob) {tr : ExecTrace} (hle : setupTrace r ≤ tr) :
    (tr.at? 6 : Option CompTrace.PQXDHEntry) =
      some (EvE (.IdentityRegistered r.bob (setupPublic r 2) (DY.Signature.vk (randTerm 5 32)) true)) := by
  have hat2 : ((pt_setupTr2 r.alice r.bob).at? 6 : Option CompTrace.PQXDHEntry) =
      some (EvE (.IdentityRegistered r.bob (DY.DiffieHellman.dhPk (randTerm 5 32))
        (DY.Signature.vk (randTerm 5 32)) true)) := by
    unfold pt_setupTr2
    refine at?_append_of_some_pt (at?_append_of_some_pt (at?_append_of_some_pt ?_))
    convert Trace.at?_append _
        (EvE (.IdentityRegistered r.bob (DY.DiffieHellman.dhPk (randTerm 5 32))
          (DY.Signature.vk (randTerm 5 32)) true)) using 2
    simp [pt_setupTr1, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hat0 : ((setupTrace r).at? 6 : Option CompTrace.PQXDHEntry) =
      some (EvE (.IdentityRegistered r.bob (DY.DiffieHellman.dhPk (randTerm 5 32))
        (DY.Signature.vk (randTerm 5 32)) true)) :=
    setupTrace_of_setupTr4 r hNe (at?_setupTr4_of_setupTr3 (at?_setupTr3_of_setupTr2 hat2))
  have hat := CompTrace.at?_le_some hle hat0
  rwa [← setupPublic_2_eq r hNe] at hat

theorem getMessageSentAt_of_netMsgAt {tr : ExecTrace} {i : Nat} {b : DY.Bytes}
    (h : CompTrace.NetMsgAt b i tr) : tr.getMessageSentAt i = some b := by
  (simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1] at *; unfold CompTrace.NetMsgAt at *); rw [h]

private theorem slice_10_32_eq_tail_slice_9_33_pte5f (b : HwBytes) : slice b 10 32 = (slice b 9 33).tail := by
  unfold slice; rw [show (10 : Nat) = 9 + 1 from rfl, ← List.tail_drop]; cases b.drop 9 <;> rfl

theorem bundleMatches_honest {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {bundle : HwBytes} {spk spkSig pqpk pqpkSig : DY.Bytes} {opk : Option DY.Bytes}
    (hbm : PreKeyBundleLayoutMatches interpretation S g bundle ([spk, spkSig, pqpk, pqpkSig] ++ opk.toList))
    (hhon : HonestBundle interpretation r bundle) :
    gamma interpretation S g spk = pubBytes interpretation (secretBytes r 2) ∧
    gamma interpretation S g pqpk = r.opaqueBytes (setupPublic r 6) ∧
    opk.map (gamma interpretation S g) =
      if bundle[4]? = some 1#8 then some (slice bundle 10 32) else none := by
  cases opk with
  | none =>
    simp only [Option.toList, List.append_nil] at hbm
    rcases hbm with ⟨⟨hlen, hspk_bm, _, hpq_bm, _⟩, hb4⟩
    have hhon' := hhon hlen
    exact ⟨ecKey_inj (hspk_bm.symm.trans hhon'.1), kyberKey_inj (hpq_bm.symm.trans hhon'.2.2.1), by simp [hb4]⟩
  | some u =>
    simp only [Option.toList, List.cons_append, List.nil_append] at hbm
    rcases hbm with ⟨⟨hlen, hspk_bm, _, hpq_bm, _⟩, hb4, h9⟩
    have hhon' := hhon hlen
    have hslice10 : slice bundle 10 32 = gamma interpretation S g u := by
      dsimp only [DY.Libsignal.PQXDH.Refinement.BundleBlob.opkPub] at h9
      rw [slice_10_32_eq_tail_slice_9_33_pte5f, h9]; rfl
    exact ⟨ecKey_inj (hspk_bm.symm.trans hhon'.1), kyberKey_inj (hpq_bm.symm.trans hhon'.2.2.1), by simp [hb4, hslice10]⟩

private theorem forall₂_kyberCoin_getElem? {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {e : DY.Bytes} {ds_kem : List HwBytes} {idxs : List Nat}
    (hrel : List.Forall₂ (EventMatchesEntry interpretation r S g)
      (ds_kem.map MachineEvent.rng) (idxs.map fun j => (⟨.rng, [e], .kyberCoin j, none⟩ : VisEntry)))
    {k : Nat} (hk : k < idxs.length) :
    (ds_kem.getD k []).length = 4 ∧ (gamma interpretation S g e).length = 32 ∧
    (ds_kem.getD k []).head? = (gamma interpretation S g e)[idxs[k]]? := by
  induction idxs generalizing ds_kem k with
  | nil => simp at hk
  | cons j idxs ih =>
    cases ds_kem with
    | nil => cases hrel
    | cons d ds_kem =>
      simp only [List.map_cons] at hrel; cases hrel with
      | cons hhead htail =>
        cases k with
        | zero =>
          rcases hhead with ⟨_, hlen4, t, ht_eq, hlen32, hhead?⟩
          simp only [List.cons.injEq, and_true] at ht_eq; subst ht_eq
          simpa [eventBytes] using ⟨hlen4, hlen32, hhead?⟩
        | succ k' => exact ih htail (Nat.lt_of_succ_lt_succ hk)

theorem rng_vis_aliceStart_35 {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ts : Nat} {ds : List HwBytes}
    (hds : ds.map List.length = initiateFullDrawLengths)
    (hrel : List.Forall₂ (EventMatchesEntry interpretation r S g) (ds.map MachineEvent.rng)
      (rngEntry (randTerm ts 32) :: kyberCoinEntries (randTerm (ts + 1) 32) ++
        [{ rngEntry (randTerm ts.succ.succ 32) with anchor := some (ts + 5) }])) :
    gamma interpretation S g (randTerm ts 32) = ds.getD 0 [] ∧
    gamma interpretation S g (randTerm (ts + 1) 32) = entropyBytes ds ∧
    gamma interpretation S g (randTerm (ts + 2) 32) = ds.getD 33 [] := by
  cases ds with
  | nil => simp [initiateFullDrawLengths] at hds
  | cons d0 ds1 =>
    simp only [List.cons_append, List.map_cons] at hrel; cases hrel with
    | cons h0 hrel1 =>
      have hd0 : gamma interpretation S g (randTerm ts 32) = d0 := by
        rcases h0 with ⟨_, h0_single⟩; simpa [rngEntry, eventBytes] using h0_single
      have hlen_ds1 : ds1.length = 33 := by
        have := congrArg List.length hds; simp [initiateFullDrawLengths] at this; omega
      have hsplit : ds1 = ds1.take 32 ++ ds1.drop 32 := (List.take_append_drop 32 ds1).symm
      rw [hsplit, List.map_append] at hrel1
      have hlen_take : ((ds1.take 32).map MachineEvent.rng).length =
          (kyberCoinEntries (randTerm (ts + 1) 32)).length := by simp [kyberCoinEntries, hlen_ds1]
      have hrel_kem : List.Forall₂ (EventMatchesEntry interpretation r S g)
          ((ds1.take 32).map MachineEvent.rng) (kyberCoinEntries (randTerm (ts + 1) 32)) :=
        List.forall₂_iff_get.2 ⟨hlen_take, fun i hi1 hi2 => by
          simpa [List.getElem_append_left hi1, List.getElem_append_left hi2] using
            (List.forall₂_iff_get.1 hrel1).2 i (by simp only [List.length_append]; omega)
              (by simp only [List.length_append]; omega)⟩
      have hrel_last := forall₂_append_cancel_left hrel1 hlen_take
      have hlen_drop : (ds1.drop 32).length = 1 := by simp [hlen_ds1]
      rcases List.length_eq_one_iff.1 hlen_drop with ⟨d33, hd33_eq⟩
      rw [hd33_eq, List.map_singleton] at hrel_last
      have hd33 : gamma interpretation S g (randTerm (ts + 2) 32) = d33 := by
        cases hrel_last with | cons hlast _ => rcases hlast with ⟨_, hlast_single⟩; simpa [rngEntry, eventBytes] using hlast_single
      have hd33_getD : (d0 :: ds1).getD 33 [] = d33 := by
        have hget : (d0 :: ds1)[33]? = (ds1.drop 32)[0]? := by simp only [List.getElem?_cons_succ, List.getElem?_drop, Nat.add_zero]
        rw [List.getD_eq_getElem?_getD, hget, hd33_eq]; rfl
      have hent : gamma interpretation S g (randTerm (ts + 1) 32) =
          entropyBytes (d0 :: ds1) := by
        have hlen32 : (gamma interpretation S g (randTerm (ts + 1) 32)).length = 32 :=
          (forall₂_kyberCoin_getElem? (idxs := List.range 32) hrel_kem (k := 0) (by simp)).2.1
        apply List.ext_getElem?; intro j
        by_cases hj : j < 32
        · have hj_kem := forall₂_kyberCoin_getElem? (idxs := List.range 32) hrel_kem (k := j) (by simp [hj])
          have hgetD_take : (ds1.take 32).getD j [] = (d0 :: ds1).getD (j + 1) [] := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_take_of_lt hj]
          have hlen4 : ((d0 :: ds1).getD (j + 1) []).length = 4 := by rw [← hgetD_take]; exact hj_kem.1
          have hhead := hj_kem.2.2; simp only [List.getElem_range] at hhead; rw [hgetD_take] at hhead
          rw [← hhead, List.head?_eq_getElem?, (getElem?_entropyBytes (d0 :: ds1) hj hlen4).symm]
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
      exact ⟨hd0, hent, hd33.trans hd33_getD.symm⟩

theorem vis_aliceStart_of_next_id {a b : DY.Participant} {idStateIdx regIdxB : Nat}
    {h : PQXDH.BundleHandles} {tr : ExecTrace}
    (hnext : (Move.aliceStart a b idStateIdx regIdxB h 35).next tr = tr) :
    (Move.aliceStart a b idStateIdx regIdxB h 35).vis tr =
      [⟨.recv, received tr ([h.spk, h.spkSig, h.pqpk, h.pqpkSig] ++ h.opk.toList), .bundle, none⟩] := by
  dsimp only [Move.vis]; rw [hnext]; simp [aliceVis, newRandoms, exposures, newIndices, aliceDraws]

theorem vis_aliceStart_of_next_rnd {a b : DY.Participant} {idStateIdx regIdxB : Nat}
    {h : PQXDH.BundleHandles} {tr : ExecTrace}
    (hnext : (Move.aliceStart a b idStateIdx regIdxB h 35).next tr = tr.append (RndE 32)) :
    (Move.aliceStart a b idStateIdx regIdxB h 35).vis tr =
      [⟨.recv, received tr ([h.spk, h.spkSig, h.pqpk, h.pqpkSig] ++ h.opk.toList), .bundle, none⟩,
       rngEntry (randTerm tr.length 32)] := by
  dsimp only [Move.vis]; rw [hnext]
  have hni : newIndices tr (tr.append (RndE 32)) = [tr.length] := by simp [newIndices]
  have hat_rnd : ((tr.append (RndE 32)).at? tr.length : Option DY.Random.ExecEntryT) = some (RndE 32) :=
    Trace.at?_append tr (RndE 32)
  have hat_pq : ((tr.append (RndE 32)).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by
    rw [at?_append_eq_of_eq _ _ rfl]; rfl
  have hat_tr : ((tr.append (RndE 32)).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT TripleRatchet.TREvent)) = none := by
    rw [at?_append_eq_of_eq _ _ rfl]; rfl
  have hnr : newRandoms tr (tr.append (RndE 32)) = [(randTerm tr.length 32, 32)] := by simp [newRandoms, hni, hat_rnd, RndE]
  have hexp : exposures tr (tr.append (RndE 32)) = [] := by
    simp [exposures, pqExposureAt, trExposureAt, hni, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat_pq, hat_tr]
  have hev : eventIdx isAliceDone tr (tr.append (RndE 32)) = none := by
    simp [eventIdx, hni, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat_pq]
  unfold aliceVis; rw [hnr, hexp, hev]; simp [aliceDraws]

/-! ## Concretization of `aliceAgreement` -/

unseal DY.Bytes in
instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_spqrInit (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (k d : DY.Bytes) :
    gamma interpretation S g (DY.Spqr.spqrInit k d) =
      S.init (gamma interpretation S g k) (gamma interpretation S g d) := by
  unfold gamma gamma'
  show ((({ authKey := k, params := d } : DY.Spqr.InitState.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll interpretation S g)]; rfl

def kemEncapCtBytes (interpretation : ExternInterpretation) (pk e : HwBytes) : HwBytes :=
  if e.length = 32 then
    ((interpretation DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [pk, e]).getD []).take 1568
  else []

def kemEncapSSBytes (interpretation : ExternInterpretation) (r : ProtocolSetup) (pk e : HwBytes) :
    HwBytes :=
  if e.length = 32 then
    ((interpretation DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [pk, e]).getD []).drop 1568
  else (kyberDecapsBytes interpretation r e).getD []

def aliceLitIkmBytes (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (bundle : HwBytes) (ds : List HwBytes) : HwBytes :=
  let dh1 := dhAgreeBytes interpretation (secretBytes r 0) (pubBytes interpretation (secretBytes r 2))
  let dh2 := dhAgreeBytes interpretation (ds.getD 0 []) (pubBytes interpretation (secretBytes r 1))
  let dh3 := dhAgreeBytes interpretation (ds.getD 0 []) (pubBytes interpretation (secretBytes r 2))
  let dh4 := if bundle[4]? = some 1#8 then
    some (dhAgreeBytes interpretation (ds.getD 0 []) (slice bundle 10 32)) else none
  let ss := kemEncapSSBytes interpretation r (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds)
  pqxdhIkmBytes dh1 dh2 dh3 dh4 ss

theorem comp_gamma_aliceAgreement (interpretation : ExternInterpretation)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (r : ProtocolSetup) (g : Ghost) (bundle : HwBytes) (ds : List HwBytes)
    {ikA ek ikB spk pqpk e : DY.Bytes} {opk : Option DY.Bytes}
    (hikA : gamma interpretation (compSemOf interpretation r) g ikA = secretBytes r 0)
    (hek : gamma interpretation (compSemOf interpretation r) g ek = ds.getD 0 [])
    (hikB : gamma interpretation (compSemOf interpretation r) g ikB = pubBytes interpretation (secretBytes r 1))
    (hspk : gamma interpretation (compSemOf interpretation r) g spk = pubBytes interpretation (secretBytes r 2))
    (hpqpk : gamma interpretation (compSemOf interpretation r) g pqpk = r.opaqueBytes (setupPublic r 6))
    (hopk : opk.map (gamma interpretation (compSemOf interpretation r) g) =
      if bundle[4]? = some 1#8 then some (slice bundle 10 32) else none)
    (he : gamma interpretation (compSemOf interpretation r) g e = entropyBytes ds) :
    let S := compSemOf interpretation r
    let a := PQXDH.aliceAgreement ikA ek ikB spk pqpk opk e
    let F := DY.Libsignal.Refinement.sha256CompressFunction interpretation
    let kdfB := pqxdhKdfBytes F (aliceLitIkmBytes interpretation r bundle ds)
    gamma interpretation S g a.1 =
      kemEncapCtBytes interpretation (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds) ∧
    gamma interpretation S g a.2.rk = kdfB.1 ∧
    gamma interpretation S g a.2.ck = kdfB.2.1 ∧
    gamma interpretation S g a.2.pqr = kdfB.2.2 := by
  intro S a F kdfB
  dsimp only [a, PQXDH.aliceAgreement]
  have hct : gamma interpretation S g (DY.PQKem.kemEncap pqpk e).1 =
      kemEncapCtBytes interpretation (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds) := by
    rw [gamma_kemEncap_fst, hpqpk, he]; rfl
  have hss : gamma interpretation S g (DY.PQKem.kemEncap pqpk e).2 =
      kemEncapSSBytes interpretation r (r.opaqueBytes (setupPublic r 6)) (entropyBytes ds) := by
    rw [gamma_kemEncap_snd, hpqpk, he]; rfl
  have hopk_eq : (opk.map (PQXDH.agree · ek)).map (gamma interpretation S g) =
      if bundle[4]? = some 1#8 then
        some (dhAgreeBytes interpretation (ds.getD 0 []) (slice bundle 10 32))
      else none := by
    cases opk with
    | none =>
      split_ifs at hopk ⊢
      · simp at hopk
      · rfl
    | some u =>
      split_ifs at hopk ⊢
      · simp only [Option.map, Option.some.injEq] at hopk ⊢
        rw [gamma_agree interpretation hEq, hek, hopk]; rfl
      · simp at hopk
  have hikm : gamma interpretation S g
      (PQXDH.pqxdhIkm (PQXDH.agree spk ikA) (PQXDH.agree ikB ek)
        (PQXDH.agree spk ek) (opk.map (PQXDH.agree · ek)) (DY.PQKem.kemEncap pqpk e).2) =
      aliceLitIkmBytes interpretation r bundle ds := by
    rw [gamma_pqxdhIkm, gamma_agree interpretation hEq, gamma_agree interpretation hEq,
        gamma_agree interpretation hEq, hikA, hek, hikB, hspk, hopk_eq, hss]; rfl
  have hkdf := gamma_pqxdhKdf interpretation S g
    (PQXDH.pqxdhIkm (PQXDH.agree spk ikA) (PQXDH.agree ikB ek)
      (PQXDH.agree spk ek) (opk.map (PQXDH.agree · ek)) (DY.PQKem.kemEncap pqpk e).2)
  rw [hikm] at hkdf
  exact ⟨hct, hkdf.1, hkdf.2.1, hkdf.2.2⟩

/-! ## Pending-record serialization and initial `StateRel` -/

open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr

private theorem length_le_lenField_pt (tag : Nat) (body : List (BitVec 8)) :
    body.length ≤ (CryptoVerification.E2E.Record.lenField tag body).length := by
  simp only [CryptoVerification.E2E.Record.lenField, List.length_append]; omega

private theorem comp_u32Field_eq : @DY.Libsignal.Composed.Refinement.u32Field = @DY.Libsignal.TripleRatchet.Refinement.u32Field := rfl
private theorem comp_bytesField_eq : @DY.Libsignal.Composed.Refinement.bytesField = @DY.Libsignal.TripleRatchet.Refinement.bytesField := rfl
private theorem comp_msgField_eq : @DY.Libsignal.Composed.Refinement.msgField = @DY.Libsignal.TripleRatchet.Refinement.msgField := rfl
private theorem comp_chainBytes_eq : @DY.Libsignal.Composed.Refinement.chainBytes = @DY.Libsignal.TripleRatchet.Refinement.chainBytes := rfl

theorem recordBytes_sessionToRecordRecPending (s : Session (List (BitVec 8)))
    (halice : s.aliceBaseKey.length < 2 ^ 63) (hpq : s.state.pqRatchetState.length < 2 ^ 63)
    (hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hrc_len : ∀ rc ∈ s.state.receiverChains, (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64)
    (hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64) :
    recordBytes (sessionToRecordRecPending s) = encodeRecord ⟨some s⟩ := by
  have hppk_msg_len : (CryptoVerification.E2E.Record.msgField 9
      (s.pendingPreKey.map CryptoVerification.E2E.Record.encPendingPreKey)).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
    unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega
  have hpkp_msg_len : (CryptoVerification.E2E.Record.msgField 14
      (s.pendingKyberPreKey.map CryptoVerification.E2E.Record.encPendingKyber)).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
    unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega
  unfold recordBytes sessionToRecordRecPending
    Swarm.Phase0WholeFunctionBridge.sessionToSessionRec CryptoVerification.E2E.Record.encodeRecord
  rw [comp_msgField_eq, comp_u32Field_eq, comp_bytesField_eq, comp_chainBytes_eq]
  dsimp only [List.flatMap_nil, List.append_nil, Option.map_some, CryptoVerification.E2E.Record.msgField]
  have hloc_len : s.state.localIdentity.serialize.length = 33 := by
    simp [CryptoGames.LibsignalSession.IdentityKey.serialize, CryptoGames.LibsignalSession.PublicKey.serialize]
  have hrem_len : ((s.state.remoteIdentity.map CryptoGames.LibsignalSession.IdentityKey.serialize).getD []).length < 2 ^ 64 := by
    cases s.state.remoteIdentity <;>
      simp [CryptoGames.LibsignalSession.IdentityKey.serialize, CryptoGames.LibsignalSession.PublicKey.serialize]
  have hrk_len : (CryptoGames.HMAC.keyToBytes32 s.state.rootKey).length = 32 := by
    simp [CryptoGames.HMAC.keyToBytes32]
  have hsc_eq : ((Option.map Swarm.Phase0WholeFunctionBridge.senderChainToChainRec s.state.senderChain).map
      (DY.Libsignal.TripleRatchet.Refinement.msgField 6 ∘ DY.Libsignal.TripleRatchet.Refinement.chainBytes)).getD [] =
      CryptoVerification.E2E.Record.msgField 6 (s.state.senderChain.map CryptoVerification.E2E.Record.encSenderChain) := by
    cases s.state.senderChain with
    | none => rfl
    | some sc =>
      dsimp only [Option.map_some, Option.getD_some, Function.comp_apply,
        CryptoVerification.E2E.Record.msgField, Swarm.Phase0WholeFunctionBridge.senderChainToChainRec]
      rw [Swarm.Phase0WholeFunctionBridge.chainBytes_sender_eq_encSenderChain sc]
      have hsc_len : (CryptoVerification.E2E.Record.encSenderChain sc).length < 2 ^ 64 := by
        unfold CryptoVerification.E2E.Record.encSenderChain; dsimp [CryptoVerification.E2E.Record.msgField]
        have h1 := Swarm.Phase0WholeFunctionBridge.record_bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
        have h2 := Swarm.Phase0WholeFunctionBridge.record_bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
        have h3 := Swarm.Phase0WholeFunctionBridge.lenField_length_le 3 (CryptoVerification.E2E.Record.encChainKey sc.chainKey)
        have h4 := Swarm.Phase0WholeFunctionBridge.encChainKey_length_lt sc.chainKey
        have hpub : sc.ratchetKey.publicKey.serialize.length = 33 := by simp [CryptoGames.LibsignalSession.PublicKey.serialize]
        have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 := List.Vector.toList_length _
        simp only [List.length_append]; omega
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 6 _ hsc_len (by decide)
  have hrc_eq : (List.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec s.state.receiverChains).flatMap
      (DY.Libsignal.TripleRatchet.Refinement.msgField 7 ∘ DY.Libsignal.TripleRatchet.Refinement.chainBytes) =
      (s.state.receiverChains.map fun c =>
        CryptoVerification.E2E.Record.lenField 7 (CryptoVerification.E2E.Record.encReceiverChain c)).flatten := by
    rw [List.flatMap_map, List.flatMap_def]; congr 1; apply List.map_congr_left; intro rc hrc
    dsimp only [Function.comp_apply]
    rw [Swarm.Phase0WholeFunctionBridge.chainBytes_receiver_eq_encReceiverChain rc (hseeds rc hrc),
        Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 7 _ (hrc_len rc hrc) (by decide)]
  have hppk_eq : ((Option.map (fun p => (CryptoVerification.E2E.Record.encPendingPreKey p, ([] : HwBytes))) s.pendingPreKey).map
      (fun p => DY.Libsignal.TripleRatchet.Refinement.msgField 9 (p.1 ++ p.2))).getD [] =
      CryptoVerification.E2E.Record.msgField 9 (s.pendingPreKey.map CryptoVerification.E2E.Record.encPendingPreKey) := by
    cases hpp : s.pendingPreKey with
    | none => rfl
    | some pp =>
      rw [hpp] at hppk_msg_len
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField] at hppk_msg_len ⊢
      rw [List.append_nil]
      have hle := length_le_lenField_pt 9 (CryptoVerification.E2E.Record.encPendingPreKey pp)
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 9 _ (by omega) (by decide)
  have hpkp_eq : ((Option.map (fun p => (CryptoVerification.E2E.Record.encPendingKyber p, ([] : HwBytes))) s.pendingKyberPreKey).map
      (fun p => DY.Libsignal.TripleRatchet.Refinement.msgField 14 (p.1 ++ p.2))).getD [] =
      CryptoVerification.E2E.Record.msgField 14 (s.pendingKyberPreKey.map CryptoVerification.E2E.Record.encPendingKyber) := by
    cases hkp : s.pendingKyberPreKey with
    | none => rfl
    | some kp =>
      rw [hkp] at hpkp_msg_len
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField] at hpkp_msg_len ⊢
      rw [List.append_nil]
      have hle := length_le_lenField_pt 14 (CryptoVerification.E2E.Record.encPendingKyber kp)
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 14 _ (by omega) (by decide)
  have hbody :
      DY.Libsignal.TripleRatchet.Refinement.u32Field 1 s.state.sessionVersion ++
        DY.Libsignal.TripleRatchet.Refinement.bytesField 2 s.state.localIdentity.serialize ++
        DY.Libsignal.TripleRatchet.Refinement.bytesField 3
          ((s.state.remoteIdentity.map CryptoGames.LibsignalSession.IdentityKey.serialize).getD []) ++
        DY.Libsignal.TripleRatchet.Refinement.bytesField 4
          (CryptoGames.HMAC.keyToBytes32 s.state.rootKey) ++
        DY.Libsignal.TripleRatchet.Refinement.u32Field 5 s.state.previousCounter ++
        ((Option.map Swarm.Phase0WholeFunctionBridge.senderChainToChainRec s.state.senderChain).map
          (DY.Libsignal.TripleRatchet.Refinement.msgField 6 ∘
            DY.Libsignal.TripleRatchet.Refinement.chainBytes)).getD [] ++
        (List.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec s.state.receiverChains).flatMap
          (DY.Libsignal.TripleRatchet.Refinement.msgField 7 ∘
            DY.Libsignal.TripleRatchet.Refinement.chainBytes) ++
        ((Option.map (fun p => (CryptoVerification.E2E.Record.encPendingPreKey p, ([] : HwBytes))) s.pendingPreKey).map
          (fun p => DY.Libsignal.TripleRatchet.Refinement.msgField 9 (p.1 ++ p.2))).getD [] ++
        DY.Libsignal.TripleRatchet.Refinement.u32Field 10 s.remoteRegistrationId ++
        DY.Libsignal.TripleRatchet.Refinement.u32Field 11 s.localRegistrationId ++
        DY.Libsignal.TripleRatchet.Refinement.bytesField 13 s.aliceBaseKey ++
        ((Option.map (fun p => (CryptoVerification.E2E.Record.encPendingKyber p, ([] : HwBytes))) s.pendingKyberPreKey).map
          (fun p => DY.Libsignal.TripleRatchet.Refinement.msgField 14 (p.1 ++ p.2))).getD [] ++
        DY.Libsignal.TripleRatchet.Refinement.bytesField 15 s.state.pqRatchetState =
      CryptoVerification.E2E.Record.encSession s := by
    unfold CryptoVerification.E2E.Record.encSession
    rw [Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 1,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 2 _ (by omega),
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 3 _ hrem_len,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 4 _ (by omega),
        Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 5,
        hsc_eq, hrc_eq, hppk_eq,
        Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 10,
        Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 11,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 13 _ (by omega),
        hpkp_eq,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 15 _ (by omega)]
  rw [hbody, Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 1 _ hsess_len (by decide)]
  simp only [List.flatMap_nil, List.append_nil]

theorem length_gamma_pqxdhKdf (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (ikm : DY.Bytes) :
    (gamma interpretation S g (PQXDH.pqxdhKdf ikm).rk).length = 32 ∧
    (gamma interpretation S g (PQXDH.pqxdhKdf ikm).ck).length = 32 ∧
    (gamma interpretation S g (PQXDH.pqxdhKdf ikm).pqr).length = 32 := by
  rw [(gamma_pqxdhKdf interpretation S g ikm).1, (gamma_pqxdhKdf interpretation S g ikm).2.1,
      (gamma_pqxdhKdf interpretation S g ikm).2.2]
  exact ⟨CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _,
         CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _,
         CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _⟩

theorem length_gamma_createChain (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (rk dhPub dhPriv : DY.Bytes) :
    (gamma interpretation S g (DY.Libsignal.TripleRatchet.createChain rk dhPub dhPriv).1).length = 32 ∧
    (gamma interpretation S g (DY.Libsignal.TripleRatchet.createChain rk dhPub dhPriv).2).length = 32 := by
  unfold DY.Libsignal.TripleRatchet.createChain DY.X25519.agree DY.Libsignal.TripleRatchet.kdfRk DY.Libsignal.TripleRatchet.hkdfBlock1 DY.Libsignal.TripleRatchet.hkdfBlock2
  dsimp only
  refine ⟨?_, ?_⟩ <;> (rw [gamma_hmac]; exact CryptoVerification.LibsignalSpqrV1.length_hmacWith _ _ _)

theorem serializedKey_drop1_ecKey (xs : HwBytes) :
    TR.serializedKey ((ecKey xs).drop 1) = ecKey xs := rfl

/-- Proves `TR.StateRel` for `sessionToRecordRecPending (aliceInitiatedSessionV1 ...)` from the
field equalities against `aliceStartState tr r.bob o`. -/
theorem aliceStart_stateRel_pending (interpretation : ExternInterpretation) (r : ProtocolSetup) (g : Ghost)
    (tr : ExecTrace) (o : PQXDH.AliceHandshakeOut)
    (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey baseKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : KeyPair) (ck1 : ChainKey) (opkId? : Option (BitVec 32))
    (spkId kyberPreKeyId remoteRegId : BitVec 32)
    (kemCtSer pqBytes : List (BitVec 8))
    (_hdhs_len : (gamma interpretation (compSemOf interpretation r) g (randTerm (tr.length + 2) 32)).length = 32)
    (_hck0_len : (gamma interpretation (compSemOf interpretation r) g o.keys.ck).length = 32)
    (hourId : ourIdentity.serialize = gamma interpretation (compSemOf interpretation r) g (PQXDH.serializedIk o.ikA))
    (htheirId : theirIdentity.serialize = gamma interpretation (compSemOf interpretation r) g (PQXDH.serializedIk o.ikB))
    (hrk1 : CryptoGames.HMAC.keyToBytes32 rk1 =
      gamma interpretation (compSemOf interpretation r) g
        (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).1)
    (hsendPub : sendingKeyPair.publicKey.bytes.toList =
      gamma interpretation (compSemOf interpretation r) g (DY.DiffieHellman.dhPk (randTerm (tr.length + 2) 32)))
    (hsendPriv : sendingKeyPair.privateKey.bytes.toList =
      clamp (gamma interpretation (compSemOf interpretation r) g (randTerm (tr.length + 2) 32)))
    (hckIdx : ck1.index = 0#32)
    (hckKey : CryptoGames.HMAC.keyToBytes32 ck1.key =
      gamma interpretation (compSemOf interpretation r) g
        (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).2)
    (htheirRatchet : theirRatchetKey.serialize =
      TR.serializedKey (gamma interpretation (compSemOf interpretation r) g o.spk))
    (hck0 : CryptoGames.HMAC.keyToBytes32 ck0 =
      gamma interpretation (compSemOf interpretation r) g o.keys.ck)
    (hpq : pqBytes =
      gamma interpretation (compSemOf interpretation r) g (DY.Spqr.spqrInit o.keys.pqr TripleRatchet.spqrA2B)) :
    let sess := aliceInitiatedSessionV1
      ourIdentity theirIdentity theirRatchetKey baseKey rk1 ck0 sendingKeyPair ck1 opkId?
      spkId kyberPreKeyId remoteRegId r.regIdA kemCtSer pqBytes
    TR.StateRel interpretation (compSemOf interpretation r) g
      (aliceStartState tr r.bob o) (sessionToRecordRecPending sess) := by
  intro sess
  let S := compSemOf interpretation r
  let dhsA := randTerm (tr.length + 2) 32
  refine ⟨rfl, ?_⟩
  unfold sessionToRecordRecPending TR.eraseSkipped TR.eraseUnmodelled TR.sessionOf
    Swarm.Phase0WholeFunctionBridge.sessionToSessionRec
    Swarm.Phase0WholeFunctionBridge.senderChainToChainRec
    Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec
    sess aliceInitiatedSessionV1 aliceInitiatedStateV1 aliceStartState
  simp only [Option.map_some, Option.getD_some, List.map_cons, List.map_nil]
  have hpub_ser : sendingKeyPair.publicKey.serialize =
      TR.serializedKey ((interpretation DY.Libsignal.Refinement.x25519PublicKeySymbol
        [clamp (gamma interpretation S g dhsA)]).getD []) := by
    change 0x05#8 :: sendingKeyPair.publicKey.bytes.toList = _
    rw [hsendPub, gamma_dhPk]
    rfl
  rw [hourId, htheirId, gamma_serializedIk, gamma_serializedIk,
      serializedKey_drop1_ecKey, serializedKey_drop1_ecKey,
      hrk1,
      hpub_ser,
      hsendPriv,
      hckIdx, hckKey,
      htheirRatchet,
      hck0,
      hpq]
  rfl

theorem trKeyShape_aliceStartState (interpretation : ExternInterpretation) (r : ProtocolSetup) (g : Ghost)
    (tr : ExecTrace) (o : PQXDH.AliceHandshakeOut) (ds : List HwBytes)
    (hds : ds.map List.length = initiateFullDrawLengths)
    (hdhs : gamma interpretation (compSemOf interpretation r) g (randTerm (tr.length + 2) 32) = ds.getD 33 []) :
    TR.TRKeyShape interpretation (compSemOf interpretation r) g (aliceStartState tr r.bob o) := by
  let S := compSemOf interpretation r
  have hlen_dhs : (ds.getD 33 []).length = 32 := by
    have hget := congrArg (fun l : List Nat => l[33]?) hds
    simp [initiateFullDrawLengths] at hget
    rcases h33 : ds[33]? with _ | d33 <;> simp [List.getD_eq_getElem?_getD, h33] at hget ⊢; exact hget
  have hcc := length_gamma_createChain interpretation S g o.keys.rk o.spk (randTerm (tr.length + 2) 32)
  refine ⟨?_, hcc.2, ?_, ?_⟩
  · dsimp only [aliceStartState]; rw [hdhs, hlen_dhs]
  · dsimp only [aliceStartState]; rw [gamma_serializedIk]; rfl
  · dsimp only [aliceStartState]; rw [gamma_serializedIk]; rfl

theorem forall₂_snoc_inv {α β : Type _} {R : α → β → Prop}
    {xs : List α} {x : α} {ys : List β} {y : β}
    (h : List.Forall₂ R (xs ++ [x]) (ys ++ [y])) :
    List.Forall₂ R xs ys ∧ R x y := by
  have hlen : xs.length = ys.length := by
    have := h.length_eq; simp only [List.length_append, List.length_singleton] at this; omega
  refine ⟨List.forall₂_iff_get.2 ⟨hlen, fun i hi1 hi2 => by
    simpa [List.getElem_append_left hi1, List.getElem_append_left hi2] using
      (List.forall₂_iff_get.1 h).2 i (by simp only [List.length_append]; omega)
        (by simp only [List.length_append]; omega)⟩, ?_⟩
  cases forall₂_append_cancel_left h hlen with
  | cons hxy _ => exact hxy

end Symbolic.Swarm.CREF
