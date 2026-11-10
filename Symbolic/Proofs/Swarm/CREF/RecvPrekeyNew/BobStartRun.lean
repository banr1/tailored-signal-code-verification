/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Trials -- shake: keep
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
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
# Symbolic Execution of `Composed.bobStart`

Defines the intermediate states and trace formula (`bobInitSt`, `bobRatchetedChain`,
`bobRatchetedSt`, `bobStartPreSkipTr`, `bobStartTr`) produced by `DY.Libsignal.Composed.bobStart`,
unpacks `bobKeys` via `OpkSel` and `bobKeysOf`, and proves `Runs.bobStart` and
`opkUsedB_append_rnd_net`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY DY.Comparse DY.Libsignal ByteSpecs
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTrace (PQStE PQEvE NetE RndE TREvE TRStE CEvE)
open Symbolic.Swarm.CREF.Stage1Trials (bobOpk?)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg consumeMessageKey)

/-! ## `Traceful` step combinators -/

/-- Exact successful run equation for `Traceful` computations on `ExecTrace`. -/
abbrev BobRuns {α : Type} (m : Traceful α) (tr : ExecTrace) (a : α) (tr' : ExecTrace) : Prop :=
  (m.run tr).1 = some a ∧ (m.run tr).2.val = tr'

private theorem bsr_runs_pure {α : Type} (tr : ExecTrace) (a : α) :
    BobRuns (Pure.pure a : Traceful α) tr a tr := by
  simp [BobRuns, DY.Traceful.run_pure]

private theorem bsr_runs_bind {α β : Type} {m : Traceful α} {f : α → Traceful β}
    {tr tr₁ tr₂ : ExecTrace} {a : α} {b : β}
    (hm : BobRuns m tr a tr₁) (hf : BobRuns (f a) tr₁ b tr₂) :
    BobRuns (m >>= f) tr b tr₂ := by
  refine ⟨?_, ?_⟩
  · rw [CompTrace.run_bind_fst, hm.1, hm.2]
    exact hf.1
  · rw [CompTrace.run_bind_snd, hm.1, hm.2]
    exact hf.2

private theorem bsr_runs_guard {c : Prop} [Decidable c] (tr : ExecTrace) (hc : c) :
    BobRuns (_root_.guard c : Traceful Unit) tr () tr := by
  simp only [_root_.guard, hc, ↓reduceIte]; exact bsr_runs_pure tr ()

private theorem bsr_runs_guardOnTrace {tr : ExecTrace} {p : ExecTrace → Bool}
    (hp : p tr = true) :
    BobRuns (PQXDH.guardTrace p) tr () tr := by
  unfold BobRuns PQXDH.guardTrace
  simp only [Traceful.run_mk, hp, ↓reduceIte]
  exact ⟨trivial, trivial⟩

private theorem bsr_runs_getEntry {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {idx : Nat} {e : E}
    (h : (tr.at? idx : Option E) = some e) :
    BobRuns (DY.getEntry idx : Traceful E) tr e tr := by
  unfold BobRuns
  rw [Symbolic.DYBridge.DY.getEntry_eq_1]
  erw [DY.Traceful.run_mk]
  exact ⟨h, rfl⟩

private theorem bsr_runs_getKey {tr : ExecTrace} {me : Participant} {idx : Nat}
    {kind : PQXDH.KeyKind} {sk : DY.Bytes}
    (h : tr.at? idx = some (PQStE me { kind := kind, sk := sk })) :
    BobRuns (PQXDH.getKey me idx kind) tr sk tr := by
  (unfold PQXDH.getKey; simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1])
  refine bsr_runs_bind (bsr_runs_bind (bsr_runs_bind (bsr_runs_getEntry h) (bsr_runs_pure _ _))
    (bsr_runs_bind (bsr_runs_guard _ rfl) (bsr_runs_pure _ _))) ?_
  exact bsr_runs_bind (bsr_runs_guard _ rfl) (bsr_runs_pure _ _)

private theorem bsr_runs_appendEntry {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) :
    BobRuns (DY.appendEntry e) tr tr.length (tr.append e) := by
  unfold BobRuns
  rw [Symbolic.DYBridge.DY.appendEntry_eq_1]
  erw [DY.Traceful.run_mk]
  exact ⟨rfl, rfl⟩

private theorem bsr_runs_sendMessage (tr : ExecTrace) (msg : DY.Bytes) :
    BobRuns (DY.Network.sendMessage msg) tr tr.length (tr.append (NetE msg)) := by
  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1]
  exact bsr_runs_appendEntry tr (NetE msg)

private theorem bsr_runs_logEvent_pq (tr : ExecTrace) (ev : PQXDH.PQXDHEvent) :
    BobRuns (DY.ProtocolEvent.logEvent ev) tr () (tr.append (PQEvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact bsr_runs_bind (bsr_runs_appendEntry tr (PQEvE ev)) (bsr_runs_pure _ ())

private theorem bsr_runs_genRand (tr : ExecTrace) (size : Nat) :
    BobRuns (DY.Random.genRand size) tr (randTerm tr.length size) (tr.append (RndE size)) := by
  rw [Symbolic.DYBridge.DY.Random.genRand_eq_1]
  exact bsr_runs_bind (bsr_runs_appendEntry tr (RndE size)) (bsr_runs_pure _ _)

/-! ## `bobKeys` and `OpkSel` unpackers -/

def bobKeysOf (r : ProtocolSetup) (x : PreKeyRep) (opk : Option DY.Bytes) : PQXDH.HandshakeKeys :=
  PQXDH.pqxdhKdf (PQXDH.pqxdhIkm (PQXDH.agree (setupPublic r 0) (setupSecret r 2))
    (PQXDH.agree x.ek (setupSecret r 1))
    (PQXDH.agree x.ek (setupSecret r 2)) (opk.map (PQXDH.agree x.ek ·))
    ((PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) x.ct)).getD
      (DY.PQKem.kemRejKey (setupSecret r 4) x.ct)))

def OpkSel (r : ProtocolSetup) (p : PreKeyFields) (opk : Option DY.Bytes) : Prop :=
  (p.preKeyId = none ∧ opk = none) ∨
    (r.withOpk = true ∧ p.preKeyId = some r.opkId ∧ opk = some (setupSecret r 6))

/-- Computes `bobKeysOf r x opk` when `bobOpk? r p = some opk`. -/
def bobKeys (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep) : Option PQXDH.HandshakeKeys :=
  (bobOpk? r p).map (bobKeysOf r x)

theorem bobOpk?_unpack {r : ProtocolSetup} {p : PreKeyFields} {opk : Option DY.Bytes}
    (h : bobOpk? r p = some opk) :
    OpkSel r p opk := by
  unfold Symbolic.Swarm.Stage1Trials.bobOpk? at h
  cases hpk : p.preKeyId with
  | none =>
    rw [hpk] at h
    injection h with heq
    exact .inl ⟨hpk, heq.symm⟩
  | some id =>
    rw [hpk] at h
    by_cases hid : (r.withOpk && id == r.opkId) = true
    · simp only [hid, ↓reduceIte, Option.some.injEq] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at hid
      exact .inr ⟨hid.1, hpk.trans (congrArg some hid.2), h.symm⟩
    · simp [hid] at h

theorem bobKeys_unpack (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep)
    (keys : PQXDH.HandshakeKeys)
    (hk : bobKeys r p x = some keys) :
    ∃ opk, OpkSel r p opk ∧ keys = bobKeysOf r x opk := by
  unfold bobKeys at hk
  rcases hopk : bobOpk? r p with _ | opk
  · rw [hopk] at hk; cases hk
  · rw [hopk] at hk
    simp only [Option.map_some, Option.some.injEq] at hk
    exact ⟨opk, bobOpk?_unpack hopk, hk.symm⟩

/-! ## Symbolic step lemmas for `Composed.bobStart` -/

def StOpt (tr : ExecTrace) (me : Participant) : Option Nat → Option DY.Bytes → Prop
  | none, none => True
  | some i, some o => tr.at? i = some (PQStE me { kind := .oneTimePrekey, sk := o })
  | _, _ => False

def bobOut (ikB spk pqsk : DY.Bytes) (opk : Option DY.Bytes) (ikAPk ek ct : DY.Bytes)
    (keys : PQXDH.HandshakeKeys) : PQXDH.BobHandshakeOut :=
  { ikB := DY.DiffieHellman.dhPk ikB, ikA := ikAPk, spk := DY.DiffieHellman.dhPk spk,
    pqpk := DY.PQKem.kemPk pqsk, opk := opk.map DY.DiffieHellman.dhPk,
    ek, ct, spkSk := spk, keys }

theorem Runs.lookupIdentity {tr : ExecTrace} {p : Participant} {regIdx : Nat}
    {ikPk vkPk : DY.Bytes} {honest : Bool}
    (hreg : tr.at? regIdx = some (PQEvE (.IdentityRegistered p ikPk vkPk honest))) :
    BobRuns (DY.Libsignal.PQXDH.lookupIdentity p regIdx) tr (ikPk, vkPk) tr := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  exact bsr_runs_bind (bsr_runs_getEntry hreg)
    (bsr_runs_bind (bsr_runs_guard tr rfl) (bsr_runs_pure tr _))

theorem Runs.receiveMessage {tr : ExecTrace} {idx : Nat} {b : DY.Bytes}
    (hnet : tr.at? idx = some (NetE b)) :
    BobRuns (DY.Network.receiveMessage idx) tr b tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1]
  exact bsr_runs_bind (bsr_runs_getEntry hnet) (bsr_runs_pure tr _)

theorem Runs.bobHandshake {tr : ExecTrace} {b a : Participant} {h : PQXDH.BobKeyHandles}
    {regA ekH ctH : Nat} {ikB spk pqsk ikAPk vkA ek ct : DY.Bytes} {opk : Option DY.Bytes}
    {honest : Bool} {keys : PQXDH.HandshakeKeys}
    (hik : tr.at? h.ik = some (PQStE b { kind := .identity, sk := ikB }))
    (hspk : tr.at? h.spk = some (PQStE b { kind := .signedPrekey, sk := spk }))
    (hpq : tr.at? h.pqspk = some (PQStE b { kind := .pqPrekey, sk := pqsk }))
    (hopk : StOpt tr b h.opk opk)
    (hreg : tr.at? regA = some (PQEvE (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? ekH = some (NetE ek)) (hct : tr.at? ctH = some (NetE ct))
    (hcan : PQXDH.isCanonicalKey ek = true)
    (hagree : PQXDH.bobAgreement ikB spk pqsk opk ikAPk ek ct = some keys) :
    BobRuns (DY.Libsignal.PQXDH.bobHandshake b a h regA ekH ctH) tr
      (bobOut ikB spk pqsk opk ikAPk ek ct keys) tr := by
  unfold DY.Libsignal.PQXDH.bobHandshake
  refine bsr_runs_bind (bsr_runs_getKey hik) (bsr_runs_bind (bsr_runs_getKey hspk)
    (bsr_runs_bind (bsr_runs_getKey hpq) ?_))
  rcases hoi : h.opk with _ | i <;> rcases opk with _ | o <;>
    rw [hoi] at hopk <;> dsimp only [StOpt] at hopk
  · dsimp only
    refine bsr_runs_bind (bsr_runs_pure tr _) (bsr_runs_bind (Runs.lookupIdentity hreg)
      (bsr_runs_bind (Runs.receiveMessage hek) (bsr_runs_bind (Runs.receiveMessage hct)
      (bsr_runs_bind (bsr_runs_guard tr hcan) ?_))))
    rw [hagree]; exact bsr_runs_pure tr _
  · dsimp only
    refine bsr_runs_bind (bsr_runs_getKey hopk) (bsr_runs_bind (bsr_runs_pure tr _)
      (bsr_runs_bind (Runs.lookupIdentity hreg) (bsr_runs_bind (Runs.receiveMessage hek)
      (bsr_runs_bind (Runs.receiveMessage hct) (bsr_runs_bind (bsr_runs_guard tr hcan) ?_)))))
    rw [hagree]; exact bsr_runs_pure tr _

theorem bobOpkPk_eq (tr : ExecTrace) (b : Participant) (h : PQXDH.BobKeyHandles)
    (opk : Option DY.Bytes) (hopk : StOpt tr b h.opk opk) :
    bobOpkPk b h tr = opk.map DY.DiffieHellman.dhPk := by
  unfold bobOpkPk
  rcases h with ⟨ik, spk, pqspk, oi⟩
  rcases oi with _ | i <;> rcases opk with _ | o
  · rfl
  · exact False.elim hopk
  · exact False.elim hopk
  · dsimp only [Option.bind]; rw [(bsr_runs_getKey hopk).1]

theorem Runs.traceLength (tr : ExecTrace) :
    BobRuns DY.Libsignal.TripleRatchet.traceLength tr tr.length tr := by
  unfold BobRuns DY.Libsignal.TripleRatchet.traceLength
  erw [DY.Traceful.run_mk]
  exact ⟨rfl, rfl⟩

theorem Runs.receiveSignalMsg {tr : ExecTrace} {msgH : Nat} {raw : DY.Bytes}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hnet : tr.at? msgH = some (NetE raw))
    (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg)
    (hver : msg.version = DY.Libsignal.TripleRatchet.messageVersion) :
    BobRuns (DY.Libsignal.TripleRatchet.receiveSignalMsg msgH) tr msg tr := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  refine bsr_runs_bind (Runs.receiveMessage hnet) ?_
  rw [hparse]; dsimp only
  exact bsr_runs_bind (bsr_runs_guard tr hver) (bsr_runs_pure tr _)

theorem Runs.verifyMacAndDecrypt {tr : ExecTrace}
    {st : DY.Libsignal.TripleRatchet.TRState}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    {pqSalt seed m : DY.Bytes}
    (hmac : msg.mac = DY.Libsignal.TripleRatchet.computeMac
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : PQXDH.errToOption (DY.SymEnc.symDec
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m) :
    BobRuns (DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed) tr m tr := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt
  refine bsr_runs_bind (bsr_runs_guard tr hmac) ?_
  rcases hsym : DY.SymEnc.symDec
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext with _ | m' <;>
    rw [hsym] at hdec
  · cases hdec
  · injection hdec with h; subst h
    unfold BobRuns
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    erw [DY.Traceful.run_mk]
    exact ⟨rfl, rfl⟩

def bobInitSt (a : Participant) (ikB ikA : DY.Bytes) (keys : PQXDH.HandshakeKeys)
    (sS rt : DY.Bytes) : DY.Libsignal.TripleRatchet.TRState :=
  { peer := a, myIk := PQXDH.serializedIk ikB, peerIk := PQXDH.serializedIk ikA,
    rk := keys.rk, dhs := sS, cks := keys.ck, ns := 0, pn := 0,
    sid := Concat.concat (DY.X25519.normalizeX25519Key rt) keys.rk, initiator := false, rIdx := 0, recv := [],
    spqr := DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A }

def bobRatchetedChain (keys : PQXDH.HandshakeKeys) (rt sS : DY.Bytes) :
    DY.Libsignal.TripleRatchet.RecvChain :=
  { ratchetKey := rt, chainKey := (DY.Libsignal.TripleRatchet.createChain keys.rk rt sS).2,
    index := 0, rIdx := 2 }

def bobRatchetedSt (a : Participant) (ikB ikA : DY.Bytes) (keys : PQXDH.HandshakeKeys)
    (sS rt dhs : DY.Bytes) : DY.Libsignal.TripleRatchet.TRState :=
  let (rk1, _) := DY.Libsignal.TripleRatchet.createChain keys.rk rt sS
  let (rk2, cks) := DY.Libsignal.TripleRatchet.createChain rk1 rt dhs
  { peer := a, myIk := PQXDH.serializedIk ikB, peerIk := PQXDH.serializedIk ikA,
    rk := rk2, dhs := dhs, cks := cks, ns := 0, pn := 0,
    sid := Concat.concat (DY.X25519.normalizeX25519Key rt) keys.rk, initiator := false, rIdx := 2,
    recv := [bobRatchetedChain keys rt sS],
    spqr := DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A }

theorem Runs.ensureReceiverChain_bobInitSt {tr : ExecTrace}
    {a : Participant} {ikB ikA : DY.Bytes} {keys : PQXDH.HandshakeKeys}
    {sS rt : DY.Bytes} (hlo : DY.Libsignal.TripleRatchet.x25519LowOrder rt = false) :
    BobRuns (DY.Libsignal.TripleRatchet.ensureReceiverChain (bobInitSt a ikB ikA keys sS rt) rt) tr
      (bobRatchetedSt a ikB ikA keys sS rt (randTerm tr.length 32),
       bobRatchetedChain keys rt sS, true)
      (tr.append (RndE 32)) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  unfold DY.Libsignal.TripleRatchet.recvChainFor DY.Libsignal.TripleRatchet.findRecvChain
  dsimp only [bobInitSt, List.find?_nil]
  simp only [hlo, Bool.false_eq_true, ↓reduceIte]
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  have hlo' : (!DY.Libsignal.TripleRatchet.x25519LowOrder rt) = true := by simp [hlo]
  exact bsr_runs_bind
    (bsr_runs_bind (bsr_runs_guard tr hlo')
      (bsr_runs_bind (bsr_runs_genRand tr 32) (bsr_runs_pure _ _)))
    (bsr_runs_pure _ _)

theorem Runs.logEvent_tr (tr : ExecTrace) (ev : DY.Libsignal.TripleRatchet.TREvent) :
    BobRuns (DY.ProtocolEvent.logEvent ev) tr ()
      (tr.append (TREvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact bsr_runs_bind (bsr_runs_appendEntry tr _) (bsr_runs_pure _ _)

theorem Runs.logEvent_c (tr : ExecTrace) (ev : ComposedEvent) :
    BobRuns (DY.ProtocolEvent.logEvent ev) tr ()
      (tr.append (CEvE ev)) := by
  rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1]
  exact bsr_runs_bind (bsr_runs_appendEntry tr _) (bsr_runs_pure _ _)

theorem Runs.storeLocalState_tr (tr : ExecTrace) (me : Participant)
    (st : DY.Libsignal.TripleRatchet.TRState) :
    BobRuns (DY.PersistentLocalState.storeLocalState me st) tr tr.length
      (tr.append (TRStE me st)) := by
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1]
  exact bsr_runs_appendEntry _ _

theorem Runs.logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx srcIdx : Nat) (ck : DY.Bytes) (idx : UInt32) (k : Nat) (tr : ExecTrace) :
    BobRuns (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k) tr ()
      ((DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx srcIdx ck idx k).run tr).2.val := by
  refine ⟨?_, rfl⟩
  induction k generalizing ck idx tr with
  | zero => (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
  | succ k ih =>
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys
    rw [CompTrace.run_bind_fst, (Runs.logEvent_tr tr _).1]
    exact ih (DY.Libsignal.TripleRatchet.kdfCk ck).1 (idx + 1) _

theorem Runs.logMessageKeyAndStore (b : Participant) (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes)
    (idx : UInt32) (rIdx parentIdx : Nat) (st : DY.Libsignal.TripleRatchet.TRState)
    (tr : ExecTrace) :
    BobRuns (DY.Libsignal.TripleRatchet.logMessageKeyAndStore b s dir seed pqSalt
      idx rIdx parentIdx st) tr (tr.length + 1)
      ((tr.append (TREvE
        (.MessageKey s dir seed pqSalt idx rIdx parentIdx))).append
        (TRStE b st)) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  let tr₁ := tr.append (TREvE (.MessageKey s dir seed pqSalt idx rIdx parentIdx))
  have hlen : tr₁.length = tr.length + 1 := by
    simp only [tr₁, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hst : BobRuns (DY.PersistentLocalState.storeLocalState b st) tr₁ (tr.length + 1)
      (tr₁.append (TRStE b st)) := by
    rw [← hlen]; exact Runs.storeLocalState_tr tr₁ b st
  exact bsr_runs_bind (Runs.logEvent_tr tr _) hst

def bobStartPreSkipTr (tr : ExecTrace) (b a : Participant) (o : PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (key : DY.Bytes) : ExecTrace :=
  let dhs := randTerm tr.length 32
  let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey dhs
  let tr_dh := tr.append (RndE 32)
  let tr_send := tr_dh.append (NetE key)
  let tr_opk := match o.opk with
    | some opkPk => tr_send.append (PQEvE (.OPKUsed b opkPk))
    | none => tr_send
  let doneIdx := tr_opk.length
  let tr_done := tr_opk.append (PQEvE (.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))
  let tr_rat1 := tr_done.append (TREvE
    (.DHRatchet b st.peer msg.ratchetKey (DY.DiffieHellman.dhPk st.dhs)))
  let tr_rat2 := tr_rat1.append (TREvE
    (.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2)))
  tr_rat2.append (CEvE
    (.HandshakeSession (st.sessionInfo b) doneIdx))

def bobStartTr (tr : ExecTrace) (b a : Participant) (o : PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain)
    (spqr' key seed pqSalt m : DY.Bytes) : ExecTrace :=
  let dhs := randTerm tr.length 32
  let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey dhs
  let c := bobRatchetedChain o.keys msg.ratchetKey o.spkSk
  let tr_hs := bobStartPreSkipTr tr b a o msg key
  let skipped := msg.counter.toNat - c.index.toNat
  let childIdx := tr_hs.length + skipped + 2
  let tr_skip := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey
    c.rIdx childIdx c.chainKey c.index skipped).run tr_hs).2.val
  let tr_recv := tr_skip.append (TREvE
    (.Received b st.peer msg.ratchetKey msg.counter m))
  (tr_recv.append (TREvE
    (.MessageKey (st.sessionInfo b) .receiver seed pqSalt msg.counter c.rIdx
      childIdx))).append
    (TRStE b
      { st with recv := DY.Libsignal.TripleRatchet.setRecvChain st.recv c', spqr := spqr' })

theorem Runs.bobStart {tr : ExecTrace} {b a : Participant} {kh : PQXDH.BobKeyHandles}
    {regA : Nat} {mh : PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    {ikB spk pqsk ikAPk vkA ek ct raw spqr' key seed pqSalt m : DY.Bytes}
    {opk : Option DY.Bytes} {honest : Bool} {keys : PQXDH.HandshakeKeys}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    {c' : DY.Libsignal.TripleRatchet.RecvChain}
    (hik : tr.at? kh.ik = some (PQStE b { kind := .identity, sk := ikB }))
    (hspk : tr.at? kh.spk = some (PQStE b { kind := .signedPrekey, sk := spk }))
    (hpq : tr.at? kh.pqspk = some (PQStE b { kind := .pqPrekey, sk := pqsk }))
    (hopk : StOpt tr b kh.opk opk)
    (hreg : tr.at? regA = some (PQEvE (.IdentityRegistered a ikAPk vkA honest)))
    (hek : tr.at? mh.ek = some (NetE ek)) (hct : tr.at? mh.ct = some (NetE ct))
    (hcan : PQXDH.isCanonicalKey ek = true)
    (hagree : PQXDH.bobAgreement ikB spk pqsk opk ikAPk ek ct = some keys)
    (hmsg : tr.at? mh.msg = some (NetE raw))
    (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg)
    (hver : msg.version = DY.Libsignal.TripleRatchet.messageVersion)
    (hlow : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey = false)
    (hcons : DY.Libsignal.TripleRatchet.consumeMessageKey
      (bobRatchetedChain keys msg.ratchetKey spk) msg.counter = some (seed, c'))
    (hspqr : DY.Spqr.spqrRecv
      (bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey
        (randTerm tr.length 32)).spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((tr.append (RndE 32)).append (NetE key)).at? pqIdx = some (NetE pqSalt))
    (hmac : msg.mac = DY.Libsignal.TripleRatchet.computeMac
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey
      (bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey
        (randTerm tr.length 32)).peerIk
      (bobRatchetedSt a (DY.DiffieHellman.dhPk ikB) ikAPk keys spk msg.ratchetKey
        (randTerm tr.length 32)).myIk msg.wire)
    (hdec : PQXDH.errToOption (DY.SymEnc.symDec
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).cipherKey
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m)
    (hused : ∀ o, opk = some o →
      PQXDH.opkUsedB ((tr.append (RndE 32)).append (NetE key)) b (DY.DiffieHellman.dhPk o) = false) :
    let o := bobOut ikB spk pqsk opk ikAPk ek ct keys
    let st := bobRatchetedSt a o.ikB o.ikA o.keys o.spkSk msg.ratchetKey (randTerm tr.length 32)
    let c := bobRatchetedChain o.keys msg.ratchetKey o.spkSk
    let tr_hs := bobStartPreSkipTr tr b a o msg key
    let skipped := msg.counter.toNat - c.index.toNat
    let childIdx := tr_hs.length + skipped + 2
    let tr_skip := ((DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey
      c.rIdx childIdx c.chainKey c.index skipped).run tr_hs).2.val
    let tr_recv := tr_skip.append (TREvE
      (.Received b st.peer msg.ratchetKey msg.counter m))
    BobRuns (DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqrMsgIdx) tr
      (tr_recv.length + 1)
      (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) := by
  intro o st c tr_hs skipped childIdx tr_skip tr_recv
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
  refine bsr_runs_bind (Runs.bobHandshake hik hspk hpq hopk hreg hek hct hcan hagree)
    (bsr_runs_bind (Runs.receiveSignalMsg hmsg hparse hver)
    (bsr_runs_bind (Runs.ensureReceiverChain_bobInitSt hlow) ?_))
  dsimp only [o, bobOut]; rw [hcons, hspqr]; dsimp only
  refine bsr_runs_bind (bsr_runs_sendMessage _ key)
    (bsr_runs_bind (Runs.receiveMessage hpqSalt)
    (bsr_runs_bind (Runs.verifyMacAndDecrypt hmac hdec) ?_))
  rcases opk with _ | o_opk
  · dsimp only [Option.map]
    exact bsr_runs_bind (Runs.traceLength _) (bsr_runs_bind (bsr_runs_logEvent_pq _ _)
      (bsr_runs_bind (Runs.logEvent_tr _ _) (bsr_runs_bind (Runs.logEvent_tr _ _)
      (bsr_runs_bind (Runs.logEvent_c _ _) (bsr_runs_bind (Runs.traceLength _)
      (bsr_runs_bind (Runs.logSkippedKeys _ _ _ _ _ _ _ _)
      (bsr_runs_bind (Runs.logEvent_tr _ _)
      (Runs.logMessageKeyAndStore b _ .receiver seed pqSalt msg.counter _ _ _ _))))))))
  · dsimp only [Option.map]
    have hused' : (!PQXDH.opkUsedB ((tr.append (RndE 32)).append (NetE key)) b
        (DY.DiffieHellman.dhPk o_opk)) = true := by simp [hused o_opk rfl]
    exact bsr_runs_bind (bsr_runs_guardOnTrace hused') (bsr_runs_bind (bsr_runs_logEvent_pq _ _)
      (bsr_runs_bind (Runs.traceLength _) (bsr_runs_bind (bsr_runs_logEvent_pq _ _)
      (bsr_runs_bind (Runs.logEvent_tr _ _) (bsr_runs_bind (Runs.logEvent_tr _ _)
      (bsr_runs_bind (Runs.logEvent_c _ _) (bsr_runs_bind (Runs.traceLength _)
      (bsr_runs_bind (Runs.logSkippedKeys _ _ _ _ _ _ _ _)
      (bsr_runs_bind (Runs.logEvent_tr _ _)
      (Runs.logMessageKeyAndStore b _ .receiver seed pqSalt msg.counter _ _ _ _))))))))))

theorem bsr_opkUsedB_append_nonEvent {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E} {b : Participant} {opkPk : DY.Bytes}
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none) :
    PQXDH.opkUsedB (tr.append e) b opkPk = PQXDH.opkUsedB tr b opkPk := by
  unfold PQXDH.opkUsedB
  rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?,
      DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?]
  have hlen : (tr.append e).length = tr.length + 1 := by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen, List.range_succ, List.any_append]
  have hn : ((tr.append e).at? tr.length :
      Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = none := by
    have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by simp [Symbolic.DYBridge.DY.Trace.length_eq_2]
    simp only [Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hnone]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [hn]
  simp only [Bool.or_false]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  refine ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, ?_⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, ?_⟩⟩ <;>
  · have hilt : i < tr.length := List.mem_range.mp hi
    have hev : ((tr.append e).at? i :
        Option (DY.ProtocolEvent.ExecEntryT PQXDH.PQXDHEvent)) = tr.at? i :=
      CompTrace.at?_append_of_lt tr e hilt
    simpa only [hev] using h

theorem opkUsedB_append_rnd_net (tr : ExecTrace) (b : Participant) (opkPk key : DY.Bytes) :
    PQXDH.opkUsedB ((tr.append (RndE 32)).append (NetE key)) b opkPk =
      PQXDH.opkUsedB tr b opkPk := by
  rw [bsr_opkUsedB_append_nonEvent rfl, bsr_opkUsedB_append_nonEvent rfl]

end Symbolic.Swarm.CREF
