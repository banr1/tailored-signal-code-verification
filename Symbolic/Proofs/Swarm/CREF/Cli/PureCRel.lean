/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RelPure
public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
public import Symbolic.Proofs.Swarm.CREF.TR.SendsFitRun
public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKey
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Machine-Free Composed Refinement Relation

Defines the hardware-independent session-record, history, and trace invariant `PureCRel`
for the CLI composed refinement proof.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

/-- Hardware-independent counterpart of `AliceInitPending` for an unacknowledged initiator pre-key
session. -/
def PureAliceInitPending (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (rec : HwBytes) : Prop :=
  ∃ (sess : Session (List (BitVec 8))) (sc : SenderChain) (remote : IdentityKey)
    (items : PendingPreKey) (kpk : PendingKyberPreKey) (st : TripleRatchet.TRState)
    (stateIdx ekIdx ctIdx : Nat) (ek ct : DY.Bytes),
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec sess ∧
    TR.Pure.slots_RecordInScopeP ⟨some sess⟩ ∧
    TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess⟩ ∧
    ((PersistentLocalState.getLocalState r.alice stateIdx : Traceful TripleRatchet.TRState).run
      (runTraceMoves r ms)).1 = some st ∧
    TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
    st.initiator = true ∧ st.peer = r.bob ∧
    (runTraceMoves r ms).getMessageSentAt ekIdx = some ek ∧
    (runTraceMoves r ms).getMessageSentAt ctIdx = some ct ∧
    sess.localRegistrationId = r.regIdA ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.state.previousCounter = st.pn.toBitVec ∧
    sess.state.localIdentity.serialize = gamma interpretation S g st.myIk ∧
    sess.state.remoteIdentity = some remote ∧
    remote.serialize = gamma interpretation S g st.peerIk ∧
    sess.state.senderChain = some sc ∧
    sc.ratchetKey.publicKey.bytes.toList =
      gamma interpretation S g (DY.DiffieHellman.dhPk st.dhs) ∧
    CryptoGames.HMAC.keyToBytes32 sc.chainKey.key = gamma interpretation S g st.cks ∧
    sc.chainKey.index = st.ns.toBitVec ∧
    sess.pendingPreKey = some items ∧
    items.timestamp = 0#64 ∧
    items.baseKey.serialize = ecKey (gamma interpretation S g ek) ∧
    sess.pendingKyberPreKey = some kpk ∧
    kpk.ciphertext = kyberKey (gamma interpretation S g ct) ∧
    sess.state.pqRatchetState = gamma interpretation S g st.spqr ∧
    ∃ recR : RecordRec, rec = recordBytes recR ∧
      TR.StateRel interpretation S g st recR ∧
      TR.TRKeyShape interpretation S g st ∧
      (∀ c ∈ recR.current.receiverChains, c.messageKeys = []) ∧
      (recR.current.receiverChains.map ChainRec.senderRatchetKey).Nodup

/-- Every `RecordRec` encoding of Bob's stored session record has `pendingKyberPreKey = none`. -/
def PureBobKyberNone (r : ProtocolSetup) (records : Participant → Option HwBytes) : Prop :=
  ∀ rr : RecordRec, records r.bob = some (recordBytes rr) →
    rr.current.pendingKyberPreKey = none

/-- Parameter bundle of canonicality, receive-simulation, and token predicates for
`PureTRRecordStateInv`. -/
structure TR.PureTRSlots where
  canon : Participant → HwBytes → Prop
  recvSim : Ghost → List Move → Prop
  tok : Unit → Prop

/-- Hardware-independent Triple Ratchet session-record invariant over `TR.PureTRSlots`. -/
def TR.PureTRRecordStateInv (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (Z : TR.PureTRSlots) (g : Ghost) (ms : List Move)
    (records : Participant → Option HwBytes) : Prop :=
  ∀ p b, records p = some b →
    (p = r₀.alice ∨ p = r₀.bob) ∧
    ∃ (rec : RecordRec) (st : TripleRatchet.TRState) (stateIdx : Nat),
      b = recordBytes rec ∧
      ((PersistentLocalState.getLocalState p stateIdx : Traceful TripleRatchet.TRState).run
        (runTraceMoves r₀ ms)).1 = some st ∧
      TripleRatchet.isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx = true ∧
      TR.StateRel interpretation S g st rec ∧
      (∀ c ∈ rec.current.receiverChains, ∀ k ∈ c.messageKeys,
        ∃ pk rIdx srcIdx skIdx seed,
          (runTraceMoves r₀ ms).EventLoggedAt
            (TripleRatchet.TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec k.1) seed
              rIdx srcIdx) skIdx ∧
          !TripleRatchet.skippedKeyUsedB (runTraceMoves r₀ ms) skIdx ∧
          !TripleRatchet.receiverKeyUsedB (runTraceMoves r₀ ms) (st.sessionInfo p) seed (UInt32.ofBitVec k.1)
            rIdx ∧
          gamma interpretation S g seed = k.2 ∧
          c.senderRatchetKey = TR.serializedKey (gamma interpretation S g pk) ∧
          (TripleRatchet.findRecvChain st.toDRState.recv pk).isSome = true) ∧
      (b.length < 2 ^ 32 - 2 ^ 20 → Z.canon p b) ∧
      TR.TRKeyShape interpretation S g st ∧
      ((rec.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
        (∀ c ∈ rec.current.receiverChains, (c.messageKeys.map Prod.fst).Nodup) ∧
        ∀ c ∈ rec.current.receiverChains, ∀ k ∈ c.messageKeys, ∃ ck, c.chainKey = some ck ∧ k.1 < ck.1)

def pureTrSlots (r : ProtocolSetup) : TR.PureTRSlots where
  canon := TR.PureTRRecordCanon r
  recvSim := fun _ _ => True
  tok := fun _ => True

/-- Active-session record relation: either steady-state `PureTRRecordStateInv` or Alice's pending
pre-key session. -/
def PureCRecRel (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (p : Participant) (b : HwBytes) : Prop :=
  TR.PureTRRecordStateInv interp r S (pureTrSlots r) g ms
      (fun q => if q = p then some b else none) ∨
    (p = r.alice ∧ PureAliceInitPending interp r S g ms b)

/-- Archived-session record relation: non-empty `previous` sessions with a valid active `current`
session. -/
def PureCPrevRel (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (p : Participant) (b : HwBytes) : Prop :=
  ∃ rr : RecordRec, b = recordBytes rr ∧ rr.previous ≠ [] ∧
    PureCRecRel interp r S g ms p (recordBytes { rr with previous := [] })

def PureCRecRelH (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (p : Participant) (b : HwBytes) : Prop :=
  PureCRecRel interp r S g ms p b ∨ PureCPrevRel interp r S g ms p b

/-- Per-explanation invariant combining `PureCRecRelH`, `CBook`, `CHist`, and `RoleSnapshots`. -/
def PureCRelAt (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (records : Participant → Option HwBytes)
    (sent accepted : List HwBytes) (acc : List MachineEvent) : Prop :=
  (∀ p b, records p = some b → (p = r.alice ∨ p = r.bob) ∧ b ≠ [] ∧
    PureCRecRelH interp r S g ms p b) ∧
  CBook interp r S g ms sent accepted acc ∧
  CHist interp r S g ms ∧
  RoleSnapshots r (runTraceMoves r ms)

/-- Trace and record invariant over `(records, sent, accepted, acc)` quantified over all `Clean`
explanations. -/
structure PureCRel (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (records : Participant → Option HwBytes)
    (sent accepted : List HwBytes) (acc : List MachineEvent) : Prop where
  oooAll   : COooAll records
  sendsFit : TR.SendsFit acc
  bka      : BobRecordBaseKeyInAccepted r records accepted
  bkn      : PureBobKyberNone r records
  clean    : ∀ g ms, Clean interp r S who ok g ms acc →
    PureCRelAt interp r S g ms records sent accepted acc ∧
    BobRecordBaseKeyInSession interp r S g ms records

end Symbolic.Swarm.CREF
