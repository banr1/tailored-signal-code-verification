/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.TripleRatchet
public import Symbolic.Specifications.Model.PQXDH
import DY.Meta.CombineMacro

/-!
# Composed Symbolic Protocol (PQXDH + Triple Ratchet)

Composes the `PQXDH` handshake and threat transitions with the `TripleRatchet` messaging and state
exposure transitions into a single DyLean state machine (`Composed.reachability`). `aliceStart`
initializes Alice's `TRState` from `PQXDH.aliceHandshake`; `bobStart` atomically runs
`PQXDH.bobHandshake`, initializes Bob's `TRState`, and decrypts the opening `SignalMessage`.
-/

namespace DY.Libsignal.Composed

open DY.Comparse
open PQXDH (PQXDHState PQXDHEvent HandshakeKeys BundleHandles BobKeyHandles PreKeyMsgHandles
  serializedIk)
open TripleRatchet (SessionInfo TRState TREvent guardTrace)

public section ExecBytesConfig

attribute [scoped instance] TripleRatchet.HasExecBytes.bytesFunc
  TripleRatchet.HasExecBytes.bytesFunc0 TripleRatchet.HasExecBytes.bytesFunc1
  TripleRatchet.HasExecBytes.bytesFunc2 TripleRatchet.HasExecBytes.bytesFunc3
  TripleRatchet.HasExecBytes.bytesFunc4 TripleRatchet.HasExecBytes.bytesFunc5
  TripleRatchet.HasExecBytes.bytesFunc6 TripleRatchet.HasExecBytes.bytesFunc8
  TripleRatchet.HasExecBytes.bytesLen TripleRatchet.HasExecBytes.att
attribute [scoped instance] TripleRatchet.HasExecBytes.bytesLen0
  TripleRatchet.HasExecBytes.bytesLen1 TripleRatchet.HasExecBytes.bytesLen2
  TripleRatchet.HasExecBytes.bytesLen3 TripleRatchet.HasExecBytes.bytesLen4
  TripleRatchet.HasExecBytes.bytesLen5 TripleRatchet.HasExecBytes.bytesLen6
  TripleRatchet.HasExecBytes.bytesLen8
attribute [scoped instance] TripleRatchet.HasExecBytes.att0 TripleRatchet.HasExecBytes.att1
  TripleRatchet.HasExecBytes.att2 TripleRatchet.HasExecBytes.att3 TripleRatchet.HasExecBytes.att4
  TripleRatchet.HasExecBytes.att5 TripleRatchet.HasExecBytes.att6
  TripleRatchet.HasExecBytes.att8
attribute [scoped instance] TripleRatchet.HasExecBytes.bytesFuncSpqr
  TripleRatchet.HasExecBytes.bytesFuncTrWire
attribute [scoped instance] TripleRatchet.HasExecBytes.bytesLenSpqr
  TripleRatchet.HasExecBytes.bytesLenTrWire TripleRatchet.HasExecBytes.attSpqr
  TripleRatchet.HasExecBytes.attTrWire
attribute [scoped instance] PQXDH.HasExecBytes.bytesFuncKem PQXDH.HasExecBytes.bytesFuncSig
attribute [scoped instance] PQXDH.HasExecBytes.bytesLenKem PQXDH.HasExecBytes.bytesLenSig
  PQXDH.HasExecBytes.attKem PQXDH.HasExecBytes.attSig

/-- Unified term algebra extending both `TripleRatchet.HasExecBytes` and `PQXDH.HasExecBytes`. -/
class HasExecBytes extends
    toTRExecBytes : TripleRatchet.HasExecBytes,
    toPQXDHExecBytes : PQXDH.HasExecBytes

attribute [instance 50] HasExecBytes.toTRExecBytes HasExecBytes.toPQXDHExecBytes

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

/-- Ghost event linking a Triple Ratchet session `s` to the trace index `doneIdx` of its
`PQXDHEvent.AliceDone` or `PQXDHEvent.BobDone` event. -/
inductive ComposedEvent where
  | HandshakeSession (s: SessionInfo) (doneIdx: Nat)

end Structures

public section ExecTraceConfig

/-- Unified protocol trace carrying network messages, randomness, `TREvent`, `PQXDHEvent`,
`ComposedEvent`, and compromisable `TRState` and `PQXDHState` stores. -/
class HasExecTrace extends toCExecBytes : HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT TREvent)]
  [traceExec3: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT PQXDHEvent)]
  [traceExec4: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT ComposedEvent)]
  [traceExec5: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TRState)]
  [traceExec6: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT PQXDHState)]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec HasExecTrace.traceExec0
  HasExecTrace.traceExec1 HasExecTrace.traceExec2 HasExecTrace.traceExec3 HasExecTrace.traceExec4
  HasExecTrace.traceExec5 HasExecTrace.traceExec6 HasExecTrace.attBase

end ExecTraceConfig

@[expose] public section DerivedInstances

variable [HasExecTrace]

@[reducible] scoped instance toTripleRatchet: TripleRatchet.HasExecTrace where
  toHasExecBytes := HasExecTrace.toCExecBytes.toTRExecBytes
  traceExec := HasExecTrace.traceExec
  traceExec0 := HasExecTrace.traceExec0
  traceExec1 := HasExecTrace.traceExec1
  traceExec2 := HasExecTrace.traceExec2
  traceExec3 := HasExecTrace.traceExec5
  attBase := HasExecTrace.attBase

@[reducible] scoped instance toPQXDHSpqr: PQXDH.HasExecTrace where
  toPQXDHExecBytes := HasExecTrace.toCExecBytes.toPQXDHExecBytes
  traceExec := HasExecTrace.traceExec
  traceExec0 := HasExecTrace.traceExec0
  traceExec1 := HasExecTrace.traceExec1
  traceExec2 := HasExecTrace.traceExec3
  traceExec3 := HasExecTrace.traceExec6
  attBase := HasExecTrace.attBase

end DerivedInstances

@[expose] public section Specification

variable [HasExecTrace]

open DiffieHellman
open PersistentLocalState (storeLocalState)
open Network (sendMessage receiveMessage)
open Random (genRand)
open ProtocolEvent (logEvent)

/-- Alice's session initialization (`process_prekey_bundle` / `initialize_alice_session`): runs
`PQXDH.aliceHandshake`, draws Alice's initial sending ratchet key `dhsA`, publishes the unauthenticated
`PreKeySignalMessage` outer fields (`ek`, `ct`), logs `AliceDone`, `InitSession`, and
`HandshakeSession`, and stores Alice's initial `TRState`. All application ciphertexts (including
message 0) are sent separately via `TripleRatchet.messageEncrypt`. -/
def aliceStart (a b: Participant) (idStateIdx regIdxB: Nat) (h: BundleHandles) :
    Traceful Nat := do
  let o ← PQXDH.aliceHandshake a b idStateIdx regIdxB h
  let dhsA ← genRand 32
  let stA := TripleRatchet.initAliceState b (serializedIk o.ikA) (serializedIk o.ikB)
    dhsA o.spk o.keys.rk o.keys.ck o.keys.pqr
  let _ ← sendMessage o.ek
  let _ ← sendMessage o.ct
  let doneIdx ← TripleRatchet.traceLength
  logEvent (PQXDHEvent.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys)
  logEvent (TREvent.InitSession a b (dhPk dhsA) o.spk)
  logEvent (ComposedEvent.HandshakeSession (stA.sessionInfo a) doneIdx)
  storeLocalState a stA

/-- Bob's atomic session initialization (`message_decrypt_prekey`): runs `PQXDH.bobHandshake`,
constructs Bob's initial in-memory `TRState` (`sid` bound to both `normalizeX25519Key msg.ratchetKey`
and `keys.rk`), and decrypts the inner `SignalMessage` via `TripleRatchet.decryptInMemory`. State
and events (`OPKUsed`, `BobDone`, `DHRatchet`, `HonestDH`, `HandshakeSession`, skipped keys,
`Received`, `MessageKey`) are committed only if decryption succeeds. -/
def bobStart (b a: Participant) (kh: BobKeyHandles) (regIdxA: Nat) (mh: PreKeyMsgHandles)
    (pqIdx: Nat) (spqrMsgIdx: UInt32) : Traceful Nat := do
  let o ← PQXDH.bobHandshake b a kh regIdxA mh.ek mh.ct
  let msg ← TripleRatchet.receiveSignalMsg mh.msg
  let st0 := TripleRatchet.initBobState a (serializedIk o.ikB) (serializedIk o.ikA)
    o.spkSk msg.ratchetKey o.keys.rk o.keys.ck o.keys.pqr
  let pending ← TripleRatchet.decryptInMemory st0 msg pqIdx spqrMsgIdx
  match o.opk with
  | some opk =>
    guardTrace fun tr => !PQXDH.opkUsedB tr b opk
    logEvent (PQXDHEvent.OPKUsed b opk)
  | none => pure ()
  let doneIdx ← TripleRatchet.traceLength
  logEvent (PQXDHEvent.BobDone b a o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys)
  pending.logRatchet b
  logEvent (ComposedEvent.HandshakeSession (pending.st.sessionInfo b) doneIdx)
  pending.commit b

end Specification

public section Reachability

variable [HasExecTrace]

@[expose] public section
def aliceStart.reachability: ReachabilityConfig :=
  .make (fun ((a, b, idStateIdx, regIdxB, h):
      Participant × Participant × Nat × Nat × BundleHandles) =>
    aliceStart a b idStateIdx regIdxB h)
def bobStart.reachability: ReachabilityConfig :=
  .make (fun ((b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx):
      Participant × Participant × BobKeyHandles × Nat × PreKeyMsgHandles × Nat × UInt32) =>
    bobStart b a kh regIdxA mh pqIdx spqrMsgIdx)
end

#combine into ReachabilityConfig from
  Network,
  PQXDH.registerIdentity,
  PQXDH.registerCorruptIdentity,
  PQXDH.genSignedPrekey,
  PQXDH.genPQPrekey,
  PQXDH.genOneTimePrekey,
  aliceStart,
  bobStart,
  TripleRatchet.messageEncrypt,
  TripleRatchet.messageEncryptAbort,
  TripleRatchet.messageDecrypt,
  TripleRatchet.messageDecryptSkipped,
  TripleRatchet.exposeKey,
  TripleRatchet.exposeSpqr,
  TripleRatchet.exposeSkipped,
  PQXDH.compromiseIK,
  PQXDH.compromiseSPK,
  PQXDH.compromisePQSPK,
  PQXDH.compromiseOPK,
  PQXDH.breakDH,
  PQXDH.breakKEM,
  PQXDH.invertDH,
  PQXDH.invertKEM,

end Reachability

end DY.Libsignal.Composed
