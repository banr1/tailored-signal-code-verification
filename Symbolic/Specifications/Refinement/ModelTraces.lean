/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Concrete.MachineEvents
public import Aesop.BuiltinRules
public import Mathlib.Data.Subtype
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToAdditive
public import Symbolic.Specifications.Model.Instance
public import Symbolic.Specifications.Refinement.Concretization

/-!
# Composed Model Steps, Traces, and Visible Entries

First-order step representation (`Step`), initial PKI/pre-key setup (`ProtocolSetup`, `setupTrace`),
observable entry projection (`stepView`), and faithful run predicate (`ModelRunWF`) for the
composed symbolic state machine `Composed.reachability`.
-/

@[expose] public section

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (x25519PublicKeySymbol)
open PQXDH (PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles)
open TripleRatchet (TREvent TRState)

/-- Provision Alice's and Bob's honest identities, Bob's signed X25519 and Kyber-1024 prekeys, and
(when `withOpk` holds) one one-time prekey for Bob. -/
def setupAct (a b : Participant) (withOpk : Bool) : Traceful Unit := do
  let _ ← PQXDH.registerIdentity a
  let hB ← PQXDH.registerIdentity b
  let _ ← PQXDH.genSignedPrekey b hB
  let _ ← PQXDH.genPQPrekey b hB
  if withOpk then do let _ ← PQXDH.genOneTimePrekey b; pure ()

/-- First-order inductive mirror of the 23 transitions in `Composed.reachability`. -/
inductive Step where
  | network (msg : DY.Bytes)
  | registerIdentity (p : Participant)
  | registerCorruptIdentity (p : Participant) (skIdx : Nat)
  | genSignedPrekey (b : Participant) (idStateIdx : Nat)
  | genPQPrekey (b : Participant) (idStateIdx : Nat)
  | genOneTimePrekey (b : Participant)
  | aliceStart (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles)
  | bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat) (mh : PreKeyMsgHandles)
      (pqIdx : Nat) (spqrMsgIdx : UInt32)
  | messageEncrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat)
  | messageEncryptAbort (me : Participant) (stateIdx : Nat)
  | messageDecrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32)
  | messageDecryptSkipped (me : Participant) (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat)
      (spqrMsgIdx : UInt32)
  | exposeKey (me : Participant) (stateIdx : Nat) (k : TripleRatchet.KeyComponent)
  | exposeSpqr (me : Participant) (stateIdx : Nat)
  | exposeSkipped (skippedKeyEventIdx : Nat)
  | compromiseIK (p : Participant) (stateIdx : Nat)
  | compromiseSPK (b : Participant) (stateIdx : Nat)
  | compromisePQSPK (b : Participant) (stateIdx : Nat)
  | compromiseOPK (b : Participant) (stateIdx : Nat)
  | breakDH
  | breakKEM
  | invertDH (pkIdx : Nat)
  | invertKEM (pkIdx : Nat)

abbrev stepIn (c : ReachabilityConfig) [i : ReachabilityConfig.HasStep c reachability]
    (x : c.Input) : reachability.Input :=
  i.inj x

def Step.toInput : Step → reachability.Input
  | .network msg => stepIn Network.reachability msg
  | .registerIdentity p => stepIn PQXDH.registerIdentity.reachability p
  | .registerCorruptIdentity p skIdx => stepIn PQXDH.registerCorruptIdentity.reachability (p, skIdx)
  | .genSignedPrekey b i => stepIn PQXDH.genSignedPrekey.reachability (b, i)
  | .genPQPrekey b i => stepIn PQXDH.genPQPrekey.reachability (b, i)
  | .genOneTimePrekey b => stepIn PQXDH.genOneTimePrekey.reachability b
  | .aliceStart a b idStateIdx regIdxB h =>
    stepIn Composed.aliceStart.reachability (a, b, idStateIdx, regIdxB, h)
  | .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    stepIn Composed.bobStart.reachability (b, a, kh, regIdxA, mh, pqIdx, spqrMsgIdx)
  | .messageEncrypt me stateIdx coinsLen pqIdx =>
    stepIn TripleRatchet.messageEncrypt.reachability (me, stateIdx, coinsLen, pqIdx)
  | .messageEncryptAbort me stateIdx =>
    stepIn TripleRatchet.messageEncryptAbort.reachability (me, stateIdx)
  | .messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx =>
    stepIn TripleRatchet.messageDecrypt.reachability (me, stateIdx, msgIdx, pqIdx, spqrMsgIdx)
  | .messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx =>
    stepIn TripleRatchet.messageDecryptSkipped.reachability
      (me, stateIdx, msgIdx, skIdx, pqIdx, spqrMsgIdx)
  | .exposeKey me stateIdx k => stepIn TripleRatchet.exposeKey.reachability (me, stateIdx, k)
  | .exposeSpqr me stateIdx => stepIn TripleRatchet.exposeSpqr.reachability (me, stateIdx)
  | .exposeSkipped skIdx => stepIn TripleRatchet.exposeSkipped.reachability skIdx
  | .compromiseIK p stateIdx => stepIn PQXDH.compromiseIK.reachability (p, stateIdx)
  | .compromiseSPK b stateIdx => stepIn PQXDH.compromiseSPK.reachability (b, stateIdx)
  | .compromisePQSPK b stateIdx => stepIn PQXDH.compromisePQSPK.reachability (b, stateIdx)
  | .compromiseOPK b stateIdx => stepIn PQXDH.compromiseOPK.reachability (b, stateIdx)
  | .breakDH => stepIn PQXDH.breakDH.reachability ()
  | .breakKEM => stepIn PQXDH.breakKEM.reachability ()
  | .invertDH pkIdx => stepIn PQXDH.invertDH.reachability pkIdx
  | .invertKEM pkIdx => stepIn PQXDH.invertKEM.reachability pkIdx

/-- Resulting trace after running `s` on `tr`. -/
def Step.next (s : Step) : ExecTrace → ExecTrace :=
  fun tr => ((reachability.step s.toInput).2.run tr).2.val

/-- Whether `s` succeeds on `tr`. -/
def Step.ok (s : Step) (tr : ExecTrace) : Bool :=
  ((reachability.step s.toInput).2.run tr).1.isSome

/-- Reachability precondition of `s` on `tr`. -/
def Step.PreCond (s : Step) (tr : ExecTrace) : Prop := reachability.PreCond s.toInput tr

/-- Alignment category of a `Step` with respect to CLI trace events. -/
inductive StepClass where
  /-- Honest party transition matched by one exit-0 CLI `RunEvent`. -/
  | party
  /-- Compromise, exposure, break, inversion, or corrupt registration matched by one `EnvEvent`. -/
  | env
  /-- Attacker `network` deduction step matched by no CLI event. -/
  | invisible
  /-- Key-provisioning step permitted only in the initial setup prefix. -/
  | setup
  deriving DecidableEq

def Step.cls : Step → StepClass
  | .network .. => .invisible
  | .registerIdentity .. => .setup
  | .genSignedPrekey .. => .setup
  | .genPQPrekey .. => .setup
  | .genOneTimePrekey .. => .setup
  | .aliceStart .. => .party
  | .bobStart .. => .party
  | .messageEncrypt .. => .party
  | .messageEncryptAbort .. => .party
  | .messageDecrypt .. => .party
  | .messageDecryptSkipped .. => .party
  | .exposeKey .. => .env
  | .exposeSpqr .. => .env
  | .exposeSkipped .. => .env
  | .compromiseIK .. => .env
  | .compromiseSPK .. => .env
  | .compromisePQSPK .. => .env
  | .compromiseOPK .. => .env
  | .breakDH => .env
  | .breakKEM => .env
  | .invertDH .. => .env
  | .invertKEM .. => .env
  | .registerCorruptIdentity .. => .env

/-- Acting or compromised participant of a step (`none` for `exposeSkipped` and global steps). -/
def Step.party? : Step → Option Participant
  | .aliceStart a .. => some a
  | .bobStart b .. => some b
  | .messageEncrypt me .. => some me
  | .messageEncryptAbort me _ => some me
  | .messageDecrypt me .. => some me
  | .messageDecryptSkipped me .. => some me
  | .exposeKey me .. => some me
  | .exposeSpqr me _ => some me
  | .compromiseIK p _ => some p
  | .compromiseSPK b _ => some b
  | .compromisePQSPK b _ => some b
  | .compromiseOPK b _ => some b
  | _ => none

/-- Network handle read by `messageDecrypt` or `messageDecryptSkipped` (`none` otherwise). -/
def Step.decryptMsgIdx? : Step → Option Nat
  | .messageDecrypt _ _ msgIdx .. => some msgIdx
  | .messageDecryptSkipped _ _ msgIdx .. => some msgIdx
  | _ => none

/-- Observable kind of a `VisEntry` (`pt`, `send`, `rng`, `accept`, `recv`, or `leak`). -/
inductive VisEventKind where
  | pt | send | rng | accept | recv | leak
  deriving DecidableEq

/-- Byte-level encoding layout relating concrete `HwBytes` to the symbolic terms in a `VisEntry`. -/
inductive VisByteLayout where
  | single
  | whisper
  | bundle
  | preKeySend
  | preKeyRecv
  /-- `0x03 || PreKeySignalMessage` decrypted on an existing Bob session whose base key lies in
  `eks` (`promote_matching_session`). -/
  | preKeyInner (eks : List DY.Bytes)
  | fresh (n : Nat)
  | kyberCoin (j : Nat)
  | unconstrained
  | leakPq (pq : Bool)
  | leakRecord
  deriving DecidableEq

/-- Observable entry emitted by a `Step`, with optional trace index `anchor` of its logged event. -/
structure VisEntry where
  kind : VisEventKind
  terms : List DY.Bytes
  layout : VisByteLayout
  anchor : Option Nat

def randTerm (i n : Nat) : DY.Bytes := ({timestamp := i, size := n} : DY.Random.Random DY.Bytes).pack

def newIndices (tr tr' : ExecTrace) : List Nat := List.range' tr.length (tr'.length - tr.length)

def newRandoms (tr tr' : ExecTrace) : List (DY.Bytes × Nat) :=
  (newIndices tr tr').filterMap fun i =>
    (tr'.at? i : Option DY.Random.ExecEntryT).map fun e => (randTerm i e.length, e.length)

def received (tr : ExecTrace) (hs : List Nat) : List DY.Bytes :=
  hs.filterMap fun i => tr.getMessageSentAt i

def rngEntry (t : DY.Bytes) : VisEntry := ⟨.rng, [t], .single, none⟩

def eventIdx (p : PQXDHEvent → Bool) (tr tr' : ExecTrace) : Option Nat :=
  (newIndices tr tr').find? fun i => ((tr'.getEventAt PQXDHEvent i).map p).getD false

def isAliceDone : PQXDHEvent → Bool
  | .AliceDone .. => true
  | _ => false

def isBobDone : PQXDHEvent → Bool
  | .BobDone .. => true
  | _ => false

def receivedPlaintext (tr tr' : ExecTrace) : Option DY.Bytes :=
  (newIndices tr tr').findSome? fun i =>
    match tr'.getEventAt TREvent i with
    | some (.Received _ _ _ _ m) => some m
    | _ => none

def lastSent (tr tr' : ExecTrace) : Option DY.Bytes :=
  if tr.length < tr'.length then tr'.getMessageSentAt (tr'.length - 1) else none

def kyberCoinEntries (entropy : DY.Bytes) : List VisEntry :=
  (List.range 32).map fun j => ⟨.rng, [entropy], .kyberCoin j, none⟩

def aliceDraws (done : Option Nat) : List DY.Bytes → List VisEntry
  | [] => []
  | [ek] => [rngEntry ek]
  | ek :: entropy :: rest =>
    rngEntry ek :: kyberCoinEntries entropy ++
      (rest.take 1).map fun dhsA => ({ rngEntry dhsA with anchor := done } : VisEntry)

def aliceVis (tr tr' : ExecTrace) (h : BundleHandles) : List VisEntry :=
  ⟨.recv, received tr ([h.spk, h.spkSig, h.pqpk, h.pqpkSig] ++ h.opk.toList), .bundle, none⟩ ::
    aliceDraws (eventIdx isAliceDone tr tr') ((newRandoms tr tr').map (·.1))

def bobOpkPk (b : Participant) (h : BobKeyHandles) (tr : ExecTrace) : Option DY.Bytes :=
  h.opk.bind fun i => ((PQXDH.getKey b i .oneTimePrekey).run tr).1.map DY.DiffieHellman.dhPk

def bobVis (tr tr' : ExecTrace) (mh : PreKeyMsgHandles) (opk : Option DY.Bytes) :
    List VisEntry :=
  ⟨.recv, received tr [mh.ek, mh.ct, mh.msg] ++ opk.toList, .preKeyRecv, none⟩ ::
    (newRandoms tr tr').map (fun r => rngEntry r.1) ++
    ((receivedPlaintext tr tr').map fun m =>
      (⟨.accept, [m], .single, eventIdx isBobDone tr tr'⟩ : VisEntry)).toList

def encDraws : List (DY.Bytes × Nat) → List VisEntry
  | [] => []
  | (m, _) :: rest =>
    ⟨.pt, [m], .single, none⟩ :: (rest.filter (·.2 != 0)).map fun r => rngEntry r.1

def _root_.DY.ExecTrace.getLocalStateAt (StateT : Type) [ExecTraceTypes]
    [ExecTraceTypes.Has (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState StateT))]
    (tr : ExecTrace) (i : Nat) : Option (PersistentLocalState.LocalState StateT) :=
  (tr.at? i : Option (PersistentGlobalState.State.ExecEntryT
    (PersistentLocalState.LocalState StateT))).map (·.st)

def sessionHandshakeEvents (tr : ExecTrace) (s0 : TripleRatchet.SessionInfo) : List PQXDHEvent :=
  (List.range tr.length).filterMap fun i =>
    match tr.getEventAt ComposedEvent i with
    | some (.HandshakeSession s d) => if s = s0 then tr.getEventAt PQXDHEvent d else none
    | none => none

/-- Base keys (`alice_base_key`) recorded by `BobDone` events linked to the session stored at
`stateIdx` on `tr`. -/
def sessionBaseKeys (tr : ExecTrace) (stateIdx : Nat) : List DY.Bytes :=
  match tr.getLocalStateAt TRState stateIdx with
  | some ls =>
    (sessionHandshakeEvents tr (ls.state.sessionInfo ls.participant)).filterMap fun
      | .BobDone _ _ _ _ _ _ _ ek _ _ => some ek
      | _ => none
  | none => []

def decVis (tr tr' : ExecTrace) (stateIdx msgIdx : Nat) (wrapped : Bool) : List VisEntry :=
  ((tr.getMessageSentAt msgIdx).map fun b =>
    (⟨.recv, [b], if wrapped then .preKeyInner (sessionBaseKeys tr stateIdx) else .whisper,
      none⟩ : VisEntry)).toList ++
    (newRandoms tr tr').map (fun r => rngEntry r.1) ++
    ((receivedPlaintext tr tr').map fun m => (⟨.accept, [m], .single, none⟩ : VisEntry)).toList

def pqExposureAt (tr' : ExecTrace) (j : Nat) : Option VisEntry :=
  let term := (tr'.getMessageSentAt (j + 1)).toList
  match tr'.getEventAt PQXDHEvent j with
  | some (.CompromisedIK ..) | some (.CompromisedSPK ..) | some (.CompromisedOPK ..) =>
    some ⟨.leak, term, .leakPq false, some j⟩
  | some (.CompromisedPQSPK ..) => some ⟨.leak, term, .leakPq true, some j⟩
  | _ => none

def trExposureAt (tr' : ExecTrace) (j : Nat) : Option VisEntry :=
  let term := (tr'.getMessageSentAt (j + 1)).toList
  match tr'.getEventAt TREvent j with
  | some (.ExposedRK ..) | some (.ExposedDHs ..) | some (.ExposedCKs ..)
  | some (.ExposedCKr ..) | some (.ExposedMK ..) | some (.ExposedSpqr ..) =>
    some ⟨.leak, term, .leakRecord, some j⟩
  | _ => none

def exposures (tr tr' : ExecTrace) : List VisEntry :=
  (newIndices tr tr').filterMap (pqExposureAt tr') ++ (newIndices tr tr').filterMap (trExposureAt tr')

/-- Provisioned setup parameters: Alice and Bob identities, registration and prekey IDs, Bob's
3169-byte Kyber secret key, and concrete bytes for setup draws (`fresh`) and opaque public terms
(`opaqueBytes`). -/
structure ProtocolSetup where
  alice : Participant
  bob : Participant
  withOpk : Bool
  regIdA : BitVec 32
  regIdB : BitVec 32
  spkId : BitVec 32
  kpkId : BitVec 32
  opkId : BitVec 32
  kyberSecB : HwBytes
  fresh : Nat → Nat → HwBytes
  opaqueBytes : DY.Bytes → HwBytes

/-- Initial model trace produced by running `setupAct` on the empty trace. -/
def setupTrace (r : ProtocolSetup) : ExecTrace := ((setupAct r.alice r.bob r.withOpk).run Trace.nil).2.val

def setupRandoms (r : ProtocolSetup) : List DY.Bytes := (newRandoms Trace.nil (setupTrace r)).map (·.1)

def setupSent (r : ProtocolSetup) : List DY.Bytes :=
  (newIndices Trace.nil (setupTrace r)).filterMap fun i => (setupTrace r).getMessageSentAt i

def setupSecret (r : ProtocolSetup) (k : Nat) : DY.Bytes := ((setupRandoms r)[k]?).getD (randTerm 0 0)

def setupPublic (r : ProtocolSetup) (k : Nat) : DY.Bytes := ((setupSent r)[k]?).getD (randTerm 0 0)

def ecKey (b : HwBytes) : HwBytes := 0x05#8 :: b

def kyberKey (b : HwBytes) : HwBytes := 0x08#8 :: b

/-- X25519 public key bytes computed from clamped private key bytes `b`. -/
def pubBytes (interpretation : ExternInterpretation) (b : HwBytes) : HwBytes :=
  (interpretation x25519PublicKeySymbol [clamp b]).getD []

def setupRandomsAt (r : ProtocolSetup) : List (Nat × Nat) :=
  (newIndices Trace.nil (setupTrace r)).filterMap fun i =>
    ((setupTrace r).at? i : Option DY.Random.ExecEntryT).map fun e => (i, e.length)

def secretBytes (r : ProtocolSetup) (k : Nat) : HwBytes :=
  (((setupRandomsAt r)[k]?).map fun p => r.fresh p.1 p.2).getD []

namespace ProtocolSetup

def ikASecTerm (r : ProtocolSetup) : DY.Bytes := setupSecret r 0
def ikBSecTerm (r : ProtocolSetup) : DY.Bytes := setupSecret r 1
def spkSecTerm (r : ProtocolSetup) : DY.Bytes := setupSecret r 2
def pqskSecTerm (r : ProtocolSetup) : DY.Bytes := setupSecret r 4
def opkSecTerm (r : ProtocolSetup) : DY.Bytes := setupSecret r 6

def ikAPubTerm (r : ProtocolSetup) : DY.Bytes := setupPublic r 0
def ikBPubTerm (r : ProtocolSetup) : DY.Bytes := setupPublic r 2
def spkPubTerm (r : ProtocolSetup) : DY.Bytes := setupPublic r 4
def spkSigTerm (r : ProtocolSetup) : DY.Bytes := setupPublic r 5
def pqpkPubTerm (r : ProtocolSetup) : DY.Bytes := setupPublic r 6
def pqpkSigTerm (r : ProtocolSetup) : DY.Bytes := setupPublic r 7
def opkPubTerm (r : ProtocolSetup) : DY.Bytes := setupPublic r 8

def ikASecBytes (r : ProtocolSetup) : HwBytes := secretBytes r 0
def ikBSecBytes (r : ProtocolSetup) : HwBytes := secretBytes r 1
def spkSecBytes (r : ProtocolSetup) : HwBytes := secretBytes r 2
def opkSecBytes (r : ProtocolSetup) : HwBytes := secretBytes r 6

end ProtocolSetup

def storedStates (r : ProtocolSetup) (tr : ExecTrace) :
    List (PersistentLocalState.LocalState TRState) :=
  (newIndices (setupTrace r) tr).filterMap (tr.getLocalStateAt TRState)

/-- Whether session `s` has decrypted any incoming message before `stateIdx`. -/
def sessionHasDecrypted (tr : ExecTrace) (s : TripleRatchet.SessionInfo) (stateIdx : Nat) : Bool :=
  (List.range stateIdx).any fun j =>
    match tr.getEventAt TREvent j with
    | some (.MessageKey s' .receiver ..) => decide (s' = s)
    | _ => false

/-- Pending `(ek, ct)` pre-key items for an Alice session at `stateIdx` prior to decrypting a
reply (`none` once acknowledged or for Bob sessions). -/
def pendingPreKey (tr : ExecTrace) (stateIdx : Nat) : Option (DY.Bytes × DY.Bytes) :=
  match tr.getLocalStateAt TRState stateIdx with
  | some ls =>
    let s0 := ls.state.sessionInfo ls.participant
    if sessionHasDecrypted tr s0 stateIdx then none
    else
      (sessionHandshakeEvents tr s0).findSome? fun
        | .AliceDone _ _ _ _ _ _ _ ek ct _ => some (ek, ct)
        | _ => none
  | none => none

/-- Observable `send` entry of an encryption step on `stateIdx`, matching `wrapped` against
`pendingPreKey tr stateIdx`. -/
def encSendEntry (tr tr' : ExecTrace) (stateIdx : Nat) (wrapped : Bool) : List VisEntry :=
  match lastSent tr tr' with
  | some w =>
    match wrapped, pendingPreKey tr stateIdx with
    | true, some (ek, ct) => [⟨.send, [ek, ct, w], .preKeySend, none⟩]
    | false, none => [⟨.send, [w], .whisper, none⟩]
    | _, _ => []
  | none => []

/-- Observable `VisEntry` sequence emitted by running `s` from `tr` (suppressing `send` and
`accept` entries when `s.ok tr = false`). -/
def stepView (s : Step) (tr : ExecTrace) (wrapped : Bool) : List VisEntry :=
  let tr' := s.next tr
  let own : List VisEntry :=
    match s with
    | .aliceStart _ _ _ _ h => aliceVis tr tr' h
    | .bobStart b _ kh _ mh _ _ => bobVis tr tr' mh (bobOpkPk b kh tr)
    | .messageEncrypt _ stateIdx .. =>
      encDraws (newRandoms tr tr') ++ encSendEntry tr tr' stateIdx wrapped
    | .messageEncryptAbort .. => encDraws (newRandoms tr tr')
    | .messageDecrypt _ stateIdx msgIdx .. => decVis tr tr' stateIdx msgIdx wrapped
    | .messageDecryptSkipped _ stateIdx msgIdx .. => decVis tr tr' stateIdx msgIdx wrapped
    | _ => []
  (if s.ok tr then own else own.filter fun v => v.kind != .send && v.kind != .accept) ++
    exposures tr tr'

def runSteps : List Step → ExecTrace → ExecTrace
  | [], tr => tr
  | s :: ss, tr => runSteps ss (s.next tr)

/-- Trace produced by running `ss` starting from `setupTrace r`. -/
def runTrace (r : ProtocolSetup) (ss : List Step) : ExecTrace := runSteps ss (setupTrace r)

/-- Trace handle at which `messageEncrypt` run from `tr` publishes its SPQR send key. -/
def encryptOwnSpqrKeyIdx (tr : ExecTrace) : Nat := tr.length + 2

/-- Out-of-range `pqIdx` handle modeling an `spqr::send` failure after coin draw and key
publication. -/
def encryptAbortAfterSpqrIdx (tr : ExecTrace) : Nat := tr.length + 3

/-- SPQR send key published by a non-aborting `messageEncrypt` step `s` on `tr`. -/
def Step.publishedSpqrKey? (s : Step) (tr : ExecTrace) : Option DY.Bytes :=
  match s with
  | .messageEncrypt _ _ _ pqIdx =>
    if pqIdx = encryptAbortAfterSpqrIdx tr then none
    else (s.next tr).getMessageSentAt (encryptOwnSpqrKeyIdx tr)
  | _ => none

/-- Step-local refinement invariants on `s` at `tr`: exposures target current snapshots/chains, and
`messageEncrypt` draws `coinsLen ∈ {0, 32, 64}` and reads its own SPQR key handle (or aborts via
`encryptAbortAfterSpqrIdx tr`). -/
def Step.LocalOk (s : Step) (tr : ExecTrace) : Prop :=
  match s with
  | .exposeKey _ stateIdx _ | .exposeSpqr _ stateIdx =>
    TripleRatchet.isCurrentSnapshot tr stateIdx = true
  | .exposeSkipped skIdx =>
    TripleRatchet.isSkippedChainCurrent tr skIdx = true
  | .messageEncrypt _ _ coinsLen pqIdx =>
    (coinsLen = 0 ∨ coinsLen = 32 ∨ coinsLen = 64) ∧
      (pqIdx = encryptOwnSpqrKeyIdx tr ∨ pqIdx = encryptAbortAfterSpqrIdx tr)
  | _ => True

def StepsWF : List Step → ExecTrace → Prop
  | [], _ => True
  | s :: ss, tr => s.PreCond tr ∧ s.LocalOk tr ∧ StepsWF ss (s.next tr)

/-- `(me, stateIdx, storesSuccessor)` for steps that load a stored `TRState` snapshot. -/
def Step.stateLoad? : Step → Option (Participant × Nat × Bool)
  | .messageEncrypt me stateIdx .. => some (me, stateIdx, true)
  | .messageEncryptAbort me stateIdx => some (me, stateIdx, false)
  | .messageDecrypt me stateIdx .. => some (me, stateIdx, true)
  | .messageDecryptSkipped me stateIdx .. => some (me, stateIdx, true)
  | _ => none

/-- Linear consumption of stored session snapshots: once a step loads snapshot `k` and succeeds in
storing a successor, no later step loads `k`. -/
def StepsStateFaithful (r : ProtocolSetup) (ss : List Step) : Prop :=
  ∀ (i j : Nat) (si sj : Step) (p : Participant) (k : Nat) (b : Bool), i < j →
    ss[i]? = some si → ss[j]? = some sj →
    si.stateLoad? = some (p, k, true) →
    si.ok (runTrace r (ss.take i)) = true →
    sj.stateLoad? = some (p, k, b) → False

/-- Faithful model run `ss` from `ProtocolSetup` `r`: setup draws succeed and are reachable, every
step satisfies `PreCond` and `LocalOk`, and stored session snapshots are consumed linearly. -/
def ModelRunWF (r : ProtocolSetup) (ss : List Step) : Prop :=
  (setupRandoms r).length = (if r.withOpk then 7 else 6) ∧
  (setupTrace r).Reachable reachability ∧
  StepsWF ss (setupTrace r) ∧
  StepsStateFaithful r ss

end DY.Libsignal.Composed.Refinement
