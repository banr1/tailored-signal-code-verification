/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ModelTraces

/-!
# Move-Based Model Traces and Faithfulness Predicates

Defines hardware `MachineEvent`s, composed-model `Move` transitions, visible-entry projections
`Move.vis` and `runVis`, and the move-run well-formedness predicate `ModelRun`.
-/

@[expose] public section

namespace DY.Libsignal.HwEvents

/-- Hardware-granularity events observed across libsignal session calls. -/
inductive MachineEvent
  | pt    (plaintext : HwBytes)
  | send  (wire : HwBytes)
  | recv  (wire : HwBytes)
  | rng   (bytes : HwBytes)
  /-- A receive accepted the message and returned this plaintext. -/
  | accept (plaintext : HwBytes)
  /-- A party's record, revealed to the environment. -/
  | leak  (record : HwBytes)
  deriving DecidableEq, Repr

end DY.Libsignal.HwEvents

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open PQXDH (PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles)
open TripleRatchet (TREvent TRState)

/-! ## Moves -/

/-- Transition of the composed model (`reachability`), together with `reject` and `encryptFail`. -/
inductive Move where
  | setup (a b : Participant) (withOpk : Bool)
  /-- `aliceStart` showing `shown` visible entries. -/
  | aliceStart (a b : Participant) (idStateIdx regIdxB : Nat) (h : BundleHandles) (shown : Nat)
  /-- `bobStart` showing `shown` visible entries. -/
  | bobStart (b a : Participant) (kh : BobKeyHandles) (regIdxA : Nat) (mh : PreKeyMsgHandles)
      (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat)
  /-- `messageEncrypt me stateIdx coinsLen pqIdx`, optionally wrapping the output in a
  `PreKeySignalMessage` with base-key and Kyber-ciphertext handles `wrap = some (ekIdx, ctIdx)`. -/
  | encrypt (me : Participant) (stateIdx coinsLen pqIdx : Nat) (wrap : Option (Nat × Nat))
  | encryptAbort (me : Participant) (stateIdx : Nat)
  /-- `messageEncrypt` with out-of-range salt handle `traceLength + 3`, stopping after SPQR key
  publication. -/
  | encryptFail (me : Participant) (stateIdx coinsLen : Nat)
  /-- `messageDecrypt`, with `wrapped = true` when delivered inside a `PreKeySignalMessage`. -/
  | decrypt (me : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
  /-- `messageDecryptSkipped`, with `wrapped` as for `decrypt`. -/
  | decryptSkipped (me : Participant) (stateIdx msgIdx skippedKeyEventIdx pqIdx : Nat)
      (spqrMsgIdx : UInt32) (wrapped : Bool)
  /-- Rejected call consuming one unconstrained `recv` and fresh draws of lengths `draws`. -/
  | reject (draws : List Nat)
  | compromiseIK (p : Participant) (stateIdx : Nat)
  | compromiseSPK (b : Participant) (stateIdx : Nat)
  | compromisePQSPK (b : Participant) (stateIdx : Nat)
  | compromiseOPK (b : Participant) (stateIdx : Nat)
  | exposeKey (me : Participant) (stateIdx : Nat) (k : TripleRatchet.KeyComponent)
  | exposeSpqr (me : Participant) (stateIdx : Nat)
  | exposeSkipped (skippedKeyEventIdx : Nat)
  | attackerSend (msg : DY.Bytes)
  | brkDH
  | brkKEM

/-- Traceful computation executed by a `Move` (discarding return values). -/
def Move.act : Move → Traceful Unit
  | .setup a b withOpk => setupAct a b withOpk
  | .aliceStart a b idStateIdx regIdxB h _ => do
    let _ ← Composed.aliceStart a b idStateIdx regIdxB h; pure ()
  | .bobStart b a kh regIdxA mh pqIdx spqrMsgIdx _ => do
    let _ ← Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx; pure ()
  | .encrypt me stateIdx coinsLen pqIdx _ => do
    let _ ← TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx; pure ()
  | .encryptAbort me stateIdx => do let _ ← TripleRatchet.messageEncryptAbort me stateIdx; pure ()
  | .encryptFail me stateIdx coinsLen => do
    let n ← TripleRatchet.traceLength
    let _ ← TripleRatchet.messageEncrypt me stateIdx coinsLen (n + 3); pure ()
  | .decrypt me stateIdx msgIdx pqIdx spqrMsgIdx _ => do
    let _ ← TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx; pure ()
  | .decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx _ => do
    let _ ← TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx
      spqrMsgIdx
    pure ()
  | .reject _ => pure ()
  | .compromiseIK p stateIdx => do let _ ← PQXDH.compromiseIK p stateIdx; pure ()
  | .compromiseSPK b stateIdx => do let _ ← PQXDH.compromiseSPK b stateIdx; pure ()
  | .compromisePQSPK b stateIdx => do let _ ← PQXDH.compromisePQSPK b stateIdx; pure ()
  | .compromiseOPK b stateIdx => do let _ ← PQXDH.compromiseOPK b stateIdx; pure ()
  | .exposeKey me stateIdx k => do let _ ← TripleRatchet.exposeKey me stateIdx k; pure ()
  | .exposeSpqr me stateIdx => do let _ ← TripleRatchet.exposeSpqr me stateIdx; pure ()
  | .exposeSkipped skippedKeyEventIdx => do
    let _ ← TripleRatchet.exposeSkipped skippedKeyEventIdx; pure ()
  | .attackerSend msg => do let _ ← Network.sendMessage msg; pure ()
  | .brkDH => PQXDH.breakDH
  | .brkKEM => PQXDH.breakKEM

def Move.next (m : Move) (tr : ExecTrace) : ExecTrace := (m.act.run tr).2.val

def Move.isSetup : Move → Bool
  | .setup .. => true
  | _ => false

/-! ## Visible Entries -/

def eventKind : HwEvents.MachineEvent → VisEventKind
  | .pt _ => .pt | .send _ => .send | .recv _ => .recv | .rng _ => .rng | .accept _ => .accept
  | .leak _ => .leak

def eventBytes : HwEvents.MachineEvent → HwBytes
  | .pt b | .send b | .recv b | .rng b | .accept b | .leak b => b

/-- Outgoing `send` entry of an encrypt step from `tr` to `tr'`, either as a whisper message or
wrapped as a `PreKeySignalMessage` using `wrap`. -/
def encSend (tr tr' : ExecTrace) (wrap : Option (Nat × Nat)) : List VisEntry :=
  match lastSent tr tr' with
  | some w =>
    match wrap with
    | none => [⟨.send, [w], .whisper, none⟩]
    | some (e, c) => [⟨.send, received tr [e, c] ++ [w], .preKeySend, none⟩]
  | none => []

/-- Visible entries of an encrypt step from `tr` to `tr'`: `encDraws` followed optionally by
`encSend`. -/
def encVis (tr tr' : ExecTrace) (wrap : Option (Nat × Nat)) (withSend : Bool) : List VisEntry :=
  encDraws (newRandoms tr tr') ++ (if withSend then encSend tr tr' wrap else [])

/-- Visible entries emitted by move `m` from trace `tr`, including any logged `exposures`. -/
def Move.vis (m : Move) (tr : ExecTrace) : List VisEntry :=
  let tr' := m.next tr
  (match m with
    | .aliceStart _ _ _ _ h shown => (aliceVis tr tr' h).take shown
    | .bobStart b _ kh _ mh _ _ shown => (bobVis tr tr' mh (bobOpkPk b kh tr)).take shown
    | .encrypt _ _ _ _ wrap => encVis tr tr' wrap true
    | .encryptAbort .. => encVis tr tr' none false
    | .encryptFail .. => encVis tr tr' none false
    | .decrypt _ stateIdx msgIdx _ _ wrapped => decVis tr tr' stateIdx msgIdx wrapped
    | .decryptSkipped _ stateIdx msgIdx _ _ _ wrapped => decVis tr tr' stateIdx msgIdx wrapped
    | .reject draws =>
      ⟨.recv, [], .unconstrained, none⟩ :: draws.map fun n => ⟨.rng, [], .fresh n, none⟩
    | _ => []) ++
  exposures tr tr'

/-- Executes `ms` starting from `tr`, returning the final trace and accumulated visible entries. -/
def runMoves : List Move → ExecTrace → ExecTrace × List VisEntry
  | [], tr => (tr, [])
  | m :: ms, tr =>
    let (tr', vs) := runMoves ms (m.next tr)
    (tr', m.vis tr ++ vs)

/-! ## Runs from Provisioned Setup -/

def ProtocolSetup.setupMove (r : ProtocolSetup) : Move := .setup r.alice r.bob r.withOpk

/-- Final model trace after executing `r.setupMove` followed by `ms`. -/
def runTraceMoves (r : ProtocolSetup) (ms : List Move) : ExecTrace := (runMoves (r.setupMove :: ms) Trace.nil).1

/-- Visible entries emitted by `r.setupMove` followed by `ms`. -/
def runVis (r : ProtocolSetup) (ms : List Move) : List VisEntry :=
  (runMoves (r.setupMove :: ms) Trace.nil).2

theorem setupMove_next_nil (r : ProtocolSetup) : r.setupMove.next Trace.nil = setupTrace r := rfl

theorem setupMove_next_nil' (r : ProtocolSetup) :
    r.setupMove.next Trace.nil = ((setupAct r.alice r.bob r.withOpk).run Trace.nil).2.val := rfl

/-! ## Anchoring and State Faithfulness -/

/-- Requires session-start moves (`aliceStart`, `bobStart`) to show at least one visible entry and
anchor any logged completion event (`AliceDone`, `BobDone`) in `m.vis tr`. -/
def Move.LogsSessionCompletion (m : Move) (tr : ExecTrace) : Prop :=
  match m with
  | .aliceStart _ _ _ _ _ shown =>
    1 ≤ shown ∧
      ∀ i, eventIdx isAliceDone tr (m.next tr) = some i → ∃ v ∈ m.vis tr, v.anchor = some i
  | .bobStart _ _ _ _ _ _ _ shown =>
    1 ≤ shown ∧
      ∀ i, eventIdx isBobDone tr (m.next tr) = some i → ∃ v ∈ m.vis tr, v.anchor = some i
  | _ => True

def MovesAnchored : List Move → ExecTrace → Prop
  | [], _ => True
  | m :: ms, tr => m.LogsSessionCompletion tr ∧ MovesAnchored ms (m.next tr)

/-- Checks that every `exposeKey` and `exposeSpqr` move in `ms` reads from a current snapshot. -/
def compromisesCurrentFrom : ExecTrace → List Move → Bool
  | _, [] => true
  | tr, m :: ms =>
    (match m with
      | .exposeKey _ stateIdx _ | .exposeSpqr _ stateIdx =>
        TripleRatchet.isCurrentSnapshot tr stateIdx
      | _ => true) &&
    compromisesCurrentFrom (m.next tr) ms

/-- Checks that every `encrypt` move in `ms` reads its SPQR salt at the handle of the SPQR key it
publishes (`tr.length + 2`). -/
def ownSaltsFrom : ExecTrace → List Move → Bool
  | _, [] => true
  | tr, m :: ms =>
    (match m with
      | .encrypt _ _ _ pqIdx _ => pqIdx == tr.length + 2
      | _ => true) &&
    ownSaltsFrom (m.next tr) ms

def Move.MatchesSetupPeer (r : ProtocolSetup) : Move → Prop
  | .aliceStart _ b .. => b = r.bob
  | .bobStart _ a .. => a = r.alice
  | _ => True

/-- Every session-start move in `ms` names the peer provisioned in `r`. -/
def PeerFaithful (r : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ m ∈ ms, m.MatchesSetupPeer r

/-- Returns `(me, stateIdx, stores)` for moves calling `getLocalState me stateIdx`, where `stores`
is `true` iff a successful execution stores a successor state. -/
def Move.stateLoad? : Move → Option (Participant × Nat × Bool)
  | .encrypt me stateIdx .. => some (me, stateIdx, true)
  | .encryptAbort me stateIdx => some (me, stateIdx, false)
  | .encryptFail me stateIdx _ => some (me, stateIdx, false)
  | .decrypt me stateIdx .. => some (me, stateIdx, true)
  | .decryptSkipped me stateIdx .. => some (me, stateIdx, true)
  | _ => none

/-- Linear session-state usage: once a move loads the state at index `k` and succeeds, no subsequent
move loads `k`. -/
def StateFaithful (r : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ (i j : Nat) (mi mj : Move) (p : Participant) (k : Nat) (b : Bool), i < j →
    ms[i]? = some mi → ms[j]? = some mj →
    mi.stateLoad? = some (p, k, true) →
    (mi.act.run (runTraceMoves r (ms.take i))).1.isSome = true →
    mj.stateLoad? = some (p, k, b) → False

/-- Well-formedness of a move run `ms` from setup `r`: reachable prefixes, anchored session starts,
current-snapshot exposures, own-key encrypt salts, peer faithfulness, and linear state usage. -/
def ModelRun (r : ProtocolSetup) (ms : List Move) : Prop :=
  (setupRandoms r).length = (if r.withOpk then 7 else 6) ∧
  (∀ m ∈ ms, m.isSetup = false) ∧
  ((runTraceMoves r ms).Reachable reachability ∧ MovesAnchored ms (setupTrace r) ∧
    ∀ k, (runTraceMoves r (ms.take k)).Reachable reachability) ∧
  compromisesCurrentFrom (setupTrace r) ms = true ∧ ownSaltsFrom (setupTrace r) ms = true ∧
  PeerFaithful r ms ∧ StateFaithful r ms

end DY.Libsignal.Composed.Refinement
