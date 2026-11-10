/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces

/-!
# Move-Based Trace Explanation and Collision Predicates

Defines hardware-event to visible-entry matching (`EventMatchesEntry`), term representations of
wire messages (`recvRepresentations`, `preKeyRepresentations`), faithfulness conditions
(`MatchedPrefix`, `ExplainsMoves`), and move-based collision predicates.
-/

@[expose] public section

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Rust
open CryptoVerification.LibsignalProtoCodec (WireType decodeKey mergeBytes mergeUint32 skipField
  recursionLimit protoSignalCodec)
open DY.Libsignal.Refinement (x25519PublicKeySymbol ExternCryptoLawsHold encodeField)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys pqxdhKdf pqxdhIkm agree errToOption serializedIk)
open DY.Libsignal.PQXDH.Refinement (PreKeyProto versionByte msgPreamble? wirePrekeyTag preKeyBundleByteLength kyberEncapsSymbol kyberDecapsSymbol)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open TripleRatchet (messageVersion recvChainFor consumeMessageKey skippedSeeds
  computeMac RecvChain createChain TRState TRSignalMsg parseTrSignalMsg trMsgKeys)

/-! ## Event Matching -/

/-- Matches a hardware `MachineEvent` against a model `VisEntry` by event kind and layout:

| layout | bytes |
|---|---|
| `single` | `gamma` of the single term |
| `whisper` | `0x02 :: gamma t` |
| `bundle` | `PreKeyBundleLayoutMatches` |
| `preKeySend` / `preKeyRecv` | `SendMatches` / `PreKeyRecvOpkMatches` |
| `preKeyInner eks` | pre-key message with inner `gamma t` and base key `ecKey (gamma ek)` for some `ek ∈ eks` |
| `fresh n` | any `n` bytes |
| `kyberCoin j` | 4 bytes starting with byte `j` of a 32-byte `gamma t` |
| `unconstrained` | unrestricted |
| `leakPq pq` | `r.kyberSecB` if `pq`, else `gamma` of the single term |
| `leakRecord` | `gamma t` or `clamp (gamma t)` |
-/
def EventMatchesEntry (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (e : MachineEvent) (v : VisEntry) : Prop :=
  eventKind e = v.kind ∧
    let b := eventBytes e
    let γ := gamma interpretation S g
    match v.layout with
    | .single => v.terms.map γ = [b]
    | .whisper => ∃ t, v.terms = [t] ∧ b = wireWhisperTag :: γ t
    | .bundle => PreKeyBundleLayoutMatches interpretation S g b v.terms
    | .preKeySend => ∃ ids, SendMatches interpretation r S g (some ids) b v.terms
    | .preKeyRecv => PreKeyRecvOpkMatches interpretation r S g b v.terms
    | .preKeyInner eks =>
      ∃ t p, v.terms = [t] ∧ parsePreKeyWire b = some p ∧
        (∃ ek ∈ eks, p.baseKey.take 33 = ecKey (γ ek)) ∧ p.message = γ t
    | .fresh n => b.length = n
    | .kyberCoin j =>
      b.length = 4 ∧ ∃ t, v.terms = [t] ∧ (γ t).length = 32 ∧ b.head? = (γ t)[j]?
    | .unconstrained => True
    | .leakPq pq => if pq then b = r.kyberSecB else v.terms.map γ = [b]
    | .leakRecord =>
      ∃ t, v.terms = [t] ∧ (b = γ t ∨ b = clamp (γ t))

/-! ## Representations and Faithfulness -/

/-- Attacker-known terms on `runTraceMoves r ms` that concretize to `b`, parse as a `TRSignalMsg`
with non-SPQR-headed MAC, and align field-for-field with `SignalMessage.tryFrom` on `b`. -/
def recvRepresentations (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (b : HwBytes) : Set DY.Bytes :=
  {t | t.AttackerKnows (runTraceMoves r ms) ∧ gamma interpretation S g t = b ∧
    (parseTrSignalMsg t).isSome = true ∧
    ∀ msg, parseTrSignalMsg t = some msg →
      gamma interpretation S g msg.wire = b.take (b.length - 8) ∧
      gamma interpretation S g msg.mac = b.drop (b.length - 8) ∧
      spqrHeaded msg.mac = false ∧
      ∀ m : CryptoGames.LibsignalSession.SignalMessage,
        CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec b = .ok m →
        gamma interpretation S g msg.ciphertext = m.ciphertext ∧
        gamma interpretation S g msg.ratchetKey = m.senderRatchetKey.bytes.toList ∧
        gamma interpretation S g msg.pqRatchet = m.pqRatchet ∧
        msg.counter.toNat = m.counter.toNat ∧ msg.version.toNat = m.messageVersion.toNat}

/-- Attacker-known `PreKeyRep` triples `(ek, ct, msg)` matching a received pre-key wire message `b`
with `FaithfulInner` on the parsed inner message. -/
def preKeyRepresentations (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (b : HwBytes) : Set PreKeyRep :=
  {x | x.ek.AttackerKnows (runTraceMoves r ms) ∧ x.ct.AttackerKnows (runTraceMoves r ms) ∧
    x.msg.AttackerKnows (runTraceMoves r ms) ∧
    PreKeyRecvMatches interpretation r S g b [x.ek, x.ct, x.msg] ∧
    ∃ p, parsePreKeyWire b = some p ∧ FaithfulInner interpretation S g x.msg p}

/-- Participant whose call a move explains (`some p` for session starts, encrypts, and decrypts;
`none` for `reject` and environment moves). -/
def Move.party? : Move → Option Participant
  | .aliceStart a .. => some a
  | .bobStart b .. => some b
  | .encrypt me .. => some me
  | .encryptAbort me _ => some me
  | .encryptFail me .. => some me
  | .decrypt me .. => some me
  | .decryptSkipped me .. => some me
  | _ => none

/-- Number of harness calls started in `vs` (one `recv` or `pt` entry per call). -/
def callCount (vs : List VisEntry) : Nat :=
  (vs.filter fun v => v.kind == .recv || v.kind == .pt).length

/-- Every move in `ms` with a participant matches the caller schedule `who` at its `callCount`
index. -/
def RoleFaithful (r : ProtocolSetup) (who : List Participant) (ms : List Move) : Prop :=
  ∀ (i : Nat) (m : Move) (p : Participant), ms[i]? = some m → m.party? = some p →
    who[callCount (runVis r (ms.take i))]? = some p

/-- Hardware events starting harness calls in `τ₁` (`recv` and `pt` events). -/
def callStarts (τ₁ : List MachineEvent) : List MachineEvent :=
  τ₁.filter fun e => eventKind e == .recv || eventKind e == .pt

/-- Pre-key receive path of a move: `some true` for wrapped existing-session decrypts, `some false`
for `bobStart`, and `none` otherwise. -/
def Move.prekeyPath? : Move → Option Bool
  | .decrypt _ _ _ _ _ w => if w then some true else none
  | .decryptSkipped _ _ _ _ _ _ w => if w then some true else none
  | .bobStart .. => some false
  | _ => none

/-- Pre-key path faithfulness: a pre-key receive move takes the existing-session path iff the wire
base key matches an earlier `BobDone` base key in the prefix. -/
def PathFaithful (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (τ₁ : List MachineEvent) : Prop :=
  ∀ (i : Nat) (m : Move) (promote : Bool) (b : HwBytes) (p : PreKeyFields),
    ms[i]? = some m → m.prekeyPath? = some promote →
    (callStarts τ₁)[callCount (runVis r (ms.take i))]? = some (.recv b) →
    parsePreKeyWire b = some p →
    (promote = true ↔ ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r (ms.take i)),
      ecKey (gamma interpretation S g ek) = p.baseKey.take 33)

/-- Every received term read at a `recv` entry of `runVis r ms` belongs to `recvRepresentations`
or `preKeyRepresentations` of the corresponding wire bytes in `τ₁`. -/
def ReadFaithful (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (τ₁ : List MachineEvent) : Prop :=
  ∀ ev ∈ τ₁.zip (runVis r ms), ev.2.kind = .recv →
    match ev.2.layout, ev.2.terms, eventBytes ev.1 with
    | .whisper, [t], _ :: body => t ∈ recvRepresentations interpretation r S g ms body
    | .preKeyInner _, [t], b =>
      ∀ p, parsePreKeyWire b = some p → t ∈ recvRepresentations interpretation r S g ms p.message
    | .preKeyRecv, ek :: ct :: msg :: _, b =>
      ⟨ek, ct, msg⟩ ∈ preKeyRepresentations interpretation r S g ms b
    | _, _, _ => True

/-- Prefix explanation of hardware trace `τ` by model run `ms` under `S`, caller schedule `who`,
and ghost `g`. -/
def MatchedPrefix (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (g : Ghost) (ms : List Move) (τ : List MachineEvent) : Prop :=
  GhostAndSemMatchSetup interpretation r S g ∧ ModelRun r ms ∧
    RoleFaithful r who ms ∧ PathFaithful interpretation r S g ms τ ∧
    ReadFaithful interpretation r S g ms τ ∧
    List.Forall₂ (EventMatchesEntry interpretation r S g) τ (runVis r ms)

/-- Agreement of `ms` with outcome schedule `ok`: `reject` moves have `ok k = false` and moves
logging `AliceDone` have `ok k = true`. -/
def OutcomeFaithful (r : ProtocolSetup) (ok : Nat → Bool) (ms : List Move) : Prop :=
  ∀ (i : Nat) (m : Move), ms[i]? = some m →
    let k := callCount (runVis r (ms.take i))
    (∀ ds, m = .reject ds → ok k = false) ∧
    ((eventIdx isAliceDone (runTraceMoves r (ms.take i)) (m.next (runTraceMoves r (ms.take i)))).isSome →
      ok k = true)

/-- Prefix explanation combining `MatchedPrefix` and `OutcomeFaithful`. -/
def ExplainsMoves (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (τ₁ : List MachineEvent) : Prop :=
  MatchedPrefix interpretation r S who g ms τ₁ ∧ OutcomeFaithful r ok ms

/-! ## Collisions and Receiver Trials -/

/-- SPQR keys published by `encrypt` moves in `ms` starting from `tr`. -/
def honestKeysFrom : ExecTrace → List Move → List DY.Bytes
  | _, [] => []
  | tr, m :: ms =>
    (match m with
      | .encrypt .. => ((m.next tr).getMessageSentAt (tr.length + 2)).toList
      | _ => []) ++ honestKeysFrom (m.next tr) ms

/-- Candidate SPQR salts for receiver MAC trials after `ms`: `zeroKey` together with `honestKeysFrom`. -/
def honestSalts (r : ProtocolSetup) (ms : List Move) : List DY.Bytes :=
  DY.Spqr.zeroKey :: honestKeysFrom (setupTrace r) ms

/-- Receive collision on term `t` after `ms`: either `MemoCollisionOn` across `t` and expanded
`whisperTrials`, or `MacTagForgeryOrCollision` across `whisperTrials`. -/
def RecvCollision (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (t : DY.Bytes) : Prop :=
  let tr := runTraceMoves r ms
  let known := fun u : DY.Bytes => u.AttackerKnows tr
  let salts := honestSalts r ms
  match parseTrSignalMsg t with
  | none => MemoCollisionOn interpretation r S g known tr (runVis r ms) [t] []
  | some msg =>
    let ctxs := whisperTrials interpretation r S g tr msg
    MemoCollisionOn interpretation r S g known tr (runVis r ms)
        (t :: ctxs.flatMap (trialTerms salts msg)) [] ∨
      MacTagForgeryOrCollision interpretation S g known salts msg ctxs

/-- Ratchet-key reselection collision: `msg.ratchetKey` shares concretized bytes with a distinct
stored ratchet key `rk`, some representation reselects to `rk`, and every reselecting representation
triggers `RecvCollision`. -/
def ReselectCollision (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (t : DY.Bytes) : Prop :=
  let tr := runTraceMoves r ms
  let γ := gamma interpretation S g
  ∃ msg, parseTrSignalMsg t = some msg ∧
    ∃ rk ∈ storedRatchetKeys r tr msg, γ rk = γ msg.ratchetKey ∧ rk ≠ msg.ratchetKey ∧
      (∃ t' ∈ recvRepresentations interpretation r S g ms (γ t),
        ∃ msg', parseTrSignalMsg t' = some msg' ∧ ReselectsTo msg msg' rk) ∧
      ∀ t' ∈ recvRepresentations interpretation r S g ms (γ t),
        ∀ msg', parseTrSignalMsg t' = some msg' → ReselectsTo msg msg' rk →
          RecvCollision interpretation r S g ms t'

/-- Network message index read by `decrypt` or `decryptSkipped`, and `none` for all other moves. -/
def Move.decryptMsgIdx? : Move → Option Nat
  | .decrypt _ _ msgIdx .. => some msgIdx
  | .decryptSkipped _ _ msgIdx .. => some msgIdx
  | _ => none

/-- Existence of attacker sends `ext` of known terms and a decrypt move `m` reading `t` that
extends `(g, ms)` to an explanation of `τ₁ ++ e :: τ₂.take (k + 1)` ending in `.accept pt`. -/
def ModelAcceptsTermAfterCoinSplit (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (τ₁ : List MachineEvent) (e : MachineEvent) (τ₂ : List MachineEvent)
    (t : DY.Bytes) : Prop :=
  ∃ (ext : List DY.Bytes) (m : Move) (msgIdx k : Nat) (pt : HwBytes) (g₁ : Ghost),
    (∀ x ∈ ext, x.AttackerKnows (runTraceMoves r ms)) ∧
    m.decryptMsgIdx? = some msgIdx ∧
    g₁.addr = g.addr ∧ (∀ i, i < (runTraceMoves r ms).length → g₁.σ i = g.σ i) ∧
    (runTraceMoves r (ms ++ ext.map .attackerSend)).getMessageSentAt msgIdx = some t ∧
    τ₂[k]? = some (.accept pt) ∧
    (τ₂.take k).all (fun ev => eventKind ev == .rng) = true ∧
    ExplainsMoves interpretation r S who ok g₁ (ms ++ ext.map .attackerSend ++ [m])
      (τ₁ ++ e :: τ₂.take (k + 1))

/-- Extracts the inner `SignalMessage` byte slice `b` from a whisper or pre-key `.recv` event `e`. -/
def RecvMsgBody (e : MachineEvent) (b : HwBytes) : Prop :=
  match e with
  | .recv (tag :: body) =>
      (tag = wireWhisperTag ∧ b = body) ∨
        ∃ p, parsePreKeyWire (tag :: body) = some p ∧ b = p.message
  | _ => False

/-- Holds when `m` is a `decrypt` or `decryptSkipped` reading a `RecvCollision` term at `pre`. -/
def MoveReadsCollidingMsg (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pre : List Move) (e : MachineEvent) : Move → Prop
  | .decrypt _ _ msgIdx .. =>
      ∃ (b : HwBytes) (t : DY.Bytes), RecvMsgBody e b ∧
        (runTraceMoves r pre).getMessageSentAt msgIdx = some t ∧
        RecvCollision interpretation r S g pre t
  | .decryptSkipped _ _ msgIdx .. =>
      ∃ (b : HwBytes) (t : DY.Bytes), RecvMsgBody e b ∧
        (runTraceMoves r pre).getMessageSentAt msgIdx = some t ∧
        RecvCollision interpretation r S g pre t
  | _ => False

/-- Holds when some earlier accepted receive event in `τ` is explained by a move reading a colliding
term (`MoveReadsCollidingMsg`). -/
def ReadCollision (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (τ : List MachineEvent) : Prop :=
  ∃ (i : Nat) (τ₁ : List MachineEvent) (e : MachineEvent) (τ₂ : List MachineEvent) (m : Move),
    τ = τ₁ ++ e :: τ₂ ∧ ms[i]? = some m ∧
    List.Forall₂ (EventMatchesEntry interpretation r S g) τ₁ (runVis r (ms.take i)) ∧
    (∃ pt, (τ₂.filter fun e => eventKind e != .rng).head? = some (.accept pt)) ∧
    MoveReadsCollidingMsg interpretation r S g (ms.take i) e m

/-- Collision or MAC-forgery excuse for Bob's session start on representation `x` after `ms`. -/
def BobSessionStartCollidesOrImplicitRejects (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (p : PreKeyFields) (x : PreKeyRep) : Prop :=
  let tr := runTraceMoves r ms
  let known := fun u : DY.Bytes => u.AttackerKnows tr
  let salts := honestSalts r ms
  match parseTrSignalMsg x.msg with
  | none => MemoCollisionOn interpretation r S g known tr (runVis r ms) [x.ek, x.ct, x.msg] []
  | some msg =>
    let ctxs := bobTrials r tr p x msg
    MemoCollisionOn interpretation r S g known tr (runVis r ms)
        ([x.ek, x.ct, x.msg] ++ ctxs.flatMap (trialTerms salts msg)) [] ∨
      MacTagForgeryOrCollision interpretation S g known salts msg ctxs

/-- Visible `.pt` entry of the next `encrypt` move after `ms`. -/
def ptEntryOfNextEncrypt (r : ProtocolSetup) (ms : List Move) : VisEntry :=
  ⟨.pt, [randTerm (runTraceMoves r ms).length 32], .single, none⟩

/-- Holds when `p.baseKey` matches the concretized base key of an earlier `BobDone` event in `ms`. -/
def KnownBaseKey (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (p : PreKeyFields) : Prop :=
  ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms), p.baseKey.take 33 = ecKey (gamma interpretation S g ek)

end DY.Libsignal.Composed.Refinement
