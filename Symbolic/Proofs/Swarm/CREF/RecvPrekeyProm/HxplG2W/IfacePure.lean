/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2AdapterPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PkDispatchAtPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetWAtHelpersPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Branch Interfaces and Run-Level Context for Session Promotion

Defines the branch-trichotomy proposition `PromDecSelCases`, the skipped-key public-key dispatch
relation `SkippedPkDispatchAtK`, and the clean-prefix run-level context `PromRawCtx` with its
supply predicate `PromRawCtxSupply`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (computeMac messageVersion TRState TREvent TRSignalMsg
  parseTrSignalMsg trMsgKeys)
open DY.Libsignal.Refinement (aesCbcDecryptSymbol)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt

def PromDecSelCases (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt →
    PromDecSelSkipped sess pf.inner mid coins ∨ PromDecSelNoRatchet sess pf.inner mid coins ∨
      PromDecSelRatchetDH sess pf.inner mid coins

/-- Skipped-key public-key dispatch relation over `RecvCollision` and `ReselectCollision`. -/
def SkippedPkDispatchAtK
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms₁ : List Move) (_τ₁ : List MachineEvent) : Prop :=
  ∀ (p : Participant) (stateIdx₀ : Nat) (body ptBytes : HwBytes) (m : SignalMessage) (st₀ st_prov : TRState)
    (t₀ pk seed k_own : DY.Bytes) (msg₀ : TRSignalMsg) (rIdx srcIdx skIdx : Nat),
    SignalMessage.tryFrom protoSignalCodec body = .ok m →
    t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body →
    parseTrSignalMsg t₀ = some msg₀ →
    msg₀.version = messageVersion →
    msg₀.counter = UInt32.ofBitVec m.counter →
    ¬RecvCollision interpretation r₀ S g ms₁ t₀ →
    ¬ReselectCollision interpretation r₀ S g ms₁ t₀ →
    ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀ →
    st_prov ∈ availableStates r₀ (runTraceMoves r₀ ms₁) →
    (st_prov.peerIk = st₀.peerIk ∧ st_prov.myIk = st₀.myIk) →
    (∀ (msg : TRSignalMsg), msg.version = messageVersion → msg.ratchetKey = pk → msg.counter = msg₀.counter →
      recvSeed st_prov msg = some seed) →
    k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st_prov msg₀ →
    k_own = ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack →
    (runTraceMoves r₀ ms₁).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx →
    TR.G1.RecvHistInvTR interpretation S g r₀ ms₁ →
    TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) →
    (TR.G1.JunkTR pk → ∀ x, pk.view? DY.X25519.Variant.SubF = some x → seed.AttackerKnows (runTraceMoves r₀ ms₁)) →
    gamma interpretation S g pk = m.senderRatchetKey.bytes.toList →
    body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire) →
    st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) →
    st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁) →
    interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some ptBytes →
    ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg),
      t₁ ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ parseTrSignalMsg t₁ = some msg₁ ∧
      msg₁.version = messageVersion ∧ msg₁.ratchetKey = pk ∧ msg₁.counter = msg₀.counter ∧
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) ∧
      (seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨ ∃ salt ∈ honestSalts r₀ ms₁,
        AuthenticDecryptRepB3AtSt interpretation r₀ S g ms₁ body ptBytes t₁ msg₁ st_prov salt seed ∧
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) =
          gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) ∧
        interpretation aesCbcDecryptSymbol
          [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
           (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some ptBytes)

/-- Run-level context facts supplied at a clean explanation `(g, ms)` of `acc` for the session-promotion
decrypt branches. -/
structure PromRawCtx (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (acc : List MachineEvent) : Prop where
  atF : TR.RecvDecStepAt.RecvAtFacts interpretation r S g ms
  pkNR : TR.RecvDecStepAt.NoRatchetPkDispatchAt interpretation r S g ms acc
  pkSk : SkippedPkDispatchAtK interpretation r S g ms acc
  abs' : TR.G1.G1cAttackerBuiltSeedExcl' interpretation r S g ms

def PromRawCtxSupply (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (j : Nat) (e' : PromTurn) (mid acc : List MachineEvent)
    (rec b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (sess sess' : Session (List (BitVec 8)))
    (coins : BitVec 256) (expected : Option (List (BitVec 8))) (pt : List (BitVec 8)),
    PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt →
    ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt) →
    ∀ g ms, CleanBy interpretation r S who ok g ms acc → PromRawCtx interpretation r S g ms acc

end Symbolic.Swarm.CREF.CliPure
