/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptNewRecTieBExclPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Cross-Seed MAC Collision Predicate and Exclusion Hypothesis

Defines `skippedSeedsFor`, the cross-seed MAC collision predicate `A2bCrossSeedMacGuess` between
a cached skipped seed and a receive-chain seed with distinct concretized bytes, and the exclusion
hypothesis `A2bCrossSeedExcl` reducing `A2bCrossSeedMacGuess` to `RecvCollision`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr gamma_concat gamma_dhPk newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo consumeMessageKey computeMac messageVersion)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.Pure

/-- Cached `SkippedKeyStored` seeds on `tr` matching `msg.ratchetKey` and `msg.counter`. -/
def skippedSeedsFor (tr : ExecTrace) (msg : TRSignalMsg) : List DY.Bytes :=
  (List.range tr.length).filterMap fun i =>
    match tr.getEventAt TREvent i with
    | some (.SkippedKeyStored _ pk n seed _ _) =>
      if pk = msg.ratchetKey ∧ n = msg.counter then some seed else none
    | _ => none

/-- Predicate asserting that `t` carries a valid MAC under a cached skipped seed `seed` whose
concretized bytes also match a MAC computed from a distinct receive-chain seed `seed'`. -/
def A2bCrossSeedMacGuess (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (t : DY.Bytes) : Prop :=
  let tr := runTraceMoves r ms
  ∃ msg, parseTrSignalMsg t = some msg ∧ msg.version = messageVersion ∧
    ∃ seed ∈ skippedSeedsFor tr msg, ∃ (salt : DY.Bytes) (st₀ : TRState),
      st₀ ∈ availableStates r tr ∧
      (findRecvChain st₀.toDRState.recv msg.ratchetKey).isSome = true ∧
      msg.mac = computeMac (trMsgKeys salt seed).macKey st₀.peerIk st₀.myIk msg.wire ∧
    ∃ st ∈ availableStates r tr, ∃ c ∈ st.toDRState.recv, ∃ seed' c',
      gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey ∧
      consumeMessageKey c msg.counter = some (seed', c') ∧
      gamma interpretation S g seed' ≠ gamma interpretation S g seed ∧
    ∃ k ∈ ownKeys r tr st msg,
      gamma interpretation S g (computeMac (trMsgKeys k seed').macKey st.peerIk st.myIk msg.wire) =
        gamma interpretation S g msg.mac

/-- Hypothesis stating that every `A2bCrossSeedMacGuess` instance triggers `RecvCollision`. -/
def A2bCrossSeedExcl (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (acc : List MachineEvent) : Prop :=
  ∀ t, A2bCrossSeedMacGuess interpretation r₀ S g ms t → RecvCollision interpretation r₀ S g ms t

theorem a2b_mem_skippedSeedsFor {tr : ExecTrace} {skIdx : Nat} {s : SessionInfo}
    {msg : TRSignalMsg} {seed : DY.Bytes} {rIdx srcIdx : Nat}
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored s msg.ratchetKey msg.counter seed rIdx srcIdx⟩) :
    seed ∈ skippedSeedsFor tr msg := by
  have hlt : skIdx < tr.length := by
    by_contra h
    rw [at?_ge_length tr (Nat.le_of_not_lt h)] at hsk
    cases hsk
  unfold skippedSeedsFor
  refine List.mem_filterMap.mpr ⟨skIdx, List.mem_range.mpr hlt, ?_⟩
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hsk]

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
