/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.SpqrSemDef
public import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Skipped-Install Byte-Freshness and Non-Low-Order Ratchet-Key Predicates

Defines `TRStateStoredAt`, `RecvRkLensAll`, `SkippedInstallByteFresh`, `RecvRkNotLowP`, and
`RecvRkNotLowAll` on composed protocol runs.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain recvChainFor)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.RecvHistStep2 (StEntry)

abbrev TRStateStoredAt (p : Participant) (st : TRState) (idx : Nat) (tr : ExecTrace) : Prop :=
  (tr.at? idx : Option StEntry) = some ⟨⟨p, st⟩⟩

theorem mem_availableStates_of_trStateStoredAt (r₀ : ProtocolSetup) (ms : List Move)
    {p : Participant} {st : TRState} {idx : Nat}
    (h : TRStateStoredAt p st idx (runTraceMoves r₀ ms)) :
    st ∈ availableStates r₀ (runTraceMoves r₀ ms) :=
  RecvHistStep2.mem_availableStates_of_at? r₀ ms h

def RecvRkLensAll (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms), ∀ c ∈ st.recv,
    (gamma interpretation S g c.ratchetKey).length = 32

/-- At the source state `st₀` of any `SkippedKeyStored` event taking the fresh-chain branch
(`recvChainFor st₀.toDRState pk = some (c₀, true)`), no existing chain `c ∈ st₀.recv` has the same
concretized ratchet-key bytes as `pk`. -/
def SkippedInstallByteFresh (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ (s : SessionInfo) (pk : DY.Bytes) (n : UInt32) (seed : DY.Bytes) (rIdx src i : Nat)
    (p₀ : Participant) (st₀ : TRState) (c₀ : RecvChain),
    (runTraceMoves r₀ ms).EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) i →
    TRStateStoredAt p₀ st₀ src (runTraceMoves r₀ ms) →
    recvChainFor st₀.toDRState pk = some (c₀, true) →
    ∀ c ∈ st₀.recv, gamma interpretation S g c.ratchetKey ≠ gamma interpretation S g pk

/-- Every receiver chain of `st` has a non-low-order concretized ratchet key. -/
def RecvRkNotLowP (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (st : TRState) : Prop :=
  ∀ c ∈ st.recv,
    DY.X25519.isLowOrderKey ((gamma interpretation S g c.ratchetKey).map BitVec.toNat) = false

theorem recvDetermined_recvRkNotLowP (interpretation : ExternInterpretation) (S : SpqrSem)
    (g : Ghost) : RecvHistStep2.RecvDetermined (RecvRkNotLowP interpretation S g) := by
  intro st st' heq h c hc
  rw [heq] at hc
  exact h c hc

/-- Every receiver chain of every available `TRState` has a non-low-order concretized ratchet key. -/
def RecvRkNotLowAll (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (r₀ : ProtocolSetup) (ms : List Move) : Prop :=
  ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms), ∀ c ∈ st.recv,
    DY.X25519.isLowOrderKey ((gamma interpretation S g c.ratchetKey).map BitVec.toNat) = false

end Symbolic.Swarm.CREF.TR
