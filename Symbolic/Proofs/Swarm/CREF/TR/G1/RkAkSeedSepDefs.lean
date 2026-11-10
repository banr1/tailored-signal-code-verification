/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkAkSeedSepBase
public import Symbolic.Proofs.Swarm.CREF.TR.G1.RkSpine
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Shared Definitions for Relaxed Seed Separation

Defines honest receive-chain roots (`RecvRoot`), intermediate root-key nodes (`RkInter`), twin
chain roots (`RootX`), and the link and shape-twin statement interfaces (`RecvLinkStored`,
`RecvLinkSkipped`, `AliceBobTwin`, `RkTwinStmt`, `RkTwinStoredStmt`, `RootTwinStmt`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse DY.DiffieHellman DY.Libsignal.TripleRatchet Symbolic.Swarm.CREF.TR
open DY.Libsignal.TripleRatchet (createChain chainKeyAt kdfCk)
open DY.Libsignal.PQXDH (HandshakeKeys)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.COMPOSED.CompTrace Symbolic.Swarm.COMPOSED

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

/-- Honest receive-chain roots for peer ratchet key `pk`:
(a) a stored state `st₀` receiving `pk` (`dhRatchetStep` / `recvChainFor`);
(b) Bob's first receive chain in `bobStart` (signed-prekey secret);
(c) Alice's initial PQXDH receive chain. -/
def RecvRoot (T : ExecTrace) (pk R : DY.Bytes) : Prop :=
  (∃ (p : Participant) (st₀ : TRState) (i₀ : Nat), TRStateStoredAt p st₀ i₀ T ∧
    R = (createChain st₀.rk pk st₀.dhs).2) ∨
  (∃ (keys : HandshakeKeys) (t : Nat) (b : Participant) (idx : Nat), BobDoneKeys T keys ∧
    CompTrace.PQXDHStoredAt T b { kind := .signedPrekey, sk := randTerm t 32 } idx ∧
    R = (createChain keys.rk pk (randTerm t 32)).2) ∨
  (∃ keys : HandshakeKeys, AliceDoneKeys T keys ∧ R = keys.ck)

/-- Every receive chain of a stored state descends via `chainKeyAt` from an honest `RecvRoot`. -/
def RecvLinkStored (T : ExecTrace) : Prop :=
  ∀ {p : Participant} {st : TRState} {i₀ : Nat}, TRStateStoredAt p st i₀ T →
    ∀ c ∈ st.recv, ∃ (R : DY.Bytes) (j : Nat), c.chainKey = chainKeyAt R j ∧ RecvRoot T c.ratchetKey R

/-- Every logged skipped seed derives from `chainKeyAt` over an honest `RecvRoot`. -/
def RecvLinkSkipped (T : ExecTrace) : Prop :=
  ∀ {k : Nat} {s : DY.Libsignal.TripleRatchet.SessionInfo} {pk : DY.Bytes} {n : UInt32}
    {seed : DY.Bytes} {rIdx src : Nat},
    T.EventLoggedAt (TREvent.SkippedKeyStored s pk n seed rIdx src) k →
    ∃ (pk' R : DY.Bytes) (j : Nat), seed = (kdfCk (chainKeyAt R j)).2 ∧ RecvRoot T pk' R

/-- Honest intermediate root-key nodes with peer key `pk`: a stored state's root key after
receiving `pk` (before drawing a new `dhs`), or Bob's first PQXDH root step. -/
def RkInter (T : ExecTrace) (pk x : DY.Bytes) : Prop :=
  (∃ (p : Participant) (st : TRState) (i₀ : Nat), TRStateStoredAt p st i₀ T ∧
    x = (createChain st.rk pk st.dhs).1) ∨
  (∃ (keys : HandshakeKeys) (t : Nat) (b : Participant) (idx : Nat), BobDoneKeys T keys ∧
    CompTrace.PQXDHStoredAt T b { kind := .signedPrekey, sk := randTerm t 32 } idx ∧
    x = (createChain keys.rk pk (randTerm t 32)).1)

/-- An `AliceDone` key bundle and a `BobDone` key bundle whose root keys have equal `gamma'` shapes
have equal root keys unless `KemSlotAlias` holds. -/
def AliceBobTwin (T : ExecTrace) : Prop :=
  ∀ {k₁ k₂ : HandshakeKeys} {t₁ t₂ : DY.Bytes}, AliceDoneKeys T k₁ → BobDoneKeys T k₂ →
    (∀ e ∈ (gamma' i S g k₁.rk).memo, e ∈ (gamma' i S g t₁).memo) →
    (∀ e ∈ (gamma' i S g k₂.rk).memo, e ∈ (gamma' i S g t₂).memo) →
    (gamma' i S g k₁.rk).shape = (gamma' i S g k₂.rk).shape →
    k₁.rk = k₂.rk

/-- Shape-twin property between a stored root key and an intermediate root-key node `RkInter`. -/
def RkTwinStmt (T : ExecTrace) : Prop :=
  ∀ {p₁ : Participant} {st₁ : TRState} {i₁ : Nat} {pk x t₁ t₂ : DY.Bytes},
    TRStateStoredAt p₁ st₁ i₁ T → RkInter T pk x →
    (∀ e ∈ (gamma' i S g st₁.rk).memo, e ∈ (gamma' i S g t₁).memo) →
    (∀ e ∈ (gamma' i S g x).memo, e ∈ (gamma' i S g t₂).memo) →
    (gamma' i S g st₁.rk).shape = (gamma' i S g x).shape →
    st₁.rk = x

/-- Shape-twin property between two stored root keys. -/
def RkTwinStoredStmt (T : ExecTrace) : Prop :=
  ∀ {p₁ p₂ : Participant} {st₁ st₂ : TRState} {i₁ i₂ : Nat} {t₁ t₂ : DY.Bytes},
    TRStateStoredAt p₁ st₁ i₁ T → TRStateStoredAt p₂ st₂ i₂ T →
    (∀ e ∈ (gamma' i S g st₁.rk).memo, e ∈ (gamma' i S g t₁).memo) →
    (∀ e ∈ (gamma' i S g st₂.rk).memo, e ∈ (gamma' i S g t₂).memo) →
    (gamma' i S g st₁.rk).shape = (gamma' i S g st₂.rk).shape →
    st₁.rk = st₂.rk

/-- Honest chain roots on the twin (`u'`) side: an honest sending-chain root, or Alice's initial
PQXDH chain key. -/
def RootX (T : ExecTrace) (X : DY.Bytes) : Prop :=
  HonestSendRoot T X ∨ ∃ keys : HandshakeKeys, AliceDoneKeys T keys ∧ X = keys.ck

/-- Shape-twin property between an honest chain root `RootX` and a receive-chain root `RecvRoot`. -/
def RootTwinStmt (T : ExecTrace) : Prop :=
  ∀ {X pk R t₁ t₂ : DY.Bytes}, RootX T X → RecvRoot T pk R →
    (∀ e ∈ (gamma' i S g X).memo, e ∈ (gamma' i S g t₁).memo) →
    (∀ e ∈ (gamma' i S g R).memo, e ∈ (gamma' i S g t₂).memo) →
    (gamma' i S g X).shape = (gamma' i S g R).shape →
    X = R

end Symbolic.Swarm.CREF.TR.G1.Spine
