/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.Specifications.Security.Binary
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryFixed

/-!
# Overview of Symbolic Forward Secrecy

Definitional checks and clause witnesses for the symbolic forward-secrecy specification
`DY.Libsignal.Composed.Security.ForwardSecrecy` across the composed Dolev–Yao model
(`Symbolic/Specifications/Security/Model.lean`), the CLI refinement boundary
(`AllSecurityQueriesHoldOnHwTrace`), and the ARM64 binary boundary (`SignalSessionSecure`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.ForwardSecrecyTour

open DY
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Cheval

/-!
`ForwardSecrecy` quantifies `FSQuery tr` over every reachable model trace. At the CLI layer,
`AllSecurityQueriesHoldOnHwTrace` instantiates `FSQuery` on `runTrace r ss` with
`HwAttackerKnows r vis` in place of `Bytes.AttackerKnows tr`, and `SignalSessionSecure` lifts that
guarantee to the ARM64 ELF binary.
-/

section Overview

example :
    ForwardSecrecy = (∀ tr : ExecTrace, tr.Reachable reachability → FSQuery tr) :=
  rfl

example (tr : ExecTrace) :
    FSQuery tr = FSQuery tr (fun t => t.AttackerKnows tr) :=
  rfl

example (interp : CryptoProofLib.Refinement.ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (evs : List DY.Libsignal.HwEvents.CliEvent)
    (hAll : AllSecurityQueriesHoldOnHwTrace interp r S evs)
    (g : Ghost) (ss : List Step) (vis : List VisEntry)
    (hExp : Explains interp r S g ss vis evs) :
    FSQuery (runTrace r ss) (HwAttackerKnows r vis) :=
  (hAll g ss vis hExp).1

example : List (BitVec 8) → Prop := SignalSessionSecure

end Overview

/-!
`ExecTrace` is an append-only snoc-list over seven `ExecEntryT` variants: network messages,
fresh random draws, `TREvent` / `PQXDHEvent` / `ComposedEvent` ghost events, and immutable
`TRState` / `PQXDHState` local snapshots. `Trace.Reachable reachability` closes `Trace.nil` under
the 23 transitions of `DY.Libsignal.Composed.reachability` (honest ratchet steps require
`isCurrentSnapshot`, whereas state-exposure transitions also apply to stale snapshots), and
`Bytes.AttackerKnows` is the least fixpoint over `Trace.BaseAttackerKnows` closed under the 13
equational theories in `Symbolic/Specifications/Model/Instance.lean`.
-/

section ReachabilityMechanics

example : (Trace.nil : ExecTrace).Reachable reachability :=
  .Base

example (tr : ExecTrace) (hTr : tr.Reachable reachability)
    (input : reachability.Input) (hPre : reachability.PreCond input tr) :
    (((reachability.step input).snd).run tr).snd.val.Reachable reachability :=
  .Step input hPre hTr

example (b : Bytes) (tr1 tr2 : ExecTrace) (hLe : tr1 ≤ tr2) (hKnow : b.AttackerKnows tr1) :
    b.AttackerKnows tr2 :=
  Bytes.AttackerKnows_le b tr1 tr2 hLe hKnow

end ReachabilityMechanics

/-!
`MessageSeedUsed tr seed pqSalt` projects `TREvent.MessageKey` onto `(seed, pqSalt)`.
`FSQuery tr Knows` asserts that whenever `TRKeyKnown Knows seed pqSalt` holds (`Knows seed` or
`Knows (trMsgKeys pqSalt seed).cipherKey`), at least one of `seed`, a chain key deriving `seed`,
or a root key deriving that chain satisfies `CompromisedKey tr`.
-/

section InlinedPredicates

example (tr : ExecTrace) (seed pqSalt : Bytes) :
    MessageSeedUsed tr seed pqSalt ↔
      (∃ s dir n rIdx parentStateIdx,
        tr.EventLogged (TREvent.MessageKey s dir seed pqSalt n rIdx parentStateIdx)) :=
  Iff.rfl

example (tr : ExecTrace) (Knows : Bytes → Prop) :
    FSQuery tr Knows ↔
      (∀ seed pqSalt,
        MessageSeedUsed tr seed pqSalt →
        (Knows seed ∨ Knows (trMsgKeys pqSalt seed).cipherKey) →
        CompromisedKey tr seed ∨
        (∃ ck, DerivesMsgKey ck seed ∧ CompromisedKey tr ck) ∨
        (∃ rk ck, DerivesChain rk ck ∧ DerivesMsgKey ck seed ∧ CompromisedKey tr rk)) :=
  Iff.rfl

end InlinedPredicates

/-!
`DerivesMsgKey ck seed` iterates symmetric ratcheting (`chainKeyAt` / `kdfCk`), while
`RootDescends` and `DerivesChain` iterate DH-ratchet root updates (`createChain`). Because `kdfCk`
and `createChain` are free symbolic constructors, post-step chain and root keys do not derive
earlier message seeds, giving forward secrecy without explicit trace-index inequalities outside
`HandshakeRootCompromised`. Note that `HandshakeRootCompromised` includes `keys.ck` directly
because `aliceStart` installs `keys.ck` as Alice's initial receiving chain without `createChain`,
and `ExposedSpqr` is absent from `CompromisedKey` because SPQR output keys are published on the
network in the symbolic model.
-/

section GenealogyAndClauses

example (ck : Bytes) :
    DerivesMsgKey ck (kdfCk ck).2 :=
  ⟨0, rfl⟩

example (ck : Bytes) :
    DerivesMsgKey ck (kdfCk (kdfCk ck).1).2 :=
  ⟨1, rfl⟩

example (rk theirPk ourSk : Bytes) :
    DerivesChain rk (createChain rk theirPk ourSk).2 :=
  ⟨rk, theirPk, ourSk, .refl, rfl⟩

example (rk theirPk₁ ourSk₁ theirPk₂ ourSk₂ : Bytes) :
    DerivesChain rk (createChain (createChain rk theirPk₁ ourSk₁).1 theirPk₂ ourSk₂).2 :=
  ⟨(createChain rk theirPk₁ ourSk₁).1, theirPk₂, ourSk₂, .step .refl, rfl⟩

-- Disjunct 1 via `ExposedMK`.
example (tr : ExecTrace) (s : SessionInfo) (seed : Bytes) (n : UInt32) (rIdx : Nat)
    (hExp : tr.EventLogged (TREvent.ExposedMK s seed n rIdx)) :
    CompromisedKey tr seed :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, n, rIdx, hExp⟩

-- Disjunct 2 via `ExposedCKs`.
example (tr : ExecTrace) (s : SessionInfo) (ck : Bytes) (ns : UInt32) (rIdx : Nat)
    (hExp : tr.EventLogged (TREvent.ExposedCKs s ck ns rIdx)) :
    let seed := (kdfCk (chainKeyAt ck ns.toNat)).2
    ∃ ck₀, DerivesMsgKey ck₀ seed ∧ CompromisedKey tr ck₀ :=
  ⟨ck, ⟨ns.toNat, rfl⟩, Or.inr <| Or.inr <| Or.inl ⟨s, ns, rIdx, hExp⟩⟩

-- Disjunct 2 via `HandshakeRootCompromised` on Alice's initial receiving chain `keys.ck`.
example (tr : ExecTrace) (keys : HandshakeKeys) (j : Nat)
    (hKeys : HandshakeKeysAt tr j keys)
    (hAllComp : ∀ keys' j', HandshakeKeysAt tr j' keys' →
      (keys.ck = keys'.rk ∨ keys.ck = keys'.ck) → HandshakeWasCompromisedAt tr j')
    (steps : Nat) :
    let seed := (kdfCk (chainKeyAt keys.ck steps)).2
    ∃ ck, DerivesMsgKey ck seed ∧ CompromisedKey tr ck :=
  ⟨keys.ck, ⟨steps, rfl⟩,
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨⟨keys, j, hKeys, Or.inr rfl⟩, hAllComp⟩⟩

-- Disjunct 3 via `ExposedRK`.
example (tr : ExecTrace) (s : SessionInfo) (rk theirPk ourSk : Bytes) (rIdx steps : Nat)
    (hExp : tr.EventLogged (TREvent.ExposedRK s rk rIdx)) :
    let ck := (createChain rk theirPk ourSk).2
    let seed := (kdfCk (chainKeyAt ck steps)).2
    ∃ rk₀ ck₀, DerivesChain rk₀ ck₀ ∧ DerivesMsgKey ck₀ seed ∧ CompromisedKey tr rk₀ :=
  ⟨rk, (createChain rk theirPk ourSk).2,
    ⟨rk, theirPk, ourSk, .refl, rfl⟩,
    ⟨steps, rfl⟩,
    Or.inl ⟨s, rIdx, hExp⟩⟩

end GenealogyAndClauses

end Symbolic.Tests.ForwardSecrecyTour
