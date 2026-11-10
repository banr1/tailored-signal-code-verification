/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
public import LibsignalBinary.Proofs.E2E.Record.Support.Phi

/-!
# Scope predicates, `HonestEnv`, and reachable-session invariant `Inv`

Defines the `SessionRecord` scope predicates (`RecordInScope`, `RecordPqEmpty`, `RecordRepr`,
`InScope`), the binary execution environment `HonestEnv`, and the reachable-session invariant `Inv`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
export CryptoVerification.LibsignalPublicApiRepr (AddrVal serializeAddrVals OptU32Rel PendingRel
  KyberRel sessionStateReprAt RecordGhost sessionRecordAt)

/-! ## Scope predicates (`RecordInScope`, `RecordPqEmpty`, `RecordRepr`, `InScope`) -/

/-- Public-API scope constraints on the current session of `r` (distinct identities, 32-byte seeds, clamped sender scalar, bounded counters). -/
def RecordInScope (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s →
    s.state.remoteIdentity ≠ some s.state.localIdentity ∧ SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 32

/-- Every current session in `r` has an empty `pqRatchetState` (SPQR disabled). -/
def RecordPqEmpty (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s → s.state.pqRatchetState = []

/-- Binary layout bounds on `r`: bounded `receiverChains` / `messageKeys` lengths, non-zero registration IDs, and 33-byte `aliceBaseKey`. -/
def RecordRepr (r : SessionRecord Bytes) : Prop :=
  ∀ s, r.currentSession = some s →
    (∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys) ∧
      (∀ sc, s.state.senderChain = some sc →
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) ∧
      s.Wf ∧ s.aliceBaseKey.length < 2 ^ 32

/-- Conjunction of `RecordInScope`, `RecordPqEmpty`, and `RecordRepr`. -/
def InScope (r : SessionRecord Bytes) : Prop := RecordInScope r ∧ RecordPqEmpty r ∧ RecordRepr r

/-! ## `HonestEnv` and reachable-session invariant `Inv` -/

/-- Binary execution environment bundling `Crypto`, `RustAlloc`, party identities, addresses, and `SessionExtras`. -/
structure HonestEnv where
  C : Crypto
  A : RustAlloc
  ctl : BitVec 64
  uuidParse : UuidParser
  img : Obj.Image
  encRecord : SessionRecord Bytes → Bytes
  decRecord : Bytes → Option (SessionRecord Bytes)
  hooks : SessionRecord Bytes → String → Option (State → State)
  idOf : Party → IdentityKey
  addr : Party → AddrVal
  now : SystemTime
  extras : Party → SessionExtras
  retAddr : BitVec 64
  encEntry : SessionRecord Bytes → Party → Bytes → State
  tfEntry : SessionRecord Bytes → Party → Bytes → State
  decEntry : SessionRecord Bytes → Party → State → BitVec 256 → State

namespace HonestEnv

variable (E : HonestEnv)

/-- The session model's parameters for this environment instance. -/
def params : Params Bytes Unit :=
  ⟨E.C, protoSignalCodec, spqrOffB, E.idOf .A, E.idOf .B,
    serializeAddrVals (serviceIdParse uuidTryParse) (E.addr .A) (E.addr .B),
    serializeAddrVals (serviceIdParse uuidTryParse) (E.addr .B) (E.addr .A)⟩

/-- The record an honest store holds for ghost state `g`. -/
def recOf (g : GhostState Bytes) : SessionRecord Bytes := toRecord E.extras g

end HonestEnv

/-- The identity key of a party's own session at the instance's parameters. -/
def ownId (E : HonestEnv) : Party → IdentityKey
  | .A => E.params.idA
  | .B => E.params.idB

/-- Reachable-session invariant at `E.params`: `InScope (E.recOf g)` and matching party identity keys. -/
def Inv (E : HonestEnv) (g : GhostState Bytes) : Prop :=
  InScope (E.recOf g) ∧ g.session.localIdentity = ownId E g.party ∧
    g.session.remoteIdentity = some (ownId E g.party.other)

namespace SeedLengthFacts

theorem pure_true_sepConj {P : SepProp} {φ : Prop} (h : φ) : (⌜φ⌝ ∗ P) = P :=
  pure_sepConj_of_true h P

end SeedLengthFacts

end CryptoVerification.E2E.Record

