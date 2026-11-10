/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core

/-!
# SPQR V1: shared `pq_ratchet.proto` message structures

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `ChainParams.default`, `ChainParams.intoPbTest` and the `Inhabited ChainParams` instance
built from `default`, which are checked by Lean (see `Computational/docs/TRUSTED_BASE.md`).

Defines the `pq_ratchet.proto` structures shared across `Chain.lean`, `Auth.lean`, and `Proto.lean`:
symmetric-chain parameters (`ChainParams`, `DEFAULT_CHAIN_PARAMS`, `ChainParamsPB`, `intoPb`,
`maxJumpOrDefault`, `maxOooKeysOrDefault`, `trimSize`), serialized chain epochs (`EpochDirectionPB`,
`ChainEpochPB`, `ChainPB`), version negotiation (`VersionNegotiationPB`), and authenticator state
(`ProtoAuthenticator`). Kept free of `CryptoGames` imports so `Proto.lean` stays within the
symbolic statement dependency boundary.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

/-! ## `ChainParams` and `pqrpb::ChainParams` (`src/chain.rs:17–89`) -/

/-- Protobuf symmetric-chain parameters (`pqrpb::ChainParams`, where `0` encodes the default). -/
structure ChainParamsPB where
  maxJump : BitVec 32 := 0#32
  maxOooKeys : BitVec 32 := 0#32
  deriving DecidableEq, Repr, Inhabited

/-- Symmetric-chain limits (`src/chain.rs:17–26`): maximum forward counter jump `maxJump` and
maximum retained out-of-order message keys `maxOooKeys`. -/
structure ChainParams where
  maxJump : BitVec 32 := 25000#32
  maxOooKeys : BitVec 32 := 2000#32
  deriving DecidableEq, Repr

/-- Default symmetric-chain parameters (`maxJump = 25000`, `maxOooKeys = 2000`). -/
def DEFAULT_CHAIN_PARAMS : ChainParams :=
  { maxJump := 25000#32, maxOooKeys := 2000#32 }

namespace ChainParams

def default : ChainParams := DEFAULT_CHAIN_PARAMS

/-- Converts `ChainParams` to `ChainParamsPB`, mapping default field values to `0`. -/
def intoPb (self : ChainParams) : ChainParamsPB :=
  { maxJump :=
      if self.maxJump == DEFAULT_CHAIN_PARAMS.maxJump then 0#32 else self.maxJump
    maxOooKeys :=
      if self.maxOooKeys == DEFAULT_CHAIN_PARAMS.maxOooKeys then 0#32 else self.maxOooKeys }

def intoPbTest (self : ChainParams) : ChainParamsPB :=
  self.intoPb

end ChainParams

namespace ChainParamsPB

def maxJumpOrDefault (self : ChainParamsPB) : BitVec 32 :=
  if self.maxJump > 0#32 then self.maxJump else DEFAULT_CHAIN_PARAMS.maxJump

def maxOooKeysOrDefault (self : ChainParamsPB) : BitVec 32 :=
  if self.maxOooKeys > 0#32 then self.maxOooKeys else DEFAULT_CHAIN_PARAMS.maxOooKeys

/-- Out-of-order key history threshold `maxOoo * 11 / 10 + 1` (`src/chain.rs:84–88`). -/
def trimSize (self : ChainParamsPB) : Nat :=
  let maxOoo := self.maxOooKeysOrDefault.toNat
  maxOoo * 11 / 10 + 1

end ChainParamsPB

/-- `pqrpb::chain::epoch::EpochDirection` (`src/proto/pq_ratchet.proto:197–201`). -/
structure EpochDirectionPB where
  ctr : BitVec 32 := 0#32
  next : Bytes := []
  prev : Bytes := []
  deriving DecidableEq, Repr, Inhabited

/-- `pqrpb::chain::Epoch` (`src/proto/pq_ratchet.proto:196–204`). -/
structure ChainEpochPB where
  send : Option EpochDirectionPB := none
  recv : Option EpochDirectionPB := none
  deriving DecidableEq, Repr, Inhabited

/-- `pqrpb::Chain` (`src/proto/pq_ratchet.proto:195–211`). -/
structure ChainPB where
  direction : BitVec 32 := 0#32
  currentEpoch : Epoch := 0#64
  links : List ChainEpochPB := []
  nextRoot : Bytes := []
  sendEpoch : Epoch := 0#64
  params : Option ChainParamsPB := none
  deriving DecidableEq, Repr, Inhabited

/-- `pqrpb::pq_ratchet_state::VersionNegotiation` (`src/proto/pq_ratchet.proto:26–31`). -/
structure VersionNegotiationPB where
  authKey : Bytes := []
  direction : BitVec 32 := 0#32
  minVersion : BitVec 32 := 0#32
  chainParams : Option ChainParamsPB := none
  deriving DecidableEq, Repr, Inhabited


/-- `pqrpb::Authenticator` (`src/proto/pq_ratchet.proto:61–64`). -/
structure ProtoAuthenticator where
  rootKey : Bytes
  macKey : Bytes
  deriving DecidableEq, Repr, Inhabited

end CryptoVerification.LibsignalSpqrV1
