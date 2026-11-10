/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPendingPreKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSessionVersion

/-!
# Per-Tag Leaf Theorems for General `SessionStructure::merge_field`

Exports the per-tag `mergeFieldGenSpec` leaf theorems (`1`, `2`–`4`, `5`, `6`, `7`, `9`) combined in
`MergeField.lean`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed

/-- Tag `1` (`session_version`, varint): `int32::merge` into `ss + 0x148`. -/
theorem mergeFieldGenSessionVersion_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) : MergeFieldGenOk C ctl (fun fl => fl.tag = 1) abs := by
  exact Leaf.MergeFieldGenSessionVersion.mergeFieldGenSessionVersion_ok C ctl hC

/-- Tag `5` (`previous_counter`, varint): `int32::merge` into `ss + 0x14c`. -/
theorem mergeFieldGenPreviousCounter_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) : MergeFieldGenOk C ctl (fun fl => fl.tag = 5) abs := by
  exact Leaf.MergeFieldGenPreviousCounter.mergeFieldGenPreviousCounter_ok C ctl hC

/-- Tags `2`, `3`, `4` (`local_identity_public` at `ss`, `remote_identity_public` at `ss + 0x18`,
`root_key` at `ss + 0x30`): `bytes::merge` of 33- or 32-byte payloads. -/
theorem mergeFieldGenIdentityRootKeys_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) :
    MergeFieldGenOk C ctl (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4) abs := by
  exact Leaf.MergeFieldGenIdentityRootKeys.mergeFieldGenIdentityRootKeys_ok C ctl hC

/-- Tag `6` (`sender_chain` when `sender = none`): initializes `Chain::default()` at `ss + 0x90` and
calls `message::merge<Chain>`. -/
theorem mergeFieldGenSenderChain_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hCh : ChainMergeGenOk C ctl abs) :
    MergeFieldGenOk C ctl (fun fl => fl.tag = 6) abs := by
  exact Leaf.MergeFieldGenSenderChain.mergeFieldGenSenderChain_ok C ctl hC hCh

/-- Tag `7` (`receiver_chains` when `recv.length < maxReceiverChains`): decodes a `Chain` via
`message::merge<Chain>` and pushes it into `Vec<Chain>` at `ss + 0x48` (calling
`RawVec<Chain>::grow_one` when `len = cap`). -/
theorem mergeFieldGenReceiverChains_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (hCh : ChainMergeGenOk C ctl abs) :
    MergeFieldGenOk C ctl (fun fl => fl.tag = 7) abs := by
  exact Leaf.MergeFieldGenReceiverChains.mergeFieldGenReceiverChains_ok C ctl hC hCh

/-- Tag `9` (`pending_pre_key` when `pending = none`): initializes `PendingPreKey::default()` and
decodes `base_key` (tag `2`, 33 bytes) into `ss + 0xf8` via `bytes::merge`. -/
theorem mergeFieldGenPendingPreKey_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) : MergeFieldGenOk C ctl (fun fl => fl.tag = 9) abs := by
  exact Leaf.MergeFieldGenPendingPreKey.mergeFieldGenPendingPreKey_ok C ctl hC

end CryptoVerification.E2E.Record.DeserializeGeneral
