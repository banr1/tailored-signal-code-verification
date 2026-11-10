/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainExitG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG

/-!
# Segment Leaf Theorems for General `message::merge<Chain>`

Exports the entry, per-tag (`1`/`2`, `3`, `4`), and exit segment theorems for
`prost::encoding::message::merge::<Chain>` (`0x3974`) composed in `ChainMerge.lean`.
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

/-- Entry segment (`+0x000 → +0x120`, `k = 0`) of `message::merge<Chain>`: checks wire type `2`,
decodes the 1–3 byte length varint, verifies the remaining-length bound, and initializes registers
for `prostChainGAt A0 a ChainG.empty`. -/
theorem chainEntryG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (recordProg C ctl abs).fnAddr chainMergeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ chainMergeGenSpec.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    ChainStepG C ctl x R s0 s0 (ChainLoopG C ctl x R s0 0) abs := by
  exact Leaf.ChainEntryG.chainEntryG_ok_impl C ctl hC x R s0 hpc hrun hpre hal

/-- Field step (`+0x120 → +0x120`, `k → k + 1`) for tag `1` (`sender_ratchet_key` at `a`) and
tag `2` (`sender_ratchet_key_private` at `a + 0x18`) via `bytes::merge`. -/
theorem chainSenderRatchetKeyG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2)
    (hs : ChainLoopG C ctl x R s0 k s) :
    ChainStepG C ctl x R s0 s (ChainLoopG C ctl x R s0 (k + 1)) abs := by
  exact Leaf.ChainSenderRatchetKeyG.chainSenderRatchetKeyG_ok C ctl hC x R s0 k s hk htag hs

/-- Field step (`+0x120 → +0x120`, `k → k + 1`) for tag `3` (`chain_key` nested `ChainKey` message
into `Option<ChainKey>` at `a + 0x48`, decoding optional `index` tag `1` and `key` tag `2`). -/
theorem chainKeyFieldG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 3)
    (hs : ChainLoopG C ctl x R s0 k s) :
    ChainStepG C ctl x R s0 s (ChainLoopG C ctl x R s0 (k + 1)) abs := by
  exact Leaf.ChainKeyFieldG.chainKeyFieldG_ok C ctl hC x R s0 k s hk htag hs

/-- Field step (`+0x120 → +0x120`, `k → k + 1`) for tag `4` (`message_keys` nested `MessageKey`
sub-loop decoding optional `counter` tag `1` and 32-byte `seed` tag `5`, then pushing into
`Vec<MessageKey>` at `a + 0x30` via `RawVec<Chain>::grow_one` when `len = cap`). -/
theorem chainMessageKeysG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length) (htag : (x.c.fields[k]'hk).tag = 4)
    (hs : ChainLoopG C ctl x R s0 k s) :
    ChainStepG C ctl x R s0 s (ChainLoopG C ctl x R s0 (k + 1)) abs := by
  exact Leaf.ChainMessageKeysG.chainMessageKeysG_ok C ctl hC x R s0 k s hk htag hs

/-- Exit segment (`+0x120 → ret`) when all fields of `x.c` have been decoded, establishing
`chainMergeGenSpec.post`. -/
theorem chainExitG_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (x : ChainMergeGenGhost) (R : SepProp) (s0 s : State)
    (hs : ChainLoopG C ctl x R s0 x.c.fields.length s) :
    ChainStepG C ctl x R s0 s (ChainRetG x R s0) abs := by
  exact Leaf.ChainExitG.chainExitG_ok C ctl x R s0 s hs

end CryptoVerification.E2E.Record.DeserializeGeneral
