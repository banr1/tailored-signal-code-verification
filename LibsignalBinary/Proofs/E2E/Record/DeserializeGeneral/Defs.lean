/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeedTop
public import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Definitions and Specifications for General `SessionRecord::deserialize`

Defines the decoded prost value representations, memory layouts, scope predicates, and subroutine
specifications for `SessionRecord::deserialize` (`0x16ed4`) over arbitrary in-scope records
`encodeRecord r` (`DeserializeScope r`):
* `ChainG` and `prostChainGAt`: 104-byte prost `Chain` layout with `Vec<MessageKey>` at `+0x30`
  (104-byte `prostMsgKeyAt` elements holding `seed` at `+72` and `counter` at `+96`).
* `SSG` and `prostSSGAt`: 344-byte prost `SessionStructure` layout including `previous_counter` at
  `+0x14c` and up to `maxReceiverChains` (`5`) receiver chains at `+0x48`.
* `GenField`, `genFields`, and `recFields`: wire field decomposition with multi-byte varint lengths
  and omitted zero chain-key indices.
* `mergeFieldGenSpec`, `chainMergeGenSpec`, and `deserializeGenSpec`: general contracts for
  `SessionStructure::merge_field` (`0x581c`), `message::merge<Chain>` (`0x3974`), and
  `SessionRecord::deserialize` (`0x16ed4`).
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
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord allocPanic)

/-! ## Prost `Chain` Values, Fields, and Layout -/

/-- The decoded value of a prost `session_structure::Chain`: the serialized sender ratchet key, the
private key (`[]` when absent: receiver chains), the chain key `(index, key)` if present, and the
skipped message keys in wire order (oldest last, as `encReceiverChain` writes them). -/
structure ChainG where
  srk : List (BitVec 8)
  priv : List (BitVec 8)
  ck : Option (BitVec 32 × List (BitVec 8))
  keys : List MessageKeyGenerator

def ChainG.empty : ChainG := ⟨[], [], none, []⟩

/-- The bytes prost writes for a chain (`encSenderChain` / `encReceiverChain`, `Phi.lean`):
`srk` (tag 1), the private key (tag 2, omitted when empty), the chain key message (tag 3, when
present; its index omitted when 0), the message keys (tag 4 each). -/
def ChainG.enc (c : ChainG) : List (BitVec 8) :=
  bytesField 1 c.srk ++ bytesField 2 c.priv ++
    msgField 3 (c.ck.map fun ik => uint32Field 1 ik.1 ++ bytesField 2 ik.2) ++
    (c.keys.map fun m => lenField 4 (encMessageKey m)).flatten

/-- The length-delimited payload of a chain field (tags 6 / 7 of the SS): varint length, body. -/
def ChainG.payload (c : ChainG) : List (BitVec 8) :=
  encodeVarint (BitVec.ofNat 64 c.enc.length) ++ c.enc

/-- The well-formedness of a decoded in-scope chain: a 33-byte serialized key, a private key that
is absent or 32 bytes, a 32-byte chain key, 32-byte seeds, at most `maxMessageKeys` (2000) keys. -/
def ChainG.Ok (c : ChainG) : Prop :=
  c.srk.length = 33 ∧ (c.priv = [] ∨ c.priv.length = 32) ∧
    (∀ ik, c.ck = some ik → ik.2.length = 32) ∧ (∀ m ∈ c.keys, m.seed.length = 32) ∧
    c.keys.length ≤ maxMessageKeys

/-- One field of a chain's encoding, with its decoded payload. -/
inductive ChainField where
  /-- tag 1 (`sender_ratchet_key`). -/
  | srk (b : List (BitVec 8))
  /-- tag 2 (`sender_ratchet_key_private`). -/
  | priv (b : List (BitVec 8))
  /-- tag 3 (`chain_key`, a `ChainKey` message: index tag 1, key tag 2). -/
  | ck (i : BitVec 32) (k : List (BitVec 8))
  /-- tag 4 (`message_keys`, one `MessageKey` message: counter tag 1, seed tag 5; pushed). -/
  | key (mk : MessageKeyGenerator)

def ChainField.tag : ChainField → Nat
  | .srk _ => 1 | .priv _ => 2 | .ck _ _ => 3 | .key _ => 4

/-- The bytes of a chain field (key, varint length, body). -/
def ChainField.enc : ChainField → List (BitVec 8)
  | .srk b => lenField 1 b
  | .priv b => lenField 2 b
  | .ck i k => lenField 3 (uint32Field 1 i ++ bytesField 2 k)
  | .key m => lenField 4 (encMessageKey m)

/-- prost's `Chain::merge_field` on the decoded value: bytes fields replace, the chain key is set,
message keys are pushed. -/
def ChainG.apply (c : ChainG) : ChainField → ChainG
  | .srk b => { c with srk := b }
  | .priv b => { c with priv := b }
  | .ck i k => { c with ck := some (i, k) }
  | .key m => { c with keys := c.keys ++ [m] }

/-- The fields of `c.enc`, in order. -/
def ChainG.fields (c : ChainG) : List ChainField :=
  (if c.srk = [] then [] else [ChainField.srk c.srk]) ++
    (if c.priv = [] then [] else [ChainField.priv c.priv]) ++
    (match c.ck with
     | some (i, k) => [ChainField.ck i k]
     | none => []) ++
    c.keys.map ChainField.key

def chainGAfter (c : ChainG) (k : Nat) : ChainG :=
  (c.fields.take k).foldl ChainG.apply ChainG.empty

/-- A prost `MessageKey` at `a` (104 bytes) holding the `Seed`-form key `mk` (same layout as
`messageKeyAt`, `Specifications/LibsignalSessionRepr.lean`). -/
def prostMsgKeyAt (A : RustAlloc) (mk : MessageKeyGenerator) (a : BitVec 64) : SepProp :=
  vecU8 A a [] ∗ vecU8 A (a + 24#64) [] ∗ vecU8 A (a + 48#64) [] ∗ vecU8 A (a + 72#64) mk.seed ∗
    ((a + 96#64) ↦₃₂ mk.counter) ∗ memRegion (a + 100#64) 4

/-- 104-byte prost `session_structure::Chain` layout at `a` holding `c`, with `Vec<MessageKey>`
(104-byte elements, alignment 8) at `a + 0x30`. -/
def prostChainGAt (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗
    vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

/-! ## Prost `SessionStructure` Values, Fields, and Layout -/

/-- The decoded value of the prost `SessionStructure` fields an in-scope record can set (the
others stay at their defaults; `prostSSGAt` pins them). -/
structure SSG where
  version : BitVec 32
  lik : List (BitVec 8)
  rik : List (BitVec 8)
  root : List (BitVec 8)
  prevCounter : BitVec 32
  recv : List ChainG
  sender : Option ChainG
  pending : Option (List (BitVec 8))

def SSG.empty : SSG := ⟨0, [], [], [], 0, [], none, none⟩

/-- 344-byte prost `SessionStructure` layout at `ss` holding `v : SSG`, with `ChainG` chains and
`previous_counter` at `ss + 0x14c`. -/
def prostSSGAt (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

/-- One field of an in-scope `encSession s`, with its decoded payload. -/
inductive GenField where
  /-- tag 1 (`session_version`, varint). -/
  | version (v : BitVec 32)
  /-- tag 2 (`local_identity_public`). -/
  | lik (b : List (BitVec 8))
  /-- tag 3 (`remote_identity_public`). -/
  | rik (b : List (BitVec 8))
  /-- tag 4 (`root_key`). -/
  | root (b : List (BitVec 8))
  /-- tag 5 (`previous_counter`, varint). -/
  | prevCounter (v : BitVec 32)
  /-- tag 6 (`sender_chain`, a `Chain` message). -/
  | sender (c : ChainG)
  /-- tag 7 (`receiver_chains`, one `Chain` message, pushed). -/
  | recv (c : ChainG)
  /-- tag 9 (`pending_pre_key`, a `PendingPreKey` message with only `base_key`, tag 2). -/
  | pending (baseKey : List (BitVec 8))

def GenField.tag : GenField → Nat
  | .version _ => 1 | .lik _ => 2 | .rik _ => 3 | .root _ => 4 | .prevCounter _ => 5
  | .sender _ => 6 | .recv _ => 7 | .pending _ => 9

/-- The wire type of a field: varint for tags 1 and 5, length-delimited otherwise. -/
def GenField.wt : GenField → WireType
  | .version _ => .varint
  | .prevCounter _ => .varint
  | _ => .lengthDelimited

/-- The payload bytes of a field after its key: the varint for tags 1 / 5, the varint length and
body for the others. -/
def GenField.payload : GenField → List (BitVec 8)
  | .version v => encodeVarint (v.setWidth 64)
  | .lik b => encodeVarint (BitVec.ofNat 64 b.length) ++ b
  | .rik b => encodeVarint (BitVec.ofNat 64 b.length) ++ b
  | .root b => encodeVarint (BitVec.ofNat 64 b.length) ++ b
  | .prevCounter v => encodeVarint (v.setWidth 64)
  | .sender c => c.payload
  | .recv c => c.payload
  | .pending k => encodeVarint (BitVec.ofNat 64 (lenField 2 k).length) ++ lenField 2 k

def GenField.enc (fl : GenField) : List (BitVec 8) := encodeKey fl.tag fl.wt ++ fl.payload

/-- prost's `SessionStructure::merge_field` on the decoded value: scalars and bytes replace,
`sender_chain` merges into a default chain (it is `None` before: `GenField.Fresh`),
`receiver_chains` pushes, `pending_pre_key` merges `base_key` into a default `PendingPreKey`. -/
def SSG.apply (v : SSG) : GenField → SSG
  | .version x => { v with version := x }
  | .lik b => { v with lik := b }
  | .rik b => { v with rik := b }
  | .root b => { v with root := b }
  | .prevCounter x => { v with prevCounter := x }
  | .sender c => { v with sender := some c }
  | .recv c => { v with recv := v.recv ++ [c] }
  | .pending k => { v with pending := some k }

/-- Payload facts of an in-scope field: 33-byte keys, a 32-byte root key, well-formed chains
(the sender chain with a 32-byte private key, a chain key and no message keys; receiver chains
with no private key). -/
def GenField.Ok : GenField → Prop
  | .version _ => True
  | .lik b => b.length = 33
  | .rik b => b.length = 33
  | .root b => b.length = 32
  | .prevCounter _ => True
  | .sender c => c.Ok ∧ c.priv.length = 32 ∧ c.ck.isSome = true ∧ c.keys = []
  | .recv c => c.Ok ∧ c.priv = []
  | .pending k => k.length = 33

/-- The freshness side condition of a field against the decoded value before it: `sender_chain`
and `pending_pre_key` are still `None` (each comes at most once), and `receiver_chains` has room
(fewer than `maxReceiverChains` = 5 chains, so the push grows the buffer 0 → 4 → 8 at most). -/
def GenField.Fresh (v : SSG) : GenField → Prop
  | .sender _ => v.sender = none
  | .recv _ => v.recv.length < maxReceiverChains
  | .pending _ => v.pending = none
  | _ => True

/-! ## Record Field Lists -/

def senderChainG (c : SenderChain) : ChainG :=
  ⟨c.ratchetKey.publicKey.serialize, c.ratchetKey.privateKey.bytes.toList,
    some (c.chainKey.index, HMAC.keyToBytes32 c.chainKey.key), []⟩

def recvChainG (c : ReceiverChain) : ChainG :=
  ⟨c.senderRatchetKey.serialize, [],
    c.chainKey.map (fun ck => (ck.index, HMAC.keyToBytes32 ck.key)), c.messageKeys⟩

/-- Ordered wire fields of `encSession s` for an in-scope session (`SessionScope`). -/
def genFields (s : Session (List (BitVec 8))) : List GenField :=
  (if s.state.sessionVersion = 0 then [] else [GenField.version s.state.sessionVersion]) ++
  (if s.state.localIdentity.serialize = [] then []
   else [GenField.lik s.state.localIdentity.serialize]) ++
  (match s.state.remoteIdentity with
   | some ik => if ik.serialize = [] then [] else [GenField.rik ik.serialize]
   | none => []) ++
  (if HMAC.keyToBytes32 s.state.rootKey = [] then []
   else [GenField.root (HMAC.keyToBytes32 s.state.rootKey)]) ++
  (if s.state.previousCounter = 0 then [] else [GenField.prevCounter s.state.previousCounter]) ++
  (match s.state.senderChain with
   | some c => [GenField.sender (senderChainG c)]
   | none => []) ++
  s.state.receiverChains.map (fun c => GenField.recv (recvChainG c)) ++
  (match s.pendingPreKey with
   | some p => [GenField.pending p.baseKey.serialize]
   | none => [])

def recFields (r : SessionRecord (List (BitVec 8))) : List GenField :=
  match r.currentSession with
  | some s => genFields s
  | none => []

def ssgAfter (r : SessionRecord (List (BitVec 8))) (k : Nat) : SSG :=
  ((recFields r).take k).foldl SSG.apply SSG.empty

/-- Decoded `SSG` of a complete in-scope session (`ssgAfter r (recFields r).length`). -/
def ssgOf (s : Session (List (BitVec 8))) : SSG :=
  ⟨s.state.sessionVersion, s.state.localIdentity.serialize,
    (s.state.remoteIdentity.map IdentityKey.serialize).getD [], HMAC.keyToBytes32 s.state.rootKey,
    s.state.previousCounter, s.state.receiverChains.map recvChainG,
    s.state.senderChain.map senderChainG, s.pendingPreKey.map (fun p => p.baseKey.serialize)⟩

/-! ## Decoder Scope (`SessionScope` and `DeserializeScope`) -/

/-- Session-level scope for general `SessionRecord::deserialize`: at most `maxReceiverChains` (`5`)
receiver chains, no Kyber pre-key, zero registration IDs, empty `alice_base_key`, and at most
`base_key` set in `pending_pre_key`. -/
def SessionScope (s : Session (List (BitVec 8))) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧ s.pendingKyberPreKey = none ∧
    s.localRegistrationId = 0 ∧ s.remoteRegistrationId = 0 ∧ s.aliceBaseKey = [] ∧
    ∀ p, s.pendingPreKey = some p → p.preKeyId = none ∧ p.signedPreKeyId = 0 ∧ p.timestamp = 0

/-- Record-level scope for general `SessionRecord::deserialize`: `InScope r`, a `some` current
session, and `SessionScope`. -/
def DeserializeScope (r : SessionRecord (List (BitVec 8))) : Prop :=
  InScope r ∧ ∃ s, r.currentSession = some s ∧ SessionScope s

/-! ## Callee Specifications (`merge_field` and `message::merge<Chain>`) -/

/-- Ghost arguments of a general `merge_field` call: the SS address `ss`, the decoded value `v`
before the call, the field `fld` (key already consumed), the cursor `&mut &mut &[u8]` `bufRef`
holding the slice-header address `slot`, the slice data pointer `ptr` and the rest `tail`. -/
structure MergeFieldGenGhost where
  ss : BitVec 64
  v : SSG
  fld : GenField
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)

def mergeFieldGenSpecAt (img : Obj.Image) (P : GenField → Prop) : Spec MergeFieldGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 32 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGAt A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStack
  onPanic := allocPanic

/-- Contract for `SessionStructure::merge_field` (`0x581c`) on an in-scope field satisfying `P`. -/
def mergeFieldGenSpec (P : GenField → Prop) : Spec MergeFieldGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 32 ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      prostSSGAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGAt A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStack
  onPanic := allocPanic

/-- Ghost arguments of a general `message::merge<Chain>` call: the chain address `a`, the decoded
chain `c` it ends with, the cursor (`bufRef`, `slot`, `ptr`) and the rest `tail`. -/
structure ChainMergeGenGhost where
  a : BitVec 64
  c : ChainG
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  tail : List (BitVec 8)

def chainMergeGenSpecAt (img : Obj.Image) : Spec ChainMergeGenGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ x.c.Ok ∧
      (x.c.payload ++ x.tail).length < 2 ^ 32 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostChainGAt A0 x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      stackAt s.sp chainMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainGAt A0 x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      stackAt s0.sp chainMergeStack
  onPanic := allocPanic

/-- Contract for `message::merge<Chain>` (`0x3974`) decoding an in-scope chain into a default
`Chain`. -/
def chainMergeGenSpec : Spec ChainMergeGenGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ x.c.Ok ∧
      (x.c.payload ++ x.tail).length < 2 ^ 32 ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      prostChainGAt A0 x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      stackAt s.sp chainMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainGAt A0 x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      stackAt s0.sp chainMergeStack
  onPanic := allocPanic

def MergeFieldGenOkAt (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (P : GenField → Prop) (abs : String → Option (State → State) := fun _ => none) : Prop :=
  OkAt img.base C ctl abs mergeFieldName (mergeFieldGenSpecAt img P)

def ChainMergeGenOkAt (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State) := fun _ => none) : Prop :=
  OkAt img.base C ctl abs chainMergeName (chainMergeGenSpecAt img)

/-- The callee contracts needed by `deserialize` and `merge_field` on arbitrary loaded `img`. -/
def DeserializeCalleesAt (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State) := fun _ => none) : Prop :=
  Prost.DecodeVarintSliceOk img.base C A0 ctl abs ∧
    Prost.Int32MergeOk img.base C A0 ctl abs ∧
    Prost.BytesMergeOk img C A0 ctl abs ∧
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage img)

def MergeFieldGenOk (C : Crypto) (ctl : BitVec 64)
    (P : GenField → Prop) (abs : String → Option (State → State) := fun _ => none) : Prop :=
  OkAt sessionImg0.base C ctl abs mergeFieldName (mergeFieldGenSpec P)

def ChainMergeGenOk (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State) := fun _ => none) : Prop :=
  OkAt sessionImg0.base C ctl abs chainMergeName chainMergeGenSpec

/-! ## Top-Level `deserializeGenSpec` and `SegStepG` -/

/-- Ghost arguments of a general `SessionRecord::deserialize` call: the input pointer `p`, the
`sret` slot `out`, and the record `r` whose encoding is the input (pinned, not existential). -/
structure DeserializeGenGhost where
  p : BitVec 64
  out : BitVec 64
  r : SessionRecord (List (BitVec 8))

/-- Specification of `SessionRecord::deserialize` (`0x16ed4`) on `encodeRecord r` for `r` satisfying
`DeserializeScope r`: writes `Ok(record)` at `out` holding `r` with a canonical `SessionGhost`
(`CanonRecord`). -/
noncomputable def deserializeGenSpec : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScope x.r ∧
      sessionImg0.FrozenLoaded s ∧ s.symtab = sessionImg0.symtab⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗
      (∃∗ g : RecordGhost, ⌜CanonRecord g x.r⌝ ∗ sessionRecordAt A0 x.out g x.r) ∗
      stackAt s0.sp recDeserializeStack
  onPanic := allocPanic

noncomputable def deserializeGenSpecAt (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScope x.r ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗
      (∃∗ g : RecordGhost, ⌜CanonRecord g x.r⌝ ∗ sessionRecordAt A0 x.out g x.r) ∗
      stackAt s0.sp recDeserializeStack
  onPanic := allocPanic

/-- Image-free postcondition of `SessionRecord::deserialize` (`deserializeGenSpec.post`), extracted
without referencing `sessionImg0` or `Obj.Image`. -/
noncomputable abbrev deserializeGenPost (x : DeserializeGenGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗
    (∃∗ g : RecordGhost, ⌜CanonRecord g x.r⌝ ∗ sessionRecordAt A0 x.out g x.r) ∗
    stackAt s0.sp recDeserializeStack

theorem deserializeGenSpec_post_eq :
    deserializeGenSpec.post = deserializeGenPost :=
  rfl

theorem deserializeGenSpecAt_post_eq (img : Obj.Image) :
    (deserializeGenSpecAt img).post = deserializeGenPost :=
  rfl


/-! ## Generic Segment Steps -/

/-- Single segment step from `s` of a function meeting `spec` in `prog`: if code is loaded,
execution reaches `Q` or panics with `spec.onPanic`. -/
def SegStepG {α : Type} (prog : Program) (spec : Spec α) (x : α) (R : SepProp) (s0 s : State)
    (Q : State → Prop) : Prop :=
  prog.CodeLoaded s.mem →
    ∃ s', Steps prog s s' ∧
      (Q s' ∨ (s'.status = .Panicked ∧ (s'.mem ⊨ spec.onPanic x s0 s' ∗ R)))

theorem segStepG_then {α : Type} {prog : Program} {spec : Spec α} {x : α} {R : SepProp}
    {s0 s : State} {Q : State → Prop} (h : SegStepG prog spec x R s0 s Q)
    (k : ∀ s', Q s' → reaches_outcome prog spec x R s0 s') :
    reaches_outcome prog spec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s', hst, hq | ⟨hpan, hmem⟩⟩ := h hL
  · exact reaches_outcome_steps hst (k s' hq)
  · exact reaches_outcome_steps hst (reaches_outcome_refl_panic hpan hmem)

end CryptoVerification.E2E.Record.DeserializeGeneral
