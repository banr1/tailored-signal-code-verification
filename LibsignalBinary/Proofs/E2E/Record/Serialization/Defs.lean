/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Support.Phi
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefs
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
public import LibsignalBinary.Proofs.E2E.Record.Support.Repr -- shake: keep

/-!
# Specifications and memory-level encoders for `SessionRecord::serialize`

Defines symbol names, stack budgets, memory-level protobuf encoders, ghost canonicity predicates,
and Hoare specifications for `<SessionRecord>::serialize` (`0x1857c`) and its callees
(`MessageKey::encoded_len`, `Chain::encoded_len`, `SessionStructure::encoded_len`,
`encode::<Chain>`, `SessionStructure::encode_raw`, `SessionStructure::clone`, and
`Vec<Vec<u8>>::clone`).

Because `sessionStateReprAt` and `chainAt` permit non-canonical trailing bytes in ghost `Vec<u8>`
fields, each leaf specification states its output in terms of memory-level encoders (`encChainMem`,
`encSessionMem`, `encRecordMem`) parameterized by the ghost state; `Canon.lean` equates these with
`encSession` and `encodeRecord` under `CanonSession` / `CanonRecord`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record

/-! ## Symbol names -/

/-- `SessionRecord::serialize` (image offset `0x1857c`). -/
abbrev serializeName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::serialize"

/-- `<SessionStructure as Clone>::clone` (image offset `0x240f0`). -/
abbrev sessionCloneName : String :=
  "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"

/-- `<Vec<Vec<u8>> as Clone>::clone` (image offset `0x2c75c`). -/
abbrev vecVecCloneName : String :=
  "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"

/-- `<SessionStructure as prost::Message>::encode_raw::<Vec<u8>>` (image offset `0x4d38`). -/
abbrev encodeRawName : String :=
  "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"

/-- `prost::encoding::message::encode::<Chain, Vec<u8>>` (image offset `0x44b0`). -/
abbrev encodeChainName : String :=
  "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"

/-- `<SessionStructure as prost::Message>::encoded_len` (image offset `0x25fd0`). -/
abbrev sessionLenName : String :=
  "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len"

/-- `<Chain as prost::Message>::encoded_len` (image offset `0x26aa0`). -/
abbrev chainLenName : String :=
  "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len"

/-- `<chain::MessageKey as prost::Message>::encoded_len` (image offset `0x2d6bc`). -/
abbrev msgKeyLenName : String :=
  "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len"

/-! ## Stack budgets

Upper bounds formed by adding each function's own stack frame to the budgets of its sequential
callees. -/

/-- `MessageKey::encoded_len` (`0x2d6bc`): leaf, frame `0x10`. -/
abbrev msgKeyLenStack : Nat := 0x10

/-- `Chain::encoded_len` (`0x26aa0`): frame `0x40`, calls `MessageKey::encoded_len`. -/
abbrev chainLenStack : Nat := 0x40 + msgKeyLenStack

/-- `SessionStructure::encoded_len` (`0x25fd0`): frame `0x40`, calls `Chain::encoded_len`. -/
abbrev sessionLenStack : Nat := 0x40 + chainLenStack

/-- `encode::<Chain>` (`0x44b0`): frame `0x60`, calling `encode_varint`, `do_reserve_and_handle`,
`Chain::encoded_len`, and `memcpy`. -/
abbrev encodeChainStack : Nat :=
  0x60 + Prost.encodeVarintStack + doReserveStack + chainLenStack

/-- `SessionStructure::encode_raw` (`0x4d38`): frame `0x50`, calls `encode_varint`,
`do_reserve_and_handle`, `encode::<Chain>` and `memcpy`. -/
abbrev encodeRawStack : Nat :=
  0x50 + Prost.encodeVarintStack + doReserveStack + encodeChainStack

/-- `SessionStructure::clone` (`0x240f0`, frame `0x1d0`) and `Chain::clone` (`0x24848`, frame
`0xd0`), plus `__rust_alloc` and `0x400` bytes for the inlined `Vec<MessageKey>` clone loops. -/
abbrev sessionCloneStack : Nat := 0x1d0 + 0xd0 + 0x400 + allocHookStack

/-- `Vec<Vec<u8>>::clone` (`0x2c75c`): frame `0x60` plus `__rust_alloc` when non-empty. -/
abbrev vecVecCloneStack : Nat := 0x60 + allocHookStack

/-- `SessionRecord::serialize` (`0x1857c`): own frame (`0x360` upper bound) plus clone, length,
encoding, reserve, and drop callees. -/
abbrev serializeStack : Nat :=
  0x360 + sessionCloneStack + vecVecCloneStack + sessionLenStack + allocHookStack +
    Prost.encodeVarintStack + encodeRawStack + doReserveStack +
    FromRecordCallees.dropSessionStructureLocal1Stack

/-! ## Little-endian byte decoding -/

/-- Natural number represented by little-endian bytes `bs`. -/
def leNat : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- Little-endian `u32` at byte offset `i` of `bs`. -/
def leU32At (bs : List (BitVec 8)) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (leNat ((bs.drop i).take 4))

/-! ## Memory-level protobuf encodings

Protobuf encoders reading the raw ghost `Vec<u8>` slices in `encode_raw` tag order. -/

/-- Memory-level protobuf encoding of `session_structure::Chain`: tags 1 (`sender_ratchet_key`),
2 (`sender_ratchet_key_private`), 3 (`chain_key`), and 4 (`message_keys`, omitting the three empty
key/IV `Vec`s in `messageKeyAt`). -/
def encChainMem (gc : ChainGhost × ReceiverChain) : List (BitVec 8) :=
  bytesField 1 gc.1.srk.bytes ++ bytesField 2 gc.1.priv.bytes ++
    msgField 3 (gc.2.chainKey.map encChainKey) ++
    (gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten

/-- Views a `SenderChain` as a `ReceiverChain`-shaped `Chain` with empty `messageKeys` for uniform
`protoChainAt` and `encChainMem` reasoning. -/
def senderAsChain (sc : SenderChain) : ReceiverChain :=
  { senderRatchetKey := sc.ratchetKey.publicKey, chainKey := some sc.chainKey, messageKeys := [] }

/-- Views a `SenderChainGhost` as a `ChainGhost` with empty message-key ghost list. -/
def senderGhostAsChain (g : SenderChainGhost) : ChainGhost :=
  { srk := g.srk, priv := g.priv, mkCap := g.mkCap, mkPtr := g.mkPtr, keys := [], ck := g.ck }

/-- Memory-level protobuf encoding of `PendingPreKey` (tags 1–4), reading `base_key` from the ghost
`Vec<u8>` and scalar fields from the model via `PendingRel`. -/
def encPendingMem (g : TailVecGhost) (p : PendingPreKey) : List (BitVec 8) :=
  optUint32Field 1 p.preKeyId ++ bytesField 2 g.vec.bytes ++ int32Field 3 p.signedPreKeyId ++
    uint64Field 4 p.timestamp

/-- Memory-level `pending_pre_key` field (tag 9). -/
def encPendingFieldMem : Option TailVecGhost → Option PendingPreKey → List (BitVec 8)
  | some g, some p => lenField 9 (encPendingMem g p)
  | _, _ => []

/-- Memory-level `sender_chain` field (tag 6). -/
def encSenderFieldMem : Option SenderChainGhost → Option SenderChain → List (BitVec 8)
  | some g, some sc => lenField 6 (encChainMem (senderGhostAsChain g, senderAsChain sc))
  | _, _ => []

/-- Memory-level protobuf encoding of `SessionStructure` in tag order 1–7, 9, 10, 11, 13, 14, 15,
using ghost `Vec<u8>` bytes for identity and chain keys. -/
def encSessionMem (G : SessionGhost) (s : Session (List (BitVec 8))) : List (BitVec 8) :=
  let st := s.state
  uint32Field 1 st.sessionVersion ++
  bytesField 2 G.localIk.bytes ++
  bytesField 3 G.remoteIk.bytes ++
  bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++
  uint32Field 5 st.previousCounter ++
  encSenderFieldMem G.sender st.senderChain ++
  ((G.chains.zip st.receiverChains).map fun gc => lenField 7 (encChainMem gc)).flatten ++
  encPendingFieldMem G.pending s.pendingPreKey ++
  uint32Field 10 s.remoteRegistrationId ++
  uint32Field 11 s.localRegistrationId ++
  bytesField 13 s.aliceBaseKey ++
  msgField 14 (s.pendingKyberPreKey.map encPendingKyber) ++
  bytesField 15 st.pqRatchetState

/-- Memory-level `current_session` field (tag 1 of `RecordStructure`). -/
def encCurMem : Option SessionGhost → Option (Session (List (BitVec 8))) → List (BitVec 8)
  | some G, some s => lenField 1 (encSessionMem G s)
  | _, _ => []

/-- Memory-level protobuf encoding of `RecordStructure` with empty `previous_sessions`. -/
def encRecordMem (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : List (BitVec 8) :=
  encCurMem g.cur r.currentSession

/-! ## Ghost canonicity predicates -/

/-- Canonicity of a receiver-chain ghost: canonical `senderRatchetKey` bytes and empty private-key `Vec`. -/
def CanonChain (gc : ChainGhost × ReceiverChain) : Prop :=
  gc.1.srk.bytes = gc.2.senderRatchetKey.serialize ∧ gc.1.priv.bytes = []

/-- Canonicity of a sender-chain ghost: canonical public-key serialization and exact 32-byte private key. -/
def CanonSender : Option SenderChainGhost → Option SenderChain → Prop
  | none, none => True
  | some g, some sc => g.srk.bytes = sc.ratchetKey.publicKey.serialize ∧
      g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList
  | _, _ => False

/-- Canonicity of a pending pre-key ghost: canonical `base_key` serialization. -/
def CanonPending : Option TailVecGhost → Option PendingPreKey → Prop
  | none, none => True
  | some g, some p => g.vec.bytes = p.baseKey.serialize
  | _, _ => False

/-- Canonicity of a session ghost across identity keys, sender/receiver chains, and pending pre-key. -/
def CanonSession (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  G.localIk.bytes = s.state.localIdentity.serialize ∧
  G.remoteIk.bytes = (s.state.remoteIdentity.map IdentityKey.serialize).getD [] ∧
  CanonSender G.sender s.state.senderChain ∧
  G.chains.length = s.state.receiverChains.length ∧
  (∀ gc ∈ G.chains.zip s.state.receiverChains, CanonChain gc) ∧
  CanonPending G.pending s.pendingPreKey

/-- Option lifting of `CanonSession` to `current_session`. -/
def CanonCur : Option SessionGhost → Option (Session (List (BitVec 8))) → Prop
  | none, none => True
  | some G, some s => CanonSession G s
  | _, _ => False

/-- Canonicity of a `RecordGhost` with respect to `SessionRecord`. -/
def CanonRecord (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  CanonCur g.cur r.currentSession

/-! ## Subroutine specifications -/

/-- Panic postcondition for allocator failure (`allocFailedIn s0 sf` with monotonic trace). -/
def allocPanic {α : Type} : α → State → State → SepProp :=
  fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Ghost state for `MessageKey::encoded_len`. -/
structure MsgKeyLenGhost where
  a : BitVec 64
  gk : MessageKeyGhost × MessageKeyGenerator

/-- `<chain::MessageKey as Message>::encoded_len` (`0x2d6bc`): returns `(encMessageKey gk.2).length`
without panicking while preserving `messageKeyAt`. -/
def msgKeyLenSpec (A : RustAlloc) : Spec MsgKeyLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ messageKeyAt A x.gk x.a ∗ stackAt s.sp msgKeyLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encMessageKey x.gk.2).length ∧ sf.trace = s0.trace⌝ ∗
      messageKeyAt A x.gk x.a ∗ stackAt s0.sp msgKeyLenStack

/-- Shared `session_structure::Chain` heap layout common to both `chainAt` (receiver chains) and
`optSenderChainAt` (`Some` sender chains). -/
def protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧
    gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

/-- Ghost state for `Chain::encoded_len`. -/
structure ChainLenGhost where
  a : BitVec 64
  gc : ChainGhost × ReceiverChain

/-- `<Chain as Message>::encoded_len` (`0x26aa0`): returns `(encChainMem gc).length` while preserving `protoChainAt`. -/
def chainLenSpec (A : RustAlloc) : Spec ChainLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ (encChainMem x.gc).length < 2 ^ 32⌝ ∗
      protoChainAt A x.gc x.a ∗ stackAt s.sp chainLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length ∧ sf.trace = s0.trace⌝ ∗
      protoChainAt A x.gc x.a ∗ stackAt s0.sp chainLenStack

/-- Ghost state for `SessionStructure::encoded_len`. -/
structure SessionLenGhost where
  ss : BitVec 64
  G : SessionGhost
  s : Session (List (BitVec 8))

/-- `<SessionStructure as Message>::encoded_len` (`0x25fd0`): returns `(encSessionMem G s).length` while preserving `sessionStateReprAt`. -/
def sessionLenSpec (A : RustAlloc) : Spec SessionLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s.sp sessionLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encSessionMem x.G x.s).length ∧ sf.trace = s0.trace⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s0.sp sessionLenStack

/-- Ghost state for `prost::encoding::message::encode::<Chain, Vec<u8>>`. -/
structure EncodeChainGhost where
  tag : Nat
  a : BitVec 64
  gc : ChainGhost × ReceiverChain
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- `prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`): appends
`lenField tag (encChainMem gc)` to the output `Vec<u8>`, preserving `protoChainAt`. -/
def encodeChainSpec (A : RustAlloc) : Spec EncodeChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧ x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32⌝ ∗
      protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeChainStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ protoChainAt A x.gc x.a ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A x.v cap' ptr' (x.bs ++ lenField x.tag (encChainMem x.gc))) ∗
      A.pool ∗ stackAt s0.sp encodeChainStack
  onPanic := allocPanic

/-- Ghost state for `SessionStructure::encode_raw::<Vec<u8>>`. -/
structure EncodeRawGhost where
  ss : BitVec 64
  G : SessionGhost
  s : Session (List (BitVec 8))
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- `<SessionStructure as Message>::encode_raw::<Vec<u8>>` (`0x4d38`): appends `encSessionMem G s`
to the output `Vec<u8>`, preserving `sessionStateReprAt`. -/
def encodeRawSpec (A : RustAlloc) : Spec EncodeRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp encodeRawStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool ∗ stackAt s0.sp encodeRawStack
  onPanic := allocPanic

/-- Ghost state for `SessionStructure::clone`. -/
structure SessionCloneGhost where
  dst : BitVec 64
  src : BitVec 64
  G : SessionGhost
  s : Session (List (BitVec 8))

/-- `<SessionStructure as Clone>::clone` (`0x240f0`): deep-copies `sessionStateReprAt` into the
344-byte destination at `dst` with a fresh ghost `G'` having identical `encSessionMem`. -/
def sessionCloneSpec (A : RustAlloc) : Spec SessionCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      sessionStateReprAt A x.src x.G x.s ∗ memRegion x.dst 344 ∗ A.pool ∗ stackAt s.sp sessionCloneStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A x.dst G' x.s) ∗
      A.pool ∗ stackAt s0.sp sessionCloneStack
  onPanic := allocPanic

/-- Ghost state for `Vec<Vec<u8>>::clone` on an empty source vector. -/
structure VecVecCloneGhost where
  dst : BitVec 64
  src : BitVec 64

/-- `<Vec<Vec<u8>> as Clone>::clone` (`0x2c75c`) on `len = 0`: writes the empty `Vec` header
`(0, 8, 0)` at `dst` without allocating. -/
def vecVecCloneEmptySpec : Spec VecVecCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 0#64⌝ ∗
      memRegion x.dst 24 ∗ stackAt s.sp vecVecCloneStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecHeader x.dst 0#64 8#64 0#64 ∗ stackAt s0.sp vecVecCloneStack

/-! ## Top-level `SessionRecord::serialize` specifications -/

/-- Ghost state for `SessionRecord::serialize`. -/
structure SerializeGhost where
  self : BitVec 64
  out : BitVec 64
  g : RecordGhost
  r : SessionRecord (List (BitVec 8))

/-- `SessionRecord::serialize` (`0x1857c`), memory-level: writes `Ok(encRecordMem g r)` to `out`
while preserving `sessionRecordAt`. -/
def serializeSpec (A : RustAlloc) : Spec SerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ (encRecordMem x.g x.r).length < 2 ^ 32⌝ ∗
      sessionRecordAt A x.self x.g x.r ∗ memRegion x.out 32 ∗ A.pool ∗
      stackAt s.sp serializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionRecordAt A x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encRecordMem x.g x.r) ∗
      A.pool ∗ stackAt s0.sp serializeStack
  onPanic := allocPanic

/-- `SessionRecord::serialize` (`0x1857c`) on a canonical record: writes `Ok(encodeRecord r)` to `out`. -/
def serializeCanonSpec (A : RustAlloc) : Spec SerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ CanonRecord x.g x.r ∧
      (encodeRecord x.r).length < 2 ^ 32⌝ ∗
      sessionRecordAt A x.self x.g x.r ∗ memRegion x.out 32 ∗ A.pool ∗
      stackAt s.sp serializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionRecordAt A x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecord x.r) ∗
      A.pool ∗ stackAt s0.sp serializeStack
  onPanic := allocPanic

/-! ## Program-level and relocatable helpers -/

/-- `subroutine_ok` wrapper for `name` on `tripleRatchetProgAt b C ctl abs`. -/
def OkAt {α : Type} (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (spec : Spec α) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr name) spec

/-- Sequences two `SepWP` segments across an entailment while preserving `LibsignalCodeLoaded`. -/
theorem sepWP_seq_clean_lscl {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {pl : Obj.MultiPlacement}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → Q sm → SepWP prog tgt sm P_mid post) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hclm =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hclm hQ))

/-- External allocator, `memcpy`, shim, and error-handler hook contracts required by `SessionRecord::serialize`. -/
structure PlacedSerializeHooks (A : RustAlloc) (H : String → Option (State → State)) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimSpec
  alloc : HookSat H lsRustAllocSym (rustAllocSpec A)
  realloc : HookSat H lsRustReallocSym (rustReallocSpec A)
  dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  memcpy : HookSat H "memcpy" sessionMemcpyRegionSpec
  panic_handle_error : H lsHandleErrorSym = some Rust.panicked

end CryptoVerification.E2E.Record.Serialization


