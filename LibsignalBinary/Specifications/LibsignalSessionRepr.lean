/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.RustHeap.Vec
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.AsmConstants -- shake: keep

/-!
# Ratchet-State Memory Layouts and Representation Predicates (`LibsignalSessionRepr`)

**Checked by Lean.** Byte encodings, ghost layout pins (`VecPin`, `VecGhost`, `MessageKeyGhost`,
`ChainGhost`, `RatchetGhost`), and separation-logic representation predicates (`messageKeyAt`,
`optChainKeyAt`, `chainAt`, `ratchetAt`, `consumeMessageKeyResultAt`) relating the compiled
`RatchetState` layout (`rustc` 1.98.1, `aarch64`, `panic = "abort"`, `codegen-units = 1`; DEV-M7)
to `CryptoGames.LibsignalSession`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSessionRepr

open Arm64 CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap

/-! ## Byte encodings -/

/-- Little-endian bytes of the low `n` bytes of a natural number. -/
def leBytes (n v : Nat) : List (BitVec 8) := (List.range n).map fun i => BitVec.ofNat 8 (v / 256 ^ i)

/-- The 36 bytes of a `ChainKey { key: [u8; 32], index: u32 }` (`ratchet/keys.rs:142–145`). The model
stores `key` as the `BitVec 256` of its little-endian bytes (`keyToBytes32` / `bytesToKey32`). -/
def chainKeyBytes (ck : ChainKey) : List (BitVec 8) :=
  keyToBytes32 ck.key ++ leBytes 4 ck.index.toNat

/-- The 100 bytes of a `SenderChain { ratchet_key: KeyPair, chain_key: ChainKey }`. -/
def senderChainBytes (sc : SenderChain) : List (BitVec 8) :=
  sc.ratchetKey.publicKey.bytes.toList ++ sc.ratchetKey.privateKey.bytes.toList ++
    chainKeyBytes sc.chainKey

/-- The 104 bytes of `Option<SenderChain>` at `RatchetState + 24`: `u32` tag, then the payload.
After a `None` tag the 100 payload bytes are unspecified (`pad`, a ghost). -/
def optSenderChainBytes (o : Option SenderChain) (pad : List (BitVec 8)) : List (BitVec 8) :=
  match o with
  | none => leBytes 4 0 ++ pad
  | some sc => leBytes 4 1 ++ senderChainBytes sc

/-- `CiphertextMessageType`'s `repr(u8)` discriminant (`rust/protocol/src/protocol.rs:32–40`). -/
def msgTypeByte : MessageType → BitVec 8
  | .whisper => 2
  | .preKey => 3

/-- The `Option<chain::ChainKey>` niche: `None` is the capacity word `usize::MAX` (all ones), as
rustc 1.98.1 lays it out in this image. Evidence (image offsets): `find_receiver_chain_key`
`0xe940: ldr x9, [x8, #0x48]; cmn x9, #1; b.eq` → `Err(InvalidSessionStructure("missing receiver
chain key"))`; `consume_message_key` uses the same `cmn …, #1` test for the `Option<MessageKey>`
niches at `+0x410` and `+0x634`. (`consume_message_key`'s own drop at `+0x564` only tests
`(cap as isize) ≥ 1`, so it treats every word ≥ 2^63 alike; `find_receiver_chain_key` does not.) -/
def optChainKeyNone : BitVec 64 := asm64% optionVecNoneWord

/-- `SignalProtocolError::DuplicatedMessage`'s variant word (niche in the `String` capacity of
other variants). -/
def errDuplicatedMessage : BitVec 64 := 0x8000000000000017#64

/-- `SignalProtocolError::InvalidMessage`'s variant word. -/
def errInvalidMessage : BitVec 64 := 0x8000000000000018#64

/-- `"message from too far into the future"` (`double_ratchet.rs:232–235`), 36 bytes. -/
def tooFarInFutureStr : List (BitVec 8) :=
  "message from too far into the future".toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

/-! ## Ghost pins -/

/-- The exact `(cap, ptr)` of a `Vec` whose contents the model determines. -/
structure VecPin where
  cap : BitVec 64
  ptr : BitVec 64

/-- The exact `Vec<u8>` `{cap, ptr, bytes}` of a preserved field whose bytes the model does not
determine by itself (e.g. the serialized `sender_ratchet_key`: the predicates pin its bytes to the
canonical 33-byte serialization by side conditions). -/
structure VecGhost where
  cap : BitVec 64
  ptr : BitVec 64
  bytes : List (BitVec 8)

/-- A preserved `Vec<u8>` at `v`, exactly as in its ghost. -/
def vecGhostAt (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  vecU8At A v g.cap g.ptr g.bytes

/-- The pins of one stored `chain::MessageKey`: its four `Vec<u8>` headers. -/
structure MessageKeyGhost where
  cipher : VecPin
  mac : VecPin
  iv : VecPin
  seed : VecPin

/-! ## Element predicates -/

/-- A stored skipped key `chain::MessageKey` at `a` in the `Seed` form that `into_pb` writes
(`ratchet/keys.rs:45–61`): empty `cipher_key` / `mac_key` / `iv`, the seed, the counter, each `Vec`
at its pinned `(cap, ptr)`. The seed must be **non-empty**, because `from_pb` (`:63–88`) reads a key
with an empty seed as the legacy `Keys` form, which the session model does not have (DEV-LS9). -/
def messageKeyAt (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    SepProp :=
  ⌜gk.2.seed ≠ []⌝ ∗ vecU8At A a gk.1.cipher.cap gk.1.cipher.ptr [] ∗
    vecU8At A (a + asm64% mkMacKeyOff) gk.1.mac.cap gk.1.mac.ptr [] ∗
    vecU8At A (a + asm64% mkIvOff) gk.1.iv.cap gk.1.iv.ptr [] ∗
    vecU8At A (a + asm64% mkSeedOff) gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
    ((a + asm64% mkIndexOff) ↦₃₂ gk.2.counter) ∗
    memRegion (a + asm64% (mkIndexOff + 4)) (asm% (messageKeySize - (mkIndexOff + 4)))

/-- `Option<chain::ChainKey>` at `a` (32 bytes): `None` is the niche (24 bytes unspecified, the pin
unused), `Some ck` is the 32-byte key `Vec` at its pinned `(cap, ptr)` and the index
(`ChainKey::to_pb`, `ratchet/keys.rs:155–160`). -/
def optChainKeyAt (A : RustAlloc) (pin : VecPin) (o : Option ChainKey) (a : BitVec 64) : SepProp :=
  match o with
  | none => (a ↦₆₄ optChainKeyNone) ∗ memRegion (a + asm64% vecPtrOff) (asm% (chainKeySize - vecPtrOff))
  | some ck =>
    vecU8At A a pin.cap pin.ptr (keyToBytes32 ck.key) ∗ ((a + asm64% chainKeyIndexOff) ↦₃₂ ck.index) ∗
      memRegion (a + asm64% (chainKeyIndexOff + 4)) (asm% (chainKeySize - (chainKeyIndexOff + 4)))

/-- The ghost of one receiver chain: every `Vec` it owns, exactly. -/
structure ChainGhost where
  /-- `sender_ratchet_key` (the serialized public key `0x05 ‖ key`, exactly 33 bytes). -/
  srk : VecGhost
  /-- `sender_ratchet_key_private` (empty: `add_receiver_chain` stores `vec![]`; never read here). -/
  priv : VecGhost
  /-- The `message_keys` `Vec<MessageKey>` buffer. -/
  mkCap : BitVec 64
  mkPtr : BitVec 64
  /-- The pins of the stored keys, in order. -/
  keys : List MessageKeyGhost
  /-- The `chain_key` key `Vec` (unused when the chain key is `None`). -/
  ck : VecPin

/-- A receiver chain `session_structure::Chain` at `a` (104 bytes) holding the session model's
chain `c`, with every `Vec` at its pinned place. `sender_ratchet_key` deserializes to
`c.senderRatchetKey` (`PublicKey::deserialize`, `core/src/curve.rs:84–105`); this excludes corrupt
chains, which upstream skips with a warning. The skipped keys are at most `maxMessageKeys = 2000`
(`consts.rs:9`; `store_skipped_key` keeps the bound). Their `Vec<MessageKey>` buffer has element
size 104 and alignment 8.

**Canonical stored keys**: `sender_ratchet_key` is exactly 33 bytes (the canonical
`PublicKey::serialize`, `0x05 ‖ key`) and `sender_ratchet_key_private` is empty, which is what
upstream writes (`add_receiver_chain`, `state/session.rs:342–350`). Upstream's reader accepts more
(trailing bytes after the key, any private-key bytes); such records are outside the specs. -/
def chainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
    gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗
    vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + asm64% chainPrivOff) ∗
    vecAt A (asm% messageKeySize) (asm% messageKeyAlign) (messageKeyAt A)
      (a + asm64% chainMessageKeysOff) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys) ∗
    optChainKeyAt A gc.1.ck gc.2.chainKey (a + asm64% chainChainKeyOff)

/-! ## The ratchet state -/

/-- The ghost layout of a `RatchetState`: the `receiver_chains` buffer, every `Vec` of every chain,
and the unspecified bytes after a `None` sender-chain tag. -/
structure RatchetGhost where
  chainsCap : BitVec 64
  chainsPtr : BitVec 64
  chains : List ChainGhost
  senderPad : List (BitVec 8)

/-- `G'` is `G` except possibly at chain `i`, where only the `message_keys` buffer, the key pins
and the chain-key pin may differ (the two key `Vec`s stay exact). `i = none`: `G' = G`. -/
def RatchetGhost.AgreeExcept (G G' : RatchetGhost) (i : Option Nat) : Prop :=
  G'.chainsCap = G.chainsCap ∧ G'.chainsPtr = G.chainsPtr ∧ G'.senderPad = G.senderPad ∧
    G'.chains.length = G.chains.length ∧
    ∀ j (h : j < G.chains.length) (h' : j < G'.chains.length),
      if i = some j then G'.chains[j].srk = G.chains[j].srk ∧ G'.chains[j].priv = G.chains[j].priv
      else G'.chains[j] = G.chains[j]

/-- `RatchetState` at `self` (176 bytes) holding the session model's state `st`, with ghost layout
`G`. `receiver_chains` is a `Vec<Chain>` (element 104 bytes, align 8) with capacity `G.chainsCap` at
`G.chainsPtr`. `sender_chain` and `root_key` are exact bytes, `max_forward_jumps` a `usize`, then
`previous_counter`. -/
def ratchetAt (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost) (st : RatchetState) : SepProp :=
  ⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
    st.maxForwardJumps < 2 ^ 64⌝ ∗
    vecAt A 104 8 (chainAt A) self G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
    ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
    ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
    ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4

/-! ## The result -/

/-- `Result<MessageKeyGenerator, SignalProtocolError>` at `r` (88 bytes) for the results that
`consume_message_key` returns normally: `Ok(Seed((seed, counter)))` (tag 1), `DuplicatedMessage` and
`InvalidMessage(type, "message from too far into the future")` (tag 2). Anything else is `False`:
the other errors are panics or are not produced by this method. -/
def consumeMessageKeyResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError MessageKeyGenerator → SepProp
  | .ok k =>
    (r ↦₃₂ 1#32) ∗ memRegion (r + 4#64) 4 ∗ vecU8 A (r + 8#64) k.seed ∗
      ((r + 32#64) ↦₃₂ k.counter) ∗ memRegion (r + 36#64) 52
  | .error (.duplicatedMessage i c) =>
    (r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗ ((r + 8#64) ↦₆₄ errDuplicatedMessage) ∗
      ((r + 16#64) ↦₃₂ i) ∗ ((r + 20#64) ↦₃₂ c) ∗ memRegion (r + 24#64) 64
  | .error (.invalidMessage t .tooFarInFuture) =>
    (r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗ ((r + 8#64) ↦₆₄ errInvalidMessage) ∗
      vecU8 A (r + 16#64) tooFarInFutureStr ∗ ((r + 40#64) ↦ₛ [msgTypeByte t]) ∗
      memRegion (r + 41#64) 47
  | .error _ => ⌜False⌝

end CryptoVerification.LibsignalSessionRepr
