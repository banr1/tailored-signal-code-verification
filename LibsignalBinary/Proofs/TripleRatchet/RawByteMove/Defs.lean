/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap

/-!
# Inline-Byte and Detached-Heap Decompositions for Session Structures

Decomposes `chainAt` (104 B), `optSenderChainAt` (104 B), `optTailVecAt` (48 / 32 B), and
`sessionStateAt` (344 B) into:
* a position-independent pure predicate (`ChainInline`, `OptSenderChainInline`, `OptTailVecInline`,
  `SessionInline`) on the flat inline byte list `bs`,
* the contiguous byte-slice assertion `a ↦ₛ bs` at the struct base address, and
* an address-independent detached-heap predicate (`chainHeap`, `optSenderChainHeap`,
  `optTailVecHeap`, `sessionHeap`), supporting raw register/quadword and `memcpy` struct moves.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.RawByteMove

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## 128-bit little-endian unpacking and 104-byte chunk layouts -/

/-- Unpack a 128-bit quadword into its 16 little-endian bytes (`lo` 64 bits then `hi` 64 bits,
matching `Arm64.pointsTo128`). -/
def unpack128 (v : BitVec 128) : List (BitVec 8) :=
  unpack64 (v.extractLsb' 0 64) ++ unpack64 (v.extractLsb' 64 64)

/-- 104 bytes packed as a leading 64-bit word at `+0x00` and six 128-bit quadwords at `+0x08..+0x68`. -/
def bytes104OfW6Q (w0 : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) : List (BitVec 8) :=
  unpack64 w0 ++ unpack128 q0 ++ unpack128 q1 ++ unpack128 q2 ++
    unpack128 q3 ++ unpack128 q4 ++ unpack128 q5

/-- Spatial layout of 104 bytes at `a` as `(a ↦₆₄ w0)` at `+0x00` and six `↦₁₂₈` quadwords at
`+0x08, +0x18, +0x28, +0x38, +0x48, +0x58`. -/
def chunks104W6QAt (a : BitVec 64) (w0 : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 0x8#64) ↦₁₂₈ q0) ∗ ((a + 0x18#64) ↦₁₂₈ q1) ∗
    ((a + 0x28#64) ↦₁₂₈ q2) ∗ ((a + 0x38#64) ↦₁₂₈ q3) ∗
    ((a + 0x48#64) ↦₁₂₈ q4) ∗ ((a + 0x58#64) ↦₁₂₈ q5)

/-- 96 bytes packed as six 128-bit quadwords at `+0x00..+0x60`. -/
def bytes96Of6Q (q0 q1 q2 q3 q4 q5 : BitVec 128) : List (BitVec 8) :=
  unpack128 q0 ++ unpack128 q1 ++ unpack128 q2 ++
    unpack128 q3 ++ unpack128 q4 ++ unpack128 q5

/-- Six contiguous `↦₁₂₈` quadwords (96 bytes) at `base + {0x00, 0x10, 0x20, 0x30, 0x40, 0x50}`. -/
def chunks96_6QAt (base : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) : SepProp :=
  (base ↦₁₂₈ q0) ∗ ((base + 16#64) ↦₁₂₈ q1) ∗ ((base + 32#64) ↦₁₂₈ q2) ∗
    ((base + 48#64) ↦₁₂₈ q3) ∗ ((base + 64#64) ↦₁₂₈ q4) ∗
    ((base + 80#64) ↦₁₂₈ q5)

/-- 104 bytes packed as six 128-bit quadwords at `+0x00..+0x60` and a trailing 64-bit word at `+0x60`. -/
def bytes104Of6QW (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) : List (BitVec 8) :=
  unpack128 q0 ++ unpack128 q1 ++ unpack128 q2 ++
    unpack128 q3 ++ unpack128 q4 ++ unpack128 q5 ++ unpack64 w6

/-- Spatial layout of 104 bytes at `a` as six `↦₁₂₈` quadwords at
`+0x00, +0x10, +0x20, +0x30, +0x40, +0x50` and `((a + 0x60#64) ↦₆₄ w6)`. -/
def chunks104_6QWAt (a : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    SepProp :=
  (a ↦₁₂₈ q0) ∗ ((a + 0x10#64) ↦₁₂₈ q1) ∗ ((a + 0x20#64) ↦₁₂₈ q2) ∗
    ((a + 0x30#64) ↦₁₂₈ q3) ∗ ((a + 0x40#64) ↦₁₂₈ q4) ∗
    ((a + 0x50#64) ↦₁₂₈ q5) ∗ ((a + 0x60#64) ↦₆₄ w6)

/-! ## `VecGhost` and `optChainKeyAt` inline-byte / heap building blocks -/

/-- The 24 inline header bytes `{cap, ptr, len}` of a `VecGhost`. -/
def vecGhostHeaderBytes (g : VecGhost) : List (BitVec 8) :=
  vecHeaderBytes g.cap g.ptr (BitVec.ofNat 64 g.bytes.length)

/-- The detached heap buffer of a `VecGhost` (independent of the header's address). -/
def vecGhostHeap (A : RustAlloc) (g : VecGhost) : SepProp :=
  vecU8Buf A g.cap g.ptr g.bytes

/-- Pure relation characterizing the 32 inline bytes `bs` of `optChainKeyAt A pin o a`:
* `none`: 8-byte `optChainKeyNone` niche followed by 24 unspecified padding bytes;
* `some ck`: 24-byte `Vec<u8>` header `{pin.cap, pin.ptr, 32}`, 4-byte LE `ck.index`, and 4
  unspecified padding bytes. -/
def OptChainKeyInline (pin : VecPin) : Option ChainKey → List (BitVec 8) → Prop
  | none, bs =>
    ∃ pad : List (BitVec 8), pad.length = 24 ∧ bs = unpack64 optChainKeyNone ++ pad
  | some ck, bs =>
    ∃ pad : List (BitVec 8), pad.length = 4 ∧
      bs = vecHeaderBytes pin.cap pin.ptr 32#64 ++ unpack32 ck.index ++ pad

/-- Detached heap buffer of `optChainKeyAt A pin o a` (independent of `a`). -/
def optChainKeyHeap (A : RustAlloc) (pin : VecPin) : Option ChainKey → SepProp
  | none => emp
  | some ck => vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)

/-! ## `chainAt` (104 bytes): `ChainInline` and `chainHeap` -/

/-- Pure well-formedness invariant shared by `chainAt` and `optSenderChainAt` (`Some`). -/
def ProtoChainPure (gc : ChainGhost × ReceiverChain) : Prop :=
  PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
    gc.1.srk.bytes.length = 33

/-- Pure well-formedness invariant of `chainAt A gc a`. -/
def ChainPure (gc : ChainGhost × ReceiverChain) : Prop :=
  PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
    gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []

/-- Common `session_structure::Chain` layout (without `gc.1.priv.bytes = []`), shared by
`chainAt` and `optSenderChainAt` (`Some`). -/
def protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜ProtoChainPure gc⌝ ∗
    vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
    vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys) ∗
    optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

/-- The deterministic first 72 inline bytes of `chainAt A gc a`:
* `+0x00..+0x18` (24 B): `sender_ratchet_key` header,
* `+0x18..+0x30` (24 B): `sender_ratchet_key_private` header,
* `+0x30..+0x48` (24 B): `message_keys` `Vec<MessageKey>` header. -/
def chainPrefixBytes (gc : ChainGhost × ReceiverChain) : List (BitVec 8) :=
  vecGhostHeaderBytes gc.1.srk ++
    vecGhostHeaderBytes gc.1.priv ++
    vecHeaderBytes gc.1.mkCap gc.1.mkPtr
      (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length)

/-- Position-independent pure predicate on the 104 inline bytes `bs` of `chainAt A gc a`:
the 72-byte `chainPrefixBytes gc` followed by 32 bytes satisfying `OptChainKeyInline`. -/
def ChainInline (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8)) : Prop :=
  ∃ ckBs : List (BitVec 8),
    ckBs.length = 32 ∧
    OptChainKeyInline gc.1.ck gc.2.chainKey ckBs ∧
    bs = chainPrefixBytes gc ++ ckBs

/-- Position-independent detached heap of `protoChainAt A gc a`. -/
def protoChainHeap (A : RustAlloc) (gc : ChainGhost × ReceiverChain) : SepProp :=
  ⌜ProtoChainPure gc⌝ ∗
    vecGhostHeap A gc.1.srk ∗
    vecGhostHeap A gc.1.priv ∗
    vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys) ∗
    optChainKeyHeap A gc.1.ck gc.2.chainKey

/-- Address-independent detached heap of `chainAt A gc a`: `ChainPure gc`, the two key `Vec<u8>`
buffers, the `Vec<MessageKey>` buffer (`vecBuf`), and the optional `chain_key` buffer. -/
def chainHeap (A : RustAlloc) (gc : ChainGhost × ReceiverChain) : SepProp :=
  ⌜ChainPure gc⌝ ∗
    vecGhostHeap A gc.1.srk ∗
    vecGhostHeap A gc.1.priv ∗
    vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys) ∗
    optChainKeyHeap A gc.1.ck gc.2.chainKey

/-! ## `optSenderChainAt` (104 bytes): `OptSenderChainInline` and `optSenderChainHeap` -/

/-- View a `SenderChainGhost` as a `ChainGhost` with `keys = []`. -/
abbrev _root_.CryptoVerification.LibsignalTripleRatchetRepr.SenderChainGhost.toChainGhost
    (g : SenderChainGhost) : ChainGhost :=
  ⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩

abbrev toChainGhost (g : SenderChainGhost) : ChainGhost := g.toChainGhost

/-- View a `SenderChain` as a `ReceiverChain` with `chainKey = some sc.chainKey` and
`messageKeys = []`. -/
abbrev _root_.CryptoGames.LibsignalSession.SenderChain.toReceiverChain
    (sc : SenderChain) : ReceiverChain :=
  ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩

abbrev toReceiverChain (sc : SenderChain) : ReceiverChain := sc.toReceiverChain

/-- Extra pure private-key clamping invariant carried by `optSenderChainAt` in the `Some` case
beyond `protoChainAt`. -/
def SenderChainPrivPure (g : SenderChainGhost) (sc : SenderChain) : Prop :=
  g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes

/-- Position-independent pure predicate on the 104 inline bytes `bs` of
`optSenderChainAt A a g sc`:
* `none, none`: 8-byte `noneCap` (`-1`) niche followed by 96 unspecified bytes;
* `some sg, some s`: `ChainInline (sg.toChainGhost, s.toReceiverChain) bs`;
* mismatched `Option` tags: `False`. -/
def OptSenderChainInline : Option SenderChainGhost → Option SenderChain → List (BitVec 8) → Prop
  | none, none, bs =>
    ∃ pad : List (BitVec 8), pad.length = 96 ∧ bs = unpack64 noneCap ++ pad
  | some g, some sc, bs =>
    ChainInline (g.toChainGhost, sc.toReceiverChain) bs
  | _, _, _ => False

/-- Address-independent detached heap of `optSenderChainAt A a g sc`. -/
def optSenderChainHeap (A : RustAlloc) :
    Option SenderChainGhost → Option SenderChain → SepProp
  | none, none => emp
  | some g, some sc =>
    ⌜SenderChainPrivPure g sc⌝ ∗ protoChainHeap A (g.toChainGhost, sc.toReceiverChain)
  | _, _ => ⌜False⌝

/-! ## `optTailVecAt` and `sessionStateAt` (344 bytes): `SessionInline` and `sessionHeap` -/

/-- Position-independent pure predicate on the `size` inline bytes `bs` of
`optTailVecAt A size a o`:
* `none`: 8-byte `noneCap` niche followed by `size - 8` unspecified bytes;
* `some g`: 24-byte `VecGhost` header followed by `g.tail` of length `size - 24`. -/
def OptTailVecInline (size : Nat) : Option TailVecGhost → List (BitVec 8) → Prop
  | none, bs =>
    ∃ pad : List (BitVec 8), pad.length = size - 8 ∧ bs = unpack64 noneCap ++ pad
  | some g, bs =>
    g.tail.length = size - 24 ∧ bs = vecGhostHeaderBytes g.vec ++ g.tail

/-- Address-independent detached heap of `optTailVecAt A size a o`. -/
def optTailVecHeap (A : RustAlloc) : Option TailVecGhost → SepProp
  | none => emp
  | some g => vecGhostHeap A g.vec

/-- Pure well-formedness invariant of `sessionStateAt A ss G st`. -/
def SessionPure (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)

/-- The deterministic first 144 (`0x90`) inline bytes of `sessionStateAt A ss G st`
(`+0x00..+0x90`): the six 24-byte `Vec` headers (`localIk`, `remoteIk`, `root`, `receiver_chains`,
`alice`, `pq`). -/
def sessionPrefixBytes (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    List (BitVec 8) :=
  vecGhostHeaderBytes G.localIk ++
    vecGhostHeaderBytes G.remoteIk ++
    vecHeaderBytes G.root.cap G.root.ptr 32#64 ++
    vecHeaderBytes G.chainsCap G.chainsPtr
      (BitVec.ofNat 64 (G.chains.zip st.receiverChains).length) ++
    vecGhostHeaderBytes G.alice ++
    vecHeaderBytes G.pq.cap G.pq.ptr (BitVec.ofNat 64 st.pqRatchetState.length)

/-- The deterministic last 16 (`0x10`) inline bytes of `sessionStateAt A ss G st`
(`+0x148..+0x158`): `session_version` (4 B), `previous_counter` (4 B), and `regIds` (8 B). -/
def sessionSuffixBytes (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    List (BitVec 8) :=
  unpack32 st.sessionVersion ++ unpack32 st.previousCounter ++ G.regIds

/-- Position-independent pure predicate on the 344 inline bytes `bs` of
`sessionStateAt A ss G st`:
* `+0x00..+0x90` (144 B): `sessionPrefixBytes G st`,
* `+0x90..+0xf8` (104 B): `scBs` satisfying `OptSenderChainInline G.sender st.senderChain`,
* `+0xf8..+0x128` (48 B): `pendBs` satisfying `OptTailVecInline 48 G.pending`,
* `+0x128..+0x148` (32 B): `kybBs` satisfying `OptTailVecInline 32 G.kyber`,
* `+0x148..+0x158` (16 B): `sessionSuffixBytes G st` (with `G.regIds.length = 8`). -/
def SessionInline (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (bs : List (BitVec 8)) : Prop :=
  G.regIds.length = 8 ∧
    ∃ scBs pendBs kybBs : List (BitVec 8),
      scBs.length = 104 ∧ OptSenderChainInline G.sender st.senderChain scBs ∧
      pendBs.length = 48 ∧ OptTailVecInline 48 G.pending pendBs ∧
      kybBs.length = 32 ∧ OptTailVecInline 32 G.kyber kybBs ∧
      bs = sessionPrefixBytes G st ++ scBs ++ pendBs ++ kybBs ++ sessionSuffixBytes G st

/-- Address-independent detached heap of `sessionStateAt A ss G st`: `SessionPure G st` together
with all owned heap buffers (`localIk`, `remoteIk`, `root`, `receiver_chains`, `alice`, `pq`,
`sender_chain`, `pending_pre_key`, and `pending_kyber_pre_key`). -/
def sessionHeap (A : RustAlloc) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜SessionPure G st⌝ ∗
    vecGhostHeap A G.localIk ∗
    vecGhostHeap A G.remoteIk ∗
    vecU8Buf A G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    vecGhostHeap A G.alice ∗
    vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainHeap A G.sender st.senderChain ∗
    optTailVecHeap A G.pending ∗
    optTailVecHeap A G.kyber

/-! ## Chunk, decomposition, and move statement abbreviations -/

/-- `chunks104W6QAt a w0 q0..q5` equals `a ↦ₛ bytes104OfW6Q w0 q0..q5`. -/
def Chunks104W6QStmt (a : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) : Prop :=
  chunks104W6QAt a w0 q0 q1 q2 q3 q4 q5 = (a ↦ₛ bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5)

/-- `chunks104_6QWAt a q0..q5 w6` equals `a ↦ₛ bytes104Of6QW q0..q5 w6`. -/
def Chunks104_6QWStmt (a : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128)
    (w6 : BitVec 64) : Prop :=
  chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 = (a ↦ₛ bytes104Of6QW q0 q1 q2 q3 q4 q5 w6)

/-- `chunks96_6QAt b q0..q5` equals `b ↦ₛ bytes96Of6Q q0..q5`. -/
def Chunks96_6QStmt (b : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) : Prop :=
  chunks96_6QAt b q0 q1 q2 q3 q4 q5 = (b ↦ₛ bytes96Of6Q q0 q1 q2 q3 q4 q5)

/-- Every 104-byte list decomposes as `bytes104OfW6Q w0 q0..q5`. -/
def Split104W6QStmt (bs : List (BitVec 8)) : Prop :=
  bs.length = 104 →
    ∃ (w0 : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128),
      bs = bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5

/-- Every 104-byte list decomposes as `bytes104Of6QW q0..q5 w6`. -/
def Split104_6QWStmt (bs : List (BitVec 8)) : Prop :=
  bs.length = 104 →
    ∃ (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64),
      bs = bytes104Of6QW q0 q1 q2 q3 q4 q5 w6

/-- Every 96-byte list decomposes as `bytes96Of6Q q0..q5`. -/
def Split96_6QStmt (bs : List (BitVec 8)) : Prop :=
  bs.length = 96 →
    ∃ (q0 q1 q2 q3 q4 q5 : BitVec 128),
      bs = bytes96Of6Q q0 q1 q2 q3 q4 q5

/-- `protoChainAt` decomposes into 104 inline bytes (`ChainInline`) and `protoChainHeap`. -/
def ProtoChainAtDecompStmt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : Prop :=
  protoChainAt A gc a =
    ∃∗ bs : List (BitVec 8),
      ⌜bs.length = 104 ∧ ChainInline gc bs⌝ ∗ (a ↦ₛ bs) ∗ protoChainHeap A gc

/-- `chainAt` decomposes into 104 inline bytes (`ChainInline`) and `chainHeap`. -/
def ChainAtDecompStmt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : Prop :=
  chainAt A gc a =
    ∃∗ bs : List (BitVec 8),
      ⌜bs.length = 104 ∧ ChainInline gc bs⌝ ∗ (a ↦ₛ bs) ∗ chainHeap A gc

/-- `optSenderChainAt` in the `some` case reduces to `protoChainAt` plus `SenderChainPrivPure`. -/
def OptSenderChainSomeBridgeStmt (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) : Prop :=
  optSenderChainAt A a (some g) (some sc) =
    ⌜SenderChainPrivPure g sc⌝ ∗ protoChainAt A (g.toChainGhost, sc.toReceiverChain) a

/-- `optSenderChainAt` decomposes into 104 inline bytes (`OptSenderChainInline`) and `optSenderChainHeap`. -/
def OptSenderChainAtDecompStmt (A : RustAlloc) (a : BitVec 64)
    (g : Option SenderChainGhost) (sc : Option SenderChain) : Prop :=
  optSenderChainAt A a g sc =
    ∃∗ bs : List (BitVec 8),
      ⌜bs.length = 104 ∧ OptSenderChainInline g sc bs⌝ ∗ (a ↦ₛ bs) ∗ optSenderChainHeap A g sc

/-- `sessionStateAt` decomposes into 344 inline bytes (`SessionInline`) and `sessionHeap`. -/
def SessionStateAtDecompStmt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : Prop :=
  sessionStateAt A ss G st =
    ∃∗ bs : List (BitVec 8),
      ⌜bs.length = 344 ∧ SessionInline G st bs⌝ ∗ (ss ↦ₛ bs) ∗ sessionHeap A G st

/-- Transferring `sessionHeap A G st` to `dst ↦ₛ bs` (`SessionInline G st bs`) yields `sessionStateAt A dst G st`. -/
def SessionStateMoveStmt (A : RustAlloc) (src dst : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) (bs : List (BitVec 8)) : Prop :=
  SessionInline G st bs →
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ sessionHeap A G st) ⊢
      sessionStateAt A dst G st ∗ (src ↦ₛ bs)

end CryptoVerification.LibsignalTripleRatchet.RawByteMove
