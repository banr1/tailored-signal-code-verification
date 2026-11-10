/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Layout
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
import ProofLib.BV.WidthNorm
import ProofLib.VCGen

/-!
# Representation Predicates, Pure `encodedLen` Models, and Specs for Core SPQR V1 Protobuf Structs

Separation-logic representation predicates (`SepProp`), pure `prost` 0.14.4 `encoded_len` models,
equivalence bridges to `LibsignalSpqrV1.Proto`, and Hoare specifications for `ChainParams`,
`EpochDirection`, `Epoch`, `Chain`, `Authenticator`, and `VersionNegotiation`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1

/-- Alias for `CryptoVerification.RustHeap.vecU8` (`∃∗ cap ptr, vecU8At A v cap ptr bs`). -/
abbrev rustBytesVecAt := vecU8

/-! ## Symbol Names in `libsignalSessionCode` -/

/-- `<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#1]`
    (`0x38abc`, 121 instructions). -/
abbrev epochEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#1]"

/-- `<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#2]`
    (`0x664fc`, 121 instructions). -/
abbrev epochEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#2]"

/-- `<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#1]`
    (`0x39698`, 126 instructions). -/
abbrev chainEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#1]"

/-- `<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#2]`
    (`0x68790`, 126 instructions). -/
abbrev chainEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#2]"

/-! ## Stack Budgets -/

/-- Stack budget for `<Epoch as Message>::encoded_len` (`0x38abc` and `0x664fc`):
    `0x10` bytes (`+0x000: stp x29, x30, [sp, #-0x10]!`, leaf on non-overflow path). -/
abbrev epochEncodedLenStack : Nat := 0x10

/-- Own stack frame of `<Chain as Message>::encoded_len` (`0x39698` and `0x68790`):
    `0x50` bytes (`+0x000: stp x29, x30, [sp, #-0x50]!`). -/
abbrev chainEncodedLenFrame : Nat := 0x50

/-- Total stack budget for `<Chain as Message>::encoded_len` (`0x39698` and `0x68790`):
    own `0x50`-byte frame plus `0x10` bytes for callee `<Epoch as Message>::encoded_len` (`0x60` bytes). -/
abbrev chainEncodedLenStack : Nat := chainEncodedLenFrame + epochEncodedLenStack

/-! ## Varint Length Formula (`prost::encoding::encoded_len_varint`) -/

/-- Byte length `1..10` of the LEB128 varint encoding of `v : BitVec 64`, as computed by
    `prost::encoding::encoded_len_varint` (`(((clz(v | 1) ^ 0x3f) * 9 + 73) >> 6)`). -/
def varintLen (v : BitVec 64) : Nat :=
  (((v ||| 1#64).clz ^^^ 0x3f#64).toNat * 9 + 73) / 64

/-! ## 1. `ChainParamsPB` (`8` bytes) and `Option<ChainParamsPB>` (`12` bytes) -/

/-- `spqr::proto::pq_ratchet::ChainParams` at `a` (`8` bytes, align `4`):
    * `a + 0x00`: `max_jump: u32` (tag 1)
    * `a + 0x04`: `max_ooo_keys: u32` (tag 2) -/
def chainParamsPBAt (a : BitVec 64) (p : ChainParamsPB) : SepProp :=
  (a ↦₃₂ p.maxJump) ∗ ((a + 4#64) ↦₃₂ p.maxOooKeys)

/-- `Option<spqr::proto::pq_ratchet::ChainParams>` at `a` (`12` bytes, align `4`):
    * `none`: `(a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8`
    * `some p`: `(a ↦₃₂ 1#32) ∗ chainParamsPBAt (a + 4#64) p` -/
def optChainParamsPBAt (a : BitVec 64) : Option ChainParamsPB → SepProp
  | none => (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8
  | some p => (a ↦₃₂ 1#32) ∗ chainParamsPBAt (a + 4#64) p

/-! ## 2. `EpochDirectionPB` (`56` bytes) and `Option<EpochDirectionPB>` (`56` bytes) -/

/-- Ghost `(cap, ptr)` pins for the two `Vec<u8>` fields of an `EpochDirectionPB` (`56` bytes). -/
structure EpochDirectionPBGhost where
  /-- Pin for `next: Vec<u8>` at `+0x00` (tag 2). -/
  next : VecPin
  /-- Pin for `prev: Vec<u8>` at `+0x18` (tag 3). -/
  prev : VecPin

/-- Pinned `spqr::proto::pq_ratchet::chain::epoch::EpochDirection` at `a` (`56` bytes = `0x38`, align `8`):
    * `a + 0x00`: `next: Vec<u8>` (tag 2, 24B)
    * `a + 0x18`: `prev: Vec<u8>` (tag 3, 24B)
    * `a + 0x30`: `ctr: u32` (tag 1, 4B)
    * `a + 0x34`: 4 bytes trailing padding (`memRegion (a + 0x34#64) 4`) -/
def epochDirectionPBPinnedAt (A : RustAlloc) (g : EpochDirectionPBGhost) (a : BitVec 64)
    (d : EpochDirectionPB) : SepProp :=
  vecU8At A a g.next.cap g.next.ptr d.next ∗
    vecU8At A (a + 0x18#64) g.prev.cap g.prev.ptr d.prev ∗
    ((a + 0x30#64) ↦₃₂ d.ctr) ∗
    memRegion (a + 0x34#64) 4

/-- Unpinned `spqr::proto::pq_ratchet::chain::epoch::EpochDirection` at `a` (`56` bytes = `0x38`, align `8`),
    using `rustBytesVecAt` (`∃∗ cap ptr, vecU8At ...`). -/
def epochDirectionPBAt (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) : SepProp :=
  rustBytesVecAt A a d.next ∗
    rustBytesVecAt A (a + 0x18#64) d.prev ∗
    ((a + 0x30#64) ↦₃₂ d.ctr) ∗
    memRegion (a + 0x34#64) 4

/-- Pinned `Option<EpochDirection>` at `a` (`56` bytes = `0x38`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48` (`next.cap = 0xFFFFFFFFFFFFFFFF#64` niche)
    * `some d`: `epochDirectionPBPinnedAt A g a d` -/
def optEpochDirectionPBPinnedAt (A : RustAlloc) (g : EpochDirectionPBGhost) (a : BitVec 64) :
    Option EpochDirectionPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48
  | some d => epochDirectionPBPinnedAt A g a d

/-- Unpinned `Option<EpochDirection>` at `a` (`56` bytes = `0x38`, align `8`). -/
def optEpochDirectionPBAt (A : RustAlloc) (a : BitVec 64) : Option EpochDirectionPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48
  | some d => epochDirectionPBAt A a d

/-! ## 3. `ChainEpochPB` (`112` bytes) -/

/-- Ghost `(cap, ptr)` pins for the `send` and `recv` `Option<EpochDirection>` fields of a `ChainEpochPB`. -/
structure ChainEpochPBGhost where
  /-- Pins for `send: Option<EpochDirection>` at `+0x00` (tag 1, unused when `none`). -/
  send : EpochDirectionPBGhost
  /-- Pins for `recv: Option<EpochDirection>` at `+0x38` (tag 2, unused when `none`). -/
  recv : EpochDirectionPBGhost

/-- Pinned `spqr::proto::pq_ratchet::chain::Epoch` at `a` (`112` bytes = `0x70`, align `8`):
    * `a + 0x00`: `send: Option<EpochDirection>` (tag 1, 56B)
    * `a + 0x38`: `recv: Option<EpochDirection>` (tag 2, 56B) -/
def chainEpochPBPinnedAt (A : RustAlloc) (g : ChainEpochPBGhost) (a : BitVec 64)
    (ep : ChainEpochPB) : SepProp :=
  optEpochDirectionPBPinnedAt A g.send a ep.send ∗
    optEpochDirectionPBPinnedAt A g.recv (a + 0x38#64) ep.recv

/-- Unpinned `spqr::proto::pq_ratchet::chain::Epoch` at `a` (`112` bytes = `0x70`, align `8`). -/
def chainEpochPBAt (A : RustAlloc) (a : BitVec 64) (ep : ChainEpochPB) : SepProp :=
  optEpochDirectionPBAt A a ep.send ∗
    optEpochDirectionPBAt A (a + 0x38#64) ep.recv

/-! ## 4. `ChainPB` (`80` bytes) and `Option<ChainPB>` (`80` bytes) -/

/-- Contiguous array of `ChainEpochPB` elements at `base` with stride `112` (`0x70`) bytes. -/
def chainEpochPBArrayAt (A : RustAlloc) : BitVec 64 → List ChainEpochPB → SepProp :=
  arrayAt (fun ep addr => chainEpochPBAt A addr ep) chainEpochPBSize

/-- Pinned `Vec<ChainEpochPB>` at `v` (24-byte header `{cap, ptr, len}`, stride `112`, align `8`). -/
def chainLinksVecPinnedAt (A : RustAlloc) (pin : VecPin) (v : BitVec 64)
    (links : List ChainEpochPB) : SepProp :=
  vecAt A chainEpochPBSize 8 (fun ep addr => chainEpochPBAt A addr ep) v pin.cap pin.ptr links

/-- Unpinned `Vec<ChainEpochPB>` at `v` (24-byte header `{cap, ptr, len}`, stride `112`, align `8`). -/
def chainLinksVecAt (A : RustAlloc) (v : BitVec 64) (links : List ChainEpochPB) : SepProp :=
  vecOf A chainEpochPBSize 8 (fun ep addr => chainEpochPBAt A addr ep) v links

/-- Ghost `(cap, ptr)` pins for the top-level `Vec` fields of a `ChainPB` (`80` bytes). -/
structure ChainPBGhost where
  /-- Pin for `links: Vec<Epoch>` at `+0x00` (tag 3). -/
  links : VecPin
  /-- Pin for `next_root: Vec<u8>` at `+0x18` (tag 4). -/
  nextRoot : VecPin

/-- Pinned `spqr::proto::pq_ratchet::Chain` at `a` (`80` bytes = `0x50`, align `8`):
    * `a + 0x00`: `links: Vec<Epoch>` (tag 3, 24B, element stride `112`, align `8`)
    * `a + 0x18`: `next_root: Vec<u8>` (tag 4, 24B)
    * `a + 0x30`: `current_epoch: u64` (tag 2, 8B)
    * `a + 0x38`: `send_epoch: u64` (tag 5, 8B)
    * `a + 0x40`: `params: Option<ChainParams>` (tag 6, 12B)
    * `a + 0x4c`: `direction: i32` (tag 1, 4B) -/
def chainPBPinnedAt (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (ch : ChainPB) : SepProp :=
  chainLinksVecPinnedAt A g.links a ch.links ∗
    vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
    ((a + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
    ((a + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
    optChainParamsPBAt (a + 0x40#64) ch.params ∗
    ((a + 0x4c#64) ↦₃₂ ch.direction)

/-- Unpinned `spqr::proto::pq_ratchet::Chain` at `a` (`80` bytes = `0x50`, align `8`). -/
def chainPBAt (A : RustAlloc) (a : BitVec 64) (ch : ChainPB) : SepProp :=
  chainLinksVecAt A a ch.links ∗
    rustBytesVecAt A (a + 0x18#64) ch.nextRoot ∗
    ((a + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
    ((a + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
    optChainParamsPBAt (a + 0x40#64) ch.params ∗
    ((a + 0x4c#64) ↦₃₂ ch.direction)

/-- Pinned `Option<spqr::proto::pq_ratchet::Chain>` at `a` (`80` bytes = `0x50`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72` (`links.cap = 0xFFFFFFFFFFFFFFFF#64` niche)
    * `some ch`: `chainPBPinnedAt A g a ch` -/
def optChainPBPinnedAt (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) :
    Option ChainPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some ch => chainPBPinnedAt A g a ch

/-- Unpinned `Option<spqr::proto::pq_ratchet::Chain>` at `a` (`80` bytes = `0x50`, align `8`). -/
def optChainPBAt (A : RustAlloc) (a : BitVec 64) : Option ChainPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some ch => chainPBAt A a ch

/-! ## 5. `AuthenticatorPB` (`48` bytes) -/

/-- Ghost `(cap, ptr)` pins for the two `Vec<u8>` fields of an `AuthenticatorPB` (`48` bytes). -/
structure AuthenticatorPBGhost where
  /-- Pin for `root_key: Vec<u8>` at `+0x00` (tag 1). -/
  rootKey : VecPin
  /-- Pin for `mac_key: Vec<u8>` at `+0x18` (tag 2). -/
  macKey : VecPin

/-- Pinned `spqr::proto::pq_ratchet::Authenticator` at `a` (`48` bytes = `0x30`, align `8`):
    * `a + 0x00`: `root_key: Vec<u8>` (tag 1, 24B)
    * `a + 0x18`: `mac_key: Vec<u8>` (tag 2, 24B) -/
def authenticatorPBPinnedAt (A : RustAlloc) (g : AuthenticatorPBGhost) (a : BitVec 64)
    (auth : AuthenticatorPB) : SepProp :=
  vecU8At A a g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
    vecU8At A (a + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey

/-- Unpinned `spqr::proto::pq_ratchet::Authenticator` at `a` (`48` bytes = `0x30`, align `8`). -/
def authenticatorPBAt (A : RustAlloc) (a : BitVec 64) (auth : AuthenticatorPB) : SepProp :=
  rustBytesVecAt A a auth.rootKey ∗
    rustBytesVecAt A (a + 0x18#64) auth.macKey

/-! ## 6. `VersionNegotiationPB` (`48` bytes) and `Option<VersionNegotiationPB>` (`48` bytes) -/

/-- Ghost `(cap, ptr)` pin for `auth_key: Vec<u8>` of a `VersionNegotiationPB` (`48` bytes). -/
structure VersionNegotiationPBGhost where
  /-- Pin for `auth_key: Vec<u8>` at `+0x00` (tag 1). -/
  authKey : VecPin

/-- Pinned `spqr::proto::pq_ratchet::pq_ratchet_state::VersionNegotiation` at `a` (`48` bytes = `0x30`, align `8`):
    * `a + 0x00`: `auth_key: Vec<u8>` (tag 1, 24B)
    * `a + 0x18`: `chain_params: Option<ChainParams>` (tag 4, 12B)
    * `a + 0x24`: `direction: i32` (tag 2, 4B)
    * `a + 0x28`: `min_version: i32` (tag 3, 4B)
    * `a + 0x2c`: 4 bytes trailing padding (`memRegion (a + 0x2c#64) 4`) -/
def versionNegotiationPBPinnedAt (A : RustAlloc) (g : VersionNegotiationPBGhost) (a : BitVec 64)
    (vn : VersionNegotiationPB) : SepProp :=
  vecU8At A a g.authKey.cap g.authKey.ptr vn.authKey ∗
    optChainParamsPBAt (a + 0x18#64) vn.chainParams ∗
    ((a + 0x24#64) ↦₃₂ vn.direction) ∗
    ((a + 0x28#64) ↦₃₂ vn.minVersion) ∗
    memRegion (a + 0x2c#64) 4

/-- Unpinned `spqr::proto::pq_ratchet::pq_ratchet_state::VersionNegotiation` at `a` (`48` bytes = `0x30`, align `8`). -/
def versionNegotiationPBAt (A : RustAlloc) (a : BitVec 64) (vn : VersionNegotiationPB) : SepProp :=
  rustBytesVecAt A a vn.authKey ∗
    optChainParamsPBAt (a + 0x18#64) vn.chainParams ∗
    ((a + 0x24#64) ↦₃₂ vn.direction) ∗
    ((a + 0x28#64) ↦₃₂ vn.minVersion) ∗
    memRegion (a + 0x2c#64) 4

/-- Pinned `Option<VersionNegotiation>` at `a` (`48` bytes = `0x30`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40` (`auth_key.cap = 0xFFFFFFFFFFFFFFFF#64` niche)
    * `some vn`: `versionNegotiationPBPinnedAt A g a vn` -/
def optVersionNegotiationPBPinnedAt (A : RustAlloc) (g : VersionNegotiationPBGhost) (a : BitVec 64) :
    Option VersionNegotiationPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some vn => versionNegotiationPBPinnedAt A g a vn

/-- Unpinned `Option<VersionNegotiation>` at `a` (`48` bytes = `0x30`, align `8`). -/
def optVersionNegotiationPBAt (A : RustAlloc) (a : BitVec 64) : Option VersionNegotiationPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some vn => versionNegotiationPBAt A a vn

/-! ## Pure `encodedLen` Models (`prost` 0.14.4 Proto3 `Message::encoded_len`) -/

/-- Proto3 encoded length of a `uint32` field with a 1-byte tag (`tag ∈ 1..15`):
    `0` when `v = 0#32`, else `1 + varintLen (v.zeroExtend 64)`. -/
def u32VarintFieldEncodedLen (v : BitVec 32) : Nat :=
  if v = 0#32 then 0 else 1 + varintLen (v.zeroExtend 64)

/-- Proto3 encoded length of a `uint64` field with a 1-byte tag (`tag ∈ 1..15`):
    `0` when `v = 0#64`, else `1 + varintLen v`. -/
def u64VarintFieldEncodedLen (v : BitVec 64) : Nat :=
  if v = 0#64 then 0 else 1 + varintLen v

/-- Proto3 encoded length of an `int32` or `enum` field with a 1-byte tag (`tag ∈ 1..15`),
    matching `prost::encoding::int32::encoded_len` (`value as i64 as u64`, i.e. `ldrsw`):
    `0` when `v = 0#32`, else `1 + varintLen (v.signExtend 64)`. -/
def i32VarintFieldEncodedLen (v : BitVec 32) : Nat :=
  if v = 0#32 then 0 else 1 + varintLen (v.signExtend 64)

/-- Proto3 encoded length of a `bytes` (`Vec<u8>`) field with a 1-byte tag (`tag ∈ 1..15`):
    `0` when `bs` is empty, else `1 + varintLen (BitVec.ofNat 64 bs.length) + bs.length`. -/
def bytesFieldEncodedLen (bs : List (BitVec 8)) : Nat :=
  if bs.isEmpty then 0 else 1 + varintLen (BitVec.ofNat 64 bs.length) + bs.length

/-- Encoded length of `spqr::proto::pq_ratchet::chain::epoch::EpochDirection`:
    tag 1 `ctr: u32` + tag 2 `next: Vec<u8>` + tag 3 `prev: Vec<u8>`. -/
def epochDirectionPBEncodedLen (d : EpochDirectionPB) : Nat :=
  u32VarintFieldEncodedLen d.ctr +
    bytesFieldEncodedLen d.next +
    bytesFieldEncodedLen d.prev

/-- Encoded length of an optional nested `EpochDirection` message field with a 1-byte tag:
    `0` when `none`, else `1 + varintLen (BitVec.ofNat 64 inner) + inner` where
    `inner = epochDirectionPBEncodedLen d`. -/
def optEpochDirectionPBFieldEncodedLen : Option EpochDirectionPB → Nat
  | none => 0
  | some d =>
    let inner := epochDirectionPBEncodedLen d
    1 + varintLen (BitVec.ofNat 64 inner) + inner

/-- Encoded length of `spqr::proto::pq_ratchet::chain::Epoch`
    (`<Epoch as prost::message::Message>::encoded_len`):
    tag 1 `send: Option<EpochDirection>` + tag 2 `recv: Option<EpochDirection>`. -/
def chainEpochPBEncodedLen (ep : ChainEpochPB) : Nat :=
  optEpochDirectionPBFieldEncodedLen ep.send +
    optEpochDirectionPBFieldEncodedLen ep.recv

/-- Length-delimited payload size (`varintLen len + len`, excluding the 1-byte field tag) of a
    single `Epoch` element inside `Chain.links` (`Chain::encoded_len+0x080..+0x094`). -/
def chainEpochPBBodyEncodedLen (ep : ChainEpochPB) : Nat :=
  let inner := chainEpochPBEncodedLen ep
  varintLen (BitVec.ofNat 64 inner) + inner

/-- Sum of `chainEpochPBBodyEncodedLen` across a list of `Epoch` elements
    (`prost::encoding::message::encoded_len_repeated` loop accumulator `x24` in
    `Chain::encoded_len+0x070..+0x0ac`). -/
def chainLinksBodiesEncodedLen (links : List ChainEpochPB) : Nat :=
  links.foldl (fun acc ep => acc + chainEpochPBBodyEncodedLen ep) 0

/-- Total encoded length of `links: Vec<Epoch>` (tag 3, 1-byte tag per element):
    `chainLinksBodiesEncodedLen links + links.length` (`Chain::encoded_len+0x0b0`). -/
def chainLinksFieldEncodedLen (links : List ChainEpochPB) : Nat :=
  chainLinksBodiesEncodedLen links + links.length

/-- Encoded length of `spqr::proto::pq_ratchet::ChainParams`:
    tag 1 `max_jump: u32` + tag 2 `max_ooo_keys: u32`. -/
def chainParamsPBEncodedLen (p : ChainParamsPB) : Nat :=
  u32VarintFieldEncodedLen p.maxJump + u32VarintFieldEncodedLen p.maxOooKeys

/-- Encoded length of `params: Option<ChainParams>` (tag 6, 1-byte tag):
    `0` when `none`, else `1 + varintLen (BitVec.ofNat 64 inner) + inner` where
    `inner = chainParamsPBEncodedLen p`. -/
def optChainParamsPBFieldEncodedLen : Option ChainParamsPB → Nat
  | none => 0
  | some p =>
    let inner := chainParamsPBEncodedLen p
    1 + varintLen (BitVec.ofNat 64 inner) + inner

/-- Encoded length of `spqr::proto::pq_ratchet::Chain`
    (`<Chain as prost::message::Message>::encoded_len`):
    tag 1 `direction: i32` + tag 2 `current_epoch: u64` + tag 3 `links: Vec<Epoch>` +
    tag 4 `next_root: Vec<u8>` + tag 5 `send_epoch: u64` + tag 6 `params: Option<ChainParams>`. -/
def chainPBEncodedLen (ch : ChainPB) : Nat :=
  i32VarintFieldEncodedLen ch.direction +
    u64VarintFieldEncodedLen ch.currentEpoch +
    chainLinksFieldEncodedLen ch.links +
    bytesFieldEncodedLen ch.nextRoot +
    u64VarintFieldEncodedLen ch.sendEpoch +
    optChainParamsPBFieldEncodedLen ch.params

/-- Encoded length of `spqr::proto::pq_ratchet::Authenticator`:
    tag 1 `root_key: Vec<u8>` + tag 2 `mac_key: Vec<u8>`. -/
def authenticatorPBEncodedLen (auth : AuthenticatorPB) : Nat :=
  bytesFieldEncodedLen auth.rootKey + bytesFieldEncodedLen auth.macKey

/-- Encoded length of `spqr::proto::pq_ratchet::pq_ratchet_state::VersionNegotiation`:
    tag 1 `auth_key: Vec<u8>` + tag 2 `direction: i32` + tag 3 `min_version: i32` +
    tag 4 `chain_params: Option<ChainParams>`. -/
def versionNegotiationPBEncodedLen (vn : VersionNegotiationPB) : Nat :=
  bytesFieldEncodedLen vn.authKey +
    i32VarintFieldEncodedLen vn.direction +
    i32VarintFieldEncodedLen vn.minVersion +
    optChainParamsPBFieldEncodedLen vn.chainParams

/-! ## Non-Overflow Predicates (`usize` Bounds) -/

/-- Size bound on a `ChainEpochPB` for `<Epoch as Message>::encoded_len`:
    the total encoded length fits in a 64-bit `usize` (`< 2 ^ 64`). -/
def EpochEncodedLenFits (ep : ChainEpochPB) : Prop :=
  chainEpochPBEncodedLen ep < 2 ^ 64

/-- Size bound on a `ChainPB` for `<Chain as Message>::encoded_len`:
    the total encoded length fits in a 64-bit `usize` (`< 2 ^ 64`). -/
def ChainEncodedLenFits (ch : ChainPB) : Prop :=
  chainPBEncodedLen ch < 2 ^ 64

/-! ## Hoare Specifications (`Spec`) for `Epoch::encoded_len` and `Chain::encoded_len` -/

/-- Ghost arguments of `<Epoch as Message>::encoded_len` (pinned version). -/
structure EpochEncodedLenPinnedGhost where
  /-- Pointer to `&Epoch` (`x0`, 112 bytes). -/
  a : BitVec 64
  /-- `Vec` pins of the `send` and `recv` `Option<EpochDirection>` fields. -/
  g : ChainEpochPBGhost
  /-- The pure `ChainEpochPB` value. -/
  ep : ChainEpochPB

/-- Ghost arguments of `<Epoch as Message>::encoded_len` (unpinned version). -/
structure EpochEncodedLenGhost where
  /-- Pointer to `&Epoch` (`x0`, 112 bytes). -/
  a : BitVec 64
  /-- The pure `ChainEpochPB` value. -/
  ep : ChainEpochPB

/-- Contract of `<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len`
    (`0x38abc` `[local#1]` and `0x664fc` `[local#2]`) with pinned `ChainEpochPBGhost`. -/
def epochEncodedLenPinnedSpec (A : RustAlloc) : Spec EpochEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ EpochEncodedLenFits x.ep⌝ ∗
      chainEpochPBPinnedAt A x.g x.a x.ep ∗ stackAt s.sp epochEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen x.ep) ∧ sf.trace = s0.trace⌝ ∗
      chainEpochPBPinnedAt A x.g x.a x.ep ∗ stackAt s0.sp epochEncodedLenStack

/-- Contract of `<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len`
    (`0x38abc` `[local#1]` and `0x664fc` `[local#2]`) with unpinned `chainEpochPBAt`. -/
def epochEncodedLenSpec (A : RustAlloc) : Spec EpochEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ EpochEncodedLenFits x.ep⌝ ∗
      chainEpochPBAt A x.a x.ep ∗ stackAt s.sp epochEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen x.ep) ∧ sf.trace = s0.trace⌝ ∗
      chainEpochPBAt A x.a x.ep ∗ stackAt s0.sp epochEncodedLenStack

/-- Ghost arguments of `<Chain as Message>::encoded_len` (pinned version). -/
structure ChainEncodedLenPinnedGhost where
  /-- Pointer to `&Chain` (`x0`, 80 bytes). -/
  a : BitVec 64
  /-- `Vec` pins of `links` and `next_root`. -/
  g : ChainPBGhost
  /-- The pure `ChainPB` value. -/
  ch : ChainPB

/-- Ghost arguments of `<Chain as Message>::encoded_len` (unpinned version). -/
structure ChainEncodedLenGhost where
  /-- Pointer to `&Chain` (`x0`, 80 bytes). -/
  a : BitVec 64
  /-- The pure `ChainPB` value. -/
  ch : ChainPB

/-- Contract of `<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len`
    (`0x39698` `[local#1]` and `0x68790` `[local#2]`) with pinned `ChainPBGhost`. -/
def chainEncodedLenPinnedSpec (A : RustAlloc) : Spec ChainEncodedLenPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ ChainEncodedLenFits x.ch⌝ ∗
      chainPBPinnedAt A x.g x.a x.ch ∗ stackAt s.sp chainEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chainPBEncodedLen x.ch) ∧ sf.trace = s0.trace⌝ ∗
      chainPBPinnedAt A x.g x.a x.ch ∗ stackAt s0.sp chainEncodedLenStack

/-- Contract of `<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len`
    (`0x39698` `[local#1]` and `0x68790` `[local#2]`) with unpinned `chainPBAt`. -/
def chainEncodedLenSpec (A : RustAlloc) : Spec ChainEncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ ChainEncodedLenFits x.ch⌝ ∗
      chainPBAt A x.a x.ch ∗ stackAt s.sp chainEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chainPBEncodedLen x.ch) ∧ sf.trace = s0.trace⌝ ∗
      chainPBAt A x.a x.ch ∗ stackAt s0.sp chainEncodedLenStack

/-! ## Varint Length & `LibsignalSpqrV1.Proto` Bridge Theorems -/

/-- Threshold decision tree equivalent to `varintLen v` and `(Proto.encodeVarint v).length`. -/
def varintLenBV (v : BitVec 64) : BitVec 64 :=
  if v < 0x80#64 then 1#64
  else if v >>> 7 < 0x80#64 then 2#64
  else if v >>> 14 < 0x80#64 then 3#64
  else if v >>> 21 < 0x80#64 then 4#64
  else if v >>> 28 < 0x80#64 then 5#64
  else if v >>> 35 < 0x80#64 then 6#64
  else if v >>> 42 < 0x80#64 then 7#64
  else if v >>> 49 < 0x80#64 then 8#64
  else if v >>> 56 < 0x80#64 then 9#64
  else 10#64

private theorem or_one_ne_zero (x : BitVec 64) : (x ||| 1#64) ≠ 0#64 := by
  bv_bits

private theorem or_one_div_two (x : BitVec 64) :
    (x ||| 1#64).toNat / 2 = x.toNat / 2 := by
  have h : (x ||| 1#64) >>> 1 = x >>> 1 := by bv_bits
  have h1 : ((x ||| 1#64) >>> 1).toNat = (x >>> 1).toNat := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using h1

private theorem shr_lt_128_iff_clz_gt (v : BitVec 64) (s : Nat) (hs : s ≤ 56) :
    (v >>> s < 0x80#64) ↔ BitVec.ofNat 64 (56 - s) < (v ||| 1#64).clz := by
  have hc_le : (v ||| 1#64).clz.toNat ≤ 63 := ProofLib.clz_or_one_toNat_le v
  have hlo : 2 ^ (64 - 1 - (v ||| 1#64).clz.toNat) ≤ (v ||| 1#64).toNat :=
    BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide : 0 < 64) (or_one_ne_zero v)
  have hhi : (v ||| 1#64).toNat < 2 ^ (64 - (v ||| 1#64).clz.toNat) :=
    BitVec.toNat_lt_two_pow_sub_clz
  have hdiv := or_one_div_two v
  have hpow_s : 2 ^ (s + 7) = 128 * 2 ^ s := by rw [Nat.pow_add, Nat.mul_comm]
  have hpow_even : 2 ^ (s + 7) = 2 * 2 ^ (s + 6) := by
    rw [show s + 7 = (s + 6) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have h1 : (v >>> s < 0x80#64) ↔ v.toNat < 2 ^ (s + 7) := by
    rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change v.toNat / 2 ^ s < 128 ↔ v.toNat < 2 ^ (s + 7)
    rw [hpow_s]
    exact Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)
  have h2 : v.toNat < 2 ^ (s + 7) ↔ (v ||| 1#64).toNat < 2 ^ (s + 7) := by omega
  have h3 : (v ||| 1#64).toNat < 2 ^ (s + 7) ↔ 56 - s < (v ||| 1#64).clz.toNat := by
    constructor
    · intro hlt
      have hpow_lt : 2 ^ (64 - 1 - (v ||| 1#64).clz.toNat) < 2 ^ (s + 7) :=
        Nat.lt_of_le_of_lt hlo hlt
      have hexp : 64 - 1 - (v ||| 1#64).clz.toNat < s + 7 :=
        (Nat.pow_lt_pow_iff_right (by decide)).mp hpow_lt
      omega
    · intro hgt
      have hexp : 64 - (v ||| 1#64).clz.toNat ≤ s + 7 := by omega
      exact Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) hexp)
  have h4 : 56 - s < (v ||| 1#64).clz.toNat ↔ BitVec.ofNat 64 (56 - s) < (v ||| 1#64).clz := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h1.trans (h2.trans (h3.trans h4))

theorem hwVarintLen_eq_varintLenBV (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      varintLenBV v := by
  unfold varintLenBV
  have hv0 : (v < 0x80#64) ↔ (v >>> 0 < 0x80#64) := by simp
  simp only [hv0,
      shr_lt_128_iff_clz_gt v 0 (by decide),
      shr_lt_128_iff_clz_gt v 7 (by decide),
      shr_lt_128_iff_clz_gt v 14 (by decide),
      shr_lt_128_iff_clz_gt v 21 (by decide),
      shr_lt_128_iff_clz_gt v 28 (by decide),
      shr_lt_128_iff_clz_gt v 35 (by decide),
      shr_lt_128_iff_clz_gt v 42 (by decide),
      shr_lt_128_iff_clz_gt v 49 (by decide),
      shr_lt_128_iff_clz_gt v 56 (by decide)]
  have hle : (v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le v
  generalize (v ||| 1#64).clz = c at hle ⊢
  have hc : c = (c.truncate 8).zeroExtend 64 := by bv_bits
  have hc8 : c.truncate 8 ≤ 63#8 := by bv_bits
  rw [hc]
  generalize c.truncate 8 = b at hc8 ⊢
  revert b hc8; decide

private theorem ushiftRight_add (w : BitVec 64) (a b : Nat) :
    (w >>> a) >>> b = w >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

theorem varintLenBV_eq_protoEncodeVarint_length (v : BitVec 64) :
    varintLenBV v = BitVec.ofNat 64 (Proto.encodeVarint v).length := by
  unfold varintLenBV Proto.encodeVarint
  dsimp only [Proto.encodeVarintAux]
  simp only [ushiftRight_add, Nat.reduceAdd]
  by_cases h0 : v < 0x80#64 <;> simp only [h0, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h1 : v >>> 7 < 0x80#64 <;> simp only [h1, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h2 : v >>> 14 < 0x80#64 <;> simp only [h2, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h3 : v >>> 21 < 0x80#64 <;> simp only [h3, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h4 : v >>> 28 < 0x80#64 <;> simp only [h4, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h5 : v >>> 35 < 0x80#64 <;> simp only [h5, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h6 : v >>> 42 < 0x80#64 <;> simp only [h6, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h7 : v >>> 49 < 0x80#64 <;> simp only [h7, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h8 : v >>> 56 < 0x80#64 <;> simp only [h8, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]
  have h9 : v >>> 63 < 0x80#64 := by bv_bits
  simp only [h9, ↓reduceIte, List.length_cons, List.length_nil, Nat.reduceAdd]

theorem varintLen_bounds (v : BitVec 64) :
    1 ≤ varintLen v ∧ varintLen v ≤ 10 := by
  unfold varintLen
  have hle : (v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le v
  have hlt : ((v ||| 1#64).clz ^^^ 0x3f#64).toNat ≤ 63 := by
    have : ((v ||| 1#64).clz ^^^ 0x3f#64) ≤ 63#64 := by bv_bits
    exact this
  omega

theorem hwVarintLen_eq_ofNat_varintLen (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (varintLen v) := by
  have hbv : ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      (((v ||| 1#64).clz ^^^ 0x3f#64) * 9#64 + 73#64) >>> 6 := by
    have hle : (v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le v
    generalize (v ||| 1#64).clz = c at hle ⊢
    have hc : c = (c.truncate 8).zeroExtend 64 := by bv_bits
    have hc8 : c.truncate 8 ≤ 63#8 := by bv_bits
    rw [hc]
    generalize c.truncate 8 = b at hc8 ⊢
    revert b hc8; decide
  apply BitVec.eq_of_toNat_eq
  have h2 : (((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6).toNat =
      varintLen v := by
    unfold varintLen
    rw [hbv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hlt : ((v ||| 1#64).clz ^^^ 0x3f#64).toNat < 64 := by
      have hle : (v ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le v
      have : ((v ||| 1#64).clz ^^^ 0x3f#64) < 64#64 := by bv_bits
      exact this
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have hm1 : ((v ||| 1#64).clz ^^^ 0x3f#64).toNat * 9 % 2 ^ 64 =
        ((v ||| 1#64).clz ^^^ 0x3f#64).toNat * 9 := Nat.mod_eq_of_lt (by omega)
    rw [hm1, Nat.mod_eq_of_lt (by omega)]
  have hb := varintLen_bounds v
  rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem hwVarintLen_bvShift_eq_ofNat_varintLen (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 63#64) + (((v ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      BitVec.ofNat 64 (varintLen v) :=
  hwVarintLen_eq_ofNat_varintLen v

theorem protoEncodedLenVarint_eq_varintLen (v : BitVec 64) :
    Proto.encodedLenVarint v = varintLen v := by
  unfold Proto.encodedLenVarint
  have h1 := (hwVarintLen_eq_varintLenBV v).symm.trans (hwVarintLen_eq_ofNat_varintLen v)
  rw [varintLenBV_eq_protoEncodeVarint_length] at h1
  have h2 := congrArg BitVec.toNat h1
  have hb := varintLen_bounds v
  have hlen : (Proto.encodeVarint v).length ≤ 11 := by
    unfold Proto.encodeVarint
    let rec aux (n : Nat) (x : BitVec 64) : (Proto.encodeVarintAux n x).length ≤ n + 1 := by
      cases n with
      | zero => simp [Proto.encodeVarintAux]
      | succ n =>
        unfold Proto.encodeVarintAux
        split
        · simp
        · simp only [List.length_cons]
          have := aux n (x >>> 7)
          omega
    exact aux 10 v
  simp only [BitVec.toNat_ofNat] at h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  exact h2

theorem varintLen_zext32_le_five (v : BitVec 32) :
    varintLen (v.zeroExtend 64) ≤ 5 := by
  unfold varintLen
  have hclz : 32#64 ≤ (v.zeroExtend 64 ||| 1#64).clz := by
    have hhi : (v.zeroExtend 64 ||| 1#64).toNat < 2 ^ 32 := by
      change (v.zeroExtend 64 ||| 1#64) < 0x100000000#64
      bv_bits
    have hlo := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide : 0 < 64)
      (or_one_ne_zero (v.zeroExtend 64))
    have hlt : 2 ^ (64 - 1 - (v.zeroExtend 64 ||| 1#64).clz.toNat) < 2 ^ 32 :=
      Nat.lt_of_le_of_lt hlo hhi
    have hexp : 64 - 1 - (v.zeroExtend 64 ||| 1#64).clz.toNat < 32 :=
      (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
    rw [BitVec.le_def]
    change 32 ≤ (v.zeroExtend 64 ||| 1#64).clz.toNat
    omega
  have hx : ((v.zeroExtend 64 ||| 1#64).clz ^^^ 0x3f#64) ≤ 31#64 := by
    have hle : (v.zeroExtend 64 ||| 1#64).clz ≤ 63#64 := ProofLib.clz_or_one_le _
    generalize (v.zeroExtend 64 ||| 1#64).clz = c at hclz hle ⊢
    bv_bits
  have hxt : ((v.zeroExtend 64 ||| 1#64).clz ^^^ 0x3f#64).toNat ≤ 31 := hx
  omega

theorem u32VarintFieldEncodedLen_le_six (v : BitVec 32) :
    u32VarintFieldEncodedLen v ≤ 6 := by
  unfold u32VarintFieldEncodedLen
  split
  · omega
  · have := varintLen_zext32_le_five v
    omega

theorem chainParamsPBEncodedLen_le_twelve (p : ChainParamsPB) :
    chainParamsPBEncodedLen p ≤ 12 := by
  unfold chainParamsPBEncodedLen
  have h1 := u32VarintFieldEncodedLen_le_six p.maxJump
  have h2 := u32VarintFieldEncodedLen_le_six p.maxOooKeys
  omega

theorem varintLen_of_lt_128 {n : Nat} (hn : n < 128) :
    varintLen (BitVec.ofNat 64 n) = 1 := by
  rw [← protoEncodedLenVarint_eq_varintLen]
  unfold Proto.encodedLenVarint Proto.encodeVarint Proto.encodeVarintAux
  have hlt : BitVec.ofNat 64 n < 0x80#64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hn
  simp [hlt]

theorem optChainParamsPBFieldEncodedLen_some (p : ChainParamsPB) :
    optChainParamsPBFieldEncodedLen (some p) = 2 + chainParamsPBEncodedLen p := by
  dsimp only [optChainParamsPBFieldEncodedLen]
  have hle := chainParamsPBEncodedLen_le_twelve p
  rw [varintLen_of_lt_128 (by omega)]

/-! ### Exact equivalence with `LibsignalSpqrV1.Proto` `encodedLen` -/

private theorem protoEncodeKey_len_one (tag : BitVec 32) (wt : Proto.WireType)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeKey tag wt).length = 1 := by
  have hlt : ((tag <<< 3) ||| wt.toU32).zeroExtend 64 < 0x80#64 := by
    rcases htag with ⟨_, h2⟩
    cases wt <;> dsimp [Proto.WireType.toU32] <;> bv_bits
  dsimp only [Proto.encodeKey, Proto.encodeVarint, Proto.encodeVarintAux]
  split
  · rfl
  · contradiction

theorem u32VarintFieldEncodedLen_eq_proto (tag : BitVec 32) (v : BitVec 32)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeUint32Field tag v).length = u32VarintFieldEncodedLen v := by
  unfold Proto.encodeUint32Field u32VarintFieldEncodedLen
  by_cases hv : v = 0#32
  · simp [hv]
  · have hbeq : (v == 0#32) = false := beq_eq_false_iff_ne.mpr hv
    simp only [hv, hbeq, ↓reduceIte, Bool.false_eq_true, List.length_append,
      protoEncodeKey_len_one tag .varint htag, ← protoEncodedLenVarint_eq_varintLen,
      Proto.encodedLenVarint]

theorem u64VarintFieldEncodedLen_eq_proto (tag : BitVec 32) (v : BitVec 64)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeUint64Field tag v).length = u64VarintFieldEncodedLen v := by
  unfold Proto.encodeUint64Field u64VarintFieldEncodedLen
  by_cases hv : v = 0#64
  · simp [hv]
  · have hbeq : (v == 0#64) = false := beq_eq_false_iff_ne.mpr hv
    simp only [hv, hbeq, ↓reduceIte, Bool.false_eq_true, List.length_append,
      protoEncodeKey_len_one tag .varint htag, ← protoEncodedLenVarint_eq_varintLen,
      Proto.encodedLenVarint]

theorem i32VarintFieldEncodedLen_eq_proto (tag : BitVec 32) (v : BitVec 32)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeInt32Field tag v).length = i32VarintFieldEncodedLen v := by
  unfold Proto.encodeInt32Field i32VarintFieldEncodedLen
  by_cases hv : v = 0#32
  · simp [hv]
  · have hbeq : (v == 0#32) = false := beq_eq_false_iff_ne.mpr hv
    simp only [hv, hbeq, ↓reduceIte, Bool.false_eq_true, List.length_append,
      protoEncodeKey_len_one tag .varint htag, ← protoEncodedLenVarint_eq_varintLen,
      Proto.encodedLenVarint]

theorem bytesFieldEncodedLen_eq_proto (tag : BitVec 32) (bs : List (BitVec 8))
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeBytesField tag bs).length = bytesFieldEncodedLen bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond bytesFieldEncodedLen
  cases hbs : bs.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte, List.length_append,
      protoEncodeKey_len_one tag .lengthDelimited htag, ← protoEncodedLenVarint_eq_varintLen,
      Proto.encodedLenVarint]
  · simp

theorem epochDirectionPBEncodedLen_eq_proto (d : EpochDirectionPB) :
    EpochDirectionPB.encodedLen d = epochDirectionPBEncodedLen d := by
  unfold EpochDirectionPB.encodedLen EpochDirectionPB.encodeRaw epochDirectionPBEncodedLen
  simp only [List.length_append,
    u32VarintFieldEncodedLen_eq_proto 1#32 d.ctr ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 2#32 d.next ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 3#32 d.prev ⟨by decide, by decide⟩]

theorem optEpochDirectionPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option EpochDirectionPB) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage EpochDirectionPB.encodeRaw tag opt).length =
      optEpochDirectionPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some d =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optEpochDirectionPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← epochDirectionPBEncodedLen_eq_proto, EpochDirectionPB.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

theorem chainEpochPBEncodedLen_eq_proto (ep : ChainEpochPB) :
    ChainEpochPB.encodedLen ep = chainEpochPBEncodedLen ep := by
  unfold ChainEpochPB.encodedLen ChainEpochPB.encodeRaw chainEpochPBEncodedLen
  simp only [List.length_append,
    optEpochDirectionPBFieldEncodedLen_eq_proto 1#32 ep.send ⟨by decide, by decide⟩,
    optEpochDirectionPBFieldEncodedLen_eq_proto 2#32 ep.recv ⟨by decide, by decide⟩]

theorem chainParamsPBEncodedLen_eq_proto (p : ChainParamsPB) :
    ChainParamsPB.encodedLen p = chainParamsPBEncodedLen p := by
  unfold ChainParamsPB.encodedLen ChainParamsPB.encodeRaw chainParamsPBEncodedLen
  simp only [List.length_append,
    u32VarintFieldEncodedLen_eq_proto 1#32 p.maxJump ⟨by decide, by decide⟩,
    u32VarintFieldEncodedLen_eq_proto 2#32 p.maxOooKeys ⟨by decide, by decide⟩]

theorem optChainParamsPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option ChainParamsPB) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage ChainParamsPB.encodeRaw tag opt).length =
      optChainParamsPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some p =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optChainParamsPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← chainParamsPBEncodedLen_eq_proto, ChainParamsPB.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

private theorem foldl_body_add (init : Nat) (links : List ChainEpochPB) :
    links.foldl (fun acc ep => acc + chainEpochPBBodyEncodedLen ep) init =
      init + links.foldl (fun acc ep => acc + chainEpochPBBodyEncodedLen ep) 0 := by
  induction links generalizing init with
  | nil => simp
  | cons ep rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + chainEpochPBBodyEncodedLen ep), ih (chainEpochPBBodyEncodedLen ep)]
    omega

theorem chainLinksBodiesEncodedLen_cons (ep : ChainEpochPB) (rest : List ChainEpochPB) :
    chainLinksBodiesEncodedLen (ep :: rest) =
      chainEpochPBBodyEncodedLen ep + chainLinksBodiesEncodedLen rest := by
  unfold chainLinksBodiesEncodedLen
  simp only [List.foldl_cons, Nat.zero_add]
  exact foldl_body_add (chainEpochPBBodyEncodedLen ep) rest

theorem chainLinksFieldEncodedLen_eq_proto (tag : BitVec 32) (links : List ChainEpochPB)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw tag links).length =
      chainLinksFieldEncodedLen links := by
  unfold chainLinksFieldEncodedLen
  induction links with
  | nil => rfl
  | cons ep rest ih =>
    change (Proto.encodeMessage ChainEpochPB.encodeRaw tag ep ++
      Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw tag rest).length =
      chainLinksBodiesEncodedLen (ep :: rest) + (ep :: rest).length
    rw [List.length_append, List.length_cons, chainLinksBodiesEncodedLen_cons, ih]
    unfold Proto.encodeMessage chainEpochPBBodyEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one tag .lengthDelimited htag,
      ← chainEpochPBEncodedLen_eq_proto, ChainEpochPB.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]
    omega

theorem chainPBEncodedLen_eq_proto (ch : ChainPB) :
    ChainPB.encodedLen ch = chainPBEncodedLen ch := by
  unfold ChainPB.encodedLen ChainPB.encodeRaw chainPBEncodedLen
  simp only [List.length_append,
    i32VarintFieldEncodedLen_eq_proto 1#32 ch.direction ⟨by decide, by decide⟩,
    u64VarintFieldEncodedLen_eq_proto 2#32 ch.currentEpoch ⟨by decide, by decide⟩,
    chainLinksFieldEncodedLen_eq_proto 3#32 ch.links ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 4#32 ch.nextRoot ⟨by decide, by decide⟩,
    u64VarintFieldEncodedLen_eq_proto 5#32 ch.sendEpoch ⟨by decide, by decide⟩,
    optChainParamsPBFieldEncodedLen_eq_proto 6#32 ch.params ⟨by decide, by decide⟩]

theorem authenticatorPBEncodedLen_eq_proto (auth : AuthenticatorPB) :
    ProtoAuthenticator.encodedLen auth = authenticatorPBEncodedLen auth := by
  unfold ProtoAuthenticator.encodedLen ProtoAuthenticator.encodeRaw authenticatorPBEncodedLen
  simp only [List.length_append,
    bytesFieldEncodedLen_eq_proto 1#32 auth.rootKey ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 2#32 auth.macKey ⟨by decide, by decide⟩]

theorem versionNegotiationPBEncodedLen_eq_proto (vn : VersionNegotiationPB) :
    VersionNegotiationPB.encodedLen vn = versionNegotiationPBEncodedLen vn := by
  unfold VersionNegotiationPB.encodedLen VersionNegotiationPB.encodeRaw versionNegotiationPBEncodedLen
  simp only [List.length_append,
    bytesFieldEncodedLen_eq_proto 1#32 vn.authKey ⟨by decide, by decide⟩,
    i32VarintFieldEncodedLen_eq_proto 2#32 vn.direction ⟨by decide, by decide⟩,
    i32VarintFieldEncodedLen_eq_proto 3#32 vn.minVersion ⟨by decide, by decide⟩,
    optChainParamsPBFieldEncodedLen_eq_proto 4#32 vn.chainParams ⟨by decide, by decide⟩]

/-! ### Unpinned (`*PBAt`) ↔ Pinned (`*PBPinnedAt`) Existential Bridges -/

private theorem sepExists_const {α : Sort _} (a₀ : α) (P : SepProp) :
    (∃∗ _ : α, P) = P := by
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun _ => Entails.refl _
  · exact Entails.sepExists_right a₀ (Entails.refl _)

theorem vecU8_eq_exists_pin (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs = ∃∗ pin : VecPin, vecU8At A v pin.cap pin.ptr bs := by
  unfold vecU8
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun c => Entails.sepExists_elim fun p =>
      Entails.sepExists_right ⟨c, p⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨c, p⟩ =>
      Entails.sepExists_right c (Entails.sepExists_right p (Entails.refl _))

theorem epochDirectionPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    epochDirectionPBAt A a d = ∃∗ g : EpochDirectionPBGhost, epochDirectionPBPinnedAt A g a d := by
  simp only [epochDirectionPBAt, epochDirectionPBPinnedAt, rustBytesVecAt, vecU8_eq_exists_pin,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun p2 => Entails.sepExists_elim fun p1 =>
      Entails.sepExists_right ⟨p1, p2⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨p1, p2⟩ =>
      Entails.sepExists_right p2 (Entails.sepExists_right p1 (Entails.refl _))

theorem optEpochDirectionPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option EpochDirectionPB) :
    optEpochDirectionPBAt A a opt =
      ∃∗ g : EpochDirectionPBGhost, optEpochDirectionPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optEpochDirectionPBAt, optEpochDirectionPBPinnedAt]
    exact (sepExists_const ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ _).symm
  | some d =>
    exact epochDirectionPBAt_eq_exists_pinned A a d

theorem chainEpochPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64) (ep : ChainEpochPB) :
    chainEpochPBAt A a ep = ∃∗ g : ChainEpochPBGhost, chainEpochPBPinnedAt A g a ep := by
  simp only [chainEpochPBAt, chainEpochPBPinnedAt, optEpochDirectionPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun gr => Entails.sepExists_elim fun gs =>
      Entails.sepExists_right ⟨gs, gr⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨gs, gr⟩ =>
      Entails.sepExists_right gr (Entails.sepExists_right gs (Entails.refl _))

theorem chainLinksVecAt_eq_exists_pin (A : RustAlloc) (v : BitVec 64) (links : List ChainEpochPB) :
    chainLinksVecAt A v links = ∃∗ pin : VecPin, chainLinksVecPinnedAt A pin v links := by
  unfold chainLinksVecAt chainLinksVecPinnedAt vecOf
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun c => Entails.sepExists_elim fun p =>
      Entails.sepExists_right ⟨c, p⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨c, p⟩ =>
      Entails.sepExists_right c (Entails.sepExists_right p (Entails.refl _))

theorem chainPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64) (ch : ChainPB) :
    chainPBAt A a ch = ∃∗ g : ChainPBGhost, chainPBPinnedAt A g a ch := by
  simp only [chainPBAt, chainPBPinnedAt, chainLinksVecAt_eq_exists_pin,
    rustBytesVecAt, vecU8_eq_exists_pin,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun p2 => Entails.sepExists_elim fun p1 =>
      Entails.sepExists_right ⟨p1, p2⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨p1, p2⟩ =>
      Entails.sepExists_right p2 (Entails.sepExists_right p1 (Entails.refl _))

theorem authenticatorPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64) (auth : AuthenticatorPB) :
    authenticatorPBAt A a auth = ∃∗ g : AuthenticatorPBGhost, authenticatorPBPinnedAt A g a auth := by
  simp only [authenticatorPBAt, authenticatorPBPinnedAt, rustBytesVecAt, vecU8_eq_exists_pin,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun p2 => Entails.sepExists_elim fun p1 =>
      Entails.sepExists_right ⟨p1, p2⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨p1, p2⟩ =>
      Entails.sepExists_right p2 (Entails.sepExists_right p1 (Entails.refl _))

theorem versionNegotiationPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (vn : VersionNegotiationPB) :
    versionNegotiationPBAt A a vn =
      ∃∗ g : VersionNegotiationPBGhost, versionNegotiationPBPinnedAt A g a vn := by
  simp only [versionNegotiationPBAt, versionNegotiationPBPinnedAt, rustBytesVecAt, vecU8_eq_exists_pin,
    sepExists_sepConj_left]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun p1 =>
      Entails.sepExists_right ⟨p1⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨p1⟩ =>
      Entails.sepExists_right p1 (Entails.refl _)

end CryptoVerification.SpqrV1.ProtoRepr
