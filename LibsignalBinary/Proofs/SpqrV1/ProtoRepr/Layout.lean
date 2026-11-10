/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module


/-!
# Memory Layout Constants for Core SPQR V1 Protobuf Structs

Byte sizes, alignments, field offsets, and `Option` niche encodings for the `prost` 0.14.4 structs
`ChainParams`, `EpochDirection`, `Epoch`, `Chain`, `Authenticator`, and `VersionNegotiation` in
`libsignalSessionCode`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

/-! ## Function Entry Offsets in `libsignalSessionCode` -/

/-- `<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#1]`
    (`0x38abc`, 121 instructions, 484 bytes). -/
def epochEncodedLenLocal1Off : BitVec 64 := 0x38ba0#64

/-- `<spqr::proto::pq_ratchet::chain::Epoch as prost::message::Message>::encoded_len [local#2]`
    (`0x664fc`, 121 instructions, 484 bytes). -/
def epochEncodedLenLocal2Off : BitVec 64 := 0x61104#64

/-- `<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#1]`
    (`0x39698`, 126 instructions, 504 bytes). -/
def chainEncodedLenLocal1Off : BitVec 64 := 0x3977c#64

/-- `<spqr::proto::pq_ratchet::Chain as prost::message::Message>::encoded_len [local#2]`
    (`0x68790`, 126 instructions, 504 bytes). -/
def chainEncodedLenLocal2Off : BitVec 64 := 0x63398#64

/-! ## 1. `ChainParams` (`8` B, align `4`) and `Option<ChainParams>` (`12` B, align `4`)

`ChainParams` stores `max_jump: u32` at `+0x00` (tag 1) and `max_ooo_keys: u32` at `+0x04` (tag 2);
`Option<ChainParams>` prepends a `u32` discriminant (`0` = `None`, `1` = `Some`) at `+0x00`. -/

/-- Byte size of `spqr::proto::pq_ratchet::ChainParams` (`8` bytes). -/
def chainParamsPBSize : Nat := 8

/-- Byte alignment of `spqr::proto::pq_ratchet::ChainParams` (`4` bytes). -/
def chainParamsPBAlign : BitVec 64 := 4#64

/-- Offset of `max_jump: u32` (tag 1) within `ChainParams`. -/
def chainParamsPBMaxJumpOff : BitVec 64 := 0x00#64

/-- Offset of `max_ooo_keys: u32` (tag 2) within `ChainParams`. -/
def chainParamsPBMaxOooKeysOff : BitVec 64 := 0x04#64

/-- Byte size of `Option<spqr::proto::pq_ratchet::ChainParams>` (`12` bytes). -/
def optChainParamsPBSize : Nat := 12

/-- Discriminant value for `None : Option<ChainParams>` (`0#32`). -/
def optChainParamsPBNoneTag : BitVec 32 := 0#32

/-- Discriminant value for `Some : Option<ChainParams>` (`1#32`). -/
def optChainParamsPBSomeTag : BitVec 32 := 1#32

/-- Offset of the `u32` discriminant within `Option<ChainParams>`. -/
def optChainParamsPBTagOff : BitVec 64 := 0x00#64

/-- Offset of the `ChainParams` payload within `Option<ChainParams>`. -/
def optChainParamsPBPayloadOff : BitVec 64 := 0x04#64

/-- Offset of `max_jump: u32` within `Option<ChainParams>`. -/
def optChainParamsPBMaxJumpOff : BitVec 64 := 0x04#64

/-- Offset of `max_ooo_keys: u32` within `Option<ChainParams>`. -/
def optChainParamsPBMaxOooKeysOff : BitVec 64 := 0x08#64

/-! ## 2. `EpochDirection` (`56` B, align `8`)

Stores `next: Vec<u8>` at `+0x00..+0x18` (tag 2), `prev: Vec<u8>` at `+0x18..+0x30` (tag 3),
`ctr: u32` at `+0x30` (tag 1), and 4 bytes of trailing padding at `+0x34..+0x38`.
`Option<EpochDirection>` uses the `next.cap = 0xFFFFFFFFFFFFFFFF` niche at `+0x00` for `None`. -/

/-- Byte size of `spqr::proto::pq_ratchet::chain::epoch::EpochDirection` (`56` bytes = `0x38`). -/
def epochDirectionPBSize : Nat := 56

/-- Byte size of `EpochDirection` as a 64-bit bitvector (`0x38#64`). -/
def epochDirectionPBSizeBV : BitVec 64 := 0x38#64

/-- Byte alignment of `EpochDirection` (`8` bytes). -/
def epochDirectionPBAlign : BitVec 64 := 8#64

/-- Offset of `next: Vec<u8>` (tag 2, 24 bytes: `{cap @ +0x00, ptr @ +0x08, len @ +0x10}`) within `EpochDirection`. -/
def epochDirectionPBNextOff : BitVec 64 := 0x00#64

/-- Offset of `next.cap: usize` within `EpochDirection` (also the `Option<EpochDirection>` niche word). -/
def epochDirectionPBNextCapOff : BitVec 64 := 0x00#64

/-- Offset of `next.ptr: *mut u8` within `EpochDirection`. -/
def epochDirectionPBNextPtrOff : BitVec 64 := 0x08#64

/-- Offset of `next.len: usize` within `EpochDirection`. -/
def epochDirectionPBNextLenOff : BitVec 64 := 0x10#64

/-- Offset of `prev: Vec<u8>` (tag 3, 24 bytes: `{cap @ +0x18, ptr @ +0x20, len @ +0x28}`) within `EpochDirection`. -/
def epochDirectionPBPrevOff : BitVec 64 := 0x18#64

/-- Offset of `prev.cap: usize` within `EpochDirection`. -/
def epochDirectionPBPrevCapOff : BitVec 64 := 0x18#64

/-- Offset of `prev.ptr: *mut u8` within `EpochDirection`. -/
def epochDirectionPBPrevPtrOff : BitVec 64 := 0x20#64

/-- Offset of `prev.len: usize` within `EpochDirection`. -/
def epochDirectionPBPrevLenOff : BitVec 64 := 0x28#64

/-- Offset of `ctr: u32` (tag 1, 4 bytes) within `EpochDirection`. -/
def epochDirectionPBCtrOff : BitVec 64 := 0x30#64

/-- Offset of the 4-byte trailing padding (`+0x34..+0x38`) within `EpochDirection`. -/
def epochDirectionPBPadOff : BitVec 64 := 0x34#64

/-- Byte length of the trailing padding within `EpochDirection` (`4` bytes). -/
def epochDirectionPBPadSize : Nat := 4

/-- Byte size of the uninitialized tail of `Option<EpochDirection>::None` after the 8-byte niche word (`48` bytes). -/
def optEpochDirectionPBNoneTailSize : Nat := 48

/-! ## 3. `chain::Epoch` (`112` B, align `8`)

Stores `send: Option<EpochDirection>` at `+0x00..+0x38` (tag 1) and `recv: Option<EpochDirection>`
at `+0x38..+0x70` (tag 2), with `Vec<Epoch>` element stride `0x70 = 112` bytes. -/

/-- Byte size of `spqr::proto::pq_ratchet::chain::Epoch` (`112` bytes = `0x70`). -/
def chainEpochPBSize : Nat := 112

/-- Byte size / element stride of `Epoch` as a 64-bit bitvector (`0x70#64`). -/
def chainEpochPBStride : BitVec 64 := 0x70#64

/-- Byte alignment of `Epoch` (`8` bytes). -/
def chainEpochPBAlign : BitVec 64 := 8#64

/-- Offset of `send: Option<EpochDirection>` (tag 1, 56 bytes) within `Epoch`. -/
def chainEpochPBSendOff : BitVec 64 := 0x00#64

/-- Offset of `recv: Option<EpochDirection>` (tag 2, 56 bytes) within `Epoch`. -/
def chainEpochPBRecvOff : BitVec 64 := 0x38#64

/-- Offset of `recv.next.len: usize` within `Epoch` (`0x38 + 0x10 = 0x48`). -/
def chainEpochPBRecvNextLenOff : BitVec 64 := 0x48#64

/-- Offset of `recv.prev.len: usize` within `Epoch` (`0x38 + 0x28 = 0x60`). -/
def chainEpochPBRecvPrevLenOff : BitVec 64 := 0x60#64

/-- Offset of `recv.ctr: u32` within `Epoch` (`0x38 + 0x30 = 0x68`). -/
def chainEpochPBRecvCtrOff : BitVec 64 := 0x68#64

/-! ## 4. `Chain` (`80` B, align `8`)

Stores `links: Vec<Epoch>` at `+0x00..+0x18` (tag 3), `next_root: Vec<u8>` at `+0x18..+0x30`
(tag 4), `current_epoch: u64` at `+0x30` (tag 2), `send_epoch: u64` at `+0x38` (tag 5),
`params: Option<ChainParams>` at `+0x40..+0x4c` (tag 6), and `direction: i32` at `+0x4c` (tag 1).
`Option<Chain>` uses the `links.cap = 0xFFFFFFFFFFFFFFFF` niche at `+0x00` for `None`. -/

/-- Byte size of `spqr::proto::pq_ratchet::Chain` (`80` bytes = `0x50`). -/
def chainPBSize : Nat := 80

/-- Byte alignment of `Chain` (`8` bytes). -/
def chainPBAlign : BitVec 64 := 8#64

/-- Offset of `links: Vec<Epoch>` (tag 3, 24 bytes: `{cap @ +0x00, ptr @ +0x08, len @ +0x10}`) within `Chain`. -/
def chainPBLinksOff : BitVec 64 := 0x00#64

/-- Offset of `links.cap: usize` within `Chain` (also the `Option<Chain>` niche word). -/
def chainPBLinksCapOff : BitVec 64 := 0x00#64

/-- Offset of `links.ptr: *mut Epoch` within `Chain`. -/
def chainPBLinksPtrOff : BitVec 64 := 0x08#64

/-- Offset of `links.len: usize` within `Chain`. -/
def chainPBLinksLenOff : BitVec 64 := 0x10#64

/-- Offset of `next_root: Vec<u8>` (tag 4, 24 bytes: `{cap @ +0x18, ptr @ +0x20, len @ +0x28}`) within `Chain`. -/
def chainPBNextRootOff : BitVec 64 := 0x18#64

/-- Offset of `next_root.cap: usize` within `Chain`. -/
def chainPBNextRootCapOff : BitVec 64 := 0x18#64

/-- Offset of `next_root.ptr: *mut u8` within `Chain`. -/
def chainPBNextRootPtrOff : BitVec 64 := 0x20#64

/-- Offset of `next_root.len: usize` within `Chain`. -/
def chainPBNextRootLenOff : BitVec 64 := 0x28#64

/-- Offset of `current_epoch: u64` (tag 2, 8 bytes) within `Chain`. -/
def chainPBCurrentEpochOff : BitVec 64 := 0x30#64

/-- Offset of `send_epoch: u64` (tag 5, 8 bytes) within `Chain`. -/
def chainPBSendEpochOff : BitVec 64 := 0x38#64

/-- Offset of `params: Option<ChainParams>` (tag 6, 12 bytes) within `Chain`. -/
def chainPBParamsOff : BitVec 64 := 0x40#64

/-- Offset of `params` discriminant (`u32`) within `Chain`. -/
def chainPBParamsTagOff : BitVec 64 := 0x40#64

/-- Offset of `params.max_jump` (`u32`) within `Chain`. -/
def chainPBParamsMaxJumpOff : BitVec 64 := 0x44#64

/-- Offset of `params.max_ooo_keys` (`u32`) within `Chain`. -/
def chainPBParamsMaxOooKeysOff : BitVec 64 := 0x48#64

/-- Offset of `direction: i32` (tag 1, 4 bytes) within `Chain`. -/
def chainPBDirectionOff : BitVec 64 := 0x4c#64

/-- Byte size of the uninitialized tail of `Option<Chain>::None` after the 8-byte niche word (`72` bytes). -/
def optChainPBNoneTailSize : Nat := 72

/-! ## 5. `Authenticator` (`48` B, align `8`)

Stores `root_key: Vec<u8>` at `+0x00..+0x18` (tag 1) and `mac_key: Vec<u8>` at `+0x18..+0x30`
(tag 2). -/

/-- Byte size of `spqr::proto::pq_ratchet::Authenticator` (`48` bytes = `0x30`). -/
def authenticatorPBSize : Nat := 48

/-- Byte alignment of `Authenticator` (`8` bytes). -/
def authenticatorPBAlign : BitVec 64 := 8#64

/-- Offset of `root_key: Vec<u8>` (tag 1, 24 bytes: `{cap @ +0x00, ptr @ +0x08, len @ +0x10}`) within `Authenticator`. -/
def authenticatorPBRootKeyOff : BitVec 64 := 0x00#64

/-- Offset of `mac_key: Vec<u8>` (tag 2, 24 bytes: `{cap @ +0x18, ptr @ +0x20, len @ +0x28}`) within `Authenticator`. -/
def authenticatorPBMacKeyOff : BitVec 64 := 0x18#64

/-! ## 6. `VersionNegotiation` (`48` B, align `8`)

Stores `auth_key: Vec<u8>` at `+0x00..+0x18` (tag 1), `chain_params: Option<ChainParams>` at
`+0x18..+0x24` (tag 4), `direction: i32` at `+0x24` (tag 2), `min_version: i32` at `+0x28`
(tag 3), and 4 bytes of padding at `+0x2c..+0x30`. `Option<VersionNegotiation>` uses the
`auth_key.cap = 0xFFFFFFFFFFFFFFFF` niche at `+0x00` for `None`. -/

/-- Byte size of `spqr::proto::pq_ratchet::pq_ratchet_state::VersionNegotiation` (`48` bytes = `0x30`). -/
def versionNegotiationPBSize : Nat := 48

/-- Byte alignment of `VersionNegotiation` (`8` bytes). -/
def versionNegotiationPBAlign : BitVec 64 := 8#64

/-- Offset of `auth_key: Vec<u8>` (tag 1, 24 bytes: `{cap @ +0x00, ptr @ +0x08, len @ +0x10}`) within `VersionNegotiation`. -/
def versionNegotiationPBAuthKeyOff : BitVec 64 := 0x00#64

/-- Offset of `chain_params: Option<ChainParams>` (tag 4, 12 bytes) within `VersionNegotiation`. -/
def versionNegotiationPBChainParamsOff : BitVec 64 := 0x18#64

/-- Offset of `direction: i32` (tag 2, 4 bytes) within `VersionNegotiation`. -/
def versionNegotiationPBDirectionOff : BitVec 64 := 0x24#64

/-- Offset of `min_version: i32` (tag 3, 4 bytes) within `VersionNegotiation`. -/
def versionNegotiationPBMinVersionOff : BitVec 64 := 0x28#64

/-- Offset of the 4-byte trailing padding (`+0x2c..+0x30`) within `VersionNegotiation`. -/
def versionNegotiationPBPadOff : BitVec 64 := 0x2c#64

/-- Byte length of the trailing padding within `VersionNegotiation` (`4` bytes). -/
def versionNegotiationPBPadSize : Nat := 4

/-- Byte size of the uninitialized tail of `Option<VersionNegotiation>::None` after the 8-byte niche word (`40` bytes). -/
def optVersionNegotiationPBNoneTailSize : Nat := 40

end CryptoVerification.SpqrV1.ProtoRepr
