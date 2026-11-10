/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Block Code Definitions for SPQR V1 `Prost.MessageMerge` (Part 1)

Per-block `Program` (`blkPC_<idx>`), `Placement` (`blkPl_<idx>`), instruction-fetch lemmas, and
`[wp_step]` / `[arm64_norm]` attributes for Blocks `294` (`ChainParams::merge`), `296`
(`PolynomialDecoder::merge`), `297` (`PolynomialEncoder::merge`), `299` (`EpochDirection::merge`),
`302` (`Chunked.HeaderSent::merge`), `306` (`Chunked.HeaderReceived::merge`), and `308`
(`Chunked.NoHeaderReceived::merge`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

-- Block 294: `prost::encoding::message::merge::<spqr::proto::pq_ratchet::ChainParams, &mut &[u8]>` (`0x4dcf8`)
gen_ls_blk 294

-- Block 296: `prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>` (`0x4e10c`)
gen_ls_blk 296

-- Block 297: `prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>` (`0x4e498`)
gen_ls_blk 297

-- Block 299: `prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>` (`0x4f544`)
gen_ls_blk 299

-- Block 302: `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent, &mut &[u8]>` (`0x4fdb0`)
gen_ls_blk 302

-- Block 306: `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived, &mut &[u8]>` (`0x50bac`)
gen_ls_blk 306

-- Block 308: `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived, &mut &[u8]>` (`0x511b4`)
gen_ls_blk 308

end CryptoVerification.SpqrV1.Prost.MessageMerge
