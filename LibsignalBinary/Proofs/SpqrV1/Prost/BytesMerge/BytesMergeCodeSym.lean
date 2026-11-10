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
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym -- shake: keep

/-!
# Relocatable Per-Block Fetches for `Prost/BytesMerge`

Pre-extracted instruction-fetch tables for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`
(Block `290`) and its callees (`decode_varint` in Block `291`, `DecodeError::from` in Block `261`,
`do_reserve_and_handle` in Block `320`, and `<Bytes as From<Vec<u8>>>::from` in Block `250`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 290

end CryptoVerification
