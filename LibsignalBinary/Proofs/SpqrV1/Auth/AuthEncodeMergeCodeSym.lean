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
public import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym -- shake: keep

/-!
# Relocatable Per-Block Fetches for `Authenticator` Encode and Merge

Generates per-block code symbols (`gen_ls_blk`) for blocks 151 (`encode<Authenticator> [local#1]`),
314 (`encode<Authenticator> [local#2]`), and 295 (`merge<Authenticator, &mut &[u8]>`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 151
gen_ls_blk 314
gen_ls_blk 295

end CryptoVerification
