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
# Relocatable Per-Block Fetches for `TripleRatchet/Getters`

Provides relocatable instruction fetches for the `Chain`, `MessageKey`, and
`SignalProtocolError` drop glue, `IdentityKey::is_same_account`, `SessionState` identity-key
and pre-key getters, and `PublicKey` deserialization and constant-time equality.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification

gen_ls_blk 2
gen_ls_blk 3
gen_ls_blk 5
gen_ls_blk 17
gen_ls_blk 28
gen_ls_blk 29
gen_ls_blk 35
gen_ls_blk 142
gen_ls_blk 211
gen_ls_blk 212
gen_ls_blk 213

end CryptoVerification.LibsignalTripleRatchet.Getters
