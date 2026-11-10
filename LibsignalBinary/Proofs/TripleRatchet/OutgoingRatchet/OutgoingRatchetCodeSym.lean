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
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym -- shake: keep

/-!
# Relocatable Per-Block Fetches for `TripleRatchet/OutgoingRatchet`

Per-block `gen_block_Sym` instruction fetch lemmas for `OutgoingTripleRatchet::from_session_state`,
`OutgoingTripleRatchet::apply_to_session_state`, `SessionState::remote_identity_key`, and
`drop_glue::<SignalProtocolError>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 29
gen_ls_blk 19
gen_ls_blk 20

end CryptoVerification
