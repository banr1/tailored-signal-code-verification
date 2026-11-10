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
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.OutgoingRatchetCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- shake: keep

/-!
# Relocatable Per-Block Symbol Bindings for `TripleRatchet/ReceiveRatchet`

Per-block symbol bindings and instruction-fetch aliases for `TripleRatchet::from_session_state`
(block 57), `TripleRatchet::apply_to_session_state` (block 58), and their `Vec` drop-glue callees
(blocks 2 and 3).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 2
gen_ls_blk 3
gen_ls_blk 57
gen_ls_blk 58

end CryptoVerification
