/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.RecordCodeSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Relocatable Per-Block Fetches for `session_message_decrypt_signal`

Generated placed block program and instruction fetch lemmas for block `197`
(`session_message_decrypt_signal`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.LibsignalPublicApi.Placed

open Arm64 Arm64.Obj ProofLib CryptoVerification

set_option maxHeartbeats 32000000 in
gen_ls_blk 197

theorem lsProg_197_eq_record_lsProg_197 [LibsignalPlacement] (H : LibsignalHooks) :
    lsProg_197 H = CryptoVerification.LibsignalTripleRatchet.Record.lsProg_197 H :=
  (instIsLsBlockProg_197 H).eq_blockProgram.trans
    (CryptoVerification.LibsignalTripleRatchet.Record.instIsLsBlockProg_197 H).eq_blockProgram.symm

end CryptoVerification.LibsignalPublicApi.Placed
