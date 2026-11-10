/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Per-Block Fetches for `signal_session_ratchet` Helper Blocks (Part C)

Generates `[LibsignalPlacement]` fetch and relocation lemmas via `gen_ls_blk_ultra` for
Blocks `458, 459, 460, 461, 465, 468, 469, 470`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.CliRatchet.Placed

open Arm64 Arm64.Obj ProofLib CryptoVerification

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 458

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 459

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 460

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 461

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 465

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 468

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 469

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 470

end CryptoVerification.CliRatchet.Placed
