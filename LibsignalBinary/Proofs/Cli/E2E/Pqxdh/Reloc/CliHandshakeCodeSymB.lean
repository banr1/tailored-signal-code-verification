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
# Relocatable Per-Block Fetches for `signal_session_handshake` Helper Blocks (Part B)

Generates relocatable per-block instruction fetch definitions for Blocks `516`, `517`, `519`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.CliHandshake.Placed

open Arm64 Arm64.Obj ProofLib CryptoVerification

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 516

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 517

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 519

end CryptoVerification.CliHandshake.Placed
