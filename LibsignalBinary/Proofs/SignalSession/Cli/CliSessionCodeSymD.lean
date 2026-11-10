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
# Relocatable Per-Block Fetches for `signal_session` Helper Blocks (Part D)

Instruction-fetch lemmas under `[LibsignalPlacement]` for blocks `587, 588, 589, 590, 592, 593, 594, 596, 597`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.SignalSession.Cli.Placed

open Arm64 Arm64.Obj ProofLib CryptoVerification

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 587

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 588

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 589

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 590

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 592

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 593

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 594

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 596

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 597

end CryptoVerification.SignalSession.Cli.Placed
