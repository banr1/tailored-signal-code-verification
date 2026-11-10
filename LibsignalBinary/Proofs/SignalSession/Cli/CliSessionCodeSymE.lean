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
# Relocatable Per-Block Fetches for `signal_session` Helper Blocks (Part E)

Instruction-fetch lemmas under `[LibsignalPlacement]` for blocks `598, 600, 601, 602, 603, 604, 605, 606, 608, 610, 611, 613`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.SignalSession.Cli.Placed

open Arm64 Arm64.Obj ProofLib CryptoVerification

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 598

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 600

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 601

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 602

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 603

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 604

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 605

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 606

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 608

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 610

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 611

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 613

end CryptoVerification.SignalSession.Cli.Placed
