/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Decodes
public import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced

/-!
# `<spqr::v1::chunked::states::States>::from_pb` (Block `333`): Relocatable Decodes & Jump Table (`DecodesPlaced`)

Consolidates all 4 fetch shards (`0..11640`), seals `CryptoVerification.blkPC_333` as `[irreducible]`,
and defines `statesFromPbJumpTablePlacedAt` + `rodata_statesFromPbJumpTablePlacedAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] CryptoVerification.blkPC_333

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib
open CryptoVerification

/-- `.rodata` symbol for the 22-byte jump table of `<States>::from_pb` (Block `333`). -/
abbrev statesFromPbJumpTableSym : String :=
  "spqr:.rodata.<spqr::v1::chunked::states::States>::from_pb"

/-- Relocatable `.rodata` jump table for `<States>::from_pb` (Block `333`, `22` bytes). -/
def statesFromPbJumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ statesFromPbJumpTableSym) ↦ᵣ statesFromPbJumpTableBytes

/-- Extract `statesFromPbJumpTablePlacedAt` (`22` bytes) from `LibsignalRoLoaded lsmpl m`. -/
theorem rodata_statesFromPbJumpTablePlacedAt [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ statesFromPbJumpTablePlacedAt ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

end CryptoVerification.SpqrV1.States.FromPb
