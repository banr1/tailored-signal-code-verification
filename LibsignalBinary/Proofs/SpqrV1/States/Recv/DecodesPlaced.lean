/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymBasePlaced

/-!
# `<States>::recv` (Block `332`): Relocatable Decodes & `.rodata`

Consolidates the 6 placed fetch shards (`0..19532`), seals `blkPC_332`, and defines
`statesRecvJumpTablePlacedAt` and `statesRecvRoPlacedAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] CryptoVerification.blkPC_332

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib
open CryptoVerification
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)

/-- `.rodata` symbol for the 22-byte jump table of `<States>::recv` (Block `332`). -/
abbrev statesRecvJumpTableSym : String :=
  "spqr:.rodata.<spqr::v1::chunked::states::States>::recv"

/-- Relocatable `.rodata` jump table for `<States>::recv` (Block `332`, `22` bytes). -/
def statesRecvJumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ statesRecvJumpTableSym) ↦ᵣ statesRecvJumpTableBytes

/-- Expanded 22-byte jump table at `lsρ statesRecvJumpTableSym`. -/
def statesRecvJumpTablePlacedExpanded [LibsignalPlacement] : SepProp :=
  let jt := lsρ statesRecvJumpTableSym
  (jt ↦₈ᵣ 0#8) ∗ ((jt + 1#64) ↦₈ᵣ 0#8) ∗
  ((jt + 2#64) ↦₈ᵣ 169#8) ∗ ((jt + 3#64) ↦₈ᵣ 1#8) ∗
  ((jt + 4#64) ↦₈ᵣ 171#8) ∗ ((jt + 5#64) ↦₈ᵣ 0#8) ∗
  ((jt + 6#64) ↦₈ᵣ 21#8) ∗ ((jt + 7#64) ↦₈ᵣ 1#8) ∗
  ((jt + 8#64) ↦₈ᵣ 33#8) ∗ ((jt + 9#64) ↦₈ᵣ 0#8) ∗
  ((jt + 10#64) ↦₈ᵣ 253#8) ∗ ((jt + 11#64) ↦₈ᵣ 1#8) ∗
  ((jt + 12#64) ↦₈ᵣ 31#8) ∗ ((jt + 13#64) ↦₈ᵣ 2#8) ∗
  ((jt + 14#64) ↦₈ᵣ 102#8) ∗ ((jt + 15#64) ↦₈ᵣ 1#8) ∗
  ((jt + 16#64) ↦₈ᵣ 56#8) ∗ ((jt + 17#64) ↦₈ᵣ 3#8) ∗
  ((jt + 18#64) ↦₈ᵣ 123#8) ∗ ((jt + 19#64) ↦₈ᵣ 0#8) ∗
  ((jt + 20#64) ↦₈ᵣ 63#8) ∗ ((jt + 21#64) ↦₈ᵣ 2#8)

/-- Relocatable `.rodata` + global bundle required by `<States>::recv` (Block `332`). -/
def statesRecvRoPlacedAt [LibsignalPlacement] : SepProp :=
  statesRecvJumpTablePlacedAt ∗
    unchunkedSendCt2PlacedRoAt ∗
    tokenInitPlacedAt ∗
    reduceTablePlacedAt

theorem rodata_statesRecvJumpTablePlacedAt [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ statesRecvJumpTablePlacedAt ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

end CryptoVerification.SpqrV1.States.Recv
