/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.TopDecodes
public import LibsignalBinary.Proofs.SpqrV1.Drop.States1a
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
import GeneratedLean.LibsignalSessionObj

/-!
# Relocatable Per-Block Fetches for Chunked `States` Drop Glue (Block `443`)

Generates per-block instruction decode, entry-address, and `.rodata` jump-table lemmas under
`[LibsignalPlacement]` for Block `443` (`core::ptr::drop_glue::<States> [local#3]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Drop.TopPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open CryptoVerification

gen_ls_blk 443

end CryptoVerification.Cli.SpqrV1.Drop.TopPlaced

namespace CryptoVerification.Cli.SpqrV1.Drop

open Arm64 Arm64.Obj ProofLib CryptoVerification
open CryptoVerification.SpqrV1.Drop (chunkedStatesLocal1JumpTableBytes)

abbrev dropChunkedStatesLocal1BlkIdx : Nat := 443

abbrev chunkedStatesLocal1JumpTableSym : String :=
  "libsignal_cli_ratchet:.rodata.core::ptr::drop_glue::<spqr::v1::chunked::states::States>"

def chunkedStatesLocal1JumpTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsmpl.ρ chunkedStatesLocal1JumpTableSym) ↦ᵣ chunkedStatesLocal1JumpTableBytes

def chunkedStatesLocal1JumpTablePlacedExpanded [LibsignalPlacement] : SepProp :=
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym) ↦₈ᵣ 49#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 1#64) ↦₈ᵣ 0#8) ∗
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 2#64) ↦₈ᵣ 61#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 3#64) ↦₈ᵣ 0#8) ∗
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 4#64) ↦₈ᵣ 19#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 5#64) ↦₈ᵣ 90#8) ∗
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 6#64) ↦₈ᵣ 104#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 7#64) ↦₈ᵣ 82#8) ∗
  ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 8#64) ↦₈ᵣ 132#8) ∗ ((lsmpl.ρ chunkedStatesLocal1JumpTableSym + 9#64) ↦₈ᵣ 43#8)

@[simp, arm64_norm, wp_norm]
theorem dropChunkedStatesLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl dropChunkedStatesLocal1Name = pl.base dropChunkedStatesLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

theorem chunkedStatesLocal1JumpTable_lsro_cli_intro {pl : MultiPlacement} {m : Memory}
    (hro : LibsignalRoLoaded pl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (pl.ρ chunkedStatesLocal1JumpTableSym ↦ᵣ chunkedStatesLocal1JumpTableBytes) ∗ P :=
  lsro_slice_intro hro (sym := chunkedStatesLocal1JumpTableSym) (off := 0) (by simp) (by decide +kernel) hP

end CryptoVerification.Cli.SpqrV1.Drop
