/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1State
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.EncodedLenCodeSym
import LibsignalBinary.Proofs.Placed.BridgeReloc

/-!
# Relocatable Jump Table and Entry Helpers for `V1State::encoded_len [local#3]` (Block `484`)

Defines `.rodata` jump-table symbols and `[LibsignalPlacement]` entry helpers for CLI Block `484`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoVerification
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced

abbrev v1StateEncodedLenLocal1BlkIdx : Nat := 484

abbrev cliV1StateJtSym : String :=
  "libsignal_cli_ratchet:.rodata.<spqr::proto::pq_ratchet::V1State as prost::message::Message>::encoded_len"

@[simp, arm64_norm, wp_norm]
theorem v1StateEncodedLenLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl v1StateEncodedLenLocal1Name = pl.base v1StateEncodedLenLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

theorem v1StateJumpTableBytes_lsro_cli_intro {pl : MultiPlacement} {m : Memory}
    (hro : LibsignalRoLoaded pl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (pl.ρ cliV1StateJtSym ↦ᵣ v1StateJumpTableBytes) ∗ P :=
  lsro_slice_intro hro (sym := cliV1StateJtSym) (off := 0) (by simp) (by decide +kernel) hP

theorem hasJumpTableStepP2_placed_cli [LibsignalPlacement] (H : LibsignalHooks) :
    HasJumpTableStepP2 ((blkPC_484).rebase (blkPl_484).base H) (blkPl_484).base
      (lsρ cliV1StateJtSym) := by
  intro s P post oom hpc hrun hnext
  exact blkPC_484_pairStep_0x38 (blkPl_484).base H rfl hpc hrun hnext

end CryptoVerification.Cli.SpqrV1.ProtoRepr
