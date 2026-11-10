/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Relocatable Per-Block Fetches for CLI SPQR V1 `RawVecInner` Helpers (Blocks `465`, `460`)

Generates per-block instruction decode and entry-address theorems under `[LibsignalPlacement]` for
Block `465` (`finish_grow [local#8]`) and Block `460` (`do_reserve_and_handle [local#7]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Alloc.Placed

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open CryptoVerification

gen_ls_blk 465
gen_ls_blk 460

end CryptoVerification.Cli.SpqrV1.Alloc.Placed

namespace CryptoVerification.Cli.SpqrV1.Alloc

open Arm64 Arm64.Obj ProofLib CryptoVerification

abbrev finishGrow2BlkIdx : Nat := 465

abbrev doReserve2BlkIdx : Nat := 460

abbrev finishGrow2CliName : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]"

abbrev doReserve2CliName : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"

@[simp, arm64_norm, wp_norm]
theorem finishGrow2Cli_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl finishGrow2CliName = pl.base finishGrow2BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem doReserve2Cli_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl doReserve2CliName = pl.base doReserve2BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

end CryptoVerification.Cli.SpqrV1.Alloc
