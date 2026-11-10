/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.Decodes
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.GenLsBlock
import GeneratedLean.LibsignalSessionObj

/-!
# Relocatable Per-Block Fetches for CLI SPQR V1 Leaf Drop Glue (Blocks `435`–`446`)

Generates per-block instruction decode and entry-address theorems under `[LibsignalPlacement]` for
Blocks `435`, `436`, `439`, `440`, `441`, `444`, and `446`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Drop.Placed

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open CryptoVerification

gen_ls_blk 435
gen_ls_blk 436
gen_ls_blk 439
gen_ls_blk 440
gen_ls_blk 441
gen_ls_blk 444
gen_ls_blk 446

end CryptoVerification.Cli.SpqrV1.Drop.Placed

namespace CryptoVerification.Cli.SpqrV1.Drop

open Arm64 Arm64.Obj ProofLib CryptoVerification

abbrev dropOptProtoPolyEncoderBlkIdx : Nat := 435
abbrev dropOptProtoUnchunkedCt1SentBlkIdx : Nat := 436
abbrev dropProtoSpqrChainBlkIdx : Nat := 439
abbrev dropPolyDecoderBlkIdx : Nat := 440
abbrev dropPolyEncoderLocal1BlkIdx : Nat := 441
abbrev dropUnchunkedCt1SentLocal1BlkIdx : Nat := 444
abbrev dropChainEpochSliceLocal1BlkIdx : Nat := 446

@[simp, arm64_norm, wp_norm]
theorem dropChainEpochSliceLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl dropChainEpochSliceLocal1Name = pl.base dropChainEpochSliceLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem dropProtoSpqrChain_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl dropProtoSpqrChainName = pl.base dropProtoSpqrChainBlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem dropPolyEncoderLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl dropPolyEncoderLocal1Name = pl.base dropPolyEncoderLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem dropPolyDecoder_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl dropPolyDecoderName = pl.base dropPolyDecoderBlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem dropOptProtoPolyEncoder_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl dropOptProtoPolyEncoderName = pl.base dropOptProtoPolyEncoderBlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem dropUnchunkedCt1SentLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl dropUnchunkedCt1SentLocal1Name = pl.base dropUnchunkedCt1SentLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem dropOptProtoUnchunkedCt1Sent_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl dropOptProtoUnchunkedCt1SentName = pl.base dropOptProtoUnchunkedCt1SentBlkIdx :=
  ls_fnAddr_block (by decide +kernel)

end CryptoVerification.Cli.SpqrV1.Drop
