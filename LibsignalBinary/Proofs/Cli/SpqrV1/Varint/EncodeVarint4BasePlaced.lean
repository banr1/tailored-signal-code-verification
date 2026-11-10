/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Aesop.BuiltinRules
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.GenLsBlock
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Relocatable Per-Block Fetches for `Cli/SpqrV1/Varint` (Blocks `451`, `448`)

Generates `[LibsignalPlacement]` per-block fetch and relocation lemmas for `encode_varint [local#4]`
(Block `451`) and `encode_repeated [local#3]` (Block `448`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Varint.Placed

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open CryptoVerification

gen_ls_blk 451
gen_ls_blk 448

end CryptoVerification.Cli.SpqrV1.Varint.Placed

namespace CryptoVerification.Cli.SpqrV1.Varint

open Arm64 Arm64.Obj ProofLib CryptoVerification

abbrev encodeVarint2BlkIdx : Nat := 451
abbrev encodeRepeated1BlkIdx : Nat := 448

abbrev encodeVarint2CliName : String :=
  "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#4]"

abbrev encodeRepeated1CliName : String :=
  "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#3]"

@[simp, arm64_norm, wp_norm]
theorem encodeVarint2Cli_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl encodeVarint2CliName = pl.base encodeVarint2BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem encodeRepeated1Cli_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl encodeRepeated1CliName = pl.base encodeRepeated1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

end CryptoVerification.Cli.SpqrV1.Varint
