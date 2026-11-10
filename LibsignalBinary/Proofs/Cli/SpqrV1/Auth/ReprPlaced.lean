/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Repr
public import Aesop.BuiltinRules
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Relocatable Per-Block Fetches for `Authenticator::encode [local#3]` (Block `454`)

Generates per-block instruction decode and entry-address theorems under `[LibsignalPlacement]` for
Block `454` (`prost::encoding::message::encode::<Authenticator, Vec<u8>> [local#3]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Auth.Placed

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open CryptoVerification

gen_ls_blk 454

end CryptoVerification.Cli.SpqrV1.Auth.Placed

namespace CryptoVerification.Cli.SpqrV1.Auth

open Arm64 Arm64.Obj ProofLib CryptoVerification

abbrev authEncodeLocal1BlkIdx : Nat := 454

abbrev cliAuthPanicRoSym : String :=
  "libsignal_cli_ratchet:.rodata..Lanon.165"

@[simp, arm64_norm, wp_norm]
theorem authEncodeLocal1_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl authEncodeLocal1Name = pl.base authEncodeLocal1BlkIdx :=
  ls_fnAddr_block (by decide +kernel)

end CryptoVerification.Cli.SpqrV1.Auth
