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
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Relocatable Per-Block Decode Tables for `Cli/SpqrV1/Prost/MessageEncode`

Generates relocatable per-block fetch/decode lemmas for CLI Blocks `453` and `455`–`459`
(`ChainParams`, `PolynomialDecoder`, `PolynomialEncoder`, `EpochDirection`, `EkSentCt1Received`,
and `Ct1Sent` message encoders).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open CryptoVerification

gen_ls_blk 453
gen_ls_blk 455
gen_ls_blk 456
gen_ls_blk 457
gen_ls_blk 458
gen_ls_blk 459

end CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed
