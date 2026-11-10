/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym -- shake: keep

/-!
# Instruction Decode & Block Lemmas for `SpqrV1/Prost/MessageEncode` (`[local#2]`)

Generates per-block placement descriptors (`Blocks 313, 315–319`) and `gen_decodes` instruction
tables for `ChainParams`, `PolynomialDecoder`, `PolynomialEncoder`, and `EpochDirection`
`encode` and `encoded_len` monomorphizations.
-/

@[expose] public section

namespace CryptoVerification

set_option maxRecDepth 2000000

gen_ls_blk 313
gen_ls_blk 315
gen_ls_blk 316
gen_ls_blk 317
gen_ls_blk 318
gen_ls_blk 319

end CryptoVerification

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

gen_decodes libsignalSessionCode_tree libsignalSessionBin
  [0x37278 → 0x373b8, 0x37604 → 0x37af4,
   0x4cd78 → 0x4cec8, 0x4d14c → 0x4d6a4]

gen_decodes libsignalSessionCode_tree spqrPolyDecBin
  [0x39f7c → 0x3a060, 0x642fc → 0x643e0]

gen_decodes libsignalSessionCode_tree spqrPolyEncBin
  [0x38e70 → 0x38f7c, 0x615f4 → 0x61700]

end CryptoVerification.SpqrV1.Prost.MessageEncode
