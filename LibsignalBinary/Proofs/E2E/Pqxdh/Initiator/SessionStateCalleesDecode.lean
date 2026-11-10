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

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.E2E.Pqxdh

open Arm64 CryptoVerification ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree initPrivKeySerialize [0x3e7c0 → 0x3e814]
gen_decodes libsignalSessionCode_tree initWithSenderChain [0x117e8 → 0x119f4]
gen_decodes libsignalSessionCode_tree sessionStateNew [0x125a4 → 0x126a0]
gen_decodes libsignalSessionCode_tree withReceiverChain [0x11c98 → 0x12064]
gen_decodes libsignalSessionCode_tree setUnackPreKeyMsg [0x12298 → 0x123d0]

end CryptoVerification.E2E.Pqxdh

namespace CryptoVerification.E2E.Pqxdh.Initiator

gen_ls_blk 27
gen_ls_blk 30
gen_ls_blk 33
gen_ls_blk 37
gen_ls_blk 43
gen_ls_blk 45
gen_ls_blk 205
gen_ls_blk 208

end CryptoVerification.E2E.Pqxdh.Initiator
