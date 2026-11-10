/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.GenDecodes
import VCVio.Prelude.Core

/-!
# Instruction decode lemmas for `SessionStructure::merge_field` tag 14

Instruction fetch/decode lemmas at offset `0x581c` covering the tag-14 (`pending_kyber_pre_key`)
dispatch, multi-byte outer length varint decode, nested `PendingKyberPreKey` field loop, and
epilogue.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux

open Arm64 ProofLib ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

gen_decodes CryptoVerification.libsignalSessionCode_tree mf14
  [0x581c → 0x5858, 0x598c → 0x59d4, 0x5cd4 → 0x5d00, 0x5d44 → 0x5db8,
   0x5dbc → 0x5ea8, 0x5eac → 0x5ed8, 0x5f74 → 0x5f8c, 0x6134 → 0x6150]

end CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
