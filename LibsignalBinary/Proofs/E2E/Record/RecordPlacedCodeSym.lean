/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionPlacedObj
import LibsignalBinary.Proofs.Placed.BridgeReloc

/-!
# Relocatable per-block instruction fetches for `E2E/Record` and `SessionRecordAt`

Re-exports the per-block instruction fetch lemmas from `RecordPlacedCodeSymA`–`RecordPlacedCodeSymF`
(blocks `11, 12, 14, 15, 46, 52, 80, 82, 85, 86, 88, 117, 118`) together with `.rodata` vtable
resolution lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Record.Placed

open Arm64 Arm64.Obj ProofLib CryptoVerification

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_promotable_even_vtable (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "bytes::bytes::PROMOTABLE_EVEN_VTABLE" =
      pl.ρ "bytes::bytes::PROMOTABLE_EVEN_VTABLE" :=
  ls_resolve_data (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_promotable_odd_vtable (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "bytes::bytes::PROMOTABLE_ODD_VTABLE" =
      pl.ρ "bytes::bytes::PROMOTABLE_ODD_VTABLE" :=
  ls_resolve_data (by decide +kernel)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_shared_vtable (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl "bytes::bytes::SHARED_VTABLE" =
      pl.ρ "bytes::bytes::SHARED_VTABLE" :=
  ls_resolve_data (by decide +kernel)

end CryptoVerification.E2E.Record.Placed
