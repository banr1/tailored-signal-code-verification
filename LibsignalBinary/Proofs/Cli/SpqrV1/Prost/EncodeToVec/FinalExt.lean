/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalExt

@[expose] public section

set_option autoImplicit false

/-!
# CLI Re-Export of Bounded-Stack `PqRatchetState::encode_to_vec` (`AllocContractsX`)

Re-exports `pqRatchetStateEncodeToVec_pinned_okX_ax` and `pqRatchetStateEncodeToVec_okX_ax`
under `CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec`, matching
`LibsignalBinary/Proofs/Cli/SpqrV1/Prost/EncodeToVec/Final.lean` without requiring
0-stack `AllocContracts`.
-/

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Alloc

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_pinned_okX_ax
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqRatchetStateEncodeToVecPinnedOkX img A ext :=
  pqRatchetStateEncodeToVec_pinned_ok_ext_xa hAx himg

theorem _root_.CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_okX_ax
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqRatchetStateEncodeToVecOkX img A ext :=
  pqRatchetStateEncodeToVec_ok_ext_xa hAx himg

end CryptoVerification.SpqrV1.Prost.EncodeToVec
