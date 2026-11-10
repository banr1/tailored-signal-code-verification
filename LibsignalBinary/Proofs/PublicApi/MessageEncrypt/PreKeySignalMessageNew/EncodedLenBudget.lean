/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPfBudget

/-!
# Budget-Compatible `PreKeySignalMessage::encoded_len`

Relocatable `[LibsignalPlacement]` wrapper establishing `SplitBudget.preKeyMsgEncodedLenSpec A`
(with `VmPreserved`) for `<wire::PreKeySignalMessage as prost::message::Message>::encoded_len`
(block `119`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_119 blkPl_119)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
  (preKeyMsgEncodedLenSpec PreKeyMsgEncodedLenPlacedOk)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPfBudget
  (preKeyMsgEncodedLen_placed_ok)

/-- Relocatable `PreKeySignalMessage::encoded_len` (block `119`) satisfies
`SplitBudget.preKeyMsgEncodedLenSpec A`. -/
theorem encodedLen_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} :
    subroutine_ok (lsProg_119 H) (blkPl_119).base (preKeyMsgEncodedLenSpec A) :=
  preKeyMsgEncodedLen_placed_ok

theorem encodedLen_placed_ok' [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} :
    PreKeyMsgEncodedLenPlacedOk A H :=
  preKeyMsgEncodedLen_placed_ok

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenBudget
