/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionPlacedObj
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# Relocatable Entry Resolution for `PqRatchetState::encode_to_vec` (Block `426`)

Block index and entry-point resolution for `<spqr::proto::pq_ratchet::PqRatchetState as
prost::message::Message>::encode_to_vec` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec

open Arm64 Arm64.Obj ProofLib CryptoVerification

abbrev pqRatchetStateEncodeToVecBlkIdx : Nat := 426

abbrev pqRatchetStateEncodeToVecSym : String :=
  "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"

abbrev spqrEncodeToVecName : String := pqRatchetStateEncodeToVecSym

@[simp, arm64_norm, wp_norm]
theorem pqRatchetStateEncodeToVec_fnAddr (pl : MultiPlacement) :
    libsignalSessionLib.fnAddr pl pqRatchetStateEncodeToVecSym =
      pl.base pqRatchetStateEncodeToVecBlkIdx :=
  ls_fnAddr_block (by decide +kernel)

end CryptoVerification.Cli.SpqrV1.Prost.EncodeToVec
