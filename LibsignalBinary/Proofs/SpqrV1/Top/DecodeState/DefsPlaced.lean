/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateCodeSym

/-!
# Relocatable `[LibsignalPlacement]` Definitions for `spqr::decode_state` (Block `325`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Obj.lookup

/-- Rebased relocatable block program for `spqr::decode_state` (Block `325`). -/
noncomputable abbrev decodeStatePlacedProg [LibsignalPlacement] (ext : String → Option (State → State)) : Program :=
  (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)

/-- Relocatable entry address of `spqr::decode_state` (Block `325`). -/
noncomputable abbrev decodeStatePlacedEntry [LibsignalPlacement] : BitVec 64 :=
  (blkPl_325).base

end CryptoVerification.SpqrV1.Top.DecodeState
