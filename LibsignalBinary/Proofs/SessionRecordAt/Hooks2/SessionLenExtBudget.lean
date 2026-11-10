/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenBudget
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# `VmPreserved`-Carrying `<SessionStructure as prost::Message>::encoded_len` (Block `86`)

Re-exports the `VmPreserved`-carrying `DefsBudget.sessionLenSpec` contract for Block `86`
(`<SessionStructure as prost::Message>::encoded_len`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SessionLenExtBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record.Placed (blkPl_86 lsProg_86)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (sessionLenSpec)
open LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenBudget (sessionLen_placed_ok)

/-- Block `86` (`<SessionStructure as prost::Message>::encoded_len`) under `[LibsignalPlacement]`. -/
theorem sessionLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_86 H) (blkPl_86).base
      (withLsCodeLoaded lsmpl (sessionLenSpec A)) :=
  sessionLen_placed_ok A H

theorem sessionLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 86)
      (withLsCl lsmpl (sessionLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (sessionLen_placed_ok A H)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SessionLenExtBudget
