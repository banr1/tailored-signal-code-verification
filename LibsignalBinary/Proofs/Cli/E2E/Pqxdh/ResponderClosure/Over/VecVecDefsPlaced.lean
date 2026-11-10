/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefs
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `<Vec<Vec<u8>> as Clone>::clone` Contract Statement on 1 Element

Defines `VecVecClone1PlacedOkStmt` at `lsmpl.base 117` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization CryptoVerification.E2E.Record.Placed
open Proofs.libsignal.Hooks2

/-- Placed subroutine contract for `<Vec<Vec<u8>> as Clone>::clone` on `len = 1` at `lsmpl.base 117`. -/
def VecVecClone1PlacedOkStmt [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_117).rebase (blkPl_117).base H) (lsmpl.base 117)
    (withLsCodeLoaded lsmpl (vecVecClone1SpecX A))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
