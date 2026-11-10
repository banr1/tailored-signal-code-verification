/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefs
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public meta import Lean
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `SessionRecord::serialize` with One Previous Session

Relocatable `[LibsignalPlacement]` statement `SerializePrev1PlacedOkStmt` for
`<SessionRecord>::serialize` (Block `52`) on a record with one archived previous session.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Placed

def SerializePrev1PlacedOkStmt [LibsignalPlacement] (prog : Program) (A : RustAlloc) : Prop :=
  subroutine_ok prog (lsmpl.base 52) (withLsCl lsmpl (serializePrev1Spec A))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
