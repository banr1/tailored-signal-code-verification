/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Chain3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.EntryPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SrkPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyInnerPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeySeg3cPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ExitPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `message::merge<Chain> [local#4]` Slice Assembly

`[LibsignalPlacement]` counterpart of `Chain3`, assembling the placed entry, SRK, ChainKey,
MessageKeys, and exit slices into `Chain3PlacedOkAtW`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.LibsignalPlacement

/-- `Chain3PlacedOkAtW` from the placed callee contracts and the ChainKey / MessageKeys slice statements. -/
theorem chain3PlacedOkAtW_of_slices [LibsignalPlacement] (ext : String → Option (State → State))
    (hC : Chain3CalleesPlacedW ext) (hCk : Chain3ChainKeyPlacedStmt ext)
    (hMk : Chain3MessageKeysPlacedStmt ext) :
    Chain3PlacedOkAtW ext :=
  chainMerge3W_placed_ok ext hC (chain3Entry_placed_ok ext) (chain3Srk_placed_ok ext) hCk hMk
    (chain3Exit_placed_ok ext)

/-- `Chain3PlacedOkAtW` (`= Chain5PlacedOkAtW`) from `Chain3CalleesPlacedW ext` alone. -/
theorem chain3_placed_ok_of_callees [LibsignalPlacement] (ext : String → Option (State → State))
    (hC : Chain3CalleesPlacedW ext) :
    Chain3PlacedOkAtW ext :=
  chain3PlacedOkAtW_of_slices ext hC (chain3ChainKey_placed_ok ext) (chain3MessageKeys_placed_ok ext)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
