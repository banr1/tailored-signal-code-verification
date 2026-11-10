/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Callees
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Chain3Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `message::merge<Chain> [local#4]` Closure from `Chain3CalleePlacedKit`

`[LibsignalPlacement]` counterpart of `Callees`, deriving `Chain3CalleesPlacedW` and
`Chain3PlacedOkAtW` (`chainMerge5_placed_ok`) from `Chain3CalleePlacedKit`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.LibsignalPlacement

/-- `Chain3CalleesPlacedW ext` from `kit : Chain3CalleePlacedKit`. -/
theorem chain3CalleesPlacedW_of_kit [LibsignalPlacement] (kit : Chain3CalleePlacedKit)
    {ext : String → Option (State → State)} :
    Chain3CalleesPlacedW ext where
  dv := kit.dv (Rust.withPanics ext)
  bm := kit.bm (Rust.withPanics ext)
  grow := kit.grow (Rust.withPanics ext)

theorem chain3PlacedOkAtW_of_kit [LibsignalPlacement] (kit : Chain3CalleePlacedKit)
    {ext : String → Option (State → State)} :
    Chain3PlacedOkAtW ext :=
  chain3_placed_ok_of_callees ext (chain3CalleesPlacedW_of_kit kit)

/-- Placed `Chain5PlacedOkAtW` contract from `Chain3CalleePlacedKit` and `AllocContractsPlaced`. -/
theorem chainMerge5_placed_ok [LibsignalPlacement] (kit : Chain3CalleePlacedKit)
    (ext : String → Option (State → State)) :
    Chain5PlacedOkAtW ext :=
  chain3PlacedOkAtW_of_kit kit

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
