/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage P1 on Store Kits

Relocatable `[LibsignalPlacement]` Stage P1 umbrella module on Block `518` (`lsProg_518`, entry
`(blkPl_518).base = lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Block `518` (`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`) program
under `[LibsignalPlacement]`. -/
abbrev stageP1ProgPlaced [LibsignalPlacement] (ext : String → Option (State → State)) : Program :=
  lsProg_518 ext

/-- Block `518` entry address `(blkPl_518).base = lsmpl.base 518` under `[LibsignalPlacement]`. -/
abbrev stageP1EntryPlaced [LibsignalPlacement] : BitVec 64 :=
  (blkPl_518).base

theorem stageP1EntryPlaced_eq_lsmpl_base [LibsignalPlacement] :
    stageP1EntryPlaced = lsmpl.base 518 := rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

