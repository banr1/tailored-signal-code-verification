/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrHooksExt
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateExt

@[expose] public section

set_option autoImplicit false

/-!
# CLI `spqr::decode_state` Contract Instantiation

Instantiates `spqr_decode_state_ok_4k` with `spqrAllocContracts4K_of_externsOk_on` and
`spqrHooks_of_externsOk_on` to discharge `DecodeStateOkX canonicalV1InnerHeap img A ext'` under
`CliExternsOk P A ext`.
-/

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecodeStateExt

open Arm64 ProofLib
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliExternsOk cliExternsWith)
open CryptoVerification.SignalSession.Cli.Slots (AgreeOnCliHooks)
open CryptoVerification.Cli.SpqrV1.M4
  (spqrAllocContracts4K_of_externsOk_on)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateOkX canonicalV1InnerHeap spqr_decode_state_ok_4k)

/-- `spqr::decode_state` meets `DecodeStateOkX canonicalV1InnerHeap img A ext'` under
`CliExternsOk P A ext`, `AgreeOnCliHooks ext ext'`, and `Obj.Loads libsignalSessionImage img`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.M4.decodeState_ok_of_externsOk_on
    {P : PEParams} {img : Obj.Image} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext')
    (himg : Obj.Loads libsignalSessionImage img) :
    DecodeStateOkX canonicalV1InnerHeap img A ext' :=
  spqr_decode_state_ok_4k himg
    (spqrAllocContracts4K_of_externsOk_on hOk hAg img.base)

/-- `spqr::decode_state` meets `DecodeStateOkX canonicalV1InnerHeap img A (cliExternsWith ext)`
from `CliExternsOk P A ext` and `Obj.Loads libsignalSessionImage img`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.M4.decodeState_ok_of_externsOk
    {P : PEParams} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    DecodeStateOkX canonicalV1InnerHeap img A (cliExternsWith ext) :=
  CryptoVerification.Cli.SpqrV1.M4.decodeState_ok_of_externsOk_on
    hOk (AgreeOnCliHooks.cliExternsWith ext) himg

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecodeStateExt
