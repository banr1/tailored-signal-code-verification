/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom

/-!
# `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` CLI Contract

Instantiates `DecodeDeps` from `AllocContractsX` and proves `identityKeyPairTryFrom_cli_ok` against
`identityKeyPairTryFromSpec`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli.RunProofs

/-- CLI `DecodeDeps` at arbitrary `A : RustAlloc` and `ext` from `AllocContractsX`. -/
theorem cliDecodeDeps_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (C : Crypto)
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext) :
    DecodeDeps img A ext :=
  let td := cliTryFromDeps_ok C 0#64 himg hA
  { varintSlice := td.varintSlice
    int32Merge := td.int32Merge
    skipField := td.skipField
    dropDecodeError := td.dropDecodeError
    bytesMerge := td.bytesMerge
    pkTryFrom := pkTryFrom_ok_ext img ext himg }

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` meets `identityKeyPairTryFromSpec A img`
at arbitrary `A : RustAlloc` and `ext` given `AllocContractsX img A ext`. -/
theorem identityKeyPairTryFrom_cli_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (C : Crypto)
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName)
      (identityKeyPairTryFromSpec A img) :=
  IkpTryFrom.ikp_subroutine_ok (C := C)
    (S := ⟨fun _ _ => none, fun _ _ => 0, fun _ _ => .error false, fun _ _ => False,
      fun _ _ => False⟩)
    (cliTryFromHooksW_ok C _ himg hA)
    (cliDecodeDeps_ok C himg hA)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
