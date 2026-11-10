/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueX

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.SerGlueX

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchet

theorem serContractsX_cli (W : CliHooks) (img : Obj.Image) :
    Proofs.libsignal.Hooks2.SerContractsX img E2E.HooksE.A0 (cliExterns W) :=
  serContractsX_of_trAllocContractsX (MainHops.allocContractsX_cli W img)

theorem serializeCanonX_cli (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.SignalSession.Cli.recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX E2E.HooksE.A0).inImage img) :=
  serializeCanonX_ok_of_trAllocContractsX (MainHops.allocContractsX_cli W img)

theorem serContractsX_of_allocContractsX {img : Obj.Image} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) :
    Proofs.libsignal.Hooks2.SerContractsX img A ext :=
  serContractsX_of_trAllocContractsX hC

theorem serializeCanonX_of_allocContractsX {img : Obj.Image} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.SignalSession.Cli.recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img) :=
  serializeCanonX_ok_of_trAllocContractsX hC

theorem serContractsX_ext {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    Proofs.libsignal.Hooks2.SerContractsX img A (cliExternsWith ext) :=
  serContractsX_of_trAllocContractsX (MainHops.AllocContractsX.of_externsOk hOk img)

theorem serializeCanonX_ext {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.SignalSession.Cli.recordSerializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img) :=
  serializeCanonX_ok_of_trAllocContractsX (MainHops.AllocContractsX.of_externsOk hOk img)

end CryptoVerification.SignalSession.Cli.Store.SerGlueX

namespace CryptoVerification.SignalSession.Cli.Store.SerGlueXCli
export CryptoVerification.SignalSession.Cli.Store.SerGlueX
  (serContractsX_cli serializeCanonX_cli
   serContractsX_of_allocContractsX serializeCanonX_of_allocContractsX
   serContractsX_ext serializeCanonX_ext)
end CryptoVerification.SignalSession.Cli.Store.SerGlueXCli
