/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO

@[expose] public section

set_option autoImplicit false

/-!
# Constant-Time Equality, `PublicKey::eq`, and HKDF Hook Bridges

Derives `ctEqSliceROSpecExt.inImage`, `PublicKeyEqOkExt32`, `FindIndexOkX`, and `HkdfContractsExt`
from `CliExternsOk` and the stacked 32-bit `subtle::black_box::<u8>` contract.
-/

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq

open Arm64 ProofLib
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots

theorem hookSat_blackBox32_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    HookSat ext' "subtle::black_box::<u8>" CliExt.blackBoxSpec :=
  hAg.hookSat (by decide) hOk.blackBox

theorem hookSat_compress256_of_externsOk_on {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    HookSat ext' "sha2::sha256::compress256" (CliExt.compress256Spec P.C) :=
  hAg.hookSat (by decide) hOk.compress256

theorem hkdfContractsExt_of_externsOk_on (img : Obj.Image) {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    HkdfContractsExt img P.C.F ext' :=
  HkdfContractsExt.of_hookSat img P.C ext'
    (hAg.hookSat (by decide) hOk.compress256)
    (hAg.hookSat (by decide) hOk.memcpy)
    (hAg.hookSat (by decide) hOk.memcpyRO)
    (hAg.hookSat (by decide) hOk.memset)

theorem ctEqRO_inImage_of_blackBox32 (img : Obj.Image)
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ConsumeMessageKeyTransfer.ctEqName)
      (ctEqSliceROSpecExt.inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (ctEqRO_ok_ext32 img.base h_bb)

theorem publicKeyEq_ok_of_blackBox32 (b : BitVec 64)
    {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    Getters.PublicKeyEqOkExt32 b ext :=
  publicKeyEq_ok_ext32 b h_bb

theorem findIndex_ok_of_blackBox32 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_bb : HookSat ext "subtle::black_box::<u8>" CliExt.blackBoxSpec) :
    Proofs.libsignal.Stage1X.FindIndexOkX img A ext :=
  findIndex_ok_ext32 himg h_bb

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq
