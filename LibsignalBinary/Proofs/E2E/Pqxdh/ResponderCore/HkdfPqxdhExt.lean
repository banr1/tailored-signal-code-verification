/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfStubsExt
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfExpandShortExt
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfExtractNoneExt
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongExt

/-!
# `.inImage`-Free PQXDH HKDF and Responder Entry Points

Assembles `PqxdhHkdfExtractOk_ext` and `PqxdhHkdfExpandMultiInfoOk_ext` under `CliExternsOk P0 A ext`,
yielding `.inImage`-free contracts for `HandshakeKeys::derive` and `Pqxdh::accept`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.Initiator

/-! ## `PqxdhHkdfExpandMultiInfoOk_ext` from `HkdfStubsExt` -/

/-- `.inImage`-free `PqxdhHkdfExpandMultiInfoOk_ext P img ext` from `HkdfStubsExt img.base C.F ext`
(`k = 8` / `64` B, `k = 10` / `80` B, `k = 12` / `96` B, and vacuous `k ∉ {8, 10, 12}`). -/
theorem pqxdhHkdfExpandMultiInfo_ok_of_stubsExt
    {P : Primitives} {C : Crypto} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (hS : HkdfStubsExt img.base C.F ext) :
    PqxdhHkdfExpandMultiInfoOk_ext P img ext :=
  pqxdhHkdfExpandMultiInfo_ok_ext hP
    (expand_multi_info_ok_ro_ext hS)
    (expand_multi_info_96_46_ok_ext hS)

/-! ## `CliExternsOk`-Backed HKDF Contracts -/

theorem pqxdhHkdfExtract_ok_of_externsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhHkdfExtractOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img ext :=
  pqxdhHkdfExtract_ok_of_stubsExt
    (primitivesMatchCrypto_modelPrims X P0) himg
    (HkdfStubsExt.of_externsOk_raw img.base hOk)

theorem pqxdhHkdfExtract_ok_of_cliExternsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhHkdfExtractOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img
      (SignalSession.cliExternsWith ext) :=
  pqxdhHkdfExtract_ok_of_stubsExt
    (primitivesMatchCrypto_modelPrims X P0) himg
    (HkdfStubsExt.of_externsOk img.base hOk)

theorem pqxdhHkdfExpandMultiInfo_ok_of_externsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (_himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhHkdfExpandMultiInfoOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img ext :=
  pqxdhHkdfExpandMultiInfo_ok_of_stubsExt
    (primitivesMatchCrypto_modelPrims X P0)
    (HkdfStubsExt.of_externsOk_raw img.base hOk)

theorem pqxdhHkdfExpandMultiInfo_ok_of_cliExternsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (_himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhHkdfExpandMultiInfoOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img
      (SignalSession.cliExternsWith ext) :=
  pqxdhHkdfExpandMultiInfo_ok_of_stubsExt
    (primitivesMatchCrypto_modelPrims X P0)
    (HkdfStubsExt.of_externsOk img.base hOk)

/-! ## `HandshakeKeys::derive` and `Pqxdh::accept` Corollaries -/

theorem handshakeKeysDerive_ok_of_externsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  handshakeKeysDerive_ok_ext himg hWF
    (pqxdhHkdfExtract_ok_of_externsOk X himg hOk)
    (pqxdhHkdfExpandMultiInfo_ok_of_externsOk X himg hOk)

theorem handshakeKeysDerive_ok_of_cliExternsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  handshakeKeysDerive_ok_ext himg hWF
    (pqxdhHkdfExtract_ok_of_cliExternsOk X himg hOk)
    (pqxdhHkdfExpandMultiInfo_ok_of_cliExternsOk X himg hOk)

theorem pqxdhAccept_opt_fields_ok_of_externsOk'
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_opt_fields_ok_of_externsOk X himg hWF hOk
    (pqxdhHkdfExtract_ok_of_externsOk X himg hOk)
    (pqxdhHkdfExpandMultiInfo_ok_of_externsOk X himg hOk)

theorem pqxdhAccept_opt_fields_ok_of_cliExternsOk'
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_opt_fields_ok_of_cliExternsOk X himg hWF hOk
    (pqxdhHkdfExtract_ok_of_cliExternsOk X himg hOk)
    (pqxdhHkdfExpandMultiInfo_ok_of_cliExternsOk X himg hOk)

theorem pqxdhAccept_ok_of_externsOk'
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_ok_of_externsOk X himg hWF hOk
    (pqxdhHkdfExtract_ok_of_externsOk X himg hOk)
    (pqxdhHkdfExpandMultiInfo_ok_of_externsOk X himg hOk)

theorem pqxdhAccept_ok_of_cliExternsOk'
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_ok_of_cliExternsOk X himg hWF hOk
    (pqxdhHkdfExtract_ok_of_cliExternsOk X himg hOk)
    (pqxdhHkdfExpandMultiInfo_ok_of_cliExternsOk X himg hOk)

theorem accept_ok_of_externsOk'
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_opt_fields_ok_of_externsOk' X himg hWF hOk

theorem accept_ok_of_cliExternsOk'
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_opt_fields_ok_of_cliExternsOk' X himg hWF hOk

end CryptoVerification.E2E.Pqxdh.ResponderCore
