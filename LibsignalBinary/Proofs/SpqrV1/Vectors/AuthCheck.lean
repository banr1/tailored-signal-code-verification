/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Proofs.SpqrV1.Vectors.Authenticator
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Authenticator

/-!
# Differential Vector Checks for `Auth.lean`

Checks `Auth.lean` against all `authUpdateVectors` and `authMacVerifyVectors` in
`Vectors/Authenticator.lean` via `#guard` and `decide +kernel`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Vectors.AuthCheck

open CryptoGames.HMAC
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalSpqrV1.Tests (sha256Compress)
open CryptoVerification.SpqrV1.Vectors.Authenticator

/-- Check one `AuthUpdateVec` entry against `Authenticator.update`, `Authenticator.new` (when starting
from 32 zero bytes), and `intoPb`/`fromPb` round-trip. -/
def checkUpdateVec (v : AuthUpdateVec) : Bool :=
  let a0 : Authenticator := { rootKey := v.rootKeyBefore, macKey := v.macKeyBefore }
  let a1 := a0.update sha256Compress v.epoch v.inputKey
  let newOk :=
    if v.rootKeyBefore == List.replicate 32 0#8 && v.macKeyBefore == List.replicate 32 0#8 then
      Authenticator.new sha256Compress v.inputKey v.epoch == a1
    else
      true
  a1.rootKey == v.rootKeyAfter &&
  a1.macKey == v.macKeyAfter &&
  newOk &&
  Authenticator.fromPb a1.intoPb == a1

def checkMacVec (v : AuthMacVerifyVec) : Bool :=
  let a : Authenticator := { rootKey := v.rootKey, macKey := v.macKey }
  a.macHdr sha256Compress v.epoch v.payload == .ok v.hdrMac &&
  a.macCt sha256Compress v.epoch v.payload == .ok v.ctMac

/-- Check `verifyHdr`, `verifyCt`, `verifyHdrError`, `verifyCtError`, and `compareBounds` panic on
one `AuthMacVerifyVec` entry. -/
def checkVerifyVec (v : AuthMacVerifyVec) : Bool :=
  let a : Authenticator := { rootKey := v.rootKey, macKey := v.macKey }
  let expectedHdr : Except AuthError Unit := if v.verifyHdrOk then .ok () else .error .invalidHdrMac
  let expectedCt : Except AuthError Unit := if v.verifyCtOk then .ok () else .error .invalidCtMac
  let expectedHdrErr : Except Error Unit := if v.verifyHdrOk then .ok () else .error .macVerifyFailed
  let expectedCtErr : Except Error Unit := if v.verifyCtOk then .ok () else .error .macVerifyFailed
  a.verifyHdr sha256Compress v.epoch v.payload v.candidateMac == .ok expectedHdr &&
  a.verifyCt sha256Compress v.epoch v.payload v.candidateMac == .ok expectedCt &&
  a.verifyHdrError sha256Compress v.epoch v.payload v.candidateMac == .ok expectedHdrErr &&
  a.verifyCtError sha256Compress v.epoch v.payload v.candidateMac == .ok expectedCtErr &&
  a.verifyHdr sha256Compress v.epoch v.payload (v.candidateMac ++ [0#8]) == .error .compareBounds &&
  a.verifyCt sha256Compress v.epoch v.payload (v.candidateMac ++ [0#8]) == .error .compareBounds

def checkMacVerifyVec (v : AuthMacVerifyVec) : Bool :=
  checkMacVec v && checkVerifyVec v

#guard authUpdateVectors.all checkUpdateVec
#guard authMacVerifyVectors.all checkMacVerifyVec

end CryptoVerification.SpqrV1.Vectors.AuthCheck
