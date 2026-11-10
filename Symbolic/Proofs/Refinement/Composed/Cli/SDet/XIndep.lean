/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir

/-!
# Independence of PQXDH CLI Models from `UnreachedPqxdhPrimitives`

Proves that `initiateState`, `recvPrekeyState`, `pqInitModel`, and `pqRecvPrekeyModel` are
independent of the `UnreachedPqxdhPrimitives` parameter.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli.SDet

open CryptoGames (Party)
open CryptoVerification.E2E (PreKeyBundleFields PreKeyMessageFields ResponderPreKeySecrets LocalIdentity UnreachedPqxdhPrimitives PEParams
  initiateTapeLen initiateState recvPrekeyState modelPrims)
open CryptoVerification.SignalSession (PqParty pqInitModel pqRecvPrekeyModel)

private theorem sha256Step_congr {Q Q' : SignalPqxdh.Primitives}
    (h : Q.sha256Compress = Q'.sha256Compress) :
    SignalPqxdh.sha256Step Q = SignalPqxdh.sha256Step Q' := by
  funext s blk
  simp [SignalPqxdh.sha256Step, h]

private theorem sha256Ref_congr {Q Q' : SignalPqxdh.Primitives}
    (h : Q.sha256Compress = Q'.sha256Compress) :
    SignalPqxdh.sha256Ref Q = SignalPqxdh.sha256Ref Q' := by
  funext msg
  simp only [SignalPqxdh.sha256Ref, sha256Step_congr h]

private theorem hmacSha256Ref_congr {Q Q' : SignalPqxdh.Primitives}
    (h : Q.sha256Compress = Q'.sha256Compress) :
    SignalPqxdh.hmacSha256Ref Q = SignalPqxdh.hmacSha256Ref Q' := by
  funext key msg
  simp only [SignalPqxdh.hmacSha256Ref, sha256Ref_congr h]

private theorem hkdfDerive96Ref_congr {Q Q' : SignalPqxdh.Primitives}
    (h : Q.sha256Compress = Q'.sha256Compress) :
    SignalPqxdh.hkdfDerive96Ref Q = SignalPqxdh.hkdfDerive96Ref Q' := by
  funext secrets
  simp only [SignalPqxdh.hkdfDerive96Ref, SignalPqxdh.hkdfExpand96Ref,
    SignalPqxdh.hkdfExtractRef, hmacSha256Ref_congr h]

private theorem sha512Step_congr {Q Q' : SignalPqxdh.Primitives}
    (h : Q.sha512Compress = Q'.sha512Compress) :
    SignalPqxdh.sha512Step Q = SignalPqxdh.sha512Step Q' := by
  funext s blk
  simp [SignalPqxdh.sha512Step, h]

private theorem sha512Ref_congr {Q Q' : SignalPqxdh.Primitives}
    (h : Q.sha512Compress = Q'.sha512Compress) :
    SignalPqxdh.sha512Ref Q = SignalPqxdh.sha512Ref Q' := by
  funext msg
  simp only [SignalPqxdh.sha512Ref, sha512Step_congr h]

private theorem xeddsaVerifyRef_congr {Q Q' : SignalPqxdh.Primitives}
    (h_mte : Q.montToEd = Q'.montToEd)
    (h_cmp : Q.compress = Q'.compress)
    (h_neg : Q.edNeg = Q'.edNeg)
    (h_sw : Q.scalarFromWide = Q'.scalarFromWide)
    (h_sha : Q.sha512 = Q'.sha512)
    (h_sm : Q.scalarFromBytesModOrder = Q'.scalarFromBytesModOrder)
    (h_dsmb : Q.doubleScalarMulBasepoint = Q'.doubleScalarMulBasepoint) :
    SignalPqxdh.xeddsaVerifyRef Q = SignalPqxdh.xeddsaVerifyRef Q' := by
  funext pk m sig
  simp only [SignalPqxdh.xeddsaVerifyRef, h_mte, h_cmp, h_neg, h_sw, h_sha, h_sm, h_dsmb]

private theorem isCanonicalRef_congr {Q Q' : SignalPqxdh.Primitives}
    (h_mte : Q.montToEd = Q'.montToEd)
    (h_tf : Q.isTorsionFree = Q'.isTorsionFree) :
    SignalPqxdh.isCanonicalRef Q = SignalPqxdh.isCanonicalRef Q' := by
  funext pk
  simp only [SignalPqxdh.isCanonicalRef, h_mte, h_tf]

private theorem modelPrims_x25519_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) :
    (modelPrims X P).x25519 = (modelPrims X' P).x25519 := rfl

private theorem modelPrims_x25519Base_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) :
    (modelPrims X P).x25519Base = (modelPrims X' P).x25519Base := rfl

private theorem modelPrims_kemEncaps_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) :
    (modelPrims X P).kemEncaps = (modelPrims X' P).kemEncaps := rfl

private theorem modelPrims_kemDecaps_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) :
    (modelPrims X P).kemDecaps = (modelPrims X' P).kemDecaps := rfl

private theorem modelPrims_hkdfDerive96_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) :
    (modelPrims X P).hkdfDerive96 = (modelPrims X' P).hkdfDerive96 :=
  hkdfDerive96Ref_congr rfl

private theorem modelPrims_isCanonical_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) :
    (modelPrims X P).isCanonical = (modelPrims X' P).isCanonical :=
  isCanonicalRef_congr rfl rfl

private theorem modelPrims_sigVerify_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) :
    (modelPrims X P).sigVerify = (modelPrims X' P).sigVerify :=
  xeddsaVerifyRef_congr rfl rfl rfl rfl (sha512Ref_congr rfl) rfl rfl

private theorem initiateKeys_modelPrims_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams)
    (inp : SignalPqxdh.InitiateKeysInput) :
    SignalPqxdh.Model.initiateKeys (modelPrims X P) inp =
      SignalPqxdh.Model.initiateKeys (modelPrims X' P) inp := by
  unfold SignalPqxdh.Model.initiateKeys
  rw [modelPrims_sigVerify_xindep X X' P,
      modelPrims_kemEncaps_xindep X X' P,
      modelPrims_x25519Base_xindep X X' P,
      modelPrims_x25519_xindep X X' P,
      modelPrims_hkdfDerive96_xindep X X' P]

private theorem acceptKeys_modelPrims_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams)
    (inp : SignalPqxdh.AcceptKeysInput) :
    SignalPqxdh.Model.acceptKeys (modelPrims X P) inp =
      SignalPqxdh.Model.acceptKeys (modelPrims X' P) inp := by
  unfold SignalPqxdh.Model.acceptKeys
  rw [modelPrims_isCanonical_xindep X X' P,
      modelPrims_x25519_xindep X X' P,
      modelPrims_kemDecaps_xindep X X' P,
      modelPrims_hkdfDerive96_xindep X X' P]

theorem initiateState_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) (party : Party) (me : LocalIdentity)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    initiateState X P party me b t = initiateState X' P party me b t := by
  unfold initiateState
  rw [initiateKeys_modelPrims_xindep X X' P]

theorem recvPrekeyState_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) (party : Party) (me : LocalIdentity)
    (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256) :
    recvPrekeyState X P party me k m rc = recvPrekeyState X' P party me k m rc := by
  unfold recvPrekeyState
  rw [acceptKeys_modelPrims_xindep X X' P]

theorem pqInitModel_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    pqInitModel X P st b t = pqInitModel X' P st b t := by
  unfold pqInitModel
  rw [initiateState_xindep X X' P]

theorem pqRecvPrekeyModel_xindep (X X' : UnreachedPqxdhPrimitives) (P : PEParams) (st : PqParty)
    (m : PreKeyMessageFields) (rc : BitVec 256) :
    pqRecvPrekeyModel X P st m rc = pqRecvPrekeyModel X' P st m rc := by
  simp only [pqRecvPrekeyModel, recvPrekeyState_xindep X X' P]

end DY.Libsignal.Composed.Refinement.Cli.SDet
