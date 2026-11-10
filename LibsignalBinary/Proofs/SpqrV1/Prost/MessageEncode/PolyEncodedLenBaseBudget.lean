/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase

/-!
# `VmPreserved` Specifications for `PolynomialDecoder::encoded_len` and `PolynomialEncoder::encoded_len`

Defines `VmPreserved`-strengthened (`0`-allocation) contracts
`polynomial{Decoder,Encoder}EncodedLen{Pinned,}Spec` and `subroutine_ok_withMsgEnc48CS_of_no_panic`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget

open Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (PolynomialDecoderEncodedLenPinnedGhost PolynomialDecoderEncodedLenGhost
   PolynomialEncoderEncodedLenPinnedGhost PolynomialEncoderEncodedLenGhost
   withMsgEnc48CS subroutine_ok_withMsgEnc48CS_ext)

def polynomialDecoderEncodedLenPinnedSpec (A : RustAlloc) :
    Spec PolynomialDecoderEncodedLenPinnedGhost :=
  withVmPreserved
    (CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenPinnedSpec A)

def polynomialDecoderEncodedLenSpec (A : RustAlloc) : Spec PolynomialDecoderEncodedLenGhost :=
  withVmPreserved
    (CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialDecoderEncodedLenSpec A)

def polynomialEncoderEncodedLenPinnedSpec (A : RustAlloc) :
    Spec PolynomialEncoderEncodedLenPinnedGhost :=
  withVmPreserved
    (CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialEncoderEncodedLenPinnedSpec A)

def polynomialEncoderEncodedLenSpec (A : RustAlloc) : Spec PolynomialEncoderEncodedLenGhost :=
  withVmPreserved
    (CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialEncoderEncodedLenSpec A)

/-- Any non-panicking `subroutine_ok` (`spec.onPanic = fun _ _ _ => ⌜False⌝`) automatically lifts
    to `withMsgEnc48CS s0 spec`. -/
theorem subroutine_ok_withMsgEnc48CS_of_no_panic {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hok : subroutine_ok prog entry spec)
    (_hnoPanic : ∀ x s1 sf, spec.onPanic x s1 sf = ⌜False⌝) (s0 : State) :
    subroutine_ok prog entry (withMsgEnc48CS s0 spec) :=
  subroutine_ok_withMsgEnc48CS_ext s0 hok

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget
