/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1

/-!
# `VmPreserved` Specifications for Polynomial and Chunked `encoded_len`

`VmPreserved`-augmented Hoare contracts for `Polynomial{Decoder,Encoder}::encoded_len` and
`V1State.Chunked.{Ct1Sampled,HeaderSent}::encoded_len`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget

open _root_.Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open CryptoVerification.SpqrV1.ProtoRepr
  (PolynomialDecoderEncodedLenPinnedGhost PolynomialDecoderEncodedLenGhost
   PolynomialEncoderEncodedLenPinnedGhost PolynomialEncoderEncodedLenGhost
   ChunkedCt1SampledEncodedLenPinnedGhost ChunkedCt1SampledEncodedLenGhost
   ChunkedHeaderSentEncodedLenPinnedGhost ChunkedHeaderSentEncodedLenGhost)

def polynomialDecoderEncodedLenPinnedSpec (A : RustAlloc) :
    Spec PolynomialDecoderEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.polynomialDecoderEncodedLenPinnedSpec A)

def polynomialDecoderEncodedLenSpec (A : RustAlloc) : Spec PolynomialDecoderEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.polynomialDecoderEncodedLenSpec A)

def polynomialEncoderEncodedLenPinnedSpec (A : RustAlloc) :
    Spec PolynomialEncoderEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.polynomialEncoderEncodedLenPinnedSpec A)

def polynomialEncoderEncodedLenSpec (A : RustAlloc) : Spec PolynomialEncoderEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.polynomialEncoderEncodedLenSpec A)

def chunkedCt1SampledEncodedLenPinnedSpec (A : RustAlloc) :
    Spec ChunkedCt1SampledEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec A)

def chunkedCt1SampledEncodedLenSpec (A : RustAlloc) : Spec ChunkedCt1SampledEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenSpec A)

def chunkedHeaderSentEncodedLenPinnedSpec (A : RustAlloc) :
    Spec ChunkedHeaderSentEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLenPinnedSpec A)

def chunkedHeaderSentEncodedLenSpec (A : RustAlloc) : Spec ChunkedHeaderSentEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLenSpec A)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
