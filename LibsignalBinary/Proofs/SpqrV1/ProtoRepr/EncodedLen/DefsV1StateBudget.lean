/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1State

/-!
# `VmPreserved` Specifications for `V1State::encoded_len`

`VmPreserved`-augmented Hoare contracts `v1StateEncodedLen{RoPinned,Ro,Pinned,}Spec` for
zero-allocation budget transport across `V1State::encoded_len`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget

open _root_.Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withVmPreserved)
open CryptoVerification.SpqrV1.ProtoRepr
  (V1StateEncodedLenPinnedGhost V1StateEncodedLenGhost)

def v1StateEncodedLenRoPinnedSpec (A : RustAlloc) (roBase : BitVec 64) :
    Spec V1StateEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec A roBase)

def v1StateEncodedLenRoSpec (A : RustAlloc) (roBase : BitVec 64) :
    Spec V1StateEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoSpec A roBase)

def v1StateEncodedLenPinnedSpec (A : RustAlloc) : Spec V1StateEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenPinnedSpec A)

def v1StateEncodedLenSpec (A : RustAlloc) : Spec V1StateEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenSpec A)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
