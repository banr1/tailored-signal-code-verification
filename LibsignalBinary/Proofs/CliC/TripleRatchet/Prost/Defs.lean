/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.Defs

/-!
# Symbol and Contract Definitions for `CliC` `drop_glue<DecodeError>`

Defines `dropDecodeErrorName` and `DropDecodeErrorOk` for
`core::ptr::drop_glue::<prost::error::DecodeError>` in `CliC`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

abbrev _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName : String :=
  "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]"

def _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.DropDecodeErrorOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeErrorName)
    (dropDecodeErrorSpec A)

end CryptoVerification.LibsignalTripleRatchet.Prost
