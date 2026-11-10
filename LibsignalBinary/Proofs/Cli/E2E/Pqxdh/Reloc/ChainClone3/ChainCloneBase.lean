/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBase
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneFetch
import ProofLib.SepLogic.WPp

/-!
# `Chain::clone` Stack Frame & Address Normalization Helpers

Stack frame decomposition (`208` B), register-read normalization, and byte-packing helpers for
`<session_structure::Chain as Clone>::clone` on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.ChainClone3

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.ProtoChainClone3Ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name)
    (protoChainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.ProtoChainClone3Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name)
    (protoChainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.ChainClone3Ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name)
    (chainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.ChainClone3Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name)
    (chainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.SenderChainClone3Ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name)
    (senderChainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.SenderChainClone3Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name)
    (senderChainCloneSpec A)

/-! ## Stack Frame Decomposition and Address Normalization -/

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace BS5

end BS5

end CryptoVerification.LibsignalTripleRatchet.ChainClone3
