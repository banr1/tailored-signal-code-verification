/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Defs

/-!
# `Chain::clone [local#3]` Contract Predicates for the CLI Image

Defines the symbol name and `subroutine_ok` target predicates (`ChainCloneOk*`,
`SenderChainCloneOk*`) for `Chain::clone [local#3]` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Receiver-Chain Clone Predicates -/

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName : String :=
  "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]"

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName)
    (chainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName)
    (chainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName)
    (chainCloneSpec A)

/-! ## Sender-Chain Clone Predicates -/

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName)
    (senderChainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName)
    (senderChainCloneSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chainCloneName)
    (senderChainCloneSpec A)

end CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
