/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs

/-!
# Callee Symbols and Contracts for `try_decrypt_from_record`

Symbol names and `subroutine_ok` predicates for `drop_glue<SessionStructure> [local#2]` and
`try_decrypt_from_record::{closure#0}` (log-off path) in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalSession

/-- Symbol name of `core::ptr::drop_glue::<SessionStructure> [local#2]`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]"

/-- Symbol name of `try_decrypt_from_record::<Coins>::{closure#0}`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName : String :=
  "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}"

/-- `subroutine_ok` predicate for `drop_glue<SessionStructure> [local#2]` on `tripleRatchetProgAtExt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name)
    (dropSessionStructureLocal2Spec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name)
    (dropSessionStructureLocal2Spec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name)
    (dropSessionStructureLocal2Spec A)

/-- `subroutine_ok` predicate for `try_decrypt_from_record::{closure#0}` (log-off path) on
`tripleRatchetProgAtExt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOkExt (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName)
    ((logClosureSpec img).inImage img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName)
    ((logClosureSpec img).inImage img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName)
    ((logClosureSpec img).inImage img)

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
