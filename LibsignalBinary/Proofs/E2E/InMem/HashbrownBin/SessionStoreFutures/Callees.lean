/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.ReserveRehash
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Transport

/-!
# Callee Names and Offset Guards for `InMemSessionStore` Future Closures
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

abbrev stringCloneName : String :=
  "<alloc::string::String as core::clone::Clone>::clone"

theorem stringCloneName_fnOff :
    libsignalSessionCode.fnOff stringCloneName = num% (ls_off% "<alloc::string::String as core::clone::Clone>::clone") :=
  (ls_lemma% fnOff "<alloc::string::String as core::clone::Clone>::clone")

abbrev sessionCloneName : String :=
  "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"

theorem sessionCloneName_fnOff :
    libsignalSessionCode.fnOff sessionCloneName = num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone") :=
  (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone")

abbrev vecVecCloneName : String :=
  "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"

theorem vecVecCloneName_fnOff :
    libsignalSessionCode.fnOff vecVecCloneName = num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") :=
  (ls_lemma% fnOff "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")

theorem dropSessionStructureLocal1Name_fnOff :
    libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
  (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")

theorem reserveRehashSessionEmpty_ok_at_storeSessionClosure
    (b : BitVec 64) (ext : HookMap) (A : RustAlloc) (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr storeSessionClosureName - bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore as libsignal_protocol::storage::traits::SignedPreKeyStore>::save_signed_pre_key::{closure#0}" + 324))
      (reserveRehashSessionEmptySpec A) :=
  inImage_ok_back storeSessionClosure_fnOff reserveRehashSession_fnOff (d := num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore as libsignal_protocol::storage::traits::SignedPreKeyStore>::save_signed_pre_key::{closure#0}" + 324)) (by decide)
    (reserveRehashSessionEmpty_ok b ext A hHooks)

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
