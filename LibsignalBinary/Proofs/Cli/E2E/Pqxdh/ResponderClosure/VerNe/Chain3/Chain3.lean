/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Entry
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Exit
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Key
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MK
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Srk

/-!
# `message::merge<Chain> [local#5]` Slice Assembly

Assembles the verified entry (`chain3Entry_ok`), SRK (`chain3Srk_ok`), ChainKey (`chain3ChainKey_ok`),
MessageKeys (`chain3MessageKeys_ok`), and exit (`chain3Exit_ok`) slices into `Chain3OkAtWExt`
(`chain3_ok_of_callees_ext` and `chain3_ok_of_callees`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.E2E.Record (A0)

/-- `Chain3OkAtWExt A` from the callee contracts and the ChainKey / MessageKeys slice statements. -/
theorem chain3OkAtW_of_slices_ext {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hC : Chain3CalleesWExt A img ext) (hCk : Chain3ChainKeyStmtExt A img ext)
    (hMk : Chain3MessageKeysStmtExt A img ext) :
    Chain3OkAtWExt A img ext :=
  chainMerge3W_ok_ext img ext hC (chain3Entry_ok_ext img ext) (chain3Srk_ok_ext img ext) hCk hMk
    (chain3Exit_ok_ext img ext)

/-- `Chain3OkAtWExt A` (`= Chain5OkAtWExt A`) from `Chain3CalleesWExt A img ext` alone. -/
theorem chain3_ok_of_callees_ext {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hC : Chain3CalleesWExt A img ext) :
    Chain3OkAtWExt A img ext :=
  chain3OkAtW_of_slices_ext img ext hC (chain3ChainKey_ok_ext img ext)
    (chain3MessageKeys_ok_ext img ext)

theorem chain3OkAtW_of_slices (img : Obj.Image) (ext : String → Option (State → State))
    (hC : Chain3CalleesW img ext) (hCk : Chain3ChainKeyStmt img ext)
    (hMk : Chain3MessageKeysStmt img ext) :
    Chain3OkAtW img ext :=
  chainMerge3W_ok img ext hC (chain3Entry_ok img ext) (chain3Srk_ok img ext) hCk hMk
    (chain3Exit_ok img ext)

theorem chain3_ok_of_callees (img : Obj.Image) (ext : String → Option (State → State))
    (hC : Chain3CalleesW img ext) :
    Chain3OkAtW img ext :=
  chain3OkAtW_of_slices img ext hC (chain3ChainKey_ok img ext) (chain3MessageKeys_ok img ext)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
