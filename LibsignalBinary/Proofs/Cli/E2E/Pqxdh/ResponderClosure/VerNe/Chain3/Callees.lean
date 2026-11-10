/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Chain3

/-!
# `message::merge<Chain> [local#5]` Closure from `Chain3CalleeKit`

Discharges `Chain3CalleesWExt` and `Chain3OkAtWExt` (`Chain5OkAtWExt`) for
`prost::encoding::message::merge::<Chain, &mut &[u8]> [local#5]` from `Chain3CalleeKitExt`,
`Obj.Loads libsignalSessionImage img`, and `AllocContractsX`, discharging `grow_one<MessageKey>` via
`growOneMessageKey_ok_ext_x`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.E2E.Record (A0)

/-- `Chain3CalleesWExt A img ext` from `kit : Chain3CalleeKitExt A`,
`Obj.Loads libsignalSessionImage img`, and `LibsignalTripleRatchet.AllocContractsX img A ext`. -/
theorem chain3CalleesW_of_kit_ext {A : RustAlloc} (kit : Chain3CalleeKitExt A)
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads CryptoVerification.libsignalSessionImage img)
    (hAlloc : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Chain3CalleesWExt A img ext where
  dv := kit.dv img ext himg hAlloc
  bm := kit.bm img ext himg hAlloc
  grow := growOneMessageKey_ok_ext_x (c3_stage1Alloc_of_allocContractsX hAlloc)

/-- `Chain3OkAtWExt A img ext` from `kit`, image load, and `AllocContractsX`. -/
theorem chain3OkAtW_of_kit_ext {A : RustAlloc} (kit : Chain3CalleeKitExt A)
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads CryptoVerification.libsignalSessionImage img)
    (hAlloc : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Chain3OkAtWExt A img ext :=
  chain3_ok_of_callees_ext img ext (chain3CalleesW_of_kit_ext kit himg hAlloc)

/-- Top-level `Chain5OkAtWExt A img ext` contract from `Chain3CalleeKitExt A`, `Obj.Loads`, and `AllocContractsX`. -/
theorem chainMerge5_ok_ext {A : RustAlloc} (kit : Chain3CalleeKitExt A)
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads CryptoVerification.libsignalSessionImage img)
    (hAlloc : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Chain5OkAtWExt A img ext :=
  chain3OkAtW_of_kit_ext kit himg hAlloc

theorem chain3CalleesW_of_kit (kit : Chain3CalleeKit)
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads CryptoVerification.libsignalSessionImage img)
    (hAlloc : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A0 ext) :
    Chain3CalleesW img ext :=
  chain3CalleesW_of_kit_ext kit himg hAlloc

theorem chain3OkAtW_of_kit (kit : Chain3CalleeKit)
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads CryptoVerification.libsignalSessionImage img)
    (hAlloc : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A0 ext) :
    Chain3OkAtW img ext := by
  rw [← Chain3OkAtWExt_A0]
  exact chain3OkAtW_of_kit_ext kit himg hAlloc

/-- Top-level `Chain5OkAtW img ext` contract at `A0` from `Chain3CalleeKit`, `Obj.Loads`, and `AllocContractsX`. -/
theorem chainMerge5_ok (kit : Chain3CalleeKit)
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads CryptoVerification.libsignalSessionImage img)
    (hAlloc : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A0 ext) :
    Chain5OkAtW img ext :=
  chain3OkAtW_of_kit kit himg hAlloc

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
