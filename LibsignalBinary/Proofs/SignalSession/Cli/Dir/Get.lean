/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Proof

/-!
# Verification of `<signal_session::stores::Dir>::get`

Verifies `Dir::get` (`0x70`-byte frame) against `dirGetSpec rd pathOk A img stk`:
searches the in-memory `changed` table via `bcmp` (cloning the cached `Vec<u8>` on hit), and on miss
joins `self.path` with `name` (`pathOf`), invokes `read_file` under `FsInv`, formats `"file could
not be read"` (`speAt`) on I/O failure, and deallocates any temporary path buffer before returning.
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.Get

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- `Dir::get` satisfies `dirGetSpec rd pathOk A img stk` at any 4 KiB-aligned image base, given
allocator/memcpy/`bcmp` contracts, `path`, `read_file`, trace soundness, and `< 2 ^ 32` `pathOk` lengths. -/
theorem dirGet_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
      (readFileSpec rd pathOk A img readStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) := by
  exact dirGet_ok_of_loads hC hRO hBcmp hPath hRead hFs hstk hb himg hpathLen

/-- `Dir::get` satisfies `dirGetSpec rd pathOk A img stk` from `MemcpyROOkExtX img ext`. -/
theorem dirGet_ok_of_deps_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsX img A ext)
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
      (readFileSpec rd pathOk A img readStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) :=
  dirGet_ok_of_loads_roX hC hRO hBcmp hPath hRead hFs hstk hb himg hpathLen

/-- `Dir::get` satisfies `dirGetSpec rd pathOk A img stk` from a stacked read-only `memcpy` contract (`roStk ≤ extHookStack`). -/
theorem dirGet_ok_of_deps_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk roStk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
      (readFileSpec rd pathOk A img readStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) :=
  dirGet_ok_of_loads_withStack hC hRO hBcmp hPath hRead hFs hstk hb himg hpathLen hro

end CryptoVerification.SignalSession.Cli.Get
