/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.ToOwned

/-!
# Verification of `<signal_session::stores::Dir>::put::<&str>`

Verifies `Dir::put::<&str>` (`0x50`-byte frame) against `dirPutStrSpec A img stk`:
clones the borrowed `name` slice (read-only or heap-owned) via `to_owned()`, then updates
`Dir.changed` via linear `bcmp` scan, value replacement + tail-deallocation on hit, or `grow_one` +
append on miss.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.PutStr

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- `Dir::put::<&str>` satisfies `dirPutStrSpec A img stk` at any 4 KiB-aligned image base, given
allocator/memcpy/`bcmp` contracts, read-only `memcpy`, and `grow_one`. -/
theorem dirPutStr_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img stk) := by
  let _ := hb
  exact Helpers.dirPutStr_ok_main hC hRO hBcmp hGrow hstk

/-- `Dir::put::<&str>` satisfies `dirPutStrSpec A img stk` from `MemcpyROOkExtX img ext`. -/
theorem dirPutStr_ok_of_deps_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img stk) := by
  let _ := hb
  exact Helpers.dirPutStr_ok_main_roX hC hRO hBcmp hGrow hstk

/-- `Dir::put::<&str>` satisfies `dirPutStrSpec A img stk` from a stacked read-only `memcpy` contract (`roStk ≤ extHookStack`). -/
theorem dirPutStr_ok_of_deps_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img stk) := by
  let _ := hb
  exact Helpers.dirPutStr_ok_main_withStack hC hRO hBcmp hGrow hstk hro

end CryptoVerification.SignalSession.Cli.PutStr
