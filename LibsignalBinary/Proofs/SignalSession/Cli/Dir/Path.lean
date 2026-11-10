/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Steps

/-!
# Verification of `signal_session::stores::path`

Verifies `signal_session::stores::path` (`0x70`-byte frame) against `pathSpec A img stk`:
clones `dir` (`dir.to_owned()`), unconditionally reserves and appends `'/'`, reserves and copies
`name` (`dir ++ "/" ++ name = pathOf dir name` for `dir ≠ []`), and writes `{cap, ptr, len}` to the
return slot.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Path

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- `path` satisfies `pathSpec A img stk` at any 4 KiB-aligned image base, given allocator/memcpy
contracts, read-only `memcpy`, and `do_reserve_and_handle` (stack `resStack`). -/
theorem path_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hstk : 0x70 + max resStack extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img stk) :=
  Helpers.path_ok_of_deps_core hC hRO hRes hstk hb

/-- `path` satisfies `pathSpec A img stk` from `MemcpyROOkExtX img ext`. -/
theorem path_ok_of_deps_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext)
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hstk : 0x70 + max resStack extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img stk) :=
  Helpers.path_ok_of_deps_core_roX hC hRO hRes hstk hb

/-- `path` satisfies `pathSpec A img stk` from a stacked read-only `memcpy` contract (`roStk ≤ extHookStack`). -/
theorem path_ok_of_deps_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack stk roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (hRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img))
    (hstk : 0x70 + max resStack extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img stk) :=
  Helpers.path_ok_of_deps_core_withStack hC hRO hRes hstk hb hro

end CryptoVerification.SignalSession.Cli.Path
