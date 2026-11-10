/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Ext

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt

open Arm64 ProofLib
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt extHookStack)
open CryptoVerification.SpqrV1.Alloc (MemcpyROOkExtX memcpyROOkExtX_of_hookSat_withStack)
open CryptoVerification.SignalSession.Cli
  (pathName pathSpec dirGetName dirGetSpec bundleReadName bundleReadSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Path (path_ok_of_deps_roX)
open CryptoVerification.SignalSession.Cli.Get (dirGet_ok_of_deps_roX)
open CryptoVerification.SignalSession.Cli.RunProofs
  (cliConcatName cliConcat2Spec cliConcat2_ok_ext)
open CryptoVerification.SignalSession.Cli.RunSkeleton
  (RunHooksExt RunBudgets RunSlots RunCallees pathNeed base_aligned
   reserve_ok_ext bundleRead_ok_of_path_ext)

/-!
# Read-Only `memcpy` Callees from `RunHooksExt`

Derives `concat_ok_ext`, `path_ok_ext`, `dirGet_ok_ext`, and `bundleRead_ok_ext` from the
contract-backed `RunHooksExt` bundle.
-/

theorem memcpyRO_okExtX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hh : RunHooksExt img A ext) :
    MemcpyROOkExtX img ext :=
  memcpyROOkExtX_of_hookSat_withStack (Nat.le_refl _) hh.memcpyRO_X

theorem concat_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hh : RunHooksExt img A ext) (stk : Nat)
    (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliConcatName)
      ((cliConcat2Spec A stk).inImage img) :=
  cliConcat2_ok_ext hh.alloc hh.memcpyRO_X stk hstk hstk64

theorem path_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) {stk : Nat}
    (hstk : pathNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName) (pathSpec A img stk) :=
  path_ok_of_deps_roX hh.alloc (memcpyRO_okExtX hh)
    (reserve_ok_ext hh (Nat.le_refl _)) hstk (base_aligned himg)

theorem dirGet_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {σ : RunSlots} (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) (hc : RunCallees img A ext B σ) {stk : Nat}
    (hstk : B.dirGetNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec cliIo.rd cliWrOk A img stk) :=
  dirGet_ok_of_deps_roX himg (fun _ h => h.2) hh.alloc (memcpyRO_okExtX hh)
    hh.bcmp (path_ok_ext himg hh (Nat.le_refl _))
    hc.readFile hh.fs hstk (base_aligned himg)

theorem bundleRead_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {σ : RunSlots} (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext) (hc : RunCallees img A ext B σ) {stk : Nat}
    (hstk : B.bundleReadNeed ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName)
      (bundleReadSpec cliIo.rd cliWrOk A img stk) :=
  bundleRead_ok_of_path_ext himg hh (path_ok_ext himg hh (Nat.le_refl _)) hc hstk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SignalSession.Cli.RunSkeleton
export LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt
  (memcpyRO_okExtX concat_ok_ext path_ok_ext dirGet_ok_ext bundleRead_ok_ext)
end CryptoVerification.SignalSession.Cli.RunSkeleton
-- AUTO-BRIDGE END
