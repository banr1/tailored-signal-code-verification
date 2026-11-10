/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs

/-!
# Call-Distance Transport Helpers for Compiled `hashbrown` Proofs

Transports `subroutine_ok` contracts along fixed positive (`inImage_ok_at`) or negative
(`inImage_ok_back`) code offsets on `RebasedProg b ext`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet

/-- Move a callee's `subroutine_ok` contract to `fnAddr caller + k#64` when `callee` is `k` bytes
after `caller` (`callerOff + k = calleeOff`). -/
theorem inImage_ok_at {α : Type} {b : BitVec 64} {ext : HookMap} {spec : Spec α}
    {caller callee : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff caller + k = libsignalSessionCode.fnOff callee)
    (h : subroutine_ok (RebasedProg b ext) ((RebasedProg b ext).fnAddr callee) spec) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr caller + BitVec.ofNat 64 k) spec := by
  rwa [← Program.fnAddr_rel rfl rfl hk]

/-- Move a callee's `subroutine_ok` contract to `fnAddr caller - d#64` when `callee` is `d` bytes
before `caller` (`calleeOff + d = callerOff`). -/
theorem inImage_ok_back {α : Type} {b : BitVec 64} {ext : HookMap} {spec : Spec α}
    {caller callee : String} {callerOff calleeOff d : Nat}
    (hcaller : libsignalSessionCode.fnOff caller = callerOff)
    (hcallee : libsignalSessionCode.fnOff callee = calleeOff)
    (hd : calleeOff + d = callerOff)
    (h : subroutine_ok (RebasedProg b ext) ((RebasedProg b ext).fnAddr callee) spec) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr caller - BitVec.ofNat 64 d) spec := by
  rwa [← Program.fnAddr_back hcaller hcallee hd]

end CryptoVerification.E2E.InMem.HashbrownBin
