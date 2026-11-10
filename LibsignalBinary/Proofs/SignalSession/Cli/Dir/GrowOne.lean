/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Sym

/-!
# Verification of `RawVec<(String, Vec<u8>)>::grow_one`

Verifies `RawVec<(String, Vec<u8>)>::grow_one` (`0x40`-byte frame) against `growOneDirSpec A img stk`:
doubles capacity with floor 4 (`max (2 * cap) 4`), invokes `finish_grow` at element alignment 8 and
stride 48 over the `dirEntryAt` headers while framing per-entry heap buffers, and panics via
`handle_error` only after `allocFailedEvent`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.GrowOne

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- `grow_one` (`Dir.changed`) satisfies `growOneDirSpec A img stk` at any 4 KiB-aligned image base, given `finish_grow`. -/
theorem growOneDir_ok_of_deps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hFG : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliFinishGrowName)
      ((finishGrowSpecX A).inImage img))
    (hstk : 0x40 + finishGrowStackX ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img stk) := by
  let _ := hb
  exact Helpers.growOneDir_of_bytes (Helpers.growOneDirBytes_ok hFG) hstk

end CryptoVerification.SignalSession.Cli.GrowOne

