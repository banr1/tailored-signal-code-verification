/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrow
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne

/-!
# Closed `RawVec<(String, Vec<u8>)>::grow_one` Verification

Composes `growOneDir_ok_of_deps` with `cliFinishGrow_ok_x` so `grow_one` on `Dir.changed` satisfies
`growOneDirSpec` directly from `AllocContractsX`.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.GrowOne

open Arm64 ProofLib CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-- `grow_one` satisfies `growOneDirSpec A img stk` at any 4 KiB-aligned image base under `AllocContractsX`. -/
theorem growOneDir_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hA : AllocContractsX img A ext)
    (hstk : 0x40 + finishGrowStackX ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img stk) :=
  growOneDir_ok_of_deps (FinishGrow.cliFinishGrow_ok_x hA) hstk hb

end CryptoVerification.SignalSession.Cli.GrowOne
