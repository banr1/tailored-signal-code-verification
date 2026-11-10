/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Library.Calls
public import VerifiedLibraries.Musl.Spec

/-!
# Shared Helpers for Musl String Proofs

Provides `Arm64.Obj.fetch_patchCalls_b` for fetching relocated unconditional `b` tail-call words
(used by `bcmp` -> `memcmp` and `memmove` -> `memcpy`).
-/

set_option autoImplicit false

@[expose] public section

namespace Arm64.Obj

set_option linter.literalFetch false in
/-- A patched `b` word in `patchCalls calls words a resolve` fetches as an unconditional branch to
    `resolve r.2`. -/
theorem fetch_patchCalls_b {prog : Program} {calls : List (Nat × String)}
    {words : List (BitVec 32)} {a : BitVec 64} {resolve : String → BitVec 64} {r : Nat × String}
    (h : prog.hasWords a (patchCalls calls words a resolve))
    (hr : calls.find? (·.1 == r.1) = some r) (h4 : r.1 % 4 = 0)
    (hlen : r.1 / 4 < words.length)
    (hw : words[r.1 / 4] &&& 0xfc000000#32 = 0x14000000#32)
    (hrange : BranchInRange (a + BitVec.ofNat 64 r.1) (resolve r.2)) :
    prog.fetch (a + BitVec.ofNat 64 r.1) =
      some (.b (resolve r.2 - (a + BitVec.ofNat 64 r.1))) := by
  have hj : r.1 = 4 * (r.1 / 4) := by omega
  have hlen' : r.1 / 4 < (patchCalls calls words a resolve).length := by
    simp [patchCalls, hlen]
  have hf := Program.fetch_of_hasWords h (r.1 / 4) hlen'
  rw [← hj] at hf
  rw [hf, show (patchCalls calls words a resolve)[r.1 / 4] =
      branchWord words[r.1 / 4] (a + BitVec.ofNat 64 r.1) (resolve r.2) by
    simp only [patchCalls, List.getElem_mapIdx]
    rw [← hj, hr]]
  exact decode_branchWord_b hw hrange

end Arm64.Obj
