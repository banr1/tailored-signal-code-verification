/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh.TopLevel
open Arm64 ProofLib

/-- Split `memRegion (sp3 + 1824#64) 560` (`coroPtr + 0x2c8 .. + 0x4f8`) into the exact
coroutine slots consumed by `ResponderClosure.stageP1_ok` plus the remaining unaccessed regions. -/
theorem coro_1824_560_split_for_p1 (sp3 : BitVec 64) :
    let coroPtr := sp3 + 1112#64
    memRegion (sp3 + 1824#64) 560 =
      (∃∗ b_4f2 : BitVec 8, ∃∗ u_3a0 : BitVec 64, ∃∗ u_398 : BitVec 64, ∃∗ b_390 : BitVec 8,
        cells (coroPtr + 0x2c8#64) 25 ∗
        ((coroPtr + 0x390#64) ↦₈ b_390) ∗
        ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
        ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
        cells (coroPtr + 0x428#64) 8 ∗
        cells (coroPtr + 0x490#64) 4 ∗
        ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
        memRegion (coroPtr + 0x391#64) 7 ∗
        memRegion (coroPtr + 0x3a8#64) 128 ∗
        memRegion (coroPtr + 0x468#64) 40 ∗
        memRegion (coroPtr + 0x4b0#64) 66 ∗
        memRegion (coroPtr + 0x4f3#64) 5) := by
  dsimp only
  have h1cell (a : BitVec 64) : memRegion a 8 = (∃∗ v : BitVec 64, a ↦₆₄ v) := by
    rw [ProofLib.memRegion_cells a 1 (by decide)]
    simp only [cells, sepConj_emp]
  rw [memRegion_split (sp3 + 1824#64) 200 360 (by decide),
      memRegion_split (sp3 + 1824#64 + 200#64) 1 359 (by decide),
      memRegion_split (sp3 + 1824#64 + 200#64 + 1#64) 7 352 (by decide),
      memRegion_split (sp3 + 1824#64 + 200#64 + 1#64 + 7#64) 8 344 (by decide),
      memRegion_split (sp3 + 1824#64 + 200#64 + 1#64 + 7#64 + 8#64) 8 336 (by decide),
      memRegion_split (sp3 + 1824#64 + 200#64 + 1#64 + 7#64 + 8#64 + 8#64) 128 208 (by decide),
      memRegion_split
        (sp3 + 1824#64 + 200#64 + 1#64 + 7#64 + 8#64 + 8#64 + 128#64) 64 144 (by decide),
      memRegion_split
        (sp3 + 1824#64 + 200#64 + 1#64 + 7#64 + 8#64 + 8#64 + 128#64 + 64#64) 40 104 (by decide),
      memRegion_split
        (sp3 + 1824#64 + 200#64 + 1#64 + 7#64 + 8#64 + 8#64 + 128#64 + 64#64 + 40#64)
        32 72 (by decide),
      memRegion_split
        (sp3 + 1824#64 + 200#64 + 1#64 + 7#64 + 8#64 + 8#64 + 128#64 + 64#64 + 40#64 + 32#64)
        66 6 (by decide),
      memRegion_split
        (sp3 + 1824#64 + 200#64 + 1#64 + 7#64 + 8#64 + 8#64 + 128#64 + 64#64 + 40#64 + 32#64 +
          66#64) 1 5 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_cells (sp3 + 1824#64) 25 (by decide),
      memRegion_one (sp3 + 2024#64),
      h1cell (sp3 + 2032#64),
      h1cell (sp3 + 2040#64),
      ProofLib.memRegion_cells (sp3 + 2176#64) 8 (by decide),
      ProofLib.memRegion_cells (sp3 + 2280#64) 4 (by decide),
      memRegion_one (sp3 + 2378#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun b_4f2 => ?_)
  refine congrArg sepExists (funext fun u_3a0 => ?_)
  refine congrArg sepExists (funext fun u_398 => ?_)
  refine congrArg sepExists (funext fun b_390 => ?_)
  ac_rfl

end CryptoVerification.E2E.Pqxdh.TopLevel
