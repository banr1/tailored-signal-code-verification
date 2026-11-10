/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.Placed
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture

/-!
# `mallocngLib` Placement Witnesses on `f3TrialElf`

**Checked by Lean.** Proves `Placeable`, `InElf`, `DataDisjoint`, `CodeLoaded`, `CodeBlocksPermRX`,
and `dataInit` for `VerifiedLibraries.mallocngLib` on `f3TrialElf` at `f3MallocngMpl`, together
with segment-disjoint byte-patch preservation helpers for `patchElfTokensPlaced`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.CliPlacement

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng.Proofs (
  mallocngMultiL mallocngMultiL_names mallocngMultiL_toMultiPlacedLib
)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.SignalSession (
  patchRegionByte patchElfByte patchElfTokensPlaced wellFormed_patchElfByte
)
open LibsignalBinary.Heap.Fine (f3MallocngMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX codeBlocksPermRX_of_codeLoaded
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture (
  f3TrialElf f3TrialElfSyms_eq
)

set_option maxRecDepth 200000

/-! ## `mallocngLib` Placement and Load Witnesses -/

set_option maxHeartbeats 2000000 in
/-- `Placeable ∧ InElf f3TrialElf ∧ DataDisjoint` for `VerifiedLibraries.mallocngLib` at
`f3MallocngMpl`. -/
theorem mallocngLib_in_f3TrialElf :
    VerifiedLibraries.mallocngLib.Placeable f3MallocngMpl ∧
    VerifiedLibraries.mallocngLib.InElf f3TrialElf f3MallocngMpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint f3MallocngMpl := by
  rw [← mallocngMultiL_toMultiPlacedLib]
  exact Obj.Interned.checkMultiDisjoint_spec mallocngMultiL_names f3TrialElfSyms_eq
    (by decide +kernel)

theorem mallocngLib_codeLoaded_f3Trial {inputs : ProcessInputs} {s : State}
    (hload : f3TrialElf.loadState inputs = .ok s) :
    VerifiedLibraries.mallocngLib.CodeLoaded f3MallocngMpl s.mem :=
  VerifiedLibraries.mallocngLib.codeLoaded_of_inElf mallocngLib_in_f3TrialElf.1
    mallocngLib_in_f3TrialElf.2.1 hload

theorem mallocngLib_codeBlocksPermRX_f3Trial {inputs : ProcessInputs} {s : State}
    (hload : f3TrialElf.loadState inputs = .ok s) :
    CodeBlocksPermRX f3MallocngMpl s :=
  codeBlocksPermRX_of_codeLoaded (mallocngLib_codeLoaded_f3Trial hload)

theorem mallocngLib_dataInit_f3Trial {inputs : ProcessInputs} {s : State}
    (hload : f3TrialElf.loadState inputs = .ok s) :
    s.mem ⊨ VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl :=
  VerifiedLibraries.mallocngLib.satisfies_dataInit_of_inElf mallocngLib_in_f3TrialElf.1
    mallocngLib_in_f3TrialElf.2.1 hload (by decide) mallocngLib_in_f3TrialElf.2.2

/-! ## Segment-Disjoint `patchElfByte` Preservation -/

/-- `patchRegionByte addr val r = r` when `addr` lies outside `[r.start, r.start + r.bytes.length)`
without 64-bit wraparound. -/
theorem patchRegionByte_eq_self_of_disjoint {addr : BitVec 64} {val : BitVec 8}
    {r : Snapshot.Region}
    (hnoWrap : r.start.toNat + r.bytes.length ≤ 2 ^ 64)
    (hdisj : addr.toNat < r.start.toNat ∨ r.start.toNat + r.bytes.length ≤ addr.toNat) :
    patchRegionByte addr val r = r := by
  have hnotLt : ¬ (addr - r.start).toNat < r.bytes.length := by
    have ha := addr.isLt
    have hs := r.start.isLt
    rw [BitVec.toNat_sub]
    rcases hdisj with hlt | hge
    · have hmod : (2 ^ 64 - r.start.toNat + addr.toNat) % 2 ^ 64 =
          2 ^ 64 - r.start.toNat + addr.toNat :=
        Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      omega
    · have hmod : (2 ^ 64 - r.start.toNat + addr.toNat) % 2 ^ 64 =
          addr.toNat - r.start.toNat := by
        have hsplit : 2 ^ 64 - r.start.toNat + addr.toNat =
            2 ^ 64 + (addr.toNat - r.start.toNat) := by omega
        rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      omega
  unfold patchRegionByte
  dsimp only
  simp only [hnotLt, ↓reduceIte]

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.CliPlacement
