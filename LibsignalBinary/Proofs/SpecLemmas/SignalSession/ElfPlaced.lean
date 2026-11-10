/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionPlacedObj
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMallocngPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Two-Placement Witnesses and Uniqueness for `cliElfBytes`

**Checked by Lean.** Assembles and re-exports the two-placement `libsignalSessionLib` and
`VerifiedLibraries.mallocngLib` witnesses on `cliElfBytes` (`LinkedAt`, `LinkedIn`,
relocation-inversion uniqueness, `CliElfCodeMatchesPlaced`, and injective extern symbol mapping
`cliElf_externs_nodup_of_linkedAt`).
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced

open Arm64
open Arm64.Obj (MultiPlacedLib MultiPlacement)
open ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionExterns)
open CryptoVerification.SignalSession (
  cliElfBytes cliElfImage cliElf_parse
  CliHooks Inputs Outcome OutcomeMatchesProcess cliProcessInputs
  libsignalSessionLib cliHookTablePlaced isCliPanicSymbolPlaced cliExternsPlaced cliExternsPlacedSig
  CliReachesOOMPlaced
)
open CryptoVerification.SignalSession.Placed (
  CliElfCodeMatchesPlaced cliProgPlacedSig cliTokenPatchPlaced CliRunsToPlaced cliRunPlacedSig
)
open LibsignalBinary.Heap.Fine (f3MallocngMpl)

/-! ## Re-exported Interned Layout and Reflection Witnesses -/

noncomputable abbrev lsInternedMultiLib : Obj.Interned.MultiLib :=
  ElfCodeMatchesData.lsInternedMultiLib

noncomputable abbrev lsNameChars : List (List Char) :=
  ElfCodeMatchesData.lsNameChars

noncomputable abbrev lsNames : List String :=
  ElfCodeMatchesData.lsNames

noncomputable abbrev lsSharedExterns : List Nat :=
  ElfCodeMatchesData.lsSharedExterns

noncomputable abbrev cliElfBlockBases : List (BitVec 64) :=
  ElfCodeMatchesData.f3LsBlockBases

noncomputable abbrev cliElfSymAddrs : List (BitVec 64) :=
  ElfCodeMatchesData.f3LsSymAddrs

noncomputable abbrev cliElfMultiLayout : Obj.Interned.MultiLayout :=
  ElfCodeMatchesData.f3LsLayout

noncomputable abbrev cliElfMultiPlacement : MultiPlacement :=
  ElfCodeMatchesData.f3LsMpl

noncomputable abbrev cliElfSymChars : List (List Char × BitVec 64) :=
  ElfSymChars.cliElfSymChars

theorem cliElf_symbols_eq :
    cliElfImage.symbols = ProofLib.ProgramReflection.toStringAssoc cliElfSymChars :=
  ElfSymChars.cliElf_symbols_eq

theorem ls_names_eq : lsInternedMultiLib.names = lsNameChars.map String.ofList :=
  ElfCodeMatchesData.ls_names_eq

theorem ls_names_nodup : lsInternedMultiLib.names.Nodup :=
  ElfCodeMatchesData.ls_names_nodup

theorem ls_toMultiPlacedLib_eq : libsignalSessionLib = lsInternedMultiLib.toMultiPlacedLib :=
  ElfCodeMatchesData.ls_toMultiPlacedLib_eq

/-! ## `libsignalSessionLib` Placement, `LinkedAt`, and Uniqueness -/

/-- `Placeable ∧ InElf cliElfImage ∧ DataDisjoint` for `libsignalSessionLib` at
`cliElfMultiPlacement`. -/
theorem cliElf_libsignal_placed :
    libsignalSessionLib.Placeable cliElfMultiPlacement ∧
    libsignalSessionLib.InElf cliElfImage cliElfMultiPlacement ∧
    libsignalSessionLib.DataDisjoint cliElfMultiPlacement :=
  ElfCodeMatchesPlaced.f3CliElf_libsignal_placed

theorem cliElf_linkedAt :
    libsignalSessionLib.LinkedAt cliElfBytes cliElfMultiPlacement :=
  ⟨cliElfImage, cliElf_parse, cliElf_libsignal_placed.1, cliElf_libsignal_placed.2.1⟩

theorem cliElf_linkedIn :
    libsignalSessionLib.LinkedIn cliElfBytes :=
  ⟨cliElfMultiPlacement, cliElf_linkedAt⟩

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `LinkedAt cliElfBytes` placement of
`libsignalSessionLib`. -/
theorem cliElf_linkedAt_unique {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    (∀ i < libsignalSessionLib.blocks.length, mpl.base i = cliElfMultiPlacement.base i) ∧
    (∀ s ∈ lsInternedMultiLib.names,
      libsignalSessionLib.resolve mpl s = libsignalSessionLib.resolve cliElfMultiPlacement s) ∧
    (∀ s ∈ lsInternedMultiLib.names,
      Obj.lookupBlockSym s libsignalSessionLib.blocks = none →
        mpl.ρ s = cliElfMultiPlacement.ρ s) ∧
    libsignalSessionLib.DataDisjoint mpl :=
  ElfCodeMatchesPlaced.f3CliElf_libsignal_linkedAt_unique hlink

/-! ## `VerifiedLibraries.mallocngLib` Placement and Uniqueness -/

theorem cliElf_mallocng_linkedAt :
    VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes ElfMallocngPlaced.cliElfMallocngPlacement :=
  ElfMallocngPlaced.cliElf_mallocng_linkedAt

theorem cliElf_mallocng_linkedIn :
    VerifiedLibraries.mallocngLib.LinkedIn cliElfBytes :=
  ElfMallocngPlaced.cliElf_mallocng_linkedIn

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `LinkedAt cliElfBytes` placement of
`VerifiedLibraries.mallocngLib`. -/
theorem cliElf_mallocng_linkedAt_unique {mmpl : MultiPlacement}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    (∀ i < VerifiedLibraries.mallocngLib.blocks.length,
      mmpl.base i = ElfMallocngPlaced.cliElfMallocngPlacement.base i) ∧
    (∀ s ∈ VerifiedLibraries.Mallocng.Proofs.mallocngMultiL.names,
      VerifiedLibraries.mallocngLib.resolve mmpl s =
        VerifiedLibraries.mallocngLib.resolve ElfMallocngPlaced.cliElfMallocngPlacement s) ∧
    (∀ s ∈ VerifiedLibraries.Mallocng.Proofs.mallocngMultiL.names,
      Obj.lookupBlockSym s VerifiedLibraries.mallocngLib.blocks = none →
        mmpl.ρ s = ElfMallocngPlaced.cliElfMallocngPlacement.ρ s) ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl :=
  ElfMallocngPlaced.cliElf_mallocng_linkedAt_unique hlink

/-! ## Two-Placement `CliElfCodeMatchesPlaced` Witnesses -/

/-- Concrete two-placement `CliElfCodeMatchesPlaced` witness on `cliElfMultiPlacement` and
`cliElfMallocngPlacement`. -/
theorem cliElf_codeMatchesPlaced :
    CliElfCodeMatchesPlaced cliElfMultiPlacement
      ElfMallocngPlaced.cliElfMallocngPlacement cliElfImage :=
  ElfCodeMatchesPlaced.f3TrialElf_codeMatchesPlaced_of_linkedAt
    cliElf_linkedAt ElfMallocngPlaced.cliElf_mallocng_linkedAt

theorem cliElf_codeMatchesPlaced_f3 :
    CliElfCodeMatchesPlaced cliElfMultiPlacement f3MallocngMpl cliElfImage :=
  ElfCodeMatchesPlaced.f3TrialElf_codeMatchesPlaced

/-- Universal `CliElfCodeMatchesPlaced mpl mmpl cliElfImage` witness for arbitrary `(mpl, mmpl)`
linked in `cliElfBytes`. -/
theorem cliElf_codeMatchesPlaced_of_linkedAt {mpl mmpl : MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    CliElfCodeMatchesPlaced mpl mmpl cliElfImage :=
  ElfCodeMatchesPlaced.f3TrialElf_codeMatchesPlaced_of_linkedAt hls hmng

/-! ## Extern Address Injectivity -/

set_option maxRecDepth 4000000 in
private theorem sharedExterns_check_ok :
    libsignalSessionExterns =
        lsSharedExterns.map (fun idx => lsInternedMultiLib.names.getD idx "") ∧
      (lsSharedExterns.all fun idx =>
        Nat.blt idx lsInternedMultiLib.names.length &&
          (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)) = true := by
  exact ⟨by rfl_kernel, by rfl_kernel⟩

private theorem toMultiPlacement_rho_eq (mly : Obj.Interned.MultiLayout) (names : List String)
    (s : String) :
    (mly.toMultiPlacement names).ρ s = mly.addrs.getD (names.idxOf s) 0#64 := by
  rfl

private theorem cliElf_rho_getD_eq {idx : Nat}
    (hlt : idx < lsInternedMultiLib.names.length) :
    cliElfMultiPlacement.ρ (lsInternedMultiLib.names.getD idx "") =
      cliElfSymAddrs.getD idx 0#64 := by
  unfold cliElfMultiPlacement ElfCodeMatchesData.f3LsMpl cliElfSymAddrs
  rw [toMultiPlacement_rho_eq, Obj.Interned.idxOf_getD ls_names_nodup hlt]
  rfl

private theorem mem_lsNames_of_lt {idx : Nat}
    (hlt : idx < lsInternedMultiLib.names.length) :
    lsInternedMultiLib.names.getD idx "" ∈ lsInternedMultiLib.names := by
  rw [Obj.Interned.getD_of_lt hlt]
  exact List.getElem_mem hlt

private theorem lookupBlockSym_none_of_lt {idx : Nat}
    (hlt : idx < lsInternedMultiLib.names.length)
    (hid : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none) :
    Obj.lookupBlockSym (lsInternedMultiLib.names.getD idx "") libsignalSessionLib.blocks = none := by
  rw [ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ElfCodeMatchesData.ls_idsOk hlt]
  exact hid

private def bv64NodupBool : List (BitVec 64) → Bool
  | [] => true
  | x :: xs => !(xs.any (· == x)) && bv64NodupBool xs

private theorem bv64NodupBool_spec :
    ∀ {xs : List (BitVec 64)}, bv64NodupBool xs = true → xs.Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    simp only [bv64NodupBool, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.Pairwise.cons (fun y hy hxy => ?_) (bv64NodupBool_spec h.2)
    rw [← hxy] at hy
    have hany : xs.any (· == x) = true := List.any_eq_true.mpr ⟨x, hy, beq_self_eq_true x⟩
    rw [h.1] at hany
    exact Bool.noConfusion hany

set_option maxRecDepth 4000000 in
private theorem cliElf_sharedExterns_addrs_nodup :
    bv64NodupBool (lsSharedExterns.map fun idx => cliElfSymAddrs.getD idx 0#64) = true := by
  rfl_kernel

/-- Every `mpl` satisfying `libsignalSessionLib.LinkedAt cliElfBytes mpl` maps
`libsignalSessionExterns` injectively (`(libsignalSessionExterns.map mpl.ρ).Nodup`). -/
theorem cliElf_externs_nodup_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    (libsignalSessionExterns.map mpl.ρ).Nodup := by
  have huniq := (cliElf_linkedAt_unique hlink).2.2.1
  have hmap :
      libsignalSessionExterns.map mpl.ρ =
        lsSharedExterns.map (fun idx => cliElfSymAddrs.getD idx 0#64) := by
    rw [sharedExterns_check_ok.1, List.map_map]
    refine List.map_congr_left fun idx hidx => ?_
    dsimp only [Function.comp_def]
    have hall := List.all_eq_true.mp sharedExterns_check_ok.2 idx hidx
    simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hall
    exact (huniq _ (mem_lsNames_of_lt hall.1) (lookupBlockSym_none_of_lt hall.1 hall.2)).trans
      (cliElf_rho_getD_eq hall.1)
  rw [hmap]
  exact bv64NodupBool_spec cliElf_sharedExterns_addrs_nodup

/-! ## Two-Placement Execution Determinism Re-exports -/

theorem cliTokenPatchPlaced_eq_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    cliTokenPatchPlaced mpl = cliTokenPatchPlaced cliElfMultiPlacement :=
  ElfCodeMatchesPlaced.cliTokenPatchPlaced_eq_of_linkedAt hlink

theorem cliRunsToPlaced_eq_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) :
    CliRunsToPlaced mpl mmpl cliElfImage W =
      CliRunsToPlaced cliElfMultiPlacement mmpl cliElfImage W :=
  ElfCodeMatchesPlaced.cliRunsToPlaced_eq_of_linkedAt hlink mmpl W

theorem cliRunPlacedSig_eq_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) :
    cliRunPlacedSig mpl mmpl cliElfImage W =
      cliRunPlacedSig cliElfMultiPlacement mmpl cliElfImage W :=
  ElfCodeMatchesPlaced.cliRunPlacedSig_eq_of_linkedAt hlink mmpl W

theorem cliReachesOOMPlaced_iff_of_linkedAt {mpl : MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) (i : Inputs) :
    CliReachesOOMPlaced mpl mmpl cliElfImage W i ↔
      CliReachesOOMPlaced cliElfMultiPlacement mmpl cliElfImage W i :=
  ElfCodeMatchesPlaced.cliReachesOOMPlaced_iff_of_linkedAt hlink mmpl W i

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
