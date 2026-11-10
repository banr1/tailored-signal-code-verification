/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
public import Symbolic.Proofs.Refinement.Composed.Cli.Model
public import Symbolic.Proofs.Refinement.Composed.Cli.ModelB2
public import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
public import Symbolic.Specifications.Refinement.Statement

/-!
# Flat-Bundle Initiate ELF Refinement Bridges

Proves that `parseBundleFiles` agrees with `parseBundleDir` on the bundle directory and lifts the
two-placement `CliPqBinaryV2OomF3Placed` flat-bundle `init` clauses across `InputsEquiv`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Refinement.Composed.Cli.BundleInitElfF3Placed

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement.Cli (
  BundleFilesFlat BundleReadWithinCapB2 DirectorySnapshot InputsEquiv ScrubAgree bundleSplitId
  bundleSplitSigned bundleU32 parseBundleFiles parseEcKey parseKyberKey pqInitInputsF
)
open CryptoVerification.E2E (
  PreKeyBundleFields UnreachedPqxdhPrimitives initiateTapeLen
)
open CryptoVerification.SignalSession (
  CliHooks CliReachesOOMPlaced Inputs Outcome OutcomeOrExcusedAbort PqParty
  PqxdhPartyInSpecDomain bundleDir filesOf pqInitModel pqxdhExpectedOutcome publicBundleOf
)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli (ofLe32 splitId splitSigned)
open CryptoVerification.SignalSession.Cli.RunCompose (readU32LE)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (
  CliPqBinaryV2OomF3Placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity (
  normDjbKey normKyberKey parseBundleDir
)

theorem scrubAgree_refl (o : Outcome) : ScrubAgree o o := by
  cases o with
  | aborted => trivial
  | exited _ _ _ => exact ⟨rfl, rfl, fun _ => rfl⟩

theorem scrubAgree_of_eq {o o' : Outcome} (h : o = o') : ScrubAgree o o' :=
  h ▸ scrubAgree_refl o

private theorem parseEcKey_eq_normDjbKey (bs : HwBytes) : parseEcKey bs = normDjbKey bs := by
  cases bs with
  | nil => rfl
  | cons t rest =>
    by_cases h1 : t = 5#8 <;> by_cases h2 : 32 ≤ rest.length <;>
      simp [parseEcKey, DY.Libsignal.PQXDH.Refinement.ecKeyParses, normDjbKey, h1, h2]

private theorem parseKyberKey_eq_normKyberKey (bs : HwBytes) :
    parseKyberKey bs = normKyberKey bs := by
  cases bs with
  | nil => rfl
  | cons t rest =>
    simp only [parseKyberKey, normKyberKey]
    by_cases ht : t = 8#8 ∧ rest.length = 1568 <;> [obtain ⟨rfl, _⟩ := ht; skip] <;> simp [*]

private theorem bundleU32_eq_readU32LE (bs : HwBytes) : bundleU32 bs = readU32LE bs := by
  match bs with
  | [b0, b1, b2, b3] => simp [bundleU32, readU32LE, ofLe32]
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => rfl

private theorem bundleSplitId_eq_splitId (bs : HwBytes) : bundleSplitId bs = splitId bs := by
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => simp [bundleSplitId, bundleU32, splitId, ofLe32]
  | [] | [_] | [_, _] | [_, _, _] => rfl

private theorem bundleSplitSigned_eq_splitSigned (bs : HwBytes) :
    bundleSplitSigned bs = splitSigned bs := by
  unfold bundleSplitSigned splitSigned
  rw [bundleSplitId_eq_splitId]
  cases splitId bs with
  | none => rfl
  | some p => by_cases hle : 64 ≤ p.2.length <;> simp [hle]

private def opkDirOpt (bs : List (BitVec 8)) : Option (Option (BitVec 32 × List (BitVec 8))) :=
  if bs.isEmpty = true then some none else do
    let x ← splitId bs
    let opkKey ← normDjbKey x.2
    some (some (x.1, opkKey))

private theorem opk_rhs_eq (bs : List (BitVec 8)) :
    (if bs.isEmpty = true then some none else do
      let x ← splitId bs
      let opkKey ← normDjbKey x.2
      some (some (x.1, opkKey))) = opkDirOpt bs := rfl

theorem parseBundleFiles_eq_parseBundleDir (d : DirectorySnapshot) :
    parseBundleFiles d = parseBundleDir d bundleDir := by
  unfold parseBundleFiles parseBundleDir
  dsimp only
  simp only [opk_rhs_eq]
  simp only [parseEcKey_eq_normDjbKey, parseKyberKey_eq_normKyberKey,
    bundleU32_eq_readU32LE, bundleSplitSigned_eq_splitSigned, bundleSplitId_eq_splitId]
  dsimp only [bind, Option.bind]
  rcases normDjbKey ((d (bundleDir ++ "/" ++ "identity-key")).getD []) with _ | _ <;>
    [rfl; dsimp only]
  rcases readU32LE ((d (bundleDir ++ "/" ++ "registration-id")).getD []) with _ | _ <;>
    [rfl; dsimp only]
  rcases splitSigned ((d (bundleDir ++ "/" ++ "signed-pre-key")).getD []) with _ | ⟨_, spkRaw, _⟩ <;>
    [rfl; dsimp only]
  rcases splitSigned ((d (bundleDir ++ "/" ++ "kyber-pre-key")).getD []) with _ | ⟨_, kpkRaw, _⟩ <;>
    [(cases normDjbKey spkRaw <;> rfl); dsimp only]
  rcases (d (bundleDir ++ "/" ++ "one-time-pre-key")).getD [] with _ | ⟨b, bs⟩
  · unfold opkDirOpt
    cases normDjbKey spkRaw <;> cases normKyberKey kpkRaw <;> rfl
  · unfold opkDirOpt
    dsimp only [bind, Option.bind]
    rcases splitId (b :: bs) with _ | ⟨_, r⟩
    · cases normDjbKey spkRaw <;> cases normKyberKey kpkRaw <;> rfl
    · dsimp only
      cases normDjbKey spkRaw <;> cases normKyberKey kpkRaw <;> cases normDjbKey r <;> rfl

theorem outcomeUpTo_pqInitFiles_exact_or_none_of_f3_inputsEquiv
    {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × HwBytes)} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquiv i (pqInitInputsF ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hs : st.session = none) (hb : BundleFilesFlat files)
    (hcap : BundleReadWithinCapB2 (filesOf files) bundleDir)
    (hparse : parseBundleFiles (filesOf files) = some (publicBundleOf b)) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsF ⟨W.C, W.Q⟩ st files t)
          (pqInitModel X ⟨W.C, W.Q⟩ st b t)) :=
  hv2.initFiles W X st files b t i heq hwf hs hb hcap
    ((parseBundleFiles_eq_parseBundleDir (filesOf files)).symm.trans hparse)

theorem outcomeUpTo_pqInitReject_or_none_of_f3_inputsEquiv
    {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf)
    (W : CliHooks)
    {st : PqParty} {files : List (String × HwBytes)}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquiv i (pqInitInputsF ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hs : st.session = none) (hb : BundleFilesFlat files)
    (hparse : parseBundleFiles (filesOf files) = none) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = .exited 1 [] (filesOf (pqInitInputsF ⟨W.C, W.Q⟩ st files t).files)) :=
  hv2.initReject W st files t i heq hwf hs hb
    ((parseBundleFiles_eq_parseBundleDir (filesOf files)).symm.trans hparse)

theorem outcomeUpTo_pqInitOverCap_or_none_of_f3_inputsEquiv
    {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf)
    (W : CliHooks)
    {st : PqParty} {files : List (String × HwBytes)}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquiv i (pqInitInputsF ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hs : st.session = none) (hb : BundleFilesFlat files)
    (hover : ¬ BundleReadWithinCapB2 (filesOf files) bundleDir) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = .exited 1 [] (filesOf (pqInitInputsF ⟨W.C, W.Q⟩ st files t).files)) :=
  hv2.initOverFileCap W st files t i heq hwf hs hb hover

end Symbolic.Proofs.Refinement.Composed.Cli.BundleInitElfF3Placed
