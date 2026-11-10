/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Strict Two-Placement Bundle-Initialization ELF Theorems

Strengthens the `BundleInitElfF3` `OutcomeOrExcusedAbort` bridges to exact `cliRunPlacedSig = some o`
and `cliRunPlacedSig ≠ none` results under `InputsLoadable`, `CliElfF3B2NeedLocksAssumptions`, and
`MainInitRunSemOkF3`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3Strict

open Arm64 (FsEntry Memory normalizePath)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage ProcessInputs)
open CryptoVerification.E2E (
  PEParams PreKeyBundleFields UnreachedPqxdhPrimitives initiateTapeLen
)
open CryptoVerification.SignalSession (
  CliHooks Inputs Outcome PqParty PqxdhPartyInSpecDomain bundleDir cliExternsPlaced coinsFile
  dirsFold encodeDir fileCapBytes filesFold filesOf files_eq_entries fsView initFsState_entries
  observe pqInitModel pqInputs pqxdhExpectedOutcome publicBundleOf stdinCapBytes stdioPaths
)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli (
  CliInputsOk CoinsReadable CommitOk InputsLoadable IsSendOverCap IsStdinOverCap MainResult
  cliInputs
)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runAns runRel)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (
  BundleFilesFlatRaw pqInitInputsFRaw
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
  cliRunPlacedSig_eq_on_input_of_progEq2
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail (
  externPreservesNoAllocFailed_cliExternsPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedSigAt_cliExternsPlaced_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity (
  BundleReadWithinCap InputsEquivRaw fileStep_entries filesFold_entries_eq_or
  filesFold_eq_foldl_fileStep parseBundleDir
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (
  CliInitD3Inputs InitRunSemOk MainInitRunSemOkF3 cliInputsOk_of_inputsEquivRaw
  cliInputsOk_pqInitInputsFRaw observe_accept_pqInitInputsFRaw_eq
  observe_overCap_pqInitInputsFRaw_eq observe_reject_pqInitInputsFRaw_eq
)

/-! ## Input-Side Helper Lemmas -/

private theorem ite_pos_f3 {α : Type} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := match inst with | isTrue _ => rfl | isFalse h => absurd hc h

private theorem ite_neg_f3 {α : Type} {c : Prop} [inst : Decidable c] (hc : ¬ c) {a b : α} :
    (if c then a else b) = b := match inst with | isTrue h => absurd h hc | isFalse _ => rfl

private theorem filesOf_eq_match_filesFold_f3 (f : List (String × List (BitVec 8))) {p : String}
    (hne : normalizePath p ≠ [])
    (hns : normalizePath p ∉ stdioPaths.map normalizePath) :
    filesOf f p = match (filesFold f {}).entries (normalizePath p) with
      | some (.file bs) => some bs | _ => none := by
  unfold filesOf fsView
  rw [ite_neg_f3 hns, files_eq_entries,
    ite_neg_f3 (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries ({ files := f } : ProcessInputs) (normalizePath p) hns]
  rfl

private theorem filesOf_pqInitInputsF_coins_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    filesOf i.files coinsFile = some t.toList := by
  rw [heq.2.2.2 coinsFile]
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_f3 _ hne hns,
    show (pqInitInputsFRaw P st files t).files =
      (encodeDir P st ++ files) ++ [(coinsFile, t.toList)] by
        simp [pqInitInputsFRaw, pqInputs, List.append_assoc],
    filesFold_eq_foldl_fileStep, List.foldl_append, List.foldl_cons, List.foldl_nil,
    fileStep_entries, ite_pos_f3 rfl]

private theorem coinsReadable_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    CoinsReadable i := by
  have hc := filesOf_pqInitInputsF_coins_f3 heq
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_f3 _ hne hns] at hc
  have hfold : (filesFold i.files {}).entries (normalizePath coinsFile) =
      some (.file t.toList) := by
    rcases hf : (filesFold i.files {}).entries (normalizePath coinsFile) with _ | bs | _ <;>
      rw [hf] at hc <;>
      [cases hc;
       (dsimp only at hc
        exact congrArg (fun x => some (FsEntry.file x)) (Option.some.inj hc));
       cases hc]
  unfold CoinsReadable
  rw [show "coins" = coinsFile from rfl, files_eq_entries,
    ite_neg_f3 (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries (cliInputs i) (normalizePath coinsFile) hns]
  change (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath coinsFile) ≠
      some .dir ∧
    ∀ bs, (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath coinsFile) =
      some (.file bs) → bs.length ≤ fileCapBytes
  rw [filesFold_entries_eq_or i.files _ hne, hfold, Option.some_or]
  refine ⟨fun h => FsEntry.noConfusion (Option.some.inj h), fun bs h => ?_⟩
  injection h with h
  injection h with h
  subst h
  simp [List.Vector.toList_length, initiateTapeLen, fileCapBytes]

private theorem not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsSendOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs] at hgt

private theorem not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsStdinOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs, stdinCapBytes] at hgt

private def dummyUnreached : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  kemKeyGen := fun _ => ([], [])
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false

/-! ## Exact `= some (...)` and `≠ none` Theorems -/

section OfF3

variable {mpl mmpl : MultiPlacement}
  {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
  {elf : ElfImage}
  (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
  (hinitSem : MainInitRunSemOkF3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
include H hinitSem

private theorem cliRunPlacedSig_of_f3_sem (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {i : Inputs} {o : Outcome}
    (hdom : CliInitD3Inputs ⟨W.C, W.Q⟩ i)
    (hi : CliInputsOk i) (hload : InputsLoadable i)
    (hnoc : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i)
    (hstep : ∀ S : RunSem, InitRunSemOk S X ⟨W.C, W.Q⟩ →
      runRel S i (runAns S i) ∧
      CommitOk i (MainResult.ofAnswer (runAns S i)) ∧
      observe i.files (runAns S i) = o) :
    cliRunPlacedSig mpl mmpl elf W i = some o := by
  obtain ⟨S, hS, hmainW⟩ := hinitSem H.base547NeZero X W
  obtain ⟨hrel, hcommit, hobs⟩ := hstep S hS
  have hrunExt :=
    cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW
      H.stkLo H.stkHi hi hload ⟨hdom, hrel⟩ hnoc hnstin hobs hcoins hcommit
  have hprogEq := (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm
  exact (cliRunPlacedSig_eq_on_input_of_progEq2 hprogEq rfl).trans hrunExt

/-- Exact `cliRunPlacedSig = some (...)` theorem for flat-bundle `init` when `parseBundleDir = some (publicBundleOf b)` and `BundleReadWithinCap` hold. -/
theorem cliRunPlacedSig_pqInitFiles_exact_eq_some_of_f3 (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    cliRunPlacedSig mpl mmpl elf W i =
      some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
        (pqInitModel X ⟨W.C, W.Q⟩ st b t)) :=
  cliRunPlacedSig_of_f3_sem H hinitSem W X ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_accept_pqInitInputsFRaw_eq X ⟨W.C, W.Q⟩ heq hwf hs hb hcap hparse hS)

theorem cliRunPlacedSig_pqInitFiles_exact_ne_none_of_f3 (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    cliRunPlacedSig mpl mmpl elf W i ≠ none :=
  by
    rw [cliRunPlacedSig_pqInitFiles_exact_eq_some_of_f3 H hinitSem W X heq hload hwf hs hb hcap hparse]
    intro hnone; cases hnone

/-- Exact `cliRunPlacedSig = some (...)` theorem for flat-bundle `init` when `parseBundleDir = none`. -/
theorem cliRunPlacedSig_pqInitReject_eq_some_of_f3 (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    cliRunPlacedSig mpl mmpl elf W i =
      some (.exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  cliRunPlacedSig_of_f3_sem H hinitSem W dummyUnreached ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_reject_pqInitInputsFRaw_eq dummyUnreached ⟨W.C, W.Q⟩ heq hwf hs hb hparse hS)

theorem cliRunPlacedSig_pqInitReject_ne_none_of_f3 (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    cliRunPlacedSig mpl mmpl elf W i ≠ none :=
  by
    rw [cliRunPlacedSig_pqInitReject_eq_some_of_f3 H hinitSem W heq hload hwf hs hb hparse]
    intro hnone; cases hnone

/-- Exact `cliRunPlacedSig = some (...)` theorem for flat-bundle `init` when `¬ BundleReadWithinCap` holds. -/
theorem cliRunPlacedSig_pqInitOverCap_eq_some_of_f3 (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    cliRunPlacedSig mpl mmpl elf W i =
      some (.exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  cliRunPlacedSig_of_f3_sem H hinitSem W dummyUnreached ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_overCap_pqInitInputsFRaw_eq dummyUnreached ⟨W.C, W.Q⟩ heq hwf hs hb hover hS)

theorem cliRunPlacedSig_pqInitOverCap_ne_none_of_f3 (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    cliRunPlacedSig mpl mmpl elf W i ≠ none :=
  by
    rw [cliRunPlacedSig_pqInitOverCap_eq_some_of_f3 H hinitSem W heq hload hwf hs hb hover]
    intro hnone; cases hnone

end OfF3

/-! ## Axiom Checks -/

/--
info: 'LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3Strict.cliRunPlacedSig_pqInitFiles_exact_eq_some_of_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cliRunPlacedSig_pqInitFiles_exact_eq_some_of_f3

/--
info: 'LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3Strict.cliRunPlacedSig_pqInitFiles_exact_ne_none_of_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cliRunPlacedSig_pqInitFiles_exact_ne_none_of_f3

/--
info: 'LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3Strict.cliRunPlacedSig_pqInitReject_eq_some_of_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cliRunPlacedSig_pqInitReject_eq_some_of_f3

/--
info: 'LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3Strict.cliRunPlacedSig_pqInitReject_ne_none_of_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cliRunPlacedSig_pqInitReject_ne_none_of_f3

/--
info: 'LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3Strict.cliRunPlacedSig_pqInitOverCap_eq_some_of_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cliRunPlacedSig_pqInitOverCap_eq_some_of_f3

/--
info: 'LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3Strict.cliRunPlacedSig_pqInitOverCap_ne_none_of_f3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cliRunPlacedSig_pqInitOverCap_ne_none_of_f3

end LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3Strict
