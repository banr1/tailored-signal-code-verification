/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.ExternWitness
public import Symbolic.Proofs.SpecLemmas.ElfBindingFixed
import all Init.Data.Repr
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunFixed
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import GeneratedLean.LibsignalSessionObj

/-!
# Kernel-Checked Guards on the Symbolic CLI Image and Hook Boundary

Checks CLI setup identifiers, the `libsignalSessionImage` GOT and `"main"` entry symbol,
disjointness and unique resolution of the 46 `cliHookTable` stubs and image-specific panic stub,
and `cliProgAbortOnPanic` / `elfRel` dispatch and joint extern-contract satisfiability.
Kept in a standalone test module so proof files do not import kernel reflection checks.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY
open Arm64 ProofLib CryptoVerification
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open CryptoVerification.E2E
  (compress512Name toEdwardsName compressName edNegName torsionFreeName dsmbName
   scalarModName scalarWideName kemEncapsName kemDecapsName
   extraImagePanicNames isImagePanicSymbol withImagePanics)
open CryptoVerification.LibsignalSpqrV1
  (mlkemFromSeedName mlkemPk1Name mlkemPk2Name mlkemEncaps1Name mlkemEncaps2Name
   mlkemDecapsName mlkemValidatePkName libcruxHmacName)
open CryptoVerification.SignalSession
  (CliHooks Inputs Outcome readFileName writeFileName readStdinName writeStdoutName
   cliHookTable cliExterns cliBase sigAbrt abortOnPanic cliExternsAbortOnPanic cliProgAbortOnPanic cliRunAbortOnPanic
   isCliPanicSymbol withCliPanics sessionFile)
open Symbolic.Proofs.Tests.Refinement.Cli
  (cliWitnessInterp cliWitnessHooks cliWitnessInterp_total cliWitnessInterp_contracts
   cliWitnessHooks_agree)

theorem aliceUuid_ne_bobUuid : aliceUuid ≠ bobUuid := by
  decide +kernel

theorem nameOf_alice_ne_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    nameOf r r.alice ≠ nameOf r r.bob := by
  unfold nameOf
  simp only [↓reduceIte, hne.symm]
  exact aliceUuid_ne_bobUuid

theorem peerNameOf_alice_ne_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    peerNameOf r r.alice ≠ peerNameOf r r.bob := by
  unfold peerNameOf
  simp only [↓reduceIte, hne.symm]
  exact aliceUuid_ne_bobUuid.symm

theorem peerOf_alice_ne_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    peerOf r r.alice ≠ peerOf r r.bob := by
  intro h
  exact peerNameOf_alice_ne_bob hne (congrArg CryptoVerification.SignalSession.Address.name h)

theorem sessionPathOf_alice_ne_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    sessionPathOf r r.alice ≠ sessionPathOf r r.bob := by
  unfold sessionPathOf peerOf peerNameOf
  simp only [↓reduceIte, hne.symm]
  decide +kernel

theorem samePath_sessionPathOf_alice_bob_false {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    SamePath (sessionPathOf r r.alice) (sessionPathOf r r.bob) = false := by
  unfold sessionPathOf peerOf peerNameOf
  simp only [↓reduceIte, hne.symm]
  decide +kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
theorem session_got_tpoff : CryptoVerification.libsignalSessionImage.got = [.tpoff 0x10] := by
  rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- `"main"` resolves uniquely in `libsignalSessionImage.symbols` and is absent from `stubs`. -/
theorem cliMain_resolves :
    ((Obj.lookupUnique "main" CryptoVerification.libsignalSessionImage.symbols).isSome &&
      !CryptoVerification.libsignalSessionImage.stubs.any (·.1 == "main")) = true := by
  rfl_kernel

/-- Hooked stub names of `cliHookTable` in table order: 10 PQXDH, 8 SPQR V1, and 28 runtime, I/O,
and primitive stubs. -/
def cliHookStubNames : List String :=
  [compress512Name,
   toEdwardsName,
   compressName,
   edNegName,
   torsionFreeName,
   dsmbName,
   scalarModName,
   scalarWideName,
   kemEncapsName,
   kemDecapsName,
   mlkemFromSeedName,
   mlkemPk1Name,
   mlkemPk2Name,
   mlkemEncaps1Name,
   mlkemEncaps2Name,
   mlkemDecapsName,
   mlkemValidatePkName,
   libcruxHmacName,
   "__rustc::__rust_no_alloc_shim_is_unstable_v2",
   "__rustc::__rust_alloc",
   "__rustc::__rust_dealloc",
   "__rustc::__rust_realloc",
   "__rustc::__rust_alloc_zeroed",
   "memset",
   "memmove",
   "memcpy",
   "bcmp",
   "strlen",
   readFileName,
   writeFileName,
   readStdinName,
   writeStdoutName,
   "core::slice::memchr::memrchr",
   "core::str::converts::from_utf8",
   "core::fmt::write",
   "alloc::fmt::format::format_inner",
   "<std::time::SystemTime>::duration_since",
   "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add",
   "subtle::black_box::<u8>",
   "sha2::sha256::compress256",
   "signal_crypto::aes_cbc::aes_256_cbc_encrypt",
   "signal_crypto::aes_cbc::aes_256_cbc_decrypt",
   "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from",
   "<x25519_dalek::x25519::StaticSecret>::diffie_hellman",
   "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop",
   "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop"]

theorem cliHookStubNames_length : cliHookStubNames.length = 46 :=
  rfl

theorem cliExtraPanicStubNames_length : extraImagePanicNames.length = 1 :=
  rfl

theorem cliAllGuardedStubs_length : (cliHookStubNames ++ extraImagePanicNames).length = 47 :=
  rfl

theorem cliHookTable_names_eq (W : CliHooks) :
    (cliHookTable W).map Prod.fst = cliHookStubNames :=
  rfl

theorem cliHookTable_length (W : CliHooks) :
    ((cliHookTable W).map Prod.fst).length = 46 :=
  rfl

theorem cliHookStubNames_nodup : cliHookStubNames.Nodup := by
  decide +kernel

theorem cliHookTable_nodup (W : CliHooks) : ((cliHookTable W).map Prod.fst).Nodup := by
  rw [cliHookTable_names_eq]
  exact cliHookStubNames_nodup

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
theorem cliHookStubNames_notRustPanic :
    cliHookStubNames.all (fun n => !Arm64.Rust.isPanicSymbol n) = true := by
  rfl_kernel

theorem cliHookTable_notRustPanic (W : CliHooks) :
    ((cliHookTable W).map Prod.fst).all (fun n => !Arm64.Rust.isPanicSymbol n) = true := by
  rw [cliHookTable_names_eq]
  exact cliHookStubNames_notRustPanic

theorem cliHookStubNames_notExtraPanic :
    cliHookStubNames.all (fun n => !extraImagePanicNames.contains n) = true := by
  decide +kernel

theorem cliHookTable_notExtraPanic (W : CliHooks) :
    ((cliHookTable W).map Prod.fst).all (fun n => !extraImagePanicNames.contains n) = true := by
  rw [cliHookTable_names_eq]
  exact cliHookStubNames_notExtraPanic

/-- No stub in `cliHookTable W` satisfies `isImagePanicSymbol`, so `withImagePanics` shadows no
hook row. -/
theorem cliHookTable_isPanicSymbolE_false (W : CliHooks) {n : String}
    (hn : n ∈ (cliHookTable W).map Prod.fst) :
    isImagePanicSymbol n = false := by
  have hn' : n ∈ cliHookStubNames := by rwa [cliHookTable_names_eq] at hn
  have h1 : (!Arm64.Rust.isPanicSymbol n) = true := List.all_eq_true.mp cliHookStubNames_notRustPanic n hn'
  have h2 : (!extraImagePanicNames.contains n) = true := List.all_eq_true.mp cliHookStubNames_notExtraPanic n hn'
  unfold isImagePanicSymbol
  cases hp : Arm64.Rust.isPanicSymbol n
  · cases he : extraImagePanicNames.contains n
    · rfl
    · rw [he] at h2; cases h2
  · rw [hp] at h1; cases h1

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Every stub in `cliHookStubNames ++ extraImagePanicNames` resolves uniquely in
`libsignalSessionImage.stubs` at a distinct offset and is absent from `symbols`. -/
theorem cliHookStubs_resolve :
    (cliHookStubNames ++ extraImagePanicNames).all (fun n =>
      match Obj.lookupUnique n CryptoVerification.libsignalSessionImage.stubs with
      | some o =>
        !CryptoVerification.libsignalSessionImage.symbols.any (·.1 == n) &&
          (CryptoVerification.libsignalSessionImage.stubs.filter (·.2 == o)).length == 1
      | none => false) = true := by
  rfl_kernel

theorem cliHookTable_and_panics_resolve (interp : ExternInterpretation) (W : CliHooks)
    (_hAgree : HooksMatchInterpretation interp W) :
    ((cliHookTable W).map Prod.fst).length = 46 ∧
    ((cliHookTable W).map Prod.fst).Nodup ∧
    ((cliHookTable W).map Prod.fst).all (fun n => !Arm64.Rust.isPanicSymbol n) = true ∧
    ((cliHookTable W).map Prod.fst).all (fun n => !extraImagePanicNames.contains n) = true ∧
    ((cliHookTable W).map Prod.fst ++ extraImagePanicNames).length = 47 ∧
    ((cliHookTable W).map Prod.fst ++ extraImagePanicNames).all (fun n =>
      match Obj.lookupUnique n CryptoVerification.libsignalSessionImage.stubs with
      | some o =>
        !CryptoVerification.libsignalSessionImage.symbols.any (·.1 == n) &&
          (CryptoVerification.libsignalSessionImage.stubs.filter (·.2 == o)).length == 1
      | none => false) = true := by
  rw [cliHookTable_names_eq]
  exact ⟨cliHookStubNames_length, cliHookStubNames_nodup, cliHookStubNames_notRustPanic,
    cliHookStubNames_notExtraPanic, cliAllGuardedStubs_length, cliHookStubs_resolve⟩

theorem cliProgSig_base_and_overrides (W : CliHooks) :
    (cliProgAbortOnPanic W).base = cliBase ∧
    (cliProgAbortOnPanic W).externs = cliExternsAbortOnPanic W ∧
    (cliProgAbortOnPanic W).overrides = (fun _ => none) :=
  ⟨rfl, rfl, rfl⟩

theorem cliProgSig_abortOnPanic_of_isPanicSymbolE (W : CliHooks) {n : String}
    (hp : isCliPanicSymbol n = true) :
    (cliProgAbortOnPanic W).externs n = some (abortOnPanic Rust.panicked) ∧
    ∀ s : State, (abortOnPanic Rust.panicked s).status = .Signaled sigAbrt := by
  refine ⟨?_, fun s => ?_⟩
  · show (cliExterns W n).map abortOnPanic = some (abortOnPanic Rust.panicked)
    unfold cliExterns
    simp [hp]
  · unfold abortOnPanic Rust.panicked
    rfl

theorem cliProgSig_externs_of_mem_cliHookTable (W : CliHooks) {n : String}
    (hn : n ∈ (cliHookTable W).map Prod.fst) :
    (cliProgAbortOnPanic W).externs n = ((cliHookTable W).lookup n).map abortOnPanic := by
  have hp : isImagePanicSymbol n = false := cliHookTable_isPanicSymbolE_false W hn
  show (cliExterns W n).map abortOnPanic = ((cliHookTable W).lookup n).map abortOnPanic
  unfold cliExterns
  simp [hp]

theorem abortOnPanic_of_ne_panicked (h : State → State) (s : State)
    (hne : (h s).status ≠ .Panicked) :
    abortOnPanic h s = h s := by
  unfold abortOnPanic
  cases hs : (h s).status <;> simp_all

theorem elfRel_eq_cliRunSig (elf : Arm64.Process.ElfImage) (interp : ExternInterpretation)
    (W : CliHooks) (i : Inputs) (o : Option Outcome) :
    elfRel elf interp W i o ↔ cliRunAbortOnPanic elf W i = o :=
  Iff.rfl

/-- Joint satisfiability of the 46-hook `cliHookTable`, `ExternContractsHoldCli`, and
`HooksMatchInterpretation` via `cliWitnessInterp` and `cliWitnessHooks`. -/
theorem cliWitness_hooksAgree_and_contracts :
    ExternInterpretationTotalOnUsedSymbols cliWitnessInterp ∧
    ExternContractsHoldCli cliWitnessInterp ∧
    HooksMatchInterpretation cliWitnessInterp cliWitnessHooks ∧
    ((cliHookTable cliWitnessHooks).map Prod.fst).length = 46 ∧
    ((cliHookTable cliWitnessHooks).map Prod.fst).Nodup :=
  ⟨cliWitnessInterp_total, cliWitnessInterp_contracts, cliWitnessHooks_agree,
   cliHookTable_length cliWitnessHooks, cliHookTable_nodup cliWitnessHooks⟩

end DY.Libsignal.Composed.Refinement.Cli
