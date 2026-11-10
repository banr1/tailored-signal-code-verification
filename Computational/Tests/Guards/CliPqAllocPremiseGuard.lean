/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers

/-!
# CLI PQXDH Allocation and Excused-Abort Premise Guards

**Checked by Lean.** Compile-time guard in `ComputationalTests` (`Computational/Tests.lean`, built
by default `lake build`) pinning:
* K2 `svc` / `overrides` agreement on `Placed.cliProgPlacedSig mpl mmpl W` (`Syscall.standard`,
  `overrides = fun _ => none`), ensuring `MallocngSvcValid (Placed.cliProgPlacedSig mpl mmpl W).svc`.
* K5 `cliHookTablePlaced` row count (`37`, whose exact `37`-key list in
  `cliHookTablePlaced_keys_guard` also fails closed if a `<String as Clone>::clone`, `memset` or
  `memcpy` row is re-added) and absence of all `9` `cliDehookedSymsPlaced` names from both
  `isCliPanicSymbolPlaced` and `cliHookTablePlaced` (`cliExternsPlacedSig mmpl W sym = none`).
* `cliRunPlacedSig_eq_none_of_reachesOOM_guard`: reaching `.OutOfMemory` (`CliReachesOOMPlaced`)
  forces `Placed.cliRunPlacedSig mpl mmpl elf W i = none`.
* `outcomeOrExcusedAbort_ok_branch_nonvacuous_guard`,
  `outcomeOrExcusedAbort_oom_branch_nonvacuous_guard`,
  `outcomeOrExcusedAbort_placed_oom_disjunct_guard`, and
  `not_outcomeOrExcusedAbort_placed_of_unexcused_none_guard` (GK2 4c): both disjuncts of
  `OutcomeOrExcusedAbort` are non-vacuous, and an unexcused `none` (`¬ CliReachesOOMPlaced`) fails
  closed.
* `cliSpecPqxdhOrExcusedAbort_false_iff_guard` and
  `cliSpecPqxdhNoMatchOrExcusedAbort_false_iff_guard` (SR R1): at `exc := fun _ => False`, the
  excused predicates recover post-TSPEC `CliSpecPqxdh` and `CliSpecPqxdhNoMatch`.
* `cliSpecPqxdh_and_noMatch_of_elfCorrectPlaced_and_noOOM_guard`: `main_of_lemmas_placed`'s
  `hNoOOM` premise combined with `CliPqxdhElfCorrectPlaced` recovers total `CliSpecPqxdh` and
  `CliSpecPqxdhNoMatch`; for `cliElfBytes`, `hNoOOM` is proved by
  `ElfNoOomPlacedInstK.cliElf_noOOM_of_parseK` (discharged via
  `ElfSlicesPqOomH2KM1.h2k_ghostArms_closed`).
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Tests.Guards.CliPqAllocPremiseGuard

open Arm64 Arm64.Process ProofLib
open CryptoVerification
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession

theorem cliProgPlacedSig_svc_eq_standard_guard
    (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (Placed.cliProgPlacedSig mpl mmpl W).svc = Syscall.standard :=
  rfl

theorem cliProgPlacedSig_overrides_eq_none_guard
    (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (Placed.cliProgPlacedSig mpl mmpl W).overrides = (fun _ => none) :=
  rfl

theorem cliProgPlacedSig_mallocngSvcValid_guard
    (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    VerifiedLibraries.Mallocng.MallocngSvcValid (Placed.cliProgPlacedSig mpl mmpl W).svc :=
  VerifiedLibraries.Mallocng.Proofs.mallocngSvcValid_standard

/-- Expected ordered `37`-symbol key list of `cliHookTablePlaced`. -/
def cliHookTableKeysExpected : List String :=
  ["_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512",
   "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards",
   "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress",
   "_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg",
   "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free",
   "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint",
   "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order",
   "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes",
   "_RNvCs65XVORQObL2_12libcrux_hmac4hmac",
   "memmove",
   "bcmp",
   "strlen",
   lsWriteFileSym,
   lsWriteStdoutSym,
   lsMemrchrSym,
   lsFromUtf8Sym,
   lsFmtWriteSym,
   lsFormatInnerSym,
   lsDurationSinceSym,
   lsTimeAddSym,
   lsBlackBoxSym,
   lsCompress256Sym,
   lsAesEncSym,
   lsAesDecSym,
   lsPubFromSecretSym,
   lsDiffieHellmanSym,
   lsStaticSecretDropSym,
   lsSharedSecretDropSym]

/-- Guard (GK2 K5): `cliHookTablePlaced` has the exact `37` expected symbol keys in order. -/
theorem cliHookTablePlaced_keys_guard
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliHookTablePlaced mmpl W).map Prod.fst = cliHookTableKeysExpected :=
  rfl

/-- Guard (GK2 K5): `cliHookTablePlaced` has `37` rows (`18` PQXDH/SPQR + `19` base/IO/crypto). -/
theorem cliHookTablePlaced_length_guard
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliHookTablePlaced mmpl W).length = 37 :=
  rfl

/-- Guard (GK2 K2): none of the `9` de-hooked symbol names in `cliDehookedSymsPlaced` is a panic symbol (`isCliPanicSymbolPlaced`). -/
theorem cliDehookedSymsPlaced_not_panic_guard :
    (cliDehookedSymsPlaced.all fun s => !isCliPanicSymbolPlaced s) = true := by
  simp [cliDehookedSymsPlaced, isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol,
    lsRustNoAllocShimSymCli, lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli,
    lsRustAllocZeroedSymCli, lsReadFileSym, lsReadStdinSym]

private theorem not_panic_of_all {s : String} {l : List String}
    (hall : (l.all fun x => !isCliPanicSymbolPlaced x) = true) (hmem : s ∈ l) :
    isCliPanicSymbolPlaced s = false := by
  simpa using List.all_eq_true.mp hall s hmem

private theorem lookup_eq_none_of_all_bne {α β : Type} [BEq α]
    {k : α} : ∀ {l : List (α × β)}, ((l.map Prod.fst).all fun a => !(k == a)) = true →
      l.lookup k = none
  | [], _ => rfl
  | (a, _) :: tl, h => by
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [List.lookup, h.1]
    exact lookup_eq_none_of_all_bne h.2

theorem cliExternsPlacedSig_dehooked_eq_none_guard
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {sym : String}
    (hsym : sym ∈ cliDehookedSymsPlaced) :
    cliExternsPlacedSig mmpl W sym = none := by
  have hp : isCliPanicSymbolPlaced sym = false :=
    not_panic_of_all cliDehookedSymsPlaced_not_panic_guard hsym
  unfold cliExternsPlacedSig cliExternsPlaced
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  rw [lookup_eq_none_of_all_bne]
  · rfl
  · rw [cliHookTablePlaced_keys_guard]
    simp only [cliDehookedSymsPlaced, List.mem_cons, List.not_mem_nil, or_false] at hsym
    rcases hsym with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem cliRunPlacedSig_eq_none_of_reachesOOM_guard
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    (hOOM : CliReachesOOMPlaced mpl mmpl elf W i) :
    Placed.cliRunPlacedSig mpl mmpl elf W i = none :=
  cliRunPlacedSig_eq_none_of_reachesOOM hOOM

theorem outcomeOrExcusedAbort_ok_branch_nonvacuous_guard (i : Inputs) (o : Outcome) :
    let exc : Inputs → Prop := fun _ => False
    let run : CliRun := fun _ => some o
    OutcomeOrExcusedAbort exc run i (· = o) ∧ ¬ exc i :=
  ⟨.inl ⟨o, rfl, rfl⟩, not_false⟩

theorem outcomeOrExcusedAbort_oom_branch_nonvacuous_guard (i : Inputs) :
    let exc : Inputs → Prop := fun j => j = i
    let run : CliRun := fun _ => none
    OutcomeOrExcusedAbort exc run i (fun _ => False) ∧ exc i ∧ (∀ o, run i ≠ some o) :=
  ⟨.inr ⟨rfl, rfl⟩, rfl, fun _ h => nomatch h⟩

theorem outcomeOrExcusedAbort_placed_oom_disjunct_guard
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {P : Outcome → Prop} (hOOM : CliReachesOOMPlaced mpl mmpl elf W i) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (Placed.cliRunPlacedSig mpl mmpl elf W) i P :=
  .inr ⟨cliRunPlacedSig_eq_none_of_reachesOOM hOOM, hOOM⟩

/-- An unexcused `none` result (`¬ CliReachesOOMPlaced`) refutes `OutcomeOrExcusedAbort`. -/
theorem not_outcomeOrExcusedAbort_placed_of_unexcused_none_guard
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {i : Inputs}
    {P : Outcome → Prop}
    (hNone : Placed.cliRunPlacedSig mpl mmpl elf W i = none)
    (hNoOOM : ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    ¬ OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (Placed.cliRunPlacedSig mpl mmpl elf W) i P := by
  rintro (⟨_, hr, _⟩ | ⟨_, hOOM⟩)
  · cases hNone.symm.trans hr
  · exact hNoOOM hOOM

theorem cliSpecPqxdhOrExcusedAbort_false_iff_guard
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdhOrExcusedAbort (fun _ => False) run X W ↔ CliSpecPqxdh run X W :=
  cliSpecPqxdhOrExcusedAbort_false_iff run X W

theorem cliSpecPqxdhNoMatchOrExcusedAbort_false_iff_guard
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdhNoMatchOrExcusedAbort (fun _ => False) run X W ↔ CliSpecPqxdhNoMatch run X W :=
  cliSpecPqxdhNoMatchOrExcusedAbort_false_iff run X W

theorem cliSpecPqxdh_and_noMatch_of_elfCorrectPlaced_and_noOOM_guard
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (hL4 : CliPqxdhElfCorrectPlaced mpl mmpl elf)
    (hNoOOM : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliSpecPqxdh (Placed.cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (Placed.cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ :=
  ⟨cliSpecPqxdh_of_elfCorrectPlaced_and_noOOM hL4 hNoOOM,
    cliSpecPqxdhNoMatch_of_elfCorrectPlaced_and_noOOM hL4 hNoOOM⟩

end Computational.Tests.Guards.CliPqAllocPremiseGuard
