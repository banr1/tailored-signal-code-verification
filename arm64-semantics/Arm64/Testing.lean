/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Harness.Encode
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Harness.FpEval
public import Arm64.Testing.Harness.Compare
public import Arm64.Testing.Harness.Serve
public import Arm64.Testing.Harness.ElfRegionLoad
public import Arm64.Testing.Harness.ElfLoaderDiff
public import Arm64.Testing.Harness.FastSemantics
public import Arm64.Testing.Generators.ExternalSuites
public import Arm64.Testing.Generators.HandWrittenVectors
public import Arm64.Testing.Generators.RandomFuzz
public import Arm64.Testing.Generators.CompiledBinary
public import Arm64.Testing.Generators.SyscallTraces
public import Arm64.Testing.Generators.TrustedSuite
public import Arm64.Testing.Conformance.IsaConformance
public import Arm64.Testing.Regression.UnitTests
public import Arm64.Testing.Regression.Process
public import Arm64.Testing.Regression.ProcessAssumptions
public import Arm64.Testing.Regression.ProcessOverrides
public import Arm64.Testing.Regression.ProcessOverrideWellBehaved
public import Arm64.Testing.Regression.ProcessE2E
public import Arm64.Testing.Regression.ElfLoaderDiff
public import Arm64.Testing.Regression.SyscallDiff
public import Arm64.Testing.SyscallDiff
public import Arm64.Testing.Regression.SyscallFamilies
public import Arm64.Testing.Regression.StdSyscalls
public import Arm64.Testing.Regression.MadvFree
public import Arm64.Testing.Regression.ObjectLoad
public import Arm64.Testing.Regression.IncludeBytes
public import Arm64.Testing.Regression.DisproofTests
public import Arm64.Testing.Regression.SimdScalarSteps
public import Arm64.Testing.Regression.UnscaledLdurSteps
public import Arm64.Testing.Regression.CondCompareSteps
public import Arm64.Testing.Regression.LitWidthNorm
public import Arm64.Testing.Regression.SymbolIndexEntry
public import Arm64.Testing.Regression.CodeLookup
public import Arm64.Testing.Regression.LoadAddrClause
public import Arm64.Testing.Regression.FunctionalCorrectness
public import Arm64.Testing.Regression.RustAbiOptionResult
public import Arm64.Testing.AsciiTests
public import Arm64.Testing.Tours.Demo
public import Arm64.Testing.Tours.EchoStdinFixture
public import Arm64.Testing.Tours.SpecAdequacyTour
public import Arm64.Testing.Tours.SepLogicLawsTour
public import Arm64.Testing.Tours.ProcessSemanticsTour
public import Arm64.Testing.Proofs.EncoderDecoder
public import Arm64.Testing.Proofs.SpecAdequacyKit
public import Arm64.Testing.Proofs.SpecAdequacyRustExamples

/-!
# AArch64 ISA, Loader, and Step-Rule Test Suite

Top-level umbrella module re-exporting test harnesses, differential and trace generators,
kernel-checked ISA conformance theorems, evaluator and step-rule regressions, guided tours,
and encoder-decoder round-trip proofs. Standalone CLI executables (`DifferentialEval`,
`ElfEval`, `PlacedEval`) define `main` and are built separately.
-/

@[expose] public section
