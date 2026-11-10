/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Tests
public import ProofLib.BV.LinearTests
public import ProofLib.BV.IntegrationTests
public import ProofLib.BV.ArithTests
public import ProofLib.BV.BitsTests
public import ProofLib.Testing.WpPerf
public import ProofLib.Testing.Perf
public import ProofLib.Testing.SymWPEval
public import ProofLib.Testing.CFGTest
public import ProofLib.Testing.SafeSepWP
public import ProofLib.Testing.AxiomAudit
public import ProofLib.Testing.BvKernel
public import ProofLib.Testing.BVReflectOptionA
public import ProofLib.Testing.SpecAudit
public import ProofLib.Testing.SpecAuditEnv
public import ProofLib.Testing.NonVacuity
public import ProofLib.Testing.CType
public import ProofLib.Testing.SymBlock
public import ProofLib.Testing.RegionPartition
public import ProofLib.Testing.HookMap
public import ProofLib.Testing.WpCallAndAshrNorm
public import ProofLib.Testing.WpCallClosedNatOffset
public import ProofLib.Testing.WpCallTransport
public import ProofLib.Testing.WpDiag
public import ProofLib.Testing.WpCallDiagnostics
public import ProofLib.Testing.MaxRecDepthDiag
public import ProofLib.Testing.TestFiles
public import ProofLib.Testing.MemRegionAndBitfield
public import ProofLib.Testing.SepFrame
public import ProofLib.Testing.SepFrameBench
public import ProofLib.Testing.CallOtherProgram
public import ProofLib.Testing.SepFresh
public import ProofLib.Testing.SepHooksAndBvExt
public import ProofLib.Testing.SepSupportedOn
public import ProofLib.Testing.SepCells
public import ProofLib.Testing.SepOwnsCell
public import ProofLib.Testing.SepFreshRO
public import ProofLib.Testing.SepProtNone
public import ProofLib.Testing.ProofTerm
public import ProofLib.Testing.ProofTerm.Bench
public import ProofLib.Testing.ProofTerm.BenchTactics
public import ProofLib.Testing.BlockSummary
public import ProofLib.Testing.BlockSummary.Bench
public import ProofLib.Testing.RegChain
public import ProofLib.Testing.RegChainBench
public import ProofLib.Testing.RegAbbrevRead
public import ProofLib.Testing.WpApply
public import ProofLib.Testing.WpApplyBench
public import ProofLib.Testing.GenDecodes
public import ProofLib.Testing.OpcodeExclusion
public import ProofLib.Testing.SliceArrayAndTactics
public import ProofLib.Testing.FnPtr
public import ProofLib.Testing.LoopCFGCombinators
public import ProofLib.Testing.SimdZvaSteps
public import ProofLib.Testing.PolyMulSteps
public import ProofLib.Testing.ByteRegion
public import ProofLib.Testing.OmegaBounded
public import ProofLib.Testing.TailcallCalleeSavedSepEq
public import ProofLib.Testing.SortedFresh
public import ProofLib.Testing.Variant
public import ProofLib.Testing.RustHeap
public import ProofLib.Testing.OracleHook
public import ProofLib.Testing.LayoutGenericRelocs
public import ProofLib.Testing.GenBlockFetches
public import ProofLib.Testing.GenPlacedFetches
public import ProofLib.Testing.GenPlacedOddSites
public import ProofLib.Testing.PairStepHook
public import ProofLib.Testing.ParamCodeFetch
public import ProofLib.Testing.RelocFnGen
public import ProofLib.Testing.ImageData
public import ProofLib.Testing.ImageDataAny
public import ProofLib.Testing.SimpSetUnfoldLint
public import ProofLib.Testing.SlicedCode
public import ProofLib.Testing.TrustedClosure
public import ProofLib.Testing.PlacedCheck
public import ProofLib.Testing.PlacedExternSymtab
public import ProofLib.Testing.PlacedMulti
public import ProofLib.Testing.PlacedSplit
public import ProofLib.Testing.PlacedSplitSingle
public import ProofLib.Testing.PlacedSplitSingleFast
public import ProofLib.Testing.PlacedNamesTree
public import ProofLib.Testing.LabelsCoverage
public import ProofLib.Testing.LabelsPrecedence
public import ProofLib.Testing.MultiSubroutineHook
public import ProofLib.Testing.MultiCodeROHook
public import ProofLib.Testing.PlacedSegmentsOnly
public import ProofLib.Testing.PlacedEntry
public import ProofLib.Testing.PlacedAdrpLdst
public import ProofLib.Testing.PlacedOpcodeExclusion
public import ProofLib.Testing.PlacedSharedCode
public import ProofLib.Testing.ProcessSteps
public import ProofLib.Testing.ProcessPartial
public import ProofLib.Testing.MadvFree
public import ProofLib.Testing.WpInitDeepPre
public import ProofLib.Testing.AsciiNum
public import ProofLib.Testing.IterN
public import ProofLib.Testing.TraceEq
public import ProofLib.Testing.WithPure
public import ProofLib.Testing.DsimpMemo
public import ProofLib.Testing.FetchLocalHyp
public import ProofLib.Testing.TableOffsetsMemo
public import ProofLib.Testing.OutlineAtomicsCas1

/-!
# ProofLib Test Suite

Umbrella module importing regression tests and benchmarks for `ProofLib` tactics, linters, and
specification DSLs.
-/

@[expose] public section
