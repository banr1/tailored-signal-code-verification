/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import Computational.Tests.AEAD.CBCDecTest
public import Computational.Tests.AEAD.HKDFTest
public import Computational.Tests.AEAD.HMACTest
public import Computational.Tests.AEAD.LibsignalAeadTest
public import Computational.Tests.AEAD.WireAeadTest
public import Computational.Tests.Binary.Kat
public import Computational.Tests.Binary.ProtoCodecDiffTest
public import Computational.Tests.Binary.ProtoCodecKatTest
public import Computational.Tests.Binary.SessionRunTest
public import Computational.Tests.Binary.TripleRatchetRunTest
public import Computational.Tests.Consistency.FirstMsgMacBridge
public import Computational.Tests.Deviations.PaperCorrRule
public import Computational.Tests.Deviations.PaperCorrRuleProof
public import Computational.Tests.Deviations.PaperFaithfulSendDefs
public import Computational.Tests.Deviations.PaperFaithfulSendProof
public import Computational.Tests.Docs.RootKdf
public import Computational.Tests.Docs.Tutorial
public import Computational.Tests.Guards.GenericGameGuard
public import Computational.Tests.Guards.HeadlineAtomicOpsGuard
public import Computational.Tests.Guards.HeadlineSamplersGuard
public import Computational.Tests.Guards.KemFailBadGuard
public import Computational.Tests.Guards.KeyInd1KeyRoGuard
public import Computational.Tests.Guards.MacSupCapsGuard
public import Computational.Tests.Guards.NoOpkCorruptGuard
public import Computational.Tests.Guards.PqxdhKemLengthGuards
public import Computational.Tests.Guards.ReductionDslSizeGuard
public import Computational.Tests.Guards.SessionCliGuards
public import Computational.Tests.Guards.SizeBudgetGuard
public import Computational.Tests.Guards.StatementPqRedsGuard
public import Computational.Tests.NonVacuity.FirstMessageRoundtrip
public import Computational.Tests.NonVacuity.KeyInd1KeyRoNonVac
public import Computational.Tests.NonVacuity.ModelPrimsWitness255
public import Computational.Tests.NonVacuity.ModelTest
public import Computational.Tests.NonVacuity.NonVac
public import Computational.Tests.NonVacuity.PqHeadlineSatisfiable
public import Computational.Tests.NonVacuity.PqNonVacuity
public import Computational.Tests.NonVacuity.PqOomSatisfiable
public import Computational.Tests.NonVacuity.PrimeOrderX25519Satisfiable
public import Computational.Tests.NonVacuity.RunLocalFitsNonVac
public import Computational.Tests.NonVacuity.SpqrOffCorr
public import Computational.Tests.NonVacuity.X25519ModelTest
public import Computational.Tests.Sanity.InOrder
public import Computational.Tests.Sanity.LibsignalCorrNoInjSanity
public import Computational.Tests.Sanity.LibsignalGameSanity
public import Computational.Tests.Sanity.LibsignalRefinesCSanity
public import Computational.Tests.Sanity.LibsignalSimCFacts
public import Computational.Tests.Sanity.LibsignalSpqrCorrectFacts
public import Computational.Tests.Sanity.LibsignalSpqrLogProjection
public import Computational.Tests.Sanity.Sanity
public import Computational.Tests.Sanity.UnrestrictedEq
public import Computational.Tests.Sanity.Window
public import Computational.Tests.Session.RootKdfTest
public import Computational.Tests.SignalPqxdh.SignalPqxdh
public import Computational.Tests.XeddsaRomNonVac
public import Computational.Tests.Guards.CliPqAllocPremiseGuard

/-!
# Computational Tests Umbrella

Root of the default `ComputationalTests` library: sanity, non-vacuity, consistency, and deviation
checks, statement guards (`Computational/Tests/Guards/`), and binary execution tests
(`Computational/Tests/{AEAD,Binary}/`). No module in `Computational/Specifications/`,
`Computational/Proofs/`, or `Computational/Theorems/` imports from `Computational/Tests/`
(`Computational/scripts/check_computational_deps.py`). Known-answer tests under
`Computational/Tests/Kat/` belong to the separate `ComputationalKat` library.
-/

@[expose] public section
