/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SimpAttrs
public import ProofLib.Meta.ToExpr
public meta import ProofLib.Meta.ToExpr
public import ProofLib.PrologueFrame
public import ProofLib.SepLogic.Defs
public import ProofLib.ReadWritevFrame
public import ProofLib.Invariant
public import ProofLib.CoreLemmas
public import ProofLib.SyscallModels
public import ProofLib.Lemmas
public import ProofLib.Exec
public import ProofLib.Simulation
public import ProofLib.ProgramReflection
public import ProofLib.ProgramReflection.IdxTree
public import ProofLib.GenDecodes
public import ProofLib.LiteralFetchLint
public import ProofLib.OpcodeExclusion
public import ProofLib.ObjectLoad
public import ProofLib.Process
public import ProofLib.Process.Overrides
public import ProofLib.Process.OverrideWellBehaved
public import ProofLib.FsTrace
public import ProofLib.Library
public import ProofLib.RelocDecode
public import ProofLib.Abi
public import ProofLib.SepLogic
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.Exists
public import ProofLib.SepLogic.Basic
public import ProofLib.SepLogic.SliceArray
public import ProofLib.SepLogic.ByteRegion
public import ProofLib.Hoare
public import ProofLib.VCGen
public import ProofLib.LitNorm
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.CFG
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.SymWP
public import ProofLib.SepLogic.WPp
public import ProofLib.SepLogic.SafeSepWP
public import ProofLib.SepLogic.Entry
public import ProofLib.SpecAudit
public import ProofLib.NonVacuity
public import ProofLib.Disproof
public import ProofLib.CType
public import ProofLib.Legacy.CType
public import ProofLib.BV
public import ProofLib.TrustedClosure
public import ProofLib.Placed
public import ProofLib.GenPlacedFetches

/-!
# Verification Infrastructure

Top-level module re-exporting untrusted proof automation outside the Trusted Computing Base:
separation logic (`ProofLib.SepLogic`), AAPCS64 and Rust ABI rules (`ProofLib.Abi`), Hoare and
loop combinators (`ProofLib.Hoare`), bit-vector solvers (`ProofLib.BV`), specification auditing
(`ProofLib.SpecAudit`), and counterexample builders (`ProofLib.Disproof`). Specification files
import `Arm64` directly and do not depend on `ProofLib`.
-/

@[expose] public section

namespace ProofLib.SepLogic
end ProofLib.SepLogic

-- Pre-realize `PUnit.enumToBitVec` and `PUnit.eq_iff_enumToBitVec_eq` here so independent
-- downstream modules invoking `bv_decide` do not synthesize conflicting copies on diamond import.
private theorem _realize_punit_bv_decide (u : PUnit) : u = () := by bv_decide

