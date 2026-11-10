/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.Top
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem noBobDone38HB : NoBobDone38HB :=
  fun _ _ _ _ _ hex => bobDone_nil_of_noAccept hex noAccept_trace_take38
theorem noAccept_torsionComp_trace_take38 : NoAccept (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) := by
  unfold NoAccept
  decide
theorem bobDone_nil_torsionComp_trace_take38 {i : ExternInterpretation} {r : Records} {S : Sem} {who₀ : List Participant} {ok₀ : Nat → Bool} {g : Ghost} {ms : List Move} (hex : DY.Libsignal.Composed.Refinement.ExplainsMoves i r S who₀ ok₀ g ms (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38)) : bobDoneBaseKeys (runTraceMoves r ms) = [] := bobDone_nil_of_noAccept hex noAccept_torsionComp_trace_take38
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
