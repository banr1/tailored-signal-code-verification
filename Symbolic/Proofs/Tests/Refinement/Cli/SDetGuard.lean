/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Refinement.Cli.ModelLinks
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.Defs
import Symbolic.Proofs.Refinement.Composed.Cli.SDet

/-!
# Statement and Definitional-Equality Guards for `sdet`

Verifies the statement signature of `DY.Libsignal.Composed.Refinement.Cli.sdet` and shows that it
discharges `ModelLinks.DraftDet`, linking `CompRefinesCliModelMoves` to `ModelLinks.LockedReading`.

Checked by Lean.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Composed.Refinement.Cli.SDet
open CryptoVerification.E2E (UnreachedPqxdhPrimitives PEParams)
open CryptoVerification.SignalSession (Inputs Outcome)

theorem sdet_statement_guard :
    (∀ (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams)
       (interp : ExternInterpretation) (i : Inputs) (o : Outcome),
       Draft.PqModelRel Xof Wof interp i o → PqModelPost interp (Wof interp) i o) :=
  DY.Libsignal.Composed.Refinement.Cli.sdet

theorem draft_pqModelRel_eq_modelLinks :
    @DY.Libsignal.Composed.Refinement.Cli.SDet.Draft.PqModelRel =
      @Symbolic.Proofs.Tests.Refinement.Cli.ModelLinks.Draft.PqModelRel :=
  rfl

theorem sdet_draftDet (Xof : ExternInterpretation → UnreachedPqxdhPrimitives)
    (Wof : ExternInterpretation → PEParams) :
    ModelLinks.DraftDet Xof Wof :=
  DY.Libsignal.Composed.Refinement.Cli.sdet Xof Wof

/-- Using `sdet`, `CompRefinesCliModelMoves` implies the draft-relation reading of
`CompRefinesCliRMoves`. -/
theorem locked_reading_of_compRefinesCliModel
    (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams)
    (hroot : CompRefinesCliModelMoves) :
    CompRefinesCliRMoves (ω := Unit) (fun interp _ => ModelAgree interp (Wof interp))
      (fun interp _ i o => ∃ o', o = some o' ∧ Draft.PqModelRel Xof Wof interp i o')
      initDirs :=
  ModelLinks.locked_of_root Xof Wof (DY.Libsignal.Composed.Refinement.Cli.sdet Xof Wof) hroot

theorem locked_reading_type_eq_modelLinks
    (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams) :
    (CompRefinesCliRMoves (ω := Unit) (fun interp _ => ModelAgree interp (Wof interp))
      (fun interp _ i o => ∃ o', o = some o' ∧ Draft.PqModelRel Xof Wof interp i o')
      initDirs) = ModelLinks.LockedReading Xof Wof :=
  rfl

#check @DY.Libsignal.Composed.Refinement.Cli.sdet
#check @Symbolic.Proofs.Tests.Refinement.Cli.locked_reading_of_compRefinesCliModel
#check @Symbolic.Proofs.Tests.Refinement.Cli.draft_pqModelRel_eq_modelLinks

#print axioms DY.Libsignal.Composed.Refinement.Cli.sdet
#print axioms draft_pqModelRel_eq_modelLinks
#print axioms locked_reading_of_compRefinesCliModel

end Symbolic.Proofs.Tests.Refinement.Cli
