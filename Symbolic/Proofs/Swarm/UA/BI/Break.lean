/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.UA.BI.Step
import VCVio.Prelude.Core

/-!
# Environment Compromise Steps in Trace Explanations

Shows that appending `.env .breakDH` or `.env .breakKEM` extends any `Explains` witness by the
silent model step `.breakDH` or `.breakKEM` without changing ghost state or visible entries.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.UA.BI.Break

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY.Libsignal.HwEvents (CliEvent)
open _root_.DY.Libsignal.Composed.Refinement
open Symbolic.Proofs.Swarm.UA.BI.Step (preCond_breakDH preCond_breakKEM explains_snoc_env_silent)

theorem explains_snoc_breakDH_step {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : Explains interp r S g ss vis evs) :
    Explains interp r S g (ss ++ [.breakDH]) vis (evs ++ [.env .breakDH]) :=
  explains_snoc_env_silent h (preCond_breakDH _) trivial rfl ⟨rfl, rfl⟩

theorem explains_snoc_breakKEM_step {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : Explains interp r S g ss vis evs) :
    Explains interp r S g (ss ++ [.breakKEM]) vis (evs ++ [.env .breakKEM]) :=
  explains_snoc_env_silent h (preCond_breakKEM _) trivial rfl ⟨rfl, rfl⟩

/-- Appending `.env .breakDH` extends an `Explains` trace explanation. -/
theorem explains_snoc_breakDH {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : Explains interp r S g ss vis evs) :
    ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ [.env .breakDH]) :=
  ⟨g, ss ++ [.breakDH], vis, explains_snoc_breakDH_step h⟩

/-- Appending `.env .breakKEM` extends an `Explains` trace explanation. -/
theorem explains_snoc_breakKEM {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {evs : List CliEvent}
    (h : Explains interp r S g ss vis evs) :
    ∃ g' ss' vis', Explains interp r S g' ss' vis' (evs ++ [.env .breakKEM]) :=
  ⟨g, ss ++ [.breakKEM], vis, explains_snoc_breakKEM_step h⟩

end Symbolic.Proofs.Swarm.UA.BI.Break
