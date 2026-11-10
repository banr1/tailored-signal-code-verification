/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
def RandUntaggedTerm (i : ExternInterpretation) (S : Sem) (g : Ghost) (term : DY.Bytes) : Prop := ∀ x ∈ (gamma' i S g term).memo, ∀ r : DY.Random.Random DY.Bytes, x.1 = r.pack → x.2.2.take 4 ≠ compTag4 ∧ x.2.2.take 4 ≠ compTag4Ipad ∧ x.2.2.take 4 ≠ compTag4Opad
theorem wsFreshSafeTerm_iff {i : ExternInterpretation} {S : Sem} {g : Ghost} {term : DY.Bytes} : WsIdx1CensusDefs.FreshSafeTerm i S g term ↔ CompFreshDistinct.FreshSafeTerm i S g term ∧ RandUntaggedTerm i S g term := by
  constructor
  · intro h
    refine ⟨fun x hx t ht hval => (h x hx).1 t (CompFreshDistinct.mem_setupFresh64_iff.mp ht) hval,
            fun x hx r hr => (h x hx).2 r hr⟩
  · rintro ⟨h1, h2⟩ x hx
    refine ⟨fun t ht hval => h1 x hx t (CompFreshDistinct.mem_setupFresh64_iff.mpr ht) hval,
            fun r hr => h2 x hx r hr⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore
