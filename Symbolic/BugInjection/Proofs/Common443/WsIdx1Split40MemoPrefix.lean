/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPrefix
open DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore (PairQ PairSide QKdf)
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (QRest)
def Split40PairsOwn (Q : PairQ40) : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ →
    let pre := preMemo40 r S g ms'
    let new := newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂
    let Z := z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂
    ∀ x₁ ∈ new, ∀ x₂ ∈ pre ++ new, Cls40 pre Z x₁ → Cls40 pre Z x₂ →
      Q S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (plaintextTerms (runVis r ms') ++ []) pre Z x₁ x₂
def QKdf40 : PairQ40 := fun S g known pts _ Z x₁ x₂ => x₁.1 ∉ Z → x₂.1 ∉ Z → QKdf S g known pts x₁ x₂
theorem qRest40_of (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (pre : List Row) (Z : List DY.Bytes) (x₁ x₂ : Row) (u₁ u₂ : DY.Bytes) (hxu₁ : x₁ ∈ (gamma' compI0 S g u₁).memo) (hxu₂ : x₂ ∈ (gamma' compI0 S g u₂).memo) (hc₁ : Cls40 pre Z x₁) (hc₂ : Cls40 pre Z x₂) (hU : ∀ x ∈ pre, assumedInjective x.1 = true → x.2.2.take 4 ≠ compTag4) (hK : QKdf40 S g known pts pre Z x₁ x₂) (hR : QRest S g known pts x₁ x₂) : QRest40 S g known pts pre Z x₁ x₂ := by
  intro hz₁ hz₂ hcol; have hs : PairSide known pts x₁ x₂ := ⟨hcol.2.1, hcol.2.2.1, hcol.2.2.2.1⟩; have heq : x₁.2.2 = x₂.2.2 := hcol.2.2.2.2
  have hcls : ∀ x : Row, Cls40 pre Z x → x.1 ∉ Z → assumedInjective x.1 = true → x.2.2.take 4 ≠ compTag4 := by
    intro x hc hz hai
    rcases hc with hpre | hni | hzx <;> [exact hU x hpre hai; (rw [hni] at hai; cases hai); exact absurd hzx hz]
  by_cases ht : x₁.2.2.take 4 = compTag4
  · exact hs.1.elim (fun hai => hcls x₁ hc₁ hz₁ hai ht) (fun hai => hcls x₂ hc₂ hz₂ hai (heq ▸ ht))
  · obtain ⟨hsh₁, hv₁⟩ := CompRPreMemoSound.memo_sound compI0 S g u₁ hxu₁
    obtain ⟨hsh₂, hv₂⟩ := CompRPreMemoSound.memo_sound compI0 S g u₂ hxu₂; exact hcol.1 (hsh₁.trans ((CompRSplit38UntaggedShape.qUntagged_of_kdf_rest S g known pts x₁ x₂ (hK hz₁ hz₂) hR hs (hv₁ ▸ ht) (hv₁ ▸ hv₂ ▸ heq)).trans hsh₂.symm))
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPrefix
