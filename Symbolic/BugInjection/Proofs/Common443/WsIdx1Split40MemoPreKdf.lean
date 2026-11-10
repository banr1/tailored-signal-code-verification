/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38QKdf
public import Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf
open DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore (QKdf)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus (KdfSalt32)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff QKdfKK QKdfInjRest qKdfC_of)
theorem qKdf_of_parts (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : Row) (u₂ : DY.Bytes) (hxu₂ : x₂ ∈ (gamma' compI0 S g u₂).memo) (hs₁ : KdfSalt32 S g x₁) (hs₂ : KdfSalt32 S g x₂) (hKK : QKdfKK S g known pts x₁ x₂) (hR : QKdfInjRest S g known pts x₁ x₂) (hN : assumedInjective x₂.1 = false → NonInjOff x₂.2.2) : QKdf S g known pts x₁ x₂ := CompRSplit38KdfHead.qKdf_of_head S g known pts x₁ x₂ (CompRSplit38KdfHead.qKdfHead_of_32 S g known pts x₁ x₂ (CompRSplit38QKdf.qKdfHead32_of_c S g known pts x₁ x₂ hs₁ hs₂ (qKdfC_of S g known pts x₁ x₂ u₂ hxu₂ hKK hR hN)))
theorem cls40_pre_of_inj {pre : List Row} {Z : List DY.Bytes} {x : Row} (hc : Cls40 pre Z x) (hz : x.1 ∉ Z) (hai : assumedInjective x.1 = true) : x ∈ pre := by rcases hc with h | h | h <;> [exact h; (rw [h] at hai; cases hai); exact absurd h hz]
theorem cls40_pre_of_kdf {pre : List Row} {Z : List DY.Bytes} {x : Row} (hc : Cls40 pre Z x) (hz : x.1 ∉ Z) {k m : DY.Bytes} (hk : x.1 = DY.KdfExtract.kdfExtract k m) : x ∈ pre := cls40_pre_of_inj hc hz (hk ▸ CompRSplit38QKdf.assumedInjective_kdfExtract k m)
theorem kdfSalt32_of_not_kdf {S : Sem} {g : Ghost} {x : Row} (h : ¬ CompRSplit38UntaggedShape.IsKdf x.1) : KdfSalt32 S g x := fun k m hk => absurd ⟨k, m, hk⟩ h
def Split40PreSalt32Own : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ preMemo40 r S g ms', KdfSalt32 S g x
def Split40PreKKOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x₁ ∈ preMemo40 r S g ms', ∀ x₂ ∈ preMemo40 r S g ms', x₁.1 ∉ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ → x₂.1 ∉ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ → QKdfKK S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (plaintextTerms (runVis r ms') ++ []) x₁ x₂
def Split40PreKIROwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x₁ ∈ preMemo40 r S g ms', ∀ x₂ ∈ preMemo40 r S g ms', x₁.1 ∉ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ → x₂.1 ∉ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ → QKdfInjRest S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (plaintextTerms (runVis r ms') ++ []) x₁ x₂
theorem split40PairsOwn_qKdf40_of (hS : Split40PreSalt32Own) (hKK : Split40PreKKOwn)
    (hR : Split40PreKIROwn)
    (hN : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ preMemo40 r S g ms' ++ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂, Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x → assumedInjective x.1 = false → NonInjOff x.2.2) :
    ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ →
      let pre := preMemo40 r S g ms'
      let new := newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂
      let Z := z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂
      ∀ x₁ ∈ new, ∀ x₂ ∈ pre ++ new, Cls40 pre Z x₁ → Cls40 pre Z x₂ → x₁.1 ∉ Z → x₂.1 ∉ Z →
        QKdf S g (fun u => u.AttackerKnows (runTraceMoves r ms')) (plaintextTerms (runVis r ms') ++ []) x₁ x₂ := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown pre new Z x₁ _ x₂ hx₂ hc₁ hc₂ hz₁ hz₂
  obtain ⟨u₂, hxu₂⟩ : ∃ u₂, x₂ ∈ (gamma' compI0 S g u₂).memo := by
    rcases List.mem_append.mp hx₂ with hm | hm <;>
      (obtain ⟨u, _, hum⟩ := List.mem_flatMap.mp hm; exact ⟨u, hum⟩)
  have hS' := hS r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown
  have hsalt : ∀ x : Row, Cls40 pre Z x → x.1 ∉ Z → KdfSalt32 S g x :=
    fun x hc hz k m hk => hS' x (cls40_pre_of_kdf hc hz hk) k m hk
  exact qKdf_of_parts S g _ _ x₁ x₂ u₂ hxu₂ (hsalt x₁ hc₁ hz₁) (hsalt x₂ hc₂ hz₂)
    (fun k₁ m₁ k₂ m₂ hk₁ hk₂ => hKK r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁
      (cls40_pre_of_kdf hc₁ hz₁ hk₁) x₂ (cls40_pre_of_kdf hc₂ hz₂ hk₂) hz₁ hz₂ k₁ m₁ k₂ m₂ hk₁ hk₂)
    (fun k m hk hK hX hT hai => hR r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁
      (cls40_pre_of_kdf hc₁ hz₁ hk) x₂ (cls40_pre_of_inj hc₂ hz₂ hai) hz₁ hz₂ k m hk hK hX hT hai)
    (hN r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₂ hx₂ hc₂)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf
