/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
def Split40ZTagInj : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → (∀ z ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂, (gamma compI0 S g z).take 4 = compTag4) ∧ (∀ a ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂, ∀ b ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂, gamma compI0 S g a = gamma compI0 S g b → a = b)
theorem sound_of_mem_flatMap {S : Sem} {g : Ghost} {L : List DY.Bytes} {x : Row} (hx : x ∈ L.flatMap fun u => (gamma' compI0 S g u).memo) : x.2.1 = (gamma' compI0 S g x.1).shape ∧ x.2.2 = gamma compI0 S g x.1 := by obtain ⟨u, -, hu⟩ := List.mem_flatMap.mp hx; exact CompRPreMemoSound.memo_sound compI0 S g u hu
theorem sound_of_mem_pre_new {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {p : PreKeyFields} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {x : Row} (hx : x ∈ preMemo40 r S g ms' ++ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂) : x.2.1 = (gamma' compI0 S g x.1).shape ∧ x.2.2 = gamma compI0 S g x.1 := (List.mem_append.mp hx).elim sound_of_mem_flatMap sound_of_mem_flatMap
theorem core_false {S : Sem} {g : Ghost} {pre : List Row} {Z : List DY.Bytes} {a b : Row} (hsa : a.2.1 = (gamma' compI0 S g a.1).shape ∧ a.2.2 = gamma compI0 S g a.1) (hsb : b.2.1 = (gamma' compI0 S g b.1).shape ∧ b.2.2 = gamma compI0 S g b.1) (htag : ∀ z ∈ Z, (gamma compI0 S g z).take 4 = compTag4) (hzinj : ∀ a ∈ Z, ∀ b ∈ Z, gamma compI0 S g a = gamma compI0 S g b → a = b) (hU : b ∈ pre → assumedInjective b.1 = true → b.2.2.take 4 ≠ compTag4) (hX : assumedInjective b.1 = false → ∀ z ∈ Z, b.2.2 ≠ gamma compI0 S g z) (hb : Cls40 pre Z b) (ha : a.1 ∈ Z) (hsh : a.2.1 ≠ b.2.1) (hval : a.2.2 = b.2.2) : False := by
  have hbv : b.2.2 = gamma compI0 S g a.1 := hval.symm.trans hsa.2
  rcases hb with hpre | hni | hz
  · cases hi : assumedInjective b.1
    · exact hX hi a.1 ha hbv
    · exact hU hpre hi (hbv ▸ htag a.1 ha)
  · exact hX hni a.1 ha hbv
  · exact hsh (hsa.1.trans (hzinj a.1 ha b.1 hz (hsa.2.symm.trans (hval.trans hsb.2)) ▸ hsb.1.symm))
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged
