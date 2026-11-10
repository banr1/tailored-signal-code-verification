/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
abbrev serAlice (r : Records) (st : DY.Libsignal.TripleRatchet.TRState) : DY.Bytes := Comparse.serialize (⟨r.alice, st⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)
def Split40PrefixAtom (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (u : DY.Bytes) : Prop :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := iniAliceStartState tr₁ r.bob o₁
  let stA₁' := encSt tr₂ stA₁ cl₁
  u = o₁.ek ∨ u = o₁.ct ∨ u = encOut tr₂ stA₁ cl₁ (tr₂.length + 2) ∨ u = encOut tr₃ stA₁' cl₂ (tr₃.length + 2) ∨ u = randTerm tr₂.length 32 ∨ u = randTerm tr₃.length 32 ∨ u = serAlice r stA₁ ∨ u = serAlice r stA₁' ∨ u = serAlice r (encSt tr₃ stA₁' cl₂)
def Split40PrefixEnumOn (r : Records) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : Prop := ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), Split40PrefixAtom r tr₁ tr₂ tr₃ cl₁ cl₂ u ∨ u ∈ storedSecrets (runTraceMoves r ms')
def Split40PrefixEnum : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Split40PrefixEnumOn r ms' tr₁ tr₂ tr₃ cl₁ cl₂
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs
