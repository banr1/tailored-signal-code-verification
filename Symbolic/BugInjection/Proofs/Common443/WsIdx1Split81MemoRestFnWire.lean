/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnWire
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnWire
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4)
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnWire Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
theorem encWire_msg1_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p₁ : PreKeyFields} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hp₁ : parsePreKeyWire SP.schedBCall1SendBytes = some p₁) : gamma compI0 S g (encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2)) = p₁.message.take (p₁.message.length - 8) := by obtain ⟨p₂, hp₂⟩ := parse_b2; obtain ⟨p₅, hp₅⟩ := parse_b5; exact (encWire_and_encMac_msgs_81 hinv hp₁ hp₂ hp₅).1.1
theorem encWire_msg2_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p₂ : PreKeyFields} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hp₂ : parsePreKeyWire SP.schedBCall2SendBytes = some p₂) : gamma compI0 S g (encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) = p₂.message.take (p₂.message.length - 8) := by obtain ⟨p₁, hp₁⟩ := parse_b1; obtain ⟨p₅, hp₅⟩ := parse_b5; exact (encWire_and_encMac_msgs_81 hinv hp₁ hp₂ hp₅).2.1.1
theorem encWire_msg5_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p₅ : PreKeyFields} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hp₅ : parsePreKeyWire SP.schedBCall5SendBytes = some p₅) : gamma compI0 S g (encWire tr₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2)) = p₅.message.take (p₅.message.length - 8) := by obtain ⟨p₁, hp₁⟩ := parse_b1; obtain ⟨p₂, hp₂⟩ := parse_b2; exact (encWire_and_encMac_msgs_81 hinv hp₁ hp₂ hp₅).2.2.1
set_option maxRecDepth 200000 in
theorem schedB2Fast_msg_bounds :
    (parsePreKeyWire Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2SendFast).map
      (fun p => decide (77 ≤ p.message.length ∧ p.message.length ≤ 1408)) = some true := by decide +kernel
theorem schedB2_msg_bounds {p : PreKeyFields} (hp : parsePreKeyWire SP.schedBCall2SendBytes = some p) : 77 ≤ p.message.length ∧ p.message.length ≤ 1408 := by
  have h := schedB2Fast_msg_bounds; unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2SendFast at h; rw [← SP.schedBCall2SendBytes_eq, hp] at h; exact of_decide_eq_true (Option.some.inj h)
set_option maxRecDepth 200000 in
theorem schedB5Fast_msg_bounds :
    (parsePreKeyWire Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall5SendFast).map
      (fun p => decide (77 ≤ p.message.length ∧ p.message.length ≤ 1408)) = some true := by decide +kernel
theorem schedB5_msg_bounds {p : PreKeyFields} (hp : parsePreKeyWire SP.schedBCall5SendBytes = some p) : 77 ≤ p.message.length ∧ p.message.length ≤ 1408 := by
  have h := schedB5Fast_msg_bounds; unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall5SendFast at h; rw [← SP.schedBCall5SendBytes_eq, hp] at h; exact of_decide_eq_true (Option.some.inj h)
theorem split81_wire_bounds_no_hp {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2))).length ∧ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2))).length ≤ 1400 ∧ 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ∧ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ≤ 1400 ∧ 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2))).length ∧ (gamma compI0 S g (Census443Defs.encWire tr₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2))).length ≤ 1400 := by
  obtain ⟨p₁, hp₁⟩ := parse_b1; obtain ⟨p₂, hp₂⟩ := parse_b2; obtain ⟨p₅, hp₅⟩ := parse_b5; have hb₁ := schedB1_msg_bounds hp₁; have hb₂ := schedB2_msg_bounds hp₂; have hb₅ := schedB5_msg_bounds hp₅; rw [encWire_msg1_81 hinv hp₁, encWire_msg2_81 hinv hp₂, encWire_msg5_81 hinv hp₅, List.length_take, List.length_take, List.length_take]; omega
theorem split81_wire_bounds {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (_hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2))).length ∧ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2))).length ≤ 1400 ∧ 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ∧ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ≤ 1400 ∧ 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2))).length ∧ (gamma compI0 S g (Census443Defs.encWire tr₅ (stA₂81 r tr₄) cl₅ (tr₅.length + 2))).length ≤ 1400 := split81_wire_bounds_no_hp hinv
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnWire
