/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def sendAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with | some (.send b) => b | _ => []
theorem seg78_eq : ∃ b_pt b_rng, seg 78 3 = [.pt b_pt, .rng b_rng, .send (sendAt 80)] := ⟨_, _, rfl⟩
def wire80Chars : List Char := tf_chars_of_hex (sendAt 80)
theorem sendAt80_eq_hex : sendAt 80 = hexBytes (tf_str_of_hex (sendAt 80)) := rfl
theorem wire80Str_eq : (tf_str_of_hex (sendAt 80)) = String.ofList wire80Chars := rfl
def wire80Fast : HwBytes := hexBytes.go hexDigit wire80Chars
theorem sendAt80_eq_fast : sendAt 80 = wire80Fast := by change sendAt 80 = hexBytes.go hexDigit wire80Chars; rw [sendAt80_eq_hex, wire80Str_eq, hexBytes_ofList]
def preKeyAuthPrefix (b : HwBytes) : Option HwBytes := (parsePreKeyWire b).map (fun p => p.message.take (p.message.length - 8))
theorem sendAt80_head? : (sendAt 80).head? = some 0x03#8 := by rw [sendAt80_eq_fast]; decide +kernel
theorem sendAt80_head_ne_whisper : (sendAt 80).head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by rw [sendAt80_head?]; decide
theorem sendAt80_length_lt : (sendAt 80).length < 2 ^ 63 := by rw [sendAt80_eq_fast]; decide +kernel
theorem sendAt80_baseKey : (parsePreKeyWire (sendAt 80)).map (fun p => p.baseKey.take 33) = some (ecKey ek2PubKey) := by rw [sendAt80_eq_fast]; decide +kernel
theorem sendAt80_parses : ∃ p, parsePreKeyWire (sendAt 80) = some p := parses_of_map sendAt80_baseKey
theorem wireAt81_inner_ne_sendAt80_inner {p₈₁ p₈₀ : PreKeyFields} (hp₈₁ : parsePreKeyWire (wireAt 81) = some p₈₁) (hp₈₀ : parsePreKeyWire (sendAt 80) = some p₈₀) : p₈₁.message.take (p₈₁.message.length - 8) ≠ p₈₀.message.take (p₈₀.message.length - 8) := by
  have h : preKeyAuthPrefix (wireAt 81) ≠ preKeyAuthPrefix (sendAt 80) := by rw [wireAt81_eq_fast, sendAt80_eq_fast]; decide +kernel
  unfold preKeyAuthPrefix at h; rw [hp₈₁, hp₈₀, Option.map_some, Option.map_some, ne_eq, Option.some.injEq] at h; exact h
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
