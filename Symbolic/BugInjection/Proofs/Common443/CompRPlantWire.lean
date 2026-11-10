/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupHighBitComp
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp
public import Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompRPlantWire
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (canonicalVariation encodeField encodeWith)
open DY.Libsignal.Composed.Refinement (PreKeyFields parsePreKeyWire)
open Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
theorem hexBytes_ofList (cs : List Char) : hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by unfold hexBytes hexDigit; rw [String.toList_ofList]
def eventBytes : MachineEvent → HwBytes
  | .recv b | .rng b | .pt b | .send b | .accept b | .leak b => b
theorem eventBytes_recv (b : HwBytes) : eventBytes (.recv b) = b := rfl
theorem eventBytes_send (b : HwBytes) : eventBytes (.send b) = b := rfl
attribute [local irreducible] Symbolic.BugInjection.hexBytes
elab "chars_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id); let eWhnf ← Lean.Meta.whnf e; let args := eWhnf.getAppArgs; let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"
elab "str_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id); let eWhnf ← Lean.Meta.whnf e; let args := eWhnf.getAppArgs; let sLit ← Lean.Meta.whnf args[0]!
  return sLit
def canonicalVariationFast : DY.Libsignal.Refinement.EncodingVariation := ⟨4, [], 0, 0, [.known 1 0 0, .known 2 0 0, .known 3 0 0, .known 4 0 0]⟩
theorem canonicalVariationFast_eq : canonicalVariationFast = canonicalVariation :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.canonicalVariation_eq.symm
def innerWirePrefixAt (c : Nat) (p : PreKeyFields) : HwBytes := encodeWith canonicalVariation ⟨4, p.inner.senderRatchetKey.bytes.toList, c, 0, p.inner.ciphertext⟩ ++ encodeField 5 0 0 (.bytes p.inner.pqRatchet)
def innerWirePrefixAtFast (c : Nat) (p : PreKeyFields) : HwBytes := encodeWith canonicalVariationFast ⟨4, p.inner.senderRatchetKey.bytes.toList, c, 0, p.inner.ciphertext⟩ ++ encodeField 5 0 0 (.bytes p.inner.pqRatchet)
theorem innerWirePrefixAtFast_eq (c : Nat) (p : PreKeyFields) : innerWirePrefixAtFast c p = innerWirePrefixAt c p := by
  unfold innerWirePrefixAtFast innerWirePrefixAt; rw [canonicalVariationFast_eq]
def InnerWireCanonicalAt (c : Nat) (p : PreKeyFields) : Prop := p.inner.counter = c ∧ p.inner.messageVersion = 4 ∧ p.message.take (p.message.length - 8) = innerWirePrefixAt c p ++ (p.message.take (p.message.length - 8)).drop (innerWirePrefixAt c p).length
def checkInnerWireCanonicalAt (c : Nat) (w : HwBytes) : Bool :=
  match parsePreKeyWire w with
  | none => false
  | some p =>
    decide (p.inner.counter = c) && decide (p.inner.messageVersion = 4) &&
    decide (p.message.take (p.message.length - 8) = innerWirePrefixAtFast c p ++ (p.message.take (p.message.length - 8)).drop (innerWirePrefixAtFast c p).length)
theorem innerWireCanonicalAt_of_check {c : Nat} {w : HwBytes} (h : checkInnerWireCanonicalAt c w = true) : (∃ p, parsePreKeyWire w = some p ∧ InnerWireCanonicalAt c p) ∧ (∀ p, parsePreKeyWire w = some p → InnerWireCanonicalAt c p) := by
  unfold checkInnerWireCanonicalAt at h
  cases hp : parsePreKeyWire w with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h; simp only [Bool.and_eq_true, decide_eq_true_eq, innerWirePrefixAtFast_eq] at h; have hcan : InnerWireCanonicalAt c p := ⟨h.1.1, h.1.2, h.2⟩; refine ⟨⟨p, rfl, hcan⟩, fun q hq => ?_⟩; cases hq; exact hcan
theorem innerWireCanonical_of_check {w : HwBytes} (h : checkInnerWireCanonicalAt 0 w = true) : (∃ p, parsePreKeyWire w = some p ∧ InnerWireCanonical p) ∧ (∀ p, parsePreKeyWire w = some p → InnerWireCanonical p) := innerWireCanonicalAt_of_check h
def sentWireBytes : HwBytes := eventBytes ((Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 37).headD (.send []))
def highBitWireBytes : HwBytes := eventBytes ((Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 38).headD (.recv []))
def torsionWireBytes : HwBytes := eventBytes ((Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.trace.drop 38).headD (.recv []))
def sentWireChars : List Char := chars_of_hex_def sentWireBytes
theorem sentWire_head_eq : (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 37).headD (.send []) = .send (hexBytes (str_of_hex_def sentWireBytes)) := rfl
theorem sentWireStr_eq : (str_of_hex_def sentWireBytes) = String.ofList sentWireChars := rfl
theorem sentWireBytes_eq : sentWireBytes = hexBytes.go hexDigit sentWireChars := by have h : sentWireBytes = hexBytes (str_of_hex_def sentWireBytes) := (congrArg eventBytes sentWire_head_eq).trans (eventBytes_send _); rw [h, sentWireStr_eq, hexBytes_ofList]
def sentWireFast : HwBytes := hexBytes.go hexDigit sentWireChars
theorem check_sentWireFast : checkInnerWireCanonicalAt 0 sentWireFast = true := by decide +kernel
theorem sentWireBytes_innerWireCanonical : (∃ p, parsePreKeyWire sentWireBytes = some p ∧ InnerWireCanonical p) ∧ (∀ p, parsePreKeyWire sentWireBytes = some p → InnerWireCanonical p) := by rw [sentWireBytes_eq]; exact innerWireCanonical_of_check check_sentWireFast
def highBitWireChars : List Char := chars_of_hex_def highBitWireBytes
theorem highBitWire_head_eq : (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 38).headD (.recv []) = .recv (hexBytes (str_of_hex_def highBitWireBytes)) := rfl
theorem highBitWireStr_eq : (str_of_hex_def highBitWireBytes) = String.ofList highBitWireChars := rfl
theorem highBitWireBytes_eq : highBitWireBytes = hexBytes.go hexDigit highBitWireChars := by have h : highBitWireBytes = hexBytes (str_of_hex_def highBitWireBytes) := (congrArg eventBytes highBitWire_head_eq).trans (eventBytes_recv _); rw [h, highBitWireStr_eq, hexBytes_ofList]
def highBitWireFast : HwBytes := hexBytes.go hexDigit highBitWireChars
theorem check_highBitWireFast : checkInnerWireCanonicalAt 0 highBitWireFast = true := by decide +kernel
theorem highBitWireBytes_innerWireCanonical : (∃ p, parsePreKeyWire highBitWireBytes = some p ∧ InnerWireCanonical p) ∧ (∀ p, parsePreKeyWire highBitWireBytes = some p → InnerWireCanonical p) := by rw [highBitWireBytes_eq]; exact innerWireCanonical_of_check check_highBitWireFast
def torsionWireChars : List Char := chars_of_hex_def torsionWireBytes
theorem torsionWire_head_eq : (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.trace.drop 38).headD (.recv []) = .recv (hexBytes (str_of_hex_def torsionWireBytes)) := rfl
theorem torsionWireStr_eq : (str_of_hex_def torsionWireBytes) = String.ofList torsionWireChars := rfl
theorem torsionWireBytes_eq : torsionWireBytes = hexBytes.go hexDigit torsionWireChars := by have h : torsionWireBytes = hexBytes (str_of_hex_def torsionWireBytes) := (congrArg eventBytes torsionWire_head_eq).trans (eventBytes_recv _); rw [h, torsionWireStr_eq, hexBytes_ofList]
def torsionWireFast : HwBytes := hexBytes.go hexDigit torsionWireChars
theorem check_torsionWireFast : checkInnerWireCanonicalAt 0 torsionWireFast = true := by decide +kernel
theorem torsionWireBytes_innerWireCanonical : (∃ p, parsePreKeyWire torsionWireBytes = some p ∧ InnerWireCanonical p) ∧ (∀ p, parsePreKeyWire torsionWireBytes = some p → InnerWireCanonical p) := by rw [torsionWireBytes_eq]; exact innerWireCanonical_of_check check_torsionWireFast
end Symbolic.BugInjection.Proofs.Common443.CompRPlantWire
