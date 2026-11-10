/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupHighBitComp
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompSmallSubgroupTrace
open Symbolic.BugInjection
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.X25519 (isLowOrderKey leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
theorem hexBytes_ofList (cs : List Char) : hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by unfold hexBytes hexDigit; rw [String.toList_ofList]
def eventBytes : MachineEvent → HwBytes
  | .recv b | .rng b | .pt b | .send b | .accept b | .leak b => b
theorem eventBytes_recv (b : HwBytes) : eventBytes (.recv b) = b := rfl
theorem eventBytes_send (b : HwBytes) : eventBytes (.send b) = b := rfl
def call0Trace : List MachineEvent := Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 35
def call1Trace : List MachineEvent := (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 35).take 3
def highBitCall2Trace : List MachineEvent := Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 38
def torsionCall2Trace : List MachineEvent := Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.trace.drop 38
def bundleBytes : HwBytes := eventBytes (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.headD (.recv []))
def ptBytes : HwBytes := eventBytes ((Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 35).headD (.pt []))
def sentWireBytes : HwBytes := eventBytes ((Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 37).headD (.send []))
def highBitWireBytes : HwBytes := eventBytes ((Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 38).headD (.recv []))
def torsionWireBytes : HwBytes := eventBytes ((Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.trace.drop 38).headD (.recv []))
def aliceIdPubKey : HwBytes := hexBytes "5af779b498d5843151f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c"
def bobIdPubKey : HwBytes := hexBytes "f76d50f376882c6ffbadce584c2428aa82e885e515b532c0b04803ff8bac7f62"
def spkPubKey : HwBytes := hexBytes "b6b88896bce6c272053abf1c7717aca151d472728303ff4cea12496c9fe31418"
attribute [local irreducible] Symbolic.BugInjection.hexBytes
elab "chars_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id); let eWhnf ← Lean.Meta.whnf e; let args := eWhnf.getAppArgs; let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"
elab "str_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id); let eWhnf ← Lean.Meta.whnf e; let args := eWhnf.getAppArgs; let sLit ← Lean.Meta.whnf args[0]!
  return sLit
def aliceIdChars : List Char := chars_of_hex_def aliceIdPubKey
theorem aliceIdPubKey_eq : aliceIdPubKey = hexBytes.go hexDigit aliceIdChars := by change hexBytes (str_of_hex_def aliceIdPubKey) = _; rw [show (str_of_hex_def aliceIdPubKey) = String.ofList aliceIdChars from rfl, hexBytes_ofList]
def bobIdChars : List Char := chars_of_hex_def bobIdPubKey
theorem bobIdPubKey_eq : bobIdPubKey = hexBytes.go hexDigit bobIdChars := by change hexBytes (str_of_hex_def bobIdPubKey) = _; rw [show (str_of_hex_def bobIdPubKey) = String.ofList bobIdChars from rfl, hexBytes_ofList]
def spkChars : List Char := chars_of_hex_def spkPubKey
theorem spkPubKey_eq : spkPubKey = hexBytes.go hexDigit spkChars := by change hexBytes (str_of_hex_def spkPubKey) = _; rw [show (str_of_hex_def spkPubKey) = String.ofList spkChars from rfl, hexBytes_ofList]
def bundleChars : List Char := chars_of_hex_def bundleBytes
theorem bundle_head_eq : Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.headD (.recv []) = .recv (hexBytes (str_of_hex_def bundleBytes)) := rfl
theorem bundleBytes_eq_hex : bundleBytes = hexBytes (str_of_hex_def bundleBytes) := (congrArg eventBytes bundle_head_eq).trans (eventBytes_recv _)
theorem bundleStr_eq : (str_of_hex_def bundleBytes) = String.ofList bundleChars := rfl
theorem bundleBytes_eq : bundleBytes = hexBytes.go hexDigit bundleChars := by rw [bundleBytes_eq_hex, bundleStr_eq, hexBytes_ofList]
def bundleFast : HwBytes := hexBytes.go hexDigit bundleChars
theorem highBit_bundle_slices_fast : slice bundleFast 46 33 = ecKey (hexBytes.go hexDigit spkChars) ∧ slice bundleFast 79 64 = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spkSig ∧ slice bundleFast 147 1569 = kyberKey Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup.kyberPk ∧ slice bundleFast 1716 64 = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup.kyberPkSig ∧ slice bundleFast 1780 33 = ecKey (hexBytes.go hexDigit bobIdChars) := by decide +kernel
theorem highBit_bundle_slices : slice bundleBytes 46 33 = ecKey spkPubKey ∧ slice bundleBytes 79 64 = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spkSig ∧ slice bundleBytes 147 1569 = kyberKey Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup.kyberPk ∧ slice bundleBytes 1716 64 = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup.kyberPkSig ∧ slice bundleBytes 1780 33 = ecKey bobIdPubKey := by rw [bundleBytes_eq, spkPubKey_eq, bobIdPubKey_eq]; exact highBit_bundle_slices_fast
theorem torsion_bundle_slices : slice bundleBytes 46 33 = ecKey spkPubKey ∧ slice bundleBytes 79 64 = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.setup.spkSig ∧ slice bundleBytes 147 1569 = kyberKey Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.setup.kyberPk ∧ slice bundleBytes 1716 64 = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.setup.kyberPkSig ∧ slice bundleBytes 1780 33 = ecKey bobIdPubKey := highBit_bundle_slices
def sentWireChars : List Char := chars_of_hex_def sentWireBytes
theorem sentWire_head_eq : (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 37).headD (.send []) = .send (hexBytes (str_of_hex_def sentWireBytes)) := rfl
theorem sentWireBytes_eq_hex : sentWireBytes = hexBytes (str_of_hex_def sentWireBytes) := (congrArg eventBytes sentWire_head_eq).trans (eventBytes_send _)
theorem sentWireStr_eq : (str_of_hex_def sentWireBytes) = String.ofList sentWireChars := rfl
theorem sentWireBytes_eq : sentWireBytes = hexBytes.go hexDigit sentWireChars := by rw [sentWireBytes_eq_hex, sentWireStr_eq, hexBytes_ofList]
def sentWireFast : HwBytes := hexBytes.go hexDigit sentWireChars
def highBitWireChars : List Char := chars_of_hex_def highBitWireBytes
theorem highBitWire_head_eq : (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 38).headD (.recv []) = .recv (hexBytes (str_of_hex_def highBitWireBytes)) := rfl
theorem highBitWireBytes_eq_hex : highBitWireBytes = hexBytes (str_of_hex_def highBitWireBytes) := (congrArg eventBytes highBitWire_head_eq).trans (eventBytes_recv _)
theorem highBitWireStr_eq : (str_of_hex_def highBitWireBytes) = String.ofList highBitWireChars := rfl
theorem highBitWireBytes_eq : highBitWireBytes = hexBytes.go hexDigit highBitWireChars := by rw [highBitWireBytes_eq_hex, highBitWireStr_eq, hexBytes_ofList]
def highBitWireFast : HwBytes := hexBytes.go hexDigit highBitWireChars
theorem highBitWireFast_identityKey : (parsePreKeyWire highBitWireFast).map (fun p => p.identityKey.take 33) = some (ecKey (hexBytes.go hexDigit aliceIdChars)) := by decide +kernel
theorem highBitWireBytes_identityKey : (parsePreKeyWire highBitWireBytes).map (fun p => p.identityKey.take 33) = some (ecKey aliceIdPubKey) := by rw [highBitWireBytes_eq, aliceIdPubKey_eq]; exact highBitWireFast_identityKey
def torsionWireChars : List Char := chars_of_hex_def torsionWireBytes
theorem torsionWire_head_eq : (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.trace.drop 38).headD (.recv []) = .recv (hexBytes (str_of_hex_def torsionWireBytes)) := rfl
theorem torsionWireBytes_eq_hex : torsionWireBytes = hexBytes (str_of_hex_def torsionWireBytes) := (congrArg eventBytes torsionWire_head_eq).trans (eventBytes_recv _)
theorem torsionWireStr_eq : (str_of_hex_def torsionWireBytes) = String.ofList torsionWireChars := rfl
theorem torsionWireBytes_eq : torsionWireBytes = hexBytes.go hexDigit torsionWireChars := by rw [torsionWireBytes_eq_hex, torsionWireStr_eq, hexBytes_ofList]
def torsionWireFast : HwBytes := hexBytes.go hexDigit torsionWireChars
theorem torsionWireFast_identityKey : (parsePreKeyWire torsionWireFast).map (fun p => p.identityKey.take 33) = some (ecKey (hexBytes.go hexDigit aliceIdChars)) := by decide +kernel
theorem torsionWireBytes_identityKey : (parsePreKeyWire torsionWireBytes).map (fun p => p.identityKey.take 33) = some (ecKey aliceIdPubKey) := by rw [torsionWireBytes_eq, aliceIdPubKey_eq]; exact torsionWireFast_identityKey
theorem highBitComp_trace_eq_append_calls : call0Trace ++ (call1Trace ++ highBitCall2Trace) = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace := rfl
theorem torsionComp_trace_eq_append_calls : call0Trace ++ (call1Trace ++ torsionCall2Trace) = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.trace := rfl
theorem highBitComp_trace_decomp : Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace = call0Trace ++ call1Trace ++ highBitCall2Trace := by rw [List.append_assoc, highBitComp_trace_eq_append_calls]
theorem torsionComp_trace_decomp : Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.trace = call0Trace ++ call1Trace ++ torsionCall2Trace := by rw [List.append_assoc, torsionComp_trace_eq_append_calls]
theorem pqFromHonest_of_mem {sent : List HwBytes} {body : HwBytes} (hmem : body ∈ sent) : PqFromHonest sent body := by intro m hm; exact ⟨body, hmem, m, hm, rfl⟩
theorem highBit_wire_message_eq_sentBody_fast : (parsePreKeyWire highBitWireFast).map (·.message) = sentBody sentWireFast := by decide +kernel
theorem highBit_wire_message_eq_sentBody : (parsePreKeyWire highBitWireBytes).map (·.message) = sentBody sentWireBytes := by rw [highBitWireBytes_eq, sentWireBytes_eq]; exact highBit_wire_message_eq_sentBody_fast
theorem torsion_wire_message_eq_sentBody_fast : (parsePreKeyWire torsionWireFast).map (·.message) = sentBody sentWireFast := by decide +kernel
theorem torsion_wire_message_eq_sentBody : (parsePreKeyWire torsionWireBytes).map (·.message) = sentBody sentWireBytes := by rw [torsionWireBytes_eq, sentWireBytes_eq]; exact torsion_wire_message_eq_sentBody_fast
theorem highBit_wire_message_mem_sentBody : ∀ q, parsePreKeyWire highBitWireBytes = some q → q.message ∈ (sentBody sentWireBytes).toList := by intro q hq; have h := highBit_wire_message_eq_sentBody; rw [hq, Option.map_some] at h; rw [← h]; simp
theorem torsion_wire_message_mem_sentBody : ∀ q, parsePreKeyWire torsionWireBytes = some q → q.message ∈ (sentBody sentWireBytes).toList := by intro q hq; have h := torsion_wire_message_eq_sentBody; rw [hq, Option.map_some] at h; rw [← h]; simp
theorem highBit_pqFromHonest : ∀ q, parsePreKeyWire highBitWireBytes = some q → PqFromHonest (sentBody sentWireBytes).toList q.message :=
  fun q hq => pqFromHonest_of_mem (highBit_wire_message_mem_sentBody q hq)
theorem torsion_pqFromHonest : ∀ q, parsePreKeyWire torsionWireBytes = some q → PqFromHonest (sentBody sentWireBytes).toList q.message :=
  fun q hq => pqFromHonest_of_mem (torsion_wire_message_mem_sentBody q hq)
theorem highBitComp_honestBundle (i : ExternInterpretation) (r : Records) (hfits : Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.fits i r) (hSpk : pubBytes i (secretBytes r 2) = spkPubKey) (hBob : pubBytes i (secretBytes r 1) = bobIdPubKey) : HonestBundle i r bundleBytes := by obtain ⟨_, _, _, _, _, _, _, _, _, h5, h6, h7, _, _, _, _⟩ := hfits; intro _; dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecBytes, DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes, DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]; rw [hSpk, hBob, h5, h6, h7]; exact highBit_bundle_slices
theorem torsionComp_honestBundle (i : ExternInterpretation) (r : Records) (hfits : Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp.fits i r) (hSpk : pubBytes i (secretBytes r 2) = spkPubKey) (hBob : pubBytes i (secretBytes r 1) = bobIdPubKey) : HonestBundle i r bundleBytes := by obtain ⟨_, _, _, _, _, _, _, _, _, h5, h6, h7, _, _, _, _⟩ := hfits; intro _; dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecBytes, DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes, DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]; rw [hSpk, hBob, h5, h6, h7]; exact torsion_bundle_slices
end Symbolic.BugInjection.Proofs.Common443.CompSmallSubgroupTrace
