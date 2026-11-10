/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
public meta import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public meta import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakStateIdx1
public meta import Symbolic.Specifications.Concrete.ByteSpecs
public meta import Symbolic.Specifications.Concrete.ExternInterpretation
public meta import Symbolic.Specifications.Refinement.TraceExplanation

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
abbrev F0 : ShaState → HwBytes → ShaState := sha256CompressFunction compI0
def ivNat : Nat := bytesToNat (shaStateBytes sha256IV)
def digestOfOut (o : Nat) : HwBytes := (shaStateOfBytes (leBytes 32 o)).toList.flatMap (toBEBytes 4)
def rowOfTake8 (v : HwBytes) : Option (Nat × Nat × Nat) := compSha256Rows.find? fun r => (digestOfOut r.2.2).take 8 == v
def rowByOut (o : Nat) : Option (Nat × Nat × Nat) := compSha256Rows.find? fun r => r.2.2 == o
def keyOfRow1 (r : Nat × Nat × Nat) : HwBytes := ((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).take 32
def keyOfTake8 (v : HwBytes) : Option HwBytes :=
  match rowOfTake8 v with | none => none | some r2 => match rowByOut r2.1 with | none => none | some r1 => if r1.1 = ivNat then some (keyOfRow1 r1) else none
def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
theorem hexBytes_ofList (cs : List Char) : hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by unfold hexBytes hexDigit; rw [String.toList_ofList]
section FastHex
attribute [local irreducible] Symbolic.BugInjection.hexBytes
elab "chars_of_hex_def" id:ident : term => do
  let eWhnf ← Lean.Meta.whnf (Lean.mkConst (← Lean.resolveGlobalConstNoOverload id))
  match ← Lean.Meta.whnf eWhnf.getAppArgs[0]! with | .lit (.strVal s) => return Lean.toExpr s.toList | sLit => throwError "not strVal: {sLit}"
def wsCall1SendBytes : HwBytes := Census443Defs.eventBytes ((Witnesses.Cheval26WeakStateIdx1.trace.drop 37).headD (.send []))
def wsCall2SendBytes : HwBytes := Census443Defs.eventBytes ((Witnesses.Cheval26WeakStateIdx1.trace.drop 39).headD (.send []))
def wsCall1SendFast : HwBytes := hexBytes.go hexDigit (chars_of_hex_def wsCall1SendBytes)
def wsCall2SendFast : HwBytes := hexBytes.go hexDigit (chars_of_hex_def wsCall2SendBytes)
end FastHex
def wsSaltZ : HwBytes := List.replicate 32 0#8
def ws1MacKey : HwBytes := [57, 0, 208, 163, 69, 193, 232, 212, 124, 95, 127, 218, 65, 194, 127, 66, 236, 188, 184, 18, 216, 32, 180, 137, 222, 237, 167, 51, 15, 37, 86, 17]
def ws1Prk : HwBytes := [187, 54, 226, 4, 174, 10, 19, 17, 48, 253, 69, 170, 58, 219, 155, 75, 22, 174, 233, 236, 92, 150, 239, 156, 118, 0, 90, 186, 220, 57, 25, 240]
def wsSalt1 : HwBytes := [117, 101, 207, 237, 172, 88, 7, 20, 94, 126, 243, 182, 84, 254, 20, 66, 172, 96, 97, 156, 179, 198, 46, 30, 247, 246, 247, 198, 68, 58, 11, 138]
def ws2MacKey : HwBytes := [114, 127, 169, 60, 91, 52, 199, 80, 101, 192, 3, 134, 56, 105, 7, 52, 114, 241, 239, 250, 80, 195, 8, 61, 18, 159, 46, 1, 166, 229, 124, 3]
def ws2Prk : HwBytes := [218, 60, 112, 85, 168, 5, 198, 88, 0, 67, 68, 248, 250, 106, 86, 99, 10, 117, 19, 237, 185, 102, 31, 145, 90, 242, 107, 126, 210, 166, 108, 15]
def wsSalt2 : HwBytes := [3, 135, 79, 214, 65, 239, 215, 73, 23, 43, 93, 228, 9, 241, 97, 76, 22, 238, 115, 16, 46, 97, 110, 254, 183, 166, 247, 35, 87, 20, 76, 122]
def ws5MacKey : HwBytes := [60, 238, 34, 191, 113, 216, 201, 115, 190, 55, 54, 114, 242, 214, 84, 235, 177, 49, 156, 101, 134, 22, 207, 107, 247, 59, 36, 25, 251, 233, 78, 66]
def ws5Prk : HwBytes := [170, 186, 92, 242, 242, 140, 67, 185, 79, 184, 102, 212, 124, 54, 127, 168, 80, 191, 161, 221, 87, 172, 137, 141, 221, 253, 22, 10, 141, 69, 123, 15]
def wsSalt5 : HwBytes := [32, 235, 61, 216, 224, 48, 56, 38, 58, 71, 234, 77, 62, 147, 122, 119, 64, 243, 207, 133, 153, 241, 175, 174, 72, 83, 193, 34, 71, 164, 22, 175]
def wsSalts40 : List HwBytes := [wsSaltZ, wsSalt1, wsSalt2]
def wsSalts81 : List HwBytes := [wsSaltZ, wsSalt1, wsSalt2, wsSalt5]
def msg32OfHmac (P : HwBytes) : HwBytes :=
  match rowOfTake8 (P.take 8) with | none => [] | some r2 => match rowOfTake8 (((leBytes 64 r2.2.1).take 32).take 8) with | none => [] | some r1 => (leBytes 64 r1.2.1).take 32
elab "eval_hwbytes " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t (some (Lean.mkConst ``HwBytes)); Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  return Lean.toExpr (← unsafe Lean.Meta.evalExpr (List (BitVec 8)) (Lean.mkConst ``HwBytes) e)
def wsSeed1 : HwBytes := eval_hwbytes (msg32OfHmac ws1Prk)
def wsSeed2 : HwBytes := eval_hwbytes (msg32OfHmac ws2Prk)
def wsSeed5 : HwBytes := eval_hwbytes (msg32OfHmac ws5Prk)
def wsSeed6 : HwBytes := eval_hwbytes ((shaStateOfBytes (leBytes 32 0xcbd75b4faf2ec43d66b76e505c95c64adc2109f26aecccac5a68a74b89f1fa25)).toList.flatMap (toBEBytes 4))
def wsInnerWire1 : HwBytes := eval_hwbytes (match parsePreKeyWire wsCall1SendFast with | some p => p.message.take (p.message.length - 8) | none => [])
def wsInnerWire2 : HwBytes := eval_hwbytes (match parsePreKeyWire wsCall2SendFast with | some p => p.message.take (p.message.length - 8) | none => [])
def wsMacIn1 : HwBytes := eval_hwbytes (ecKey (compLookupPub (clamp Witnesses.Cheval26WeakStateIdx1.setup.aliceId)) ++ (ecKey (compLookupPub (clamp Witnesses.Cheval26WeakStateIdx1.setup.bobId)) ++ wsInnerWire1))
def wsMacIn2 : HwBytes := eval_hwbytes (ecKey (compLookupPub (clamp Witnesses.Cheval26WeakStateIdx1.setup.aliceId)) ++ (ecKey (compLookupPub (clamp Witnesses.Cheval26WeakStateIdx1.setup.bobId)) ++ wsInnerWire2))
theorem wsMacIn1_def : ecKey (compLookupPub (clamp Witnesses.Cheval26WeakStateIdx1.setup.aliceId)) ++ (ecKey (compLookupPub (clamp Witnesses.Cheval26WeakStateIdx1.setup.bobId)) ++ wsInnerWire1) = wsMacIn1 := by decide +kernel
def wmkInfo1 : HwBytes := "WhisperMessageKeys".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [1#8]
def wmkLit : HwBytes := "WhisperMessageKeys".toList.map (fun c => BitVec.ofNat 8 c.toNat)
def saltedValsFor (seed macIn salt : HwBytes) : List HwBytes :=
  let prk := hmacWith F0 salt seed; let ck := hmacWith F0 prk wmkInfo1; let mk := hmacWith F0 prk (ck ++ (wmkLit ++ [2#8]))
  let iv := hmacWith F0 prk (mk ++ (wmkLit ++ [3#8])); let macFull := hmacWith F0 mk macIn; [prk, ck, mk, iv, macFull, macFull.take 8]
def sig (v : HwBytes) : Nat × HwBytes := (v.length, v.take 8)
def sigTabFor (seed macIn : HwBytes) (salts : List HwBytes) : List (Nat × HwBytes) := salts.flatMap fun s => (saltedValsFor seed macIn s).map sig
theorem saltedVals6_tagged : (wsSalts81.all fun s => (saltedValsFor wsSeed6 wsMacIn1 s).all fun v => (v.take 4 == compTag4) && (v.length == 32 || v.length == 8)) = true := by decide +kernel
theorem sigTab6_inj : (sigTabFor wsSeed6 wsMacIn1 wsSalts81).Nodup := by decide +kernel
theorem saltedVals2_z_s1_tagged : ([wsSaltZ, wsSalt1].all fun s => (saltedValsFor wsSeed2 wsMacIn2 s).all fun v => (v.take 4 == compTag4) && (v.length == 32 || v.length == 8)) = true := by decide +kernel
theorem sigTab40_inj : (sigTabFor wsSeed2 wsMacIn2 wsSalts40).Nodup := by decide +kernel
end Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
