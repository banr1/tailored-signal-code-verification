/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26WeakState

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.Census443Defs
theorem gamma_hmac_compI0 (S : Sem) (g : Ghost) (k m : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith (sha256CompressFunction compI0) (gamma compI0 S g k) (gamma compI0 S g m) := by
  unfold gamma gamma' DY.Libsignal.TripleRatchet.hmac
  show ((({salt := k, ikm := m} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll compI0 S g)).val = _
  rw [DY.Bytes.rec_eq (gKdf0 compI0) (gAll compI0 S g)]; rfl
theorem gamma_hmac_length (S : Sem) (g : Ghost) (k m : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).length = 32 := by rw [gamma_hmac_compI0]; exact sha256With_length (sha256CompressFunction compI0) _
theorem gamma_trunc8_eq (i : ExternInterpretation) (S : Sem) (g : Ghost) (a : DY.Bytes) : gamma i S g (DY.Trunc.trunc8 a) = (gamma i S g a).take 8 := by
  unfold gamma gamma'
  show ((({input := a} : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq gTrunc0 (gAll i S g)]; rfl
def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
theorem hexBytes_ofList (cs : List Char) : hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by unfold hexBytes hexDigit; rw [String.toList_ofList]
def evBytes : MachineEvent → HwBytes
  | .recv b | .rng b | .pt b | .send b | .accept b | .leak b => b
theorem evBytes_send (b : HwBytes) : evBytes (.send b) = b := rfl
attribute [local irreducible] Symbolic.BugInjection.hexBytes
elab "chars_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id); let eWhnf ← Lean.Meta.whnf e; let args := eWhnf.getAppArgs; let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"
elab "str_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id); let eWhnf ← Lean.Meta.whnf e; let args := eWhnf.getAppArgs; let sLit ← Lean.Meta.whnf args[0]!
  return sLit
def sentWireBytes : HwBytes := evBytes ((Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 37).headD (.send []))
def sentWireChars : List Char := chars_of_hex_def sentWireBytes
theorem sentWire_head_eq : (Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 37).headD (.send []) = .send (hexBytes (str_of_hex_def sentWireBytes)) := rfl
theorem sentWireStr_eq : (str_of_hex_def sentWireBytes) = String.ofList sentWireChars := rfl
theorem sentWireBytes_eq : sentWireBytes = hexBytes.go hexDigit sentWireChars := by have h : sentWireBytes = hexBytes (str_of_hex_def sentWireBytes) := (congrArg evBytes sentWire_head_eq).trans (evBytes_send _); rw [h, sentWireStr_eq, hexBytes_ofList]
def sentWireFast : HwBytes := hexBytes.go hexDigit sentWireChars
def wsCall1SendBytes : HwBytes := evBytes ((Symbolic.BugInjection.Witnesses.Cheval26WeakState.trace.drop 37).headD (.send []))
def wsCall1SendChars : List Char := chars_of_hex_def wsCall1SendBytes
theorem wsCall1SendStr_eq : (str_of_hex_def wsCall1SendBytes) = String.ofList wsCall1SendChars := rfl
def wsCall1SendFast : HwBytes := hexBytes.go hexDigit wsCall1SendChars
theorem gamma_hmac_key_of_take8 (S : Sem) (g : Ghost) (k m : DY.Bytes) (hk : (gamma compI0 S g k).length = 32) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).take 8) = some (gamma compI0 S g k) := by rw [gamma_hmac_compI0] at h ⊢; exact keyOfTake8_hmacWith _ _ hk h
theorem gamma_hmac_key_mem (S : Sem) (g : Ghost) (k m : DY.Bytes) (hk : (gamma compI0 S g k).length = 32) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).take 4 ≠ compTag4) : gamma compI0 S g k ∈ compHmacKeys32 := by rw [gamma_hmac_compI0] at h; exact hmacWith_untagged_key_mem _ _ hk h
theorem gamma_computeMac (S : Sem) (g : Ghost) (mk a b w : DY.Bytes) : gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk a b w) = (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac mk (Concat.concat a (Concat.concat b w)))).take 8 := by unfold DY.Libsignal.TripleRatchet.computeMac; rw [gamma_trunc8_eq]
theorem take4_take8 (l : HwBytes) : (l.take 8).take 4 = l.take 4 := by rw [List.take_take]; rfl
theorem keyOfTake8_computeMac (S : Sem) (g : Ghost) (mk a b w : DY.Bytes) (hk : (gamma compI0 S g mk).length = 32) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk a b w)).take 4 ≠ compTag4) : keyOfTake8 (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk a b w)) = some (gamma compI0 S g mk) := by rw [gamma_computeMac, take4_take8] at h; rw [gamma_computeMac]; exact gamma_hmac_key_of_take8 S g mk _ hk h
theorem computeMac_key_mem (S : Sem) (g : Ghost) (mk a b w : DY.Bytes) (hk : (gamma compI0 S g mk).length = 32) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk a b w)).take 4 ≠ compTag4) : gamma compI0 S g mk ∈ compHmacKeys32 := by rw [gamma_computeMac, take4_take8] at h; exact gamma_hmac_key_mem S g mk _ hk h
abbrev msgPrk (salt seed : DY.Bytes) : DY.Bytes := DY.Libsignal.TripleRatchet.hmac salt seed
theorem trMsgKeys_macKey_eq (salt seed : DY.Bytes) : (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey = DY.Libsignal.TripleRatchet.hkdfBlock2 (msgPrk salt seed) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") :=
  rfl
theorem gamma_msgPrk_length (S : Sem) (g : Ghost) (salt seed : DY.Bytes) : (gamma compI0 S g (msgPrk salt seed)).length = 32 := gamma_hmac_length S g salt seed
theorem gamma_macKey_length (S : Sem) (g : Ghost) (salt seed : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).length = 32 := by rw [trMsgKeys_macKey_eq]; unfold DY.Libsignal.TripleRatchet.hkdfBlock2; exact gamma_hmac_length S g _ _
theorem keyOfTake8_macKey (S : Sem) (g : Ghost) (salt seed : DY.Bytes) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).take 8) = some (gamma compI0 S g (msgPrk salt seed)) := by rw [trMsgKeys_macKey_eq] at h ⊢; unfold DY.Libsignal.TripleRatchet.hkdfBlock2 at h ⊢; exact gamma_hmac_key_of_take8 S g _ _ (gamma_msgPrk_length S g salt seed) h
theorem msgPrk_mem (S : Sem) (g : Ghost) (salt seed : DY.Bytes) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).take 4 ≠ compTag4) : gamma compI0 S g (msgPrk salt seed) ∈ compHmacKeys32 := by rw [trMsgKeys_macKey_eq] at h; unfold DY.Libsignal.TripleRatchet.hkdfBlock2 at h; exact gamma_hmac_key_mem S g _ _ (gamma_msgPrk_length S g salt seed) h
abbrev encSeed (stA : DY.Libsignal.TripleRatchet.TRState) : DY.Bytes := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
abbrev encKeys (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Libsignal.TripleRatchet.MessageKeys := DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) (encSeed stA)
abbrev encPrk (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes := msgPrk (encSalt tr₂ stA cl pq) (encSeed stA)
theorem encMac_eq (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : encMac tr₂ stA cl pq = DY.Libsignal.TripleRatchet.computeMac (encKeys tr₂ stA cl pq).macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq) :=
  rfl
theorem keyOfTake8_encMac (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (h : (gamma compI0 S g (encMac tr₂ stA cl pq)).take 4 ≠ compTag4) : keyOfTake8 (gamma compI0 S g (encMac tr₂ stA cl pq)) = some (gamma compI0 S g (encKeys tr₂ stA cl pq).macKey) := by rw [encMac_eq] at h ⊢; exact keyOfTake8_computeMac S g _ _ _ _ (gamma_macKey_length S g _ _) h
theorem encMacKey_mem (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (h : (gamma compI0 S g (encMac tr₂ stA cl pq)).take 4 ≠ compTag4) : gamma compI0 S g (encKeys tr₂ stA cl pq).macKey ∈ compHmacKeys32 := by rw [encMac_eq] at h; exact computeMac_key_mem S g _ _ _ _ (gamma_macKey_length S g _ _) h
theorem keyOfTake8_encMacKey (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (h : (gamma compI0 S g (encKeys tr₂ stA cl pq).macKey).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (encKeys tr₂ stA cl pq).macKey).take 8) = some (gamma compI0 S g (encPrk tr₂ stA cl pq)) := keyOfTake8_macKey S g _ _ h
def msgMac8 (p : PreKeyFields) : HwBytes := p.message.drop (p.message.length - 8)
def macChainOk (k P : HwBytes) (p : PreKeyFields) : Bool := ((msgMac8 p).take 4 != compTag4) && (keyOfTake8 (msgMac8 p) == some k) && (k.take 4 != compTag4) && (keyOfTake8 (k.take 8) == some P)
def wireMacChainOk (k P w : HwBytes) : Bool :=
  match parsePreKeyWire w with
  | some p => macChainOk k P p
  | none => false
theorem macChainOk_spec {k P : HwBytes} {p : PreKeyFields} (h : macChainOk k P p = true) : (msgMac8 p).take 4 ≠ compTag4 ∧ keyOfTake8 (msgMac8 p) = some k ∧ k.take 4 ≠ compTag4 ∧ keyOfTake8 (k.take 8) = some P := by simp only [macChainOk, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
theorem macChainOk_of_wire {k P w : HwBytes} (h : wireMacChainOk k P w = true) {p : PreKeyFields} (hp : parsePreKeyWire w = some p) : macChainOk k P p = true := by unfold wireMacChainOk at h; rw [hp] at h; exact h
theorem encMac_chain_of_macChainOk (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) {k P : HwBytes} {p : PreKeyFields} (hmac : gamma compI0 S g (encMac tr₂ stA cl pq) = msgMac8 p) (hok : macChainOk k P p = true) : gamma compI0 S g (encKeys tr₂ stA cl pq).macKey = k ∧ gamma compI0 S g (encPrk tr₂ stA cl pq) = P ∧ k ∈ compHmacKeys32 ∧ P ∈ compHmacKeys32 := by
  obtain ⟨h1, h2, h3, h4⟩ := macChainOk_spec hok
  have htag : (gamma compI0 S g (encMac tr₂ stA cl pq)).take 4 ≠ compTag4 := by rw [hmac]; exact h1
  have hk : gamma compI0 S g (encKeys tr₂ stA cl pq).macKey = k := (by have hrec := keyOfTake8_encMac S g tr₂ stA cl pq htag; rw [hmac, h2] at hrec; exact (Option.some.inj hrec).symm)
  have htag2 : (gamma compI0 S g (encKeys tr₂ stA cl pq).macKey).take 4 ≠ compTag4 := by rw [hk]; exact h3
  have hP : gamma compI0 S g (encPrk tr₂ stA cl pq) = P := (by have hrec := keyOfTake8_encMacKey S g tr₂ stA cl pq htag2; rw [hk, h4] at hrec; exact (Option.some.inj hrec).symm); refine ⟨hk, hP, ?_, ?_⟩
  · rw [← hk]; exact encMacKey_mem S g tr₂ stA cl pq htag
  · rw [← hP]; exact msgPrk_mem S g _ _ htag2
def wsMacKey : HwBytes := [57, 0, 208, 163, 69, 193, 232, 212, 124, 95, 127, 218, 65, 194, 127, 66, 236, 188, 184, 18, 216, 32, 180, 137, 222, 237, 167, 51, 15, 37, 86, 17]
def wsPrk : HwBytes := [187, 54, 226, 4, 174, 10, 19, 17, 48, 253, 69, 170, 58, 219, 155, 75, 22, 174, 233, 236, 92, 150, 239, 156, 118, 0, 90, 186, 220, 57, 25, 240]
def sentMacKey : HwBytes := [20, 3, 188, 130, 119, 143, 217, 72, 157, 239, 67, 105, 178, 178, 164, 46, 30, 186, 183, 19, 153, 104, 123, 2, 71, 99, 200, 151, 235, 134, 6, 250]
def sentPrk : HwBytes := [236, 40, 252, 150, 105, 199, 198, 128, 35, 70, 217, 189, 211, 63, 111, 207, 22, 129, 123, 79, 59, 204, 184, 95, 185, 131, 78, 193, 69, 40, 123, 253]
def sentSalt : HwBytes := [181, 57, 155, 33, 50, 17, 241, 136, 127, 15, 197, 133, 53, 224, 118, 119, 90, 175, 241, 41, 154, 65, 130, 131, 225, 135, 169, 167, 26, 198, 167, 220]
theorem wireMacChainOk_wsCall1SendFast : wireMacChainOk wsMacKey wsPrk wsCall1SendFast = true := by decide +kernel
theorem wireMacChainOk_sentWireFast : wireMacChainOk sentMacKey sentPrk sentWireFast = true := by decide +kernel
theorem wireMacChainOk_sentWire : wireMacChainOk sentMacKey sentPrk sentWireBytes = true := by rw [sentWireBytes_eq]; exact wireMacChainOk_sentWireFast
end Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
