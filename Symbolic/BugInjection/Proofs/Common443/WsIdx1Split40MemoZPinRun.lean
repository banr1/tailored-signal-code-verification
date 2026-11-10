/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public import Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPinRun
namespace SP
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins (saltAndSeedPin_of_macChainOk macChainOk_of_wire wireMacChainOk macChainOk ws3Prk_pin ws3MacKey ws3Prk wsSeed2Bytes encKeys encSeed msgMac8 gamma_computeMac gamma_hmac_compI0)
end SP
open ByteSpecs CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin
theorem wsSeed2Bytes_eq : SP.wsSeed2Bytes = WsIdx1O4Tag.wsSeed2 := by decide
def wsMacD2 : HwBytes := hmacWith WsIdx1O4Tag.F0 SP.ws3MacKey WsIdx1O4Tag.wsMacIn2
set_option maxRecDepth 200000 in theorem wsMacD2_untagged : wsMacD2.take 4 ≠ compTag4 := by decide +kernel
def wire40Ok (w : HwBytes) : Bool := SP.wireMacChainOk SP.ws3MacKey SP.ws3Prk w && ((parsePreKeyWire w).map SP.msgMac8 == some (wsMacD2.take 8))
set_option maxRecDepth 200000 in theorem wire40Ok_fast : wire40Ok WsIdx1Split40OwnSalt.wire3Idx1Fast = true := by decide +kernel
theorem wire40Ok_wire3 : wire40Ok wire3Idx1Bytes = true := by rw [WsIdx1Split40OwnSalt.wire3Idx1Bytes_eq_fast]; exact wire40Ok_fast
theorem macChainOk_wire3 {p : PreKeyFields} (hp : parsePreKeyWire wire3Idx1Bytes = some p) : SP.macChainOk SP.ws3MacKey SP.ws3Prk p = true := by
  have h := wire40Ok_wire3; simp only [wire40Ok, Bool.and_eq_true] at h; exact SP.macChainOk_of_wire h.1 hp
theorem wsMac8 {p : PreKeyFields} (hp : parsePreKeyWire wire3Idx1Bytes = some p) : SP.msgMac8 p = wsMacD2.take 8 := by
  have h := wire40Ok_wire3; simp only [wire40Ok, Bool.and_eq_true, beq_iff_eq, hp, Option.map_some] at h; exact Option.some.inj h.2
theorem wsMacD2_mem : wsMacD2 ∈ CompRI0TermInj.rowDigests := (CompRI0TermInj.hmacWith_tag_or_row _ _).resolve_left wsMacD2_untagged
theorem rowDigests_take8_inj {D₁ D₂ : HwBytes} (h₁ : D₁ ∈ CompRI0TermInj.rowDigests) (h₂ : D₂ ∈ CompRI0TermInj.rowDigests) (h : D₁.take 8 = D₂.take 8) : D₁ = D₂ := by
  have hnd : (CompRI0TermInj.rowDigests.map fun D => D.take 8).Nodup := by unfold CompRI0TermInj.rowDigests; rw [List.map_map]; exact CompRNbscTable.rows_take8_nodup
  exact List.inj_on_of_nodup_map hnd h₁ h₂ h
private theorem take4_of_take8 {a b : HwBytes} (h : a.take 8 = b.take 8) : a.take 4 = b.take 4 := by
  simpa only [List.take_take, Nat.min_def, show (4 : Nat) ≤ 8 by decide, ↓reduceIte] using congrArg (List.take 4) h
theorem macIn_of_take8 {M : HwBytes} (h8 : (hmacWith WsIdx1O4Tag.F0 SP.ws3MacKey M).take 8 = wsMacD2.take 8) : M = WsIdx1O4Tag.wsMacIn2 := by
  have hu : (hmacWith WsIdx1O4Tag.F0 SP.ws3MacKey M).take 4 ≠ compTag4 := by rw [take4_of_take8 h8]; exact wsMacD2_untagged
  have hD := rowDigests_take8_inj ((CompRI0TermInj.hmacWith_tag_or_row _ _).resolve_left hu) wsMacD2_mem h8
  exact (CompRI0ShaInj.hmacWith_inj_of_untagged (k₁ := SP.ws3MacKey) rfl (by decide) hu hD).2
theorem msgPin (S : Sem) (g : Ghost) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) {p : PreKeyFields} (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hk : gamma compI0 S g (SP.encKeys tr stA cl (tr.length + 2)).macKey = SP.ws3MacKey) (hmac : gamma compI0 S g (encMac tr stA cl (tr.length + 2)) = SP.msgMac8 p) : gamma compI0 S g (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr stA cl (tr.length + 2)))) = WsIdx1O4Tag.wsMacIn2 := by apply macIn_of_take8; rw [← wsMac8 hp, ← hmac, ← hk]; change _ = gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac (SP.encKeys tr stA cl (tr.length + 2)).macKey stA.myIk stA.peerIk (encWire tr stA cl (tr.length + 2))); rw [SP.gamma_computeMac, SP.gamma_hmac_compI0]
def Split40Ck1Pin : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → gamma compI0 S g (ck1Salt40 r tr₁) = WsIdx1O4Tag.wsSalt1
theorem split40ZPins_of (hck : Split40Ck1Pin) : Split40ZPins := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv; have hmac' : gamma compI0 S g (encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) = SP.msgMac8 p := (hinv.hwire₂ p hp).2.1; obtain ⟨hk, _, _, hseed⟩ := SP.saltAndSeedPin_of_macChainOk S g tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ hmac' (macChainOk_wire3 hp) SP.ws3Prk_pin; exact ⟨hseed.trans wsSeed2Bytes_eq, msgPin S g tr₃ _ cl₂ hp hk hmac', hck r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv⟩
theorem split40ZTagInj_of_ck1 (hck : Split40Ck1Pin) : Split40ZTagInj := split40ZTagInj_of_pins (split40ZPins_of hck)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPinRun
