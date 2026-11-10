/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPin
namespace SP
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins (gamma_computeMac gamma_hmac_compI0 saltAndSeedPin_of_macChainOk macChainOk_of_wire wireMacChainOk wireMacChainOk_b6 schedBCall6RecvBytes wsMacKey wsPrk wsPrk_pin msgMac8)
end SP
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.TripleRatchet (TRState)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
set_option maxRecDepth 200000 in theorem wireMacChainOk_wire6Idx1Fast : SP.wireMacChainOk SP.wsMacKey SP.wsPrk wire6Idx1Fast = true := by decide +kernel
theorem wireMacChainOk_wire6Idx1 : SP.wireMacChainOk SP.wsMacKey SP.wsPrk wire6Idx1Bytes = true := by rw [wire6Idx1Bytes_eq]; exact wireMacChainOk_wire6Idx1Fast
theorem gamma_ck1Salt40_ws81Idx1 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : gamma compI0 S g (ck1Salt40 r tr₁) = wsSalt1 ∧ gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (stA81 r tr₁).cks).2 = wsSeed1 := by obtain ⟨_, _, hSalt, hSeed⟩ := SP.saltAndSeedPin_of_macChainOk S g tr₂ (stA81 r tr₁) cl₁ (hinv.hwire₁ p hp).2.1 (SP.macChainOk_of_wire wireMacChainOk_wire6Idx1 hp) SP.wsPrk_pin; unfold stA81 at hSalt; rw [CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ r.bob _ cl₁] at hSalt; exact ⟨hSalt, hSeed⟩
theorem gamma_saltedNodes81 (r : Records) (S : Sem) (g : Ghost) (salt : DY.Bytes) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) {seed macIn saltB : HwBytes} (hsalt : gamma compI0 S g salt = saltB) (hseed : gamma compI0 S g (bobSeed81 r tr₁ tr₂ tr₄ cl₁) = seed) (hmsg : gamma compI0 S g (DY.Concat.concat (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)) (DY.Concat.concat (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)) (encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2)))) = macIn) : (saltedNodes81 r salt tr₁ tr₂ tr₄ cl₁).map (gamma compI0 S g) = saltedValsFor seed macIn saltB := by subst hsalt hseed hmsg; simp only [saltedNodes81, saltedValsFor, DY.Libsignal.TripleRatchet.trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock1, DY.Libsignal.TripleRatchet.hkdfBlock2, DY.Libsignal.TripleRatchet.hkdfBlock3, List.map_cons, List.map_nil, SP.gamma_computeMac, SP.gamma_hmac_compI0, CompFreshDistinct.gamma_concat_eq, gamma_wmk, gamma_litByte, ofByteArray_one, ofByteArray_two, ofByteArray_three, wmkInfo1_eq]
theorem gamma_bobSeed81 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : gamma compI0 S g (bobSeed81 r tr₁ tr₂ tr₄ cl₁) = WsIdx1O4Tag.wsSeed6 := by obtain ⟨hs0, hs1, hs2, hpub6, hEq⟩ := fits_secrets hfits; exact gamma_bobSeed0_ws81Idx1 (split81PinObl r hfits) hEq hs0 hs1 hs2 hpub6 hp hinv
theorem gamma_serializedIk_0_of_fits {r : Records} {S : Sem} {g : Ghost} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) : gamma compI0 S g (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)) = ecKey (compLookupPub (clamp setup.aliceId)) := by obtain ⟨hs0, _, _, _, _⟩ := fits_secrets hfits; unfold DY.Libsignal.PQXDH.serializedIk DY.Libsignal.PQXDH.encodeEC ecKey; rw [gamma_concat0, gamma_litByte0, gamma_setupPublic_0 (split81PinObl r hfits) hc, hs0]; rfl
theorem gamma_serializedIk_2_of_fits {r : Records} {S : Sem} {g : Ghost} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) : gamma compI0 S g (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)) = ecKey (compLookupPub (clamp setup.bobId)) := by obtain ⟨_, hs1, _, _, _⟩ := fits_secrets hfits; unfold DY.Libsignal.PQXDH.serializedIk DY.Libsignal.PQXDH.encodeEC ecKey; rw [gamma_concat0, gamma_litByte0, gamma_setupPublic_2 (split81PinObl r hfits) hc, hs1]; rfl
set_option maxRecDepth 200000 in
theorem wire6Idx1Fast_wire :
    (parsePreKeyWire wire6Idx1Fast).map (fun p => p.message.take (p.message.length - 8)) =
      some wsInnerWire1 := by decide +kernel
theorem wire6Idx1Bytes_wire {p : PreKeyFields} (hp : parsePreKeyWire wire6Idx1Bytes = some p) : p.message.take (p.message.length - 8) = wsInnerWire1 := by
  have h := wire6Idx1Fast_wire; rw [← wire6Idx1Bytes_eq, hp] at h; exact Option.some.inj h
theorem gamma_macIn81 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : gamma compI0 S g (DY.Concat.concat (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)) (DY.Concat.concat (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)) (encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2)))) = wsMacIn1 := by unfold stA81; rw [CompFreshDistinct.gamma_concat_eq, CompFreshDistinct.gamma_concat_eq, gamma_serializedIk_0_of_fits hfits hinv.compat, gamma_serializedIk_2_of_fits hfits hinv.compat, (hinv.hwire₁ p hp).1, wire6Idx1Bytes_wire hp, wsMacIn1_def]
theorem saltedVals6_nodup : (saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSaltZ ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt1 ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt2 ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt5).Nodup := by
  have h := sigTab6_inj; simp only [sigTabFor, wsSalts81, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.map_append] at h; simp only [List.append_assoc] at h ⊢; exact List.Nodup.of_map sig h
set_option maxRecDepth 200000 in
theorem z81TagInj_of_vals {S : Sem} {g : Ghost} {Z : List DY.Bytes} (hZ : Z.map (gamma compI0 S g) = saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSaltZ ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt1 ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt2 ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt5) : (∀ z ∈ Z, (gamma compI0 S g z).take 4 = compTag4) ∧ (∀ a ∈ Z, ∀ b ∈ Z, gamma compI0 S g a = gamma compI0 S g b → a = b) := by
  refine ⟨fun z hz => ?_, fun a ha b hb h => List.inj_on_of_nodup_map (by rw [hZ]; exact saltedVals6_nodup) ha hb h⟩
  have hm : gamma compI0 S g z ∈ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSaltZ ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt1 ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt2 ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt5 := by rw [← hZ]; exact List.mem_map_of_mem hz
  have hT := saltedVals6_tagged; simp only [wsSalts81, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hT
  rcases List.mem_append.mp hm with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact (hT.1 _ h1).1
      · exact (hT.2.1 _ h2).1
    · exact (hT.2.2.1 _ h3).1
  · exact (hT.2.2.2 _ h4).1
def Split81ZPins : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → gamma compI0 S g (send2Salt81 r tr₁ tr₂ tr₃ cl₁ cl₂) = wsSalt2 ∧ gamma compI0 S g (ck5Salt81 r tr₄) = wsSalt5
theorem gamma_z81Terms {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hs2 : gamma compI0 S g (send2Salt81 r tr₁ tr₂ tr₃ cl₁ cl₂) = wsSalt2) (hs5 : gamma compI0 S g (ck5Salt81 r tr₄) = wsSalt5) : (z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂).map (gamma compI0 S g) = saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSaltZ ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt1 ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt2 ++ saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt5 := by
  have hseed := gamma_bobSeed81 hfits hp hinv; have hmsg := gamma_macIn81 hfits hp hinv; rw [z81Terms, List.map_append, List.map_append, List.map_append, gamma_saltedNodes81 r S g _ _ _ _ _ (gamma_zeroKey S g) hseed hmsg, gamma_saltedNodes81 r S g _ _ _ _ _ (gamma_ck1Salt40_ws81Idx1 hp hinv).1 hseed hmsg, gamma_saltedNodes81 r S g _ _ _ _ _ hs2 hseed hmsg, gamma_saltedNodes81 r S g _ _ _ _ _ hs5 hseed hmsg]
theorem split81ZTagInj_of_pins (hP : Split81ZPins) : Split81ZTagInj := by intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv; obtain ⟨hs2, hs5⟩ := hP r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv; exact z81TagInj_of_vals (gamma_z81Terms hfits hp hinv hs2 hs5)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPin
