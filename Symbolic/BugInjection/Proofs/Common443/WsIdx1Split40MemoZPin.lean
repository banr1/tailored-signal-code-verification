/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin
namespace SP
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins (gamma_computeMac gamma_hmac_compI0)
end SP
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
private theorem toUTF8_eq_ofList (s : String) : s.toUTF8 = List.utf8Encode s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
theorem gamma_wmk (S : Sem) (g : Ghost) : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") = wmkLit := by
  show gamma compI0 S g (({ lit := "WhisperMessageKeys".toUTF8 } : DY.Literal.Literal.SubF DY.Bytes).pack) = wmkLit
  rw [CompRSchedBSalts.gamma_lit, toUTF8_eq_ofList]; decide
theorem gamma_litByte (S : Sem) (g : Ghost) (b : UInt8) : gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte b) = ofByteArray ⟨#[b]⟩ := by
  show gamma compI0 S g (({ lit := ⟨#[b]⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack) = _
  rw [CompRSchedBSalts.gamma_lit]
theorem ofByteArray_one : ofByteArray ⟨#[1]⟩ = [1#8] := by decide
theorem ofByteArray_two : ofByteArray ⟨#[2]⟩ = [2#8] := by decide
theorem ofByteArray_three : ofByteArray ⟨#[3]⟩ = [3#8] := by decide
theorem wmkInfo1_eq : wmkInfo1 = wmkLit ++ [1#8] := rfl
theorem gamma_zeroKey (S : Sem) (g : Ghost) : gamma compI0 S g DY.Spqr.zeroKey = wsSaltZ := by
  show gamma compI0 S g (({ lit := ⟨Array.replicate 32 0⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack) = wsSaltZ
  rw [CompRSchedBSalts.gamma_lit]; decide
theorem gamma_saltedNodes40 (S : Sem) (g : Ghost) (salt : DY.Bytes) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) {seed macIn saltB : HwBytes} (hsalt : gamma compI0 S g salt = saltB) (hseed : gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2 = seed) (hmsg : gamma compI0 S g (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr stA cl (tr.length + 2)))) = macIn) : (saltedNodes40 salt tr stA cl).map (gamma compI0 S g) = saltedValsFor seed macIn saltB := by subst hsalt hseed hmsg; simp only [saltedNodes40, saltedValsFor, DY.Libsignal.TripleRatchet.trMsgKeys, DY.Libsignal.TripleRatchet.hkdfBlock1, DY.Libsignal.TripleRatchet.hkdfBlock2, DY.Libsignal.TripleRatchet.hkdfBlock3, List.map_cons, List.map_nil, SP.gamma_computeMac, SP.gamma_hmac_compI0, CompFreshDistinct.gamma_concat_eq, gamma_wmk, gamma_litByte, ofByteArray_one, ofByteArray_two, ofByteArray_three, wmkInfo1_eq]
theorem saltedVals2_zs1_nodup : (saltedValsFor wsSeed2 wsMacIn2 wsSaltZ ++ saltedValsFor wsSeed2 wsMacIn2 wsSalt1).Nodup := by
  have h := sigTab40_inj; simp only [sigTabFor, wsSalts40, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.map_append] at h; exact (List.Nodup.of_map sig h).sublist (List.Sublist.append_left (List.sublist_append_left _ _) _)
theorem zTagInj_of_vals {S : Sem} {g : Ghost} {Z : List DY.Bytes} (hZ : Z.map (gamma compI0 S g) = saltedValsFor wsSeed2 wsMacIn2 wsSaltZ ++ saltedValsFor wsSeed2 wsMacIn2 wsSalt1) : (∀ z ∈ Z, (gamma compI0 S g z).take 4 = compTag4) ∧ (∀ a ∈ Z, ∀ b ∈ Z, gamma compI0 S g a = gamma compI0 S g b → a = b) := by
  refine ⟨fun z hz => ?_, fun a ha b hb h => ?_⟩
  · have hm : gamma compI0 S g z ∈
        saltedValsFor wsSeed2 wsMacIn2 wsSaltZ ++ saltedValsFor wsSeed2 wsMacIn2 wsSalt1 :=
      hZ ▸ List.mem_map_of_mem hz
    have hT := saltedVals2_z_s1_tagged; simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hT
    exact (List.mem_append.mp hm).elim (fun h => (hT.1 _ h).1) (fun h => (hT.2 _ h).1)
  · exact List.inj_on_of_nodup_map (hZ.symm ▸ saltedVals2_zs1_nodup) ha hb h
def Split40ZPins : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (stA40 r tr₁ tr₂ cl₁).cks).2 = wsSeed2 ∧ gamma compI0 S g (DY.Concat.concat (stA40 r tr₁ tr₂ cl₁).myIk (DY.Concat.concat (stA40 r tr₁ tr₂ cl₁).peerIk (encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)))) = wsMacIn2 ∧ gamma compI0 S g (ck1Salt40 r tr₁) = wsSalt1
theorem split40ZTagInj_of_pins (hP : Split40ZPins) : Split40ZTagInj := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv; obtain ⟨hseed, hmsg, hck⟩ := hP r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv
  refine zTagInj_of_vals ?_
  rw [z40Terms, List.map_append, gamma_saltedNodes40 S g _ _ _ _ (gamma_zeroKey S g) hseed hmsg, gamma_saltedNodes40 S g _ _ _ _ hck hseed hmsg]
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin
