/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2RestFn
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin
public import Symbolic.BugInjection.Proofs.Common443.CompFitsNames
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.CompRWSBobChain
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38
public import Symbolic.BugInjection.Proofs.Common443.CompC3Nbsc38HB
import Init.Data.String
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA
open CryptoProofLib.Refinement (ExternInterpretation)
open ByteSpecs DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes torsionShift)
open DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire Symbolic.BugInjection.Proofs.Common443.CompRX0SS38 Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire Symbolic.BugInjection.Proofs.Common443.CompRX0Top Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZTag Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZVals Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ Symbolic.BugInjection.Proofs.Common443.CompC2RestCore Symbolic.BugInjection.Proofs.Common443.CompC2Rest38 Symbolic.BugInjection.Proofs.Common443.CompC2RestFn Symbolic.BugInjection.Proofs.Common443.CompRWSBobChain Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def ssDhsBytes : HwBytes := CompRPlantWire.eventBytes ((Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 34).headD (.rng []))
theorem rsT_drop32 : CompRX0SS38.rsT.drop 32 = [.rng ssDhsBytes] := rfl
private theorem toUTF8_eq_ofList (s : String) : s.toUTF8 = List.utf8Encode s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
theorem sentMacKey_key_iv : (hmacWith (sha256CompressFunction compI0) sentPrk (ofByteArray "WhisperMessageKeys".toUTF8 ++ [1#8]) == compAesK0 && (hmacWith (sha256CompressFunction compI0) sentPrk (sentMacKey ++ (ofByteArray "WhisperMessageKeys".toUTF8 ++ [3#8]))).take 16 == compAesIv0) = true := by
  rw [toUTF8_eq_ofList]; decide +kernel
theorem compAesPerm_k0_iv0_ptB : compAesPerm compAesK0 compAesIv0 CompRX0SS38.ptB = compAesCt0 := by decide +kernel
theorem gamma_literalToBytes_eq (S : Sem) (g : Ghost) (bs : ByteArray) : gamma compI0 S g (DY.Literal.literalToBytes bs) = ofByteArray bs := CompFreshDistinct.gamma_lit compI0 S g bs
theorem gamma_symEnc_compI0_eq (S : Sem) (g : Ghost) (k iv m : DY.Bytes) : gamma compI0 S g (DY.SymEnc.symEnc k iv m) = compAesPerm (gamma compI0 S g k) ((gamma compI0 S g iv).take 16) (gamma compI0 S g m) := by unfold gamma gamma'; rw [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gSym0 compI0) (gAll compI0 S g)]; rfl
theorem gamma_symEnc_encKeys_hb {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} (hk : gamma compI0 S g (encKeys tr₂ stA cl pq).macKey = sentMacKey) (hP : gamma compI0 S g (encPrk tr₂ stA cl pq) = sentPrk) (hpt : gamma compI0 S g (randTerm tr₂.length 32) = CompRX0SS38.ptB) : gamma compI0 S g (DY.SymEnc.symEnc (encKeys tr₂ stA cl pq).cipherKey (encKeys tr₂ stA cl pq).iv (randTerm tr₂.length 32)) = compAesCt0 := by have h1 := sentMacKey_key_iv; simp only [Bool.and_eq_true, beq_iff_eq] at h1; have hck : gamma compI0 S g (encKeys tr₂ stA cl pq).cipherKey = compAesK0 := (by rw [encKeys_cipherKey_eq, CompRWSBobChain.gamma_hkdfBlock10, hP, CompRWSBobChain.gamma_whisperMessageKeys0]; exact h1.1); have hiv : (gamma compI0 S g (encKeys tr₂ stA cl pq).iv).take 16 = compAesIv0 := (by rw [encKeys_iv_eq, gamma_hkdfBlock3_eq, hP, ← encKeys_macKey_eq, hk, CompRWSBobChain.gamma_whisperMessageKeys0]; exact h1.2); rw [gamma_symEnc_compI0_eq, hck, hiv, hpt, compAesPerm_k0_iv0_ptB]
def sentMac8 : HwBytes := match parsePreKeyWire CompRPlantWire.sentWireFast with | some p => msgMac8 p | none => []
theorem sentWireFast_msgMac8 : (parsePreKeyWire CompRPlantWire.sentWireFast).map msgMac8 = some sentMac8 := by decide +kernel
theorem sentWireBytes_msgMac8 {q₀ : PreKeyFields} (hq₀ : parsePreKeyWire CompRPlantWire.sentWireBytes = some q₀) : msgMac8 q₀ = sentMac8 := by have h := sentWireFast_msgMac8; unfold CompRPlantWire.sentWireFast at h; rw [← CompRPlantWire.sentWireBytes_eq, hq₀] at h; exact Option.some.inj h
theorem sentWireFast_msg_ge77 : (parsePreKeyWire CompRPlantWire.sentWireFast).map (fun p => decide (77 ≤ p.message.length)) = some true := by decide +kernel
theorem sentWireBytes_msg_ge77 {q₀ : PreKeyFields} (hq₀ : parsePreKeyWire CompRPlantWire.sentWireBytes = some q₀) : 77 ≤ q₀.message.length := by have h := sentWireFast_msg_ge77; unfold CompRPlantWire.sentWireFast at h; rw [← CompRPlantWire.sentWireBytes_eq, hq₀] at h; exact of_decide_eq_true (Option.some.inj h)
theorem sentWireFast_msg_le1400 : (parsePreKeyWire CompRPlantWire.sentWireFast).map (fun p => decide (p.message.length ≤ 1400)) = some true := by decide +kernel
theorem sentWireBytes_msg_le1400 {q₀ : PreKeyFields} (hq₀ : parsePreKeyWire CompRPlantWire.sentWireBytes = some q₀) : q₀.message.length ≤ 1400 := by have h := sentWireFast_msg_le1400; unfold CompRPlantWire.sentWireFast at h; rw [← CompRPlantWire.sentWireBytes_eq, hq₀] at h; exact of_decide_eq_true (Option.some.inj h)
def hbEkAPub : HwBytes := compLookupPub (clamp CompRX0SS38.b0Bytes)
def lookupShape (S : Sem) (g : Ghost) (ts : List DY.Bytes) (v : HwBytes) : DY.Bytes :=
  match ts.find? (fun t => gamma compI0 S g t == v) with | some t => (gamma' compI0 S g t).shape | none => DY.Literal.literalToBytes .empty
theorem lookupShape_eq {S : Sem} {g : Ghost} {ts : List DY.Bytes} (hnd : (ts.map (gamma compI0 S g)).Nodup) {u : DY.Bytes} (hu : u ∈ ts) : (gamma' compI0 S g u).shape = lookupShape S g ts (gamma compI0 S g u) := by
  unfold lookupShape
  rcases hfind : ts.find? (fun t => gamma compI0 S g t == gamma compI0 S g u) with _ | t₀
  · exact absurd (beq_self_eq_true _) (List.find?_eq_none.mp hfind u hu)
  · have hf := @List.find?_some _ (fun t => gamma compI0 S g t == gamma compI0 S g u) t₀ ts hfind
    rw [List.inj_on_of_nodup_map hnd (List.mem_of_find?_eq_some hfind) hu (beq_iff_eq.mp hf)]
def rVals38HBOf (c : HwBytes) : List HwBytes := [ Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId, Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId, Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk, fillFresh 16 64, CompRX0SS38.b0Bytes, compKyberE0, ssDhsBytes, CompRX0SS38.ptB, c, compAesCt0, compKyberCt0, compKyberSs0 ]
def allVals38HBOf (c : HwBytes) : List HwBytes := rVals38HBOf c ++ [ compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId), compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId), compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk), compLookupPub (clamp CompRX0SS38.b0Bytes), compLookupPub (clamp ssDhsBytes), compLookupDh (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk)), compLookupDh (clamp CompRX0SS38.b0Bytes) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId)), compLookupDh (clamp CompRX0SS38.b0Bytes) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk)), compLookupDh (clamp ssDhsBytes) (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk)), sentMac8, CompC3Nbsc38HB.zfull0SS.take 8 ]
def rVals38HB : List HwBytes := rVals38HBOf CompRX0SS38.cB ++ (List.inits CompRX0SS38.cB).tail
def allVals38HB : List HwBytes := allVals38HBOf CompRX0SS38.cB
theorem allVals38HBOf_nodup_all : ((List.inits CompRX0SS38.cB).all fun c => decide (allVals38HBOf c).Nodup) = true := by decide +kernel
theorem allVals38HBOf_nodup {c : HwBytes} (hc : c ∈ List.inits CompRX0SS38.cB) : (allVals38HBOf c).Nodup := of_decide_eq_true (List.all_eq_true.mp allVals38HBOf_nodup_all c hc)
theorem cB_mem_inits_tail : CompRX0SS38.cB ∈ (List.inits CompRX0SS38.cB).tail := by decide +kernel
theorem cB_mem_inits : CompRX0SS38.cB ∈ List.inits CompRX0SS38.cB := List.mem_of_mem_tail cB_mem_inits_tail
theorem allVals38HB_nodup : allVals38HB.Nodup := allVals38HBOf_nodup cB_mem_inits
abbrev Rv38HB (v : HwBytes) : Prop := v ∈ rVals38HB
theorem rVals38HBOf_sub_rVals38HB {c : HwBytes} (hc : c ∈ (List.inits CompRX0SS38.cB).tail) {v : HwBytes} (hv : v ∈ rVals38HBOf c) : v ∈ rVals38HB := by
  simp only [rVals38HB, List.mem_append]
  simp only [rVals38HBOf, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inr hc
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
  · exact Or.inl (by simp [rVals38HBOf])
theorem rVals38HB_props :
    (rVals38HB.all fun v =>
      (v.length == 9) || (v.length == 16) || (v.length == 32) || (v.length == 64) || (v.length == 1568) ||
      (decide (1 ≤ v.length) && decide (v.length ≤ 68) && (v.take 1 == [35#8]) &&
        (decide (v.length < 32) || decide (KdfFree (v.take 32))))) = true ∧
    (rVals38HB.all fun v => !(decide (65 ≤ v.length)) || (v.length == 1568) || (v.take 1 == [35#8])) = true ∧
    (rVals38HB.all fun v => decide (v.length < 38) || decide (KdfFree ((v.drop (v.length - 38)).take 32))) = true ∧
    (rVals38HB.all fun v => (decide (v.length < 33)) || (x25519Vals.all fun w => !(v.take 4 == w.take 4))) = true := by decide +kernel
theorem not_rv38HB_of_len_head_ne80 {v : HwBytes} (h9 : v.length ≠ 9) (h16 : v.length ≠ 16) (h32 : v.length ≠ 32) (h64 : v.length ≠ 64) (h1568 : v.length ≠ 1568) (h80 : v.take 1 ≠ [35#8]) : ¬ Rv38HB v := by
  intro hv; have hall := List.all_eq_true.mp rVals38HB_props.1 v hv
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hall
  rcases hall with ((((h | h) | h) | h) | h) | ⟨⟨⟨_, _⟩, h⟩, _⟩
  · exact h9 h
  · exact h16 h
  · exact h32 h
  · exact h64 h
  · exact h1568 h
  · exact h80 h
theorem not_rv38HB_of_len_gt68 {v : HwBytes} (h : 69 ≤ v.length) (h1568 : v.length ≠ 1568) : ¬ Rv38HB v := by
  intro hv; have hall := List.all_eq_true.mp rVals38HB_props.1 v hv
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hall
  rcases hall with ((((hL | hL) | hL) | hL) | hL) | ⟨⟨⟨_, hle⟩, _⟩, _⟩ <;> omega
theorem not_rv38HB_of_kdf_prefix {k suf : HwBytes} (hk : ¬ KdfFree k) (hkL : k.length = 32) (h9 : k.length + suf.length ≠ 9) (h16 : k.length + suf.length ≠ 16) (h32 : k.length + suf.length ≠ 32) (h64 : k.length + suf.length ≠ 64) (h1568 : k.length + suf.length ≠ 1568) : ¬ Rv38HB (k ++ suf) := by
  intro hv; have hall := List.all_eq_true.mp rVals38HB_props.1 (k ++ suf) hv
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.length_append] at hall
  rcases hall with ((((h | h) | h) | h) | h) | ⟨⟨⟨_, _⟩, _⟩, hlt | hkf⟩
  · exact h9 h
  · exact h16 h
  · exact h32 h
  · exact h64 h
  · exact h1568 h
  · omega
  · rw [← hkL, List.take_left] at hkf; exact hk hkf
theorem rVals38HB_ge65_head80 : (rVals38HB.all fun v => !(decide (65 ≤ v.length)) || (v.length == 1568) || (v.take 1 == [35#8])) = true := rVals38HB_props.2.1
theorem not_rv38HB_of_len_ge65_head_ne80 {v : HwBytes} (h : 65 ≤ v.length) (h1568 : v.length ≠ 1568) (h0 : v.take 1 ≠ [35#8]) : ¬ Rv38HB v := by
  intro hv; have hall := List.all_eq_true.mp rVals38HB_ge65_head80 v hv; simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hall
  rcases hall with (hlt | hL) | heq <;> [exact hlt h; exact h1568 hL; exact h0 heq]
theorem rVals38HB_tail38_kdfFree : (rVals38HB.all fun v => decide (v.length < 38) || decide (KdfFree ((v.drop (v.length - 38)).take 32))) = true := rVals38HB_props.2.2.1
theorem not_rv38HB_of_kdf_tail6 {pref k suf : HwBytes} (hk : ¬ KdfFree k) (hkL : k.length = 32) (hsufL : suf.length = 6) : ¬ Rv38HB (pref ++ (k ++ suf)) := by
  intro hv; have hall := List.all_eq_true.mp rVals38HB_tail38_kdfFree _ hv; simp only [Bool.or_eq_true, decide_eq_true_eq] at hall
  have hL : (pref ++ (k ++ suf)).length = pref.length + 38 := by rw [List.length_append, List.length_append, hkL, hsufL]
  rcases hall with hlt | hkf
  · omega
  · rw [hL, Nat.add_sub_cancel, List.drop_left, ← hkL, List.take_left] at hkf; exact hk hkf
def KdfTail6 (v : HwBytes) : Prop := ∃ pre ck tail : HwBytes, v = pre ++ (ck ++ tail) ∧ ¬ KdfFree ck ∧ ck.length = 32 ∧ tail.length = 6
theorem KdfTail6.not_rv {v : HwBytes} (h : KdfTail6 v) : ¬ Rv38HB v := by rcases h with ⟨_, _, _, rfl, hk, hkL, htL⟩; exact not_rv38HB_of_kdf_tail6 hk hkL htL
theorem KdfTail6.append_left {v : HwBytes} (u : HwBytes) (h : KdfTail6 v) : KdfTail6 (u ++ v) := by rcases h with ⟨pre, ck, tail, rfl, hk, hkL, htL⟩; exact ⟨u ++ pre, ck, tail, (List.append_assoc _ _ _).symm, hk, hkL, htL⟩
theorem rVals38HB_ge33_not_x25519_prefix : (rVals38HB.all fun v => (decide (v.length < 33)) || (x25519Vals.all fun w => !(v.take 4 == w.take 4))) = true := rVals38HB_props.2.2.2
theorem not_rv38HB_of_x25519_append {a b : HwBytes} (ha : a ∈ x25519Vals) (hb : b.length = 32) : ¬ Rv38HB (a ++ b) := by
  have haL : a.length = 32 := x25519Vals_length a ha; intro hm; have hall := List.all_eq_true.mp rVals38HB_ge33_not_x25519_prefix (a ++ b) hm; simp only [Bool.or_eq_true, decide_eq_true_eq] at hall
  rcases hall with hlt | hx
  · rw [List.length_append, haL] at hlt; omega
  · have hwx := List.all_eq_true.mp hx a ha; rw [Bool.not_eq_true', beq_eq_false_iff_ne] at hwx; exact hwx (List.take_append_of_le_length (by omega))
theorem gamma_agree_mem_x25519Vals {S : Sem} {g : Ghost} (pk sk : DY.Bytes) : gamma compI0 S g (DY.Libsignal.PQXDH.agree pk sk) ∈ x25519Vals := by
  simp only [DY.Libsignal.PQXDH.agree, DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split <;> [split <;> exact gamma_mem_x25519Vals_of_isX (Or.inr ⟨_, _, rfl⟩); exact gamma_mem_x25519Vals_of_isX (Or.inr ⟨_, _, rfl⟩)]
theorem not_rv38HB_zeroDh : ¬ Rv38HB CompRI0Census.zeroDh := by decide +kernel
theorem not_rv38HB_ff32 : ¬ Rv38HB (List.replicate 32 0xff#8) := by decide +kernel
theorem not_rv38HB_variant_b0 (v : Fin 4) (t : Fin 8) : ¬ Rv38HB (variantBytes (torsionShift compI0 hbEkAPub t) v) := by revert v t; decide +kernel
attribute [local irreducible] rVals38HB allVals38HB
def FnOK (allT rT : List DY.Bytes) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := (assumedInjective x.1 = false → ¬ Rv38HB x.2.2) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → x.1 ∈ allT) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → ¬ IsX x.1 → ¬ IsTrunc8 x.1 → x.1 ∈ rT)
abbrev FnCensus (allT rT : List DY.Bytes) (S : Sem) (g : Ghost) (t : DY.Bytes) : Prop := MemoOK compI0 S g (FnOK allT rT) t
section NRPrim
variable {allT rT : List DY.Bytes} {S : Sem} {g : Ghost}
theorem fnok_of_ni {b : DY.Bytes} (hb : assumedInjective b = false) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) (hnr : ¬ Rv38HB x.2.2) : FnOK allT rT x :=
  ⟨fun _ => hnr, fun hai _ => (by rw [hx, hb] at hai; cases hai), fun hai _ _ _ => (by rw [hx, hb] at hai; cases hai)⟩
theorem fnok_of_isKdf {b : DY.Bytes} (hb : IsKdf b) (hai : assumedInjective b = true) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) : FnOK allT rT x :=
  ⟨fun h => (by rw [hx, hai] at h; cases h), fun _ hK => absurd (hx ▸ hb) hK, fun _ hK _ _ => absurd (hx ▸ hb) hK⟩
theorem fnok_of_isX {b : DY.Bytes} (hb : IsX b) (hai : assumedInjective b = true) (hm : b ∈ allT) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) : FnOK allT rT x :=
  ⟨fun h => (by rw [hx, hai] at h; cases h), fun _ _ => hx ▸ hm, fun _ _ hX _ => absurd (hx ▸ hb) hX⟩
theorem fnok_of_isTrunc8 {b : DY.Bytes} (hb : IsTrunc8 b) (hai : assumedInjective b = true) (hm : b ∈ allT) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) : FnOK allT rT x :=
  ⟨fun h => (by rw [hx, hai] at h; cases h), fun _ _ => hx ▸ hm, fun _ _ _ hT => absurd (hx ▸ hb) hT⟩
theorem fnok_of_r {b : DY.Bytes} (hai : assumedInjective b = true) (hmA : b ∈ allT) (hmR : b ∈ rT) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) : FnOK allT rT x :=
  ⟨fun h => (by rw [hx, hai] at h; cases h), fun _ _ => hx ▸ hmA, fun _ _ _ _ => hx ▸ hmR⟩
theorem nrcensus_lit (bs : ByteArray) (h : ¬ Rv38HB (gamma compI0 S g (DY.Literal.literalToBytes bs))) : FnCensus allT rT S g (DY.Literal.literalToBytes bs) := by
  intro x hx; have hv := (CompRPreMemoSound.memo_sound compI0 S g _ hx).2; unfold gamma' at hx; rw [show DY.Literal.literalToBytes bs = ({ lit := bs } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gLit0 (gAll compI0 S g)] at hx
  rcases List.mem_singleton.mp hx with rfl
  exact fnok_of_ni (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_lit_pack_eq bs) rfl (by rw [hv]; exact h)
theorem nrcensus_lit_ofBA {bs : ByteArray} (h : ¬ Rv38HB (ofByteArray bs)) : FnCensus allT rT S g (DY.Literal.literalToBytes bs) :=
  nrcensus_lit bs (by rw [show DY.Literal.literalToBytes bs = ({ lit := bs } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl, CompFreshDistinct.gamma_lit]; exact h)
theorem nrcensus_lit_size (bs : ByteArray) (h9 : bs.size ≠ 9) (h16 : bs.size ≠ 16) (h32 : bs.size ≠ 32) (h64 : bs.size ≠ 64) (h1568 : bs.size ≠ 1568) (h80 : (ofByteArray bs).take 1 ≠ [35#8]) : FnCensus allT rT S g (DY.Literal.literalToBytes bs) :=
  nrcensus_lit bs (not_rv38HB_of_len_head_ne80 (by rw [CompPlant.gamma_literalToBytes_length]; exact h9) (by rw [CompPlant.gamma_literalToBytes_length]; exact h16)
    (by rw [CompPlant.gamma_literalToBytes_length]; exact h32) (by rw [CompPlant.gamma_literalToBytes_length]; exact h64) (by rw [CompPlant.gamma_literalToBytes_length]; exact h1568) (by rw [gamma_literalToBytes_eq]; exact h80))
theorem nrcensus_litByte (b : UInt8) (hb : b.toBitVec ≠ 35#8) : FnCensus allT rT S g (DY.Libsignal.TripleRatchet.litByte b) :=
  nrcensus_lit_size _ (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ofByteArray, hb])
theorem nrcensus_concat {a c : DY.Bytes} (h : ¬ Rv38HB (gamma compI0 S g a ++ gamma compI0 S g c)) (ha : FnCensus allT rT S g a) (hc : FnCensus allT rT S g c) : FnCensus allT rT S g (DY.Concat.concat a c) := by
  intro x hx; unfold gamma' at hx; rw [show DY.Concat.concat a c = ({ lhs := a, rhs := c } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gConcat0 (gAll compI0 S g)] at hx; simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, CompPlant.bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxc <;> [exact fnok_of_ni (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq a c) rfl h; exact ha x hxa; exact hc x hxc]
theorem nrcensus_concat_len_ne80 {a c : DY.Bytes} (h9 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 9) (h16 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 16) (h32 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 32) (h64 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 64) (h1568 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 1568) (ha1 : 1 ≤ (gamma compI0 S g a).length) (ha80 : (gamma compI0 S g a).take 1 ≠ [35#8]) (ha : FnCensus allT rT S g a) (hc : FnCensus allT rT S g c) : FnCensus allT rT S g (DY.Concat.concat a c) :=
  nrcensus_concat (not_rv38HB_of_len_head_ne80 (by simpa using h9) (by simpa using h16) (by simpa using h32) (by simpa using h64) (by simpa using h1568) (by rw [List.take_append_of_le_length ha1]; exact ha80)) ha hc
theorem nrcensus_concat_len_gt68 {a c : DY.Bytes} (h69 : 69 ≤ (gamma compI0 S g a).length + (gamma compI0 S g c).length) (h1568 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 1568) (ha : FnCensus allT rT S g a) (hc : FnCensus allT rT S g c) : FnCensus allT rT S g (DY.Concat.concat a c) :=
  nrcensus_concat (not_rv38HB_of_len_gt68 (by simpa using h69) (by simpa using h1568)) ha hc
theorem nrcensus_concat_kdf {a c : DY.Bytes} (hk : ¬ KdfFree (gamma compI0 S g a)) (haL : (gamma compI0 S g a).length = 32) (h9 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 9) (h16 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 16) (h32 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 32) (h64 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 64) (h1568 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 1568) (ha : FnCensus allT rT S g a) (hc : FnCensus allT rT S g c) : FnCensus allT rT S g (DY.Concat.concat a c) :=
  nrcensus_concat (not_rv38HB_of_kdf_prefix hk haL h9 h16 h32 h64 h1568) ha hc
theorem nrcensus_randTerm {ts sz : Nat} (hmA : randTerm ts sz ∈ allT) (hmR : randTerm ts sz ∈ rT) : FnCensus allT rT S g (randTerm ts sz) := by
  intro x hx; unfold gamma' randTerm at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll compI0 S g)] at hx
  dsimp only [gRandom, concretizeRandom] at hx; split_ifs at hx with hsz
  · cases hx
  · rcases List.mem_singleton.mp hx with rfl
    exact fnok_of_r ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (.inl ⟨_, DY.BytesView.view_pack _, hsz⟩)) hmA hmR rfl
theorem nrcensus_randTerm_zero (ts : Nat) : FnCensus allT rT S g (randTerm ts 0) := by
  intro x hx; unfold gamma' randTerm at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll compI0 S g)] at hx
  dsimp only [gRandom, concretizeRandom] at hx; split_ifs at hx with hsz
  · cases hx
  · exact absurd rfl hsz
theorem nrcensus_dhPk {sk : DY.Bytes} (hmA : DY.DiffieHellman.dhPk sk ∈ allT) (hsk : FnCensus allT rT S g sk) : FnCensus allT rT S g (DY.DiffieHellman.dhPk sk) :=
  memoOK_dhPk (fun _ hx => fnok_of_isX (.inl ⟨sk, rfl⟩) ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack])) hmA hx) hsk
theorem nrcensus_dh_pack {pk sk : DY.Bytes} (hmA : (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) ∈ allT) (hpk : FnCensus allT rT S g pk) (hsk : FnCensus allT rT S g sk) : FnCensus allT rT S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) :=
  memoOK_dh_pack (fun _ hx => fnok_of_isX (.inr ⟨pk, sk, rfl⟩) ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [DY.BytesView.view_pack])) hmA hx) hpk hsk
theorem nrcensus_kdfExtract {k m : DY.Bytes} (hk : FnCensus allT rT S g k) (hm : FnCensus allT rT S g m) : FnCensus allT rT S g (DY.KdfExtract.kdfExtract k m) :=
  memoOK_kdfExtract (fun _ hx => fnok_of_isKdf ⟨k, m, rfl⟩ (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_kdfExtract_eq k m) hx) hk hm
theorem nrcensus_symEnc {k iv m : DY.Bytes} (hmA : DY.SymEnc.symEnc k iv m ∈ allT) (hmR : DY.SymEnc.symEnc k iv m ∈ rT) (hk : FnCensus allT rT S g k) (hiv : FnCensus allT rT S g iv) (hm : FnCensus allT rT S g m) : FnCensus allT rT S g (DY.SymEnc.symEnc k iv m) :=
  memoOK_symEnc (fun _ hx => fnok_of_r ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack])) hmA hmR hx) hk hiv hm
theorem nrcensus_trunc8 {a : DY.Bytes} (hmA : DY.Trunc.trunc8 a ∈ allT) (ha : FnCensus allT rT S g a) : FnCensus allT rT S g (DY.Trunc.trunc8 a) :=
  memoOK_trunc8 (fun _ hx => fnok_of_isTrunc8 ⟨a, rfl⟩ ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack])) hmA hx) ha
theorem nrcensus_variant_ek {k : DY.Bytes} (v : Fin 4) (t : Fin 8) (hk_val : gamma compI0 S g (DY.X25519.x25519Key k) = hbEkAPub) (hk : FnCensus allT rT S g (DY.X25519.x25519Key k)) : FnCensus allT rT S g (DY.X25519.x25519TorsionVariant k v t) := by
  unfold DY.X25519.x25519TorsionVariant
  split
  · exact hk
  · intro x hx; have hv := (CompRPreMemoSound.memo_sound compI0 S g _ hx).2; unfold gamma' at hx; rw [DY.Bytes.rec_eq (gVariant0 compI0) (gAll compI0 S g)] at hx; simp only [gVariant0, concretizeVariant, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, CompPlant.bytes_rec_gAll] at hx
    rcases hx with rfl | hxk
    · have hni : assumedInjective (({ key := DY.X25519.x25519Key k, variation := v, torsion := t } : DY.X25519.Variant.SubF DY.Bytes).pack) = false := by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.variant_view?_none (DY.X25519.x25519Key k) v t
        rw [Bool.eq_false_iff, ne_eq, Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff]
        intro h; simp [h1, h2, h3, h4, h5, h6, h7, h8] at h
      refine fnok_of_ni hni rfl ?_; rw [hv, CompFreshDistinct.gamma_variant_pack, hk_val]; exact not_rv38HB_variant_b0 v t
    · exact hk x hxk
theorem nrcensus_agree_dhPk {q sk : DY.Bytes} (hag : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk q) sk ∈ allT) (hpk_sk : DY.DiffieHellman.dhPk sk ∈ allT) (hpk : FnCensus allT rT S g (DY.DiffieHellman.dhPk q)) (hsk : FnCensus allT rT S g sk) : FnCensus allT rT S g (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk q) sk) := by
  have hv : (DY.DiffieHellman.dhPk q).view? DY.DiffieHellman.DhPk.SubF = some { sk := q } := (by dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]; rw [DY.BytesView.view_pack]); simp only [DY.Libsignal.PQXDH.agree, CompPlant.x25519Key_dhPk, DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, hv] at hag ⊢
  split_ifs at hag ⊢
  · exact nrcensus_dh_pack hag hpk hsk
  · exact nrcensus_dh_pack hag (nrcensus_dhPk hpk_sk hsk) (memoOK_dhPk_elim hpk)
theorem nrcensus_hmac {a b : DY.Bytes} (ha : FnCensus allT rT S g a) (hb : FnCensus allT rT S g b) : FnCensus allT rT S g (DY.Libsignal.TripleRatchet.hmac a b) := nrcensus_kdfExtract ha hb
theorem gamma_litByte_length (b : UInt8) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte b)).length = 1 := CompPlant.gamma_literalToBytes_length compI0 S g _
theorem gamma_trLit_length (s : String) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.lit s)).length = s.toUTF8.size := CompPlant.gamma_literalToBytes_length compI0 S g _
theorem nrcensus_hkdf3 {prk info : DY.Bytes} (h8 : (gamma compI0 S g info).length ≠ 8) (h15 : (gamma compI0 S g info).length ≠ 15) (h31 : (gamma compI0 S g info).length ≠ 31) (h63 : (gamma compI0 S g info).length ≠ 63) (hinfo1 : 1 ≤ (gamma compI0 S g info).length) (hinfoU : (gamma compI0 S g info).length < 1500) (hinfo80 : (gamma compI0 S g info).take 1 ≠ [35#8]) (hprk : FnCensus allT rT S g prk) (hinfo : FnCensus allT rT S g info) : FnCensus allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) ∧ FnCensus allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) ∧ FnCensus allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := by
  have hb1 : FnCensus allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := by
    unfold DY.Libsignal.TripleRatchet.hkdfBlock1
    refine nrcensus_hmac hprk (nrcensus_concat_len_ne80 ?_ ?_ ?_ ?_ ?_ hinfo1 hinfo80 hinfo (nrcensus_litByte _ (by decide))) <;> rw [gamma_litByte_length] <;> omega
  have hb2 : FnCensus allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := by
    unfold DY.Libsignal.TripleRatchet.hkdfBlock2
    refine nrcensus_hmac hprk (nrcensus_concat_kdf (not_kdfFree_kdfExtract _ _) (CompFreshDistinct.gamma_hmac_length S g _ _) ?_ ?_ ?_ ?_ ?_ hb1 (nrcensus_concat_len_ne80 ?_ ?_ ?_ ?_ ?_ hinfo1 hinfo80 hinfo (nrcensus_litByte _ (by decide)))) <;>
      simp only [gamma_concat, List.length_append, gamma_litByte_length, DY.Libsignal.TripleRatchet.hkdfBlock1, CompFreshDistinct.gamma_hmac_length] <;> omega
  have hb3 : FnCensus allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := by
    unfold DY.Libsignal.TripleRatchet.hkdfBlock3
    refine nrcensus_hmac hprk (nrcensus_concat_kdf (not_kdfFree_kdfExtract _ _) (CompFreshDistinct.gamma_hmac_length S g _ _) ?_ ?_ ?_ ?_ ?_ hb2 (nrcensus_concat_len_ne80 ?_ ?_ ?_ ?_ ?_ hinfo1 hinfo80 hinfo (nrcensus_litByte _ (by decide)))) <;>
      simp only [gamma_concat, List.length_append, gamma_litByte_length, DY.Libsignal.TripleRatchet.hkdfBlock2, CompFreshDistinct.gamma_hmac_length] <;> omega
  exact ⟨hb1, hb2, hb3⟩
theorem nrcensus_zeroSalt : FnCensus allT rT S g DY.Libsignal.TripleRatchet.zeroSalt := nrcensus_lit_ofBA not_rv38HB_zeroDh
theorem nrcensus_zeroKey : FnCensus allT rT S g DY.Spqr.zeroKey := nrcensus_lit_ofBA not_rv38HB_zeroDh
theorem nrcensus_discontinuity : FnCensus allT rT S g DY.Libsignal.PQXDH.discontinuity := nrcensus_lit_ofBA not_rv38HB_ff32
theorem nrcensus_trWire_of_len {ver : UInt8} {rk ct pq : DY.Bytes} {c pc : UInt32} {ev : DY.TrWire.EncodingVariation} (h69 : 69 ≤ (gamma compI0 S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev)).length) (h1568 : (gamma compI0 S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev)).length ≠ 1568) (hrk : FnCensus allT rT S g rk) (hct : FnCensus allT rT S g ct) (hpq : FnCensus allT rT S g pq) : FnCensus allT rT S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev) := by
  rw [show DY.TrWire.trWireMsg ver rk c pc ct pq ev = ({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack from rfl] at h69 h1568 ⊢; intro x hx
  refine memoOK_trWire (P := fun y => y.2.2 = gamma compI0 S g y.1 → FnOK allT rT y)
    (fun y hy hs => fnok_of_ni (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_trWire_pack_eq _) hy (by rw [hs, hy]; exact not_rv38HB_of_len_gt68 h69 h1568))
    (fun y hy _ => hrk y hy) (fun y hy _ => hct y hy) (fun y hy _ => hpq y hy) x hx (CompRPreMemoSound.memo_sound compI0 S g _ hx).2
theorem nrcensus_createChain_dhPk {rk q sk : DY.Bytes} (hag : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk q) sk ∈ allT) (hpk_sk : DY.DiffieHellman.dhPk sk ∈ allT) (hrk : FnCensus allT rT S g rk) (hpk : FnCensus allT rT S g (DY.DiffieHellman.dhPk q)) (hsk : FnCensus allT rT S g sk) : FnCensus allT rT S g (DY.Libsignal.TripleRatchet.createChain rk (DY.DiffieHellman.dhPk q) sk).1 ∧ FnCensus allT rT S g (DY.Libsignal.TripleRatchet.createChain rk (DY.DiffieHellman.dhPk q) sk).2 := by
  have h := nrcensus_hkdf3 (info := DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
    (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (nrcensus_hmac hrk (nrcensus_agree_dhPk hag hpk_sk hpk hsk)) (nrcensus_lit_size _ (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide))
  exact ⟨h.1, h.2.1⟩
theorem nrcensus_kdfCk {ck : DY.Bytes} (hck : FnCensus allT rT S g ck) : FnCensus allT rT S g (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∧ FnCensus allT rT S g (DY.Libsignal.TripleRatchet.kdfCk ck).2 := ⟨nrcensus_hmac hck (nrcensus_litByte _ (by decide)), nrcensus_hmac hck (nrcensus_litByte _ (by decide))⟩
theorem nrcensus_trMsgKeys {salt seed : DY.Bytes} (hsalt : FnCensus allT rT S g salt) (hseed : FnCensus allT rT S g seed) : let mk := DY.Libsignal.TripleRatchet.trMsgKeys salt seed; FnCensus allT rT S g mk.cipherKey ∧ FnCensus allT rT S g mk.macKey ∧ FnCensus allT rT S g mk.iv := nrcensus_hkdf3 (info := DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
    (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (nrcensus_hmac hsalt hseed) (nrcensus_lit_size _ (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide))
theorem nrcensus_serializedIk {ik : DY.Bytes} (hikL : (gamma compI0 S g ik).length = 32) (hik : FnCensus allT rT S g ik) : FnCensus allT rT S g (DY.Libsignal.PQXDH.serializedIk ik) := by
  unfold DY.Libsignal.PQXDH.serializedIk DY.Libsignal.PQXDH.encodeEC
  refine nrcensus_concat_len_ne80 ?_ ?_ ?_ ?_ ?_ ?_ ?_ (nrcensus_litByte _ (by decide)) hik <;> first | (rw [gamma_litByte_length, hikL]; decide) | rw [gamma_litByte_length] | (unfold DY.Libsignal.TripleRatchet.litByte; rw [gamma_literalToBytes_eq]; decide)
theorem gamma_serializedIk_length {ik : DY.Bytes} (hikL : (gamma compI0 S g ik).length = 32) : (gamma compI0 S g (DY.Libsignal.PQXDH.serializedIk ik)).length = 33 := by unfold DY.Libsignal.PQXDH.serializedIk DY.Libsignal.PQXDH.encodeEC; rw [gamma_concat, List.length_append, gamma_litByte_length, hikL]
theorem nrcensus_pqxdhKdf_none {dh1 dh2 dh3 ss : DY.Bytes} (hdh1L : (gamma compI0 S g dh1).length = 32) (hdh2L : (gamma compI0 S g dh2).length = 32) (hdh3L : (gamma compI0 S g dh3).length = 32) (hssL : (gamma compI0 S g ss).length = 32) (hdh3X : gamma compI0 S g dh3 ∈ x25519Vals) (hdh1 : FnCensus allT rT S g dh1) (hdh2 : FnCensus allT rT S g dh2) (hdh3 : FnCensus allT rT S g dh3) (hss : FnCensus allT rT S g ss) : let keys := DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss);
    FnCensus allT rT S g keys.rk ∧ FnCensus allT rT S g keys.ck ∧ FnCensus allT rT S g keys.pqr := by
  have hc3 := nrcensus_concat (not_rv38HB_of_x25519_append hdh3X hssL) hdh3 hss
  have hc2 : FnCensus allT rT S g (DY.Concat.concat dh2 (DY.Concat.concat dh3 ss)) := by refine nrcensus_concat_len_gt68 ?_ ?_ hdh2 hc3 <;> · rw [gamma_concat, List.length_append, hdh2L, hdh3L, hssL]; decide
  have hc1 : FnCensus allT rT S g (DY.Concat.concat dh1 (DY.Concat.concat dh2 (DY.Concat.concat dh3 ss))) := by refine nrcensus_concat_len_gt68 ?_ ?_ hdh1 hc2 <;> · rw [gamma_concat, gamma_concat, List.length_append, List.length_append, hdh1L, hdh2L, hdh3L, hssL]; decide
  have hikm : FnCensus allT rT S g (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss) := by
    refine nrcensus_concat_len_gt68 ?_ ?_ nrcensus_discontinuity hc1 <;>
      · rw [DY.Libsignal.PQXDH.discontinuity, CompPlant.gamma_literalToBytes_length, gamma_concat, gamma_concat, gamma_concat, List.length_append, List.length_append, List.length_append, hdh1L, hdh2L, hdh3L, hssL]; decide
  exact nrcensus_hkdf3 (info := DY.Libsignal.PQXDH.pqxdhLabel)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.PQXDH.pqxdhLabel DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (nrcensus_hmac nrcensus_zeroSalt hikm) (nrcensus_lit_size _ (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide) (by rw [toUTF8_eq_ofList]; decide))
end NRPrim
section NRSer
variable {allT rT : List DY.Bytes} {S : Sem} {g : Ghost}
theorem concatPrefixes_singleton (x s : DY.Bytes) : Comparse.concatPrefixes [x] s = DY.Concat.concat x s := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
theorem gamma_concatPrefixes_length (ps : List DY.Bytes) (s : DY.Bytes) : (gamma compI0 S g (Comparse.concatPrefixes ps s)).length = (ps.flatMap (gamma compI0 S g)).length + (gamma compI0 S g s).length := by rw [CompExcuse.gamma_concatPrefixes, List.length_append]
theorem nrcensus_concatPrefixes_kdfTail6 : ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensus allT rT S g p) → FnCensus allT rT S g s → KdfTail6 (gamma compI0 S g s) → FnCensus allT rT S g (Comparse.concatPrefixes ps s) ∧ KdfTail6 (gamma compI0 S g (Comparse.concatPrefixes ps s))
  | [], _, _, hs, hT => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact ⟨hs, hT⟩
  | p :: ps, s, hps, hs, hT => by
    obtain ⟨ih, ihT⟩ := nrcensus_concatPrefixes_kdfTail6 ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs hT; have hT' := ihT.append_left (gamma compI0 S g p)
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat]; exact ⟨nrcensus_concat hT'.not_rv (hps p (List.mem_cons_self ..)) ih, hT'⟩
theorem nrcensus_concatPrefixes_ge65_head : ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensus allT rT S g p ∧ 1 ≤ (gamma compI0 S g p).length ∧ (gamma compI0 S g p).take 1 ≠ [35#8]) → FnCensus allT rT S g s → 65 ≤ (gamma compI0 S g s).length → (gamma compI0 S g (Comparse.concatPrefixes ps s)).length < 1568 → FnCensus allT rT S g (Comparse.concatPrefixes ps s) ∧ 65 ≤ (gamma compI0 S g (Comparse.concatPrefixes ps s)).length
  | [], _, _, hs, hL, _ => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact ⟨hs, hL⟩
  | p :: ps, s, hps, hs, hL, hU => by
    have hlen : (gamma compI0 S g (Comparse.concatPrefixes (p :: ps) s)).length = (gamma compI0 S g p).length + (gamma compI0 S g (Comparse.concatPrefixes ps s)).length := (by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat, List.length_append]); obtain ⟨ih, ihL⟩ := nrcensus_concatPrefixes_ge65_head ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs hL (by omega); obtain ⟨hpC, hp1, hp0⟩ := hps p (List.mem_cons_self ..); refine ⟨?_, by omega⟩; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    refine nrcensus_concat (not_rv38HB_of_len_ge65_head_ne80 ?_ ?_ ?_) hpC ih <;> [ (rw [List.length_append]; omega); (rw [List.length_append]; omega); (rw [List.take_append_of_le_length hp1]; exact hp0) ]
theorem nrcensus_concatPrefixes_33_lt64 : ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensus allT rT S g p ∧ 1 ≤ (gamma compI0 S g p).length ∧ (gamma compI0 S g p).take 1 ≠ [35#8]) → FnCensus allT rT S g s → 33 ≤ (gamma compI0 S g s).length → (gamma compI0 S g (Comparse.concatPrefixes ps s)).length < 64 → FnCensus allT rT S g (Comparse.concatPrefixes ps s) ∧ 33 ≤ (gamma compI0 S g (Comparse.concatPrefixes ps s)).length
  | [], _, _, hs, h33, _ => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact ⟨hs, h33⟩
  | p :: ps, s, hps, hs, h33, h64 => by
    have hlen : (gamma compI0 S g (Comparse.concatPrefixes (p :: ps) s)).length = (gamma compI0 S g p).length + (gamma compI0 S g (Comparse.concatPrefixes ps s)).length := (by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat, List.length_append]); obtain ⟨ih, ih33⟩ := nrcensus_concatPrefixes_33_lt64 ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs h33 (by omega); obtain ⟨hpC, hp1, hp0⟩ := hps p (List.mem_cons_self ..); refine ⟨?_, by omega⟩; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]; exact nrcensus_concat_len_ne80 (by omega) (by omega) (by omega) (by omega) (by omega) hp1 hp0 hpC ih
theorem nrcensus_concatPrefixes_lt9 : ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensus allT rT S g p ∧ 1 ≤ (gamma compI0 S g p).length ∧ (gamma compI0 S g p).take 1 ≠ [35#8]) → FnCensus allT rT S g s → (gamma compI0 S g (Comparse.concatPrefixes ps s)).length < 9 → FnCensus allT rT S g (Comparse.concatPrefixes ps s)
  | [], _, _, hs, _ => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact hs
  | p :: ps, s, hps, hs, hL => by
    have hlen : (gamma compI0 S g (Comparse.concatPrefixes (p :: ps) s)).length = (gamma compI0 S g p).length + (gamma compI0 S g (Comparse.concatPrefixes ps s)).length := (by rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat, List.length_append])
    obtain ⟨hpC, hp1, hp0⟩ := hps p (List.mem_cons_self ..)
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    exact nrcensus_concat_len_ne80 (by omega) (by omega) (by omega) (by omega) (by omega) hp1 hp0 hpC
      (nrcensus_concatPrefixes_lt9 ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs (by omega))
theorem nrcensus_mem_bool_head (b : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize b) : FnCensus allT rT S g p ∧ 1 ≤ (gamma compI0 S g p).length ∧ (gamma compI0 S g p).take 1 ≠ [35#8] := by
  obtain ⟨ba, hba_sz, hba_hd, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.bool_serialize_singleton_head b
  rw [hser] at hp; rcases List.mem_singleton.mp hp with rfl
  have h80 : (gamma compI0 S g (DY.Literal.literalToBytes ba)).take 1 ≠ [35#8] := by
    rw [gamma_literalToBytes_eq, hba_hd]; cases b <;> decide
  refine ⟨?_, ?_, h80⟩
  · refine nrcensus_lit _ (not_rv38HB_of_len_head_ne80 ?_ ?_ ?_ ?_ ?_ h80) <;>
      rw [CompPlant.gamma_literalToBytes_length] <;> omega
  · rw [CompPlant.gamma_literalToBytes_length]; omega
theorem nrcensus_mem_bool (b : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize b) : FnCensus allT rT S g p := (nrcensus_mem_bool_head b hp).1
theorem nrcensus_mem_slowNat : ∀ (n : Nat) {p : DY.Bytes}, p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n → FnCensus allT rT S g p
  | 0, _, hp => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero] at hp
    exact nrcensus_mem_bool false hp
  | n + 1, _, hp => by
    have hstep := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n
    rw [hstep, List.mem_append] at hp; exact hp.elim (nrcensus_mem_bool true) (nrcensus_mem_slowNat n)
theorem nrcensus_mem_slowNat_head : ∀ (n : Nat) {p : DY.Bytes}, p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n → FnCensus allT rT S g p ∧ 1 ≤ (gamma compI0 S g p).length ∧ (gamma compI0 S g p).take 1 ≠ [35#8]
  | 0, _, hp => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero] at hp
    exact nrcensus_mem_bool_head false hp
  | n + 1, _, hp => by
    have hstep := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n
    rw [hstep, List.mem_append] at hp; exact hp.elim (nrcensus_mem_bool_head true) (nrcensus_mem_slowNat_head n)
theorem nrcensus_mem_uint32_01 {n : UInt32} (hn : n = 0 ∨ n = 1) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize n) : FnCensus allT rT S g p ∧ 1 ≤ (gamma compI0 S g p).length ∧ (gamma compI0 S g p).take 1 ≠ [35#8] := by
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := hn.elim Or.inl (fun h => Or.inr (Or.inl h))
  obtain ⟨ba, hba_sz, hba_hd, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.uint32_serialize_singleton_head n hn'
  rw [hser] at hp; rcases List.mem_singleton.mp hp with rfl
  have h80 : (gamma compI0 S g (DY.Literal.literalToBytes ba)).take 1 ≠ [35#8] := by
    rw [gamma_literalToBytes_eq]; rcases hba_hd with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  refine ⟨?_, ?_, h80⟩
  · refine nrcensus_lit _ (not_rv38HB_of_len_head_ne80 ?_ ?_ ?_ ?_ ?_ h80) <;>
      rw [CompPlant.gamma_literalToBytes_length] <;> omega
  · rw [CompPlant.gamma_literalToBytes_length]; omega
theorem nrcensus_mem_slowBytes {b : DY.Bytes} (hb : FnCensus allT rT S g b) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize b) : FnCensus allT rT S g p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq b
  rw [hser, List.mem_append, List.mem_singleton] at hp; exact hp.elim (nrcensus_mem_slowNat _) (· ▸ hb)
theorem nrcensus_mem_slowString_participant {s : String} (hs : s = "alice" ∨ s = "bob") {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : FnCensus allT rT S g p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s; rw [hser, List.mem_append, List.mem_singleton] at hp
  rcases hp with hnat | rfl
  · exact nrcensus_mem_slowNat _ hnat
  · change FnCensus allT rT S g (DY.Literal.literalToBytes s.toUTF8)
    rcases hs with rfl | rfl <;> (rw [toUTF8_eq_ofList]; exact nrcensus_lit_size _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
theorem nrcensus_mem_slowString_participant_head {s : String} (hs : s = "alice" ∨ s = "bob") {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : FnCensus allT rT S g p ∧ 1 ≤ (gamma compI0 S g p).length ∧ (gamma compI0 S g p).take 1 ≠ [35#8] := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s; rw [hser, List.mem_append, List.mem_singleton] at hp
  rcases hp with hnat | rfl
  · exact nrcensus_mem_slowNat_head _ hnat
  · refine ⟨?_, ?_, ?_⟩
    · change FnCensus allT rT S g (DY.Literal.literalToBytes s.toUTF8); rcases hs with rfl | rfl <;> (rw [toUTF8_eq_ofList]; exact nrcensus_lit_size _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · change 1 ≤ (gamma compI0 S g (DY.Literal.literalToBytes s.toUTF8)).length; rw [CompPlant.gamma_literalToBytes_length, toUTF8_eq_ofList]; rcases hs with rfl | rfl <;> decide
    · change (gamma compI0 S g (DY.Literal.literalToBytes s.toUTF8)).take 1 ≠ [35#8]; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; rcases hs with rfl | rfl <;> decide
theorem gamma_slowString_serialize_length (s : String) : (((Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize s).flatMap (gamma compI0 S g)).length = s.utf8ByteSize + 1 + s.toUTF8.size := by have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s; rw [hser, List.flatMap_append, List.length_append, CompPlant.gamma_slowNat_serialize_length, List.flatMap_cons, List.flatMap_nil, List.append_nil, CompPlant.gamma_literalToBytes_length]
theorem nrcensus_serialize_recv1 {rk ck : DY.Bytes} (hrk : FnCensus allT rT S g rk) (hck : FnCensus allT rT S g ck) (hck_kf : ¬ KdfFree (gamma compI0 S g ck)) (hckL : (gamma compI0 S g ck).length = 32) : let l := (Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize [{ ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 }];
    FnCensus allT rT S g l ∧ KdfTail6 (gamma compI0 S g l) := by
  intro l; let t_sn : DY.Bytes := Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize 1) (DY.Literal.literalToBytes .empty); let t0 : DY.Bytes := Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize 0 ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize 1) (DY.Literal.literalToBytes .empty); let t_ck : DY.Bytes := Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length ck)) (DY.Concat.concat ck t0); have hl : l = Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize rk ++ Comparse.NonExtensibleMessageFormat.slowBytes.serialize ck) t0 := (by have hnil := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_nil; have h1 := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons { ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 } []; have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq { ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 }; dsimp only [l]; rw [h1, hser, hnil, ← List.append_assoc, ← CompExcuse.concatPrefixes_append, ← CompExcuse.concatPrefixes_append])
  have hT_sn : FnCensus allT rT S g t_sn ∧ (gamma compI0 S g t_sn).length = 2 := by
    have hL : (gamma compI0 S g t_sn).length = 2 := by dsimp only [t_sn]; rw [gamma_concatPrefixes_length, CompPlant.gamma_slowNat_serialize_length, CompPlant.gamma_literalToBytes_length]; rfl
    exact ⟨nrcensus_concatPrefixes_lt9 _ (fun _ hp => nrcensus_mem_slowNat_head _ hp) (nrcensus_lit_size _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by change (gamma compI0 S g t_sn).length < 9; omega), hL⟩
  have hT0 : FnCensus allT rT S g t0 ∧ (gamma compI0 S g t0).length = 6 := by
    obtain ⟨ba0, _, hu0⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.uint32_serialize_singleton 0
    let u0 : DY.Bytes := DY.Literal.literalToBytes ba0
    obtain ⟨hu0C, hu01, hu080⟩ := nrcensus_mem_uint32_01 (Or.inl rfl) (by rw [hu0]; exact List.mem_singleton_self u0)
    have hu0L : (gamma compI0 S g u0).length = 4 := by have h := CompPlant.gamma_uint32_serialize_length compI0 S g 0; rw [hu0] at h; simpa using h
    change FnCensus allT rT S g (Comparse.concatPrefixes _ _) ∧ (gamma compI0 S g (Comparse.concatPrefixes _ _)).length = 6; rw [← CompExcuse.concatPrefixes_append, hu0, concatPrefixes_singleton, gamma_concat, List.length_append, hu0L, hT_sn.2]; exact ⟨nrcensus_concat_len_ne80 (by rw [hu0L, hT_sn.2]; decide) (by rw [hu0L, hT_sn.2]; decide) (by rw [hu0L, hT_sn.2]; decide) (by rw [hu0L, hT_sn.2]; decide) (by rw [hu0L, hT_sn.2]; decide) hu01 hu080 hu0C hT_sn.1, rfl⟩
  have hsplit_ck := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq ck; have hsplit_rk := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq rk; have hckT' : KdfTail6 (gamma compI0 S g ck ++ gamma compI0 S g t0) := ⟨[], _, _, rfl, hck_kf, hckL, hT0.2⟩
  have hckT : KdfTail6 (gamma compI0 S g (DY.Concat.concat ck t0)) := by rw [gamma_concat]; exact hckT'
  obtain ⟨hs_ck, hs_ckT⟩ := nrcensus_concatPrefixes_kdfTail6 _ (fun _ hp => nrcensus_mem_slowNat _ hp) (nrcensus_concat hckT'.not_rv hck hT0.1) hckT; have hT2T' : KdfTail6 (gamma compI0 S g rk ++ gamma compI0 S g t_ck) := hs_ckT.append_left _
  have hT2T : KdfTail6 (gamma compI0 S g (DY.Concat.concat rk t_ck)) := by rw [gamma_concat]; exact hT2T'
  rw [hl, ← CompExcuse.concatPrefixes_append, hsplit_ck, ← CompExcuse.concatPrefixes_append, concatPrefixes_singleton, hsplit_rk, ← CompExcuse.concatPrefixes_append, concatPrefixes_singleton]; exact nrcensus_concatPrefixes_kdfTail6 _ (fun _ hp => nrcensus_mem_slowNat _ hp) (nrcensus_concat hT2T'.not_rv hrk hs_ck) hT2T
theorem nrcensus_concatPrefixes_bool (b : Bool) {s : DY.Bytes} (hs : FnCensus allT rT S g s) (hL : (gamma compI0 S g s).length = 32 ∨ (gamma compI0 S g s).length = 64) : FnCensus allT rT S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.bool.serialize b) s) ∧ ((gamma compI0 S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.bool.serialize b) s)).length = 33 ∨ 65 ≤ (gamma compI0 S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.bool.serialize b) s)).length) := by
  obtain ⟨ba, _, hx⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton b
  let x : DY.Bytes := DY.Literal.literalToBytes ba
  obtain ⟨hxC, hx1, hx80⟩ := nrcensus_mem_bool_head b (by rw [hx]; exact List.mem_singleton_self x)
  have hxL : (gamma compI0 S g x).length = 1 := by have h := CompPlant.gamma_bool_serialize_length compI0 S g b; rw [hx] at h; simpa using h
  rw [hx, concatPrefixes_singleton, gamma_concat, List.length_append, hxL]; exact ⟨nrcensus_concat_len_ne80 (by rw [hxL]; omega) (by rw [hxL]; omega) (by rw [hxL]; omega) (by rw [hxL]; omega) (by rw [hxL]; omega) hx1 hx80 hxC hs, by omega⟩
theorem nrcensus_serialize_local_pqxdh {ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState} (hpa : ls.participant = "alice" ∨ ls.participant = "bob") (hsk : FnCensus allT rT S g ls.state.sk) (hskL : (gamma compI0 S g ls.state.sk).length = 32 ∨ (gamma compI0 S g ls.state.sk).length = 64) : FnCensus allT rT S g (Comparse.serialize ls : DY.Bytes) := by
  rw [CompRX0NBSC38Parts.serialize_local_pqxdh_eq, ← CompExcuse.concatPrefixes_append, ← CompExcuse.concatPrefixes_append]; obtain ⟨h2, h2L⟩ := nrcensus_concatPrefixes_bool (allT := allT) (rT := rT) (S := S) (g := g) ls.state.kind.toBits.2 hsk hskL
  have hpsH : ∀ p ∈ (Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize ls.participant ++ (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize ls.state.kind.toBits.1, FnCensus allT rT S g p ∧ 1 ≤ (gamma compI0 S g p).length ∧ (gamma compI0 S g p).take 1 ≠ [35#8] := fun _ hp =>
    (List.mem_append.mp hp).elim (nrcensus_mem_slowString_participant_head hpa) (nrcensus_mem_bool_head _)
  rw [CompExcuse.concatPrefixes_append]
  rcases h2L with h33 | h65
  · refine (nrcensus_concatPrefixes_33_lt64 _ hpsH h2 (by omega) ?_).1; rw [gamma_concatPrefixes_length, List.flatMap_append, List.length_append, gamma_slowString_serialize_length, CompPlant.gamma_bool_serialize_length, h33]
    rcases hpa with hpA | hpB
    · rw [hpA, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.2]; decide
    · rw [hpB, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.2]; decide
  · refine (nrcensus_concatPrefixes_ge65_head _ hpsH h2 h65 ?_).1
    have hpartU : ls.participant.utf8ByteSize + 1 + ls.participant.toUTF8.size < 20 := by
      rcases hpa with hpA | hpB
      · rw [hpA, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.2]; decide
      · rw [hpB, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.2]; decide
    simp only [gamma_concatPrefixes_length, List.flatMap_append, List.length_append, gamma_slowString_serialize_length, CompPlant.gamma_bool_serialize_length]
    rcases hskL with h | h <;> omega
end NRSer
end Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA
