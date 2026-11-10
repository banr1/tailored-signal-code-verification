/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus
public import Symbolic.BugInjection.Proofs.Common443.CompRWSBobChain
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.CompFitsNames
import Init.Data.String
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2Census38
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection.Proofs.Common443.CompExcuse (gamma_concat trStatePrefixes)
open Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct (gamma_hmac_length)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompRMemoKnown CompRI0TermInj CompRNonInj38Census CompRQRestCensusZ Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def NIOK (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := DY.Libsignal.Composed.Refinement.assumedInjective x.1 = false → NonInjOffXZ x.2.2
theorem nonInjOffXZ_of_len {v : HwBytes} (h32 : v.length ≠ 32) (h8 : v.length ≠ 8) : NonInjOffXZ v := ⟨⟨fun h => absurd h h32, fun h => absurd h h8⟩, fun h => absurd h h32⟩
theorem niok_of_len {x : DY.Bytes × DY.Bytes × HwBytes} (h32 : x.2.2.length ≠ 32) (h8 : x.2.2.length ≠ 8) : NIOK x := fun _ => nonInjOffXZ_of_len h32 h8
theorem niok_of_inj {x : DY.Bytes × DY.Bytes × HwBytes} (h : DY.Libsignal.Composed.Refinement.assumedInjective x.1 = true) : NIOK x := fun h' => absurd (h.symm.trans h') (by decide)
theorem nonInjOffXZ_zeroDh : NonInjOffXZ CompRI0Census.zeroDh := ⟨⟨fun _ => kdfFree_of_mem_x25519Vals (by simp [x25519Vals]), fun h => absurd h (by decide)⟩, fun _ _ => rfl⟩
abbrev Census (i : ExternInterpretation) (S : Sem) (g : Ghost) (t : DY.Bytes) : Prop := MemoOK i S g NIOK t
section Prim
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem census_lit (bs : ByteArray) (h : NonInjOffXZ (gamma i S g (DY.Literal.literalToBytes bs))) : Census i S g (DY.Literal.literalToBytes bs) := by
  intro x hx _; have hv := (CompRPreMemoSound.memo_sound i S g _ hx).2; unfold gamma' at hx; rw [show DY.Literal.literalToBytes bs = ({ lit := bs } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gLit0 (gAll i S g)] at hx
  rcases List.mem_singleton.mp hx with rfl; exact hv ▸ h
theorem census_concat {a c : DY.Bytes} (h : NonInjOffXZ (gamma i S g a ++ gamma i S g c)) (ha : Census i S g a) (hc : Census i S g c) : Census i S g (DY.Concat.concat a c) := by
  intro x hx; unfold gamma' at hx; rw [show DY.Concat.concat a c = ({ lhs := a, rhs := c } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gConcat0 (gAll i S g)] at hx; simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, CompPlant.bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxc <;> [exact fun _ => h; exact ha x hxa; exact hc x hxc]
theorem census_concat_len {a c : DY.Bytes} (h32 : (gamma i S g a).length + (gamma i S g c).length ≠ 32) (h8 : (gamma i S g a).length + (gamma i S g c).length ≠ 8) (ha : Census i S g a) (hc : Census i S g c) : Census i S g (DY.Concat.concat a c) :=
  census_concat (nonInjOffXZ_of_len (by simpa using h32) (by simpa using h8)) ha hc
theorem census_randTerm (ts sz : Nat) : Census i S g (randTerm ts sz) := by
  intro x hx hai; unfold gamma' randTerm at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx
  split_ifs at hx with hsz; · cases hx
  rcases List.mem_singleton.mp hx with rfl
  have htrue : assumedInjective (({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack) = true :=
    (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (.inl ⟨_, DY.BytesView.view_pack _, hsz⟩)
  exact absurd (htrue.symm.trans hai) (by decide)
theorem census_dhPk {sk : DY.Bytes} (hsk : Census i S g sk) : Census i S g (DY.DiffieHellman.dhPk sk) := memoOK_dhPk (fun _ hx => niok_of_inj (by rw [hx]; exact (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]))) hsk
theorem census_dh_pack {pk sk : DY.Bytes} (hpk : Census i S g pk) (hsk : Census i S g sk) : Census i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := memoOK_dh_pack (fun _ hx => niok_of_inj (by rw [hx]; exact (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [DY.BytesView.view_pack]))) hpk hsk
theorem census_kdfExtract {k m : DY.Bytes} (hk : Census i S g k) (hm : Census i S g m) : Census i S g (DY.KdfExtract.kdfExtract k m) := memoOK_kdfExtract (fun _ hx => niok_of_inj (by rw [hx]; exact (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.KdfExtract.kdfExtract k m = ({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]))) hk hm
theorem census_symEnc {k iv m : DY.Bytes} (hk : Census i S g k) (hiv : Census i S g iv) (hm : Census i S g m) : Census i S g (DY.SymEnc.symEnc k iv m) := memoOK_symEnc (fun _ hx => niok_of_inj (by rw [hx]; exact (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]))) hk hiv hm
theorem census_trunc8 {a : DY.Bytes} (ha : Census i S g a) : Census i S g (DY.Trunc.trunc8 a) := memoOK_trunc8 (fun _ hx => niok_of_inj (by rw [hx]; exact (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]))) ha
theorem census_kemPk {sk : DY.Bytes} (hsk : Census i S g sk) : Census i S g (DY.PQKem.kemPk sk) := memoOK_kemPk hsk
theorem census_kemEncap_fst {pk e : DY.Bytes} (hpk : Census i S g pk) (he : Census i S g e) : Census i S g (DY.PQKem.kemEncap pk e).1 := memoOK_kemEncap_fst (fun _ hx => niok_of_inj (by rw [hx]; exact (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show (DY.PQKem.kemEncap pk e).1 = ({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]))) hpk he
theorem census_kemEncap_snd {pk e : DY.Bytes} (hpk : Census i S g pk) (he : Census i S g e) : Census i S g (DY.PQKem.kemEncap pk e).2 := memoOK_kemEncap_snd (fun _ hx => niok_of_inj (by rw [hx]; exact (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show (DY.PQKem.kemEncap pk e).2 = ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]))) hpk he
theorem census_spqrInit {a p : DY.Bytes} (ha : Census i S g a) (hp : Census i S g p) : Census i S g (DY.Spqr.spqrInit a p) := memoOK_spqrInit ha hp
theorem census_spqrChainKey {a p idx : DY.Bytes} (ha : Census i S g a) (hp : Census i S g p) (hidx : Census i S g idx) : Census i S g (DY.Spqr.spqrChainKey a p idx) := memoOK_spqrChainKey ha hp hidx
theorem census_spqrSendState {st c : DY.Bytes} (hst : Census i S g st) (hc : Census i S g c) : Census i S g (DY.Spqr.spqrSend st c).1 := memoOK_spqrSendState hst hc
theorem census_spqrSendMsg {st c : DY.Bytes} (hst : Census i S g st) (hc : Census i S g c) : Census i S g (DY.Spqr.spqrSend st c).2.2 := memoOK_spqrSendMsg hst hc
theorem census_x25519Key {pk : DY.Bytes} (h : Census i S g pk) : Census i S g (DY.X25519.x25519Key pk) := memoOK_x25519Key h
theorem census_of_dhPk {sk : DY.Bytes} (h : Census i S g (DY.DiffieHellman.dhPk sk)) : Census i S g sk := memoOK_dhPk_elim h
theorem census_dh {pk sk : DY.Bytes} (hpk : Census i S g pk) (hsk : Census i S g sk) : Census i S g (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    split <;> [exact census_dh_pack hpk hsk; exact census_dh_pack (census_dhPk hsk) (census_of_dhPk hpk)]
  · exact census_dh_pack hpk hsk
theorem census_agree {pk sk : DY.Bytes} (hpk : Census i S g pk) (hsk : Census i S g sk) : Census i S g (DY.Libsignal.PQXDH.agree pk sk) := census_dh (census_x25519Key hpk) hsk
theorem census_hmac {a b : DY.Bytes} (ha : Census i S g a) (hb : Census i S g b) : Census i S g (DY.Libsignal.TripleRatchet.hmac a b) := census_kdfExtract ha hb
theorem census_lit_size (bs : ByteArray) (h32 : bs.size ≠ 32) (h8 : bs.size ≠ 8) : Census i S g (DY.Literal.literalToBytes bs) :=
  census_lit bs (nonInjOffXZ_of_len (by rw [CompPlant.gamma_literalToBytes_length]; exact h32) (by rw [CompPlant.gamma_literalToBytes_length]; exact h8))
theorem census_litByte (b : UInt8) : Census i S g (DY.Libsignal.TripleRatchet.litByte b) := census_lit_size _ (by simp [ByteArray.size]) (by simp [ByteArray.size])
theorem gamma_litByte_length (b : UInt8) : (gamma i S g (DY.Libsignal.TripleRatchet.litByte b)).length = 1 := CompPlant.gamma_literalToBytes_length i S g _
theorem gamma_trLit_length (s : String) : (gamma i S g (DY.Libsignal.TripleRatchet.lit s)).length = s.toUTF8.size := CompPlant.gamma_literalToBytes_length i S g _
theorem census_hkdfBlock1 {prk info : DY.Bytes} (h31 : (gamma i S g info).length ≠ 31) (h7 : (gamma i S g info).length ≠ 7) (hprk : Census i S g prk) (hinfo : Census i S g info) : Census i S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := by
  unfold DY.Libsignal.TripleRatchet.hkdfBlock1
  refine census_hmac hprk (census_concat_len ?_ ?_ hinfo (census_litByte _)) <;> rw [gamma_litByte_length] <;> omega
end Prim
section I0
variable {S : Sem} {g : Ghost}
theorem census_hkdfBlock2 {prk info : DY.Bytes} (h31 : (gamma compI0 S g info).length ≠ 31) (h7 : (gamma compI0 S g info).length ≠ 7) (hprk : Census compI0 S g prk) (hinfo : Census compI0 S g info) : Census compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := by
  unfold DY.Libsignal.TripleRatchet.hkdfBlock2
  refine census_hmac hprk (census_concat_len ?_ ?_ (census_hkdfBlock1 h31 h7 hprk hinfo) (census_concat_len ?_ ?_ hinfo (census_litByte _))) <;>
    simp only [gamma_concat, List.length_append, gamma_litByte_length, DY.Libsignal.TripleRatchet.hkdfBlock1, gamma_hmac_length] <;> omega
theorem census_hkdfBlock3 {prk info : DY.Bytes} (h31 : (gamma compI0 S g info).length ≠ 31) (h7 : (gamma compI0 S g info).length ≠ 7) (hprk : Census compI0 S g prk) (hinfo : Census compI0 S g info) : Census compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := by
  unfold DY.Libsignal.TripleRatchet.hkdfBlock3
  refine census_hmac hprk (census_concat_len ?_ ?_ (census_hkdfBlock2 h31 h7 hprk hinfo) (census_concat_len ?_ ?_ hinfo (census_litByte _))) <;>
    simp only [gamma_concat, List.length_append, gamma_litByte_length, DY.Libsignal.TripleRatchet.hkdfBlock2, gamma_hmac_length] <;> omega
theorem nonInjOffXZ_ff32 : NonInjOffXZ (List.replicate 32 0xff#8) := ⟨⟨fun _ => by decide, fun h => absurd h (by decide)⟩, fun _ hmem => absurd hmem (by decide)⟩
theorem census_lit_ofBA {bs : ByteArray} (h : NonInjOffXZ (ofByteArray bs)) : Census compI0 S g (DY.Literal.literalToBytes bs) :=
  census_lit bs (by rw [show DY.Literal.literalToBytes bs = ({ lit := bs } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl, CompFreshDistinct.gamma_lit]; exact h)
theorem census_zeroSalt : Census compI0 S g DY.Libsignal.TripleRatchet.zeroSalt := census_lit_ofBA nonInjOffXZ_zeroDh
theorem census_zeroKey : Census compI0 S g DY.Spqr.zeroKey := census_lit_ofBA nonInjOffXZ_zeroDh
theorem census_discontinuity : Census compI0 S g DY.Libsignal.PQXDH.discontinuity := census_lit_ofBA nonInjOffXZ_ff32
theorem compKyberEncaps_drop1568_length' (b : HwBytes) : ((compKyberEncaps b).drop 1568).length = 32 := by
  have hL : (compKyberEncaps b).length = 1600 := by unfold compKyberEncaps; split_ifs <;> simp only [List.length_append, compKyberCt0, compKyberSs0, compKyberCt1, compKyberSs1, compKyberCt2, compKyberSs2, compDefaultKyberCt, compDefaultKyberSs, CompRBobInit.leBytes_length', List.length_replicate]
  rw [List.length_drop, hL]
theorem gamma_kemEncap_snd_length' {pk e : DY.Bytes} (he : (gamma compI0 S g e).length = 32) : (gamma compI0 S g (DY.PQKem.kemEncap pk e).2).length = 32 := by rw [CompRWSBobChain.gamma_kemEncap_snd_compI0]; simp only [he, ite_true]; exact compKyberEncaps_drop1568_length' (gamma compI0 S g e)
theorem census_trWire_of_len {ver : UInt8} {rk ct pq : DY.Bytes} {c pc : UInt32} {ev : DY.TrWire.EncodingVariation} (h32 : (gamma compI0 S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev)).length ≠ 32) (h8 : (gamma compI0 S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev)).length ≠ 8) (hrk : Census compI0 S g rk) (hct : Census compI0 S g ct) (hpq : Census compI0 S g pq) : Census compI0 S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev) := by
  rw [show DY.TrWire.trWireMsg ver rk c pc ct pq ev = ({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack from rfl] at h32 h8 ⊢; intro x hx
  exact memoOK_trWire (P := fun y => y.2.2 = gamma compI0 S g y.1 → NIOK y)
    (fun y hy hs => niok_of_len (by rw [hs, hy]; exact h32) (by rw [hs, hy]; exact h8))
    (fun y hy _ => hrk y hy) (fun y hy _ => hct y hy) (fun y hy _ => hpq y hy) x hx (CompRPreMemoSound.memo_sound compI0 S g _ hx).2
theorem census_createChain {rk pk sk : DY.Bytes} (hrk : Census compI0 S g rk) (hpk : Census compI0 S g pk) (hsk : Census compI0 S g sk) : Census compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧ Census compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by
  have hsz : "WhisperRatchet".toUTF8.size = 14 := by
    rw [String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := "WhisperRatchet"), String.toByteArray_ofList]; decide
  have hprk := census_hmac hrk (census_agree hpk hsk); have hinfo : Census compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := census_lit_size _ (by rw [hsz]; decide) (by rw [hsz]; decide)
  exact ⟨census_hkdfBlock1 (by rw [gamma_trLit_length, hsz]; decide) (by rw [gamma_trLit_length, hsz]; decide) hprk hinfo,
    census_hkdfBlock2 (by rw [gamma_trLit_length, hsz]; decide) (by rw [gamma_trLit_length, hsz]; decide) hprk hinfo⟩
theorem census_kdfCk {ck : DY.Bytes} (hck : Census compI0 S g ck) : Census compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∧ Census compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck).2 := ⟨census_hmac hck (census_litByte _), census_hmac hck (census_litByte _)⟩
theorem census_trMsgKeys {salt seed : DY.Bytes} (hsalt : Census compI0 S g salt) (hseed : Census compI0 S g seed) : let mk := DY.Libsignal.TripleRatchet.trMsgKeys salt seed;
    Census compI0 S g mk.cipherKey ∧ Census compI0 S g mk.macKey ∧ Census compI0 S g mk.iv := by
  have hsz : "WhisperMessageKeys".toUTF8.size = 18 := by
    rw [String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := "WhisperMessageKeys"), String.toByteArray_ofList]; decide
  have hprk := census_hmac hsalt hseed; have hinfo : Census compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") := census_lit_size _ (by rw [hsz]; decide) (by rw [hsz]; decide)
  have h31 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")).length ≠ 31 := by rw [gamma_trLit_length, hsz]; decide
  have h7 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")).length ≠ 7 := by rw [gamma_trLit_length, hsz]; decide
  exact ⟨census_hkdfBlock1 h31 h7 hprk hinfo, census_hkdfBlock2 h31 h7 hprk hinfo, census_hkdfBlock3 h31 h7 hprk hinfo⟩
theorem census_serializedIk {ik : DY.Bytes} (hikL : (gamma compI0 S g ik).length = 32) (hik : Census compI0 S g ik) : Census compI0 S g (DY.Libsignal.PQXDH.serializedIk ik) := by
  unfold DY.Libsignal.PQXDH.serializedIk DY.Libsignal.PQXDH.encodeEC
  refine census_concat_len ?_ ?_ (census_litByte _) hik <;> rw [gamma_litByte_length, hikL] <;> decide
theorem census_pqxdhKdf_none {dh1 dh2 dh3 ss : DY.Bytes} (hdh1L : (gamma compI0 S g dh1).length = 32) (hdh2L : (gamma compI0 S g dh2).length = 32) (hdh3L : (gamma compI0 S g dh3).length = 32) (hssL : (gamma compI0 S g ss).length = 32) (hdh1 : Census compI0 S g dh1) (hdh2 : Census compI0 S g dh2) (hdh3 : Census compI0 S g dh3) (hss : Census compI0 S g ss) : let keys := DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss);
    Census compI0 S g keys.rk ∧ Census compI0 S g keys.ck ∧ Census compI0 S g keys.pqr := by
  have hsz : "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8.size = 46 := by
    rw [String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"), String.toByteArray_ofList]; decide
  have hc3 := census_concat_len (by rw [hdh3L, hssL]; decide) (by rw [hdh3L, hssL]; decide) hdh3 hss
  have hc2 : Census compI0 S g (DY.Concat.concat dh2 (DY.Concat.concat dh3 ss)) := by refine census_concat_len ?_ ?_ hdh2 hc3 <;> (rw [gamma_concat, List.length_append, hdh2L, hdh3L, hssL]; decide)
  have hc1 : Census compI0 S g (DY.Concat.concat dh1 (DY.Concat.concat dh2 (DY.Concat.concat dh3 ss))) := by refine census_concat_len ?_ ?_ hdh1 hc2 <;> (rw [gamma_concat, gamma_concat, List.length_append, List.length_append, hdh1L, hdh2L, hdh3L, hssL]; decide)
  have hikm : Census compI0 S g (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss) := by refine census_concat_len ?_ ?_ census_discontinuity hc1 <;> (rw [DY.Libsignal.PQXDH.discontinuity, CompPlant.gamma_literalToBytes_length, gamma_concat, gamma_concat, gamma_concat, List.length_append, List.length_append, List.length_append, hdh1L, hdh2L, hdh3L, hssL]; decide)
  have hprk := census_hmac census_zeroSalt hikm; have hinfo : Census compI0 S g DY.Libsignal.PQXDH.pqxdhLabel := census_lit_size _ (by rw [hsz]; decide) (by rw [hsz]; decide)
  have h31 : (gamma compI0 S g DY.Libsignal.PQXDH.pqxdhLabel).length ≠ 31 := by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, hsz]; decide
  have h7 : (gamma compI0 S g DY.Libsignal.PQXDH.pqxdhLabel).length ≠ 7 := by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, hsz]; decide
  exact ⟨census_hkdfBlock1 h31 h7 hprk hinfo, census_hkdfBlock2 h31 h7 hprk hinfo, census_hkdfBlock3 h31 h7 hprk hinfo⟩
end I0
section Ser
open Comparse Comparse.NonExtensibleMessageFormat
open DY.Literal (literalToBytes)
open DY.Concat (concat)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse (concatPrefixes_nil concatPrefixes_cons)
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem census_concatPrefixes : ∀ (ps : List Bytes) {s : Bytes}, (∀ p ∈ ps, Census i S g p) → Census i S g s → 33 ≤ (gamma i S g s).length → Census i S g (concatPrefixes ps s) ∧ 33 ≤ (gamma i S g (concatPrefixes ps s)).length
  | [], _, _, hs, hL => by rw [concatPrefixes_nil]; exact ⟨hs, hL⟩
  | p :: ps, s, hps, hs, hL => by
    obtain ⟨ih, ihL⟩ := census_concatPrefixes ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs hL
    rw [concatPrefixes_cons]
    have hlen : (gamma i S g (concat p (concatPrefixes ps s))).length = (gamma i S g p).length + (gamma i S g (concatPrefixes ps s)).length := by rw [gamma_concat, List.length_append]
    exact ⟨census_concat_len (by omega) (by omega) (hps p (List.mem_cons_self ..)) ih, by omega⟩
theorem census_mem_bool (b : Bool) {p : Bytes} (hp : p ∈ bool.serialize b) : Census i S g p := by
  obtain ⟨ba, hba_sz, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton b
  rw [hser] at hp; rcases List.mem_singleton.mp hp with rfl
  refine census_lit _ (nonInjOffXZ_of_len ?_ ?_) <;> rw [CompPlant.gamma_literalToBytes_length] <;> omega
theorem census_mem_slowNat : ∀ (n : Nat) {p : Bytes}, p ∈ slowNat.serialize n → Census i S g p
  | 0, _, hp => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero] at hp
    exact census_mem_bool false hp
  | n + 1, _, hp => by
    have hstep := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n
    rw [hstep, List.mem_append] at hp; exact hp.elim (census_mem_bool true) (census_mem_slowNat n)
theorem census_mem_uint32 (n : UInt32) {p : Bytes} (hp : p ∈ uint32.serialize n) : Census i S g p := by
  obtain ⟨ba, hba_sz, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.uint32_serialize_singleton n
  rw [hser] at hp; rcases List.mem_singleton.mp hp with rfl
  refine census_lit _ (nonInjOffXZ_of_len ?_ ?_) <;> rw [CompPlant.gamma_literalToBytes_length] <;> omega
theorem census_mem_slowBytes {b : Bytes} (hb : Census i S g b) {p : Bytes} (hp : p ∈ slowBytes.serialize b) : Census i S g p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq b
  rw [hser, List.mem_append, List.mem_singleton] at hp; exact hp.elim (census_mem_slowNat _) (· ▸ hb)
theorem census_mem_slowString (s : String) (h32 : s.toUTF8.size ≠ 32) (h8 : s.toUTF8.size ≠ 8) {p : Bytes} (hp : p ∈ slowString.serialize s) : Census i S g p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s
  rw [hser, List.mem_append, List.mem_singleton] at hp; rcases hp with hnat | rfl <;> [exact census_mem_slowNat _ hnat; exact census_lit_size _ h32 h8]
theorem census_concatPrefixes_lt8 : ∀ (ps : List Bytes) {s : Bytes}, (∀ p ∈ ps, Census i S g p) → Census i S g s → (gamma i S g (concatPrefixes ps s)).length < 8 → Census i S g (concatPrefixes ps s)
  | [], _, _, hs, _ => by rw [concatPrefixes_nil]; exact hs
  | p :: ps, s, hps, hs, hL => by
    rw [concatPrefixes_cons] at hL ⊢
    have hlen : (gamma i S g (concat p (concatPrefixes ps s))).length = (gamma i S g p).length + (gamma i S g (concatPrefixes ps s)).length := by rw [gamma_concat, List.length_append]
    exact census_concat_len (by omega) (by omega) (hps p (List.mem_cons_self ..)) (census_concatPrefixes_lt8 ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs (by omega))
theorem gamma_concatPrefixes_length (ps : List Bytes) (s : Bytes) : (gamma i S g (concatPrefixes ps s)).length = (ps.flatMap (gamma i S g)).length + (gamma i S g s).length := by rw [CompExcuse.gamma_concatPrefixes, List.length_append]
theorem census_serialize_recv1 {rk ck : Bytes} (hrk : Census i S g rk) (hck : Census i S g ck) (hckL : (gamma i S g ck).length = 32) : let l := (ExtensibleMessageFormat.list (ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize [{ ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 }];
    Census i S g l ∧ 33 ≤ (gamma i S g l).length := by
  intro l; let t0 : Bytes := concatPrefixes (uint32.serialize 0 ++ slowNat.serialize 1) (literalToBytes .empty); have hl : l = concatPrefixes (slowBytes.serialize rk ++ slowBytes.serialize ck) t0 := (by have hnil := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_nil; have h1 := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons { ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 } []; have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq { ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 }; dsimp only [l]; rw [h1, hser, hnil, ← List.append_assoc, ← CompExcuse.concatPrefixes_append, ← CompExcuse.concatPrefixes_append]); have hL : (gamma i S g t0).length = 6 := (by rw [gamma_concatPrefixes_length, List.flatMap_append, List.length_append, CompPlant.gamma_uint32_serialize_length, CompPlant.gamma_slowNat_serialize_length, CompPlant.gamma_literalToBytes_length]; rfl); have hT0 : Census i S g t0 := census_concatPrefixes_lt8 _ (fun p hp => (List.mem_append.mp hp).elim (census_mem_uint32 _) (census_mem_slowNat _)) (census_lit_size _ (by decide) (by decide)) (by change (gamma i S g t0).length < 8; omega)
  have hT1 : Census i S g (concat ck t0) := by refine census_concat_len ?_ ?_ hck hT0 <;> rw [hckL, hL] <;> decide
  have hT1L : 33 ≤ (gamma i S g (concat ck t0)).length := by rw [gamma_concat, List.length_append, hckL, hL]; decide
  have h1 : concat ck t0 = concatPrefixes [ck] t0 := by rw [concatPrefixes_cons, concatPrefixes_nil]
  rw [h1] at hT1 hT1L
  have hsplit := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq ck; rw [hl, ← CompExcuse.concatPrefixes_append, hsplit, ← CompExcuse.concatPrefixes_append]; exact census_concatPrefixes _ (fun p hp => census_mem_slowBytes hrk hp) (census_concatPrefixes _ (fun p hp => census_mem_slowNat _ hp) hT1 hT1L).1 (census_concatPrefixes _ (fun p hp => census_mem_slowNat _ hp) hT1 hT1L).2
theorem census_concatPrefixes_bool (b : Bool) {s : Bytes} (hs : Census i S g s) (hL : 32 ≤ (gamma i S g s).length) : Census i S g (concatPrefixes (bool.serialize b) s) ∧ 33 ≤ (gamma i S g (concatPrefixes (bool.serialize b) s)).length := by
  obtain ⟨ba, _, hx⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton b; have hxC : Census i S g (literalToBytes ba) := census_mem_bool b (by rw [hx]; exact List.mem_singleton_self _)
  have hxL : (gamma i S g (literalToBytes ba)).length = 1 := by have h := CompPlant.gamma_bool_serialize_length (i := i) (S := S) (g := g) b; rw [hx] at h; simpa using h
  rw [hx, concatPrefixes_cons, concatPrefixes_nil, gamma_concat, List.length_append, hxL]; exact ⟨census_concat_len (by rw [hxL]; omega) (by rw [hxL]; omega) hxC hs, by omega⟩
theorem participant_size_ne {pa : String} (h : pa = "alice" ∨ pa = "bob") : pa.toUTF8.size ≠ 32 ∧ pa.toUTF8.size ≠ 8 := by
  rcases h with rfl | rfl
  · have hsz : "alice".toUTF8.size = 5 := by
      rw [String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := "alice"), String.toByteArray_ofList]; decide
    rw [hsz]; exact ⟨by decide, by decide⟩
  · have hsz : "bob".toUTF8.size = 3 := by
      rw [String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := "bob"), String.toByteArray_ofList]; decide
    rw [hsz]; exact ⟨by decide, by decide⟩
theorem census_serialize_local_pqxdh {ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState} (hpa : ls.participant.toUTF8.size ≠ 32 ∧ ls.participant.toUTF8.size ≠ 8) (hsk : Census i S g ls.state.sk) (hskL : 32 ≤ (gamma i S g ls.state.sk).length) : Census i S g (serialize ls : Bytes) := by rw [CompRX0NBSC38Parts.serialize_local_pqxdh_eq, ← CompExcuse.concatPrefixes_append, ← CompExcuse.concatPrefixes_append]; obtain ⟨h2, h2L⟩ := census_concatPrefixes_bool (i := i) (S := S) (g := g) ls.state.kind.toBits.2 hsk hskL; obtain ⟨h1, h1L⟩ := census_concatPrefixes_bool (i := i) (S := S) (g := g) ls.state.kind.toBits.1 h2 (by omega); exact (census_concatPrefixes _ (fun p hp => census_mem_slowString _ hpa.1 hpa.2 hp) h1 h1L).1
end Ser
section St
variable {S : Sem} {g : Ghost}
theorem gamma_setup_len {r : Records} (hc : Compat compI0 r S g) (hwf : RecordsWF r) {ts sz : Nat} (hp : (ts, sz) ∈ setupRandomsAt r) (hsz : sz ≠ 0) : (gamma compI0 S g (randTerm ts sz)).length = sz := by rw [CompPlant.gamma_randTerm_length compI0 S g ts sz hsz, hc.1 (ts, sz) hp]; exact hwf.2.1 (ts, sz) hp
structure TRStateC (S : Sem) (g : Ghost) (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  peer : st.peer.toUTF8.size ≠ 32 ∧ st.peer.toUTF8.size ≠ 8
  myIk : Census compI0 S g st.myIk
  peerIk : Census compI0 S g st.peerIk
  rk : Census compI0 S g st.rk
  dhs : Census compI0 S g st.dhs
  cks : Census compI0 S g st.cks
  sid : Census compI0 S g st.sid
  spqr : Census compI0 S g st.spqr
  recv : Census compI0 S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize st.recv)
  recvL : 33 ≤ (gamma compI0 S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize st.recv)).length
theorem census_mem_trStatePrefixes {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hpa : ls.participant.toUTF8.size ≠ 32 ∧ ls.participant.toUTF8.size ≠ 8) (hst : TRStateC S g ls.state) {p : DY.Bytes} (hp : p ∈ trStatePrefixes ls) : Census compI0 S g p := by
  unfold trStatePrefixes at hp; simp only [List.mem_append] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h <;> [exact census_mem_slowString _ hpa.1 hpa.2 h; exact census_mem_slowString _ hst.peer.1 hst.peer.2 h; exact census_mem_slowBytes hst.myIk h; exact census_mem_slowBytes hst.peerIk h;
     exact census_mem_slowBytes hst.rk h; exact census_mem_slowBytes hst.dhs h; exact census_mem_slowBytes hst.cks h; exact census_mem_uint32 _ h; exact census_mem_uint32 _ h;
     exact census_mem_slowBytes hst.sid h; exact census_mem_bool _ h; exact census_mem_slowNat _ h; exact census_mem_slowBytes hst.spqr h]
theorem census_serialize_local_tr {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hpa : ls.participant.toUTF8.size ≠ 32 ∧ ls.participant.toUTF8.size ≠ 8) (hst : TRStateC S g ls.state) : Census compI0 S g (Comparse.serialize ls : DY.Bytes) := by have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls; rw [hser]; exact (census_concatPrefixes _ (fun _ hp => census_mem_trStatePrefixes hpa hst hp) hst.recv hst.recvL).1
theorem aliceOut_ck_length (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : (gamma compI0 S g (iniAliceOut tr ikA ikBPk spkPk pqPk opk).keys.ck).length = 32 := by obtain ⟨ikm, hk⟩ := CompRSplit38Untagged.iniAliceOut_keys tr ikA ikBPk spkPk pqPk opk; rw [hk]; exact gamma_hmac_length S g _ _
theorem gamma_agree_length (pk sk : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.PQXDH.agree pk sk)).length = 32 := CompFreshDistinct.gamma_dh_length S g (DY.X25519.x25519Key pk) sk
theorem census_spqrA2B : Census compI0 S g DY.Libsignal.TripleRatchet.spqrA2B := census_lit_size _ (by decide) (by decide)
theorem census_spqrIdx (n : UInt32) : Census compI0 S g (DY.Spqr.spqrIdx n) := census_lit_size _ (by simp [ByteArray.size]) (by simp [ByteArray.size])
theorem census_aliceOut {r : Records} (hNe : r.alice ≠ r.bob) (tr : ExecTrace) (hent : (gamma compI0 S g (randTerm (tr.length + 1) 32)).length = 32) : let o := iniAliceOut tr (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; Census compI0 S g o.ikA ∧ Census compI0 S g o.ikB ∧ Census compI0 S g o.spk ∧ Census compI0 S g o.ek ∧ Census compI0 S g o.ct ∧
    Census compI0 S g o.keys.rk ∧ Census compI0 S g o.keys.ck ∧ Census compI0 S g o.keys.pqr := by
  dsimp only; rw [CompSetupSecrecy.setupSecret_0 hNe, CompSetupSecrecy.setupPublic_2 hNe, CompSetupSecrecy.setupPublic_4 hNe, CompSetupSecrecy.setupPublic_6 hNe]; have hsec0 := census_randTerm (i := compI0) (S := S) (g := g) 0 32; have hpub2 := census_dhPk (census_randTerm (i := compI0) (S := S) (g := g) 5 32); have hpub4 := census_dhPk (census_randTerm (i := compI0) (S := S) (g := g) 10 32); have hpub6 := census_kemPk (census_randTerm (i := compI0) (S := S) (g := g) 16 64); have hek_r := census_randTerm (i := compI0) (S := S) (g := g) tr.length 32; have hent_r := census_randTerm (i := compI0) (S := S) (g := g) (tr.length + 1) 32
  rcases census_pqxdhKdf_none (gamma_agree_length _ _) (gamma_agree_length _ _) (gamma_agree_length _ _) (gamma_kemEncap_snd_length' hent)
    (census_agree hpub4 hsec0) (census_agree hpub2 hek_r) (census_agree hpub4 hek_r) (census_kemEncap_snd hpub6 hent_r) with ⟨hrk, hck, hpqr⟩
  exact ⟨census_dhPk hsec0, hpub2, hpub4, census_dhPk hek_r, census_kemEncap_fst hpub6 hent_r, hrk, hck, hpqr⟩
theorem trStateC_iniAliceStartState (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hb : b.toUTF8.size ≠ 32 ∧ b.toUTF8.size ≠ 8) (hikA : Census compI0 S g o.ikA) (hikAL : (gamma compI0 S g o.ikA).length = 32) (hikB : Census compI0 S g o.ikB) (hikBL : (gamma compI0 S g o.ikB).length = 32) (hspk : Census compI0 S g o.spk) (hrk : Census compI0 S g o.keys.rk) (hrkL : (gamma compI0 S g o.keys.rk).length = 32) (hck : Census compI0 S g o.keys.ck) (hckL : (gamma compI0 S g o.keys.ck).length = 32) (hpqr : Census compI0 S g o.keys.pqr) : TRStateC S g (iniAliceStartState tr b o) := by
  have hdhsA : Census compI0 S g (randTerm (tr.length + 2) 32) := census_randTerm _ _; have hcc := census_createChain hrk hspk hdhsA; obtain ⟨hrecv, hrecvL⟩ := census_serialize_recv1 (i := compI0) (S := S) (g := g) hspk hck hckL
  exact ⟨hb, census_serializedIk hikAL hikA, census_serializedIk hikBL hikB, hcc.1, hdhsA, hcc.2,
    census_concat_len (by rw [CompFreshDistinct.gamma_dhPk_length S g _, hrkL]; decide) (by rw [CompFreshDistinct.gamma_dhPk_length S g _, hrkL]; decide) (census_dhPk hdhsA) hrk,
    census_spqrInit hpqr census_spqrA2B, hrecv, hrecvL⟩
theorem trStateC_encSt (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl : Nat) (hst : TRStateC S g stA) : TRStateC S g (encSt tr₂ stA cl) := ⟨hst.peer, hst.myIk, hst.peerIk, hst.rk, hst.dhs, (census_kdfCk hst.cks).1, hst.sid, census_spqrSendState hst.spqr (census_randTerm (tr₂.length + 1) cl), hst.recv, hst.recvL⟩
theorem trStateC_stA {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (tr₁ : ExecTrace) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : TRStateC S g (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) := by obtain ⟨hikA, hikB, hspk, _, _, hrk, hck, hpqr⟩ := census_aliceOut (S := S) (g := g) hNe tr₁ hent; have hikBL : (gamma compI0 S g (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ikB).length = 32 := (by change (gamma compI0 S g (setupPublic r 2)).length = 32; rw [CompSetupSecrecy.setupPublic_2 hNe]; exact CompFreshDistinct.gamma_dhPk_length S g _); exact trStateC_iniAliceStartState tr₁ r.bob _ (participant_size_ne (Or.inr hB)) hikA (CompFreshDistinct.gamma_dhPk_length S g _) hikB hikBL hspk hrk (CompRPreMemo38KdfCensus.aliceOut_rk_length tr₁ _ _ _ _ _) hck (aliceOut_ck_length tr₁ _ _ _ _ _) hpqr
theorem census_enc (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl pq : Nat) (hst : TRStateC S g stA) (hsalt : Census compI0 S g (encSalt tr₂ stA cl pq)) (hwL : 33 ≤ (gamma compI0 S g (encWire tr₂ stA cl pq)).length) : Census compI0 S g (encWire tr₂ stA cl pq) ∧ Census compI0 S g (encOut tr₂ stA cl pq) ∧ (∀ mk : DY.Bytes, Census compI0 S g mk → Census compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk stA.myIk stA.peerIk (encWire tr₂ stA cl pq))) := by
  have hmk := census_trMsgKeys hsalt (census_kdfCk hst.cks).2; have hct := census_symEnc hmk.1 hmk.2.2 (census_randTerm (S := S) (g := g) tr₂.length 32); have hpq := census_spqrSendMsg hst.spqr (census_randTerm (S := S) (g := g) (tr₂.length + 1) cl)
  have hwire : Census compI0 S g (encWire tr₂ stA cl pq) := by
    unfold encWire DY.Libsignal.TripleRatchet.trHonestWireMsg
    exact census_trWire_of_len (by change (gamma compI0 S g (encWire tr₂ stA cl pq)).length ≠ 32; omega)
      (by change (gamma compI0 S g (encWire tr₂ stA cl pq)).length ≠ 8; omega) (census_dhPk hst.dhs) hct hpq
  have hmacIn : Census compI0 S g (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl pq))) := by refine census_concat_len ?_ ?_ hst.myIk (census_concat_len ?_ ?_ hst.peerIk hwire) <;> (try simp only [gamma_concat, List.length_append]) <;> omega
  have hcmac : ∀ mk : DY.Bytes, Census compI0 S g mk → Census compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk stA.myIk stA.peerIk (encWire tr₂ stA cl pq)) :=
    fun _ hmk' => census_trunc8 (census_hmac hmk' hmacIn)
  refine ⟨hwire, census_concat_len ?_ ?_ hwire (hcmac _ hmk.2.1), hcmac⟩ <;> omega
end St
section Pre
open Symbolic.BugInjection.Proofs.Common443.CompRNoBSC (encSalt_iniAliceStartState_eq_spqrChainKey)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts (send_terms_split38_mem storedStates_split38_cases pt_terms_split38_mem)
variable {S : Sem} {g : Ghost}
theorem gamma_trWire_canonical_length_ge_33 (v : UInt8) {rk : DY.Bytes} (hrk : (gamma compI0 S g rk).length = 32) (c pc : UInt32) (ct pq : DY.Bytes) : 33 ≤ (gamma compI0 S g (DY.TrWire.trWireMsg v rk c pc ct pq DY.TrWire.canonicalVariation)).length := by rw [CompFreshDistinct.gamma_trWire_eq]; unfold trWireBytes trFields honestTrItems; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.canonicalVariation_eq]; simp only [↓reduceIte, List.flatMap_cons, List.flatMap_append, List.cons_append, List.length_cons, List.length_append, trItemEncode, DY.TrWire.FieldItem.encode, DY.Libsignal.Refinement.knownValue?, DY.Libsignal.Refinement.encodeField]; simp only [Nat.reduceEqDiff, ↓reduceIte, reduceIte, Option.map_some, Option.getD_some, List.append_nil, List.length_append, List.length_cons, hrk, DY.Libsignal.Refinement.encodeField]; omega
theorem encWire_len_ge33 (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : 33 ≤ (gamma compI0 S g (encWire tr₂ stA cl pq)).length := gamma_trWire_canonical_length_ge_33 _ (CompFreshDistinct.gamma_dhPk_length S g stA.dhs) _ _ _ _
theorem census_encSalt_stA {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (cl : Nat) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : Census compI0 S g (encSalt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2)) := by obtain ⟨_, _, _, _, _, _, _, hpqr⟩ := census_aliceOut (S := S) (g := g) hNe tr₁ hent; rw [encSalt_iniAliceStartState_eq_spqrChainKey]; exact census_spqrChainKey hpqr census_spqrA2B (census_spqrIdx _)
theorem census_encOut_stA {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (tr₁ tr₂ : ExecTrace) (cl : Nat) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : let stA := iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none); Census compI0 S g (encWire tr₂ stA cl (tr₂.length + 2)) ∧ Census compI0 S g (encOut tr₂ stA cl (tr₂.length + 2)) ∧ (∀ mk : DY.Bytes, Census compI0 S g mk → Census compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk stA.myIk stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))) := census_enc tr₂ cl _ (trStateC_stA hNe hB tr₁ hent) (census_encSalt_stA hNe tr₁ tr₂ cl hent) (encWire_len_ge33 _ _ _ _)
theorem census_prefixTerms {r : Records} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, Census compI0 S g u) (hstates : ∀ ls ∈ storedStates r tr, Census compI0 S g (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, Census compI0 S g u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, Census compI0 S g u) : ∀ u ∈ prefixTerms r tr vis, Census compI0 S g u := CompRPreMemo38KdfCensus.memoOK_prefixTerms hsend hstates hsecrets hpt
theorem census_preTerms_split38 {r : Records} (hNe : r.alice ≠ r.bob) (hA : r.alice = "alice") (hB : r.bob = "bob") {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hent : (gamma compI0 S g (randTerm ((runMoves pre (setupTrace r)).1.length + 1) 32)).length = 32) (hsec : ∀ u ∈ storedSecrets (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post)), Census compI0 S g u) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) : let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1;
    let wrap := some (tr₁.length + 3, tr₁.length + 4); let m₁' := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap; let ms' := pre ++ m₀ :: mid ++ m₁' :: post;
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), Census compI0 S g u := by
  dsimp only; let tr₁ := (runMoves pre (setupTrace r)).1; let tr₂ := (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1; have hstA : TRStateC S g (iniAliceStartState tr₁ r.bob o) := ho ▸ trStateC_stA hNe hB tr₁ hent; have ho_out := census_aliceOut (S := S) (g := g) (r := r) hNe tr₁ hent; have henc := census_encOut_stA (S := S) (g := g) hNe hB tr₁ tr₂ cl hent; refine census_prefixTerms (fun v hv hkind u hu_v => ?_) (fun ls hls => ?_) hsec (fun v hv hkind u hu_v => ?_)
  · rcases send_terms_split38_mem hNe ho hpre hmid hpost hm₀ hv hkind hu_v with rfl | rfl | rfl <;> rw [ho] <;> [exact ho_out.2.2.2.1; exact ho_out.2.2.2.2.1; exact henc.2.1]
  · rcases storedStates_split38_cases ho hpre hmid hpost hm₀ hls with hls_eq | hls_eq <;> rw [hls_eq] <;> [exact census_serialize_local_tr (participant_size_ne (Or.inl hA)) hstA; exact census_serialize_local_tr (participant_size_ne (Or.inl hA)) (trStateC_encSt tr₂ cl hstA)]
  · rw [pt_terms_split38_mem hNe ho hpre hmid hpost hm₀ hv hkind hu_v]; exact census_randTerm _ _
end Pre
section Main
open Symbolic.BugInjection.Proofs.Common443.CompRNoBSC (encSalt_iniAliceStartState_eq_spqrChainKey encMsgKeys mem_bobTerms_x0_iff honestSalts_split_eq x25519Key_torsionVariant_aliceOut_ek)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts (runTrace_split38_swap_eq isSetup_false_split38_swap)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 (encrypt_next_split38_eq)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire (split38_forall2_vis_inv aliceVis_dhs_coin)
theorem census_bobTerms_list {S : Sem} {g : Ghost} {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (tr₁ tr₂ : ExecTrace) (cl : Nat) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none;
    let stA := iniAliceStartState tr₁ r.bob o; let pq := tr₂.length + 2; let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let zkeys := DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed; let akeys := encMsgKeys tr₂ stA cl pq;
    ∀ u ∈ [o.keys.rk, o.keys.ck, o.keys.pqr, stA.cks, (encSt tr₂ stA cl).cks, akeys.cipherKey, akeys.macKey, akeys.iv, encMac tr₂ stA cl pq, randTerm tr₂.length 32,
           zkeys.cipherKey, zkeys.macKey, zkeys.iv, DY.Libsignal.TripleRatchet.computeMac zkeys.macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq)], Census compI0 S g u := by
  intro o stA pq seed zkeys akeys u hu; obtain ⟨_, _, _, _, _, hrk, hck, hpqr⟩ := census_aliceOut (S := S) (g := g) hNe tr₁ hent; have hst : TRStateC S g stA := trStateC_stA hNe hB tr₁ hent; have henc := census_encOut_stA (S := S) (g := g) hNe hB tr₁ tr₂ cl hent; have hseed : Census compI0 S g seed := (census_kdfCk hst.cks).2; have hak := census_trMsgKeys (census_encSalt_stA (S := S) (g := g) hNe tr₁ tr₂ cl hent) hseed; have hzk := census_trMsgKeys (census_zeroKey (S := S) (g := g)) hseed; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> [exact hrk; exact hck; exact hpqr; exact hst.cks; exact (trStateC_encSt tr₂ cl hst).cks;
     exact hak.1; exact hak.2.1; exact hak.2.2; exact henc.2.2 _ hak.2.1; exact census_randTerm _ _;
     exact hzk.1; exact hzk.2.1; exact hzk.2.2; exact henc.2.2 _ hzk.2.1]
end Main
end Symbolic.BugInjection.Proofs.Common443.CompC2Census38
