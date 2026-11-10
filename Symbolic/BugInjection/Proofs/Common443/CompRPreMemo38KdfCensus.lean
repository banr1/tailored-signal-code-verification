/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged
import Symbolic.DYBridge.DY.Bytes.Basic

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey (gamma_hmac_length)
open Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def KdfSalt32 (S : Sem) (g : Ghost) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := ∀ k m : DY.Bytes, x.1 = DY.KdfExtract.kdfExtract k m → (gamma compI0 S g k).length = 32
def KdfCensus (i : ExternInterpretation) (S : Sem) (g : Ghost) (t : DY.Bytes) : Prop := MemoOK i S g (KdfSalt32 S g) t
def NotKdf (b : DY.Bytes) : Prop := b.view? DY.KdfExtract.KdfExtract.SubF = none
theorem ne_kdfExtract_of_notKdf {b : DY.Bytes} (h : NotKdf b) (k m : DY.Bytes) : b ≠ DY.KdfExtract.kdfExtract k m := by rintro rfl; unfold NotKdf at h; dsimp only [DY.KdfExtract.kdfExtract, DY.KdfExtract.CanKdfExtract.kdfExtract] at h; rw [DY.BytesView.view_pack] at h; cases h
theorem kdfExtract_salt_eq {a b a' b' : DY.Bytes} (h : DY.KdfExtract.kdfExtract a b = DY.KdfExtract.kdfExtract a' b') : a = a' := (Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj h).1
section ViewNone
theorem nk_lit (bs : ByteArray) : NotKdf (DY.Literal.literalToBytes bs : DY.Bytes) :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_randTerm (idx sz : Nat) : NotKdf (randTerm idx sz) :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_concat (a c : DY.Bytes) : NotKdf (DY.Concat.concat a c) :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_dhPk (sk : DY.Bytes) : NotKdf (DY.DiffieHellman.dhPk sk) :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_dh_pack (pk sk : DY.Bytes) : NotKdf (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_symEnc (k iv m : DY.Bytes) : NotKdf (DY.SymEnc.symEnc k iv m) :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_trunc8 (a : DY.Bytes) : NotKdf (DY.Trunc.trunc8 a) :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_trWire (ver : UInt8) (rk : DY.Bytes) (c pc : UInt32) (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation) : NotKdf (DY.TrWire.trWireMsg ver rk c pc ct pq ev) :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_kemEncap_fst (pk e : DY.Bytes) : NotKdf (DY.PQKem.kemEncap pk e).1 :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
theorem nk_kemEncap_snd (pk e : DY.Bytes) : NotKdf (DY.PQKem.kemEncap pk e).2 :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
end ViewNone
section Prim
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
private theorem ks_of_nk {b : DY.Bytes} (hb : NotKdf b) : ∀ x : DY.Bytes × DY.Bytes × HwBytes, x.1 = b → KdfSalt32 S g x := by intro x hx k m hk; exact absurd (hx.symm.trans hk) (ne_kdfExtract_of_notKdf hb k m)
theorem kdfCensus_lit (bs : ByteArray) : KdfCensus i S g (DY.Literal.literalToBytes bs) := memoOK_lit (ks_of_nk (nk_lit bs))
theorem kdfCensus_randTerm (idx sz : Nat) : KdfCensus i S g (randTerm idx sz) := by
  intro x hx; unfold gamma' randTerm at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx
  split_ifs at hx with hsz
  · cases hx
  · rcases List.mem_singleton.mp hx with rfl
    exact ks_of_nk (nk_randTerm idx sz) _ rfl
theorem kdfCensus_concat {a c : DY.Bytes} (ha : KdfCensus i S g a) (hc : KdfCensus i S g c) : KdfCensus i S g (DY.Concat.concat a c) := memoOK_concat (ks_of_nk (nk_concat a c)) ha hc
theorem kdfCensus_dhPk {sk : DY.Bytes} (hsk : KdfCensus i S g sk) : KdfCensus i S g (DY.DiffieHellman.dhPk sk) := memoOK_dhPk (ks_of_nk (nk_dhPk sk)) hsk
theorem kdfCensus_of_dhPk {sk : DY.Bytes} (h : KdfCensus i S g (DY.DiffieHellman.dhPk sk)) : KdfCensus i S g sk := memoOK_dhPk_elim h
theorem kdfCensus_dh_pack {pk sk : DY.Bytes} (hpk : KdfCensus i S g pk) (hsk : KdfCensus i S g sk) : KdfCensus i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := memoOK_dh_pack (ks_of_nk (nk_dh_pack pk sk)) hpk hsk
theorem kdfCensus_dh {pk sk : DY.Bytes} (hpk : KdfCensus i S g pk) (hsk : KdfCensus i S g sk) : KdfCensus i S g (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv; have hsk2 : KdfCensus i S g sk2 := kdfCensus_of_dhPk hpk
    split
    · exact kdfCensus_dh_pack hpk hsk
    · exact kdfCensus_dh_pack (kdfCensus_dhPk hsk) hsk2
  · exact kdfCensus_dh_pack hpk hsk
theorem kdfCensus_kdfExtract {a b : DY.Bytes} (haL : (gamma compI0 S g a).length = 32) (ha : KdfCensus i S g a) (hb : KdfCensus i S g b) : KdfCensus i S g (DY.KdfExtract.kdfExtract a b) := by refine memoOK_kdfExtract ?_ ha hb; intro x hx k m hk; rw [← kdfExtract_salt_eq (hx.symm.trans hk)]; exact haL
theorem kdfCensus_hmac {a b : DY.Bytes} (haL : (gamma compI0 S g a).length = 32) (ha : KdfCensus i S g a) (hb : KdfCensus i S g b) : KdfCensus i S g (DY.Libsignal.TripleRatchet.hmac a b) := kdfCensus_kdfExtract haL ha hb
theorem kdfCensus_hkdfBlock1 {prk info : DY.Bytes} (hL : (gamma compI0 S g prk).length = 32) (hprk : KdfCensus i S g prk) (hinfo : KdfCensus i S g info) : KdfCensus i S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := kdfCensus_hmac hL hprk (kdfCensus_concat hinfo (kdfCensus_lit _))
theorem kdfCensus_hkdfBlock2 {prk info : DY.Bytes} (hL : (gamma compI0 S g prk).length = 32) (hprk : KdfCensus i S g prk) (hinfo : KdfCensus i S g info) : KdfCensus i S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := kdfCensus_hmac hL hprk (kdfCensus_concat (kdfCensus_hkdfBlock1 hL hprk hinfo) (kdfCensus_concat hinfo (kdfCensus_lit _)))
theorem kdfCensus_hkdfBlock3 {prk info : DY.Bytes} (hL : (gamma compI0 S g prk).length = 32) (hprk : KdfCensus i S g prk) (hinfo : KdfCensus i S g info) : KdfCensus i S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := kdfCensus_hmac hL hprk (kdfCensus_concat (kdfCensus_hkdfBlock2 hL hprk hinfo) (kdfCensus_concat hinfo (kdfCensus_lit _)))
theorem kdfCensus_symEnc {k iv m : DY.Bytes} (hk : KdfCensus i S g k) (hiv : KdfCensus i S g iv) (hm : KdfCensus i S g m) : KdfCensus i S g (DY.SymEnc.symEnc k iv m) := memoOK_symEnc (ks_of_nk (nk_symEnc k iv m)) hk hiv hm
theorem kdfCensus_trunc8 {a : DY.Bytes} (ha : KdfCensus i S g a) : KdfCensus i S g (DY.Trunc.trunc8 a) := memoOK_trunc8 (ks_of_nk (nk_trunc8 a)) ha
theorem kdfCensus_trWire {ver : UInt8} {rk ct pq : DY.Bytes} {c pc : UInt32} {ev : DY.TrWire.EncodingVariation} (hrk : KdfCensus i S g rk) (hct : KdfCensus i S g ct) (hpq : KdfCensus i S g pq) : KdfCensus i S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev) := by rw [show DY.TrWire.trWireMsg ver rk c pc ct pq ev = ({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack from rfl]; exact memoOK_trWire (ks_of_nk (nk_trWire ver rk c pc ct pq ev)) hrk hct hpq
theorem kdfCensus_kemPk {sk : DY.Bytes} (hsk : KdfCensus i S g sk) : KdfCensus i S g (DY.PQKem.kemPk sk) := memoOK_kemPk hsk
theorem kdfCensus_kemEncap_fst {pk e : DY.Bytes} (hpk : KdfCensus i S g pk) (he : KdfCensus i S g e) : KdfCensus i S g (DY.PQKem.kemEncap pk e).1 := memoOK_kemEncap_fst (ks_of_nk (nk_kemEncap_fst pk e)) hpk he
theorem kdfCensus_kemEncap_snd {pk e : DY.Bytes} (hpk : KdfCensus i S g pk) (he : KdfCensus i S g e) : KdfCensus i S g (DY.PQKem.kemEncap pk e).2 := memoOK_kemEncap_snd (ks_of_nk (nk_kemEncap_snd pk e)) hpk he
theorem kdfCensus_spqrInit {a p : DY.Bytes} (ha : KdfCensus i S g a) (hp : KdfCensus i S g p) : KdfCensus i S g (DY.Spqr.spqrInit a p) := memoOK_spqrInit ha hp
theorem kdfCensus_spqrChainKey {a p idx : DY.Bytes} (ha : KdfCensus i S g a) (hp : KdfCensus i S g p) (hidx : KdfCensus i S g idx) : KdfCensus i S g (DY.Spqr.spqrChainKey a p idx) := memoOK_spqrChainKey ha hp hidx
theorem kdfCensus_spqrSendState {st c : DY.Bytes} (hst : KdfCensus i S g st) (hc : KdfCensus i S g c) : KdfCensus i S g (DY.Spqr.spqrSend st c).1 := memoOK_spqrSendState hst hc
theorem kdfCensus_spqrSendMsg {st c : DY.Bytes} (hst : KdfCensus i S g st) (hc : KdfCensus i S g c) : KdfCensus i S g (DY.Spqr.spqrSend st c).2.2 := memoOK_spqrSendMsg hst hc
theorem kdfCensus_x25519Key {pk : DY.Bytes} (h : KdfCensus i S g pk) : KdfCensus i S g (DY.X25519.x25519Key pk) := memoOK_x25519Key h
theorem kdfCensus_agree {pk sk : DY.Bytes} (hpk : KdfCensus i S g pk) (hsk : KdfCensus i S g sk) : KdfCensus i S g (DY.Libsignal.PQXDH.agree pk sk) := by unfold DY.Libsignal.PQXDH.agree; exact kdfCensus_dh (kdfCensus_x25519Key hpk) hsk
theorem kdfCensus_createChain {rk pk sk : DY.Bytes} (hrkL : (gamma compI0 S g rk).length = 32) (hrk : KdfCensus i S g rk) (hpk : KdfCensus i S g pk) (hsk : KdfCensus i S g sk) : KdfCensus i S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧ KdfCensus i S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by have hprk : KdfCensus i S g (DY.Libsignal.TripleRatchet.hmac rk (DY.Libsignal.PQXDH.agree pk sk)) := kdfCensus_hmac hrkL hrk (kdfCensus_agree hpk hsk); have hL := gamma_hmac_length S g rk (DY.Libsignal.PQXDH.agree pk sk); have hinfo : KdfCensus i S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := kdfCensus_lit _; exact ⟨kdfCensus_hkdfBlock1 hL hprk hinfo, kdfCensus_hkdfBlock2 hL hprk hinfo⟩
theorem kdfCensus_kdfCk {ck : DY.Bytes} (hckL : (gamma compI0 S g ck).length = 32) (hck : KdfCensus i S g ck) : KdfCensus i S g (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∧ KdfCensus i S g (DY.Libsignal.TripleRatchet.kdfCk ck).2 := ⟨kdfCensus_hmac hckL hck (kdfCensus_lit _), kdfCensus_hmac hckL hck (kdfCensus_lit _)⟩
theorem kdfCensus_trMsgKeys {salt ck : DY.Bytes} (hsaltL : (gamma compI0 S g salt).length = 32) (hckL : (gamma compI0 S g ck).length = 32) (hsalt : KdfCensus i S g salt) (hck : KdfCensus i S g ck) : let seed := (DY.Libsignal.TripleRatchet.kdfCk ck).2;
    let mk := DY.Libsignal.TripleRatchet.trMsgKeys salt seed;
    KdfCensus i S g mk.cipherKey ∧ KdfCensus i S g mk.macKey ∧ KdfCensus i S g mk.iv := by
  have hprk : KdfCensus i S g
      (DY.Libsignal.TripleRatchet.hmac salt (DY.Libsignal.TripleRatchet.kdfCk ck).2) :=
    kdfCensus_hmac hsaltL hsalt (kdfCensus_kdfCk hckL hck).2
  have hL := gamma_hmac_length S g salt (DY.Libsignal.TripleRatchet.kdfCk ck).2; have hinfo : KdfCensus i S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") := kdfCensus_lit _; exact ⟨kdfCensus_hkdfBlock1 hL hprk hinfo, kdfCensus_hkdfBlock2 hL hprk hinfo, kdfCensus_hkdfBlock3 hL hprk hinfo⟩
theorem kdfCensus_computeMac_trWire {mk ikS ikR : DY.Bytes} {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation} (hmkL : (gamma compI0 S g mk).length = 32) (hmk : KdfCensus i S g mk) (hikS : KdfCensus i S g ikS) (hikR : KdfCensus i S g ikR) (hrk : KdfCensus i S g rk) (hct : KdfCensus i S g ct) (hpq : KdfCensus i S g pq) : KdfCensus i S g (DY.Libsignal.TripleRatchet.computeMac mk ikS ikR (DY.TrWire.trWireMsg v rk c pc ct pq ev)) := by unfold DY.Libsignal.TripleRatchet.computeMac; exact kdfCensus_trunc8 (kdfCensus_hmac hmkL hmk (kdfCensus_concat hikS (kdfCensus_concat hikR (kdfCensus_trWire hrk hct hpq))))
theorem kdfCensus_serializedIk {ik : DY.Bytes} (hik : KdfCensus i S g ik) : KdfCensus i S g (DY.Libsignal.PQXDH.serializedIk ik) := kdfCensus_concat (kdfCensus_lit _) hik
theorem kdfCensus_pqxdhKdf_none {dh1 dh2 dh3 ss : DY.Bytes} (hdh1 : KdfCensus i S g dh1) (hdh2 : KdfCensus i S g dh2) (hdh3 : KdfCensus i S g dh3) (hss : KdfCensus i S g ss) : let keys := DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss);
    KdfCensus i S g keys.rk ∧ KdfCensus i S g keys.ck ∧ KdfCensus i S g keys.pqr := by
  have hprk : KdfCensus i S g
      (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss)) :=
    kdfCensus_hmac (CompRSplit38Untagged.gamma_zeroSalt_length S g) (kdfCensus_lit _) (kdfCensus_concat (kdfCensus_lit _) (kdfCensus_concat hdh1 (kdfCensus_concat hdh2 (kdfCensus_concat hdh3 hss))))
  have hL := gamma_hmac_length S g DY.Libsignal.TripleRatchet.zeroSalt
    (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss)
  have hinfo : KdfCensus i S g DY.Libsignal.PQXDH.pqxdhLabel := kdfCensus_lit _; exact ⟨kdfCensus_hkdfBlock1 hL hprk hinfo, kdfCensus_hkdfBlock2 hL hprk hinfo, kdfCensus_hkdfBlock3 hL hprk hinfo⟩
theorem memoOK_concatPrefixes {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hconcat : ∀ {a c}, MemoOK i S g P a → MemoOK i S g P c → MemoOK i S g P (DY.Concat.concat a c)) : ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, MemoOK i S g P p) → MemoOK i S g P s → MemoOK i S g P (Comparse.concatPrefixes ps s)
  | [], _, _, hs => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact hs
  | p :: ps, _s, hps, hs => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    exact hconcat (hps p (List.mem_cons_self ..)) (memoOK_concatPrefixes hconcat ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs)
theorem memoOK_mem_bool {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) (b : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize b) : MemoOK i S g P p := by
  obtain ⟨ba, _, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton b
  rw [hser] at hp
  rcases List.mem_singleton.mp hp with rfl
  exact hlit ba
theorem memoOK_mem_slowNat {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) : ∀ (n : Nat) {p : DY.Bytes}, p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n → MemoOK i S g P p
  | 0, _, hp => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero] at hp
    exact memoOK_mem_bool hlit false hp
  | n + 1, _, hp => by
    have hstep := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n
    rw [hstep, List.mem_append] at hp; exact hp.elim (memoOK_mem_bool hlit true) (memoOK_mem_slowNat hlit n)
theorem memoOK_mem_uint32 {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) (n : UInt32) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize n) : MemoOK i S g P p := by
  obtain ⟨ba, _, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.uint32_serialize_singleton n
  rw [hser] at hp
  rcases List.mem_singleton.mp hp with rfl
  exact hlit ba
theorem memoOK_mem_slowBytes {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) {b : DY.Bytes} (hb : MemoOK i S g P b) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize b) : MemoOK i S g P p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq b
  rw [hser, List.mem_append, List.mem_singleton] at hp
  exact hp.elim (memoOK_mem_slowNat hlit _) (· ▸ hb)
theorem memoOK_mem_slowString {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) (s : String) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : MemoOK i S g P p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s
  rw [hser, List.mem_append, List.mem_singleton] at hp
  rcases hp with hnat | rfl
  · exact memoOK_mem_slowNat hlit _ hnat
  · exact hlit _
theorem memoOK_mem_serialize_recvChain {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) {d : DY.Libsignal.TripleRatchet.RecvChain} (hrk : MemoOK i S g P d.ratchetKey) (hck : MemoOK i S g P d.chainKey) {p : DY.Bytes} (hp : p ∈ (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d) : MemoOK i S g P p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq d
  rw [hser] at hp; simp only [List.mem_append] at hp
  rcases hp with h1 | h2 | h3 | h4
  · exact memoOK_mem_slowBytes hlit hrk h1
  · exact memoOK_mem_slowBytes hlit hck h2
  · exact memoOK_mem_uint32 hlit d.index h3
  · exact memoOK_mem_slowNat hlit d.rIdx h4
theorem memoOK_serialize_recvList {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) (hconcat : ∀ {a c}, MemoOK i S g P a → MemoOK i S g P c → MemoOK i S g P (DY.Concat.concat a c)) : ∀ {cs : List DY.Libsignal.TripleRatchet.RecvChain}, (∀ d ∈ cs, MemoOK i S g P d.ratchetKey ∧ MemoOK i S g P d.chainKey) → MemoOK i S g P ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize cs)
  | [], _ => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_nil]
    exact hlit .empty
  | d :: _, hcs => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons]
    have hd := hcs d List.mem_cons_self
    exact memoOK_concatPrefixes hconcat _ (fun _ hp => memoOK_mem_serialize_recvChain hlit hd.1 hd.2 hp)
      (memoOK_serialize_recvList hlit hconcat (fun d' hd' => hcs d' (List.mem_cons_of_mem d hd')))
theorem memoOK_serialize_local_pqxdh {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) (hconcat : ∀ {a c}, MemoOK i S g P a → MemoOK i S g P c → MemoOK i S g P (DY.Concat.concat a c)) {ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState} (hsk : MemoOK i S g P ls.state.sk) : MemoOK i S g P (Comparse.serialize ls : DY.Bytes) := by
  rw [serialize_local_pqxdh_eq]; refine memoOK_concatPrefixes hconcat _ (fun p hp => ?_) hsk; simp only [List.mem_append] at hp
  rcases hp with h1 | h2 | h3
  · exact memoOK_mem_slowString hlit _ h1
  · exact memoOK_mem_bool hlit _ h2
  · exact memoOK_mem_bool hlit _ h3
theorem memoOK_storedSecrets_of_reachable {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) (hconcat : ∀ {a c}, MemoOK i S g P a → MemoOK i S g P c → MemoOK i S g P (DY.Concat.concat a c)) (hrand : ∀ idx sz, MemoOK i S g P (randTerm idx sz)) {tr : ExecTrace} (hreach : tr.Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets tr, MemoOK i S g P u := by have hinv := CompInv.spqrInv_of_reachable tr hreach; intro u hu; obtain ⟨j, _, ls, hat, rfl⟩ := mem_storedSecrets_iff.mp hu; have hkind : CompInv.KindOK tr ls.participant ls.state := hinv.stOK ls.participant ls.state j hat; obtain ⟨idx, sz, hsk⟩ := exists_randTerm_of_kindOK hkind; refine memoOK_serialize_local_pqxdh hlit hconcat ?_; rw [hsk]; exact hrand idx sz
theorem kdfCensus_storedSecrets_of_reachable {tr : ExecTrace} (hreach : tr.Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets tr, KdfCensus i S g u := memoOK_storedSecrets_of_reachable kdfCensus_lit kdfCensus_concat kdfCensus_randTerm hreach
end Prim
structure TRStateMemoOK (i : ExternInterpretation) (S : Sem) (g : Ghost) (P : DY.Bytes × DY.Bytes × HwBytes → Prop)
    (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  myIk : MemoOK i S g P st.myIk
  peerIk : MemoOK i S g P st.peerIk
  rk : MemoOK i S g P st.rk
  dhs : MemoOK i S g P st.dhs
  cks : MemoOK i S g P st.cks
  sid : MemoOK i S g P st.sid
  spqr : MemoOK i S g P st.spqr
  recv : ∀ d ∈ st.recv, MemoOK i S g P d.ratchetKey ∧ MemoOK i S g P d.chainKey
structure TRStateKC (i : ExternInterpretation) (S : Sem) (g : Ghost)
    (st : DY.Libsignal.TripleRatchet.TRState) : Prop extends TRStateMemoOK i S g (KdfSalt32 S g) st where
  cksL : (gamma compI0 S g st.cks).length = 32
section TR
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem memoOK_mem_trStatePrefixes {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hst : TRStateMemoOK i S g P ls.state) {p : DY.Bytes} (hp : p ∈ trStatePrefixes ls) : MemoOK i S g P p := by
  unfold trStatePrefixes at hp; simp only [List.mem_append] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h
  exacts [memoOK_mem_slowString hlit _ h, memoOK_mem_slowString hlit _ h, memoOK_mem_slowBytes hlit hst.myIk h, memoOK_mem_slowBytes hlit hst.peerIk h, memoOK_mem_slowBytes hlit hst.rk h, memoOK_mem_slowBytes hlit hst.dhs h, memoOK_mem_slowBytes hlit hst.cks h, memoOK_mem_uint32 hlit _ h, memoOK_mem_uint32 hlit _ h, memoOK_mem_slowBytes hlit hst.sid h, memoOK_mem_bool hlit _ h, memoOK_mem_slowNat hlit _ h, memoOK_mem_slowBytes hlit hst.spqr h]
theorem memoOK_serialize_local_tr {P : DY.Bytes × DY.Bytes × HwBytes → Prop} (hlit : ∀ bs, MemoOK i S g P (DY.Literal.literalToBytes bs)) (hconcat : ∀ {a c}, MemoOK i S g P a → MemoOK i S g P c → MemoOK i S g P (DY.Concat.concat a c)) {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hst : TRStateMemoOK i S g P ls.state) : MemoOK i S g P (Comparse.serialize ls : DY.Bytes) := by
  have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (trStatePrefixes ls)
        ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize
          ls.state.recv) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls
  rw [hser]; exact memoOK_concatPrefixes hconcat _ (fun _ hp => memoOK_mem_trStatePrefixes hlit hst hp) (memoOK_serialize_recvList hlit hconcat hst.recv)
theorem memoOK_prefixTerms {P : DY.Bytes × DY.Bytes × HwBytes → Prop} {r : Records} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, MemoOK i S g P u) (hstates : ∀ ls ∈ storedStates r tr, MemoOK i S g P (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, MemoOK i S g P u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, MemoOK i S g P u) : ∀ u ∈ prefixTerms r tr vis, MemoOK i S g P u := by
  intro u hu; unfold prefixTerms principalTerms plaintextTerms at hu; simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq] at hu
  rcases hu with ((⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩ | ⟨ls, hls, rfl⟩) | hsec) | ⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩
  · exact hsend v hv_mem hv_kind u hu_v
  · exact hstates ls hls
  · exact hsecrets u hsec
  · exact hpt v hv_mem hv_kind u hu_v
theorem kdfCensus_serialize_local_tr {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hst : TRStateKC i S g ls.state) : KdfCensus i S g (Comparse.serialize ls : DY.Bytes) := memoOK_serialize_local_tr kdfCensus_lit kdfCensus_concat hst.toTRStateMemoOK
theorem kdfCensus_prefixTerms {r : Records} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, KdfCensus i S g u) (hstates : ∀ ls ∈ storedStates r tr, KdfCensus i S g (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, KdfCensus i S g u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, KdfCensus i S g u) : ∀ u ∈ prefixTerms r tr vis, KdfCensus i S g u := memoOK_prefixTerms hsend hstates hsecrets hpt
theorem trStateKC_iniAliceStartState (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hikA : KdfCensus i S g o.ikA) (hikB : KdfCensus i S g o.ikB) (hspk : KdfCensus i S g o.spk) (hrkL : (gamma compI0 S g o.keys.rk).length = 32) (hrk : KdfCensus i S g o.keys.rk) (hck : KdfCensus i S g o.keys.ck) (hpqr : KdfCensus i S g o.keys.pqr) : TRStateKC i S g (iniAliceStartState tr b o) := by
  have hdhsA : KdfCensus i S g (randTerm (tr.length + 2) 32) := kdfCensus_randTerm _ _; have hcc := kdfCensus_createChain hrkL hrk hspk hdhsA
  refine { myIk := kdfCensus_serializedIk hikA, peerIk := kdfCensus_serializedIk hikB, rk := hcc.1, dhs := hdhsA, cks := hcc.2, sid := kdfCensus_concat (kdfCensus_dhPk hdhsA) hrk, spqr := kdfCensus_spqrInit hpqr (kdfCensus_lit _), recv := (fun d hd => by simp only [iniAliceStartState, List.mem_singleton] at hd; subst hd; exact ⟨hspk, hck⟩), cksL := CompRSplit38Untagged.gamma_createChain_snd_length S g _ _ _ }
theorem trStateKC_encSt (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl : Nat) (hst : TRStateKC i S g stA) : TRStateKC i S g (encSt tr₂ stA cl) :=
  { hst with cks := (kdfCensus_kdfCk hst.cksL hst.cks).1, spqr := kdfCensus_spqrSendState hst.spqr (kdfCensus_randTerm _ _), cksL := gamma_hmac_length S g _ _ }
theorem kdfCensus_encOut (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl pqIdx : Nat) (hst : TRStateKC i S g stA) (hsaltL : (gamma compI0 S g (encSalt tr₂ stA cl pqIdx)).length = 32) (hsalt : KdfCensus i S g (encSalt tr₂ stA cl pqIdx)) : KdfCensus i S g (encOut tr₂ stA cl pqIdx) := by
  dsimp only [encOut, encWire, encMac, DY.Libsignal.TripleRatchet.trHonestWireMsg]; have hmk := kdfCensus_trMsgKeys hsaltL hst.cksL hsalt hst.cks; have hpt : KdfCensus i S g (randTerm tr₂.length 32) := kdfCensus_randTerm _ _; have hct := kdfCensus_symEnc hmk.1 hmk.2.2 hpt; have hdhsPk := kdfCensus_dhPk hst.dhs
  have hpqMsg := kdfCensus_spqrSendMsg hst.spqr
    (kdfCensus_randTerm (i := i) (S := S) (g := g) (tr₂.length + 1) cl)
  exact kdfCensus_concat (kdfCensus_trWire hdhsPk hct hpqMsg) (kdfCensus_computeMac_trWire (gamma_hmac_length S g _ _) hmk.2.1 hst.myIk hst.peerIk hdhsPk hct hpqMsg)
theorem kdfCensus_aliceOut {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) : let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; KdfCensus i S g o.ikA ∧ KdfCensus i S g o.ikB ∧ KdfCensus i S g o.spk ∧ KdfCensus i S g o.ek ∧ KdfCensus i S g o.ct ∧
      KdfCensus i S g o.keys.rk ∧ KdfCensus i S g o.keys.ck ∧ KdfCensus i S g o.keys.pqr := by
  dsimp only; rw [CompSetupSecrecy.setupSecret_0 hNe, CompSetupSecrecy.setupPublic_2 hNe, CompSetupSecrecy.setupPublic_4 hNe, CompSetupSecrecy.setupPublic_6 hNe]; have hsec0 : KdfCensus i S g (randTerm 0 32) := kdfCensus_randTerm _ _; have hpub2 : KdfCensus i S g (DY.DiffieHellman.dhPk (randTerm 5 32)) := kdfCensus_dhPk (kdfCensus_randTerm _ _); have hpub4 : KdfCensus i S g (DY.DiffieHellman.dhPk (randTerm 10 32)) := kdfCensus_dhPk (kdfCensus_randTerm _ _); have hpub6 : KdfCensus i S g (DY.PQKem.kemPk (randTerm 16 64)) := kdfCensus_kemPk (kdfCensus_randTerm _ _); have hek_r : KdfCensus i S g (randTerm tr₁.length 32) := kdfCensus_randTerm _ _; have hent_r : KdfCensus i S g (randTerm (tr₁.length + 1) 32) := kdfCensus_randTerm _ _
  rcases kdfCensus_pqxdhKdf_none (kdfCensus_agree hpub4 hsec0) (kdfCensus_agree hpub2 hek_r)
    (kdfCensus_agree hpub4 hek_r) (kdfCensus_kemEncap_snd hpub6 hent_r) with ⟨hrk, hck, hpqr⟩
  exact ⟨kdfCensus_dhPk hsec0, hpub2, hpub4, kdfCensus_dhPk hek_r, kdfCensus_kemEncap_fst hpub6 hent_r, hrk, hck, hpqr⟩
theorem aliceOut_rk_length (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : (gamma compI0 S g (iniAliceOut tr ikA ikBPk spkPk pqPk opk).keys.rk).length = 32 := by obtain ⟨ikm, hk⟩ := CompRSplit38Untagged.iniAliceOut_keys tr ikA ikBPk spkPk pqPk opk; rw [hk]; exact CompRSplit38Untagged.gamma_pqxdh_rk_length S g ikm
end TR
section Split38
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem gamma_spqrChainKey_length (a p idx : DY.Bytes) : (gamma compI0 S g (DY.Spqr.spqrChainKey a p idx)).length = 32 := by
  have h : gamma compI0 S g (DY.Spqr.spqrChainKey a p idx) =
      spqrKeyBytes (S.chainKey (gamma compI0 S g a) (gamma compI0 S g p) (gamma compI0 S g idx)) := by
    unfold gamma gamma'
    show ((({authKey := a, params := p, idx := idx} : DY.Spqr.ChainKey.SubF DY.Bytes).pack).rec (gAll compI0 S g)).val = _
    rw [DY.Bytes.rec_eq (gSpqrChainKey S) (gAll compI0 S g)]; rfl
  rw [h]; unfold spqrKeyBytes; simp only [List.length_take, List.length_append, List.length_replicate]; omega
theorem trStateKC_stA_split38 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) : TRStateKC i S g (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) := by obtain ⟨hikA, hikB, hspk, _, _, hrk, hck, hpqr⟩ := kdfCensus_aliceOut (i := i) (S := S) (g := g) hNe tr₁; exact trStateKC_iniAliceStartState tr₁ r.bob _ hikA hikB hspk (aliceOut_rk_length _ _ _ _ _ _) hrk hck hpqr
theorem kdfCensus_encOut_split38 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (cl : Nat) : KdfCensus i S g (encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2)) := by
  obtain ⟨_, _, _, _, _, _, _, hpqr⟩ := kdfCensus_aliceOut (i := i) (S := S) (g := g) hNe tr₁; refine kdfCensus_encOut tr₂ cl _ (trStateKC_stA_split38 hNe tr₁) ?_ ?_
  · rw [encSalt_iniAliceStartState_eq_spqrChainKey]; exact gamma_spqrChainKey_length _ _ _
  · rw [encSalt_iniAliceStartState_eq_spqrChainKey]; exact kdfCensus_spqrChainKey hpqr (kdfCensus_lit _) (kdfCensus_lit _)
theorem kdfCensus_preTerms_split38 {r : Records} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hreach : (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post)).Reachable reachability) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let wrap := some (tr₁.length + 3, tr₁.length + 4); let m₁' := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap; let ms' := pre ++ m₀ :: mid ++ m₁' :: post;
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), KdfCensus i S g u := by
  dsimp only; let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
  have hstA : TRStateKC i S g stA := by dsimp only [stA]; rw [ho]; exact trStateKC_stA_split38 hNe tr₁
  have ho_out := kdfCensus_aliceOut (i := i) (S := S) (g := g) (r := r) hNe tr₁
  have henc_out : KdfCensus i S g (encOut tr₂ stA cl (tr₂.length + 2)) := by dsimp only [stA]; rw [ho]; exact kdfCensus_encOut_split38 hNe tr₁ tr₂ cl
  refine kdfCensus_prefixTerms ?_ ?_ (kdfCensus_storedSecrets_of_reachable hreach) ?_
  · intro v hv hkind u hu_v
    rcases send_terms_split38_mem hNe ho hpre hmid hpost hm₀ hv hkind hu_v with rfl | rfl | rfl
    · rw [ho]; exact ho_out.2.2.2.1
    · rw [ho]; exact ho_out.2.2.2.2.1
    · exact henc_out
  · intro ls hls
    rcases storedStates_split38_cases ho hpre hmid hpost hm₀ hls with hls_eq | hls_eq
    · rw [hls_eq]; exact kdfCensus_serialize_local_tr hstA
    · rw [hls_eq]; exact kdfCensus_serialize_local_tr (trStateKC_encSt tr₂ cl hstA)
  · intro v hv hkind u hu_v; rw [pt_terms_split38_mem hNe ho hpre hmid hpost hm₀ hv hkind hu_v]; exact kdfCensus_randTerm _ _
theorem kdfSalt32_preMemo_split38_of_modelRun {r : Records} (hNe : r.alice ≠ r.bob) (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    ModelRun r ms → MovesFrom InvisibleNoEffect (setupTrace r) pre →
    MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
    MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
    m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
    ∀ x ∈ (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap (fun u => (gamma' i S g u).memo),
      KdfSalt32 S g x := by
  intro tr₁ o m₀ tr₂ pq ms ms' hmr hpre hmid hpost hm₀
  have htr_eq : runTraceMoves r ms = runTraceMoves r ms' := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl pq
      (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  have hreach' : (runTraceMoves r ms').Reachable reachability := htr_eq ▸ hmr.2.2.1.1; have h := kdfCensus_preTerms_split38 (i := i) (S := S) (g := g) hNe rfl hreach' hpre hmid hpost hm₀; dsimp only at h ⊢; intro x hx; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx; exact h u hu x hxu
end Split38
end Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus
