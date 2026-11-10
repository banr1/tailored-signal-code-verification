/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38Pre
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRMemoKnown CompRNoBSC CompRVariantFree38 CompRPreMemo38KdfCensus Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def KdfP (P : DY.Bytes → Prop) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := ∀ k m : DY.Bytes, x.1 = DY.KdfExtract.kdfExtract k m → P x.1
def KC (S : Sem) (g : Ghost) (P : DY.Bytes → Prop) (t : DY.Bytes) : Prop := MemoOK compI0 S g (KdfP P) t
section Prim
variable {S : Sem} {g : Ghost} {P : DY.Bytes → Prop}
private theorem kp_of_nk {b : DY.Bytes} (hb : NotKdf b) : ∀ x : DY.Bytes × DY.Bytes × HwBytes, x.1 = b → KdfP P x :=
  fun _ hx k m hk => absurd (hx.symm.trans hk) (ne_kdfExtract_of_notKdf hb k m)
theorem kc_lit (bs : ByteArray) : KC S g P (DY.Literal.literalToBytes bs) := memoOK_lit (kp_of_nk (nk_lit bs))
theorem kc_randTerm (idx sz : Nat) : KC S g P (randTerm idx sz) := by
  intro x hx; unfold gamma' randTerm at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll compI0 S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx
  split_ifs at hx with hsz; · cases hx
  rcases List.mem_singleton.mp hx with rfl; exact kp_of_nk (nk_randTerm idx sz) _ rfl
theorem kc_concat {a c : DY.Bytes} (ha : KC S g P a) (hc : KC S g P c) : KC S g P (DY.Concat.concat a c) := memoOK_concat (kp_of_nk (nk_concat a c)) ha hc
theorem kc_dhPk {sk : DY.Bytes} (hsk : KC S g P sk) : KC S g P (DY.DiffieHellman.dhPk sk) := memoOK_dhPk (kp_of_nk (nk_dhPk sk)) hsk
theorem kc_of_dhPk {sk : DY.Bytes} (h : KC S g P (DY.DiffieHellman.dhPk sk)) : KC S g P sk := memoOK_dhPk_elim h
theorem kc_dh_pack {pk sk : DY.Bytes} (hpk : KC S g P pk) (hsk : KC S g P sk) : KC S g P (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) := memoOK_dh_pack (kp_of_nk (nk_dh_pack pk sk)) hpk hsk
theorem kc_dh {pk sk : DY.Bytes} (hpk : KC S g P pk) (hsk : KC S g P sk) : KC S g P (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    split <;> [exact kc_dh_pack hpk hsk; exact kc_dh_pack (kc_dhPk hsk) (kc_of_dhPk hpk)]
  · exact kc_dh_pack hpk hsk
theorem kc_kdfExtract {a b : DY.Bytes} (hP : P (DY.KdfExtract.kdfExtract a b)) (ha : KC S g P a) (hb : KC S g P b) : KC S g P (DY.KdfExtract.kdfExtract a b) :=
  memoOK_kdfExtract (fun _ hx _ _ _ => hx ▸ hP) ha hb
theorem kc_hkdfBlock1 {prk info : DY.Bytes} (h1 : P (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info)) (hprk : KC S g P prk) (hinfo : KC S g P info) : KC S g P (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := kc_kdfExtract h1 hprk (kc_concat hinfo (kc_lit _))
theorem kc_hkdfBlock2 {prk info : DY.Bytes} (h1 : P (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info)) (h2 : P (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info)) (hprk : KC S g P prk) (hinfo : KC S g P info) : KC S g P (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := kc_kdfExtract h2 hprk (kc_concat (kc_hkdfBlock1 h1 hprk hinfo) (kc_concat hinfo (kc_lit _)))
theorem kc_hkdfBlock3 {prk info : DY.Bytes} (h1 : P (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info)) (h2 : P (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info)) (h3 : P (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info)) (hprk : KC S g P prk) (hinfo : KC S g P info) : KC S g P (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := kc_kdfExtract h3 hprk (kc_concat (kc_hkdfBlock2 h1 h2 hprk hinfo) (kc_concat hinfo (kc_lit _)))
theorem kc_symEnc {k iv m : DY.Bytes} (hk : KC S g P k) (hiv : KC S g P iv) (hm : KC S g P m) : KC S g P (DY.SymEnc.symEnc k iv m) := memoOK_symEnc (kp_of_nk (nk_symEnc k iv m)) hk hiv hm
theorem kc_trunc8 {a : DY.Bytes} (ha : KC S g P a) : KC S g P (DY.Trunc.trunc8 a) := memoOK_trunc8 (kp_of_nk (nk_trunc8 a)) ha
theorem kc_trWire {ver : UInt8} {rk ct pq : DY.Bytes} {c pc : UInt32} {ev : DY.TrWire.EncodingVariation} (hrk : KC S g P rk) (hct : KC S g P ct) (hpq : KC S g P pq) : KC S g P (DY.TrWire.trWireMsg ver rk c pc ct pq ev) := by rw [show DY.TrWire.trWireMsg ver rk c pc ct pq ev = ({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : DY.TrWire.TrWireMsg.SubF DY.Bytes).pack from rfl]; exact memoOK_trWire (kp_of_nk (nk_trWire ver rk c pc ct pq ev)) hrk hct hpq
theorem kc_kemPk {sk : DY.Bytes} (hsk : KC S g P sk) : KC S g P (DY.PQKem.kemPk sk) := memoOK_kemPk hsk
theorem kc_kemEncap_fst {pk e : DY.Bytes} (hpk : KC S g P pk) (he : KC S g P e) : KC S g P (DY.PQKem.kemEncap pk e).1 := memoOK_kemEncap_fst (kp_of_nk (nk_kemEncap_fst pk e)) hpk he
theorem kc_kemEncap_snd {pk e : DY.Bytes} (hpk : KC S g P pk) (he : KC S g P e) : KC S g P (DY.PQKem.kemEncap pk e).2 := memoOK_kemEncap_snd (kp_of_nk (nk_kemEncap_snd pk e)) hpk he
theorem kc_spqrInit {a p : DY.Bytes} (ha : KC S g P a) (hp : KC S g P p) : KC S g P (DY.Spqr.spqrInit a p) := memoOK_spqrInit ha hp
theorem kc_spqrChainKey {a p idx : DY.Bytes} (ha : KC S g P a) (hp : KC S g P p) (hidx : KC S g P idx) : KC S g P (DY.Spqr.spqrChainKey a p idx) := memoOK_spqrChainKey ha hp hidx
theorem kc_spqrSendState {st c : DY.Bytes} (hst : KC S g P st) (hc : KC S g P c) : KC S g P (DY.Spqr.spqrSend st c).1 := memoOK_spqrSendState hst hc
theorem kc_spqrSendMsg {st c : DY.Bytes} (hst : KC S g P st) (hc : KC S g P c) : KC S g P (DY.Spqr.spqrSend st c).2.2 := memoOK_spqrSendMsg hst hc
theorem kc_x25519Key {pk : DY.Bytes} (h : KC S g P pk) : KC S g P (DY.X25519.x25519Key pk) := memoOK_x25519Key h
theorem kc_agree {pk sk : DY.Bytes} (hpk : KC S g P pk) (hsk : KC S g P sk) : KC S g P (DY.Libsignal.PQXDH.agree pk sk) := kc_dh (kc_x25519Key hpk) hsk
theorem kc_serializedIk {ik : DY.Bytes} (hik : KC S g P ik) : KC S g P (DY.Libsignal.PQXDH.serializedIk ik) := kc_concat (kc_lit _) hik
theorem kc_storedSecrets_of_reachable {tr : ExecTrace} (hreach : tr.Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets tr, KC S g P u := CompRPreMemo38KdfCensus.memoOK_storedSecrets_of_reachable kc_lit kc_concat kc_randTerm hreach
end Prim
abbrev TRStateP (S : Sem) (g : Ghost) (P : DY.Bytes → Prop) (st : DY.Libsignal.TripleRatchet.TRState) : Prop := CompRPreMemo38KdfCensus.TRStateMemoOK compI0 S g (KdfP P) st
section TR
variable {S : Sem} {g : Ghost} {P : DY.Bytes → Prop}
theorem kc_serialize_local_tr {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hst : TRStateP S g P ls.state) : KC S g P (Comparse.serialize ls : DY.Bytes) := CompRPreMemo38KdfCensus.memoOK_serialize_local_tr kc_lit kc_concat hst
theorem kc_prefixTerms {r : Records} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, KC S g P u) (hstates : ∀ ls ∈ storedStates r tr, KC S g P (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, KC S g P u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, KC S g P u) : ∀ u ∈ prefixTerms r tr vis, KC S g P u := CompRPreMemo38KdfCensus.memoOK_prefixTerms hsend hstates hsecrets hpt
end TR
def o38 (r : Records) (tr₁ : ExecTrace) : DY.Libsignal.PQXDH.AliceHandshakeOut := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
def stA38 (r : Records) (tr₁ : ExecTrace) : DY.Libsignal.TripleRatchet.TRState := iniAliceStartState tr₁ r.bob (o38 r tr₁)
def ikm38 (r : Records) (tr₁ : ExecTrace) : DY.Bytes := DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree (setupPublic r 4) (setupSecret r 0)) (DY.Libsignal.PQXDH.agree (setupPublic r 2) (randTerm tr₁.length 32)) (DY.Libsignal.PQXDH.agree (setupPublic r 4) (randTerm tr₁.length 32)) none (DY.PQKem.kemEncap (setupPublic r 6) (randTerm (tr₁.length + 1) 32)).2
def dhCc38 (r : Records) (tr₁ : ExecTrace) : DY.Bytes := DY.Libsignal.PQXDH.agree (o38 r tr₁).spk (randTerm (tr₁.length + 2) 32)
def salt38 (r : Records) (tr₁ : ExecTrace) : DY.Bytes := DY.Spqr.spqrChainKey (o38 r tr₁).keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)
def seed38 (r : Records) (tr₁ : ExecTrace) : DY.Bytes := (DY.Libsignal.TripleRatchet.kdfCk (stA38 r tr₁).cks).2
def mk38 (r : Records) (tr₁ : ExecTrace) : DY.Libsignal.TripleRatchet.MessageKeys := DY.Libsignal.TripleRatchet.trMsgKeys (salt38 r tr₁) (seed38 r tr₁)
structure Nodes38 (P : DY.Bytes → Prop) (r : Records) (tr₁ tr₂ : ExecTrace) (cl : Nat) : Prop where
  prkPq : P (DY.KdfExtract.kdfExtract DY.Libsignal.TripleRatchet.zeroSalt (ikm38 r tr₁))
  rk : P (o38 r tr₁).keys.rk
  ck : P (o38 r tr₁).keys.ck
  pqr : P (o38 r tr₁).keys.pqr
  prkCc : P (DY.KdfExtract.kdfExtract (o38 r tr₁).keys.rk (dhCc38 r tr₁))
  cc1 : P (DY.Libsignal.TripleRatchet.createChain (o38 r tr₁).keys.rk (o38 r tr₁).spk (randTerm (tr₁.length + 2) 32)).1
  cc2 : P (DY.Libsignal.TripleRatchet.createChain (o38 r tr₁).keys.rk (o38 r tr₁).spk (randTerm (tr₁.length + 2) 32)).2
  ck1 : P (DY.Libsignal.TripleRatchet.kdfCk (stA38 r tr₁).cks).1
  seed : P (seed38 r tr₁)
  prkMk : P (DY.KdfExtract.kdfExtract (salt38 r tr₁) (seed38 r tr₁))
  cipher : P (mk38 r tr₁).cipherKey
  macKey : P (mk38 r tr₁).macKey
  iv : P (mk38 r tr₁).iv
  mac : P (DY.KdfExtract.kdfExtract (mk38 r tr₁).macKey (DY.Concat.concat (stA38 r tr₁).myIk (DY.Concat.concat (stA38 r tr₁).peerIk (encWire tr₂ (stA38 r tr₁) cl (tr₂.length + 2)))))
section Split38
variable {S : Sem} {g : Ghost} {P : DY.Bytes → Prop}
theorem kc_aliceOut {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (cl : Nat) (hN : Nodes38 P r tr₁ tr₂ cl) : KC S g P (o38 r tr₁).ikA ∧ KC S g P (o38 r tr₁).ikB ∧ KC S g P (o38 r tr₁).spk ∧ KC S g P (o38 r tr₁).ek ∧ KC S g P (o38 r tr₁).ct ∧ KC S g P (o38 r tr₁).keys.rk ∧ KC S g P (o38 r tr₁).keys.ck ∧ KC S g P (o38 r tr₁).keys.pqr := by
  have hsec0 : KC S g P (setupSecret r 0) := CompSetupSecrecy.setupSecret_0 hNe ▸ kc_randTerm _ _; have hpub2 : KC S g P (setupPublic r 2) := CompSetupSecrecy.setupPublic_2 hNe ▸ kc_dhPk (kc_randTerm _ _); have hpub4 : KC S g P (setupPublic r 4) := CompSetupSecrecy.setupPublic_4 hNe ▸ kc_dhPk (kc_randTerm _ _); have hpub6 : KC S g P (setupPublic r 6) := CompSetupSecrecy.setupPublic_6 hNe ▸ kc_kemPk (kc_randTerm _ _); have hek_r : KC S g P (randTerm tr₁.length 32) := kc_randTerm _ _; have hent_r : KC S g P (randTerm (tr₁.length + 1) 32) := kc_randTerm _ _
  have hprk := kc_kdfExtract hN.prkPq (kc_lit _)
    (kc_concat (kc_lit _) (kc_concat (kc_agree hpub4 hsec0) (kc_concat (kc_agree hpub2 hek_r) (kc_concat (kc_agree hpub4 hek_r) (kc_kemEncap_snd hpub6 hent_r)))))
  exact ⟨kc_dhPk hsec0, hpub2, hpub4, kc_dhPk hek_r, kc_kemEncap_fst hpub6 hent_r, kc_hkdfBlock1 hN.rk hprk (kc_lit _), kc_hkdfBlock2 hN.rk hN.ck hprk (kc_lit _), kc_hkdfBlock3 hN.rk hN.ck hN.pqr hprk (kc_lit _)⟩
theorem kc_createChain {rk pk sk : DY.Bytes} (hprkP : P (DY.KdfExtract.kdfExtract rk (DY.Libsignal.PQXDH.agree pk sk))) (h1 : P (DY.Libsignal.TripleRatchet.createChain rk pk sk).1) (h2 : P (DY.Libsignal.TripleRatchet.createChain rk pk sk).2) (hrk : KC S g P rk) (hpk : KC S g P pk) (hsk : KC S g P sk) : KC S g P (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧ KC S g P (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 :=
  let hprk := kc_kdfExtract hprkP hrk (kc_agree hpk hsk);
  ⟨kc_hkdfBlock1 h1 hprk (kc_lit _), kc_hkdfBlock2 h1 h2 hprk (kc_lit _)⟩
theorem trStateP_iniAliceStartState (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hikA : KC S g P o.ikA) (hikB : KC S g P o.ikB) (hspk : KC S g P o.spk) (hrk : KC S g P o.keys.rk) (hck : KC S g P o.keys.ck) (hpqr : KC S g P o.keys.pqr) (hprkCc : P (DY.KdfExtract.kdfExtract o.keys.rk (DY.Libsignal.PQXDH.agree o.spk (randTerm (tr.length + 2) 32)))) (hcc1 : P (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).1) (hcc2 : P (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).2) : TRStateP S g P (iniAliceStartState tr b o) :=
  let hdhsA := kc_randTerm (S := S) (g := g) (P := P) (tr.length + 2) 32; let hcc := kc_createChain hprkCc hcc1 hcc2 hrk hspk hdhsA;
  ⟨kc_serializedIk hikA, kc_serializedIk hikB, hcc.1, hdhsA, hcc.2, kc_concat (kc_dhPk hdhsA) hrk,
    kc_spqrInit hpqr (kc_lit _), fun _ hd => by rcases List.mem_singleton.mp hd with rfl; exact ⟨hspk, hck⟩⟩
theorem trStateP_stA38 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (cl : Nat) (hN : Nodes38 P r tr₁ tr₂ cl) : TRStateP S g P (stA38 r tr₁) := by obtain ⟨hikA, hikB, hspk, _, _, hrk, hck, hpqr⟩ := kc_aliceOut (S := S) (g := g) hNe tr₁ tr₂ cl hN; exact trStateP_iniAliceStartState tr₁ r.bob (o38 r tr₁) hikA hikB hspk hrk hck hpqr hN.prkCc hN.cc1 hN.cc2
theorem trStateP_encSt38 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (cl : Nat) (hN : Nodes38 P r tr₁ tr₂ cl) : TRStateP S g P (encSt tr₂ (stA38 r tr₁) cl) :=
  have hst := trStateP_stA38 (S := S) (g := g) hNe tr₁ tr₂ cl hN
  ⟨hst.myIk, hst.peerIk, hst.rk, hst.dhs, kc_kdfExtract hN.ck1 hst.cks (kc_lit _), hst.sid, kc_spqrSendState hst.spqr (kc_randTerm _ _), hst.recv⟩
theorem kc_encOut38 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (cl : Nat) (hN : Nodes38 P r tr₁ tr₂ cl) : KC S g P (encOut tr₂ (stA38 r tr₁) cl (tr₂.length + 2)) := by
  have hst := trStateP_stA38 (S := S) (g := g) hNe tr₁ tr₂ cl hN; obtain ⟨_, _, _, _, _, _, _, hpqr⟩ := kc_aliceOut (S := S) (g := g) hNe tr₁ tr₂ cl hN; have hsalt_eq : encSalt tr₂ (stA38 r tr₁) cl (tr₂.length + 2) = salt38 r tr₁ := encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ r.bob (o38 r tr₁) cl
  have hprkMk := kc_kdfExtract hN.prkMk (kc_spqrChainKey hpqr (kc_lit _) (kc_lit _))
    (kc_kdfExtract hN.seed hst.cks (kc_lit _))
  have hct := kc_symEnc (kc_hkdfBlock1 hN.cipher hprkMk (kc_lit _))
    (kc_hkdfBlock3 hN.cipher hN.macKey hN.iv hprkMk (kc_lit _)) (kc_randTerm tr₂.length 32)
  have hwire : KC S g P (encWire tr₂ (stA38 r tr₁) cl (tr₂.length + 2)) := (by dsimp only [encWire, DY.Libsignal.TripleRatchet.trHonestWireMsg]; rw [hsalt_eq]; exact kc_trWire (kc_dhPk hst.dhs) hct (kc_spqrSendMsg hst.spqr (kc_randTerm (tr₂.length + 1) cl))); have hmac : KC S g P (encMac tr₂ (stA38 r tr₁) cl (tr₂.length + 2)) := (by dsimp only [encMac]; rw [hsalt_eq]; unfold DY.Libsignal.TripleRatchet.computeMac; exact kc_trunc8 (kc_kdfExtract hN.mac (kc_hkdfBlock2 hN.cipher hN.macKey hprkMk (kc_lit _)) (kc_concat hst.myIk (kc_concat hst.peerIk hwire)))); exact kc_concat hwire hmac
theorem kc_preTerms_split38 {r : Records} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hreach : (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post)).Reachable reachability) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) (hN : Nodes38 P r (runMoves pre (setupTrace r)).1 (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1 cl) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let wrap := some (tr₁.length + 3, tr₁.length + 4); let m₁' := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) wrap; let ms' := pre ++ m₀ :: mid ++ m₁' :: post;
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), KC S g P u := by
  dsimp only; let tr₁ := (runMoves pre (setupTrace r)).1; let tr₂ := (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; have ho_out := kc_aliceOut (S := S) (g := g) hNe tr₁ tr₂ cl hN
  have hstA : TRStateP S g P stA := by dsimp only [stA]; rw [ho]; exact trStateP_stA38 hNe tr₁ tr₂ cl hN
  have henc_st : TRStateP S g P (encSt tr₂ stA cl) := by dsimp only [stA]; rw [ho]; exact trStateP_encSt38 hNe tr₁ tr₂ cl hN
  have henc_out : KC S g P (encOut tr₂ stA cl (tr₂.length + 2)) := by dsimp only [stA]; rw [ho]; exact kc_encOut38 hNe tr₁ tr₂ cl hN
  refine kc_prefixTerms (fun v hv hkind u hu_v => ?_) (fun ls hls => ?_)
    (kc_storedSecrets_of_reachable hreach) (fun v hv hkind u hu_v => ?_)
  · rcases send_terms_split38_mem hNe ho hpre hmid hpost hm₀ hv hkind hu_v with rfl | rfl | rfl
    · rw [ho]; exact ho_out.2.2.2.1
    · rw [ho]; exact ho_out.2.2.2.2.1
    · exact henc_out
  · rcases storedStates_split38_cases ho hpre hmid hpost hm₀ hls with hls_eq | hls_eq <;> rw [hls_eq]
    · exact kc_serialize_local_tr hstA
    · exact kc_serialize_local_tr henc_st
  · rw [pt_terms_split38_mem hNe ho hpre hmid hpost hm₀ hv hkind hu_v]; exact kc_randTerm _ _
theorem kdfP_preMemo_split38_of_modelRun {r : Records} (hNe : r.alice ≠ r.bob) (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    ModelRun r ms → MovesFrom InvisibleNoEffect (setupTrace r) pre →
    MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
    MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
    m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
    Nodes38 P r tr₁ tr₂ cl →
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), MemoOK compI0 S g (KdfP P) u := by
  intro tr₁ o m₀ tr₂ pq ms ms' hmr hpre hmid hpost hm₀ hN
  have htr_eq := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl pq
    (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  exact kc_preTerms_split38 (S := S) (g := g) hNe rfl (htr_eq ▸ hmr.2.2.1.1) hpre hmid hpost hm₀ hN
end Split38
end Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38Pre
