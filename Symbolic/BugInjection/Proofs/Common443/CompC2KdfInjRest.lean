/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin
public import Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT
public import Symbolic.BugInjection.Proofs.Common443.Census443Memo
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.CompPlant

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakState Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPlant CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompRI0TermInj CompRMemoKnown CompRNoBSC CompRNonInj38Census CompRPreMemo38KdfCensus CompRSplit38KdfHead CompRSplit38PairCore CompRSplit38QKdf CompRSplit38UntaggedShape CompRX0NBSC38 CompRX0NBSC38Parts Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED.CompTrace
open DY.Literal (literalToBytes) open DY.Concat (concat) open DY.KdfExtract (kdfExtract)
open DY.DiffieHellman DY.SymEnc DY.Trunc DY.TrWire DY.PQKem DY.Spqr DY.X25519
open DY.Libsignal.PQXDH (agree serializedIk PQXDHState AliceHandshakeOut BundleHandles pqxdhKdf pqxdhIkm)
open DY.Libsignal.TripleRatchet (TRState hkdfBlock1 hkdfBlock2 hkdfBlock3 createChain kdfCk trMsgKeys hmac computeMac trHonestWireMsg)
def KdfInjRestEntry (S : Sem) (g : Ghost) (x : Bytes × Bytes × HwBytes) : Prop := ¬ IsKdf x.1 → ¬ IsX x.1 → ¬ IsTrunc8 x.1 → assumedInjective x.1 = true → KdfFree (gamma compI0 S g x.1) ∨ (gamma compI0 S g x.1).length ≠ 32
def KdfInjRestCensus (i : ExternInterpretation) (S : Sem) (g : Ghost) (t : Bytes) : Prop := MemoOK i S g (KdfInjRestEntry S g) t
theorem qKdfInjRest_of_entry {S : Sem} {g : Ghost} {known : Bytes → Prop} {pts : List Bytes} {x₁ x₂ : Bytes × Bytes × HwBytes} (h₂ : KdfInjRestEntry S g x₂) : QKdfInjRest S g known pts x₁ x₂ :=
  fun _ _ _ hK₂ hX₂ hT₂ hinj₂ _ _ _ => h₂ hK₂ hX₂ hT₂ hinj₂
section Prim
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem kirc_of_ni {b : Bytes} (hb : assumedInjective b = false) : ∀ x : Bytes × Bytes × HwBytes, x.1 = b → KdfInjRestEntry S g x :=
  fun _ hx _ _ _ hinj => by rw [hx, hb] at hinj; cases hinj
theorem kirc_of_isKdf {b : Bytes} (hb : IsKdf b) : ∀ x : Bytes × Bytes × HwBytes, x.1 = b → KdfInjRestEntry S g x :=
  fun _ hx hK _ _ _ => absurd (hx ▸ hb) hK
theorem kirc_of_isX {b : Bytes} (hb : IsX b) : ∀ x : Bytes × Bytes × HwBytes, x.1 = b → KdfInjRestEntry S g x :=
  fun _ hx _ hX _ _ => absurd (hx ▸ hb) hX
theorem kirc_of_isTrunc8 {b : Bytes} (hb : IsTrunc8 b) : ∀ x : Bytes × Bytes × HwBytes, x.1 = b → KdfInjRestEntry S g x :=
  fun _ hx _ _ hT _ => absurd (hx ▸ hb) hT
theorem assumedInjective_concat (a c : Bytes) : assumedInjective (concat a c) = false :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq a c
theorem assumedInjective_trWire (ver : UInt8) (rk : Bytes) (c pc : UInt32) (ct pq : Bytes) (ev : EncodingVariation) : assumedInjective (({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : TrWireMsg.SubF Bytes).pack) = false :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_trWire_pack_eq _
theorem kirc_lit (bs : ByteArray) : KdfInjRestCensus i S g (literalToBytes bs) := memoOK_lit (kirc_of_ni (assumedInjective_lit bs))
theorem kirc_concat {a c : Bytes} (ha : KdfInjRestCensus i S g a) (hc : KdfInjRestCensus i S g c) : KdfInjRestCensus i S g (concat a c) := memoOK_concat (kirc_of_ni (assumedInjective_concat a c)) ha hc
theorem kirc_dhPk {sk : Bytes} (hsk : KdfInjRestCensus i S g sk) : KdfInjRestCensus i S g (dhPk sk) := memoOK_dhPk (kirc_of_isX (.inl ⟨sk, rfl⟩)) hsk
theorem kirc_of_dhPk {sk : Bytes} (h : KdfInjRestCensus i S g (dhPk sk)) : KdfInjRestCensus i S g sk := memoOK_dhPk_elim h
theorem kirc_dh_pack {pk sk : Bytes} (hpk : KdfInjRestCensus i S g pk) (hsk : KdfInjRestCensus i S g sk) : KdfInjRestCensus i S g (({ pk := pk, sk := sk } : Dh.SubF Bytes).pack) := memoOK_dh_pack (kirc_of_isX (.inr ⟨pk, sk, rfl⟩)) hpk hsk
theorem kirc_dh {pk sk : Bytes} (hpk : KdfInjRestCensus i S g pk) (hsk : KdfInjRestCensus i S g sk) : KdfInjRestCensus i S g (dh pk sk) := by
  have hv := Bytes.pack_view? DhPk.SubF pk; simp only [dh, CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    split <;> [exact kirc_dh_pack hpk hsk; exact kirc_dh_pack (kirc_dhPk hsk) (kirc_of_dhPk hpk)]
  · exact kirc_dh_pack hpk hsk
theorem kirc_kdfExtract {a b : Bytes} (ha : KdfInjRestCensus i S g a) (hb : KdfInjRestCensus i S g b) : KdfInjRestCensus i S g (kdfExtract a b) := memoOK_kdfExtract (kirc_of_isKdf ⟨a, b, rfl⟩) ha hb
theorem kirc_hmac {a b : Bytes} (ha : KdfInjRestCensus i S g a) (hb : KdfInjRestCensus i S g b) : KdfInjRestCensus i S g (hmac a b) := kirc_kdfExtract ha hb
theorem kirc_hkdfBlock1 {prk info : Bytes} (hprk : KdfInjRestCensus i S g prk) (hinfo : KdfInjRestCensus i S g info) : KdfInjRestCensus i S g (hkdfBlock1 prk info) := kirc_hmac hprk (kirc_concat hinfo (kirc_lit _))
theorem kirc_hkdfBlock2 {prk info : Bytes} (hprk : KdfInjRestCensus i S g prk) (hinfo : KdfInjRestCensus i S g info) : KdfInjRestCensus i S g (hkdfBlock2 prk info) := kirc_hmac hprk (kirc_concat (kirc_hkdfBlock1 hprk hinfo) (kirc_concat hinfo (kirc_lit _)))
theorem kirc_hkdfBlock3 {prk info : Bytes} (hprk : KdfInjRestCensus i S g prk) (hinfo : KdfInjRestCensus i S g info) : KdfInjRestCensus i S g (hkdfBlock3 prk info) := kirc_hmac hprk (kirc_concat (kirc_hkdfBlock2 hprk hinfo) (kirc_concat hinfo (kirc_lit _)))
theorem kirc_trunc8 {a : Bytes} (ha : KdfInjRestCensus i S g a) : KdfInjRestCensus i S g (trunc8 a) := memoOK_trunc8 (kirc_of_isTrunc8 ⟨a, rfl⟩) ha
theorem kirc_trWire {ver : UInt8} {rk ct pq : Bytes} {c pc : UInt32} {ev : EncodingVariation} (hrk : KdfInjRestCensus i S g rk) (hct : KdfInjRestCensus i S g ct) (hpq : KdfInjRestCensus i S g pq) : KdfInjRestCensus i S g (trWireMsg ver rk c pc ct pq ev) := by rw [show trWireMsg ver rk c pc ct pq ev = ({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : TrWireMsg.SubF Bytes).pack from rfl]; exact memoOK_trWire (kirc_of_ni (assumedInjective_trWire ver rk c pc ct pq ev)) hrk hct hpq
theorem kirc_kemPk {sk : Bytes} (hsk : KdfInjRestCensus i S g sk) : KdfInjRestCensus i S g (kemPk sk) := memoOK_kemPk hsk
theorem kirc_kemEncap_fst {pk e : Bytes} (hpk : KdfInjRestCensus compI0 S g pk) (he : KdfInjRestCensus compI0 S g e) : KdfInjRestCensus compI0 S g (kemEncap pk e).1 := by
  refine Census443Memo.memoOK_kemEncap_fst' (fun x hx _ he32 _ _ _ _ => Or.inr ?_) hpk he; rw [hx, Census443Memo.gamma_kemEncap_fst_eq he32, Census443Memo.length_of_mem_kyberCtVals (Census443Memo.compI0_kyberEncaps_take1568_mem _ _)]
  decide
theorem kirc_kemEncap_snd {pk e : Bytes} (hpk : KdfInjRestCensus compI0 S g pk) (he : KdfInjRestCensus compI0 S g e) (hss : KdfFree (gamma compI0 S g (kemEncap pk e).2)) : KdfInjRestCensus compI0 S g (kemEncap pk e).2 :=
  memoOK_kemEncap_snd (fun _ hx _ _ _ _ => Or.inl (hx ▸ hss)) hpk he
theorem kirc_spqrInit {a p : Bytes} (ha : KdfInjRestCensus i S g a) (hp : KdfInjRestCensus i S g p) : KdfInjRestCensus i S g (spqrInit a p) := memoOK_spqrInit ha hp
theorem kirc_spqrChainKey {a p idx : Bytes} (ha : KdfInjRestCensus i S g a) (hp : KdfInjRestCensus i S g p) (hidx : KdfInjRestCensus i S g idx) : KdfInjRestCensus i S g (spqrChainKey a p idx) := memoOK_spqrChainKey ha hp hidx
theorem kirc_spqrSendState {st c : Bytes} (hst : KdfInjRestCensus i S g st) (hc : KdfInjRestCensus i S g c) : KdfInjRestCensus i S g (spqrSend st c).1 := memoOK_spqrSendState hst hc
theorem kirc_spqrSendKey {st c : Bytes} (hst : KdfInjRestCensus i S g st) (hc : KdfInjRestCensus i S g c) : KdfInjRestCensus i S g (spqrSend st c).2.1 := by
  unfold spqrSend; dsimp only; have hp := Bytes.pack_view? InitState.SubF st
  cases hv : st.view? InitState.SubF with
  | none => exact memoOK_spqrSendKey_pack hst hc
  | some x =>
    rw [hv] at hp; rw [← hp] at hst; obtain ⟨hk, hpar⟩ := memoOK_spqrInit_elim hst; exact kirc_spqrChainKey hk hpar (kirc_lit _)
theorem kirc_spqrSendMsg {st c : Bytes} (hst : KdfInjRestCensus i S g st) (hc : KdfInjRestCensus i S g c) : KdfInjRestCensus i S g (spqrSend st c).2.2 := memoOK_spqrSendMsg hst hc
theorem kirc_x25519Key {pk : Bytes} (h : KdfInjRestCensus i S g pk) : KdfInjRestCensus i S g (x25519Key pk) := memoOK_x25519Key h
theorem kirc_symEnc_of_lt18 {k iv m : Bytes} (hm_len : (gamma compI0 S g m).length < 16) (hk : KdfInjRestCensus i S g k) (hiv : KdfInjRestCensus i S g iv) (hm : KdfInjRestCensus i S g m) : KdfInjRestCensus i S g (symEnc k iv m) := by refine memoOK_symEnc (fun x hx _ _ _ _ => ?_) hk hiv hm; have hlt : (gamma compI0 S g x.1).length < 18 := (by rw [hx, gamma_symEnc_compI0]; exact compAesPerm_length_lt (by decide) hm_len); exact Or.inr (by omega)
theorem kirc_randTerm_of {idx sz : Nat} (h : KdfFree (gamma compI0 S g (randTerm idx sz)) ∨ (gamma compI0 S g (randTerm idx sz)).length ≠ 32) : KdfInjRestCensus i S g (randTerm idx sz) := by
  intro x hx; unfold gamma' randTerm at hx; rw [Bytes.rec_eq (gRandom g) (gAll i S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx
  split_ifs at hx with hsz; · cases hx
  rcases List.mem_singleton.mp hx with rfl; exact fun _ _ _ _ => h
theorem kirc_agree {pk sk : Bytes} (hpk : KdfInjRestCensus i S g pk) (hsk : KdfInjRestCensus i S g sk) : KdfInjRestCensus i S g (agree pk sk) := kirc_dh (kirc_x25519Key hpk) hsk
theorem kirc_createChain {rk pk sk : Bytes} (hrk : KdfInjRestCensus i S g rk) (hpk : KdfInjRestCensus i S g pk) (hsk : KdfInjRestCensus i S g sk) : KdfInjRestCensus i S g (createChain rk pk sk).1 ∧ KdfInjRestCensus i S g (createChain rk pk sk).2 :=
  let hprk := kirc_hmac hrk (kirc_agree hpk hsk);
  ⟨kirc_hkdfBlock1 hprk (kirc_lit _), kirc_hkdfBlock2 hprk (kirc_lit _)⟩
theorem kirc_kdfCk {ck : Bytes} (hck : KdfInjRestCensus i S g ck) : KdfInjRestCensus i S g (kdfCk ck).1 ∧ KdfInjRestCensus i S g (kdfCk ck).2 := ⟨kirc_hmac hck (kirc_lit _), kirc_hmac hck (kirc_lit _)⟩
theorem kirc_trMsgKeys {salt ck : Bytes} (hsalt : KdfInjRestCensus i S g salt) (hck : KdfInjRestCensus i S g ck) : let mk := trMsgKeys salt (kdfCk ck).2; KdfInjRestCensus i S g mk.cipherKey ∧ KdfInjRestCensus i S g mk.macKey ∧ KdfInjRestCensus i S g mk.iv :=
  let hprk := kirc_hmac hsalt (kirc_kdfCk hck).2;
  ⟨kirc_hkdfBlock1 hprk (kirc_lit _), kirc_hkdfBlock2 hprk (kirc_lit _), kirc_hkdfBlock3 hprk (kirc_lit _)⟩
theorem kirc_computeMac_trWire {mk ikS ikR rk ct pq : Bytes} {v : UInt8} {c pc : UInt32} {ev : EncodingVariation} (hmk : KdfInjRestCensus i S g mk) (hikS : KdfInjRestCensus i S g ikS) (hikR : KdfInjRestCensus i S g ikR) (hrk : KdfInjRestCensus i S g rk) (hct : KdfInjRestCensus i S g ct) (hpq : KdfInjRestCensus i S g pq) : KdfInjRestCensus i S g (computeMac mk ikS ikR (trWireMsg v rk c pc ct pq ev)) := kirc_trunc8 (kirc_hmac hmk (kirc_concat hikS (kirc_concat hikR (kirc_trWire hrk hct hpq))))
theorem kirc_serializedIk {ik : Bytes} (hik : KdfInjRestCensus i S g ik) : KdfInjRestCensus i S g (serializedIk ik) := kirc_concat (kirc_lit _) hik
theorem kirc_pqxdhKdf_none {dh1 dh2 dh3 ss : Bytes} (hdh1 : KdfInjRestCensus i S g dh1) (hdh2 : KdfInjRestCensus i S g dh2) (hdh3 : KdfInjRestCensus i S g dh3) (hss : KdfInjRestCensus i S g ss) : let keys := pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss); KdfInjRestCensus i S g keys.rk ∧ KdfInjRestCensus i S g keys.ck ∧ KdfInjRestCensus i S g keys.pqr :=
  let hprk := kirc_hmac (kirc_lit _) (kirc_concat (kirc_lit _) (kirc_concat hdh1 (kirc_concat hdh2 (kirc_concat hdh3 hss))));
  ⟨kirc_hkdfBlock1 hprk (kirc_lit _), kirc_hkdfBlock2 hprk (kirc_lit _), kirc_hkdfBlock3 hprk (kirc_lit _)⟩
theorem kirc_serialize_local_pqxdh {ls : DY.PersistentLocalState.LocalState PQXDHState} (hsk : KdfInjRestCensus i S g ls.state.sk) : KdfInjRestCensus i S g (Comparse.serialize ls : Bytes) := CompRPreMemo38KdfCensus.memoOK_serialize_local_pqxdh kirc_lit kirc_concat hsk
end Prim
abbrev TRStateKIRC (i : ExternInterpretation) (S : Sem) (g : Ghost) (st : TRState) : Prop := CompRPreMemo38KdfCensus.TRStateMemoOK i S g (KdfInjRestEntry S g) st
section TR
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem kirc_serialize_local_tr {ls : DY.PersistentLocalState.LocalState TRState} (hst : TRStateKIRC i S g ls.state) : KdfInjRestCensus i S g (Comparse.serialize ls : Bytes) := CompRPreMemo38KdfCensus.memoOK_serialize_local_tr kirc_lit kirc_concat hst
theorem kirc_prefixTerms {r : Records} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, KdfInjRestCensus i S g u) (hstates : ∀ ls ∈ storedStates r tr, KdfInjRestCensus i S g (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, KdfInjRestCensus i S g u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, KdfInjRestCensus i S g u) : ∀ u ∈ prefixTerms r tr vis, KdfInjRestCensus i S g u := CompRPreMemo38KdfCensus.memoOK_prefixTerms hsend hstates hsecrets hpt
theorem trStateKIRC_iniAliceStartState (tr : ExecTrace) (b : Participant) (o : AliceHandshakeOut) (hdhsA : KdfInjRestCensus i S g (randTerm (tr.length + 2) 32)) (hikA : KdfInjRestCensus i S g o.ikA) (hikB : KdfInjRestCensus i S g o.ikB) (hspk : KdfInjRestCensus i S g o.spk) (hrk : KdfInjRestCensus i S g o.keys.rk) (hck : KdfInjRestCensus i S g o.keys.ck) (hpqr : KdfInjRestCensus i S g o.keys.pqr) : TRStateKIRC i S g (iniAliceStartState tr b o) :=
  let hcc := kirc_createChain hrk hspk hdhsA;
  ⟨kirc_serializedIk hikA, kirc_serializedIk hikB, hcc.1, hdhsA, hcc.2, kirc_concat (kirc_dhPk hdhsA) hrk,
    kirc_spqrInit hpqr (kirc_lit _), fun _ hd => by rcases List.mem_singleton.mp hd with rfl; exact ⟨hspk, hck⟩⟩
theorem trStateKIRC_encSt (tr₂ : ExecTrace) {stA : TRState} (cl : Nat) (hst : TRStateKIRC i S g stA) (hcoins : KdfInjRestCensus i S g (randTerm (tr₂.length + 1) cl)) : TRStateKIRC i S g (encSt tr₂ stA cl) := ⟨hst.myIk, hst.peerIk, hst.rk, hst.dhs, (kirc_kdfCk hst.cks).1, hst.sid, kirc_spqrSendState hst.spqr hcoins, hst.recv⟩
theorem kirc_encOut_self (tr₂ : ExecTrace) {stA : TRState} (cl : Nat) (hst : TRStateKIRC i S g stA) (hpt_len : (gamma compI0 S g (randTerm tr₂.length 32)).length < 16) (hcoins : KdfInjRestCensus i S g (randTerm (tr₂.length + 1) cl)) : KdfInjRestCensus i S g (encOut tr₂ stA cl (tr₂.length + 2)) := by dsimp only [encOut, encWire, encMac, trHonestWireMsg]; have hsalt : KdfInjRestCensus i S g (encSalt tr₂ stA cl (tr₂.length + 2)) := (by rw [encSalt_self]; exact kirc_spqrSendKey hst.spqr hcoins); have hmk := kirc_trMsgKeys hsalt hst.cks; have hct := kirc_symEnc_of_lt18 hpt_len hmk.1 hmk.2.2 (kirc_randTerm_of (.inr (by omega))); have hdhsPk := kirc_dhPk hst.dhs; have hpqMsg := kirc_spqrSendMsg hst.spqr hcoins; exact kirc_concat (kirc_trWire hdhsPk hct hpqMsg) (kirc_computeMac_trWire hmk.2.1 hst.myIk hst.peerIk hdhsPk hct hpqMsg)
theorem kirc_spqrRecv_state {st msg : Bytes} {idx : UInt32} {st' : Bytes} (hst : KdfInjRestCensus i S g st) (hm : KdfInjRestCensus i S g msg) (h : (spqrRecv st msg idx).map Prod.fst = some st') : KdfInjRestCensus i S g st' := by
  unfold spqrRecv at h
  split at h
  · simp at h
  · split at h
    · split at h <;> simp at h; subst h; exact memoOK_spqrRecvState_pack hst hm
    · simp at h; subst h; exact memoOK_spqrRecvState_pack hst hm
theorem kirc_aliceOut {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) (h0 : KdfInjRestCensus compI0 S g (randTerm 0 32)) (h5 : KdfInjRestCensus compI0 S g (randTerm 5 32)) (h10 : KdfInjRestCensus compI0 S g (randTerm 10 32)) (h16 : KdfInjRestCensus compI0 S g (randTerm 16 64)) (hek : KdfInjRestCensus compI0 S g (randTerm tr₁.length 32)) (hent : KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 1) 32)) (hss : KdfFree (gamma compI0 S g (kemEncap (kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2)) : let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; KdfInjRestCensus compI0 S g o.ikA ∧ KdfInjRestCensus compI0 S g o.ikB ∧ KdfInjRestCensus compI0 S g o.spk ∧ KdfInjRestCensus compI0 S g o.ek ∧ KdfInjRestCensus compI0 S g o.ct ∧ KdfInjRestCensus compI0 S g o.keys.rk ∧ KdfInjRestCensus compI0 S g o.keys.ck ∧
      KdfInjRestCensus compI0 S g o.keys.pqr := by
  dsimp only; rw [CompSetupSecrecy.setupSecret_0 hNe, CompSetupSecrecy.setupPublic_2 hNe, CompSetupSecrecy.setupPublic_4 hNe, CompSetupSecrecy.setupPublic_6 hNe]; have hpub2 := kirc_dhPk h5; have hpub4 := kirc_dhPk h10; have hpub6 := kirc_kemPk h16
  rcases kirc_pqxdhKdf_none (kirc_agree hpub4 h0) (kirc_agree hpub2 hek)
    (kirc_agree hpub4 hek) (kirc_kemEncap_snd hpub6 hent hss) with ⟨hrk, hck, hpqr⟩
  exact ⟨kirc_dhPk h0, hpub2, hpub4, kirc_dhPk hek, kirc_kemEncap_fst hpub6 hent, hrk, hck, hpqr⟩
theorem trStateKIRC_stA {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) (h0 : KdfInjRestCensus compI0 S g (randTerm 0 32)) (h5 : KdfInjRestCensus compI0 S g (randTerm 5 32)) (h10 : KdfInjRestCensus compI0 S g (randTerm 10 32)) (h16 : KdfInjRestCensus compI0 S g (randTerm 16 64)) (hek : KdfInjRestCensus compI0 S g (randTerm tr₁.length 32)) (hent : KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 1) 32)) (hss : KdfFree (gamma compI0 S g (kemEncap (kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2)) (hdhs : KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 2) 32)) : TRStateKIRC compI0 S g (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) := by obtain ⟨hikA, hikB, hspk, _, _, hrk, hck, hpqr⟩ := kirc_aliceOut hNe tr₁ h0 h5 h10 h16 hek hent hss; exact trStateKIRC_iniAliceStartState tr₁ r.bob _ hdhs hikA hikB hspk hrk hck hpqr
end TR
open DY.Libsignal.HwEvents (MachineEvent)
theorem forall2_exists_left' {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} (h : List.Forall₂ R as bs) {y : β} (hy : y ∈ bs) : ∃ x ∈ as, R x y := by
  induction h with
  | nil => cases hy
  | cons hhead _ ih =>
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact ⟨_, List.mem_cons_self .., hhead⟩
    · obtain ⟨x, hx, hr⟩ := ih hmem; exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩
theorem forall2_append_drop_exists_left' {α β : Type} {R : α → β → Prop} : ∀ {xs : List α} {ys zs : List β}, List.Forall₂ R xs (ys ++ zs) → ∀ z ∈ zs, ∃ x ∈ xs.drop ys.length, R x z
  | _, [], _, h, _, hz => forall2_exists_left' h hz
  | _ :: _, _ :: _, _, .cons _ h, _, hz => forall2_append_drop_exists_left' h _ hz
theorem gamma_of_single {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ev : MachineEvent} {v : VisEntry} {t : Bytes} (hl : v.layout = .single) (ht : v.terms = [t]) (hem : EventMatchesEntry i r S g ev v) : gamma i S g t = CompRPlantWire.eventBytes ev := by
  obtain ⟨_, hmap⟩ := hem; rcases v with ⟨k, ts, lay, anc⟩; dsimp only at hl ht hmap
  subst hl ht; simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
  cases ev <;> exact hmap
theorem kirc_draws_of_aliceVis {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {a b : Participant} {o : AliceHandshakeOut} {hb : BundleHandles} {bun b₀ : HwBytes} {rs' : List MachineEvent} (hm₀ : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: .rng b₀ :: rs') (aliceVis tr₁ (iniAliceStartTr tr₁ a b o) hb)) (hb₀ : KdfFree b₀) (hent : KdfFree (CompRX0Gamma.coinHeads (rs'.take 32))) (hdhs : ∀ ev ∈ rs'.drop 32, KdfFree (CompRPlantWire.eventBytes ev)) : KdfInjRestCensus compI0 S g (randTerm tr₁.length 32) ∧ KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 1) 32) ∧ KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 2) 32) := by
  obtain ⟨hek_eq, hent_eq⟩ := CompRX0Gamma.aliceVis_rng_coins hm₀; have hek_kirc := kirc_randTerm_of (i := compI0) (S := S) (g := g) (.inl ((List.cons.inj hek_eq).1 ▸ hb₀)); have hent_kirc := kirc_randTerm_of (i := compI0) (S := S) (g := g) (.inl (hent_eq ▸ hent)); rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr] at hm₀
  cases hm₀ with | cons _ hm₁ => cases hm₁ with | cons _ hm_rest =>
  obtain ⟨ev_dhs, hev_dhs_mem, hem_dhs⟩ := forall2_append_drop_exists_left' hm_rest
      ({ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } : VisEntry)
      (List.mem_singleton_self _)
  have hkl : (kyberCoinEntries (randTerm (tr₁.length + 1) 32)).length = 32 := by unfold kyberCoinEntries; simp
  rw [hkl] at hev_dhs_mem; have hγ := gamma_of_single rfl rfl hem_dhs; exact ⟨hek_kirc, hent_kirc, kirc_randTerm_of (.inl (hγ ▸ hdhs ev_dhs hev_dhs_mem))⟩
theorem kirc_draws_of_encVis {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : TRState} {cl pq : Nat} {wr : Nat × Nat} {pt c w : HwBytes} (hm₁ : List.Forall₂ (EventMatchesEntry compI0 r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some wr) true)) (hpt : pt.length < 16) (hc : KdfFree c) : (gamma compI0 S g (randTerm tr₂.length 32)).length < 16 ∧ KdfInjRestCensus compI0 S g (randTerm tr₂.length 32) ∧ KdfInjRestCensus compI0 S g (randTerm (tr₂.length + 1) cl) := by obtain ⟨_, hpt_em, hc_em, -⟩ := CompPrefixInvFresh.encVis_encNextTr_of_forall2_three hm₁; have hpt_lt : (gamma compI0 S g (randTerm tr₂.length 32)).length < 16 := (gamma_of_single rfl rfl hpt_em) ▸ hpt; exact ⟨hpt_lt, kirc_randTerm_of (.inr (by omega)), kirc_randTerm_of (.inl ((gamma_of_single rfl rfl hc_em) ▸ hc))⟩
theorem isKdf_or_isTrunc8_of_mem_zeroSalted {tr₂ : ExecTrace} {stA : TRState} {cl pq : Nat} {u : Bytes} (hu : u ∈ CompRX0NBSC38Hmc.zeroSaltedTermsStA tr₂ stA cl pq) : IsKdf u ∨ IsTrunc8 u := by
  unfold CompRX0NBSC38Hmc.zeroSaltedTermsStA at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (first | exact Or.inl ⟨_, _, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
theorem qKdfInjRest_of_split38_pre {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ : ExecTrace} {cl : Nat} {known : Bytes → Prop} {pts : List Bytes} {x₁ x₂ : Bytes × Bytes × HwBytes} (hpre : ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), KdfInjRestCensus compI0 S g u) (hc₂ : CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x₂) : QKdfInjRest S g known pts x₁ x₂ := by
  intro k m hk hK hX hT hai hs hu he
  rcases hc₂ with hm | hfalse | hz
  · obtain ⟨u, hu_mem, hxu⟩ := List.mem_flatMap.mp hm; exact qKdfInjRest_of_entry (hpre u hu_mem x₂ hxu) k m hk hK hX hT hai hs hu he
  · rw [hfalse] at hai; cases hai
  · exact (isKdf_or_isTrunc8_of_mem_zeroSalted hz).elim (fun h => absurd h hK) (fun h => absurd h hT)
end Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest
