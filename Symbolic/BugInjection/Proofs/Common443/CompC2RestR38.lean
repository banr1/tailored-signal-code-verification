/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2RestEntry38
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire
public import Symbolic.BugInjection.Proofs.Common443.CompFitsNames
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Bytes
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.Census443Memo
import Symbolic.DYBridge.DY.Bytes.Basic

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2RestR38
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRMemoKnown CompRNoBSC CompRPlantWire CompRX0NBSC38 CompRX0NBSC38Parts CompRX0NBSC38Wire CompRTag CompRI0TermInj CompRSplit38PairCore CompRSplit38UntaggedShape CompRNonInj38Census CompRQRestCensusZ CompC2RestCore CompC2Rest38 CompC2RestEntry38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open DY.Literal (literalToBytes) open DY.Concat (concat) open DY.KdfExtract (kdfExtract)
open DY.DiffieHellman DY.SymEnc DY.Trunc DY.TrWire DY.PQKem DY.Spqr DY.X25519
open DY.Libsignal.PQXDH (agree serializedIk PQXDHState AliceHandshakeOut pqxdhKdf pqxdhIkm)
open DY.Libsignal.TripleRatchet (TRState hkdfBlock1 hkdfBlock2 hkdfBlock3 createChain kdfCk trMsgKeys hmac computeMac)
def RVal (v : HwBytes) : Prop := NonInjOff v ∧ v ∉ x25519Vals
theorem rVal_of_len {v : HwBytes} (h32 : v.length ≠ 32) (h8 : v.length ≠ 8) : RVal v :=
  ⟨⟨fun h => absurd h h32, fun h => absurd h h8⟩, fun hv => h32 (x25519Vals_length v hv)⟩
theorem rVal_fillFresh_16_64 : RVal (fillFresh 16 64) :=
  rVal_of_len (by decide +kernel) (by decide +kernel)
theorem rVal_mem_kyberCtVals {v : HwBytes} (hv : v ∈ Census443Memo.kyberCtVals) : RVal v := by have hl := Census443Memo.length_of_mem_kyberCtVals hv; exact rVal_of_len (by omega) (by omega)
theorem rVal_compKyberSs2 : RVal compKyberSs2 := by unfold RVal NonInjOff KdfFree; decide +kernel
theorem gamma_symEnc_eq' (S : Sem) (g : Ghost) (k iv m : Bytes) : gamma compI0 S g (symEnc k iv m) = compAesPerm (gamma compI0 S g k) ((gamma compI0 S g iv).take 16) (gamma compI0 S g m) := gamma_symEnc_compI0 S g k iv m
def RE (S : Sem) (g : Ghost) (x : Bytes × Bytes × HwBytes) : Prop := x.2.2 = gamma compI0 S g x.1 → RestEntry S g x
def RC (S : Sem) (g : Ghost) (t : Bytes) : Prop := MemoOK compI0 S g (RE S g) t
section HeadDisj
unseal Bytes
theorem x25519Key_dhPk (sk : Bytes) : x25519Key (dhPk sk) = dhPk sk :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq sk
private theorem not_isDh_of_view {b : Bytes} (hv : b.view? Dh.SubF = none) : ¬ IsDh b := by rintro ⟨p, s, rfl⟩; rw [BytesView.view_pack] at hv; cases hv
private theorem not_isTrunc8_of_view {b : Bytes} (hv : b.view? Trunc8.SubF = none) : ¬ IsTrunc8 b := by rintro ⟨a, rfl⟩; rw [show trunc8 a = ({ input := a } : Trunc8.SubF Bytes).pack from rfl, BytesView.view_pack] at hv; cases hv
theorem rr_not_isDh_dhPk (sk : Bytes) : ¬ IsDh (dhPk sk) := not_isDh_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Dh.SubF ({ sk := sk } : DhPk.SubF Bytes))
theorem rr_not_isDh_symEnc (k iv m : Bytes) : ¬ IsDh (symEnc k iv m) := not_isDh_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Dh.SubF ({ key := k, iv := iv, msg := m } : Enc.SubF Bytes))
theorem rr_not_isDh_randTerm (idx sz : Nat) : ¬ IsDh (randTerm idx sz) := not_isDh_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Dh.SubF ({ timestamp := idx, size := sz } : DY.Random.Random Bytes))
theorem rr_not_isDh_kemEncap_fst (pk e : Bytes) : ¬ IsDh (kemEncap pk e).1 := not_isDh_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Dh.SubF ({ pk := pk, entropy := e } : Encap.SubF Bytes))
theorem rr_not_isDh_kemEncap_snd (pk e : Bytes) : ¬ IsDh (kemEncap pk e).2 := not_isDh_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Dh.SubF ({ pk := pk, entropy := e } : SharedSecret.SubF Bytes))
theorem rr_not_isTrunc8_dhPk (sk : Bytes) : ¬ IsTrunc8 (dhPk sk) := not_isTrunc8_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Trunc8.SubF ({ sk := sk } : DhPk.SubF Bytes))
theorem rr_not_isTrunc8_dh_pack (p s : Bytes) : ¬ IsTrunc8 (({ pk := p, sk := s } : Dh.SubF Bytes).pack) := not_isTrunc8_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Trunc8.SubF ({ pk := p, sk := s } : Dh.SubF Bytes))
theorem rr_not_isTrunc8_symEnc (k iv m : Bytes) : ¬ IsTrunc8 (symEnc k iv m) := not_isTrunc8_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Trunc8.SubF ({ key := k, iv := iv, msg := m } : Enc.SubF Bytes))
theorem rr_not_isTrunc8_randTerm (idx sz : Nat) : ¬ IsTrunc8 (randTerm idx sz) := not_isTrunc8_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Trunc8.SubF ({ timestamp := idx, size := sz } : DY.Random.Random Bytes))
theorem rr_not_isTrunc8_kemEncap_fst (pk e : Bytes) : ¬ IsTrunc8 (kemEncap pk e).1 := not_isTrunc8_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Trunc8.SubF ({ pk := pk, entropy := e } : Encap.SubF Bytes))
theorem rr_not_isTrunc8_kemEncap_snd (pk e : Bytes) : ¬ IsTrunc8 (kemEncap pk e).2 := not_isTrunc8_of_view (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none Trunc8.SubF ({ pk := pk, entropy := e } : SharedSecret.SubF Bytes))
theorem rr_dh_pack_pk_eq {p s p' s' : Bytes} (h : (({ pk := p, sk := s } : Dh.SubF Bytes).pack) = (({ pk := p', sk := s' } : Dh.SubF Bytes).pack)) : p = p' := by
  have hv := congrArg (fun u : Bytes => u.view? Dh.SubF) h
  rw [BytesView.view_pack, BytesView.view_pack] at hv; injection hv with hsub; cases hsub; rfl
theorem rr_ai_concat (a c : Bytes) : assumedInjective (concat a c) = false :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq a c
theorem rr_ai_trWire (ver : UInt8) (rk : Bytes) (c pc : UInt32) (ct pq : Bytes) (ev : EncodingVariation) : assumedInjective (({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : TrWireMsg.SubF Bytes).pack) = false :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_trWire_pack_eq _
end HeadDisj
section Heads
variable {S : Sem} {g : Ghost}
theorem re_ni {x : Bytes × Bytes × HwBytes} (h : assumedInjective x.1 = false) : RE S g x := fun _ => restEntry_of_nonInj h
theorem re_kdf {x : Bytes × Bytes × HwBytes} {k m : Bytes} (hx : x.1 = kdfExtract k m) : RE S g x := fun _ => restEntry_of_kdf hx
theorem re_trunc8_kdf {x : Bytes × Bytes × HwBytes} {k m : Bytes} (hx : x.1 = trunc8 (kdfExtract k m)) : RE S g x := fun hv => restEntry_of_trunc8_kdf hx hv
theorem re_dhPk {x : Bytes × Bytes × HwBytes} {sk : Bytes} (hx : x.1 = dhPk sk) : RE S g x :=
  fun _ => ⟨hx ▸ dhPtNotLow_of_not_dh (rr_not_isDh_dhPk sk),
    fun hT => absurd (hx ▸ hT) (rr_not_isTrunc8_dhPk sk),
    fun _ _ hX => absurd (Or.inl ⟨sk, hx⟩) hX⟩
theorem re_dh_pack_dhPk {x : Bytes × Bytes × HwBytes} {q sk : Bytes} (hx : x.1 = ({ pk := dhPk q, sk := sk } : Dh.SubF Bytes).pack) : RE S g x :=
  fun _ => ⟨hx ▸ dhPtNotLow_of_dhPk (fun _ _ hps => ⟨q, (rr_dh_pack_pk_eq hps).symm⟩),
    fun hT => absurd (hx ▸ hT) (rr_not_isTrunc8_dh_pack _ _),
    fun _ _ hX => absurd (Or.inr ⟨_, _, hx⟩) hX⟩
theorem re_val {x : Bytes × Bytes × HwBytes} (hdh : ¬ IsDh x.1) (htr : ¬ IsTrunc8 x.1) (hval : RVal (gamma compI0 S g x.1)) : RE S g x :=
  fun hv => ⟨dhPtNotLow_of_not_dh hdh, fun hT => absurd hT htr, fun _ _ _ _ => hv ▸ hval⟩
end Heads
section Prim
variable {S : Sem} {g : Ghost}
theorem rc_lit (bs : ByteArray) : RC S g (literalToBytes bs) :=
  memoOK_lit (fun _ hx => re_ni (hx ▸ assumedInjective_lit bs))
theorem rc_randTerm {idx sz : Nat} (hval : RVal (gamma compI0 S g (randTerm idx sz))) : RC S g (randTerm idx sz) := by
  intro x hx; unfold gamma' randTerm at hx; rw [Bytes.rec_eq (gRandom g) (gAll compI0 S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx
  split_ifs at hx with hsz; · cases hx
  rcases List.mem_singleton.mp hx with rfl
  exact re_val (rr_not_isDh_randTerm idx sz) (rr_not_isTrunc8_randTerm idx sz) hval
theorem rc_concat {a c : Bytes} (ha : RC S g a) (hc : RC S g c) : RC S g (concat a c) :=
  memoOK_concat (fun _ hx => re_ni (hx ▸ rr_ai_concat a c)) ha hc
theorem rc_dhPk {sk : Bytes} (hsk : RC S g sk) : RC S g (dhPk sk) := memoOK_dhPk (fun _ hx => re_dhPk hx) hsk
theorem rc_of_dhPk {sk : Bytes} (h : RC S g (dhPk sk)) : RC S g sk := memoOK_dhPk_elim h
theorem rc_dh_pack_dhPk {q sk : Bytes} (hq : RC S g q) (hsk : RC S g sk) : RC S g (({ pk := dhPk q, sk := sk } : Dh.SubF Bytes).pack) :=
  memoOK_dh_pack (fun _ hx => re_dh_pack_dhPk hx) (rc_dhPk hq) hsk
theorem rc_dh_dhPk {q sk : Bytes} (hq : RC S g q) (hsk : RC S g sk) : RC S g (dh (dhPk q) sk) := by
  have hv := Bytes.pack_view? DhPk.SubF (dhPk q); simp only [dh, CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; have hv' : dhPk sk2 = dhPk q := hv; have hq' := rc_of_dhPk (hv'.symm ▸ rc_dhPk hq)
    split <;> [exact rc_dh_pack_dhPk hq' hsk; exact rc_dh_pack_dhPk hsk hq']
  · exact rc_dh_pack_dhPk hq hsk
theorem rc_agree_dhPk {q sk : Bytes} (hq : RC S g q) (hsk : RC S g sk) : RC S g (agree (dhPk q) sk) := by change RC S g (dh (x25519Key (dhPk q)) sk); rw [x25519Key_dhPk]; exact rc_dh_dhPk hq hsk
theorem rc_kdfExtract {a b : Bytes} (ha : RC S g a) (hb : RC S g b) : RC S g (kdfExtract a b) :=
  memoOK_kdfExtract (fun _ hx => re_kdf hx) ha hb
theorem rc_hmac {a b : Bytes} (ha : RC S g a) (hb : RC S g b) : RC S g (hmac a b) := rc_kdfExtract ha hb
theorem rc_hkdfBlock1 {prk info : Bytes} (hprk : RC S g prk) (hinfo : RC S g info) : RC S g (hkdfBlock1 prk info) := rc_hmac hprk (rc_concat hinfo (rc_lit _))
theorem rc_hkdfBlock2 {prk info : Bytes} (hprk : RC S g prk) (hinfo : RC S g info) : RC S g (hkdfBlock2 prk info) := rc_hmac hprk (rc_concat (rc_hkdfBlock1 hprk hinfo) (rc_concat hinfo (rc_lit _)))
theorem rc_hkdfBlock3 {prk info : Bytes} (hprk : RC S g prk) (hinfo : RC S g info) : RC S g (hkdfBlock3 prk info) := rc_hmac hprk (rc_concat (rc_hkdfBlock2 hprk hinfo) (rc_concat hinfo (rc_lit _)))
theorem rc_symEnc {k iv m : Bytes} (hval : RVal (gamma compI0 S g (symEnc k iv m))) (hk : RC S g k) (hiv : RC S g iv) (hm : RC S g m) : RC S g (symEnc k iv m) :=
  memoOK_symEnc (fun _ hx => re_val (hx ▸ rr_not_isDh_symEnc k iv m) (hx ▸ rr_not_isTrunc8_symEnc k iv m) (hx ▸ hval)) hk hiv hm
theorem rc_trunc8_kdf {k m : Bytes} (hk : RC S g k) (hm : RC S g m) : RC S g (trunc8 (kdfExtract k m)) :=
  memoOK_trunc8 (fun _ hx => re_trunc8_kdf hx) (rc_kdfExtract hk hm)
theorem rc_trWire {ver : UInt8} {rk ct pq : Bytes} {c pc : UInt32} {ev : EncodingVariation} (hrk : RC S g rk) (hct : RC S g ct) (hpq : RC S g pq) : RC S g (trWireMsg ver rk c pc ct pq ev) := by rw [show trWireMsg ver rk c pc ct pq ev = ({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : TrWireMsg.SubF Bytes).pack from rfl]; exact memoOK_trWire (fun _ hx => re_ni (hx ▸ rr_ai_trWire ver rk c pc ct pq ev)) hrk hct hpq
theorem rc_computeMac_trWire {mk ikS ikR rk ct pq : Bytes} {v : UInt8} {c pc : UInt32} {ev : EncodingVariation} (hmk : RC S g mk) (hikS : RC S g ikS) (hikR : RC S g ikR) (hrk : RC S g rk) (hct : RC S g ct) (hpq : RC S g pq) : RC S g (computeMac mk ikS ikR (trWireMsg v rk c pc ct pq ev)) := rc_trunc8_kdf hmk (rc_concat hikS (rc_concat hikR (rc_trWire hrk hct hpq)))
theorem rc_kemPk {sk : Bytes} (hsk : RC S g sk) : RC S g (kemPk sk) := memoOK_kemPk hsk
theorem rc_kemEncap_fst {pk e : Bytes} (hpk : RC S g pk) (he : RC S g e) : RC S g (kemEncap pk e).1 :=
  Census443Memo.memoOK_kemEncap_fst' (fun _ hx hv _ _ =>
    ⟨dhPtNotLow_of_not_dh (hx ▸ rr_not_isDh_kemEncap_fst pk e),
     fun hT => absurd (hx ▸ hT) (rr_not_isTrunc8_kemEncap_fst pk e),
     fun _ _ _ _ => hv ▸ rVal_mem_kyberCtVals (Census443Memo.compI0_kyberEncaps_take1568_mem _ _)⟩) hpk he
theorem rc_kemEncap_snd {pk e : Bytes} (hval : RVal (gamma compI0 S g (kemEncap pk e).2)) (hpk : RC S g pk) (he : RC S g e) : RC S g (kemEncap pk e).2 :=
  memoOK_kemEncap_snd (fun _ hx => re_val (hx ▸ rr_not_isDh_kemEncap_snd pk e) (hx ▸ rr_not_isTrunc8_kemEncap_snd pk e) (hx ▸ hval)) hpk he
theorem rc_spqrInit {a p : Bytes} (ha : RC S g a) (hp : RC S g p) : RC S g (spqrInit a p) := memoOK_spqrInit ha hp
theorem rc_spqrChainKey {a p idx : Bytes} (ha : RC S g a) (hp : RC S g p) (hidx : RC S g idx) : RC S g (spqrChainKey a p idx) := memoOK_spqrChainKey ha hp hidx
theorem rc_spqrSendState {st c : Bytes} (hst : RC S g st) (hc : RC S g c) : RC S g (spqrSend st c).1 := memoOK_spqrSendState hst hc
theorem rc_spqrSendKey {st c : Bytes} (hst : RC S g st) (hc : RC S g c) : RC S g (spqrSend st c).2.1 := by
  unfold spqrSend; dsimp only; have hp := Bytes.pack_view? InitState.SubF st
  cases hv : st.view? InitState.SubF with
  | none => exact memoOK_spqrSendKey_pack hst hc
  | some x =>
    rw [hv] at hp; rw [← hp] at hst; obtain ⟨hk, hpar⟩ := memoOK_spqrInit_elim hst; exact rc_spqrChainKey hk hpar (rc_lit _)
theorem rc_spqrSendMsg {st c : Bytes} (hst : RC S g st) (hc : RC S g c) : RC S g (spqrSend st c).2.2 := memoOK_spqrSendMsg hst hc
theorem rc_x25519Key {pk : Bytes} (h : RC S g pk) : RC S g (x25519Key pk) := memoOK_x25519Key h
theorem rc_serializedIk {ik : Bytes} (hik : RC S g ik) : RC S g (serializedIk ik) := rc_concat (rc_lit _) hik
theorem rc_createChain_dhPk {rk q sk : Bytes} (hrk : RC S g rk) (hq : RC S g q) (hsk : RC S g sk) : RC S g (createChain rk (dhPk q) sk).1 ∧ RC S g (createChain rk (dhPk q) sk).2 :=
  let hprk := rc_hmac hrk (rc_agree_dhPk hq hsk);
  ⟨rc_hkdfBlock1 hprk (rc_lit _), rc_hkdfBlock2 hprk (rc_lit _)⟩
theorem rc_kdfCk {ck : Bytes} (hck : RC S g ck) : RC S g (kdfCk ck).1 ∧ RC S g (kdfCk ck).2 := ⟨rc_hmac hck (rc_lit _), rc_hmac hck (rc_lit _)⟩
theorem rc_trMsgKeys {salt ck : Bytes} (hsalt : RC S g salt) (hck : RC S g ck) : let mk := trMsgKeys salt (kdfCk ck).2; RC S g mk.cipherKey ∧ RC S g mk.macKey ∧ RC S g mk.iv :=
  let hprk := rc_hmac hsalt (rc_kdfCk hck).2;
  ⟨rc_hkdfBlock1 hprk (rc_lit _), rc_hkdfBlock2 hprk (rc_lit _), rc_hkdfBlock3 hprk (rc_lit _)⟩
theorem rc_pqxdhKdf_none {dh1 dh2 dh3 ss : Bytes} (hdh1 : RC S g dh1) (hdh2 : RC S g dh2) (hdh3 : RC S g dh3) (hss : RC S g ss) : let keys := pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss); RC S g keys.rk ∧ RC S g keys.ck ∧ RC S g keys.pqr :=
  let hprk := rc_hmac (rc_lit _) (rc_concat (rc_lit _) (rc_concat hdh1 (rc_concat hdh2 (rc_concat hdh3 hss))));
  ⟨rc_hkdfBlock1 hprk (rc_lit _), rc_hkdfBlock2 hprk (rc_lit _), rc_hkdfBlock3 hprk (rc_lit _)⟩
theorem rc_serialize_local_pqxdh {ls : DY.PersistentLocalState.LocalState PQXDHState} (hsk : RC S g ls.state.sk) : RC S g (Comparse.serialize ls : Bytes) := CompRPreMemo38KdfCensus.memoOK_serialize_local_pqxdh rc_lit rc_concat hsk
end Prim
abbrev TRStateRC (S : Sem) (g : Ghost) (st : TRState) : Prop := CompRPreMemo38KdfCensus.TRStateMemoOK compI0 S g (RE S g) st
section TR
variable {S : Sem} {g : Ghost}
theorem rc_serialize_local_tr {ls : DY.PersistentLocalState.LocalState TRState} (hst : TRStateRC S g ls.state) : RC S g (Comparse.serialize ls : Bytes) := CompRPreMemo38KdfCensus.memoOK_serialize_local_tr rc_lit rc_concat hst
theorem rc_prefixTerms {r : Records} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, RC S g u) (hstates : ∀ ls ∈ storedStates r tr, RC S g (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, RC S g u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, RC S g u) : ∀ u ∈ prefixTerms r tr vis, RC S g u := CompRPreMemo38KdfCensus.memoOK_prefixTerms hsend hstates hsecrets hpt
theorem trStateRC_iniAliceStartState (tr : ExecTrace) (b : Participant) (o : AliceHandshakeOut) {spkSk : Bytes} (hspk_eq : o.spk = dhPk spkSk) (hspk_sk : RC S g spkSk) (hikA : RC S g o.ikA) (hikB : RC S g o.ikB) (hrk : RC S g o.keys.rk) (hck : RC S g o.keys.ck) (hpqr : RC S g o.keys.pqr) (hdhsA : RC S g (randTerm (tr.length + 2) 32)) : TRStateRC S g (iniAliceStartState tr b o) := by
  have hcc : RC S g (createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).1 ∧ RC S g (createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).2 := hspk_eq ▸ rc_createChain_dhPk hrk hspk_sk hdhsA
  refine ⟨rc_serializedIk hikA, rc_serializedIk hikB, hcc.1, hdhsA, hcc.2,
    rc_concat (rc_dhPk hdhsA) hrk, rc_spqrInit hpqr (rc_lit _), fun d hd => ?_⟩
  rcases List.mem_singleton.mp hd with rfl; exact ⟨hspk_eq ▸ rc_dhPk hspk_sk, hck⟩
theorem trStateRC_encSt (tr₂ : ExecTrace) {stA : TRState} (cl : Nat) (hst : TRStateRC S g stA) (hc : RC S g (randTerm (tr₂.length + 1) cl)) : TRStateRC S g (encSt tr₂ stA cl) := ⟨hst.myIk, hst.peerIk, hst.rk, hst.dhs, (rc_kdfCk hst.cks).1, hst.sid, rc_spqrSendState hst.spqr hc, hst.recv⟩
end TR
theorem rc_randTerm_of_eq {S : Sem} {g : Ghost} {idx sz : Nat} {v : HwBytes} (h : gamma compI0 S g (randTerm idx sz) = v) (hv : RVal v) : RC S g (randTerm idx sz) := rc_randTerm (h ▸ hv)
theorem gamma_setupSecret_4' {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) (hc : Compat compI0 r S g) : gamma compI0 S g (setupSecret r 4) = secretBytes r 4 := by
  rw [CompPrefixInvBundle.setupSecret_4 hNe, CompRX0Bytes.gamma_randTerm']; simp only [show (64 : Nat) ≠ 0 by decide, ↓reduceIte]
  have hm : ((16, 64) : Nat × Nat) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; simp
  rw [hc.1 _ hm]; unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
section Alice
variable {S : Sem} {g : Ghost}
theorem rc_aliceOut {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) (h0 : RC S g (randTerm 0 32)) (h5 : RC S g (randTerm 5 32)) (h10 : RC S g (randTerm 10 32)) (h16 : RC S g (randTerm 16 64)) (hek : RC S g (randTerm tr₁.length 32)) (hent : RC S g (randTerm (tr₁.length + 1) 32)) (hss_val : RVal (gamma compI0 S g (kemEncap (kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2)) : let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; RC S g o.ikA ∧ RC S g o.ikB ∧ RC S g o.spk ∧ RC S g o.ek ∧ RC S g o.ct ∧
      RC S g o.keys.rk ∧ RC S g o.keys.ck ∧ RC S g o.keys.pqr := by
  dsimp only; rw [CompSetupSecrecy.setupSecret_0 hNe, CompSetupSecrecy.setupPublic_2 hNe, CompSetupSecrecy.setupPublic_4 hNe, CompSetupSecrecy.setupPublic_6 hNe]; have hpub6 : RC S g (kemPk (randTerm 16 64)) := rc_kemPk h16
  rcases rc_pqxdhKdf_none (rc_agree_dhPk h10 h0) (rc_agree_dhPk h5 hek)
    (rc_agree_dhPk h10 hek) (rc_kemEncap_snd hss_val hpub6 hent) with ⟨hrk, hck, hpqr⟩
  exact ⟨rc_dhPk h0, rc_dhPk h5, rc_dhPk h10, rc_dhPk hek, rc_kemEncap_fst hpub6 hent, hrk, hck, hpqr⟩
theorem trStateRC_stA {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) (h0 : RC S g (randTerm 0 32)) (h5 : RC S g (randTerm 5 32)) (h10 : RC S g (randTerm 10 32)) (h16 : RC S g (randTerm 16 64)) (hek : RC S g (randTerm tr₁.length 32)) (hent : RC S g (randTerm (tr₁.length + 1) 32)) (hss_val : RVal (gamma compI0 S g (kemEncap (kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2)) (hdhs : RC S g (randTerm (tr₁.length + 2) 32)) : TRStateRC S g (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) := by obtain ⟨hikA, hikB, _, _, _, hrk, hck, hpqr⟩ := rc_aliceOut hNe tr₁ h0 h5 h10 h16 hek hent hss_val; exact trStateRC_iniAliceStartState tr₁ r.bob _ (CompSetupSecrecy.setupPublic_4 hNe) h10 hikA hikB hrk hck hpqr hdhs
end Alice
end Symbolic.BugInjection.Proofs.Common443.CompC2RestR38
