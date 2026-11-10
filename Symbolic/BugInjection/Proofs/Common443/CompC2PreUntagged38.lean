/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged
public import Symbolic.BugInjection.Proofs.Common443.CompFitsNames
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma
public import Symbolic.BugInjection.Proofs.Common443.Census443Memo
public import Symbolic.BugInjection.Proofs.Common443.CompPlant
public import Symbolic.BugInjection.Proofs.Common443.CompRBobInit
public import Symbolic.BugInjection.Proofs.Common443.CompRX0Top

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPlant CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRMemoKnown CompRNoBSC CompRX0Top CompRI0TermInj CompRNbscTable CompRNbsc38MacKey CompRSplit38Untagged CompRSplit38ZPin CompRSplit38ZTag CompRSplit38TaggedAgree Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open DY.Literal (literalToBytes) open DY.Concat (concat) open DY.KdfExtract (kdfExtract)
open DY.DiffieHellman DY.SymEnc DY.Trunc DY.TrWire DY.PQKem DY.Spqr
open DY.Libsignal.PQXDH (agree serializedIk PQXDHState AliceHandshakeOut pqxdhKdf pqxdhIkm pqxdhLabel)
open DY.Libsignal.TripleRatchet (TRState hkdfBlock1 hkdfBlock2 hkdfBlock3 createChain kdfCk trMsgKeys hmac computeMac zeroSalt litByte)
def PreNX (x : Bytes × Bytes × HwBytes) : Prop := assumedInjective x.1 = true → x.2.2 ∉ x25519Vals → x.2.2.take 4 ≠ compTag4
def PreNXOK (S : Sem) (g : Ghost) (t : Bytes) : Prop := MemoOK compI0 S g PreNX t
section NotInj
theorem ai_concat (a c : Bytes) : assumedInjective (concat a c) = false :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq a c
theorem ai_trWire (ver : UInt8) (rk : Bytes) (c pc : UInt32) (ct pq : Bytes) (ev : EncodingVariation) : assumedInjective (trWireMsg ver rk c pc ct pq ev) = false :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_trWire_eq ver rk c pc ct pq ev
end NotInj
section Prim
variable {S : Sem} {g : Ghost}
private theorem preNX_of_ni {b : Bytes} (hb : assumedInjective b = false) : ∀ x : Bytes × Bytes × HwBytes, x.1 = b → PreNX x :=
  fun _ hx hai => by rw [hx, hb] at hai; cases hai
theorem preNXOK_lit (bs : ByteArray) : PreNXOK S g (literalToBytes bs) :=
  memoOK_lit_ni bs (fun _ hni hai => by rw [hni] at hai; cases hai)
theorem preNXOK_concat {a c : Bytes} (ha : PreNXOK S g a) (hc : PreNXOK S g c) : PreNXOK S g (concat a c) := memoOK_concat (preNX_of_ni (ai_concat a c)) ha hc
theorem preNXOK_dhPk {sk : Bytes} (hsk : PreNXOK S g sk) : PreNXOK S g (dhPk sk) := by
  intro x hx; unfold gamma' at hx; rw [show dhPk sk = ({ sk := sk } : DhPk.SubF Bytes).pack from rfl, Bytes.rec_eq (gDhPk compI0) (gAll compI0 S g)] at hx; simp only [gDhPk, concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, CompPlant.bytes_rec_gAll] at hx
  rcases hx with rfl | hxsk <;> [exact fun _ hnx => absurd (compLookupPub_mem _) hnx; exact hsk x hxsk]
theorem preNXOK_of_dhPk {sk : Bytes} (h : PreNXOK S g (dhPk sk)) : PreNXOK S g sk := memoOK_dhPk_elim h
theorem preNXOK_dh_pack {pk sk : Bytes} (hpk : PreNXOK S g pk) (hsk : PreNXOK S g sk) : PreNXOK S g (({ pk := pk, sk := sk } : Dh.SubF Bytes).pack) := by
  intro x hx; unfold gamma' at hx; rw [Bytes.rec_eq (gDh compI0) (gAll compI0 S g)] at hx; simp only [gDh, concretizeDh, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, CompPlant.bytes_rec_gAll] at hx
  rcases hx with rfl | hxpk | hxsk <;>
    [exact fun _ hnx => absurd (compLookupDh_mem _ _) hnx; exact hpk x hxpk; exact hsk x hxsk]
theorem preNXOK_dh {pk sk : Bytes} (hpk : PreNXOK S g pk) (hsk : PreNXOK S g sk) : PreNXOK S g (dh pk sk) := by
  have hv := Bytes.pack_view? DhPk.SubF pk; simp only [dh, CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    split <;> [exact preNXOK_dh_pack hpk hsk; exact preNXOK_dh_pack (preNXOK_dhPk hsk) (preNXOK_of_dhPk hpk)]
  · exact preNXOK_dh_pack hpk hsk
theorem preNXOK_agree {pk sk : Bytes} (hpk : PreNXOK S g pk) (hsk : PreNXOK S g sk) : PreNXOK S g (agree pk sk) := preNXOK_dh (memoOK_x25519Key hpk) hsk
theorem preNXOK_randTerm {idx sz : Nat} (hu : (gamma compI0 S g (randTerm idx sz)).take 4 ≠ compTag4) : PreNXOK S g (randTerm idx sz) := by
  intro x hx; have hval := (CompRPreMemoSound.memo_sound compI0 S g (randTerm idx sz) hx).2; unfold gamma' randTerm at hx; rw [Bytes.rec_eq (gRandom g) (gAll compI0 S g)] at hx
  dsimp only [gRandom, concretizeRandom] at hx; split_ifs at hx with hsz; · cases hx
  rcases List.mem_singleton.mp hx with rfl; exact fun _ _ => hval ▸ hu
theorem preNXOK_kdfExtract {a b : Bytes} (hu : (gamma compI0 S g (kdfExtract a b)).take 4 ≠ compTag4) (ha : PreNXOK S g a) (hb : PreNXOK S g b) : PreNXOK S g (kdfExtract a b) := by
  intro x hx; have hval := (CompRPreMemoSound.memo_sound compI0 S g (kdfExtract a b) hx).2
  exact memoOK_kdfExtract (P := fun y => y.2.2 = gamma compI0 S g y.1 → PreNX y)
    (fun _ hy hv _ _ => hv ▸ hy ▸ hu) (fun y hy _ => ha y hy) (fun y hy _ => hb y hy) x hx hval
theorem preNXOK_hmac {a b : Bytes} (hu : (gamma compI0 S g (hmac a b)).take 4 ≠ compTag4) (ha : PreNXOK S g a) (hb : PreNXOK S g b) : PreNXOK S g (hmac a b) := preNXOK_kdfExtract hu ha hb
theorem preNXOK_symEnc {k iv m : Bytes} (hu : (gamma compI0 S g (symEnc k iv m)).take 4 ≠ compTag4) (hk : PreNXOK S g k) (hiv : PreNXOK S g iv) (hm : PreNXOK S g m) : PreNXOK S g (symEnc k iv m) := by
  intro x hx; have hval := (CompRPreMemoSound.memo_sound compI0 S g (symEnc k iv m) hx).2
  exact memoOK_symEnc (P := fun y => y.2.2 = gamma compI0 S g y.1 → PreNX y)
    (fun _ hy hv _ _ => hv ▸ hy ▸ hu) (fun y hy _ => hk y hy) (fun y hy _ => hiv y hy)
    (fun y hy _ => hm y hy) x hx hval
theorem preNXOK_trunc8 {a : Bytes} (hu : (gamma compI0 S g a).take 4 ≠ compTag4) (ha : PreNXOK S g a) : PreNXOK S g (trunc8 a) := by
  intro x hx; unfold gamma' at hx; rw [show trunc8 a = ({ input := a } : Trunc8.SubF Bytes).pack from rfl, Bytes.rec_eq gTrunc0 (gAll compI0 S g)] at hx; simp only [gTrunc0, concretizeTrunc, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, CompPlant.bytes_rec_gAll] at hx
  rcases hx with rfl | hxa
  · intro _ _; change ((gamma compI0 S g a).take 8).take 4 ≠ compTag4; rw [take4_take8]; exact hu
  · exact ha x hxa
theorem preNXOK_trWire {ver : UInt8} {rk ct pq : Bytes} {c pc : UInt32} {ev : EncodingVariation} (hrk : PreNXOK S g rk) (hct : PreNXOK S g ct) (hpq : PreNXOK S g pq) : PreNXOK S g (trWireMsg ver rk c pc ct pq ev) := by rw [show trWireMsg ver rk c pc ct pq ev = ({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc, ciphertext := ct, pqRatchet := pq, encodingVariation := ev } : TrWireMsg.SubF Bytes).pack from rfl]; exact CompRMemoKnown.memoOK_trWire (preNX_of_ni (ai_trWire ver rk c pc ct pq ev)) hrk hct hpq
theorem preNXOK_kemPk {sk : Bytes} (hsk : PreNXOK S g sk) : PreNXOK S g (kemPk sk) := memoOK_kemPk hsk
theorem preNXOK_kemEncap_fst {pk e : Bytes} (hu : (gamma compI0 S g (kemEncap pk e).1).take 4 ≠ compTag4) (hpk : PreNXOK S g pk) (he : PreNXOK S g e) : PreNXOK S g (kemEncap pk e).1 :=
  Census443Memo.memoOK_kemEncap_fst' (fun _ _ hv h32 _ _ => by
    rw [Census443Memo.gamma_kemEncap_fst_eq h32] at hu; rw [hv]; exact hu) hpk he
theorem preNXOK_kemEncap_snd {pk e : Bytes} (hu : (gamma compI0 S g (kemEncap pk e).2).take 4 ≠ compTag4) (hpk : PreNXOK S g pk) (he : PreNXOK S g e) : PreNXOK S g (kemEncap pk e).2 :=
  Census443Memo.memoOK_kemEncap_snd' (fun _ _ hv h32 _ _ => by
    rw [Census443Memo.gamma_kemEncap_snd_eq h32] at hu; rw [hv]; exact hu) hpk he
theorem preNXOK_spqrInit {a p : Bytes} (ha : PreNXOK S g a) (hp : PreNXOK S g p) : PreNXOK S g (spqrInit a p) := memoOK_spqrInit ha hp
theorem preNXOK_spqrChainKey {a p idx : Bytes} (ha : PreNXOK S g a) (hp : PreNXOK S g p) (hidx : PreNXOK S g idx) : PreNXOK S g (spqrChainKey a p idx) := memoOK_spqrChainKey ha hp hidx
theorem preNXOK_spqrSendState {st c : Bytes} (hst : PreNXOK S g st) (hc : PreNXOK S g c) : PreNXOK S g (spqrSend st c).1 := memoOK_spqrSendState hst hc
theorem preNXOK_spqrSendMsg {st c : Bytes} (hst : PreNXOK S g st) (hc : PreNXOK S g c) : PreNXOK S g (spqrSend st c).2.2 := memoOK_spqrSendMsg hst hc
theorem preNXOK_serializedIk {ik : Bytes} (hik : PreNXOK S g ik) : PreNXOK S g (serializedIk ik) := preNXOK_concat (preNXOK_lit _) hik
theorem preNXOK_serialize_local_pqxdh {ls : DY.PersistentLocalState.LocalState PQXDHState} (hsk : PreNXOK S g ls.state.sk) : PreNXOK S g (Comparse.serialize ls : Bytes) := CompRPreMemo38KdfCensus.memoOK_serialize_local_pqxdh preNXOK_lit preNXOK_concat hsk
abbrev TRStateNX (S : Sem) (g : Ghost) (st : TRState) : Prop := CompRPreMemo38KdfCensus.TRStateMemoOK compI0 S g PreNX st
theorem preNXOK_serialize_local_tr {ls : DY.PersistentLocalState.LocalState TRState} (hst : TRStateNX S g ls.state) : PreNXOK S g (Comparse.serialize ls : Bytes) := CompRPreMemo38KdfCensus.memoOK_serialize_local_tr preNXOK_lit preNXOK_concat hst
theorem preNXOK_prefixTerms {r : Records} {tr : ExecTrace} {vis : List VisEntry} (hsend : ∀ v ∈ vis, v.kind = .send → ∀ u ∈ v.terms, PreNXOK S g u) (hstates : ∀ ls ∈ storedStates r tr, PreNXOK S g (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets tr, PreNXOK S g u) (hpt : ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, PreNXOK S g u) : ∀ u ∈ prefixTerms r tr vis, PreNXOK S g u := CompRPreMemo38KdfCensus.memoOK_prefixTerms hsend hstates hsecrets hpt
end Prim
theorem ws_aliceId_untagged : Witnesses.Cheval26WeakState.setup.aliceId.take 4 ≠ compTag4 := by decide +kernel
theorem ws_bobId_untagged : Witnesses.Cheval26WeakState.setup.bobId.take 4 ≠ compTag4 := by decide +kernel
theorem ws_spk_untagged : Witnesses.Cheval26WeakState.setup.spk.take 4 ≠ compTag4 := by decide +kernel
theorem fillFresh_16_64_untagged : (fillFresh 16 64).take 4 ≠ compTag4 := by decide +kernel
theorem gamma_setupSecret_4 {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) (hc : Compat compI0 r S g) : gamma compI0 S g (setupSecret r 4) = secretBytes r 4 := by
  rw [CompPrefixInvBundle.setupSecret_4 hNe, CompRX0Bytes.gamma_randTerm']; simp only [show (64 : Nat) ≠ 0 by decide, ↓reduceIte]
  have hm : ((16, 64) : Nat × Nat) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; simp
  rw [hc.1 _ hm]; unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe]; cases r.withOpk <;> rfl
section Composite
variable {S : Sem} {g : Ghost}
theorem preNXOK_hkdfBlock1 {prk info : Bytes} (hu1 : (gamma compI0 S g (hkdfBlock1 prk info)).take 4 ≠ compTag4) (hprk : PreNXOK S g prk) (hinfo : PreNXOK S g info) : PreNXOK S g (hkdfBlock1 prk info) := preNXOK_hmac hu1 hprk (preNXOK_concat hinfo (preNXOK_lit _))
theorem preNXOK_hkdfBlock2 {prk info : Bytes} (hu1 : (gamma compI0 S g (hkdfBlock1 prk info)).take 4 ≠ compTag4) (hu2 : (gamma compI0 S g (hkdfBlock2 prk info)).take 4 ≠ compTag4) (hprk : PreNXOK S g prk) (hinfo : PreNXOK S g info) : PreNXOK S g (hkdfBlock2 prk info) := preNXOK_hmac hu2 hprk (preNXOK_concat (preNXOK_hkdfBlock1 hu1 hprk hinfo) (preNXOK_concat hinfo (preNXOK_lit _)))
theorem preNXOK_hkdfBlock3 {prk info : Bytes} (hu1 : (gamma compI0 S g (hkdfBlock1 prk info)).take 4 ≠ compTag4) (hu2 : (gamma compI0 S g (hkdfBlock2 prk info)).take 4 ≠ compTag4) (hu3 : (gamma compI0 S g (hkdfBlock3 prk info)).take 4 ≠ compTag4) (hprk : PreNXOK S g prk) (hinfo : PreNXOK S g info) : PreNXOK S g (hkdfBlock3 prk info) := preNXOK_hmac hu3 hprk (preNXOK_concat (preNXOK_hkdfBlock2 hu1 hu2 hprk hinfo) (preNXOK_concat hinfo (preNXOK_lit _)))
theorem preNXOK_createChain {rk pk sk : Bytes} (hprk : (gamma compI0 S g (hmac rk (agree pk sk))).take 4 ≠ compTag4) (hrk' : (gamma compI0 S g (createChain rk pk sk).1).take 4 ≠ compTag4) (hck' : (gamma compI0 S g (createChain rk pk sk).2).take 4 ≠ compTag4) (hrk : PreNXOK S g rk) (hpk : PreNXOK S g pk) (hsk : PreNXOK S g sk) : PreNXOK S g (createChain rk pk sk).1 ∧ PreNXOK S g (createChain rk pk sk).2 :=
  let hprk_ok := preNXOK_hmac hprk hrk (preNXOK_agree hpk hsk);
  ⟨preNXOK_hkdfBlock1 hrk' hprk_ok (preNXOK_lit _), preNXOK_hkdfBlock2 hrk' hck' hprk_ok (preNXOK_lit _)⟩
theorem preNXOK_kdfCk_fst {ck : Bytes} (hu1 : (gamma compI0 S g (kdfCk ck).1).take 4 ≠ compTag4) (hck : PreNXOK S g ck) : PreNXOK S g (kdfCk ck).1 := preNXOK_hmac hu1 hck (preNXOK_lit _)
theorem preNXOK_kdfCk_snd {ck : Bytes} (hu2 : (gamma compI0 S g (kdfCk ck).2).take 4 ≠ compTag4) (hck : PreNXOK S g ck) : PreNXOK S g (kdfCk ck).2 := preNXOK_hmac hu2 hck (preNXOK_lit _)
theorem preNXOK_trMsgKeys {salt ck : Bytes} (hseed : (gamma compI0 S g (kdfCk ck).2).take 4 ≠ compTag4) (hprk : (gamma compI0 S g (hmac salt (kdfCk ck).2)).take 4 ≠ compTag4) (hckey : (gamma compI0 S g (trMsgKeys salt (kdfCk ck).2).cipherKey).take 4 ≠ compTag4) (hmkey : (gamma compI0 S g (trMsgKeys salt (kdfCk ck).2).macKey).take 4 ≠ compTag4) (hiv : (gamma compI0 S g (trMsgKeys salt (kdfCk ck).2).iv).take 4 ≠ compTag4) (hsalt : PreNXOK S g salt) (hck : PreNXOK S g ck) : let mk := trMsgKeys salt (kdfCk ck).2; PreNXOK S g mk.cipherKey ∧ PreNXOK S g mk.macKey ∧ PreNXOK S g mk.iv :=
  let hprk_ok := preNXOK_hmac hprk hsalt (preNXOK_kdfCk_snd hseed hck);
  ⟨preNXOK_hkdfBlock1 hckey hprk_ok (preNXOK_lit _), preNXOK_hkdfBlock2 hckey hmkey hprk_ok (preNXOK_lit _), preNXOK_hkdfBlock3 hckey hmkey hiv hprk_ok (preNXOK_lit _)⟩
theorem preNXOK_computeMac_trWire {mk ikS ikR rk ct pq : Bytes} {v : UInt8} {c pc : UInt32} {ev : EncodingVariation} (hu : (gamma compI0 S g (hmac mk (concat ikS (concat ikR (trWireMsg v rk c pc ct pq ev))))).take 4 ≠ compTag4) (hmk : PreNXOK S g mk) (hikS : PreNXOK S g ikS) (hikR : PreNXOK S g ikR) (hrk : PreNXOK S g rk) (hct : PreNXOK S g ct) (hpq : PreNXOK S g pq) : PreNXOK S g (computeMac mk ikS ikR (trWireMsg v rk c pc ct pq ev)) := preNXOK_trunc8 hu (preNXOK_hmac hu hmk (preNXOK_concat hikS (preNXOK_concat hikR (preNXOK_trWire hrk hct hpq))))
theorem preNXOK_pqxdhKdf_none {dh1 dh2 dh3 ss : Bytes} (hprk : (gamma compI0 S g (hmac zeroSalt (pqxdhIkm dh1 dh2 dh3 none ss))).take 4 ≠ compTag4) (hrk : (gamma compI0 S g (pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss)).rk).take 4 ≠ compTag4) (hck : (gamma compI0 S g (pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss)).ck).take 4 ≠ compTag4) (hpqr : (gamma compI0 S g (pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss)).pqr).take 4 ≠ compTag4) (hdh1 : PreNXOK S g dh1) (hdh2 : PreNXOK S g dh2) (hdh3 : PreNXOK S g dh3) (hss : PreNXOK S g ss) : let keys := pqxdhKdf (pqxdhIkm dh1 dh2 dh3 none ss); PreNXOK S g keys.rk ∧ PreNXOK S g keys.ck ∧ PreNXOK S g keys.pqr :=
  let hprk_ok := preNXOK_hmac hprk (preNXOK_lit _)
    (preNXOK_concat (preNXOK_lit _) (preNXOK_concat hdh1 (preNXOK_concat hdh2 (preNXOK_concat hdh3 hss))));
  ⟨preNXOK_hkdfBlock1 hrk hprk_ok (preNXOK_lit _), preNXOK_hkdfBlock2 hrk hck hprk_ok (preNXOK_lit _), preNXOK_hkdfBlock3 hrk hck hpqr hprk_ok (preNXOK_lit _)⟩
end Composite
namespace Lit
theorem gamma_litByte0 {S : Sem} {g : Ghost} (b : UInt8) : gamma compI0 S g (litByte b) = [b.toBitVec] := by unfold litByte; rw [CompRBobInit.gamma_lit0]; rfl
theorem gamma_pqxdhLabel0 {S : Sem} {g : Ghost} : gamma compI0 S g pqxdhLabel = ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8 := by unfold pqxdhLabel DY.Libsignal.TripleRatchet.lit; rw [CompRBobInit.gamma_lit0]
theorem gamma_whisperRatchet0 {S : Sem} {g : Ghost} : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") = ofByteArray "WhisperRatchet".toUTF8 := by unfold DY.Libsignal.TripleRatchet.lit; rw [CompRBobInit.gamma_lit0]
theorem gamma_whisperMessageKeys0 {S : Sem} {g : Ghost} : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") = ofByteArray "WhisperMessageKeys".toUTF8 := by unfold DY.Libsignal.TripleRatchet.lit; rw [CompRBobInit.gamma_lit0]
theorem gamma_hkdfBlock10 {S : Sem} {g : Ghost} (prk info : Bytes) : gamma compI0 S g (hkdfBlock1 prk info) = hmacWith F0 (gamma compI0 S g prk) (gamma compI0 S g info ++ [0x01#8]) := by unfold hkdfBlock1; rw [CompRBobInit.gamma_hmac0, CompRBobInit.gamma_concat0, gamma_litByte0]; rfl
end Lit
theorem gamma_hkdfBlock2_eq {S : Sem} {g : Ghost} (prk info : Bytes) : gamma compI0 S g (hkdfBlock2 prk info) = hmacWith F0 (gamma compI0 S g prk) (gamma compI0 S g (hkdfBlock1 prk info) ++ (gamma compI0 S g info ++ [0x02#8])) := by unfold hkdfBlock2; rw [CompRBobInit.gamma_hmac0, CompRBobInit.gamma_concat0, CompRBobInit.gamma_concat0, Lit.gamma_litByte0]; rfl
theorem gamma_hkdfBlock3_eq {S : Sem} {g : Ghost} (prk info : Bytes) : gamma compI0 S g (hkdfBlock3 prk info) = hmacWith F0 (gamma compI0 S g prk) (gamma compI0 S g (hkdfBlock2 prk info) ++ (gamma compI0 S g info ++ [0x03#8])) := by unfold hkdfBlock3; rw [CompRBobInit.gamma_hmac0, CompRBobInit.gamma_concat0, CompRBobInit.gamma_concat0, Lit.gamma_litByte0]; rfl
abbrev iniAliceIkm (tr₁ : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) : Bytes :=
  let ek := randTerm tr₁.length 32;
  pqxdhIkm (agree spkPk ikA) (agree ikBPk ek) (agree spkPk ek) none (kemEncap pqPk (randTerm (tr₁.length + 1) 32)).2
theorem iniAliceOut_keys_eq (tr₁ : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) : (iniAliceOut tr₁ ikA ikBPk spkPk pqPk none).keys = pqxdhKdf (iniAliceIkm tr₁ ikA ikBPk spkPk pqPk) := rfl
structure Split38KdfPins (S : Sem) (g : Ghost) (tr₁ tr₂ : ExecTrace) (b : Participant)
    (o : AliceHandshakeOut) (ikm : Bytes) (cl : Nat) : Prop where
  hpqPrk : (gamma compI0 S g (pqxdhPrk ikm)).take 4 ≠ compTag4
  hrk0 : (gamma compI0 S g (pqxdhKdf ikm).rk).take 4 ≠ compTag4
  hck0 : (gamma compI0 S g (pqxdhKdf ikm).ck).take 4 ≠ compTag4
  hpqr0 : (gamma compI0 S g (pqxdhKdf ikm).pqr).take 4 ≠ compTag4
  hchainPrk : (gamma compI0 S g (iniChainPrk tr₁ o)).take 4 ≠ compTag4
  hstARk : (gamma compI0 S g (iniAliceStartState tr₁ b o).rk).take 4 ≠ compTag4
  hcks0 : (gamma compI0 S g (iniAliceStartState tr₁ b o).cks).take 4 ≠ compTag4
  hcks1 : (gamma compI0 S g (kdfCk (iniAliceStartState tr₁ b o).cks).1).take 4 ≠ compTag4
  hseed : (gamma compI0 S g (kdfCk (iniAliceStartState tr₁ b o).cks).2).take 4 ≠ compTag4
  hencPrk : (gamma compI0 S g (encPrk tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))).take 4 ≠ compTag4
  hcipherKey : (gamma compI0 S g (encKeys tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)).cipherKey).take 4 ≠ compTag4
  hiv : (gamma compI0 S g (encKeys tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)).iv).take 4 ≠ compTag4
theorem pqxdhKdf_rk_eq (ikm : Bytes) : (pqxdhKdf ikm).rk = hkdfBlock1 (pqxdhPrk ikm) pqxdhLabel := rfl
theorem pqxdhKdf_ck_eq (ikm : Bytes) : (pqxdhKdf ikm).ck = hkdfBlock2 (pqxdhPrk ikm) pqxdhLabel := rfl
theorem pqxdhKdf_pqr_eq (ikm : Bytes) : (pqxdhKdf ikm).pqr = hkdfBlock3 (pqxdhPrk ikm) pqxdhLabel := rfl
theorem iniAliceStartState_rk_eq (tr₁ : ExecTrace) (b : Participant) (o : AliceHandshakeOut) : (iniAliceStartState tr₁ b o).rk = hkdfBlock1 (iniChainPrk tr₁ o) (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
theorem encKeys_cipherKey_eq (tr₂ : ExecTrace) (stA : TRState) (cl pq : Nat) : (encKeys tr₂ stA cl pq).cipherKey = hkdfBlock1 (encPrk tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") := rfl
theorem encKeys_macKey_eq (tr₂ : ExecTrace) (stA : TRState) (cl pq : Nat) : (encKeys tr₂ stA cl pq).macKey = hkdfBlock2 (encPrk tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") := rfl
theorem encKeys_iv_eq (tr₂ : ExecTrace) (stA : TRState) (cl pq : Nat) : (encKeys tr₂ stA cl pq).iv = hkdfBlock3 (encPrk tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") := rfl
theorem preNXOK_iniAliceOut {S : Sem} {g : Ghost} (tr₁ : ExecTrace) (ikA ikBPk spkPk pqPk : Bytes) (hikA : PreNXOK S g ikA) (hikB : PreNXOK S g ikBPk) (hspk : PreNXOK S g spkPk) (hpq : PreNXOK S g pqPk) (hb0 : (gamma compI0 S g (randTerm tr₁.length 32)).take 4 ≠ compTag4) (he1 : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).take 4 ≠ compTag4) (hpqPrk : (gamma compI0 S g (pqxdhPrk (iniAliceIkm tr₁ ikA ikBPk spkPk pqPk))).take 4 ≠ compTag4) (hrk0 : (gamma compI0 S g (pqxdhKdf (iniAliceIkm tr₁ ikA ikBPk spkPk pqPk)).rk).take 4 ≠ compTag4) (hck0 : (gamma compI0 S g (pqxdhKdf (iniAliceIkm tr₁ ikA ikBPk spkPk pqPk)).ck).take 4 ≠ compTag4) (hpqr0 : (gamma compI0 S g (pqxdhKdf (iniAliceIkm tr₁ ikA ikBPk spkPk pqPk)).pqr).take 4 ≠ compTag4) (hct : (gamma compI0 S g (kemEncap pqPk (randTerm (tr₁.length + 1) 32)).1).take 4 ≠ compTag4) (hss : (gamma compI0 S g (kemEncap pqPk (randTerm (tr₁.length + 1) 32)).2).take 4 ≠ compTag4) : let o := iniAliceOut tr₁ ikA ikBPk spkPk pqPk none; PreNXOK S g o.ikA ∧ PreNXOK S g o.ikB ∧ PreNXOK S g o.spk ∧ PreNXOK S g o.ek ∧ PreNXOK S g o.ct ∧
      PreNXOK S g o.keys.rk ∧ PreNXOK S g o.keys.ck ∧ PreNXOK S g o.keys.pqr := by
  dsimp only; have hek_r : PreNXOK S g (randTerm tr₁.length 32) := preNXOK_randTerm hb0; have hent_r : PreNXOK S g (randTerm (tr₁.length + 1) 32) := preNXOK_randTerm he1
  rcases preNXOK_pqxdhKdf_none hpqPrk hrk0 hck0 hpqr0 (preNXOK_agree hspk hikA) (preNXOK_agree hikB hek_r)
    (preNXOK_agree hspk hek_r) (preNXOK_kemEncap_snd hss hpq hent_r) with ⟨hrk, hck, hpqr⟩
  exact ⟨preNXOK_dhPk hikA, hikB, hspk, preNXOK_dhPk hek_r, preNXOK_kemEncap_fst hct hpq hent_r, hrk, hck, hpqr⟩
theorem trStateNX_iniAliceStartState {S : Sem} {g : Ghost} (tr₁ : ExecTrace) (b : Participant) (o : AliceHandshakeOut) (hchainPrk : (gamma compI0 S g (iniChainPrk tr₁ o)).take 4 ≠ compTag4) (hdhs : (gamma compI0 S g (randTerm (tr₁.length + 2) 32)).take 4 ≠ compTag4) (hikA : PreNXOK S g o.ikA) (hikB : PreNXOK S g o.ikB) (hspk : PreNXOK S g o.spk) (hrk : PreNXOK S g o.keys.rk) (hck : PreNXOK S g o.keys.ck) (hpqr : PreNXOK S g o.keys.pqr) (hstARk : (gamma compI0 S g (iniAliceStartState tr₁ b o).rk).take 4 ≠ compTag4) (hcks0 : (gamma compI0 S g (iniAliceStartState tr₁ b o).cks).take 4 ≠ compTag4) : TRStateNX S g (iniAliceStartState tr₁ b o) :=
  let hdhsA := preNXOK_randTerm hdhs; let hcc := preNXOK_createChain hchainPrk hstARk hcks0 hrk hspk hdhsA;
  { myIk := preNXOK_serializedIk hikA, peerIk := preNXOK_serializedIk hikB, rk := hcc.1, dhs := hdhsA, cks := hcc.2, sid := preNXOK_concat (preNXOK_dhPk hdhsA) hrk, spqr := preNXOK_spqrInit hpqr (preNXOK_lit _),
    recv := fun _ hd => by rcases List.mem_singleton.mp hd with rfl; exact ⟨hspk, hck⟩ }
theorem trStateNX_encSt {S : Sem} {g : Ghost} (tr₂ : ExecTrace) {stA : TRState} (cl : Nat) (hst : TRStateNX S g stA) (hc : (gamma compI0 S g (randTerm (tr₂.length + 1) cl)).take 4 ≠ compTag4) (hcks1 : (gamma compI0 S g (kdfCk stA.cks).1).take 4 ≠ compTag4) : TRStateNX S g (encSt tr₂ stA cl) := ⟨hst.myIk, hst.peerIk, hst.rk, hst.dhs, preNXOK_kdfCk_fst hcks1 hst.cks, hst.sid, preNXOK_spqrSendState hst.spqr (preNXOK_randTerm hc), hst.recv⟩
theorem preNXOK_encSalt_ini {S : Sem} {g : Ghost} (tr₁ tr₂ : ExecTrace) (b : Participant) (o : AliceHandshakeOut) (cl : Nat) (_hencPrk : (gamma compI0 S g (encPrk tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))).take 4 ≠ compTag4) (hpqr : PreNXOK S g o.keys.pqr) : PreNXOK S g (encSalt tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)) := by rw [encSalt_iniAliceStartState_eq_spqrChainKey]; exact preNXOK_spqrChainKey hpqr (preNXOK_lit _) (preNXOK_lit _)
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem untagged_of_eq {a b : HwBytes} (h : a = b) (hb : b.take 4 ≠ compTag4) : a.take 4 ≠ compTag4 := h ▸ hb
end Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38
