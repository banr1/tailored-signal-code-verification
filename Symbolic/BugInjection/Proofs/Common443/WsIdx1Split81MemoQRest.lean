/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRest
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPrefix Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs Symbolic.BugInjection.Proofs.Common443.CompC2RestR38 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj (KdfFree x25519Vals)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff)
open Symbolic.BugInjection.Proofs.Common443.CompC2Rest38 (RestEntry)
open Symbolic.BugInjection.Proofs.Common443.CompC2RestEntry38 (restEntry_of_nonInj restEntry_of_kdf restEntry_of_trunc8_kdf)
private theorem iniAliceOut_eq_comp : @Census443Defs.iniAliceOut = @CompPrefixInvAlice.iniAliceOut := rfl
private theorem iniAliceStartState_eq_comp : @Census443Defs.iniAliceStartState = @CompPrefixInvAlice.iniAliceStartState := rfl
private theorem encSt_eq_comp : @Census443Defs.encSt = @CompPrefixInvEnc.encSt := rfl
private theorem encOut_eq_comp : @Census443Defs.encOut = @CompPrefixInvEnc.encOut := rfl
theorem restEntry_of_saltedNodes81 {r : Records} {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr₁ tr₂ tr₄ : ExecTrace} {cl₁ : Nat} {x : Row} (hz : x.1 ∈ saltedNodes81 r salt tr₁ tr₂ tr₄ cl₁) (hv : x.2.2 = gamma compI0 S g x.1) : RestEntry S g x := by
  simp only [saltedNodes81, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h1 | h2 | h3 | h4 | h5 | h6
  · exact restEntry_of_kdf h1
  · exact restEntry_of_kdf h2
  · exact restEntry_of_kdf h3
  · exact restEntry_of_kdf h4
  · exact restEntry_of_kdf h5
  · exact restEntry_of_trunc8_kdf h6 hv
theorem restEntry_of_z81Terms {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr₄ : ExecTrace} {cl₁ cl₂ : Nat} {x : Row} (hz : x.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂) (hv : x.2.2 = gamma compI0 S g x.1) : RestEntry S g x := by
  unfold z81Terms at hz; rcases List.mem_append.mp hz with hz123 | hz4
  · rcases List.mem_append.mp hz123 with hz12 | hz3
    · rcases List.mem_append.mp hz12 with hz1 | hz2 <;> exact restEntry_of_saltedNodes81 ‹_› hv
    · exact restEntry_of_saltedNodes81 hz3 hv
  · exact restEntry_of_saltedNodes81 hz4 hv
set_option maxRecDepth 200000 in theorem rVal_compKyberE2 : RVal compKyberE2 := by unfold RVal NonInjOff KdfFree; decide +kernel
set_option maxRecDepth 200000 in theorem compKyberEncaps_e2 : compKyberEncaps compKyberE2 = compKyberCt2 ++ compKyberSs2 := by decide +kernel
theorem rVal_kemEncap_snd_of_e2 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE2) : RVal (gamma compI0 S g (DY.PQKem.kemEncap pk e).2) := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32]
  have h : compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] =
      some (compKyberEncaps (gamma compI0 S g e)) := rfl
  rw [h, Option.getD_some, he, compKyberEncaps_e2, List.drop_left' Census443Memo.kyberCtVals_lengths.2.2.1]; exact rVal_compKyberSs2
set_option maxRecDepth 200000 in theorem rVal_compAesPt3 : RVal compAesPt3 := rVal_of_len (by decide +kernel) (by decide +kernel)
theorem rVal_compAesPerm_pt3 (k iv : HwBytes) : RVal (compAesPerm k iv compAesPt3) :=
  rVal_of_len (by rw [CompI0Laws.compAesPerm_length_of_lt_16 k iv compAesPt3 (by decide)]; decide)
    (by rw [CompI0Laws.compAesPerm_length_of_lt_16 k iv compAesPt3 (by decide)]; decide)
theorem rVal_symEnc_pt3 {S : Sem} {g : Ghost} {k iv m : DY.Bytes} (hm : gamma compI0 S g m = compAesPt3) : RVal (gamma compI0 S g (DY.SymEnc.symEnc k iv m)) := by rw [gamma_symEnc_eq', hm]; exact rVal_compAesPerm_pt3 _ _
theorem rc_encOut_self_pt3 {S : Sem} {g : Ghost} (tr₅ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl₅ : Nat) (hst : TRStateRC S g stA) (hpt : gamma compI0 S g (randTerm tr₅.length 32) = compAesPt3) (hc : RC S g (randTerm (tr₅.length + 1) cl₅)) : RC S g (CompPrefixInvEnc.encOut tr₅ stA cl₅ (tr₅.length + 2)) := by
  have hsalt : RC S g (CompPrefixInvEnc.encSalt tr₅ stA cl₅ (tr₅.length + 2)) := by rw [encSalt_self]; exact rc_spqrSendKey hst.spqr hc
  dsimp only [CompPrefixInvEnc.encOut, CompPrefixInvEnc.encWire, CompPrefixInvEnc.encMac, DY.Libsignal.TripleRatchet.trHonestWireMsg]; have hmk := rc_trMsgKeys hsalt hst.cks
  have hct := rc_symEnc (rVal_symEnc_pt3 hpt) hmk.1 hmk.2.2 (rc_randTerm (by rw [hpt]; exact rVal_compAesPt3))
  have hdhsPk := rc_dhPk hst.dhs; have hpqMsg := rc_spqrSendMsg hst.spqr hc; exact rc_concat (rc_trWire hdhsPk hct hpqMsg) (rc_computeMac_trWire hmk.2.1 hst.myIk hst.peerIk hdhsPk hct hpqMsg)
set_option maxRecDepth 200000 in theorem rVal_bobRng41Bytes : RVal bobRng41Bytes := by unfold RVal NonInjOff KdfFree bobRng41Bytes; decide +kernel
theorem rc_spqrRecv_state {S : Sem} {g : Ghost} {st msg : DY.Bytes} {idx : UInt32} {st' : DY.Bytes} (hst : RC S g st) (hm : RC S g msg) (h : (DY.Spqr.spqrRecv st msg idx).map Prod.fst = some st') : RC S g st' := by obtain ⟨res, hres, rfl⟩ := Option.map_eq_some_iff.mp h; rw [DY.Spqr.spqrRecv_state st msg idx res hres]; exact Census443Memo.memoOK_spqrRecvState_pack hst hm
theorem rc_chainKeyAt {S : Sem} {g : Ghost} :
    ∀ (n : Nat) {ck : DY.Bytes}, RC S g ck → RC S g (DY.Libsignal.TripleRatchet.chainKeyAt ck n)
  | 0, _, hck => by unfold DY.Libsignal.TripleRatchet.chainKeyAt; exact hck
  | n + 1, _, hck => by unfold DY.Libsignal.TripleRatchet.chainKeyAt; exact rc_chainKeyAt n (rc_kdfCk hck).1
theorem trStateRC_bobSt81 {r : Records} {S : Sem} {g : Ghost}
    (hNe : r.alice ≠ r.bob) (tr₁ tr₂ tr₃ tr_bob : ExecTrace)
    (cl₁ cl₂ : Nat) (spqrMsgIdx₂ : UInt32) (spqr₂' : DY.Bytes) (ctr₂ : UInt32)
    (h0 : RC S g (randTerm 0 32)) (h5 : RC S g (randTerm 5 32))
    (h10 : RC S g (randTerm 10 32)) (h16 : RC S g (randTerm 16 64))
    (hek : RC S g (randTerm tr₁.length 32)) (hent : RC S g (randTerm (tr₁.length + 1) 32))
    (hss_val : RVal (gamma compI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2))
    (hdhs : RC S g (randTerm (tr₁.length + 2) 32)) (hcoins₁ : RC S g (randTerm (tr₂.length + 1) cl₁))
    (hcoins₂ : RC S g (randTerm (tr₃.length + 1) cl₂)) (hbob : RC S g (randTerm tr_bob.length 32))
    (hrecv :
      let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
      let stA₁' := CompPrefixInvEnc.encSt tr₂ stA₁ cl₁
      (DY.Spqr.spqrRecv (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂') :
    let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
    TRStateRC S g (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' ctr₂) := by
  intro o₁ stA₁; dsimp only at hrecv
  obtain ⟨_, _, _, _, _, hrk, _, hpqr⟩ := rc_aliceOut hNe tr₁ h0 h5 h10 h16 hek hent hss_val
  have hstA := trStateRC_stA hNe tr₁ h0 h5 h10 h16 hek hent hss_val hdhs
  have hstA' := trStateRC_encSt tr₂ cl₁ hstA hcoins₁
  have hdhs_eq : stA₁.dhs = randTerm (tr₁.length + 2) 32 := rfl
  have hrt : RC S g (DY.DiffieHellman.dhPk stA₁.dhs) := rc_dhPk hstA.dhs
  have hsec2 : setupSecret r 2 = randTerm 10 32 := CompSetupSecrecy.setupSecret_2 hNe
  have hc1 : RC S g (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2)).1 ∧ RC S g (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2)).2 := by
    rw [hdhs_eq, hsec2]; exact rc_createChain_dhPk hrk hdhs h10
  have hc2 : RC S g (DY.Libsignal.TripleRatchet.createChain (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2)).1 (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32)).1 ∧ RC S g (DY.Libsignal.TripleRatchet.createChain (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2)).1 (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32)).2 := by
    rw [hdhs_eq]; exact rc_createChain_dhPk hc1.1 hdhs hbob
  refine ⟨?_, ?_, hc2.1, hbob, hc2.2, rc_concat (rc_x25519Key hrt) hrk, rc_spqrRecv_state (rc_spqrInit hpqr (rc_lit _)) (rc_spqrSendMsg hstA'.spqr hcoins₂) hrecv, ?_⟩
  · show RC S g (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2))
    rw [CompSetupSecrecy.setupPublic_2 hNe]; exact rc_serializedIk (rc_dhPk h5)
  · show RC S g (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0))
    rw [CompSetupSecrecy.setupPublic_0 hNe]; exact rc_serializedIk (rc_dhPk h0)
  · intro d hd; simp only [bobSt81, List.mem_singleton] at hd; subst hd
    exact ⟨hrt, (rc_kdfCk (rc_chainKeyAt ctr₂.toNat hc1.2)).1⟩
def Split81DrawPins (r : Records) (S : Sem) (g : Ghost)
    (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : Prop :=
  let _ := r
  RVal (gamma compI0 S g (randTerm tr₁.length 32)) ∧
  RVal (gamma compI0 S g (randTerm (tr₁.length + 2) 32)) ∧
  gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1 ∧
  RVal (gamma compI0 S g (randTerm (tr₂.length + 1) cl₁)) ∧
  gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2 ∧
  RVal (gamma compI0 S g (randTerm (tr₃.length + 1) cl₂)) ∧
  RVal (gamma compI0 S g (randTerm tr₄.length 32)) ∧
  RVal (gamma compI0 S g (randTerm (tr₄.length + 2) 32)) ∧
  gamma compI0 S g (randTerm tr₅.length 32) = compAesPt3 ∧
  RVal (gamma compI0 S g (randTerm (tr₅.length + 1) cl₅))
def Split81DrawPinsOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Split81DrawPins r S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅
theorem rc_prefixAtom_81 {r : Records} {S : Sem} {g : Ghost} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hent₁ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = compKyberE1) (hent₂ : gamma compI0 S g (randTerm (tr₄.length + 1) 32) = compKyberE2) (hdraws : Split81DrawPins r S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {u : DY.Bytes} (hu : Split81PrefixAtom r S g tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ u) : RC S g u := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨h0, h5, h10, h16⟩ := rc_setup_wsIdx1 hfits hc; obtain ⟨hek₁V, hdhs₁V, hpt₁, hc₁V, hpt₂, hc₂V, hek₂V, hdhs₂V, hpt₅, hc₅V⟩ := hdraws; have hek₁R := rc_randTerm hek₁V; have hent₁R := rc_randTerm_of_eq hent₁ rVal_compKyberE1; have hss₁V := rVal_kemEncap_snd_of_e1 (pk := DY.PQKem.kemPk (randTerm 16 64)) hent₁; have hdhs₁R := rc_randTerm hdhs₁V; have hc₁R := rc_randTerm hc₁V; have hc₂R := rc_randTerm hc₂V
  have hek₂R := rc_randTerm hek₂V; have hent₂R := rc_randTerm_of_eq hent₂ rVal_compKyberE2; have hss₂V := rVal_kemEncap_snd_of_e2 (pk := DY.PQKem.kemPk (randTerm 16 64)) hent₂; have hdhs₂R := rc_randTerm hdhs₂V; have hc₅R := rc_randTerm hc₅V; have hout₁ := rc_aliceOut hNe tr₁ h0 h5 h10 h16 hek₁R hent₁R hss₁V; have hst₁ := trStateRC_stA hNe tr₁ h0 h5 h10 h16 hek₁R hent₁R hss₁V hdhs₁R; have hst₁' := trStateRC_encSt tr₂ cl₁ hst₁ hc₁R
  have hout₂ := rc_aliceOut hNe tr₄ h0 h5 h10 h16 hek₂R hent₂R hss₂V; have hst₂ := trStateRC_stA hNe tr₄ h0 h5 h10 h16 hek₂R hent₂R hss₂V hdhs₂R; unfold Split81PrefixAtom at hu; dsimp only at hu; rw [iniAliceOut_eq_comp, iniAliceStartState_eq_comp, encSt_eq_comp, encOut_eq_comp] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | ⟨tr_bob, spqrMsgIdx₂, spqr₂', hbob_pin, hrecv, rfl⟩
  · exact hout₁.2.2.2.1
  · exact hout₁.2.2.2.2.1
  · exact rc_encOut_self_pt1 tr₂ cl₁ hst₁ hpt₁ hc₁R
  · exact rc_encOut_self_pt2 tr₃ cl₂ hst₁' hpt₂ hc₂R
  · exact hout₂.2.2.2.1
  · exact hout₂.2.2.2.2.1
  · exact rc_encOut_self_pt3 tr₅ cl₅ hst₂ hpt₅ hc₅R
  · exact rc_randTerm_of_eq hpt₁ rVal_compAesPt1
  · exact rc_randTerm_of_eq hpt₂ rVal_compAesPt2
  · exact rc_randTerm_of_eq hpt₅ rVal_compAesPt3
  · exact rc_serialize_local_tr hst₁
  · exact rc_serialize_local_tr hst₁'
  · exact rc_serialize_local_tr (trStateRC_encSt tr₃ cl₂ hst₁' hc₂R)
  · exact rc_serialize_local_tr hst₂
  · exact rc_serialize_local_tr (trStateRC_encSt tr₅ cl₅ hst₂ hc₅R)
  · exact rc_serialize_local_tr (trStateRC_bobSt81 hNe tr₁ tr₂ tr₃ tr_bob cl₁ cl₂ spqrMsgIdx₂ spqr₂' 1
      h0 h5 h10 h16 hek₁R hent₁R hss₁V hdhs₁R hc₁R hc₂R (rc_randTerm_of_eq hbob_pin rVal_bobRng41Bytes) hrecv)
theorem restEntry_of_extChainRows81 {r : Records} {S : Sem} {g : Ghost} (hfits : compFitsPinned setup compI0 r) (hc : Compat compI0 r S g) {tr₁ tr₂ tr₄ : ExecTrace} {cl₁ : Nat} (hek₂V : RVal (gamma compI0 S g (randTerm tr₄.length 32))) (hent₂ : gamma compI0 S g (randTerm (tr₄.length + 1) 32) = compKyberE2) {x : Row} (hx : x ∈ extChainRows81 r S g tr₁ tr₂ tr₄ cl₁) : RestEntry S g x := by
  obtain ⟨h0, h5, h10, h16⟩ := rc_setup_wsIdx1 hfits hc
  have hout₂ := rc_aliceOut hfits.1.1.1 tr₄ h0 h5 h10 h16 (rc_randTerm hek₂V)
    (rc_randTerm_of_eq hent₂ rVal_compKyberE2) (rVal_kemEncap_snd_of_e2 (pk := DY.PQKem.kemPk (randTerm 16 64)) hent₂)
  have hv : x.2.2 = gamma compI0 S g x.1 := by obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx; rfl
  rcases extChainRows81_cases r S g tr₁ tr₂ tr₄ cl₁ hent₂ hx with hek | hct | ⟨u, hbob, rfl⟩
  · unfold o₂81 at hek; rw [iniAliceOut_eq_comp] at hek; exact hout₂.2.2.2.1 x hek hv
  · unfold o₂81 at hct; rw [iniAliceOut_eq_comp] at hct; exact hout₂.2.2.2.2.1 x hct hv
  · exact (bobChainRow_props r S g tr₁ tr₂ tr₄ cl₁ hbob).2.2.2.1
theorem split81RestEntryOwn_of_enum (hEnum : Split81PrefixEnum) (hDraws : Split81DrawPinsOwn) : Split81RestEntryOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown _ _ _ _ x hx hc; have hd := hDraws r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; have hv := exists_memo_of_mem81 hx
  rcases hc with hbase | hni | hz
  · rcases List.mem_append.mp hbase with hpre | hext
    · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hpre
      rcases hEnum r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown u hu with hatom | hsec
      · exact rc_prefixAtom_81 hfits hinv.compat hinv.hent₁ hinv.hent₂ hd hatom x hxu hv
      · exact rc_storedSecrets_40 hfits hinv.compat hinv.mp.2.1.2.1 hinv.reach u hsec x hxu hv
    · exact restEntry_of_extChainRows81 hfits hinv.compat hd.2.2.2.2.2.2.1 hinv.hent₂ hext
  · exact restEntry_of_nonInj hni
  · exact restEntry_of_z81Terms hz hv
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (QRest)
theorem split81DrawPinsOwn : Split81DrawPinsOwn := WsIdx1Split81DrawPins.split81DrawPinsOwn'
theorem split81ExtPairsOwn_qRest40_of_enum (hEnum : Split81PrefixEnum) (hDraws : Split81DrawPinsOwn) (hNX : Split81PreNXOKOwn) (hKdf : Split81ExtPairsOwn QKdf40) (hNC : Split81NonInjCensusOwn) (hFn : Split81RestFnOwn) : Split81ExtPairsOwn QRest40 := split81ExtPairsOwn_qRest40_of_pre (split81PreUntaggedOwn_of_preNXOK hNX) hKdf (split81ExtPairsOwn_qRest_of_entry_fn hNC (split81RestEntryOwn_of_enum hEnum hDraws) hFn)
theorem split81ExtPairsOwn_qRest40_of_leaves (hEnum : Split81PrefixEnum) (hDraws : Split81DrawPinsOwn) (hNX : Split81PreNXOKOwn) (hS : Split81PreSalt32Own) (hKK : Split81ExtKKOwn) (hKIR : Split81PreKIROwn) (hNC : Split81NonInjCensusOwn) (hFn : Split81RestFnOwn) : Split81ExtPairsOwn QRest40 := split81ExtPairsOwn_qRest40_of_enum hEnum hDraws hNX (split81ExtPairsOwn_qKdf40_of_census hS hKK hKIR hNC) hNC hFn
theorem split81ExtPairsOwn_qRest40_of_leaves' (hEnum : Split81PrefixEnum) (hNX : Split81PreNXOKOwn) (hS : Split81PreSalt32Own) (hKK : Split81ExtKKOwn) (hKIR : Split81PreKIROwn) (hNC : Split81NonInjCensusOwn) (hFn : Split81RestFnOwn) : Split81ExtPairsOwn QRest40 := split81ExtPairsOwn_qRest40_of_leaves hEnum split81DrawPinsOwn hNX hS hKK hKIR hNC hFn
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRest
