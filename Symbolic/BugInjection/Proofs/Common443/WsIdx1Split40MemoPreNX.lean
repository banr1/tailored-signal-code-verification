/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoClose
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
public import Symbolic.BugInjection.Proofs.Common443.CompC3Pre38HB
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreNX
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRX0Top Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
section Leaf
variable {S : Sem} {g : Ghost}
theorem preNXOK_spqrSendKey {st c : DY.Bytes} (hst : PreNXOK S g st) (hc : PreNXOK S g c) : PreNXOK S g (DY.Spqr.spqrSend st c).2.1 := by
  unfold DY.Spqr.spqrSend; dsimp only; have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  cases hv : st.view? DY.Spqr.InitState.SubF with
  | none => exact CompRMemoKnown.memoOK_spqrSendKey_pack hst hc
  | some x =>
    rw [hv] at hp; rw [← hp] at hst; obtain ⟨hk, hpar⟩ := CompRMemoKnown.memoOK_spqrInit_elim hst; exact preNXOK_spqrChainKey hk hpar (preNXOK_lit _)
private theorem gamma_symEnc_eq (k iv m : DY.Bytes) : gamma compI0 S g (DY.SymEnc.symEnc k iv m) = compAesPerm (gamma compI0 S g k) ((gamma compI0 S g iv).take 16) (gamma compI0 S g m) := by
  unfold gamma gamma'
  rw [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gSym0 compI0) (gAll compI0 S g)]; rfl
set_option maxRecDepth 200000 in theorem compAesPerm_ws1_eq : compAesPerm WsIdx1Split40MemoVals.wsCipherKey1 (WsIdx1Split40MemoVals.wsIv1Full.take 16) compAesPt1 = compAesCt1 := by decide +kernel
set_option maxRecDepth 200000 in theorem compAesPerm_ws2_eq : compAesPerm WsIdx1Split40MemoVals.wsCipherKey2 (WsIdx1Split40MemoVals.wsIv2Full.take 16) compAesPt2 = compAesCt2 := by decide +kernel
theorem gamma_symEnc_untagged_of_compAesPt1 {k iv m : DY.Bytes} (hk : gamma compI0 S g k = WsIdx1Split40MemoVals.wsCipherKey1) (hiv : gamma compI0 S g iv = WsIdx1Split40MemoVals.wsIv1Full) (hm : gamma compI0 S g m = compAesPt1) : (gamma compI0 S g (DY.SymEnc.symEnc k iv m)).take 4 ≠ compTag4 := by
  have h : compAesCt1.take 4 ≠ compTag4 := by decide +kernel
  rw [gamma_symEnc_eq, hk, hiv, hm, compAesPerm_ws1_eq]; exact h
theorem gamma_symEnc_untagged_of_compAesPt2 {k iv m : DY.Bytes} (hk : gamma compI0 S g k = WsIdx1Split40MemoVals.wsCipherKey2) (hiv : gamma compI0 S g iv = WsIdx1Split40MemoVals.wsIv2Full) (hm : gamma compI0 S g m = compAesPt2) : (gamma compI0 S g (DY.SymEnc.symEnc k iv m)).take 4 ≠ compTag4 := by
  have h : compAesCt2.take 4 ≠ compTag4 := by decide +kernel
  rw [gamma_symEnc_eq, hk, hiv, hm, compAesPerm_ws2_eq]; exact h
set_option maxRecDepth 200000 in theorem compKyberEncaps_e1 : compKyberEncaps compKyberE1 = compKyberCt1 ++ compKyberSs1 := by decide +kernel
theorem kemEncap_fst_untagged_of_e1 {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE1) : (gamma compI0 S g (DY.PQKem.kemEncap pk e).1).take 4 ≠ compTag4 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_fst_eq h32,
      show compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) from rfl,
      Option.getD_some, he, compKyberEncaps_e1, List.take_left' Census443Memo.kyberCtVals_lengths.2.1]
  exact WsIdx1Split40MemoVals.wsPrefixKemAes_untagged.2.1
theorem kemEncap_snd_untagged_of_e1 {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE1) : (gamma compI0 S g (DY.PQKem.kemEncap pk e).2).take 4 ≠ compTag4 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32,
      show compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) from rfl,
      Option.getD_some, he, compKyberEncaps_e1, List.drop_left' Census443Memo.kyberCtVals_lengths.2.1]
  exact WsIdx1Split40MemoVals.wsPrefixKemAes_untagged.2.2.1
theorem preNXOK_encOut_of (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl pqIdx : Nat) (hst : TRStateNX S g stA) (hencPrk : (gamma compI0 S g (encPrk tr₂ stA cl pqIdx)).take 4 ≠ compTag4) (hsalt : PreNXOK S g (encSalt tr₂ stA cl pqIdx)) (hpt_u : (gamma compI0 S g (randTerm tr₂.length 32)).take 4 ≠ compTag4) (hct_u : (gamma compI0 S g (DY.SymEnc.symEnc (encKeys tr₂ stA cl pqIdx).cipherKey (encKeys tr₂ stA cl pqIdx).iv (randTerm tr₂.length 32))).take 4 ≠ compTag4) (hc : PreNXOK S g (randTerm (tr₂.length + 1) cl)) (hseed : (gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).take 4 ≠ compTag4) (hcipherKey : (gamma compI0 S g (encKeys tr₂ stA cl pqIdx).cipherKey).take 4 ≠ compTag4) (hmacKey : (gamma compI0 S g (encKeys tr₂ stA cl pqIdx).macKey).take 4 ≠ compTag4) (hiv : (gamma compI0 S g (encKeys tr₂ stA cl pqIdx).iv).take 4 ≠ compTag4) (hmacFull : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA cl pqIdx).macKey (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl pqIdx))))).take 4 ≠ compTag4) : PreNXOK S g (encOut tr₂ stA cl pqIdx) := by
  dsimp only [encOut, encWire, encMac, DY.Libsignal.TripleRatchet.trHonestWireMsg]; have hmk := preNXOK_trMsgKeys hseed hencPrk hcipherKey hmacKey hiv hsalt hst.cks; have hct := preNXOK_symEnc hct_u hmk.1 hmk.2.2 (preNXOK_randTerm hpt_u); have hdhsPk := preNXOK_dhPk hst.dhs; have hpqMsg := preNXOK_spqrSendMsg hst.spqr hc; exact preNXOK_concat (preNXOK_trWire hdhsPk hct hpqMsg) (preNXOK_computeMac_trWire hmacFull hmk.2.1 hst.myIk hst.peerIk hdhsPk hct hpqMsg)
theorem preNXOK_setupSecrets_wsIdx1 {r : Records} (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup compI0 r) (hc : Compat compI0 r S g) : PreNXOK S g (randTerm 0 32) ∧ PreNXOK S g (randTerm 5 32) ∧ PreNXOK S g (randTerm 10 32) ∧ PreNXOK S g (randTerm 16 64) := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  refine ⟨preNXOK_randTerm ?_, preNXOK_randTerm ?_, preNXOK_randTerm ?_, preNXOK_randTerm ?_⟩
  · rw [← CompSetupSecrecy.setupSecret_0 hNe, CompRX0Bytes.gamma_setupSecret_0 hNe hc, hfits.1.2.2.2.2.2.2.1]
    exact WsIdx1Split40MemoPreKIR.ws1_aliceId_kdfFree.1
  · rw [← CompSetupSecrecy.setupSecret_1 hNe, CompRX0Bytes.gamma_setupSecret_1 hNe hc, hfits.1.2.2.2.2.2.2.2.1]
    exact WsIdx1Split40MemoPreKIR.ws1_bobId_kdfFree.1
  · rw [← CompSetupSecrecy.setupSecret_2 hNe, CompRX0Bytes.gamma_setupSecret_2 hNe hc, hfits.1.2.2.2.2.2.2.2.2.1]
    exact WsIdx1Split40MemoPreKIR.ws1_spk_kdfFree.1
  · rw [← CompSetupSecrecy.setupSecret_4 hNe, gamma_setupSecret_4 hNe hc, (CompFitsNames.compFits_secretBytes_fresh hfits).2.1]
    exact fillFresh_16_64_untagged
theorem preNXOK_storedSecrets_wsIdx1 {r : Records} {ms : List Move} (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup compI0 r) (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), PreNXOK S g u := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨h0, h5, h10, h16⟩ := preNXOK_setupSecrets_wsIdx1 hfits hc; have hinv := CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach; intro u hu; obtain ⟨j, _, ls, hat, rfl⟩ := CompRX0NBSC38Parts.mem_storedSecrets_iff.mp hu
  refine preNXOK_serialize_local_pqxdh ?_
  have hkind : CompInv.KindOK (runTraceMoves r ms) ls.participant ls.state := hinv.stOK ls.participant ls.state j hat
  rcases ls with ⟨part, ⟨kind, sk⟩⟩
  dsimp only [CompInv.KindOK] at hkind ⊢
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hNe hns hkind with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · rw [CompSetupSecrecy.setupSecret_0 hNe]; exact h0
    · rw [CompSetupSecrecy.setupSecret_1 hNe]; exact h5
  | signedPrekey =>
    obtain ⟨_, rfl, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hNe hns hkind; rw [CompSetupSecrecy.setupSecret_2 hNe]; exact h10
  | pqPrekey =>
    obtain ⟨_, rfl, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hNe hns hkind; rw [CompSetupSecrecy.setupSecret_4 hNe]; exact h16
  | oneTimePrekey =>
    obtain ⟨t, rfl, _, hev⟩ := hkind; have h0' := CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hNe h0' with
      ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨hopk_true, _, _⟩
    · cases heq
    · cases heq
    · cases heq
    · cases heq
    · rw [hfits.1.2.1] at hopk_true; cases hopk_true
end Leaf
theorem census_iniAliceOut_eq : @Census443Defs.iniAliceOut = @CompPrefixInvAlice.iniAliceOut := rfl
theorem census_iniAliceStartState_eq : @Census443Defs.iniAliceStartState = @CompPrefixInvAlice.iniAliceStartState := rfl
theorem census_encSt_eq : @Census443Defs.encSt = @CompPrefixInvEnc.encSt := rfl
theorem census_encOut_eq : @Census443Defs.encOut = @CompPrefixInvEnc.encOut := rfl
theorem census_encMac_eq : @Census443Defs.encMac = @CompPrefixInvEnc.encMac := rfl
theorem sp_encKeys_eq : @WsIdx1Split40MemoVals.SP.encKeys = @CompRNbsc38MacKey.encKeys := rfl
theorem sp_encPrk_eq : @WsIdx1Split40MemoVals.SP.encPrk = @CompRNbsc38MacKey.encPrk := rfl
private theorem encMac_eq' (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : encMac tr₂ stA cl pq = DY.Libsignal.TripleRatchet.computeMac (encKeys tr₂ stA cl pq).macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq) := rfl
theorem pqxdhPrk_bridge (tr₁ : ExecTrace) (ikA ikB spkB pqpkB : DY.Bytes) : DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree spkB ikA) (DY.Libsignal.PQXDH.agree ikB (randTerm tr₁.length 32)) (DY.Libsignal.PQXDH.agree spkB (randTerm tr₁.length 32)) none (DY.PQKem.kemEncap pqpkB (randTerm (tr₁.length + 1) 32)).2) = CompRSplit38Untagged.pqxdhPrk (iniAliceIkm tr₁ ikA ikB spkB pqpkB) := rfl
theorem iniChainPrk_bridge (tr₁ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : DY.Libsignal.TripleRatchet.hmac o.keys.rk (DY.Libsignal.PQXDH.agree o.spk (randTerm (tr₁.length + 2) 32)) = CompRSplit38Untagged.iniChainPrk tr₁ o := rfl
namespace SB
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins (saltAndSeedPin_s1_1 macChainOk_spec macChainOk_of_wire wireMacChainOk_b1 msgMac8 gamma_computeMac wsPrk wsMacKey)
end SB
theorem macFull_untagged_of_encMac {S : Sem} {g : Ghost} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {p : PreKeyFields} {k P : HwBytes} (hmac : gamma compI0 S g (encMac tr stA cl pq) = SB.msgMac8 p) (hok : Cheval26WeakStateIdx1.CompRSchedBSeedPins.macChainOk k P p = true) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr stA cl pq).macKey (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr stA cl pq))))).take 4 ≠ compTag4 := by
  have hu := (SB.macChainOk_spec hok).1; rw [← hmac, encMac_eq', SB.gamma_computeMac, List.take_take] at hu; exact hu
set_option maxRecDepth 200000 in theorem wsPrk_eq_ws1Prk : SB.wsPrk = WsIdx1O4Tag.ws1Prk := by decide +kernel
set_option maxRecDepth 200000 in theorem wsMacKey_eq_ws1MacKey : SB.wsMacKey = WsIdx1O4Tag.ws1MacKey := by decide +kernel
theorem msg1_nx {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat}
    (hinv : WsIdx1CensusDefs.WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) :
    let stA₁ := iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    gamma compI0 S g (encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).cipherKey = WsIdx1Split40MemoVals.wsCipherKey1 ∧
    gamma compI0 S g (encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).iv = WsIdx1Split40MemoVals.wsIv1Full ∧
    (gamma compI0 S g (encPrk tr₂ stA₁ cl₁ (tr₂.length + 2))).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).cipherKey).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).macKey).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).iv).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).macKey
      (DY.Concat.concat stA₁.myIk (DY.Concat.concat stA₁.peerIk (encWire tr₂ stA₁ cl₁ (tr₂.length + 2)))))).take 4 ≠ compTag4 := by
  intro stA₁
  let stA₁_c := Census443Defs.iniAliceStartState tr₁ r.bob (Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
  obtain ⟨p₁, hp₁⟩ := WsIdx1Split40MemoCk1Pin.parse_b1
  have hmac := WsIdx1Split40MemoCk1Pin.encMac_msg1 hinv hp₁
  obtain ⟨hK, hP, _, _⟩ := SB.saltAndSeedPin_s1_1 S g tr₂ stA₁_c cl₁ (Or.inl hp₁) hmac
  have hP' : gamma compI0 S g (WsIdx1Split40MemoVals.SP.encPrk tr₂ stA₁_c cl₁ (tr₂.length + 2)) = WsIdx1O4Tag.ws1Prk := hP.trans wsPrk_eq_ws1Prk
  have hK' : gamma compI0 S g (WsIdx1Split40MemoVals.SP.encKeys tr₂ stA₁_c cl₁ (tr₂.length + 2)).macKey = WsIdx1O4Tag.ws1MacKey := hK.trans wsMacKey_eq_ws1MacKey
  have hCK : gamma compI0 S g (WsIdx1Split40MemoVals.SP.encKeys tr₂ stA₁_c cl₁ (tr₂.length + 2)).cipherKey = WsIdx1Split40MemoVals.wsCipherKey1 := by
    rw [WsIdx1Split40MemoVals.encKeys_cipherKey, WsIdx1Split40MemoVals.gamma_hmac_of S g hP' (WsIdx1Split40MemoVals.gamma_concat_of S g (WsIdx1Split40MemoVals.gamma_wmk S g) (WsIdx1Split40MemoVals.gamma_litByte_1 S g))]
    exact WsIdx1Split40MemoVals.wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.1
  have hIV : gamma compI0 S g (WsIdx1Split40MemoVals.SP.encKeys tr₂ stA₁_c cl₁ (tr₂.length + 2)).iv = WsIdx1Split40MemoVals.wsIv1Full := by
    rw [WsIdx1Split40MemoVals.encKeys_iv, WsIdx1Split40MemoVals.gamma_hmac_of S g hP' (WsIdx1Split40MemoVals.gamma_concat_of S g hK' (WsIdx1Split40MemoVals.gamma_concat_of S g (WsIdx1Split40MemoVals.gamma_wmk S g) (WsIdx1Split40MemoVals.gamma_litByte_3 S g)))]
    exact WsIdx1Split40MemoVals.wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [stA₁_c] at hmac hP' hK' hCK hIV
  simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encMac_eq, sp_encKeys_eq, sp_encPrk_eq] at hmac hP' hK' hCK hIV
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, u1Prk, _, uCK1, _, uMK1, _, uIv1, _⟩ := WsIdx1Split40MemoVals.wsPrefixKdf_untagged
  exact ⟨hCK, hIV, untagged_of_eq hP' u1Prk, untagged_of_eq hCK uCK1, untagged_of_eq hK' uMK1, untagged_of_eq hIV uIv1, macFull_untagged_of_encMac hmac (SB.macChainOk_of_wire SB.wireMacChainOk_b1 hp₁)⟩
theorem msg2_macFull_nx {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {p : PreKeyFields}
    (hp : parsePreKeyWire WsIdx1CensusDefs.wire3Idx1Bytes = some p)
    (hinv : WsIdx1CensusDefs.WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) :
    let stA₁' := encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).macKey
      (DY.Concat.concat stA₁'.myIk (DY.Concat.concat stA₁'.peerIk (encWire tr₃ stA₁' cl₂ (tr₃.length + 2)))))).take 4 ≠ compTag4 := by
  intro stA₁'
  have hmac2 := (hinv.hwire₂ p hp).2.1
  simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, census_encMac_eq] at hmac2
  exact macFull_untagged_of_encMac hmac2 (SB.macChainOk_of_wire WsIdx1Split40MemoVals.sp_wireMacChainOk_wire3Idx1 hp)
def Split40NXDraws : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup compI0 r → parsePreKeyWire WsIdx1CensusDefs.wire3Idx1Bytes = some p → WsIdx1CensusDefs.WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → WsIdx1PrefDefs.Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → (gamma compI0 S g (randTerm tr₁.length 32)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm (tr₁.length + 2) 32)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm (tr₂.length + 1) cl₁)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm (tr₃.length + 1) cl₂)).take 4 ≠ compTag4
attribute [local irreducible] Symbolic.BugInjection.hexBytes
set_option maxRecDepth 200000 in theorem rngAt1_untagged : (Cheval26WeakStateIdx1.PtDead35.rngAt 1).take 4 ≠ compTag4 := by rw [WsIdx1Split40MemoNewCensus.rngAt1_eq_fast]; decide +kernel
set_option maxRecDepth 200000 in theorem rngAt34_untagged : (Cheval26WeakStateIdx1.PtDead35.rngAt 34).take 4 ≠ compTag4 := by rw [WsIdx1Split40MemoNewCensus.rngAt34_eq_fast]; decide +kernel
set_option maxRecDepth 200000 in
theorem rngAt36_untagged : (Cheval26WeakStateIdx1.PtDead35.rngAt 36).take 4 ≠ compTag4 := by
  have h : Cheval26WeakStateIdx1.PtDead35.rngAt 36 = hexBytes.go Cheval26WeakStateIdx1.SpecTop.hexDigit Cheval26WeakStateIdx1.PtDead38.rng36Chars := by rw [Cheval26WeakStateIdx1.PtDead38.rngAt36_eq_hex, Cheval26WeakStateIdx1.PtDead38.rng36Str_eq, Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
  rw [h]; decide +kernel
set_option maxRecDepth 200000 in
theorem rngAt36_inits_untagged : ∀ c ∈ (Cheval26WeakStateIdx1.PtDead35.rngAt 36).inits, c.take 4 ≠ compTag4 := by
  rw [WsIdx1Split40MemoNewCensus.rngAt36_eq_fast]; decide +kernel
set_option maxRecDepth 200000 in
theorem cliCoins2Fast_inits_untagged : ∀ c ∈ WsIdx1CensusDefs.cliCoins2Fast.inits, c.take 4 ≠ compTag4 := by
  decide +kernel
theorem nil_untagged : ([] : HwBytes).take 4 ≠ compTag4 := by decide +kernel
section Draws
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 (call0Rng_length)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus
attribute [local irreducible] bundle0 call0Rng rngAt setupPublic setupSecret
theorem split40NXDraws : Split40NXDraws := by intro r S g _p ms' tr₁ tr₂ tr₃ cl₁ cl₂ _hfits _hp hinv hlinks; obtain ⟨hek_pin, hdhs_pin, _, hc₁_mem, _, _, hc₂_mem, _⟩ := split40_draw_eqs hinv hlinks; exact ⟨untagged_of_eq hek_pin rngAt1_untagged, untagged_of_eq hdhs_pin rngAt34_untagged, rngAt36_inits_untagged _ hc₁_mem, cliCoins2Fast_inits_untagged _ hc₂_mem⟩
end Draws
set_option maxHeartbeats 400000 in
theorem split40PreNXOKOwn_of_enum (hE : WsIdx1Prefix40EnumDefs.Split40PrefixEnum) (hD : WsIdx1Split40MemoClose.Split40DrawPinsOwn) (hX : Split40NXDraws) : WsIdx1Split40MemoClose.Split40PreNXOKOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨_, _, hd_pt1, _, hd_pt2, _⟩ := hD r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; obtain ⟨hek_u, hdhs_u, hc1_u, hc2_u⟩ := hX r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; obtain ⟨hCipherKey1, hIv1, hPrk1_u, hCK1_u, hMK1_u, hIv1_u, hmac1_u⟩ := msg1_nx hinv; have hmac2_u := msg2_macFull_nx hp hinv; dsimp only at hmac2_u
  obtain ⟨hMacKey2, hPrk2, _hSalt2, hSeed2, hCks1, hCks0, hChainPrk, hRk0, hPqxdhPrk, hCk0, hPqr0,
      hStARk0, hSeed1, hCks2, hCipherKey2, hIv2⟩ :=
    WsIdx1Split40MemoVals.split40KdfPins r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv
  rw [pqxdhPrk_bridge] at hPqxdhPrk; rw [iniChainPrk_bridge] at hChainPrk; simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, sp_encKeys_eq, sp_encPrk_eq] at hMacKey2 hPrk2 hSeed2 hCks1 hCks0 hChainPrk hRk0 hCk0 hPqr0 hStARk0 hSeed1 hCks2 hCipherKey2 hIv2; rw [iniAliceOut_keys_eq] at hRk0 hCk0 hPqr0
  have hencSt_cks : (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁).cks = (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ r.bob
      (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)).cks).1 := rfl
  rw [hencSt_cks] at hCks1
  obtain ⟨uPqxdhPrk, uRk0, uCk0, uPqr0, uChainPrk, uStARk0, uCks0, uCks1, uCks2, uSeed1, uSeed2,
      _uSalt1, _uSalt2, _u1Prk, u2Prk, _uCK1, uCK2, _uMK1, uMK2, _uIv1, uIv2, _⟩ :=
    WsIdx1Split40MemoVals.wsPrefixKdf_untagged
  obtain ⟨h0, h5, h10, h16⟩ := preNXOK_setupSecrets_wsIdx1 hfits hinv.compat
  have hsec0 : PreNXOK S g (setupSecret r 0) := by rw [CompSetupSecrecy.setupSecret_0 hNe]; exact h0
  have hpub2 : PreNXOK S g (setupPublic r 2) := by rw [CompSetupSecrecy.setupPublic_2 hNe]; exact preNXOK_dhPk h5
  have hpub4 : PreNXOK S g (setupPublic r 4) := by rw [CompSetupSecrecy.setupPublic_4 hNe]; exact preNXOK_dhPk h10
  have hpub6 : PreNXOK S g (setupPublic r 6) := by rw [CompSetupSecrecy.setupPublic_6 hNe]; exact preNXOK_kemPk h16
  have hc1_r : PreNXOK S g (randTerm (tr₂.length + 1) cl₁) := preNXOK_randTerm hc1_u; have hc2_r : PreNXOK S g (randTerm (tr₃.length + 1) cl₂) := preNXOK_randTerm hc2_u; have he1_u := untagged_of_eq hinv.hent₁ WsIdx1Split40MemoVals.wsPrefixKemAes_untagged.2.2.2.1; have hpt1_u := untagged_of_eq hd_pt1 WsIdx1Split40MemoVals.wsPrefixKemAes_untagged.2.2.2.2.2.2.1; have hpt2_u := untagged_of_eq hd_pt2 WsIdx1Split40MemoVals.wsPrefixKemAes_untagged.2.2.2.2.2.2.2
  obtain ⟨hikA, hikB, hspk, hek, hct, hrk, hck, hpqr⟩ := preNXOK_iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) hsec0 hpub2 hpub4 hpub6 hek_u he1_u (untagged_of_eq hPqxdhPrk uPqxdhPrk) (untagged_of_eq hRk0 uRk0) (untagged_of_eq hCk0 uCk0) (untagged_of_eq hPqr0 uPqr0) (kemEncap_fst_untagged_of_e1 hinv.hent₁) (kemEncap_snd_untagged_of_e1 hinv.hent₁)
  have hstA₁ := trStateNX_iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (untagged_of_eq hChainPrk uChainPrk) hdhs_u hikA hikB hspk hrk hck hpqr (untagged_of_eq hStARk0 uStARk0) (untagged_of_eq hCks0 uCks0); have hstA₁' := trStateNX_encSt tr₂ cl₁ hstA₁ hc1_u (untagged_of_eq hCks1 uCks1); have hstA₁'' := trStateNX_encSt tr₃ cl₂ hstA₁' hc2_u (untagged_of_eq hCks2 uCks2)
  have hsalt₁ := preNXOK_encSalt_ini tr₁ tr₂ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) cl₁ hPrk1_u hpqr
  have hsalt₂ : PreNXOK S g (encSalt tr₃ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)) := by rw [CompPrefixInvEnc.encSalt_self]; exact preNXOK_spqrSendKey hstA₁'.spqr hc2_r
  have henc₁ := preNXOK_encOut_of tr₂ cl₁ (tr₂.length + 2) hstA₁ hPrk1_u hsalt₁ hpt1_u
    (gamma_symEnc_untagged_of_compAesPt1 hCipherKey1 hIv1 hd_pt1) hc1_r
    (untagged_of_eq hSeed1 uSeed1) hCK1_u hMK1_u hIv1_u hmac1_u
  have henc₂ := preNXOK_encOut_of tr₃ cl₂ (tr₃.length + 2) hstA₁'
    (untagged_of_eq hPrk2 u2Prk) hsalt₂ hpt2_u (gamma_symEnc_untagged_of_compAesPt2 hCipherKey2 hIv2 hd_pt2) hc2_r
    (untagged_of_eq hSeed2 uSeed2) (untagged_of_eq hCipherKey2 uCK2)
    (untagged_of_eq hMacKey2 uMK2) (untagged_of_eq hIv2 uIv2) hmac2_u
  intro u hu
  rcases hE r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown u hu with ha | hs
  · unfold WsIdx1Prefix40EnumDefs.Split40PrefixAtom at ha
    simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, census_encOut_eq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hek
    · exact hct
    · exact henc₁
    · exact henc₂
    · exact preNXOK_randTerm hpt1_u
    · exact preNXOK_randTerm hpt2_u
    · exact preNXOK_serialize_local_tr (ls := ⟨r.alice, _⟩) hstA₁
    · exact preNXOK_serialize_local_tr (ls := ⟨r.alice, _⟩) hstA₁'
    · exact preNXOK_serialize_local_tr (ls := ⟨r.alice, _⟩) hstA₁''
  · exact preNXOK_storedSecrets_wsIdx1 hfits hinv.compat hinv.mp.2.1.2.1 hinv.reach u hs
theorem split40PreNXOKOwn : WsIdx1Split40MemoClose.Split40PreNXOKOwn := split40PreNXOKOwn_of_enum WsIdx1Prefix40Enum.split40PrefixEnum WsIdx1Split40MemoNewCensus.split40DrawPinsOwn split40NXDraws
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreNX
