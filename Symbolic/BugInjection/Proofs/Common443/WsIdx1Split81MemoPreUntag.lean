/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreNX
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoPreUntag
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs (WS81Idx1RunInv wire3Idx1Bytes wire6Idx1Bytes)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs (Links81Own)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRX0Top Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38 Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreNX Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
section Leaf
variable {S : Sem} {g : Ghost}
set_option maxRecDepth 200000 in theorem compAesPerm_ws5_eq : compAesPerm WsIdx1Split81MemoVals.wsCipherKey5 (WsIdx1Split81MemoVals.wsIv5Full.take 16) compAesPt3 = compAesCt3 := by decide +kernel
theorem gamma_symEnc_untagged_of_compAesPt3 {k iv m : DY.Bytes} (hk : gamma compI0 S g k = WsIdx1Split81MemoVals.wsCipherKey5) (hiv : gamma compI0 S g iv = WsIdx1Split81MemoVals.wsIv5Full) (hm : gamma compI0 S g m = compAesPt3) : (gamma compI0 S g (DY.SymEnc.symEnc k iv m)).take 4 ≠ compTag4 := by
  have hγ : gamma compI0 S g (DY.SymEnc.symEnc k iv m) = compAesPerm (gamma compI0 S g k) ((gamma compI0 S g iv).take 16) (gamma compI0 S g m) := by
    unfold gamma gamma'
    rw [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl,
        DY.Bytes.rec_eq (gSym0 compI0) (gAll compI0 S g)]; rfl
  have h : compAesCt3.take 4 ≠ compTag4 := by decide +kernel
  rw [hγ, hk, hiv, hm, compAesPerm_ws5_eq]; exact h
theorem kemEncap_fst_untagged_of_e2 {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE2) : (gamma compI0 S g (DY.PQKem.kemEncap pk e).1).take 4 ≠ compTag4 := by rw [WsIdx1Split81MemoVals.gamma_kemEncap_fst_of_e2 he]; exact WsIdx1Split81MemoVals.wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem kemEncap_snd_untagged_of_e2 {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE2) : (gamma compI0 S g (DY.PQKem.kemEncap pk e).2).take 4 ≠ compTag4 := by rw [WsIdx1Split81MemoVals.gamma_kemEncap_snd_of_e2 he]; exact WsIdx1Split81MemoVals.wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem preNXOK_spqrRecv_state {st msg : DY.Bytes} {idx : UInt32} {st' : DY.Bytes} (hst : PreNXOK S g st) (hm : PreNXOK S g msg) (h : (DY.Spqr.spqrRecv st msg idx).map Prod.fst = some st') : PreNXOK S g st' := by
  rcases hres : DY.Spqr.spqrRecv st msg idx with _ | res
  · rw [hres] at h; cases h
  · rw [hres] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    rw [DY.Spqr.spqrRecv_state st msg idx res hres]; exact memoOK_spqrRecvState_pack hst hm
theorem untagged_of_freshSafe_randTerm {idx sz : Nat} (hsafe : WsIdx1CensusDefs.FreshSafeTerm compI0 S g (randTerm idx sz)) : (gamma compI0 S g (randTerm idx sz)).take 4 ≠ compTag4 := by
  by_cases hsz : sz = 0
  · subst hsz
    have h0 : gamma compI0 S g (randTerm idx 0) = [] := by unfold gamma gamma' randTerm; rw [DY.Bytes.rec_eq (gRandom g) (gAll compI0 S g)]; rfl
    rw [h0]; exact nil_untagged
  · have hmem : (randTerm idx sz, randTerm idx sz, gamma compI0 S g (randTerm idx sz)) ∈
        (gamma' compI0 S g (randTerm idx sz)).memo := by
      unfold gamma gamma' randTerm; rw [DY.Bytes.rec_eq (gRandom g) (gAll compI0 S g)]; dsimp only [gRandom, concretizeRandom]; simp [node, hsz]
    exact ((hsafe _ hmem).2 { timestamp := idx, size := sz } rfl).1
theorem freshSafe_of_memo_sub {u v : DY.Bytes} (hsafe : WsIdx1CensusDefs.FreshSafeTerm compI0 S g u) (hsub : ∀ x ∈ (gamma' compI0 S g v).memo, x ∈ (gamma' compI0 S g u).memo) : WsIdx1CensusDefs.FreshSafeTerm compI0 S g v := fun x hx => hsafe x (hsub x hx)
theorem mem_memo_spqrSendMsg_right {i : ExternInterpretation} {st coins : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g coins).memo) : x ∈ (gamma' i S g (DY.Spqr.spqrSend st coins).2.2).memo := by
  unfold gamma' at hx ⊢
  rw [show (DY.Spqr.spqrSend st coins).2.2 = ({ st := st, coins := coins } : DY.Spqr.SendMsg.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gSpqrSendMsg S) (gAll i S g)]
  simp only [gSpqrSendMsg, concretizeSpqrSendMsg, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, CompPlant.bytes_rec_gAll]; exact Or.inr hx
end Leaf
private theorem stA40_eq_census (r : Records) (tr₁ tr₂ : ExecTrace) (cl₁ : Nat) : WsIdx1Split40MemoDefs.stA40 r tr₁ tr₂ cl₁ = Census443Defs.encSt tr₂ (Census443Defs.iniAliceStartState tr₁ r.bob (Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ := rfl
private theorem stA₂81_eq_census (r : Records) (tr₄ : ExecTrace) : WsIdx1Split81MemoZPinRun.stA₂81 r tr₄ = Census443Defs.iniAliceStartState tr₄ r.bob (Census443Defs.iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) := rfl
attribute [local irreducible] Symbolic.BugInjection.hexBytes in private theorem wire3Idx1Bytes_eq_b2 : wire3Idx1Bytes = Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2SendBytes := by unfold wire3Idx1Bytes Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2SendBytes; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2Send_head_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.eventBytes_send]; rfl
theorem msg1_macFull_nx_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p : PreKeyFields}
    (hp : parsePreKeyWire wire6Idx1Bytes = some p)
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let stA₁ := iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).macKey
      (DY.Concat.concat stA₁.myIk (DY.Concat.concat stA₁.peerIk (encWire tr₂ stA₁ cl₁ (tr₂.length + 2)))))).take 4 ≠ compTag4 := by
  intro stA₁
  have hok := SB.macChainOk_of_wire WsIdx1Split81MemoVals.sp_wireMacChainOk_wire6Idx1 hp
  have hmac1 := (hinv.hwire₁ p hp).2.1
  simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encMac_eq] at hmac1
  exact macFull_untagged_of_encMac hmac1 hok
theorem msg2_macFull_nx_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let stA₁' := encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).macKey
      (DY.Concat.concat stA₁'.myIk (DY.Concat.concat stA₁'.peerIk (encWire tr₃ stA₁' cl₂ (tr₃.length + 2)))))).take 4 ≠ compTag4 := by
  intro stA₁'
  obtain ⟨p₂, hp₂⟩ := WsIdx1Split81MemoZPinRun.parse_b2
  have hmac2 := WsIdx1Split81MemoZPinRun.encMac_msg2_81 hinv hp₂
  have hp₂' : parsePreKeyWire wire3Idx1Bytes = some p₂ := by rw [wire3Idx1Bytes_eq_b2]; exact hp₂
  have hok := SB.macChainOk_of_wire WsIdx1Split40MemoVals.sp_wireMacChainOk_wire3Idx1 hp₂'
  rw [stA40_eq_census] at hmac2
  simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, census_encMac_eq] at hmac2
  exact macFull_untagged_of_encMac hmac2 hok
theorem msg5_macFull_nx_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let stA₂ := iniAliceStartState tr₄ r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₅ stA₂ cl₅ (tr₅.length + 2)).macKey
      (DY.Concat.concat stA₂.myIk (DY.Concat.concat stA₂.peerIk (encWire tr₅ stA₂ cl₅ (tr₅.length + 2)))))).take 4 ≠ compTag4 := by
  intro stA₂
  obtain ⟨p₅, hp₅⟩ := WsIdx1Split81MemoZPinRun.parse_b5
  have hmac5 := WsIdx1Split81MemoZPinRun.encMac_msg5_81 hinv hp₅
  have hok := SB.macChainOk_of_wire WsIdx1Split81MemoVals.sp_wireMacChainOk_b5 hp₅
  rw [stA₂81_eq_census] at hmac5
  simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encMac_eq] at hmac5
  exact macFull_untagged_of_encMac hmac5 hok
def wsBob3_dh1 : HwBytes := eval_hwbytes81 (compLookupDh (clamp setup.spk) WsIdx1Split81Census.ws_dhs1_pub)
def wsBob3_prk1 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 WsIdx1Split40MemoVals.wsRk0 wsBob3_dh1)
def wsBob3_rk1 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_prk1 (WsIdx1Split40MemoVals.wratInfoLit ++ [1#8]))
def wsBob3_ck1 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_prk1 (wsBob3_rk1 ++ (WsIdx1Split40MemoVals.wratInfoLit ++ [2#8])))
def wsBob3_ck1_next : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_ck1 [2#8])
def wsBob3_ck1_next2 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_ck1_next [2#8])
def wsBob3_dh2 : HwBytes := eval_hwbytes81 (compLookupDh (clamp bobRng41Bytes) WsIdx1Split81Census.ws_dhs1_pub)
def wsBob3_prk2 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_rk1 wsBob3_dh2)
def wsBob3_rk2 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_prk2 (WsIdx1Split40MemoVals.wratInfoLit ++ [1#8]))
def wsBob3_cks : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsBob3_prk2 (wsBob3_rk2 ++ (WsIdx1Split40MemoVals.wratInfoLit ++ [2#8])))
set_option maxRecDepth 200000 in theorem wsBob3_untagged : wsBob3_prk1.take 4 ≠ compTag4 ∧ wsBob3_rk1.take 4 ≠ compTag4 ∧ wsBob3_ck1.take 4 ≠ compTag4 ∧ wsBob3_ck1_next.take 4 ≠ compTag4 ∧ wsBob3_ck1_next2.take 4 ≠ compTag4 ∧ wsBob3_prk2.take 4 ≠ compTag4 ∧ wsBob3_rk2.take 4 ≠ compTag4 ∧ wsBob3_cks.take 4 ≠ compTag4 ∧ bobRng41Bytes.take 4 ≠ compTag4 := by decide +kernel
set_option maxRecDepth 200000 in theorem wsBob3_forward : compLookupDh (clamp setup.spk) WsIdx1Split81Census.ws_dhs1_pub = wsBob3_dh1 ∧ hmacWith WsIdx1O4Tag.F0 WsIdx1Split40MemoVals.wsRk0 wsBob3_dh1 = wsBob3_prk1 ∧ hmacWith WsIdx1O4Tag.F0 wsBob3_prk1 (WsIdx1Split40MemoVals.wratInfoLit ++ [1#8]) = wsBob3_rk1 ∧ hmacWith WsIdx1O4Tag.F0 wsBob3_prk1 (wsBob3_rk1 ++ (WsIdx1Split40MemoVals.wratInfoLit ++ [2#8])) = wsBob3_ck1 ∧ hmacWith WsIdx1O4Tag.F0 wsBob3_ck1 [2#8] = wsBob3_ck1_next ∧ hmacWith WsIdx1O4Tag.F0 wsBob3_ck1_next [2#8] = wsBob3_ck1_next2 ∧ compLookupDh (clamp bobRng41Bytes) WsIdx1Split81Census.ws_dhs1_pub = wsBob3_dh2 ∧ hmacWith WsIdx1O4Tag.F0 wsBob3_rk1 wsBob3_dh2 = wsBob3_prk2 ∧ hmacWith WsIdx1O4Tag.F0 wsBob3_prk2 (WsIdx1Split40MemoVals.wratInfoLit ++ [1#8]) = wsBob3_rk2 ∧ hmacWith WsIdx1O4Tag.F0 wsBob3_prk2 (wsBob3_rk2 ++ (WsIdx1Split40MemoVals.wratInfoLit ++ [2#8])) = wsBob3_cks := by decide +kernel
private theorem createChain_snd_eq_hmac (rk pk sk : DY.Bytes) : (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 = DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac rk (DY.Libsignal.PQXDH.agree pk sk)) (DY.Concat.concat (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 2))) := rfl
theorem bob_chain_nx_81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ tr₄ tr₅ tr_bob : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {p : PreKeyFields}
    (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p)
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅)
    (hrk : gamma compI0 S g (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk = WsIdx1Split40MemoVals.wsRk0)
    (hbob : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let rk1 := (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2)).1
    let ck1 := (DY.Libsignal.TripleRatchet.createChain o₁.keys.rk (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2)).2
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac o₁.keys.rk (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2)))).take 4 ≠ compTag4 ∧
    (gamma compI0 S g rk1).take 4 ≠ compTag4 ∧
    (gamma compI0 S g ck1).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac rk1 (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32)))).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain rk1 (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32)).1).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain rk1 (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32)).2).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck1).1).take 4 ≠ compTag4 ∧
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.kdfCk ck1).1).1).take 4 ≠ compTag4 := by
  intro o₁ stA₁ rk1 ck1
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  have hs2 : secretBytes r 2 = setup.spk := hfits.1.2.2.2.2.2.2.2.2.1
  have hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0 := hfits.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrt : gamma compI0 S g (DY.DiffieHellman.dhPk stA₁.dhs) = WsIdx1Split81Census.ws_dhs1_pub := by
    have hw := (hinv.hwire₁ p hp).2.2
    simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq] at hw
    rw [hw, WsIdx1Split81Census.wire6Idx1Bytes_senderRatchetKey hp]
  have hsec2 : gamma compI0 S g (setupSecret r 2) = setup.spk := by
    rw [CompRX0Bytes.gamma_setupSecret_2 hNe hinv.compat, hs2]
  have hdh1 : gamma compI0 S g (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2)) = wsBob3_dh1 := by
    rw [CompRGamma.gamma_agree compI0 hEq, hsec2, hrt]; exact wsBob3_forward.1
  have hprk1 : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac o₁.keys.rk (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk stA₁.dhs) (setupSecret r 2))) = wsBob3_prk1 := by
    rw [WsIdx1Split40MemoVals.gamma_hmac_of S g hrk hdh1]; exact wsBob3_forward.2.1
  have hrk1 : gamma compI0 S g rk1 = wsBob3_rk1 := by
    dsimp only [rk1]
    rw [WsIdx1Split81MemoVals.createChain_fst_eq_hmac, WsIdx1Split40MemoVals.gamma_hmac_of S g hprk1 (WsIdx1Split40MemoVals.gamma_concat_of S g (WsIdx1Split40MemoVals.gamma_wrat S g) (WsIdx1Split40MemoVals.gamma_litByte_1 S g))]
    exact wsBob3_forward.2.2.1
  have hck1 : gamma compI0 S g ck1 = wsBob3_ck1 := by
    dsimp only [ck1]
    rw [createChain_snd_eq_hmac, WsIdx1Split40MemoVals.gamma_hmac_of S g hprk1 (WsIdx1Split40MemoVals.gamma_concat_of S g hrk1 (WsIdx1Split40MemoVals.gamma_concat_of S g (WsIdx1Split40MemoVals.gamma_wrat S g) (WsIdx1Split40MemoVals.gamma_litByte_2 S g)))]
    exact wsBob3_forward.2.2.2.1
  have hck1_next : gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck1).1 = wsBob3_ck1_next := by
    rw [WsIdx1Split40MemoVals.kdfCk_fst, WsIdx1Split40MemoVals.gamma_hmac_of S g hck1 (WsIdx1Split40MemoVals.gamma_litByte_2 S g)]
    exact wsBob3_forward.2.2.2.2.1
  have hck1_next2 : gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.kdfCk ck1).1).1 = wsBob3_ck1_next2 := by
    rw [WsIdx1Split40MemoVals.kdfCk_fst, WsIdx1Split40MemoVals.gamma_hmac_of S g hck1_next (WsIdx1Split40MemoVals.gamma_litByte_2 S g)]
    exact wsBob3_forward.2.2.2.2.2.1
  have hdh2 : gamma compI0 S g (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32)) = wsBob3_dh2 := by
    rw [CompRGamma.gamma_agree compI0 hEq, hbob, hrt]; exact wsBob3_forward.2.2.2.2.2.2.1
  have hprk2 : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac rk1 (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32))) = wsBob3_prk2 := by
    rw [WsIdx1Split40MemoVals.gamma_hmac_of S g hrk1 hdh2]; exact wsBob3_forward.2.2.2.2.2.2.2.1
  have hrk2 : gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain rk1 (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32)).1 = wsBob3_rk2 := by
    rw [WsIdx1Split81MemoVals.createChain_fst_eq_hmac, WsIdx1Split40MemoVals.gamma_hmac_of S g hprk2 (WsIdx1Split40MemoVals.gamma_concat_of S g (WsIdx1Split40MemoVals.gamma_wrat S g) (WsIdx1Split40MemoVals.gamma_litByte_1 S g))]
    exact wsBob3_forward.2.2.2.2.2.2.2.2.1
  have hcksB : gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain rk1 (DY.DiffieHellman.dhPk stA₁.dhs) (randTerm tr_bob.length 32)).2 = wsBob3_cks := by
    rw [createChain_snd_eq_hmac, WsIdx1Split40MemoVals.gamma_hmac_of S g hprk2 (WsIdx1Split40MemoVals.gamma_concat_of S g hrk2 (WsIdx1Split40MemoVals.gamma_concat_of S g (WsIdx1Split40MemoVals.gamma_wrat S g) (WsIdx1Split40MemoVals.gamma_litByte_2 S g)))]
    exact wsBob3_forward.2.2.2.2.2.2.2.2.2
  obtain ⟨uPrk1, uRk1, uCk1, uCk1Next, uCk1Next2, uPrk2, uRk2, uCks, _⟩ := wsBob3_untagged
  exact ⟨untagged_of_eq hprk1 uPrk1, untagged_of_eq hrk1 uRk1, untagged_of_eq hck1 uCk1, untagged_of_eq hprk2 uPrk2, untagged_of_eq hrk2 uRk2, untagged_of_eq hcksB uCks, untagged_of_eq hck1_next uCk1Next, untagged_of_eq hck1_next2 uCk1Next2⟩
private theorem mem_memo_dhs_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₁ tr₂ : ExecTrace} {b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (randTerm (tr₁.length + 2) 32)).memo) : x ∈ (gamma' i S g (Census443Defs.encOut tr₂ (Census443Defs.iniAliceStartState tr₁ b o) cl pq)).memo := mem_memo_cks_of_encOut (mem_memo_hmac_left (mem_memo_hmac_right (mem_memo_agree_right hx)))
theorem split81NXDraws {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : (gamma compI0 S g (randTerm tr₁.length 32)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm (tr₁.length + 2) 32)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm (tr₂.length + 1) cl₁)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm (tr₃.length + 1) cl₂)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm tr₄.length 32)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm (tr₄.length + 2) 32)).take 4 ≠ compTag4 ∧ (gamma compI0 S g (randTerm (tr₅.length + 1) cl₅)).take 4 ≠ compTag4 := by
  obtain ⟨hmem_enc₁, _, hmem_enc₅, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv; have hsafe_enc₁ := hinv.hpref_safe _ hmem_enc₁; have hsafe_enc₅ := hinv.hpref_safe _ hmem_enc₅
  have hsafe_ek₁ : WsIdx1CensusDefs.FreshSafeTerm compI0 S g (randTerm tr₁.length 32) :=
    freshSafe_of_memo_sub hsafe_enc₁ (fun _ hx => mem_memo_rk_of_encOut (mem_memo_hmac_left (mem_memo_hmac_right
      (mem_memo_concat_right (mem_memo_concat_right (mem_memo_concat_left (mem_memo_agree_right hx)))))))
  have hsafe_dhs₂ : WsIdx1CensusDefs.FreshSafeTerm compI0 S g (randTerm (tr₄.length + 2) 32) :=
    freshSafe_of_memo_sub hsafe_enc₅ (fun _ hx => mem_memo_dhs_of_encOut hx)
  have hsafe_c₅ : WsIdx1CensusDefs.FreshSafeTerm compI0 S g (randTerm (tr₅.length + 1) cl₅) :=
    freshSafe_of_memo_sub hsafe_enc₅ (fun _ hx => mem_memo_encPqMsg_of_encOut (mem_memo_spqrSendMsg_right hx))
  exact ⟨untagged_of_freshSafe_randTerm hsafe_ek₁, untagged_of_freshSafe_randTerm hinv.hdhs₁, untagged_of_freshSafe_randTerm hinv.hcoins₁, untagged_of_freshSafe_randTerm hinv.hcoins₂, untagged_of_freshSafe_randTerm hinv.hek₂_safe, untagged_of_freshSafe_randTerm hsafe_dhs₂, untagged_of_freshSafe_randTerm hsafe_c₅⟩
set_option maxHeartbeats 400000 in
theorem split81PreNXOKOwn_of_enum (hE : Split81PrefixEnum) : Split81PreNXOKOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨_, _, hd_pt1, _, hd_pt2, _, _, _, hd_pt5, _⟩ := WsIdx1Split81DrawPins.split81DrawPinsOwn' r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; obtain ⟨hek1_u, hdhs1_u, hc1_u, hc2_u, hek2_u, hdhs2_u, hc5_u⟩ := split81NXDraws hinv; have hmac1_u := msg1_macFull_nx_81 hp hinv; have hmac2_u := msg2_macFull_nx_81 hinv
  have hmac5_u := msg5_macFull_nx_81 hinv; dsimp only at hmac1_u hmac2_u hmac5_u
  obtain ⟨hMacKey1, hPrk1, _hSalt1, hCipherKey1, hIv1, hMacKey2, hPrk2, _hSalt2, hSeed2, hCks1, hCks0, hChainPrk, hRk0, hPqxdhPrk, hCk0, hPqr0, hStARk0, hSeed1, hCks2,
      hCipherKey2, hIv2⟩ :=
    WsIdx1Split81MemoVals.split81S1KdfPins r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hp hinv
  obtain ⟨hMacKey5, hPrk5, _hSalt5, hSeed5, hCks4, hChainPrk4, hRk4, hPqxdhPrk4, hCk4, hPqr4,
      hStARk4, hCks5, hCipherKey5, hIv5⟩ :=
    WsIdx1Split81MemoVals.split81S2KdfPins r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hinv
  rw [pqxdhPrk_bridge] at hPqxdhPrk hPqxdhPrk4; rw [iniChainPrk_bridge] at hChainPrk hChainPrk4; simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, sp_encKeys_eq, sp_encPrk_eq] at hMacKey1 hPrk1 hCipherKey1 hIv1 hMacKey2 hPrk2 hSeed2 hCks1 hCks0; simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, sp_encKeys_eq] at hChainPrk hRk0 hCk0 hPqr0 hStARk0 hSeed1 hCks2 hCipherKey2 hIv2
  simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, sp_encKeys_eq, sp_encPrk_eq] at hMacKey5 hPrk5 hSeed5 hCks4 hChainPrk4 hRk4 hCk4 hPqr4 hStARk4 hCks5 hCipherKey5 hIv5; rw [iniAliceOut_keys_eq] at hRk0 hCk0 hPqr0 hRk4 hCk4 hPqr4
  have hencSt_cks : (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁).cks = (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ r.bob
      (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)).cks).1 := rfl
  rw [hencSt_cks] at hCks1
  obtain ⟨uPqxdhPrk, uRk0, uCk0, uPqr0, uChainPrk, uStARk0, uCks0, uCks1, uCks2, uSeed1, uSeed2,
      _uSalt1, _uSalt2, u1Prk, u2Prk, uCK1, uCK2, uMK1, uMK2, uIv1, uIv2, _⟩ :=
    WsIdx1Split40MemoVals.wsPrefixKdf_untagged
  obtain ⟨uPqxdhPrk4, uRk4, uCk4, uPqr4, uChainPrk4, uStARk4, uCks4, uCks5, uSeed5, _uSalt5,
      u5Prk, uCK5, uMK5, uIv5, _⟩ :=
    WsIdx1Split81MemoVals.wsS2Kdf_untagged
  obtain ⟨h0, h5, h10, h16⟩ := preNXOK_setupSecrets_wsIdx1 hfits hinv.compat
  have hsec0 : PreNXOK S g (setupSecret r 0) := by rw [CompSetupSecrecy.setupSecret_0 hNe]; exact h0
  have hpub2 : PreNXOK S g (setupPublic r 2) := by rw [CompSetupSecrecy.setupPublic_2 hNe]; exact preNXOK_dhPk h5
  have hpub4 : PreNXOK S g (setupPublic r 4) := by rw [CompSetupSecrecy.setupPublic_4 hNe]; exact preNXOK_dhPk h10
  have hpub6 : PreNXOK S g (setupPublic r 6) := by rw [CompSetupSecrecy.setupPublic_6 hNe]; exact preNXOK_kemPk h16
  have hc1_r : PreNXOK S g (randTerm (tr₂.length + 1) cl₁) := preNXOK_randTerm hc1_u; have hc2_r : PreNXOK S g (randTerm (tr₃.length + 1) cl₂) := preNXOK_randTerm hc2_u; have hc5_r : PreNXOK S g (randTerm (tr₅.length + 1) cl₅) := preNXOK_randTerm hc5_u; have he1_u := untagged_of_eq hinv.hent₁ WsIdx1Split40MemoVals.wsPrefixKemAes_untagged.2.2.2.1; have he2_u := untagged_of_freshSafe_randTerm hinv.hent₂_safe; have hpt1_u := untagged_of_freshSafe_randTerm hinv.hm₁
  have hpt2_u := untagged_of_freshSafe_randTerm hinv.hm₂
  have hpt5_u : (gamma compI0 S g (randTerm tr₅.length 32)).take 4 ≠ compTag4 :=
    untagged_of_eq hd_pt5 (by decide +kernel)
  obtain ⟨hikA, hikB, hspk, hek1, hct1, hrk1, hck1, hpqr1⟩ := preNXOK_iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) hsec0 hpub2 hpub4 hpub6 hek1_u he1_u (untagged_of_eq hPqxdhPrk uPqxdhPrk) (untagged_of_eq hRk0 uRk0) (untagged_of_eq hCk0 uCk0) (untagged_of_eq hPqr0 uPqr0) (kemEncap_fst_untagged_of_e1 hinv.hent₁) (kemEncap_snd_untagged_of_e1 hinv.hent₁)
  have hstA₁ := trStateNX_iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (untagged_of_eq hChainPrk uChainPrk) hdhs1_u hikA hikB hspk hrk1 hck1 hpqr1 (untagged_of_eq hStARk0 uStARk0) (untagged_of_eq hCks0 uCks0); have hstA₁' := trStateNX_encSt tr₂ cl₁ hstA₁ hc1_u (untagged_of_eq hCks1 uCks1); have hstA₁'' := trStateNX_encSt tr₃ cl₂ hstA₁' hc2_u (untagged_of_eq hCks2 uCks2)
  have hsalt₁ := preNXOK_encSalt_ini tr₁ tr₂ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) cl₁ (untagged_of_eq hPrk1 u1Prk) hpqr1
  have hsalt₂ : PreNXOK S g (encSalt tr₃ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)) := by rw [CompPrefixInvEnc.encSalt_self]; exact preNXOK_spqrSendKey hstA₁'.spqr hc2_r
  have henc₁ := preNXOK_encOut_of tr₂ cl₁ (tr₂.length + 2) hstA₁ (untagged_of_eq hPrk1 u1Prk) hsalt₁ hpt1_u
    (WsIdx1Split40MemoPreNX.gamma_symEnc_untagged_of_compAesPt1 hCipherKey1 hIv1 hd_pt1) hc1_r
    (untagged_of_eq hSeed1 uSeed1) (untagged_of_eq hCipherKey1 uCK1)
    (untagged_of_eq hMacKey1 uMK1) (untagged_of_eq hIv1 uIv1) hmac1_u
  have henc₂ := preNXOK_encOut_of tr₃ cl₂ (tr₃.length + 2) hstA₁' (untagged_of_eq hPrk2 u2Prk) hsalt₂ hpt2_u
    (gamma_symEnc_untagged_of_compAesPt2 hCipherKey2 hIv2 hd_pt2) hc2_r
    (untagged_of_eq hSeed2 uSeed2) (untagged_of_eq hCipherKey2 uCK2)
    (untagged_of_eq hMacKey2 uMK2) (untagged_of_eq hIv2 uIv2) hmac2_u
  obtain ⟨hikA2, hikB2, hspk2, hek2, hct2, hrk2, hck2, hpqr2⟩ := preNXOK_iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) hsec0 hpub2 hpub4 hpub6 hek2_u he2_u (untagged_of_eq hPqxdhPrk4 uPqxdhPrk4) (untagged_of_eq hRk4 uRk4) (untagged_of_eq hCk4 uCk4) (untagged_of_eq hPqr4 uPqr4) (kemEncap_fst_untagged_of_e2 hinv.hent₂) (kemEncap_snd_untagged_of_e2 hinv.hent₂)
  have hstA₂ := trStateNX_iniAliceStartState tr₄ r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (untagged_of_eq hChainPrk4 uChainPrk4) hdhs2_u hikA2 hikB2 hspk2 hrk2 hck2 hpqr2 (untagged_of_eq hStARk4 uStARk4) (untagged_of_eq hCks4 uCks4); have hstA₂' := trStateNX_encSt tr₅ cl₅ hstA₂ hc5_u (untagged_of_eq hCks5 uCks5)
  have hsalt₅ := preNXOK_encSalt_ini tr₄ tr₅ r.bob (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) cl₅ (untagged_of_eq hPrk5 u5Prk) hpqr2
  have henc₅ := preNXOK_encOut_of tr₅ cl₅ (tr₅.length + 2) hstA₂ (untagged_of_eq hPrk5 u5Prk) hsalt₅ hpt5_u
    (gamma_symEnc_untagged_of_compAesPt3 hCipherKey5 hIv5 hd_pt5) hc5_r
    (untagged_of_eq hSeed5 uSeed5) (untagged_of_eq hCipherKey5 uCK5)
    (untagged_of_eq hMacKey5 uMK5) (untagged_of_eq hIv5 uIv5) hmac5_u
  intro u hu
  rcases hE r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown u hu with ha | hs
  · unfold Split81PrefixAtom at ha
    simp only [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, census_encOut_eq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | ⟨tr_bob, spqrMsgIdx₂, spqr₂', hbob_pin, hrecv, rfl⟩
    · exact hek1
    · exact hct1
    · exact henc₁
    · exact henc₂
    · exact hek2
    · exact hct2
    · exact henc₅
    · exact preNXOK_randTerm hpt1_u
    · exact preNXOK_randTerm hpt2_u
    · exact preNXOK_randTerm hpt5_u
    · exact preNXOK_serialize_local_tr (ls := ⟨r.alice, _⟩) hstA₁
    · exact preNXOK_serialize_local_tr (ls := ⟨r.alice, _⟩) hstA₁'
    · exact preNXOK_serialize_local_tr (ls := ⟨r.alice, _⟩) hstA₁''
    · exact preNXOK_serialize_local_tr (ls := ⟨r.alice, _⟩) hstA₂
    · exact preNXOK_serialize_local_tr (ls := ⟨r.alice, _⟩) hstA₂'
    · have hRk0' : gamma compI0 S g
          (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk =
          WsIdx1Split40MemoVals.wsRk0 := by rw [iniAliceOut_keys_eq]; exact hRk0
      obtain ⟨hprk1_b, hrk1_b, hck1_b, hprk2_b, hrk2_b, hcksB_b, hck1_next_b, hck1_next2_b⟩ := bob_chain_nx_81 hfits hp hinv hRk0' hbob_pin; have hdhsB_r : PreNXOK S g (randTerm tr_bob.length 32) := preNXOK_randTerm (untagged_of_eq hbob_pin wsBob3_untagged.2.2.2.2.2.2.2.2)
      have hrt : PreNXOK S g (DY.DiffieHellman.dhPk (iniAliceStartState tr₁ r.bob
          (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)).dhs) :=
        preNXOK_dhPk hstA₁.dhs
      have hsec2 : PreNXOK S g (setupSecret r 2) := by rw [CompSetupSecrecy.setupSecret_2 hNe]; exact h10
      have hc1 := preNXOK_createChain hprk1_b hrk1_b hck1_b hrk1 hrt hsec2; have hc2 := preNXOK_createChain hprk2_b hrk2_b hcksB_b hc1.1 hrt hdhsB_r; have hspqr := preNXOK_spqrRecv_state (preNXOK_spqrInit hpqr1 (preNXOK_lit _)) (preNXOK_spqrSendMsg hstA₁'.spqr hc2_r) hrecv
      refine preNXOK_serialize_local_tr (ls := ⟨r.bob, _⟩)
        { myIk := by show PreNXOK S g (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)); rw [CompSetupSecrecy.setupPublic_2 hNe]; exact preNXOK_serializedIk (preNXOK_dhPk h5)
          peerIk := by show PreNXOK S g (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)); rw [CompSetupSecrecy.setupPublic_0 hNe]; exact preNXOK_serializedIk (preNXOK_dhPk h0)
          rk := hc2.1, dhs := hdhsB_r, cks := hc2.2
          sid := preNXOK_concat (CompRMemoKnown.memoOK_x25519Key hrt) hrk1, spqr := hspqr
          recv := fun d hd => by
            simp only [bobSt81, List.mem_singleton] at hd; subst hd
            exact ⟨hrt, preNXOK_kdfCk_fst hck1_next2_b (preNXOK_kdfCk_fst hck1_next_b hc1.2)⟩ }
  · exact preNXOK_storedSecrets_wsIdx1 hfits hinv.compat hinv.mp.2.1.2.1 hinv.reach u hs
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoPreUntag
