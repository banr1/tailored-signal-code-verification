/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreNX
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HB

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPinRun Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreNX Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 (call0Rng_length)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def rng1Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng1Chars
def rng34Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng34Chars
def rng36Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng36Chars
theorem rngAt36_eq_fast : rngAt 36 = rng36Fast := by unfold rng36Fast; rw [rngAt36_eq_hex, rng36Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
def wsZMacZBytes : HwBytes := ((saltedValsFor wsSeed2 wsMacIn2 wsSaltZ).drop 5).headD []
def wsZMac1Bytes : HwBytes := ((saltedValsFor wsSeed2 wsMacIn2 wsSalt1).drop 5).headD []
def rVals40Base : List HwBytes := [ setup.aliceId, setup.bobId, setup.spk, fillFresh 16 64, rng1Fast, compKyberE1, rng34Fast, compAesPt1, compAesPt2, compAesCt1, compAesCt2, compKyberCt1, compKyberSs1 ]
def rVals40 : List HwBytes := (rVals40Base ++ (List.inits rng36Fast).tail) ++ (List.inits cliCoins2Fast).tail
def xVals40 : List HwBytes := [ compLookupPub (clamp setup.aliceId), compLookupPub (clamp setup.bobId), compLookupPub (clamp setup.spk), compLookupPub (clamp rng1Fast), compLookupPub (clamp rng34Fast), compLookupDh (clamp setup.aliceId) (compLookupPub (clamp setup.spk)), compLookupDh (clamp rng1Fast) (compLookupPub (clamp setup.bobId)), compLookupDh (clamp rng1Fast) (compLookupPub (clamp setup.spk)), compLookupDh (clamp rng34Fast) (compLookupPub (clamp setup.spk)) ]
def t8Vals40 : List HwBytes := [ wsMac1Bytes, wsMacD2.take 8, wsZMacZBytes, wsZMac1Bytes ]
def allVals40 : List HwBytes := rVals40 ++ xVals40 ++ t8Vals40
theorem allVals40_nodup : allVals40.Nodup := by decide +kernel
theorem singleton_sublist_of_mem {α : Type} {x : α} : ∀ {l : List α}, x ∈ l → List.Sublist [x] l
  | _ :: _, .head _ => .cons_cons _ (List.nil_sublist _)
  | _ :: _, .tail _ h => .cons _ (singleton_sublist_of_mem h)
theorem coinTerms_map_sublist {S : Sem} {g : Ghost} {tr : ExecTrace} {cl : Nat} {cs : List HwBytes}
    (h : cl ≠ 0 → gamma compI0 S g (randTerm (tr.length + 1) cl) ∈ cs) :
    List.Sublist ((coinTerms tr cl).map (gamma compI0 S g)) cs := by
  unfold coinTerms; split_ifs with h0
  · exact List.nil_sublist cs
  · exact singleton_sublist_of_mem (h h0)
theorem ws40_dh_comm :
    compLookupDh (clamp setup.spk) (compLookupPub (clamp setup.aliceId)) = compLookupDh (clamp setup.aliceId) (compLookupPub (clamp setup.spk)) ∧
    compLookupDh (clamp setup.bobId) (compLookupPub (clamp rng1Fast)) = compLookupDh (clamp rng1Fast) (compLookupPub (clamp setup.bobId)) ∧
    compLookupDh (clamp setup.spk) (compLookupPub (clamp rng1Fast)) = compLookupDh (clamp rng1Fast) (compLookupPub (clamp setup.spk)) ∧
    compLookupDh (clamp setup.spk) (compLookupPub (clamp rng34Fast)) =
      compLookupDh (clamp rng34Fast) (compLookupPub (clamp setup.spk)) := by decide +kernel
theorem compAesPerm_ws1_eq : compAesPerm wsCipherKey1 (wsIv1Full.take 16) compAesPt1 = compAesCt1 := by decide +kernel
theorem compAesPerm_ws2_eq : compAesPerm wsCipherKey2 (wsIv2Full.take 16) compAesPt2 = compAesCt2 := by decide +kernel
theorem schedBCall1SendFast_msgMac8 :
    (parsePreKeyWire (hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.hexDigit Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall1SendChars)).map
      WsIdx1Split40MemoCk1Pin.SP.msgMac8 = some wsMac1Bytes := by decide +kernel
theorem msgMac8_b1_eq {p₁ : PreKeyFields} (hp₁ : parsePreKeyWire WsIdx1Split40MemoCk1Pin.SP.schedBCall1SendBytes = some p₁) : WsIdx1Split40MemoCk1Pin.SP.msgMac8 p₁ = wsMac1Bytes := by
  have h := schedBCall1SendFast_msgMac8; rw [← WsIdx1Split40MemoCk1Pin.SP.schedBCall1SendBytes_eq, hp₁] at h; exact Option.some.inj h
attribute [local irreducible] bundle0 call0Rng ptAt rngAt sendAt setupPublic setupSecret
theorem gamma_kemEncap_fst_of_e1 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE1) : gamma compI0 S g (DY.PQKem.kemEncap pk e).1 = compKyberCt1 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_fst_eq h32,
      show compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) from rfl,
      Option.getD_some, he, WsIdx1Split40MemoPreNX.compKyberEncaps_e1, List.take_left' Census443Memo.kyberCtVals_lengths.2.1]
theorem gamma_kemEncap_snd_of_e1 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE1) : gamma compI0 S g (DY.PQKem.kemEncap pk e).2 = compKyberSs1 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32,
      show compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) from rfl,
      Option.getD_some, he, WsIdx1Split40MemoPreNX.compKyberEncaps_e1, List.drop_left' Census443Memo.kyberCtVals_lengths.2.1]
theorem gamma_zMac40_of_pins (S : Sem) (g : Ghost) (salt : DY.Bytes) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) {seed macIn saltB : HwBytes} (hsalt : gamma compI0 S g salt = saltB) (hseed : gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2 = seed) (hmsg : gamma compI0 S g (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (Census443Defs.encWire tr stA cl (tr.length + 2)))) = macIn) : gamma compI0 S g (zMac40 salt tr stA cl) = ((saltedValsFor seed macIn saltB).drop 5).headD [] := by
  simpa [saltedNodes40, zMac40] using congrArg (fun l => (l.drop 5).headD [])
    (WsIdx1Split40MemoZPin.gamma_saltedNodes40 S g salt tr stA cl hsalt hseed hmsg)
theorem split40_draw_pins_fast {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hlinks : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) : gamma compI0 S g (randTerm tr₁.length 32) = rng1Fast ∧ gamma compI0 S g (randTerm (tr₁.length + 2) 32) = rng34Fast ∧ gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1 ∧ gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ rng36Fast.inits ∧ (cl₁ ≠ 0 → gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (List.inits rng36Fast).tail) ∧ gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2 ∧ gamma compI0 S g (randTerm (tr₃.length + 1) cl₂) ∈ cliCoins2Fast.inits ∧ (cl₂ ≠ 0 → gamma compI0 S g (randTerm (tr₃.length + 1) cl₂) ∈ (List.inits cliCoins2Fast).tail) := by
  obtain ⟨hek_pin, hdhs_pin, hpt₁_pin, hc₁_mem, hc₁_tail, hpt₂_pin, hc₂_mem, hc₂_tail⟩ := split40_draw_eqs hinv hlinks
  rw [rngAt36_eq_fast] at hc₁_mem hc₁_tail
  exact ⟨hek_pin.trans rngAt1_eq_fast, hdhs_pin.trans rngAt34_eq_fast, hpt₁_pin, hc₁_mem, hc₁_tail, hpt₂_pin, hc₂_mem, hc₂_tail⟩
theorem msg1_keys_And_mac_pins {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) : gamma compI0 S g (keys40 tr₂ (stA1_40 r tr₁) cl₁).cipherKey = wsCipherKey1 ∧ gamma compI0 S g (keys40 tr₂ (stA1_40 r tr₁) cl₁).iv = wsIv1Full ∧ gamma compI0 S g (Census443Defs.encMac tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2)) = wsMac1Bytes := by
  let stA₁_c := stA1_40 r tr₁
  obtain ⟨p₁, hp₁⟩ := WsIdx1Split40MemoCk1Pin.parse_b1; have hmac := WsIdx1Split40MemoCk1Pin.encMac_msg1 hinv hp₁; obtain ⟨hK, hP, _, _⟩ := SB.saltAndSeedPin_s1_1 S g tr₂ stA₁_c cl₁ (Or.inl hp₁) hmac; have hP' : gamma compI0 S g (WsIdx1Split40MemoVals.SP.encPrk tr₂ stA₁_c cl₁ (tr₂.length + 2)) = ws1Prk := hP.trans wsPrk_eq_ws1Prk; have hK' : gamma compI0 S g (WsIdx1Split40MemoVals.SP.encKeys tr₂ stA₁_c cl₁ (tr₂.length + 2)).macKey = ws1MacKey := hK.trans wsMacKey_eq_ws1MacKey
  have hCK : gamma compI0 S g (WsIdx1Split40MemoVals.SP.encKeys tr₂ stA₁_c cl₁ (tr₂.length + 2)).cipherKey = wsCipherKey1 := by rw [WsIdx1Split40MemoVals.encKeys_cipherKey, WsIdx1Split40MemoVals.gamma_hmac_of S g hP' (WsIdx1Split40MemoVals.gamma_concat_of S g (WsIdx1Split40MemoVals.gamma_wmk S g) (WsIdx1Split40MemoVals.gamma_litByte_1 S g))]; exact WsIdx1Split40MemoVals.wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.1
  have hIV : gamma compI0 S g (WsIdx1Split40MemoVals.SP.encKeys tr₂ stA₁_c cl₁ (tr₂.length + 2)).iv = wsIv1Full := by rw [WsIdx1Split40MemoVals.encKeys_iv, WsIdx1Split40MemoVals.gamma_hmac_of S g hP' (WsIdx1Split40MemoVals.gamma_concat_of S g hK' (WsIdx1Split40MemoVals.gamma_concat_of S g (WsIdx1Split40MemoVals.gamma_wmk S g) (WsIdx1Split40MemoVals.gamma_litByte_3 S g)))]; exact WsIdx1Split40MemoVals.wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨hCK, hIV, hmac.trans (msgMac8_b1_eq hp₁)⟩
theorem split40_table_pins {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hlinks : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) : (rTerms40Base r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g) = rVals40Base ∧ (xTerms40 tr₁).map (gamma compI0 S g) = xVals40 ∧ (t8Terms40 r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g) = t8Vals40 := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hc : Compat compI0 r S g := hinv.compat
  have h0 : gamma compI0 S g (randTerm 0 32) = setup.aliceId := by rw [← CompSetupSecrecy.setupSecret_0 hNe, CompRX0Bytes.gamma_setupSecret_0 hNe hc, hfits.1.2.2.2.2.2.2.1]
  have h5 : gamma compI0 S g (randTerm 5 32) = setup.bobId := by rw [← CompSetupSecrecy.setupSecret_1 hNe, CompRX0Bytes.gamma_setupSecret_1 hNe hc, hfits.1.2.2.2.2.2.2.2.1]
  have h10 : gamma compI0 S g (randTerm 10 32) = setup.spk := by rw [← CompSetupSecrecy.setupSecret_2 hNe, CompRX0Bytes.gamma_setupSecret_2 hNe hc, hfits.1.2.2.2.2.2.2.2.2.1]
  have h16 : gamma compI0 S g (randTerm 16 64) = fillFresh 16 64 := by rw [← CompSetupSecrecy.setupSecret_4 hNe, CompC2PreUntagged38.gamma_setupSecret_4 hNe hc, (CompFitsNames.compFits_secretBytes_fresh hfits).2.1]
  obtain ⟨hek, hdhs, hpt₁, _, _, hpt₂, _, _⟩ := split40_draw_pins_fast hinv hlinks; have he₁ := hinv.hent₁; obtain ⟨hck₁, hiv₁, hmac₁⟩ := msg1_keys_And_mac_pins hinv
  have hct₁ : gamma compI0 S g (DY.SymEnc.symEnc (keys40 tr₂ (stA1_40 r tr₁) cl₁).cipherKey (keys40 tr₂ (stA1_40 r tr₁) cl₁).iv (randTerm tr₂.length 32)) = compAesCt1 := by rw [CompC3RestFn38HBA.gamma_symEnc_compI0_eq, hck₁, hiv₁, hpt₁, compAesPerm_ws1_eq]
  have hkdf := WsIdx1Split40MemoVals.split40KdfPins r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv; have hck₂ : gamma compI0 S g (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).cipherKey = wsCipherKey2 := hkdf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; have hiv₂ : gamma compI0 S g (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).iv = wsIv2Full := hkdf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hct₂ : gamma compI0 S g (DY.SymEnc.symEnc (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).cipherKey (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).iv (randTerm tr₃.length 32)) = compAesCt2 := by rw [CompC3RestFn38HBA.gamma_symEnc_compI0_eq, hck₂, hiv₂, hpt₂, compAesPerm_ws2_eq]
  have hkct : gamma compI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).1 =
      compKyberCt1 := gamma_kemEncap_fst_of_e1 he₁
  have hkss : gamma compI0 S g (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2 =
      compKyberSs1 := gamma_kemEncap_snd_of_e1 he₁
  have hmapR : (rTerms40Base r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g) = rVals40Base := by simp only [rTerms40Base, rVals40Base, List.map_cons, List.map_nil, h0, h5, h10, h16, hek, he₁, hdhs, hpt₁, hpt₂, hct₁, hct₂, hkct, hkss]
  have hag1 := CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 h0 ws40_dh_comm.1; have hag2 := CompC3RestFn38HB.gamma_agree_dhPk_of_eq h5 hek ws40_dh_comm.2.1; have hag3 := CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 hek ws40_dh_comm.2.2.1; have hag4 := CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 hdhs ws40_dh_comm.2.2.2
  have hmapX : (xTerms40 tr₁).map (gamma compI0 S g) = xVals40 := by simp only [xTerms40, xVals40, List.map_cons, List.map_nil, CompFreshDistinct.gamma_dhPk_compI0, h0, h5, h10, hek, hdhs, hag1, hag2, hag3, hag4]
  have hmac₂ : gamma compI0 S g (Census443Defs.encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) = wsMacD2.take 8 := (hinv.hwire₂ p hp).2.1.trans (WsIdx1Split40MemoZPinRun.wsMac8 hp); obtain ⟨hseed₂, hmsg₂, hck_salt⟩ := WsIdx1Split40MemoCk1Pin.split40ZPins r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv
  have hzmacZ : gamma compI0 S g (zMac40 DY.Spqr.zeroKey tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂) = wsZMacZBytes := gamma_zMac40_of_pins S g DY.Spqr.zeroKey tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (WsIdx1Split40MemoZPin.gamma_zeroKey S g) hseed₂ hmsg₂; have hzmac1 : gamma compI0 S g (zMac40 (ck1Salt40 r tr₁) tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂) = wsZMac1Bytes := gamma_zMac40_of_pins S g (ck1Salt40 r tr₁) tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ hck_salt hseed₂ hmsg₂
  have hmapT8 : (t8Terms40 r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g) = t8Vals40 := by simp only [t8Terms40, t8Vals40, List.map_cons, List.map_nil, hmac₁, hmac₂, hzmacZ, hzmac1]
  exact ⟨hmapR, hmapX, hmapT8⟩
theorem rTerms40_map_sublist {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hlinks : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) : List.Sublist ((rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g)) rVals40 := by
  have hd := split40_draw_pins_fast hinv hlinks
  unfold rTerms40 rVals40
  rw [List.map_append, List.map_append, (split40_table_pins hfits hp hinv hlinks).1]
  exact ((List.Sublist.refl _).append (coinTerms_map_sublist hd.2.2.2.2.1)).append (coinTerms_map_sublist hd.2.2.2.2.2.2.2)
theorem rv40_mem_rVals40 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hlinks : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) {v : HwBytes} (hv : Rv40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ v) : v ∈ rVals40 :=
  (rTerms40_map_sublist hfits hp hinv hlinks).subset hv
theorem split40TblNodup : Split40TblNodup := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hlinks
  obtain ⟨_, hmapX, hmapT8⟩ := split40_table_pins hfits hp hinv hlinks
  have hsub : List.Sublist ((allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g)) allVals40 := by
    unfold allTerms40 allVals40
    rw [List.map_append, List.map_append, hmapX, hmapT8]
    exact ((rTerms40_map_sublist hfits hp hinv hlinks).append (List.Sublist.refl _)).append (List.Sublist.refl _)
  exact allVals40_nodup.sublist hsub
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl
