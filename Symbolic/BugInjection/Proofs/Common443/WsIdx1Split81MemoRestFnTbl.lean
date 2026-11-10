/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnTbl
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
open DY DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPinRun Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreNX Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead78 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 (call0Rng_length)
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def rng41Chars : List Char := chars_of_hex (rngAt 41)
theorem bobRng41Bytes_eq_hex : bobRng41Bytes = hexBytes (str_of_hex (rngAt 41)) := rfl
theorem rng41Str_eq : (str_of_hex (rngAt 41)) = String.ofList rng41Chars := rfl
def bobRng41Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng41Chars
theorem bobRng41Bytes_eq_fast : bobRng41Bytes = bobRng41Fast := by unfold bobRng41Fast; rw [bobRng41Bytes_eq_hex, rng41Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
attribute [local irreducible] bobRng41Bytes
def rng44Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng44Chars
def rng77Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng77Chars
def rng79Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng79Chars
theorem rngAt79_eq_fast : rngAt 79 = rng79Fast := by unfold rng79Fast; rw [rngAt79_eq_hex, rng79Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
def wsMac2Bytes : HwBytes := wsMacD2.take 8
def wsMac5Bytes : HwBytes := eval_hwbytes81 (((parsePreKeyWire Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall5SendFast).map WsIdx1Split81MemoZPinRun.SP.msgMac8).getD [])
def wsZMac81ZBytes : HwBytes := ((saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSaltZ).drop 5).headD []
def wsZMac81_1Bytes : HwBytes := ((saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt1).drop 5).headD []
def wsZMac81_2Bytes : HwBytes := ((saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt2).drop 5).headD []
def wsZMac81_5Bytes : HwBytes := ((saltedValsFor WsIdx1O4Tag.wsSeed6 wsMacIn1 wsSalt5).drop 5).headD []
def rVals81ExtBase : List HwBytes := [ bobRng41Bytes, rng44Fast, compKyberE2, rng77Fast, compAesPt3, compAesCt3, compKyberCt2, compKyberSs2 ]
def rVals81Ext : List HwBytes := rVals81ExtBase ++ (List.inits rng79Fast).tail
def rVals81 : List HwBytes := rVals40 ++ rVals81Ext
def xVals81Ext : List HwBytes := [ compLookupPub (clamp bobRng41Bytes), compLookupPub (clamp rng44Fast), compLookupPub (clamp rng77Fast), compLookupDh (clamp bobRng41Bytes) (compLookupPub (clamp rng34Fast)), compLookupDh (clamp rng44Fast) (compLookupPub (clamp setup.bobId)), compLookupDh (clamp rng44Fast) (compLookupPub (clamp setup.spk)), compLookupDh (clamp rng77Fast) (compLookupPub (clamp setup.spk)) ]
def xVals81 : List HwBytes := xVals40 ++ xVals81Ext
def t8Vals81 : List HwBytes := [ wsMac1Bytes, wsMac2Bytes, wsMac5Bytes, wsZMac81ZBytes, wsZMac81_1Bytes, wsZMac81_2Bytes, wsZMac81_5Bytes ]
def allVals81 : List HwBytes := rVals81 ++ xVals81 ++ t8Vals81
theorem allVals81_nodup : allVals81.Nodup := by
  unfold allVals81 rVals81 rVals81Ext rVals81ExtBase xVals81 xVals81Ext
  rw [bobRng41Bytes_eq_fast]; decide +kernel
theorem ws81_dh_comm : compLookupDh (clamp rng34Fast) (compLookupPub (clamp bobRng41Bytes)) = compLookupDh (clamp bobRng41Bytes) (compLookupPub (clamp rng34Fast)) ∧ compLookupDh (clamp setup.bobId) (compLookupPub (clamp rng44Fast)) = compLookupDh (clamp rng44Fast) (compLookupPub (clamp setup.bobId)) ∧ compLookupDh (clamp setup.spk) (compLookupPub (clamp rng44Fast)) = compLookupDh (clamp rng44Fast) (compLookupPub (clamp setup.spk)) ∧ compLookupDh (clamp setup.spk) (compLookupPub (clamp rng77Fast)) = compLookupDh (clamp rng77Fast) (compLookupPub (clamp setup.spk)) := by rw [bobRng41Bytes_eq_fast]; decide +kernel
theorem compAesPerm_ws5_eq : compAesPerm wsCipherKey5 (wsIv5Full.take 16) compAesPt3 = compAesCt3 := by decide +kernel
theorem schedBCall2SendFast_msgMac8 :
    (parsePreKeyWire (hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.hexDigit Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2SendChars)).map
      WsIdx1Split81MemoZPinRun.SP.msgMac8 = some wsMac2Bytes := by decide +kernel
theorem msgMac8_b2_eq {p₂ : PreKeyFields} (hp₂ : parsePreKeyWire WsIdx1Split81MemoZPinRun.SP.schedBCall2SendBytes = some p₂) : WsIdx1Split81MemoZPinRun.SP.msgMac8 p₂ = wsMac2Bytes := by
  have h := schedBCall2SendFast_msgMac8; rw [← WsIdx1Split81MemoZPinRun.SP.schedBCall2SendBytes_eq, hp₂] at h; exact Option.some.inj h
theorem schedBCall5SendFast_msgMac8 :
    (parsePreKeyWire (hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.hexDigit Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall5SendChars)).map
      WsIdx1Split81MemoZPinRun.SP.msgMac8 = some wsMac5Bytes := by decide +kernel
theorem msgMac8_b5_eq {p₅ : PreKeyFields} (hp₅ : parsePreKeyWire WsIdx1Split81MemoZPinRun.SP.schedBCall5SendBytes = some p₅) : WsIdx1Split81MemoZPinRun.SP.msgMac8 p₅ = wsMac5Bytes := by
  have h := schedBCall5SendFast_msgMac8; rw [← WsIdx1Split81MemoZPinRun.SP.schedBCall5SendBytes_eq, hp₅] at h; exact Option.some.inj h
attribute [local irreducible] bundle0 call0Rng call4Rng ptAt rngAt sendAt wireAt setupPublic setupSecret
theorem gamma_zMac81_of_pins (r : Records) (S : Sem) (g : Ghost) (salt : DY.Bytes) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) {seed macIn saltB : HwBytes} (hsalt : gamma compI0 S g salt = saltB) (hseed : gamma compI0 S g (bobSeed81 r tr₁ tr₂ tr₄ cl₁) = seed) (hmsg : gamma compI0 S g (DY.Concat.concat (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)) (DY.Concat.concat (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)) (Census443Defs.encWire tr₂ (stA81 r tr₁) cl₁ (tr₂.length + 2)))) = macIn) : gamma compI0 S g (zMac81 r salt tr₁ tr₂ tr₄ cl₁) = ((saltedValsFor seed macIn saltB).drop 5).headD [] := by
  simpa [saltedNodes81, zMac81] using congrArg (fun l => (l.drop 5).headD [])
    (WsIdx1Split81MemoZPin.gamma_saltedNodes81 r S g salt tr₁ tr₂ tr₄ cl₁ hsalt hseed hmsg)
theorem split81_draw_pins_fast {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : gamma compI0 S g (randTerm tr₁.length 32) = rng1Fast ∧ gamma compI0 S g (randTerm (tr₁.length + 2) 32) = rng34Fast ∧ gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1 ∧ gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ List.inits rng36Fast ∧ (cl₁ ≠ 0 → gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (List.inits rng36Fast).tail) ∧ gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2 ∧ gamma compI0 S g (randTerm tr₄.length 32) = rng44Fast ∧ gamma compI0 S g (randTerm (tr₄.length + 2) 32) = rng77Fast ∧ gamma compI0 S g (randTerm tr₅.length 32) = compAesPt3 ∧ gamma compI0 S g (randTerm (tr₅.length + 1) cl₅) ∈ List.inits rng79Fast ∧ (cl₅ ≠ 0 → gamma compI0 S g (randTerm (tr₅.length + 1) cl₅) ∈ (List.inits rng79Fast).tail) := by obtain ⟨h1, h34, hpt1, h36, h36t, hpt2, _, _, h44, h77, hpt5, h79, h79t⟩ := split81_draw_pins_raw hinv hlinks; exact ⟨h1.trans rngAt1_eq_fast, h34.trans rngAt34_eq_fast, hpt1, WsIdx1Split40MemoRestFnTbl.rngAt36_eq_fast ▸ h36, WsIdx1Split40MemoRestFnTbl.rngAt36_eq_fast ▸ h36t, hpt2, h44.trans rngAt44_eq_fast, h77.trans rngAt77_eq_fast, hpt5, rngAt79_eq_fast ▸ h79, rngAt79_eq_fast ▸ h79t⟩
theorem split81_table_pins {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hbob : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes) : (rTerms40Base r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g) = rVals40Base ∧ (rTerms81ExtBase r tr_bob tr₄ tr₅ cl₅).map (gamma compI0 S g) = rVals81ExtBase ∧ (xTerms81 tr₁ tr_bob tr₄).map (gamma compI0 S g) = xVals81 ∧ (t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅).map (gamma compI0 S g) = t8Vals81 ∧ (cl₁ ≠ 0 → gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (List.inits rng36Fast).tail) ∧ (cl₅ ≠ 0 → gamma compI0 S g (randTerm (tr₅.length + 1) cl₅) ∈ (List.inits rng79Fast).tail) := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hc : Compat compI0 r S g := hinv.compat
  have h0 : gamma compI0 S g (randTerm 0 32) = setup.aliceId := by rw [← CompSetupSecrecy.setupSecret_0 hNe, CompRX0Bytes.gamma_setupSecret_0 hNe hc, hfits.1.2.2.2.2.2.2.1]
  have h5 : gamma compI0 S g (randTerm 5 32) = setup.bobId := by rw [← CompSetupSecrecy.setupSecret_1 hNe, CompRX0Bytes.gamma_setupSecret_1 hNe hc, hfits.1.2.2.2.2.2.2.2.1]
  have h10 : gamma compI0 S g (randTerm 10 32) = setup.spk := by rw [← CompSetupSecrecy.setupSecret_2 hNe, CompRX0Bytes.gamma_setupSecret_2 hNe hc, hfits.1.2.2.2.2.2.2.2.2.1]
  have h16 : gamma compI0 S g (randTerm 16 64) = fillFresh 16 64 := by rw [← CompSetupSecrecy.setupSecret_4 hNe, CompC2PreUntagged38.gamma_setupSecret_4 hNe hc, (CompFitsNames.compFits_secretBytes_fresh hfits).2.1]
  obtain ⟨hek₁, hdhs₁, hpt₁, _, hc₁t, hpt₂, hek₂, hdhs₂, hpt₅, _, hc₅t⟩ := split81_draw_pins_fast hinv hlinks; have he₁ := hinv.hent₁; have he₂ := hinv.hent₂; have hs1 := WsIdx1Split81MemoVals.split81S1KdfPins r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hp hinv; have hck₁ : gamma compI0 S g (keys40 tr₂ (stA1_40 r tr₁) cl₁).cipherKey = wsCipherKey1 := hs1.2.2.2.1; have hiv₁ : gamma compI0 S g (keys40 tr₂ (stA1_40 r tr₁) cl₁).iv = wsIv1Full := hs1.2.2.2.2.1
  have hck₂ : gamma compI0 S g (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).cipherKey = wsCipherKey2 := hs1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; have hiv₂ : gamma compI0 S g (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).iv = wsIv2Full := hs1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; have hs2 := WsIdx1Split81MemoVals.split81S2KdfPins r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hinv
  have hck₅ : gamma compI0 S g (keys40 tr₅ (stA2_81 r tr₄) cl₅).cipherKey = wsCipherKey5 := hs2.2.2.2.2.2.2.2.2.2.2.2.2.1; have hiv₅ : gamma compI0 S g (keys40 tr₅ (stA2_81 r tr₄) cl₅).iv = wsIv5Full := hs2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hct₁ : gamma compI0 S g (DY.SymEnc.symEnc (keys40 tr₂ (stA1_40 r tr₁) cl₁).cipherKey (keys40 tr₂ (stA1_40 r tr₁) cl₁).iv (randTerm tr₂.length 32)) = compAesCt1 := by rw [CompC3RestFn38HBA.gamma_symEnc_compI0_eq, hck₁, hiv₁, hpt₁, WsIdx1Split40MemoRestFnTbl.compAesPerm_ws1_eq]
  have hct₂ : gamma compI0 S g (DY.SymEnc.symEnc (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).cipherKey (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).iv (randTerm tr₃.length 32)) = compAesCt2 := by rw [CompC3RestFn38HBA.gamma_symEnc_compI0_eq, hck₂, hiv₂, hpt₂, WsIdx1Split40MemoRestFnTbl.compAesPerm_ws2_eq]
  have hct₅ : gamma compI0 S g (DY.SymEnc.symEnc (keys40 tr₅ (stA2_81 r tr₄) cl₅).cipherKey (keys40 tr₅ (stA2_81 r tr₄) cl₅).iv (randTerm tr₅.length 32)) = compAesCt3 := by rw [CompC3RestFn38HBA.gamma_symEnc_compI0_eq, hck₅, hiv₅, hpt₅, compAesPerm_ws5_eq]
  have hmapR40 : (rTerms40Base r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g) = rVals40Base := by simp only [rTerms40Base, rVals40Base, List.map_cons, List.map_nil, h0, h5, h10, h16, hek₁, he₁, hdhs₁, hpt₁, hpt₂, hct₁, hct₂, gamma_kemEncap_fst_of_e1 he₁, gamma_kemEncap_snd_of_e1 he₁]
  have hmapR81Ext : (rTerms81ExtBase r tr_bob tr₄ tr₅ cl₅).map (gamma compI0 S g) = rVals81ExtBase := by simp only [rTerms81ExtBase, rVals81ExtBase, List.map_cons, List.map_nil, hbob, hek₂, he₂, hdhs₂, hpt₅, hct₅, gamma_kemEncap_fst_of_e2 he₂, gamma_kemEncap_snd_of_e2 he₂]
  have hmapX40 : (xTerms40 tr₁).map (gamma compI0 S g) = xVals40 := by simp only [xTerms40, xVals40, List.map_cons, List.map_nil, CompFreshDistinct.gamma_dhPk_compI0, h0, h5, h10, hek₁, hdhs₁, CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 h0 ws40_dh_comm.1, CompC3RestFn38HB.gamma_agree_dhPk_of_eq h5 hek₁ ws40_dh_comm.2.1, CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 hek₁ ws40_dh_comm.2.2.1, CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 hdhs₁ ws40_dh_comm.2.2.2]
  have hmapX81Ext : (xTerms81Ext tr₁ tr_bob tr₄).map (gamma compI0 S g) = xVals81Ext := by simp only [xTerms81Ext, xVals81Ext, List.map_cons, List.map_nil, CompFreshDistinct.gamma_dhPk_compI0, hbob, hek₂, hdhs₂, CompC3RestFn38HB.gamma_agree_dhPk_of_eq hdhs₁ hbob ws81_dh_comm.1, CompC3RestFn38HB.gamma_agree_dhPk_of_eq h5 hek₂ ws81_dh_comm.2.1, CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 hek₂ ws81_dh_comm.2.2.1, CompC3RestFn38HB.gamma_agree_dhPk_of_eq h10 hdhs₂ ws81_dh_comm.2.2.2]
  have hmapX : (xTerms81 tr₁ tr_bob tr₄).map (gamma compI0 S g) = xVals81 := by rw [xTerms81_eq_append, List.map_append, hmapX40, hmapX81Ext]; rfl
  obtain ⟨p₁, hp₁⟩ := WsIdx1Split40MemoCk1Pin.parse_b1; obtain ⟨p₂, hp₂⟩ := WsIdx1Split81MemoZPinRun.parse_b2; obtain ⟨p₅, hp₅⟩ := WsIdx1Split81MemoZPinRun.parse_b5; obtain ⟨⟨_, hmac₁_raw⟩, ⟨_, hmac₂_raw⟩, ⟨_, hmac₅_raw⟩⟩ := WsIdx1Split81MemoZPinRun.encWire_and_encMac_msgs_81 hinv hp₁ hp₂ hp₅; have hmac₁ : gamma compI0 S g (Census443Defs.encMac tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2)) = wsMac1Bytes := hmac₁_raw.trans (msgMac8_b1_eq hp₁)
  have hmac₂ : gamma compI0 S g (Census443Defs.encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2)) = wsMac2Bytes := hmac₂_raw.trans (msgMac8_b2_eq hp₂); have hmac₅ : gamma compI0 S g (Census443Defs.encMac tr₅ (stA2_81 r tr₄) cl₅ (tr₅.length + 2)) = wsMac5Bytes := hmac₅_raw.trans (msgMac8_b5_eq hp₅); have hseed81 := WsIdx1Split81MemoZPin.gamma_bobSeed81 hfits hp hinv; have hmsg81 := WsIdx1Split81MemoZPin.gamma_macIn81 hfits hp hinv
  obtain ⟨hsalt2, hsalt5⟩ := WsIdx1Split81MemoZPinRun.split81ZPins r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv; have hzmacZ : gamma compI0 S g (zMac81 r DY.Spqr.zeroKey tr₁ tr₂ tr₄ cl₁) = wsZMac81ZBytes := gamma_zMac81_of_pins r S g DY.Spqr.zeroKey tr₁ tr₂ tr₄ cl₁ (WsIdx1Split40MemoZPin.gamma_zeroKey S g) hseed81 hmsg81
  have hzmac1 : gamma compI0 S g (zMac81 r (ck1Salt40 r tr₁) tr₁ tr₂ tr₄ cl₁) = wsZMac81_1Bytes := gamma_zMac81_of_pins r S g (ck1Salt40 r tr₁) tr₁ tr₂ tr₄ cl₁ (WsIdx1Split81MemoZPin.gamma_ck1Salt40_ws81Idx1 hp hinv).1 hseed81 hmsg81; have hzmac2 : gamma compI0 S g (zMac81 r (send2Salt81 r tr₁ tr₂ tr₃ cl₁ cl₂) tr₁ tr₂ tr₄ cl₁) = wsZMac81_2Bytes := gamma_zMac81_of_pins r S g (send2Salt81 r tr₁ tr₂ tr₃ cl₁ cl₂) tr₁ tr₂ tr₄ cl₁ hsalt2 hseed81 hmsg81
  have hzmac5 : gamma compI0 S g (zMac81 r (ck5Salt81 r tr₄) tr₁ tr₂ tr₄ cl₁) = wsZMac81_5Bytes := gamma_zMac81_of_pins r S g (ck5Salt81 r tr₄) tr₁ tr₂ tr₄ cl₁ hsalt5 hseed81 hmsg81
  have hmapT8 : (t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅).map (gamma compI0 S g) = t8Vals81 := by simp only [t8Terms81, t8Vals81, List.map_cons, List.map_nil, hmac₁, hmac₂, hmac₅, hzmacZ, hzmac1, hzmac2, hzmac5]
  exact ⟨hmapR40, hmapR81Ext, hmapX, hmapT8, hc₁t, hc₅t⟩
theorem rTerms81_map_sublist {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hbob : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes) : List.Sublist ((rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅).map (gamma compI0 S g)) rVals81 := by
  obtain ⟨hR40, hR81Ext, _, _, hc1, hc5⟩ := split81_table_pins hfits hp hinv hlinks hbob
  have hc2 := (split81_draw_pins_raw hinv hlinks).2.2.2.2.2.2.2.1
  unfold rTerms81 rTerms40 rTerms81Ext rVals81 rVals40 rVals81Ext
  rw [List.map_append, List.map_append, List.map_append, List.map_append, hR40, hR81Ext]
  exact (((List.Sublist.refl _).append (coinTerms_map_sublist hc1)).append (coinTerms_map_sublist hc2)).append
    ((List.Sublist.refl _).append (coinTerms_map_sublist hc5))
theorem rv81_mem_rVals81 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hlinks : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (hbob : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes) {v : HwBytes} (hv : Rv81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ v) : v ∈ rVals81 :=
  (rTerms81_map_sublist hfits hp hinv hlinks hbob).subset hv
theorem split81TblNodup : Split81TblNodup := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hlinks tr_bob hbob
  obtain ⟨_, _, hX, hT8, _, _⟩ := split81_table_pins hfits hp hinv hlinks hbob
  have hsub : List.Sublist ((allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅).map (gamma compI0 S g)) allVals81 := by
    unfold allTerms81 allVals81
    rw [List.map_append, List.map_append, hX, hT8]
    exact ((rTerms81_map_sublist hfits hp hinv hlinks hbob).append (List.Sublist.refl _)).append (List.Sublist.refl _)
  exact allVals81_nodup.sublist hsub
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnTbl
