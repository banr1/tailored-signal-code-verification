/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCk1Pin
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum
public import Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38PC2_S1

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKK
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKdf Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38Pre Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38PC2_S1 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
attribute [local irreducible] Symbolic.BugInjection.hexBytes setupSecret setupPublic setupTrace
def node6Msg2Gen (tr₁ tr₂ tr₃ : ExecTrace) (b : DY.Participant)
    (ikA ikBPk spkPk pqPk : DY.Bytes) (cl₁ cl₂ : Nat) : Fin 6 → DY.Bytes :=
  let o := CompPrefixInvAlice.iniAliceOut tr₁ ikA ikBPk spkPk pqPk none
  let stA := CompPrefixInvAlice.iniAliceStartState tr₁ b o
  let stA' := CompPrefixInvEnc.encSt tr₂ stA cl₁
  let salt₂ := CompPrefixInvEnc.encSalt tr₃ stA' cl₂ (tr₃.length + 2)
  let seed₂ := (DY.Libsignal.TripleRatchet.kdfCk stA'.cks).2
  let mk₂ := DY.Libsignal.TripleRatchet.trMsgKeys salt₂ seed₂
  fun
  | ⟨0, _⟩ => (DY.Libsignal.TripleRatchet.kdfCk stA'.cks).1
  | ⟨1, _⟩ => seed₂
  | ⟨2, _⟩ => DY.KdfExtract.kdfExtract salt₂ seed₂
  | ⟨3, _⟩ => mk₂.cipherKey
  | ⟨4, _⟩ => mk₂.macKey
  | ⟨5, _⟩ => mk₂.iv
def macNode40Msg2Gen (tr₁ tr₂ tr₃ : ExecTrace) (b : DY.Participant)
    (ikA ikBPk spkPk pqPk : DY.Bytes) (cl₁ cl₂ : Nat) : DY.Bytes :=
  let o := CompPrefixInvAlice.iniAliceOut tr₁ ikA ikBPk spkPk pqPk none
  let stA := CompPrefixInvAlice.iniAliceStartState tr₁ b o
  let stA' := CompPrefixInvEnc.encSt tr₂ stA cl₁
  let salt₂ := CompPrefixInvEnc.encSalt tr₃ stA' cl₂ (tr₃.length + 2)
  let seed₂ := (DY.Libsignal.TripleRatchet.kdfCk stA'.cks).2
  let mk₂ := DY.Libsignal.TripleRatchet.trMsgKeys salt₂ seed₂
  DY.KdfExtract.kdfExtract mk₂.macKey (DY.Concat.concat stA'.myIk (DY.Concat.concat stA'.peerIk (CompPrefixInvEnc.encWire tr₃ stA' cl₂ (tr₃.length + 2))))
structure Nodes40Msg2 (P : DY.Bytes → Prop) (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : Prop where
  ck2 : P (node6Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂ ⟨0, by decide⟩)
  seed2 : P (node6Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂ ⟨1, by decide⟩)
  prkMk2 : P (node6Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂ ⟨2, by decide⟩)
  cipher2 : P (node6Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂ ⟨3, by decide⟩)
  macKey2 : P (node6Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂ ⟨4, by decide⟩)
  iv2 : P (node6Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂ ⟨5, by decide⟩)
  mac2 : P (macNode40Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂)
section Walk40
variable {S : Sem} {g : Ghost} {P : DY.Bytes → Prop}
theorem trStateP_encSt40 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat)
    (hN₁ : Nodes38 P r tr₁ tr₂ cl₁) (hN₂ : Nodes40Msg2 P r tr₁ tr₂ tr₃ cl₁ cl₂) :
    TRStateP S g P (CompPrefixInvEnc.encSt tr₃ (CompPrefixInvEnc.encSt tr₂ (stA38 r tr₁) cl₁) cl₂) :=
  have hst' := trStateP_encSt38 (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁
  { hst' with
    cks := kc_kdfExtract hN₂.ck2 hst'.cks (kc_lit _)
    spqr := kc_spqrSendState hst'.spqr (kc_randTerm _ _) }
theorem kc_encOut40_2 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (hN₁ : Nodes38 P r tr₁ tr₂ cl₁) (hN₂ : Nodes40Msg2 P r tr₁ tr₂ tr₃ cl₁ cl₂) : KC S g P (CompPrefixInvEnc.encOut tr₃ (CompPrefixInvEnc.encSt tr₂ (stA38 r tr₁) cl₁) cl₂ (tr₃.length + 2)) := by
  have hst' := trStateP_encSt38 (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁
  let stA' := CompPrefixInvEnc.encSt tr₂ (stA38 r tr₁) cl₁
  let salt₂ := CompPrefixInvEnc.encSalt tr₃ stA' cl₂ (tr₃.length + 2)
  have hsalt₂ : KC S g P salt₂ := by change KC S g P (Census443Defs.encSalt tr₃ (Census443Defs.encSt tr₂ (stA38 r tr₁) cl₁) cl₂ (tr₃.length + 2)); rw [CompRSchedBSalts.encSalt_encSt_eq_sendKeyPack]; exact CompRMemoKnown.memoOK_spqrSendKey_pack hst'.spqr (kc_randTerm _ _)
  have hprkMk₂ := kc_kdfExtract hN₂.prkMk2 hsalt₂ (kc_kdfExtract hN₂.seed2 hst'.cks (kc_lit _)); have hcipher₂ := kc_hkdfBlock1 hN₂.cipher2 hprkMk₂ (kc_lit _); have hmacKey₂ := kc_hkdfBlock2 hN₂.cipher2 hN₂.macKey2 hprkMk₂ (kc_lit _); have hiv₂ := kc_hkdfBlock3 hN₂.cipher2 hN₂.macKey2 hN₂.iv2 hprkMk₂ (kc_lit _)
  have hwire₂ : KC S g P (CompPrefixInvEnc.encWire tr₃ stA' cl₂ (tr₃.length + 2)) := kc_trWire (kc_dhPk hst'.dhs) (kc_symEnc hcipher₂ hiv₂ (kc_randTerm _ _)) (kc_spqrSendMsg hst'.spqr (kc_randTerm (tr₃.length + 1) cl₂)); exact kc_concat hwire₂ (kc_trunc8 (kc_kdfExtract hN₂.mac2 hmacKey₂ (kc_concat hst'.myIk (kc_concat hst'.peerIk hwire₂))))
theorem kc_prefixAtom_40 {r : Records} (hNe : r.alice ≠ r.bob) {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hN₁ : Nodes38 P r tr₁ tr₂ cl₁) (hN₂ : Nodes40Msg2 P r tr₁ tr₂ tr₃ cl₁ cl₂) {u : DY.Bytes} (hu : Split40PrefixAtom r tr₁ tr₂ tr₃ cl₁ cl₂ u) : KC S g P u := by
  have ho := kc_aliceOut (S := S) (g := g) hNe tr₁ tr₂ cl₁ hN₁; unfold Split40PrefixAtom at hu; dsimp only at hu; rw [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, census_encOut_eq] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.2.2.2.1
  · exact ho.2.2.2.2.1
  · exact kc_encOut38 hNe tr₁ tr₂ cl₁ hN₁
  · exact kc_encOut40_2 hNe tr₁ tr₂ tr₃ cl₁ cl₂ hN₁ hN₂
  · exact kc_randTerm _ _
  · exact kc_randTerm _ _
  · exact kc_serialize_local_tr (trStateP_stA38 hNe tr₁ tr₂ cl₁ hN₁)
  · exact kc_serialize_local_tr (trStateP_encSt38 hNe tr₁ tr₂ cl₁ hN₁)
  · exact kc_serialize_local_tr (trStateP_encSt40 hNe tr₁ tr₂ tr₃ cl₁ cl₂ hN₁ hN₂)
end Walk40
def wsVal13 : Fin 13 → HwBytes
  | ⟨0, _⟩ => wsPqxdhPrk0 | ⟨1, _⟩ => wsRk0 | ⟨2, _⟩ => wsPqxdhCk0 | ⟨3, _⟩ => wsPqxdhPqr0
  | ⟨4, _⟩ => wsChainPrk0 | ⟨5, _⟩ => wsStARk0 | ⟨6, _⟩ => wsCks0 | ⟨7, _⟩ => wsCks1
  | ⟨8, _⟩ => wsSeed1 | ⟨9, _⟩ => ws1Prk | ⟨10, _⟩ => wsCipherKey1 | ⟨11, _⟩ => ws1MacKey
  | ⟨12, _⟩ => wsIv1Full
def wsVal6Msg2 : Fin 6 → HwBytes
  | ⟨0, _⟩ => wsCks2 | ⟨1, _⟩ => wsSeed2 | ⟨2, _⟩ => ws2Prk
  | ⟨3, _⟩ => wsCipherKey2 | ⟨4, _⟩ => ws2MacKey | ⟨5, _⟩ => wsIv2Full
section DecideInj
set_option maxRecDepth 200000
theorem wsVal13_inj_decide : ∀ i j : Fin 13, wsVal13 i = wsVal13 j → i = j := by decide +kernel
theorem wsVal6Msg2_inj_decide : ∀ i j : Fin 6, wsVal6Msg2 i = wsVal6Msg2 j → i = j := by decide +kernel
theorem wsVal13_ne_wsVal6Msg2 : ∀ (i : Fin 13) (j : Fin 6), wsVal13 i ≠ wsVal6Msg2 j := by decide +kernel
theorem wsVal13_keyOfTake8_ne_ws1MacKey : ∀ i : Fin 13, SP.keyOfTake8 ((wsVal13 i).take 8) ≠ some ws1MacKey := by decide +kernel
theorem wsVal13_keyOfTake8_ne_ws2MacKey : ∀ i : Fin 13, SP.keyOfTake8 ((wsVal13 i).take 8) ≠ some ws2MacKey := by decide +kernel
theorem wsVal6Msg2_keyOfTake8_ne_ws1MacKey : ∀ j : Fin 6, SP.keyOfTake8 ((wsVal6Msg2 j).take 8) ≠ some ws1MacKey := by decide +kernel
theorem wsVal6Msg2_keyOfTake8_ne_ws2MacKey : ∀ j : Fin 6, SP.keyOfTake8 ((wsVal6Msg2 j).take 8) ≠ some ws2MacKey := by decide +kernel
theorem some_ws1MacKey_ne_some_ws2MacKey : (some ws1MacKey : Option HwBytes) ≠ some ws2MacKey := by decide +kernel
theorem wsPrk_eq_ws1Prk : Cheval26WeakStateIdx1.CompRSchedBSeedPins.wsPrk = ws1Prk := by decide +kernel
theorem wsMacKey_eq_ws1MacKey : Cheval26WeakStateIdx1.CompRSchedBSeedPins.wsMacKey = ws1MacKey := by decide +kernel
end DecideInj
def WsNodePin40Gen (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ : ExecTrace) (b : DY.Participant) (ikA ikBPk spkPk pqPk : DY.Bytes) (cl₁ cl₂ : Nat) (t : DY.Bytes) : Prop := (∃ i : Fin 13, t = node13Gen tr₁ b ikA ikBPk spkPk pqPk i ∧ gamma compI0 S g t = wsVal13 i) ∨ (∃ j : Fin 6, t = node6Msg2Gen tr₁ tr₂ tr₃ b ikA ikBPk spkPk pqPk cl₁ cl₂ j ∧ gamma compI0 S g t = wsVal6Msg2 j) ∨ (t = macNode38Gen tr₁ tr₂ b ikA ikBPk spkPk pqPk cl₁ ∧ SP.keyOfTake8 ((gamma compI0 S g t).take 8) = some ws1MacKey) ∨ (t = macNode40Msg2Gen tr₁ tr₂ tr₃ b ikA ikBPk spkPk pqPk cl₁ cl₂ ∧ SP.keyOfTake8 ((gamma compI0 S g t).take 8) = some ws2MacKey)
abbrev WsNodePin40 (S : Sem) (g : Ghost) (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (t : DY.Bytes) : Prop := WsNodePin40Gen S g tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂ t
theorem wsNodePin40Gen_inj {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {b : DY.Participant} {ikA ikBPk spkPk pqPk : DY.Bytes} {cl₁ cl₂ : Nat} {t₁ t₂ : DY.Bytes} (h₁ : WsNodePin40Gen S g tr₁ tr₂ tr₃ b ikA ikBPk spkPk pqPk cl₁ cl₂ t₁) (h₂ : WsNodePin40Gen S g tr₁ tr₂ tr₃ b ikA ikBPk spkPk pqPk cl₁ cl₂ t₂) (he : gamma compI0 S g t₁ = gamma compI0 S g t₂) : t₁ = t₂ := by
  rcases h₁ with ⟨i, rfl, hi⟩ | ⟨i, rfl, hi⟩ | ⟨rfl, hm₁⟩ | ⟨rfl, hm₁⟩ <;>
    rcases h₂ with ⟨j, rfl, hj⟩ | ⟨j, rfl, hj⟩ | ⟨rfl, hm₂⟩ | ⟨rfl, hm₂⟩
  · rw [wsVal13_inj_decide i j (hi.symm.trans (he.trans hj))]
  · exact absurd (hi.symm.trans (he.trans hj)) (wsVal13_ne_wsVal6Msg2 i j)
  · rw [← he, hi] at hm₂; exact absurd hm₂ (wsVal13_keyOfTake8_ne_ws1MacKey i)
  · rw [← he, hi] at hm₂; exact absurd hm₂ (wsVal13_keyOfTake8_ne_ws2MacKey i)
  · exact absurd (hj.symm.trans (he.symm.trans hi)) (wsVal13_ne_wsVal6Msg2 j i)
  · rw [wsVal6Msg2_inj_decide i j (hi.symm.trans (he.trans hj))]
  · rw [← he, hi] at hm₂; exact absurd hm₂ (wsVal6Msg2_keyOfTake8_ne_ws1MacKey i)
  · rw [← he, hi] at hm₂; exact absurd hm₂ (wsVal6Msg2_keyOfTake8_ne_ws2MacKey i)
  · rw [he, hj] at hm₁; exact absurd hm₁ (wsVal13_keyOfTake8_ne_ws1MacKey j)
  · rw [he, hj] at hm₁; exact absurd hm₁ (wsVal6Msg2_keyOfTake8_ne_ws1MacKey j)
  · rfl
  · rw [he] at hm₁; exact absurd (hm₁.symm.trans hm₂) some_ws1MacKey_ne_some_ws2MacKey
  · rw [he, hj] at hm₁; exact absurd hm₁ (wsVal13_keyOfTake8_ne_ws2MacKey j)
  · rw [he, hj] at hm₁; exact absurd hm₁ (wsVal6Msg2_keyOfTake8_ne_ws2MacKey j)
  · rw [he] at hm₁; exact absurd (hm₂.symm.trans hm₁) some_ws1MacKey_ne_some_ws2MacKey
  · rfl
theorem nodes40_wsNodePin40 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) : Nodes38 (WsNodePin40 S g r tr₁ tr₂ tr₃ cl₁ cl₂) r tr₁ tr₂ cl₁ ∧ Nodes40Msg2 (WsNodePin40 S g r tr₁ tr₂ tr₃ cl₁ cl₂) r tr₁ tr₂ tr₃ cl₁ cl₂ := by
  obtain ⟨hMacKey2, hPrk2, _hSalt2, hSeed2, hCks1, hCks0, hChainPrk, hRk0, hPqxdhPrk,
      hCk0, hPqr0, hStARk0, hSeed1, hCks2, hCipherKey2, hIv2⟩ :=
    split40KdfPins r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv
  let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
  obtain ⟨p₁, hp₁⟩ := WsIdx1Split40MemoCk1Pin.parse_b1; have hmac₁ := WsIdx1Split40MemoCk1Pin.encMac_msg1 hinv hp₁; obtain ⟨hK1, hP1, _, _⟩ := WsIdx1Split40MemoCk1Pin.SP.saltAndSeedPin_s1_1 S g tr₂ stA₁ cl₁ (Or.inl hp₁) hmac₁; have hPrk1' : gamma compI0 S g (SP.encPrk tr₂ stA₁ cl₁ (tr₂.length + 2)) = ws1Prk := hP1.trans wsPrk_eq_ws1Prk; have hMacKey1' : gamma compI0 S g (SP.encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).macKey = ws1MacKey := hK1.trans wsMacKey_eq_ws1MacKey
  have hCipherKey1' : gamma compI0 S g (SP.encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).cipherKey = wsCipherKey1 := by rw [encKeys_cipherKey, gamma_hmac_of S g hPrk1' (gamma_concat_of S g (gamma_wmk S g) (gamma_litByte_1 S g))]; exact wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.1
  have hIv1' : gamma compI0 S g (SP.encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).iv = wsIv1Full := by rw [encKeys_iv, gamma_hmac_of S g hPrk1' (gamma_concat_of S g hMacKey1' (gamma_concat_of S g (gamma_wmk S g) (gamma_litByte_3 S g)))]; exact wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.2.2.1
  have hmac1_pin : SP.keyOfTake8 ((gamma compI0 S g (macNode38Gen tr₁ tr₂ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁)).take 8) = some ws1MacKey := by
    have htake8 : (gamma compI0 S g (macNode38Gen tr₁ tr₂ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁)).take 8 = SP.msgMac8 p₁ := by rw [← Cheval26WeakStateIdx1.CompRSchedBSeedPins.gamma_trunc8_eq compI0 S g]; unfold macNode38Gen; dsimp only; rw [← encKeys_eq_trMsgKeys_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hmac₁
    rw [htake8, (Cheval26WeakStateIdx1.CompRSchedBSeedPins.macChainOk_spec (SP.macChainOk_of_wire WsIdx1Split40MemoCk1Pin.SP.wireMacChainOk_b1 hp₁)).2.1, wsMacKey_eq_ws1MacKey]
  have hmac2_pin : SP.keyOfTake8 ((gamma compI0 S g (macNode40Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂)).take 8) = some ws2MacKey := by
    have htake8 : (gamma compI0 S g (macNode40Msg2Gen tr₁ tr₂ tr₃ r.bob (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) cl₁ cl₂)).take 8 = SP.msgMac8 p := by rw [← Cheval26WeakStateIdx1.CompRSchedBSeedPins.gamma_trunc8_eq compI0 S g]; exact (hinv.hwire₂ p hp).2.1
    rw [htake8, (Cheval26WeakStateIdx1.CompRSchedBSeedPins.macChainOk_spec (SP.macChainOk_of_wire sp_wireMacChainOk_wire3Idx1 hp)).2.1]
  refine ⟨⟨Or.inl ⟨⟨0, by decide⟩, rfl, hPqxdhPrk⟩, Or.inl ⟨⟨1, by decide⟩, rfl, hRk0⟩,
    Or.inl ⟨⟨2, by decide⟩, rfl, hCk0⟩, Or.inl ⟨⟨3, by decide⟩, rfl, hPqr0⟩,
    Or.inl ⟨⟨4, by decide⟩, rfl, hChainPrk⟩, Or.inl ⟨⟨5, by decide⟩, rfl, hStARk0⟩,
    Or.inl ⟨⟨6, by decide⟩, rfl, hCks0⟩, Or.inl ⟨⟨7, by decide⟩, rfl, hCks1⟩,
    Or.inl ⟨⟨8, by decide⟩, rfl, hSeed1⟩,
    Or.inl ⟨⟨9, by decide⟩, rfl, by
      dsimp only [salt38, seed38, stA38, o38]
      rw [← encPrk_eq_kdfExtract_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hPrk1'⟩,
    Or.inl ⟨⟨10, by decide⟩, rfl, by
      dsimp only [mk38, salt38, seed38, stA38, o38]
      rw [← encKeys_eq_trMsgKeys_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hCipherKey1'⟩,
    Or.inl ⟨⟨11, by decide⟩, rfl, by
      dsimp only [mk38, salt38, seed38, stA38, o38]
      rw [← encKeys_eq_trMsgKeys_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hMacKey1'⟩,
    Or.inl ⟨⟨12, by decide⟩, rfl, by
      dsimp only [mk38, salt38, seed38, stA38, o38]
      rw [← encKeys_eq_trMsgKeys_ini tr₁ tr₂ r.bob o₁ cl₁]; exact hIv1'⟩,
    Or.inr (Or.inr (Or.inl ⟨rfl, hmac1_pin⟩))⟩,
    ⟨Or.inr (Or.inl ⟨⟨0, by decide⟩, rfl, hCks2⟩), Or.inr (Or.inl ⟨⟨1, by decide⟩, rfl, hSeed2⟩),
    Or.inr (Or.inl ⟨⟨2, by decide⟩, rfl, hPrk2⟩), Or.inr (Or.inl ⟨⟨3, by decide⟩, rfl, hCipherKey2⟩),
    Or.inr (Or.inl ⟨⟨4, by decide⟩, rfl, hMacKey2⟩), Or.inr (Or.inl ⟨⟨5, by decide⟩, rfl, hIv2⟩),
    Or.inr (Or.inr (Or.inr ⟨rfl, hmac2_pin⟩))⟩⟩
theorem kdfP_preMemo40 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hown : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) {x : Row} (hx : x ∈ preMemo40 r S g ms') {k m : DY.Bytes} (hkdf : x.1 = DY.KdfExtract.kdfExtract k m) : WsNodePin40 S g r tr₁ tr₂ tr₃ cl₁ cl₂ x.1 := by
  obtain ⟨hN₁, hN₂⟩ := nodes40_wsNodePin40 hfits hp hinv; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  exact (split40PrefixEnum r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown u hu).elim
    (fun hatom => kc_prefixAtom_40 hfits.1.1.1 hN₁ hN₂ hatom x hxu k m hkdf)
    (fun hsec => kc_storedSecrets_of_reachable hinv.reach u hsec x hxu k m hkdf)
theorem split40PreKKOwn : Split40PreKKOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x₁ hx₁ x₂ hx₂ _hz₁ _hz₂ k₁ m₁ k₂ m₂ e₁ e₂ _hps _hu he; have hteq : x₁.1 = x₂.1 := wsNodePin40Gen_inj (kdfP_preMemo40 hfits hp hinv hown hx₁ e₁) (kdfP_preMemo40 hfits hp hinv hown hx₂ e₂) he; rw [e₁, e₂] at hteq; obtain ⟨rfl, rfl⟩ := Symbolic.Swarm.COMPOSED.CompTermAlgebra.kdfExtract_inj hteq
  exact ⟨.base fun _ _ => rfl, .base fun _ _ => rfl⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreKK
