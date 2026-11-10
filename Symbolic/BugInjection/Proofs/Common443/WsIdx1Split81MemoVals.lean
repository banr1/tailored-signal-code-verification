/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub
public import Symbolic.BugInjection.Proofs.Common443.CompC2RestEntry38
public import Symbolic.BugInjection.Proofs.Common443.CompC2RestFn
public import Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census
public meta import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public meta import Symbolic.BugInjection.Proofs.Common443.CompRTag
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs
public meta import Symbolic.Specifications.Concrete.ByteSpecs
public meta import Symbolic.Specifications.Concrete.ExternInterpretation
public meta import Symbolic.Specifications.Refinement.TraceExplanation

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus (KdfSalt32)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (QKdfInjRest)
open ByteSpecs DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPin Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoZPinRun
abbrev o₂81 (r : Records) (tr₄ : ExecTrace) : DY.Libsignal.PQXDH.AliceHandshakeOut := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
scoped elab "eval_hwbytes81 " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t (some (Lean.mkConst ``HwBytes))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let v ← unsafe Lean.Meta.evalExpr (List (BitVec 8)) (Lean.mkConst ``HwBytes) e
  return Lean.toExpr v
def wsCks4 : HwBytes := eval_hwbytes81 ((WsIdx1O4Tag.keyOfTake8 (wsSeed5.take 8)).getD [])
def wsChainPrk4 : HwBytes := eval_hwbytes81 ((WsIdx1O4Tag.keyOfTake8 (wsCks4.take 8)).getD [])
def wsRk4 : HwBytes := eval_hwbytes81 ((WsIdx1O4Tag.keyOfTake8 (wsChainPrk4.take 8)).getD [])
def wsPqxdhPrk4 : HwBytes := eval_hwbytes81 ((WsIdx1O4Tag.keyOfTake8 (wsRk4.take 8)).getD [])
def wsPqxdhCk4 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk4 (wsRk4 ++ (pqxdhInfoLit ++ [2#8])))
def wsPqxdhPqr4 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk4 (wsPqxdhCk4 ++ (pqxdhInfoLit ++ [3#8])))
def wsStARk4 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsChainPrk4 (wratInfoLit ++ [1#8]))
def wsCks5 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 wsCks4 [2#8])
def wsCipherKey5 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 ws5Prk (wmkLit ++ [1#8]))
def wsIv5Full : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 ws5Prk (ws5MacKey ++ (wmkLit ++ [3#8])))
def ws6_bob_prk : HwBytes := eval_hwbytes81 ((WsIdx1O4Tag.keyOfTake8 (ws6_bob_ck0.take 8)).getD [])
def ws6_bob_rk1 : HwBytes := eval_hwbytes81 (hmacWith WsIdx1O4Tag.F0 ws6_bob_prk (wratInfoLit ++ [1#8]))
set_option maxRecDepth 200000 in theorem wsS2Kdf_untagged : wsPqxdhPrk4.take 4 ≠ compTag4 ∧ wsRk4.take 4 ≠ compTag4 ∧ wsPqxdhCk4.take 4 ≠ compTag4 ∧ wsPqxdhPqr4.take 4 ≠ compTag4 ∧ wsChainPrk4.take 4 ≠ compTag4 ∧ wsStARk4.take 4 ≠ compTag4 ∧ wsCks4.take 4 ≠ compTag4 ∧ wsCks5.take 4 ≠ compTag4 ∧ wsSeed5.take 4 ≠ compTag4 ∧ wsSalt5.take 4 ≠ compTag4 ∧ ws5Prk.take 4 ≠ compTag4 ∧ wsCipherKey5.take 4 ≠ compTag4 ∧ ws5MacKey.take 4 ≠ compTag4 ∧ wsIv5Full.take 4 ≠ compTag4 ∧ ws6_bob_prk.take 4 ≠ compTag4 ∧ ws6_bob_rk1.take 4 ≠ compTag4 ∧ ek2PubKey.take 4 ≠ compTag4 ∧ compKyberCt2.take 4 ≠ compTag4 ∧ compKyberSs2.take 4 ≠ compTag4 ∧ compKyberE2.take 4 ≠ compTag4 ∧ ws6_bob_ck0.take 4 ≠ compTag4 ∧ ws6_bob_ck1.take 4 ≠ compTag4 ∧ WsIdx1O4Tag.wsSeed6.take 4 ≠ compTag4 := by decide +kernel
set_option maxRecDepth 200000 in theorem wsS2Kdf_keyOfTake8 : SP.keyOfTake8 (wsSeed5.take 8) = some wsCks4 ∧ SP.keyOfTake8 (wsCks4.take 8) = some wsChainPrk4 ∧ SP.keyOfTake8 (wsChainPrk4.take 8) = some wsRk4 ∧ SP.keyOfTake8 (wsRk4.take 8) = some wsPqxdhPrk4 ∧ SP.keyOfTake8 (ws6_bob_ck0.take 8) = some ws6_bob_prk ∧ SP.keyOfTake8 (WsIdx1O4Tag.wsSeed6.take 8) = some ws6_bob_ck0 := by decide +kernel
set_option maxRecDepth 200000 in theorem wsS2Kdf_forward : hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk4 (pqxdhInfoLit ++ [1#8]) = wsRk4 ∧ hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk4 (wsRk4 ++ (pqxdhInfoLit ++ [2#8])) = wsPqxdhCk4 ∧ hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk4 (wsPqxdhCk4 ++ (pqxdhInfoLit ++ [3#8])) = wsPqxdhPqr4 ∧ hmacWith WsIdx1O4Tag.F0 wsChainPrk4 (wratInfoLit ++ [1#8]) = wsStARk4 ∧ hmacWith WsIdx1O4Tag.F0 wsChainPrk4 (wsStARk4 ++ (wratInfoLit ++ [2#8])) = wsCks4 ∧ hmacWith WsIdx1O4Tag.F0 wsCks4 [1#8] = wsSeed5 ∧ hmacWith WsIdx1O4Tag.F0 wsCks4 [2#8] = wsCks5 ∧ hmacWith WsIdx1O4Tag.F0 ws5Prk (wmkLit ++ [1#8]) = wsCipherKey5 ∧ hmacWith WsIdx1O4Tag.F0 ws5Prk (wsCipherKey5 ++ (wmkLit ++ [2#8])) = ws5MacKey ∧ hmacWith WsIdx1O4Tag.F0 ws5Prk (ws5MacKey ++ (wmkLit ++ [3#8])) = wsIv5Full ∧ hmacWith WsIdx1O4Tag.F0 ws6_bob_prk (wratInfoLit ++ [1#8]) = ws6_bob_rk1 ∧ hmacWith WsIdx1O4Tag.F0 ws6_bob_prk (ws6_bob_rk1 ++ (wratInfoLit ++ [2#8])) = ws6_bob_ck0 ∧ hmacWith WsIdx1O4Tag.F0 ws6_bob_ck0 [1#8] = WsIdx1O4Tag.wsSeed6 ∧ hmacWith WsIdx1O4Tag.F0 ws6_bob_ck0 [2#8] = ws6_bob_ck1 := by decide +kernel
theorem split81_fwd_pqxdh4 (S : Sem) (g : Ghost) (tr : ExecTrace) (ikA ikB spkB pqpkB : DY.Bytes) (hP : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree spkB ikA) (DY.Libsignal.PQXDH.agree ikB (randTerm tr.length 32)) (DY.Libsignal.PQXDH.agree spkB (randTerm tr.length 32)) none (PQKem.kemEncap pqpkB (randTerm (tr.length + 1) 32)).2)) = wsPqxdhPrk4) (hR : gamma compI0 S g (iniAliceOut tr ikA ikB spkB pqpkB none).keys.rk = wsRk4) : gamma compI0 S g (iniAliceOut tr ikA ikB spkB pqpkB none).keys.ck = wsPqxdhCk4 ∧ gamma compI0 S g (iniAliceOut tr ikA ikB spkB pqpkB none).keys.pqr = wsPqxdhPqr4 := by
  have hCk : gamma compI0 S g (iniAliceOut tr ikA ikB spkB pqpkB none).keys.ck = wsPqxdhCk4 := by rw [iniAliceOut_ck, gamma_hmac_of S g hP (gamma_concat_of S g hR (gamma_concat_of S g (gamma_pqxdhLabel S g) (gamma_litByte_2 S g)))]; exact wsS2Kdf_forward.2.1
  refine ⟨hCk, ?_⟩
  rw [iniAliceOut_pqr, gamma_hmac_of S g hP (gamma_concat_of S g hCk (gamma_concat_of S g (gamma_pqxdhLabel S g) (gamma_litByte_3 S g)))]; exact wsS2Kdf_forward.2.2.1
theorem split81_fwd_start4 (S : Sem) (g : Ghost) (tr : ExecTrace) (bob : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hC : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac o.keys.rk (DY.Libsignal.PQXDH.agree o.spk (randTerm (tr.length + 2) 32))) = wsChainPrk4) : gamma compI0 S g (iniAliceStartState tr bob o).rk = wsStARk4 := by rw [iniAliceStartState_rk, gamma_hmac_of S g hC (gamma_concat_of S g (gamma_wrat S g) (gamma_litByte_1 S g))]; exact wsS2Kdf_forward.2.2.2.1
theorem split81_fwd_enc1 (S : Sem) (g : Ghost) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (hP : gamma compI0 S g (SP.encPrk tr stA cl pq) = ws1Prk) (hK : gamma compI0 S g (SP.encKeys tr stA cl pq).macKey = ws1MacKey) : gamma compI0 S g (SP.encKeys tr stA cl pq).cipherKey = wsCipherKey1 ∧ gamma compI0 S g (SP.encKeys tr stA cl pq).iv = wsIv1Full := by
  refine ⟨?_, ?_⟩
  · rw [encKeys_cipherKey, gamma_hmac_of S g hP (gamma_concat_of S g (gamma_wmk S g) (gamma_litByte_1 S g))]
    exact wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.1
  · rw [encKeys_iv, gamma_hmac_of S g hP (gamma_concat_of S g hK (gamma_concat_of S g (gamma_wmk S g) (gamma_litByte_3 S g)))]
    exact wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.2.2.1
theorem split81_fwd_enc5 (S : Sem) (g : Ghost) (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (hP : gamma compI0 S g (SP.encPrk tr stA cl pq) = ws5Prk) (hK : gamma compI0 S g (SP.encKeys tr stA cl pq).macKey = ws5MacKey) : gamma compI0 S g (SP.encKeys tr stA cl pq).cipherKey = wsCipherKey5 ∧ gamma compI0 S g (SP.encKeys tr stA cl pq).iv = wsIv5Full := by
  refine ⟨?_, ?_⟩
  · rw [encKeys_cipherKey, gamma_hmac_of S g hP (gamma_concat_of S g (gamma_wmk S g) (gamma_litByte_1 S g))]
    exact wsS2Kdf_forward.2.2.2.2.2.2.2.1
  · rw [encKeys_iv, gamma_hmac_of S g hP (gamma_concat_of S g hK (gamma_concat_of S g (gamma_wmk S g) (gamma_litByte_3 S g)))]
    exact wsS2Kdf_forward.2.2.2.2.2.2.2.2.2.1
attribute [local irreducible] Symbolic.BugInjection.hexBytes in private theorem wire6Idx1Bytes_eq_b6' : wire6Idx1Bytes = Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvBytes := by unfold wire6Idx1Bytes Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvBytes; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6Recv_head_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.eventBytes_recv]; rfl
attribute [local irreducible] Symbolic.BugInjection.hexBytes in private theorem wire3Idx1Bytes_eq_b2' : wire3Idx1Bytes = Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2SendBytes := by unfold wire3Idx1Bytes Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2SendBytes; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall2Send_head_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.eventBytes_send]; rfl
set_option maxRecDepth 200000 in theorem sp_wireMacChainOk_wire6Idx1 : SP.wireMacChainOk ws1MacKey ws1Prk wire6Idx1Bytes = true := by rw [wire6Idx1Bytes_eq_b6', Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall6RecvBytes_eq]; decide +kernel
set_option maxRecDepth 200000 in theorem sp_ws1Prk_pin : ws1Prk.take 4 ≠ compTag4 ∧ SP.keyOfTake8 (ws1Prk.take 8) = some wsSalt1 ∧ SP.msg32OfTake8 (ws1Prk.take 8) = some wsSeed1 := by decide +kernel
set_option maxRecDepth 200000 in theorem sp_wireMacChainOk_b5 : SP.wireMacChainOk ws5MacKey ws5Prk Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall5SendBytes = true := by rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins.schedBCall5SendBytes_eq]; decide +kernel
set_option maxRecDepth 200000 in theorem sp_ws5Prk_pin : ws5Prk.take 4 ≠ compTag4 ∧ SP.keyOfTake8 (ws5Prk.take 8) = some wsSalt5 ∧ SP.msg32OfTake8 (ws5Prk.take 8) = some wsSeed5 := by decide +kernel
private theorem stA40_eq_census (r : Records) (tr₁ tr₂ : ExecTrace) (cl₁ : Nat) : stA40 r tr₁ tr₂ cl₁ = Census443Defs.encSt tr₂ (Census443Defs.iniAliceStartState tr₁ r.bob (Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ := rfl
private theorem stA₂81_eq_census (r : Records) (tr₄ : ExecTrace) : stA₂81 r tr₄ = Census443Defs.iniAliceStartState tr₄ r.bob (Census443Defs.iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) := rfl
set_option maxRecDepth 200000 in
theorem split81S1KdfPins (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move)
    (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat)
    (hp : parsePreKeyWire wire6Idx1Bytes = some p)
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let stA₁' := encSt tr₂ stA₁ cl₁
    let pqxdhPrk := DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree (setupPublic r 4) (setupSecret r 0)) (DY.Libsignal.PQXDH.agree (setupPublic r 2) (randTerm tr₁.length 32)) (DY.Libsignal.PQXDH.agree (setupPublic r 4) (randTerm tr₁.length 32)) none (PQKem.kemEncap (setupPublic r 6) (randTerm (tr₁.length + 1) 32)).2)
    let chainPrk := DY.Libsignal.TripleRatchet.hmac o₁.keys.rk (DY.Libsignal.PQXDH.agree o₁.spk (randTerm (tr₁.length + 2) 32))
    gamma compI0 S g (SP.encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).macKey = ws1MacKey ∧
    gamma compI0 S g (SP.encPrk tr₂ stA₁ cl₁ (tr₂.length + 2)) = ws1Prk ∧
    gamma compI0 S g (encSalt tr₂ stA₁ cl₁ (tr₂.length + 2)) = wsSalt1 ∧
    gamma compI0 S g (SP.encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).cipherKey = wsCipherKey1 ∧
    gamma compI0 S g (SP.encKeys tr₂ stA₁ cl₁ (tr₂.length + 2)).iv = wsIv1Full ∧
    gamma compI0 S g (SP.encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).macKey = ws2MacKey ∧
    gamma compI0 S g (SP.encPrk tr₃ stA₁' cl₂ (tr₃.length + 2)) = ws2Prk ∧
    gamma compI0 S g (encSalt tr₃ stA₁' cl₂ (tr₃.length + 2)) = wsSalt2 ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2 = wsSeed2 ∧
    gamma compI0 S g stA₁'.cks = wsCks1 ∧
    gamma compI0 S g stA₁.cks = wsCks0 ∧
    gamma compI0 S g chainPrk = wsChainPrk0 ∧
    gamma compI0 S g o₁.keys.rk = wsRk0 ∧
    gamma compI0 S g pqxdhPrk = wsPqxdhPrk0 ∧
    gamma compI0 S g o₁.keys.ck = wsPqxdhCk0 ∧
    gamma compI0 S g o₁.keys.pqr = wsPqxdhPqr0 ∧
    gamma compI0 S g stA₁.rk = wsStARk0 ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA₁.cks).2 = wsSeed1 ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).1 = wsCks2 ∧
    gamma compI0 S g (SP.encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).cipherKey = wsCipherKey2 ∧
    gamma compI0 S g (SP.encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).iv = wsIv2Full := by
  intro o₁ stA₁ stA₁' pqxdhPrk chainPrk
  have hok_wire1 := SP.macChainOk_of_wire sp_wireMacChainOk_wire6Idx1 hp
  obtain ⟨hMacKey1, hPrk1, hSalt1, hSeed1⟩ := SP.saltAndSeedPin_of_macChainOk S g tr₂ stA₁ cl₁ (hinv.hwire₁ p hp).2.1 hok_wire1 sp_ws1Prk_pin
  obtain ⟨hCipherKey1, hIv1⟩ := split81_fwd_enc1 S g tr₂ stA₁ cl₁ (tr₂.length + 2) hPrk1 hMacKey1
  obtain ⟨p₂, hp₂⟩ := parse_b2
  have hmac2 := encMac_msg2_81 hinv hp₂; rw [stA40_eq_census] at hmac2
  have hp₂' : parsePreKeyWire wire3Idx1Bytes = some p₂ := by rw [wire3Idx1Bytes_eq_b2']; exact hp₂
  have hok_wire2 := SP.macChainOk_of_wire sp_wireMacChainOk_wire3Idx1 hp₂'
  obtain ⟨hMacKey2, hPrk2, hSalt2, hSeed2⟩ := SP.saltAndSeedPin_of_macChainOk S g tr₃ stA₁' cl₂ hmac2 hok_wire2 sp_ws2Prk_pin
  have hCks1 : gamma compI0 S g stA₁'.cks = wsCks1 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) hSeed2 wsPrefixKdf_untagged.2.2.2.2.2.2.2.2.2.2.1 wsPrefixKdf_keyOfTake8.2.1
  have hCks0 : gamma compI0 S g stA₁.cks = wsCks0 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (encSt_cks tr₂ stA₁ cl₁).symm hCks1) wsPrefixKdf_untagged.2.2.2.2.2.2.2.1 wsPrefixKdf_keyOfTake8.2.2.1
  have hChainPrk : gamma compI0 S g chainPrk = wsChainPrk0 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (iniAliceStartState_cks tr₁ r.bob o₁).symm hCks0) wsPrefixKdf_untagged.2.2.2.2.2.2.1 wsPrefixKdf_keyOfTake8.2.2.2.1
  have hRk0 : gamma compI0 S g o₁.keys.rk = wsRk0 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) hChainPrk wsPrefixKdf_untagged.2.2.2.2.1 wsPrefixKdf_keyOfTake8.2.2.2.2.1
  have hPqxdhPrk : gamma compI0 S g pqxdhPrk = wsPqxdhPrk0 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (iniAliceOut_rk tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6)).symm hRk0) wsPrefixKdf_untagged.2.1 wsPrefixKdf_keyOfTake8.2.2.2.2.2
  obtain ⟨hCk0, hPqr0⟩ := split40_fwd_pqxdh S g tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) hPqxdhPrk hRk0
  have hStARk0 := split40_fwd_start S g tr₁ r.bob o₁ hChainPrk
  have hCks2 := (split40_fwd_kdfCk S g hCks1 wsPrefixKdf_forward.2.2.2.2.2.2.2.1 wsPrefixKdf_forward.2.2.2.2.2.2.2.2.1).2
  obtain ⟨hCipherKey2, hIv2⟩ := split40_fwd_enc S g tr₃ stA₁' cl₂ (tr₃.length + 2) hPrk2 hMacKey2
  exact ⟨hMacKey1, hPrk1, hSalt1, hCipherKey1, hIv1, hMacKey2, hPrk2, hSalt2, hSeed2, hCks1, hCks0, hChainPrk, hRk0, hPqxdhPrk, hCk0, hPqr0, hStARk0, hSeed1, hCks2, hCipherKey2, hIv2⟩
set_option maxRecDepth 200000 in
theorem split81S2KdfPins (r : Records) (S : Sem) (g : Ghost) (ms' : List Move)
    (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat)
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₂ := iniAliceStartState tr₄ r.bob o₂
    let pqxdhPrk4 := DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree (setupPublic r 4) (setupSecret r 0)) (DY.Libsignal.PQXDH.agree (setupPublic r 2) (randTerm tr₄.length 32)) (DY.Libsignal.PQXDH.agree (setupPublic r 4) (randTerm tr₄.length 32)) none (PQKem.kemEncap (setupPublic r 6) (randTerm (tr₄.length + 1) 32)).2)
    let chainPrk4 := DY.Libsignal.TripleRatchet.hmac o₂.keys.rk (DY.Libsignal.PQXDH.agree o₂.spk (randTerm (tr₄.length + 2) 32))
    gamma compI0 S g (SP.encKeys tr₅ stA₂ cl₅ (tr₅.length + 2)).macKey = ws5MacKey ∧
    gamma compI0 S g (SP.encPrk tr₅ stA₂ cl₅ (tr₅.length + 2)) = ws5Prk ∧
    gamma compI0 S g (encSalt tr₅ stA₂ cl₅ (tr₅.length + 2)) = wsSalt5 ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA₂.cks).2 = wsSeed5 ∧
    gamma compI0 S g stA₂.cks = wsCks4 ∧
    gamma compI0 S g chainPrk4 = wsChainPrk4 ∧
    gamma compI0 S g o₂.keys.rk = wsRk4 ∧
    gamma compI0 S g pqxdhPrk4 = wsPqxdhPrk4 ∧
    gamma compI0 S g o₂.keys.ck = wsPqxdhCk4 ∧
    gamma compI0 S g o₂.keys.pqr = wsPqxdhPqr4 ∧
    gamma compI0 S g stA₂.rk = wsStARk4 ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA₂.cks).1 = wsCks5 ∧
    gamma compI0 S g (SP.encKeys tr₅ stA₂ cl₅ (tr₅.length + 2)).cipherKey = wsCipherKey5 ∧
    gamma compI0 S g (SP.encKeys tr₅ stA₂ cl₅ (tr₅.length + 2)).iv = wsIv5Full := by
  intro o₂ stA₂ pqxdhPrk4 chainPrk4
  obtain ⟨p₅, hp₅⟩ := parse_b5
  have hok_wire5 := SP.macChainOk_of_wire sp_wireMacChainOk_b5 hp₅
  have hmac5 := encMac_msg5_81 hinv hp₅; rw [stA₂81_eq_census] at hmac5
  obtain ⟨hMacKey5, hPrk5, hSalt5, hSeed5⟩ := SP.saltAndSeedPin_of_macChainOk S g tr₅ stA₂ cl₅ hmac5 hok_wire5 sp_ws5Prk_pin
  have hCks4 : gamma compI0 S g stA₂.cks = wsCks4 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) hSeed5 wsS2Kdf_untagged.2.2.2.2.2.2.2.2.1 wsS2Kdf_keyOfTake8.1
  have hChainPrk4 : gamma compI0 S g chainPrk4 = wsChainPrk4 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (iniAliceStartState_cks tr₄ r.bob o₂).symm hCks4) wsS2Kdf_untagged.2.2.2.2.2.2.1 wsS2Kdf_keyOfTake8.2.1
  have hRk4 : gamma compI0 S g o₂.keys.rk = wsRk4 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) hChainPrk4 wsS2Kdf_untagged.2.2.2.2.1 wsS2Kdf_keyOfTake8.2.2.1
  have hPqxdhPrk4 : gamma compI0 S g pqxdhPrk4 = wsPqxdhPrk4 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (iniAliceOut_rk tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6)).symm hRk4) wsS2Kdf_untagged.2.1 wsS2Kdf_keyOfTake8.2.2.2.1
  obtain ⟨hCk4, hPqr4⟩ := split81_fwd_pqxdh4 S g tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) hPqxdhPrk4 hRk4
  have hStARk4 := split81_fwd_start4 S g tr₄ r.bob o₂ hChainPrk4
  have hCks5 := (split40_fwd_kdfCk S g hCks4 wsS2Kdf_forward.2.2.2.2.2.1 wsS2Kdf_forward.2.2.2.2.2.2.1).2
  obtain ⟨hCipherKey5, hIv5⟩ := split81_fwd_enc5 S g tr₅ stA₂ cl₅ (tr₅.length + 2) hPrk5 hMacKey5
  exact ⟨hMacKey5, hPrk5, hSalt5, hSeed5, hCks4, hChainPrk4, hRk4, hPqxdhPrk4, hCk4, hPqr4, hStARk4, hCks5, hCipherKey5, hIv5⟩
set_option maxRecDepth 200000 in theorem compKyberEncaps_e2' : compKyberEncaps compKyberE2 = compKyberCt2 ++ compKyberSs2 := by decide +kernel
theorem gamma_kemEncap_fst_of_e2 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE2) : gamma compI0 S g (DY.PQKem.kemEncap pk e).1 = compKyberCt2 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_fst_eq h32]
  have h : compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] =
      some (compKyberEncaps (gamma compI0 S g e)) := rfl
  rw [h, Option.getD_some, he, compKyberEncaps_e2', List.take_left' Census443Memo.kyberCtVals_lengths.2.2.1]
theorem gamma_kemEncap_snd_of_e2 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE2) : gamma compI0 S g (DY.PQKem.kemEncap pk e).2 = compKyberSs2 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32]
  have h : compI0 DY.Libsignal.PQXDH.Refinement.kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] =
      some (compKyberEncaps (gamma compI0 S g e)) := rfl
  rw [h, Option.getD_some, he, compKyberEncaps_e2', List.drop_left' Census443Memo.kyberCtVals_lengths.2.2.1]
theorem bobChainCk0_eq_hmac (r : Records) (rk dhsPub : DY.Bytes) : bobChainCk0 r rk dhsPub = DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac rk (DY.Libsignal.PQXDH.agree dhsPub (setupSecret r 2))) (DY.Concat.concat (DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac rk (DY.Libsignal.PQXDH.agree dhsPub (setupSecret r 2))) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 1))) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 2))) := rfl
theorem createChain_fst_eq_hmac (rk pk sk : DY.Bytes) : (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 = DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac rk (DY.Libsignal.PQXDH.agree pk sk)) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 1)) := rfl
set_option maxRecDepth 200000 in
theorem extChainTerms81_untagged {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : ∀ u ∈ extChainTerms81 r tr₁ tr₂ tr₄ cl₁, (gamma compI0 S g u).take 4 ≠ compTag4 := by
  have hseed0 := gamma_bobSeed81 hfits hp hinv; unfold bobSeed81 at hseed0
  have hck0_len : (gamma compI0 S g (bobChainCk0 r (bobStartKeys r (x81Idx1 r tr₁ tr₂ tr₄ cl₁)).rk (DY.DiffieHellman.dhPk (stA81 r tr₁).dhs))).length = 32 := by rw [bobChainCk0_eq_hmac]; exact gamma_hmac_len S g _ _
  have hck0 := gamma_key_of_hmac S g hck0_len hseed0 wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 wsS2Kdf_keyOfTake8.2.2.2.2.2; have hprk := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (bobChainCk0_eq_hmac r _ _).symm hck0) wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 wsS2Kdf_keyOfTake8.2.2.2.2.1
  have hrk1 : gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain (bobStartKeys r (x81Idx1 r tr₁ tr₂ tr₄ cl₁)).rk (DY.DiffieHellman.dhPk (stA81 r tr₁).dhs) (setupSecret r 2)).1 = ws6_bob_rk1 := by rw [createChain_fst_eq_hmac, gamma_hmac_of S g hprk (gamma_concat_of S g (gamma_wrat S g) (gamma_litByte_1 S g))]; exact wsS2Kdf_forward.2.2.2.2.2.2.2.2.2.2.1
  have hck1 := (split40_fwd_kdfCk S g hck0 wsS2Kdf_forward.2.2.2.2.2.2.2.2.2.2.2.2.1 wsS2Kdf_forward.2.2.2.2.2.2.2.2.2.2.2.2.2).2; intro u hu; unfold extChainTerms81 bobChainTerms81 at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (gamma compI0 S g (DY.DiffieHellman.dhPk (randTerm tr₄.length 32))).take 4 ≠ compTag4
    rw [hinv.hek₂]; exact wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · change (gamma compI0 S g (DY.PQKem.kemEncap (setupPublic r 6) (randTerm (tr₄.length + 1) 32)).1).take 4 ≠ compTag4
    rw [gamma_kemEncap_fst_of_e2 hinv.hent₂]; exact wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hprk]; exact wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hrk1]; exact wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hck0]; exact wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hck1]; exact wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hseed0]; exact wsS2Kdf_untagged.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
theorem extChainRows81_untagged {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : ∀ x ∈ extChainRows81 r S g tr₁ tr₂ tr₄ cl₁, x.2.2.take 4 ≠ compTag4 := by intro x hx; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx; exact extChainTerms81_untagged hfits hp hinv u hu
theorem bobChainTerms81_isKdf_salt32 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) {u : DY.Bytes} (hu : u ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁) : ∃ k m : DY.Bytes, u = DY.KdfExtract.kdfExtract k m ∧ (gamma compI0 S g k).length = 32 := by
  unfold bobChainTerms81 at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, rfl, gamma_hmac_len S g _ _⟩
  · exact ⟨_, _, rfl, gamma_hmac_len S g _ _⟩
  · exact ⟨_, _, rfl, gamma_hmac_len S g _ _⟩
  · refine ⟨_, _, rfl, ?_⟩; rw [bobChainCk0_eq_hmac]; exact gamma_hmac_len S g _ _
  · refine ⟨_, _, rfl, ?_⟩; rw [bobChainCk0_eq_hmac]; exact gamma_hmac_len S g _ _
theorem self_mem_memo_dhPk (S : Sem) (g : Ghost) (sk : DY.Bytes) : (DY.DiffieHellman.dhPk sk, (gamma' compI0 S g (DY.DiffieHellman.dhPk sk)).shape, gamma compI0 S g (DY.DiffieHellman.dhPk sk)) ∈ (gamma' compI0 S g (DY.DiffieHellman.dhPk sk)).memo := by
  have h := CompRPreMemoSound.ms_pack_dhPk (i := compI0) (S := S) (g := g) ⟨sk⟩; change (({ sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack, (gamma' compI0 S g (({ sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)).shape, (gamma' compI0 S g (({ sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)).bytes) ∈ (gamma' compI0 S g (({ sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack)).memo; rw [h]; dsimp only [gDhPk, concretizeDhPk, node]; exact List.mem_cons_self
theorem self_mem_memo_kemEncap_fst (S : Sem) (g : Ghost) (pk e : DY.Bytes) (he : (gamma compI0 S g e).length = 32) : ((DY.PQKem.kemEncap pk e).1, (gamma' compI0 S g (DY.PQKem.kemEncap pk e).1).shape, gamma compI0 S g (DY.PQKem.kemEncap pk e).1) ∈ (gamma' compI0 S g (DY.PQKem.kemEncap pk e).1).memo := by
  have h := CompRPreMemoSound.ms_pack_kemEncap (i := compI0) (S := S) (g := g) ⟨pk, e⟩; have he' : (gamma' compI0 S g e).bytes.length = 32 := he
  change (({ pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack,
    (gamma' compI0 S g (({ pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack)).shape,
    (gamma' compI0 S g (({ pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack)).bytes) ∈
    (gamma' compI0 S g (({ pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack)).memo
  rw [h]; dsimp only [gKemEncap, concretizeKemEncap]; simp only [he', ↓reduceIte, node]; exact List.mem_cons_self
theorem extChainRows81_cases (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) (hent₂ : gamma compI0 S g (randTerm (tr₄.length + 1) 32) = compKyberE2) {x : Row} (hx : x ∈ extChainRows81 r S g tr₁ tr₂ tr₄ cl₁) : x ∈ (gamma' compI0 S g (o₂81 r tr₄).ek).memo ∨ x ∈ (gamma' compI0 S g (o₂81 r tr₄).ct).memo ∨ ∃ u ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁, x = (u, (gamma' compI0 S g u).shape, gamma compI0 S g u) := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx; unfold extChainTerms81 at hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inl (self_mem_memo_dhPk S g _)
  rcases List.mem_cons.mp hu with rfl | hbob
  · have he32 : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32 := by rw [hent₂]; decide +kernel
    exact Or.inr (Or.inl (self_mem_memo_kemEncap_fst S g _ _ he32))
  · exact Or.inr (Or.inr ⟨u, hbob, rfl⟩)
theorem not_isX_of_kdfExtract (k m : DY.Bytes) : ¬ CompRSplit38UntaggedShape.IsX (DY.KdfExtract.kdfExtract k m) := by
  rintro (⟨a, h⟩ | ⟨a, b, h⟩)
  · exact CompRPreMemo38KdfCensus.ne_kdfExtract_of_notKdf (CompRPreMemo38KdfCensus.nk_dhPk a) k m h.symm
  · exact CompRPreMemo38KdfCensus.ne_kdfExtract_of_notKdf (CompRPreMemo38KdfCensus.nk_dh_pack a b) k m h.symm
theorem not_isTrunc8_of_kdfExtract (k m : DY.Bytes) : ¬ CompRSplit38UntaggedShape.IsTrunc8 (DY.KdfExtract.kdfExtract k m) := by
  rintro ⟨a, h⟩
  exact CompRPreMemo38KdfCensus.ne_kdfExtract_of_notKdf (CompRPreMemo38KdfCensus.nk_trunc8 a) k m h.symm
theorem bobChainRow_props (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat)
    {u : DY.Bytes} (hu : u ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁) :
    let x : Row := (u, (gamma' compI0 S g u).shape, gamma compI0 S g u)
    KdfSalt32 S g x ∧ assumedInjective x.1 = true ∧
    (∀ (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ : Row), QKdfInjRest S g known pts x₁ x) ∧
    Symbolic.BugInjection.Proofs.Common443.CompC2Rest38.RestEntry S g x ∧
    (∀ (F : HwBytes → DY.Bytes) (Rv : HwBytes → Prop), CompC2RestFn.RestFnEntry F Rv S g x) := by
  intro x
  obtain ⟨k₀, m₀, hu_eq, hk₀_len⟩ := bobChainTerms81_isKdf_salt32 r S g tr₁ tr₂ tr₄ cl₁ hu
  have hx1 : x.1 = DY.KdfExtract.kdfExtract k₀ m₀ := hu_eq
  have hkdf : CompRSplit38UntaggedShape.IsKdf x.1 := ⟨k₀, m₀, hx1⟩
  have hai : assumedInjective x.1 = true := by rw [hx1]; exact CompRSplit38QKdf.assumedInjective_kdfExtract k₀ m₀
  refine ⟨fun k m hkm => ?_, hai, fun _ _ _ _ _ _ hnkdf => absurd hkdf hnkdf,
    CompC2RestEntry38.restEntry_of_kdf hx1, fun F Rv => ?_⟩
  · rw [← CompRPreMemo38KdfCensus.kdfExtract_salt_eq (hx1.symm.trans hkm)]; exact hk₀_len
  · have hnx : ¬ CompRSplit38UntaggedShape.IsX x.1 := hx1 ▸ not_isX_of_kdfExtract k₀ m₀
    have hnt : ¬ CompRSplit38UntaggedShape.IsTrunc8 x.1 := hx1 ▸ not_isTrunc8_of_kdfExtract k₀ m₀
    refine ⟨?_, fun _ hnk _ _ => absurd hkdf hnk, fun hfalse => by rw [hai] at hfalse; cases hfalse⟩
    rintro (hx' | ht' | ⟨_, hnk⟩)
    · exact absurd hx' hnx
    · exact absurd ht' hnt
    · exact absurd hkdf hnk
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals
