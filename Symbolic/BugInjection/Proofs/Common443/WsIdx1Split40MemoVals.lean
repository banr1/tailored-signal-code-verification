/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoZPin
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public import Symbolic.BugInjection.Proofs.Common443.CompRBobInit
public import Symbolic.BugInjection.Proofs.Common443.CompRI0Census
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
public import Symbolic.BugInjection.Proofs.Common443.CompMemoInjGtDraws
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins
public meta import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public meta import Symbolic.BugInjection.Proofs.Common443.CompRTag
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag
public meta import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census
public meta import Symbolic.Specifications.Concrete.ByteSpecs
public meta import Symbolic.Specifications.Concrete.ExternInterpretation
public meta import Symbolic.Specifications.Refinement.TraceExplanation
import Init.Data.String
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
open ByteSpecs CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.Refinement (sha256CompressFunction)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRGamma Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound Symbolic.BugInjection.Proofs.Common443.CompRI0Census Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.BugInjection.Proofs.Common443.WsIdx1O4Tag Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged
scoped elab "eval_hwbytes40 " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t (some (Lean.mkConst ``HwBytes))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let v ← unsafe Lean.Meta.evalExpr (List (BitVec 8)) (Lean.mkConst ``HwBytes) e
  return Lean.toExpr v
def pqxdhInfoLit : HwBytes := eval_hwbytes40 (ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8)
def wratInfoLit : HwBytes := eval_hwbytes40 (ofByteArray "WhisperRatchet".toUTF8)
def wsCks1 : HwBytes := eval_hwbytes40 ((WsIdx1O4Tag.keyOfTake8 (wsSeed2.take 8)).getD [])
def wsCks0 : HwBytes := eval_hwbytes40 ((WsIdx1O4Tag.keyOfTake8 (wsCks1.take 8)).getD [])
def wsChainPrk0 : HwBytes := eval_hwbytes40 ((WsIdx1O4Tag.keyOfTake8 (wsCks0.take 8)).getD [])
def wsRk0 : HwBytes := eval_hwbytes40 ((WsIdx1O4Tag.keyOfTake8 (wsChainPrk0.take 8)).getD [])
def wsPqxdhPrk0 : HwBytes := eval_hwbytes40 ((WsIdx1O4Tag.keyOfTake8 (wsRk0.take 8)).getD [])
def wsPqxdhCk0 : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk0 (wsRk0 ++ (pqxdhInfoLit ++ [2#8])))
def wsPqxdhPqr0 : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk0 (wsPqxdhCk0 ++ (pqxdhInfoLit ++ [3#8])))
def wsStARk0 : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 wsChainPrk0 (wratInfoLit ++ [1#8]))
def wsCks2 : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 wsCks1 [2#8])
def wsCipherKey1 : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 ws1Prk (wmkLit ++ [1#8]))
def wsIv1Full : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 ws1Prk (ws1MacKey ++ (wmkLit ++ [3#8])))
def wsCipherKey2 : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 ws2Prk (wmkLit ++ [1#8]))
def wsIv2Full : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 ws2Prk (ws2MacKey ++ (wmkLit ++ [3#8])))
def wsMac1Bytes : HwBytes := eval_hwbytes40 ((hmacWith WsIdx1O4Tag.F0 ws1MacKey wsMacIn1).take 8)
def wsMac2Bytes : HwBytes := eval_hwbytes40 ((hmacWith WsIdx1O4Tag.F0 ws2MacKey wsMacIn2).take 8)
def wsMac1Full : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 ws1MacKey wsMacIn1)
def wsMac2Full : HwBytes := eval_hwbytes40 (hmacWith WsIdx1O4Tag.F0 ws2MacKey wsMacIn2)
section DecideTables
set_option maxRecDepth 200000
theorem wsPrefixKdf_untagged :
    wsPqxdhPrk0.take 4 ≠ compTag4 ∧ wsRk0.take 4 ≠ compTag4 ∧ wsPqxdhCk0.take 4 ≠ compTag4 ∧
    wsPqxdhPqr0.take 4 ≠ compTag4 ∧ wsChainPrk0.take 4 ≠ compTag4 ∧ wsStARk0.take 4 ≠ compTag4 ∧
    wsCks0.take 4 ≠ compTag4 ∧ wsCks1.take 4 ≠ compTag4 ∧ wsCks2.take 4 ≠ compTag4 ∧
    wsSeed1.take 4 ≠ compTag4 ∧ wsSeed2.take 4 ≠ compTag4 ∧ wsSalt1.take 4 ≠ compTag4 ∧
    wsSalt2.take 4 ≠ compTag4 ∧ ws1Prk.take 4 ≠ compTag4 ∧ ws2Prk.take 4 ≠ compTag4 ∧
    wsCipherKey1.take 4 ≠ compTag4 ∧ wsCipherKey2.take 4 ≠ compTag4 ∧ ws1MacKey.take 4 ≠ compTag4 ∧
    ws2MacKey.take 4 ≠ compTag4 ∧ wsIv1Full.take 4 ≠ compTag4 ∧ wsIv2Full.take 4 ≠ compTag4 ∧
    wsMac1Full.take 4 ≠ compTag4 ∧ wsMac2Full.take 4 ≠ compTag4 ∧ wsMac1Bytes.take 4 ≠ compTag4 ∧
    wsMac2Bytes.take 4 ≠ compTag4 := by decide +kernel
theorem wsPrefixKemAes_untagged :
    setup.kyberPk.take 4 ≠ compTag4 ∧ compKyberCt1.take 4 ≠ compTag4 ∧
    compKyberSs1.take 4 ≠ compTag4 ∧ compKyberE1.take 4 ≠ compTag4 ∧
    compAesCt0.take 4 ≠ compTag4 ∧ compAesCt1.take 4 ≠ compTag4 ∧
    compAesPt1.take 4 ≠ compTag4 ∧ compAesPt2.take 4 ≠ compTag4 := by decide +kernel
theorem wsPrefixKdf_keyOfTake8 :
    Cheval26WeakStateIdx1.CompRSchedBSeedPins.keyOfTake8 (wsSeed1.take 8) = some wsCks0 ∧
    Cheval26WeakStateIdx1.CompRSchedBSeedPins.keyOfTake8 (wsSeed2.take 8) = some wsCks1 ∧
    Cheval26WeakStateIdx1.CompRSchedBSeedPins.keyOfTake8 (wsCks1.take 8) = some wsCks0 ∧
    Cheval26WeakStateIdx1.CompRSchedBSeedPins.keyOfTake8 (wsCks0.take 8) = some wsChainPrk0 ∧
    Cheval26WeakStateIdx1.CompRSchedBSeedPins.keyOfTake8 (wsChainPrk0.take 8) = some wsRk0 ∧
    Cheval26WeakStateIdx1.CompRSchedBSeedPins.keyOfTake8 (wsRk0.take 8) = some wsPqxdhPrk0 := by decide +kernel
theorem wsPrefixKdf_forward :
    hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk0 (pqxdhInfoLit ++ [1#8]) = wsRk0 ∧
    hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk0 (wsRk0 ++ (pqxdhInfoLit ++ [2#8])) = wsPqxdhCk0 ∧
    hmacWith WsIdx1O4Tag.F0 wsPqxdhPrk0 (wsPqxdhCk0 ++ (pqxdhInfoLit ++ [3#8])) = wsPqxdhPqr0 ∧
    hmacWith WsIdx1O4Tag.F0 wsChainPrk0 (wratInfoLit ++ [1#8]) = wsStARk0 ∧
    hmacWith WsIdx1O4Tag.F0 wsChainPrk0 (wsStARk0 ++ (wratInfoLit ++ [2#8])) = wsCks0 ∧
    hmacWith WsIdx1O4Tag.F0 wsCks0 [1#8] = wsSeed1 ∧
    hmacWith WsIdx1O4Tag.F0 wsCks0 [2#8] = wsCks1 ∧
    hmacWith WsIdx1O4Tag.F0 wsCks1 [1#8] = wsSeed2 ∧
    hmacWith WsIdx1O4Tag.F0 wsCks1 [2#8] = wsCks2 ∧
    hmacWith WsIdx1O4Tag.F0 ws1Prk (wmkLit ++ [1#8]) = wsCipherKey1 ∧
    hmacWith WsIdx1O4Tag.F0 ws1Prk (wsCipherKey1 ++ (wmkLit ++ [2#8])) = ws1MacKey ∧
    hmacWith WsIdx1O4Tag.F0 ws1Prk (ws1MacKey ++ (wmkLit ++ [3#8])) = wsIv1Full ∧
    hmacWith WsIdx1O4Tag.F0 ws2Prk (wmkLit ++ [1#8]) = wsCipherKey2 ∧
    hmacWith WsIdx1O4Tag.F0 ws2Prk (wsCipherKey2 ++ (wmkLit ++ [2#8])) = ws2MacKey ∧
    hmacWith WsIdx1O4Tag.F0 ws2Prk (ws2MacKey ++ (wmkLit ++ [3#8])) = wsIv2Full := by decide +kernel
end DecideTables
namespace SP
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins (gamma_computeMac gamma_hmac_compI0 keyOfTake8_hmacWith saltAndSeedPin_of_macChainOk macChainOk_of_wire ws3MacKey ws3Prk ws3Prk_pin msgMac8 wireMacChainOk macChainOk keyOfTake8 msg32OfTake8 encKeys encPrk)
end SP
theorem toUTF8_eq_ofList (s : String) :
    s.toUTF8 = List.utf8Encode s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
theorem gamma_pqxdhLabel (S : Sem) (g : Ghost) : gamma compI0 S g DY.Libsignal.PQXDH.pqxdhLabel = pqxdhInfoLit := by
  show gamma compI0 S g (({ lit := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8 } :
    DY.Literal.Literal.SubF DY.Bytes).pack) = pqxdhInfoLit
  rw [CompRSchedBSalts.gamma_lit, toUTF8_eq_ofList]; decide +kernel
theorem gamma_wrat (S : Sem) (g : Ghost) : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") = wratInfoLit := by
  show gamma compI0 S g (({ lit := "WhisperRatchet".toUTF8 } : DY.Literal.Literal.SubF DY.Bytes).pack) = wratInfoLit
  rw [CompRSchedBSalts.gamma_lit, toUTF8_eq_ofList]; decide +kernel
theorem gamma_wmk (S : Sem) (g : Ghost) : gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") = wmkLit := by
  show gamma compI0 S g (({ lit := "WhisperMessageKeys".toUTF8 } : DY.Literal.Literal.SubF DY.Bytes).pack) = wmkLit
  rw [CompRSchedBSalts.gamma_lit, toUTF8_eq_ofList]; decide +kernel
theorem gamma_litByte_1 (S : Sem) (g : Ghost) : gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte 1) = [1#8] := by
  show gamma compI0 S g (({ lit := ⟨#[1]⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack) = [1#8]
  rw [CompRSchedBSalts.gamma_lit]; decide +kernel
theorem gamma_litByte_2 (S : Sem) (g : Ghost) : gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte 2) = [2#8] := by
  show gamma compI0 S g (({ lit := ⟨#[2]⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack) = [2#8]
  rw [CompRSchedBSalts.gamma_lit]; decide +kernel
theorem gamma_litByte_3 (S : Sem) (g : Ghost) : gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte 3) = [3#8] := by
  show gamma compI0 S g (({ lit := ⟨#[3]⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack) = [3#8]
  rw [CompRSchedBSalts.gamma_lit]; decide +kernel
theorem gamma_hmac_len (S : Sem) (g : Ghost) (k m : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)).length = 32 := by rw [SP.gamma_hmac_compI0]; unfold hmacWith; split <;> exact CompRTag.sha256With_length _ _
theorem kdfCk_fst (cks : DY.Bytes) : (DY.Libsignal.TripleRatchet.kdfCk cks).1 = DY.Libsignal.TripleRatchet.hmac cks (DY.Libsignal.TripleRatchet.litByte 2) := rfl
theorem kdfCk_snd (cks : DY.Bytes) : (DY.Libsignal.TripleRatchet.kdfCk cks).2 = DY.Libsignal.TripleRatchet.hmac cks (DY.Libsignal.TripleRatchet.litByte 1) := rfl
theorem encSt_cks (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : (encSt tr stA cl).cks = DY.Libsignal.TripleRatchet.hmac stA.cks (DY.Libsignal.TripleRatchet.litByte 2) := rfl
theorem iniAliceStartState_rk (tr : ExecTrace) (bob : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (iniAliceStartState tr bob o).rk = DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac o.keys.rk (DY.Libsignal.PQXDH.agree o.spk (randTerm (tr.length + 2) 32))) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 1)) := rfl
theorem iniAliceStartState_cks (tr : ExecTrace) (bob : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (iniAliceStartState tr bob o).cks = DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac o.keys.rk (DY.Libsignal.PQXDH.agree o.spk (randTerm (tr.length + 2) 32))) (DY.Concat.concat (iniAliceStartState tr bob o).rk (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 2))) := rfl
theorem iniAliceOut_rk (tr : ExecTrace) (ikA ikB spkB pqpkB : DY.Bytes) : (iniAliceOut tr ikA ikB spkB pqpkB none).keys.rk = DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree spkB ikA) (DY.Libsignal.PQXDH.agree ikB (randTerm tr.length 32)) (DY.Libsignal.PQXDH.agree spkB (randTerm tr.length 32)) none (PQKem.kemEncap pqpkB (randTerm (tr.length + 1) 32)).2)) (DY.Concat.concat DY.Libsignal.PQXDH.pqxdhLabel (DY.Libsignal.TripleRatchet.litByte 1)) := rfl
theorem iniAliceOut_ck (tr : ExecTrace) (ikA ikB spkB pqpkB : DY.Bytes) : (iniAliceOut tr ikA ikB spkB pqpkB none).keys.ck = DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree spkB ikA) (DY.Libsignal.PQXDH.agree ikB (randTerm tr.length 32)) (DY.Libsignal.PQXDH.agree spkB (randTerm tr.length 32)) none (PQKem.kemEncap pqpkB (randTerm (tr.length + 1) 32)).2)) (DY.Concat.concat (iniAliceOut tr ikA ikB spkB pqpkB none).keys.rk (DY.Concat.concat DY.Libsignal.PQXDH.pqxdhLabel (DY.Libsignal.TripleRatchet.litByte 2))) := rfl
theorem iniAliceOut_pqr (tr : ExecTrace) (ikA ikB spkB pqpkB : DY.Bytes) : (iniAliceOut tr ikA ikB spkB pqpkB none).keys.pqr = DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree spkB ikA) (DY.Libsignal.PQXDH.agree ikB (randTerm tr.length 32)) (DY.Libsignal.PQXDH.agree spkB (randTerm tr.length 32)) none (PQKem.kemEncap pqpkB (randTerm (tr.length + 1) 32)).2)) (DY.Concat.concat (iniAliceOut tr ikA ikB spkB pqpkB none).keys.ck (DY.Concat.concat DY.Libsignal.PQXDH.pqxdhLabel (DY.Libsignal.TripleRatchet.litByte 3))) := rfl
theorem encKeys_cipherKey (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : (SP.encKeys tr stA cl pq).cipherKey = DY.Libsignal.TripleRatchet.hmac (SP.encPrk tr stA cl pq) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1)) := rfl
theorem encKeys_iv (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : (SP.encKeys tr stA cl pq).iv = DY.Libsignal.TripleRatchet.hmac (SP.encPrk tr stA cl pq) (DY.Concat.concat (SP.encKeys tr stA cl pq).macKey (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 3))) := rfl
def Split40KdfPins : Prop :=
  ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ →
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let stA₁' := encSt tr₂ stA₁ cl₁
    let pqxdhPrk := DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree (setupPublic r 4) (setupSecret r 0)) (DY.Libsignal.PQXDH.agree (setupPublic r 2) (randTerm tr₁.length 32)) (DY.Libsignal.PQXDH.agree (setupPublic r 4) (randTerm tr₁.length 32)) none (PQKem.kemEncap (setupPublic r 6) (randTerm (tr₁.length + 1) 32)).2)
    let chainPrk := DY.Libsignal.TripleRatchet.hmac o₁.keys.rk (DY.Libsignal.PQXDH.agree o₁.spk (randTerm (tr₁.length + 2) 32))
    gamma compI0 S g (SP.encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).macKey = ws2MacKey ∧
    gamma compI0 S g (SP.encPrk tr₃ stA₁' cl₂ (tr₃.length + 2)) = ws2Prk ∧
    gamma compI0 S g (encSalt tr₃ stA₁' cl₂ (tr₃.length + 2)) = wsSalt2 ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2 = wsSeed2 ∧
    gamma compI0 S g stA₁'.cks = wsCks1 ∧ gamma compI0 S g stA₁.cks = wsCks0 ∧
    gamma compI0 S g chainPrk = wsChainPrk0 ∧ gamma compI0 S g o₁.keys.rk = wsRk0 ∧
    gamma compI0 S g pqxdhPrk = wsPqxdhPrk0 ∧ gamma compI0 S g o₁.keys.ck = wsPqxdhCk0 ∧
    gamma compI0 S g o₁.keys.pqr = wsPqxdhPqr0 ∧ gamma compI0 S g stA₁.rk = wsStARk0 ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA₁.cks).2 = wsSeed1 ∧
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).1 = wsCks2 ∧
    gamma compI0 S g (SP.encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).cipherKey = wsCipherKey2 ∧
    gamma compI0 S g (SP.encKeys tr₃ stA₁' cl₂ (tr₃.length + 2)).iv = wsIv2Full
set_option maxRecDepth 200000 in
theorem sp_wireMacChainOk_wire3Idx1Fast :
    SP.wireMacChainOk ws2MacKey ws2Prk WsIdx1Split40OwnSalt.wire3Idx1Fast = true := by decide +kernel
theorem sp_wireMacChainOk_wire3Idx1 : SP.wireMacChainOk ws2MacKey ws2Prk wire3Idx1Bytes = true := by rw [WsIdx1Split40OwnSalt.wire3Idx1Bytes_eq_fast]; exact sp_wireMacChainOk_wire3Idx1Fast
set_option maxRecDepth 200000 in
theorem sp_ws2Prk_pin :
    ws2Prk.take 4 ≠ compTag4 ∧ SP.keyOfTake8 (ws2Prk.take 8) = some wsSalt2 ∧
      SP.msg32OfTake8 (ws2Prk.take 8) = some wsSeed2 := by decide +kernel
theorem gamma_hmac_of (S : Sem) (g : Ghost) {k m : DY.Bytes} {kv mv : HwBytes} (hk : gamma compI0 S g k = kv) (hm : gamma compI0 S g m = mv) : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith WsIdx1O4Tag.F0 kv mv := by rw [SP.gamma_hmac_compI0, hk, hm]
theorem gamma_concat_of (S : Sem) (g : Ghost) {a b : DY.Bytes} {av bv : HwBytes} (ha : gamma compI0 S g a = av) (hb : gamma compI0 S g b = bv) : gamma compI0 S g (DY.Concat.concat a b) = av ++ bv := by rw [CompFreshDistinct.gamma_concat_eq, ha, hb]
theorem gamma_eq_of_eq (S : Sem) (g : Ghost) {a b : DY.Bytes} {v : HwBytes} (hab : a = b) (hb : gamma compI0 S g b = v) : gamma compI0 S g a = v := hab ▸ hb
theorem gamma_key_of_hmac (S : Sem) (g : Ghost) {k m : DY.Bytes} {v w : HwBytes} (hk : (gamma compI0 S g k).length = 32) (hv : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) = v) (htag : v.take 4 ≠ compTag4) (hrow : SP.keyOfTake8 (v.take 8) = some w) : gamma compI0 S g k = w := by
  have htag' : (hmacWith WsIdx1O4Tag.F0 (gamma compI0 S g k) (gamma compI0 S g m)).take 4 ≠ compTag4 := by rw [← SP.gamma_hmac_compI0, hv]; exact htag
  have hrec := SP.keyOfTake8_hmacWith (gamma compI0 S g k) (gamma compI0 S g m) hk htag'; rw [← SP.gamma_hmac_compI0, hv, hrow] at hrec
  exact Option.some.inj hrec |>.symm
theorem split40_fwd_pqxdh (S : Sem) (g : Ghost) (tr : ExecTrace) (ikA ikB spkB pqpkB : DY.Bytes) (hP : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.PQXDH.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree spkB ikA) (DY.Libsignal.PQXDH.agree ikB (randTerm tr.length 32)) (DY.Libsignal.PQXDH.agree spkB (randTerm tr.length 32)) none (PQKem.kemEncap pqpkB (randTerm (tr.length + 1) 32)).2)) = wsPqxdhPrk0) (hR : gamma compI0 S g (iniAliceOut tr ikA ikB spkB pqpkB none).keys.rk = wsRk0) : gamma compI0 S g (iniAliceOut tr ikA ikB spkB pqpkB none).keys.ck = wsPqxdhCk0 ∧ gamma compI0 S g (iniAliceOut tr ikA ikB spkB pqpkB none).keys.pqr = wsPqxdhPqr0 := by
  have hCk : gamma compI0 S g (iniAliceOut tr ikA ikB spkB pqpkB none).keys.ck = wsPqxdhCk0 := by rw [iniAliceOut_ck, gamma_hmac_of S g hP (gamma_concat_of S g hR (gamma_concat_of S g (gamma_pqxdhLabel S g) (gamma_litByte_2 S g)))]; exact wsPrefixKdf_forward.2.1
  refine ⟨hCk, ?_⟩
  rw [iniAliceOut_pqr, gamma_hmac_of S g hP (gamma_concat_of S g hCk (gamma_concat_of S g (gamma_pqxdhLabel S g) (gamma_litByte_3 S g)))]; exact wsPrefixKdf_forward.2.2.1
theorem split40_fwd_start (S : Sem) (g : Ghost) (tr : ExecTrace) (bob : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hC : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac o.keys.rk (DY.Libsignal.PQXDH.agree o.spk (randTerm (tr.length + 2) 32))) = wsChainPrk0) : gamma compI0 S g (iniAliceStartState tr bob o).rk = wsStARk0 := by rw [iniAliceStartState_rk, gamma_hmac_of S g hC (gamma_concat_of S g (gamma_wrat S g) (gamma_litByte_1 S g))]; exact wsPrefixKdf_forward.2.2.2.1
theorem split40_fwd_kdfCk (S : Sem) (g : Ghost) {cks : DY.Bytes} {c s c' : HwBytes}
    (hc : gamma compI0 S g cks = c) (hs : hmacWith WsIdx1O4Tag.F0 c [1#8] = s)
    (hc' : hmacWith WsIdx1O4Tag.F0 c [2#8] = c') :
    gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk cks).2 = s ∧ gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk cks).1 = c' :=
  ⟨by rw [kdfCk_snd, gamma_hmac_of S g hc (gamma_litByte_1 S g)]; exact hs,
   by rw [kdfCk_fst, gamma_hmac_of S g hc (gamma_litByte_2 S g)]; exact hc'⟩
theorem split40_fwd_enc (S : Sem) (g : Ghost) (tr : ExecTrace)
    (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat)
    (hP : gamma compI0 S g (SP.encPrk tr stA cl pq) = ws2Prk)
    (hK : gamma compI0 S g (SP.encKeys tr stA cl pq).macKey = ws2MacKey) :
    gamma compI0 S g (SP.encKeys tr stA cl pq).cipherKey = wsCipherKey2 ∧ gamma compI0 S g (SP.encKeys tr stA cl pq).iv = wsIv2Full :=
  ⟨by rw [encKeys_cipherKey, gamma_hmac_of S g hP (gamma_concat_of S g (gamma_wmk S g) (gamma_litByte_1 S g))]
      exact wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.2.2.2.1,
   by rw [encKeys_iv, gamma_hmac_of S g hP (gamma_concat_of S g hK
        (gamma_concat_of S g (gamma_wmk S g) (gamma_litByte_3 S g)))]
      exact wsPrefixKdf_forward.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
set_option maxRecDepth 200000 in
theorem split40KdfPins : Split40KdfPins := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ _hfits hp hinv o₁ stA₁ stA₁' pqxdhPrk chainPrk; have hok_wire := SP.macChainOk_of_wire sp_wireMacChainOk_wire3Idx1 hp; obtain ⟨hMacKey2', hPrk2', hSalt2', hSeed2'⟩ := SP.saltAndSeedPin_of_macChainOk S g tr₃ stA₁' cl₂ (hinv.hwire₂ p hp).2.1 hok_wire sp_ws2Prk_pin; have hCks1 : gamma compI0 S g stA₁'.cks = wsCks1 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) hSeed2' wsPrefixKdf_untagged.2.2.2.2.2.2.2.2.2.2.1 wsPrefixKdf_keyOfTake8.2.1
  have hCks0 : gamma compI0 S g stA₁.cks = wsCks0 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (encSt_cks tr₂ stA₁ cl₁).symm hCks1) wsPrefixKdf_untagged.2.2.2.2.2.2.2.1 wsPrefixKdf_keyOfTake8.2.2.1; have hChainPrk : gamma compI0 S g chainPrk = wsChainPrk0 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (iniAliceStartState_cks tr₁ r.bob o₁).symm hCks0) wsPrefixKdf_untagged.2.2.2.2.2.2.1 wsPrefixKdf_keyOfTake8.2.2.2.1
  have hRk0 : gamma compI0 S g o₁.keys.rk = wsRk0 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) hChainPrk wsPrefixKdf_untagged.2.2.2.2.1 wsPrefixKdf_keyOfTake8.2.2.2.2.1; have hPqxdhPrk : gamma compI0 S g pqxdhPrk = wsPqxdhPrk0 := gamma_key_of_hmac S g (gamma_hmac_len S g _ _) (gamma_eq_of_eq S g (iniAliceOut_rk tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6)).symm hRk0) wsPrefixKdf_untagged.2.1 wsPrefixKdf_keyOfTake8.2.2.2.2.2
  obtain ⟨hCk0, hPqr0⟩ := split40_fwd_pqxdh S g tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) hPqxdhPrk hRk0; obtain ⟨hCipherKey2, hIv2⟩ := split40_fwd_enc S g tr₃ stA₁' cl₂ (tr₃.length + 2) hPrk2' hMacKey2'
  exact ⟨hMacKey2', hPrk2', hSalt2', hSeed2', hCks1, hCks0, hChainPrk, hRk0, hPqxdhPrk, hCk0, hPqr0, split40_fwd_start S g tr₁ r.bob o₁ hChainPrk, (split40_fwd_kdfCk S g hCks0 wsPrefixKdf_forward.2.2.2.2.2.1 wsPrefixKdf_forward.2.2.2.2.2.2.1).1, (split40_fwd_kdfCk S g hCks1 wsPrefixKdf_forward.2.2.2.2.2.2.2.1 wsPrefixKdf_forward.2.2.2.2.2.2.2.2.1).2, hCipherKey2, hIv2⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoVals
