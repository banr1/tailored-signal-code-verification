/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnStA
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus
import Init.Data.String
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnB
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnStA Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus Symbolic.BugInjection.Proofs.Common443.CompC2RestR38 Symbolic.BugInjection.Proofs.Common443.CompC2Census38
open Symbolic.BugInjection.Proofs.Common443.CompExcuse (gamma_concat)
open Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct (gamma_hmac_length)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (not_kdfFree_kdfExtract)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 (call0Rng_length)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem gamma_kemEncap_fst_of_e1 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE1) : gamma compI0 S g (DY.PQKem.kemEncap pk e).1 = compKyberCt1 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_fst_eq h32,
      show compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) from rfl,
      Option.getD_some, he, compKyberEncaps_e1, List.take_left' Census443Memo.kyberCtVals_lengths.2.1]
theorem gamma_kemEncap_snd_of_e1 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE1) : gamma compI0 S g (DY.PQKem.kemEncap pk e).2 = compKyberSs1 := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32,
      show compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) from rfl,
      Option.getD_some, he, compKyberEncaps_e1, List.drop_left' Census443Memo.kyberCtVals_lengths.2.1]
theorem mem_memo_zeroKey_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₁ tr₂ : ExecTrace} {b : Participant} {ikA ikB spk pqpk : DY.Bytes} {cl₁ pq₁ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g DY.Spqr.zeroKey).memo) : x ∈ (gamma' i S g (encOut tr₂ (iniAliceStartState tr₁ b (iniAliceOut tr₁ ikA ikB spk pqpk none)) cl₁ pq₁)).memo := mem_memo_rk_of_encOut (mem_memo_hmac_left (mem_memo_hmac_left hx))
theorem mem_memo_trInfo1_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1))).memo) : x ∈ (gamma' i S g (encOut tr stA cl pq)).memo := mem_memo_akeys_cipherKey_of_encOut (mem_memo_hmac_right hx)
theorem mem_memo_trInfo2_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2))).memo) : x ∈ (gamma' i S g (encOut tr stA cl pq)).memo := mem_memo_akeys_macKey_of_encOut (mem_memo_hmac_right (mem_memo_concat_right hx))
theorem mem_memo_trInfo3_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 3))).memo) : x ∈ (gamma' i S g (encOut tr stA cl pq)).memo := mem_memo_akeys_iv_of_encOut (mem_memo_hmac_right (mem_memo_concat_right hx))
theorem not_rvW_hmac_concat_trInfo {S : Sem} {g : Ghost} (k m : DY.Bytes) (b : UInt8) :
    ¬ RvW (gamma compI0 S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.hmac k m) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte b)))) := by
  have h1 := gamma_hmac_length S g k m
  have h2 : (gamma compI0 S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte b))).length = 19 := by
    have hutf : "WhisperMessageKeys".toUTF8 = List.utf8Encode "WhisperMessageKeys".toList := by
      conv_lhs => rw [← String.ofList_toList (s := "WhisperMessageKeys")]
      rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
    have hL1 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")).length = 18 := by
      unfold DY.Libsignal.TripleRatchet.lit; rw [CompPlant.gamma_literalToBytes_length, hutf]; decide +kernel
    have hL2 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte b)).length = 1 := by
      unfold DY.Libsignal.TripleRatchet.litByte; rw [CompPlant.gamma_literalToBytes_length]; rfl
    rw [gamma_concat, List.length_append, hL1, hL2]
  rw [gamma_concat]
  exact not_rvW_of_kdf_prefix (not_kdfFree_kdfExtract k m) h1
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem mem_memo_trMsgKeys_cipherKey_exact {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt seed : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey).memo) : x.1 = (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac salt seed)).memo ∨ x ∈ (gamma' i S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 1))).memo := mem_memo_hmac_cases hx
theorem mem_memo_trMsgKeys_macKey_exact {S : Sem} {g : Ghost} {salt seed : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).memo) : x.1 = (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey ∨ x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.hmac salt seed)).memo ∨ x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey).memo ∨ x ∈ (gamma' compI0 S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2))).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_rhs
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_prk)
  · rcases mem_memo_concat_cases hx_rhs with hx1 | hx_ck | hx_info2
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hx1]; exact Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _, by rw [hx1]; exact not_rvW_hmac_concat_trInfo _ _ 2⟩)))
    · exact Or.inr (Or.inr (Or.inl hx_ck))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx_info2)))
theorem mem_memo_trMsgKeys_iv_exact {S : Sem} {g : Ghost} {salt seed : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv).memo) : x.1 = (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv ∨ x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.hmac salt seed)).memo ∨ x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).memo ∨ x ∈ (gamma' compI0 S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 3))).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_rhs
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_prk)
  · rcases mem_memo_concat_cases hx_rhs with hx1 | hx_mk | hx_info3
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hx1]; exact Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _, by rw [hx1]; exact not_rvW_hmac_concat_trInfo _ _ 3⟩)))
    · exact Or.inr (Or.inr (Or.inl hx_mk))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx_info3)))
theorem mem_memo_salted_cipherKey_exact40 {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).cipherKey).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g (encOut tr stA cl (tr.length + 2))).memo ∨ x.1 ∈ saltedNodes40 salt tr stA cl := by
  rcases mem_memo_trMsgKeys_cipherKey_exact hx with hx1 | hx_prk | hx_info1
  · exact Or.inr (Or.inr (by simp [saltedNodes40, hx1]))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (by simp [saltedNodes40, hx1]))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl (mem_memo_seed_of_encOut hx_seed))
  · exact Or.inr (Or.inl (mem_memo_trInfo1_of_encOut hx_info1))
theorem mem_memo_salted_macKey_exact40 {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey).memo) : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g (encOut tr stA cl (tr.length + 2))).memo ∨ x.1 ∈ saltedNodes40 salt tr stA cl ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_trMsgKeys_macKey_exact hx with hx1 | hx_prk | hx_ck | hx_info2 | h51
  · exact Or.inr (Or.inr (Or.inl (by simp [saltedNodes40, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inl (by simp [saltedNodes40, hx1])))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl (mem_memo_seed_of_encOut hx_seed))
  · rcases mem_memo_salted_cipherKey_exact40 (tr := tr) (stA := stA) (cl := cl) hx_ck with hs | hout | hnode
    · exact Or.inl hs
    · exact Or.inr (Or.inl hout)
    · exact Or.inr (Or.inr (Or.inl hnode))
  · exact Or.inr (Or.inl (mem_memo_trInfo2_of_encOut hx_info2))
  · exact Or.inr (Or.inr (Or.inr h51))
theorem mem_memo_salted_iv_exact40 {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).iv).memo) : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g (encOut tr stA cl (tr.length + 2))).memo ∨ x.1 ∈ saltedNodes40 salt tr stA cl ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_trMsgKeys_iv_exact hx with hx1 | hx_prk | hx_mk | hx_info3 | h51
  · exact Or.inr (Or.inr (Or.inl (by simp [saltedNodes40, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inl (by simp [saltedNodes40, hx1])))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl (mem_memo_seed_of_encOut hx_seed))
  · exact mem_memo_salted_macKey_exact40 (tr := tr) (stA := stA) (cl := cl) hx_mk
  · exact Or.inr (Or.inl (mem_memo_trInfo3_of_encOut hx_info3))
  · exact Or.inr (Or.inr (Or.inr h51))
theorem mem_memo_salted_computeMac_exact40 {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey stA.myIk stA.peerIk (encWire tr stA cl (tr.length + 2)))).memo) : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g (encOut tr stA cl (tr.length + 2))).memo ∨ x.1 ∈ saltedNodes40 salt tr stA cl ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_computeMac_cases hx with hx1 | hx1_full | hx_mk | hx_in
  · exact Or.inr (Or.inr (Or.inl (by simp [saltedNodes40, hx1])))
  · exact Or.inr (Or.inr (Or.inl (by simp [saltedNodes40, hx1_full])))
  · exact mem_memo_salted_macKey_exact40 (tr := tr) (stA := stA) (cl := cl) hx_mk
  · exact Or.inr (Or.inl (mem_memo_encMac_of_encOut (mem_memo_trunc8 (mem_memo_hmac_right hx_in))))
theorem mem_memo_honestSalts_in_preMemo40 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g salt).memo) : x ∈ preMemo40 r S g ms' := by
  obtain ⟨hout₂, hout₃, _, _⟩ := prefixTerms_mem_of_ws40Idx1RunInv hinv
  rcases hinv.hsalts salt hsalt with rfl | rfl | rfl
  · exact List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_zeroKey_of_encOut hx⟩
  · rw [← CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ r.bob _ cl₁] at hx
    exact List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_encSalt_of_encOut hx⟩
  · rw [← WsIdx1Split40OwnSalt.encSalt_self tr₃ _ cl₂] at hx
    exact List.mem_flatMap.mpr ⟨_, hout₃, mem_memo_encSalt_of_encOut hx⟩
theorem mem_memo_saltTerms_exact40 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {u : DY.Bytes} (hu : u ∈ WsIdx1Split40MemoNewSub.ws40Idx1SaltTerms r tr₁ tr₂ tr₃ cl₁ cl₂ salt) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g u).memo) : x ∈ preMemo40 r S g ms' ∨ x.1 ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  let stA₁' := stA40 r tr₁ tr₂ cl₁
  let seed₂ := (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2
  obtain ⟨_, hout₃, _, _⟩ := prefixTerms_mem_of_ws40Idx1RunInv hinv
  have hout₃_pre : ∀ {y : Row}, y ∈ (gamma' compI0 S g (encOut tr₃ stA₁' cl₂ (tr₃.length + 2))).memo → y ∈ preMemo40 r S g ms' :=
    fun hy => List.mem_flatMap.mpr ⟨_, hout₃, hy⟩
  have hsalts : (salt = DY.Spqr.zeroKey ∨ salt = ck1Salt40 r tr₁) ∨ salt = (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.1 := by
    rcases hinv.hsalts salt hsalt with hzero | hck1 | hsend2
    · exact Or.inl (Or.inl hzero)
    · exact Or.inl (Or.inr hck1)
    · exact Or.inr hsend2
  rcases hsalts with hzc | hsend2
  · have hstep : x ∈ (gamma' compI0 S g salt).memo ∨
        x ∈ (gamma' compI0 S g (encOut tr₃ stA₁' cl₂ (tr₃.length + 2))).memo ∨
        x.1 ∈ saltedNodes40 salt tr₃ stA₁' cl₂ ∨
        (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
      simp only [WsIdx1Split40MemoNewSub.ws40Idx1SaltTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · rcases mem_memo_salted_cipherKey_exact40 (tr := tr₃) (stA := stA₁') (cl := cl₂) hx with hs | hout | hnode
        · exact Or.inl hs
        · exact Or.inr (Or.inl hout)
        · exact Or.inr (Or.inr (Or.inl hnode))
      · exact mem_memo_salted_macKey_exact40 (tr := tr₃) (stA := stA₁') (cl := cl₂) hx
      · exact mem_memo_salted_iv_exact40 (tr := tr₃) (stA := stA₁') (cl := cl₂) hx
      · exact mem_memo_salted_computeMac_exact40 (tr := tr₃) (stA := stA₁') (cl := cl₂) hx
    rcases hstep with hs | hout | hnode | h51
    · exact Or.inl (mem_memo_honestSalts_in_preMemo40 hinv hsalt hs)
    · exact Or.inl (hout₃_pre hout)
    · exact Or.inr (Or.inl (saltedNodes40_sub_z40Terms_of_zero_or_ck1 hzc hnode))
    · exact Or.inr (Or.inr h51)
  · have hsalt_eq : salt = encSalt tr₃ stA₁' cl₂ (tr₃.length + 2) :=
      hsend2.trans (WsIdx1Split40OwnSalt.encSalt_self tr₃ stA₁' cl₂).symm
    have hkeys_eq := (congrArg (fun s => DY.Libsignal.TripleRatchet.trMsgKeys s seed₂) hsalt_eq).trans
      (trMsgKeys_encSalt_eq_encMsgKeys tr₃ stA₁' cl₂ (tr₃.length + 2))
    simp only [WsIdx1Split40MemoNewSub.ws40Idx1SaltTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rw [hkeys_eq] at hx; exact Or.inl (hout₃_pre (mem_memo_akeys_cipherKey_of_encOut hx))
    · rw [hkeys_eq] at hx; exact Or.inl (hout₃_pre (mem_memo_akeys_macKey_of_encOut hx))
    · rw [hkeys_eq] at hx; exact Or.inl (hout₃_pre (mem_memo_akeys_iv_of_encOut hx))
    · rw [hkeys_eq, computeMac_encMsgKeys_eq_encMac] at hx
      exact Or.inl (hout₃_pre (mem_memo_encMac_of_encOut hx))
theorem mem_newMemo40_exact_cases {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hown : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) {x : Row} (hx : x ∈ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂) : x ∈ preMemo40 r S g ms' ∨ x.1 ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ ∨ (assumedInjective x.1 = false ∧ ¬ RvW x.2.2) := by
  have hopk : p.preKeyId = none := WsIdx1Split40MemoNewSub.wire3Idx1Bytes_preKeyId hp; obtain ⟨hek, hct⟩ := ek_ct_mem_prefixTerms_of_links40Own hown; obtain ⟨_, hout₃, _, _⟩ := prefixTerms_mem_of_ws40Idx1RunInv hinv; have hv : x.2.2 = gamma compI0 S g x.1 := exists_memo_of_mem40 (List.mem_append_right _ hx); unfold newMemo40 at hx; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  rcases WsIdx1Split40MemoNewSub.mem_split40NewTerms_iff.mp hu with rfl | rfl | rfl | hbt
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hek, hxu⟩)
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hct, hxu⟩)
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₃, hxu⟩)
  · rcases WsIdx1Split40MemoNewSub.mem_bobTerms_x40Idx1_iff hfits.1.1.1 hopk hbt with hextra | ⟨salt, hsalt, hsalt_u⟩
    · exact Or.inl (mem_memo_extraTerms_ws40Idx1 hinv hextra hxu)
    · rcases mem_memo_saltTerms_exact40 hinv hsalt hsalt_u hxu with hpre | hz | ⟨hni, hnr⟩
      · exact Or.inl hpre
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr ⟨hni, by rw [hv]; exact hnr⟩)
theorem split40RestFnNewOwn : Split40RestFnNewOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x hx hpre _hc
  rcases mem_newMemo40_exact_cases hfits hp hinv hown hx with hpre' | hz | ⟨hni, hnr⟩
  · exact absurd hpre' hpre
  · exact fnOK40_of_z40 hz
  · exact fnOK40_of_nonInj hni (fun hrv => hnr (rvW_of_rv40 hfits hp hinv hown _ hrv))
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnB
