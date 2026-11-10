/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
public import Symbolic.BugInjection.Proofs.Common443.Census443Memo
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSubAux
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0) open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub ( eq_take_append_cons_drop runTrace_eq_of_getElem? setupTrace_le_of_runTrace_take next_le_runTrace_of_getElem? mem_runVis_of_getElem? encrypt_vis_eq trStateStoredAt_encNextTr mem_storedStates_iff encOut_mem_prefixTerms_of_getElem? serialize_encSt_mem_prefixTerms_of_getElem? mem_memo_concat_cases mem_memo_hmac_cases mem_memo_concat_left mem_memo_concat_right mem_memo_hmac_left mem_memo_hmac_right mem_memo_trunc8 mem_memo_encWire_of_encOut mem_memo_encMac_of_encOut mem_memo_encCiphertext_of_encOut mem_memo_encPqMsg_of_encOut mem_memo_akeys_cipherKey_of_encOut mem_memo_pt_of_encOut mem_memo_macInput_of_encOut mem_memo_seed_of_encOut mem_memo_cks_of_encOut mem_memo_rk_of_encOut mem_memo_pqr_of_encOut mem_memo_encSalt_of_encOut mem_memo_ck_of_serialize_encSt mem_symDec_encCiphertext_eq)
export Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc ( mem_prefixTerms_of_send_vis mem_prefixTerms_of_storedStates length_le_of_trace_le lt_length_of_at?_some mem_memo_lit_assumedInjective_false mem_memo_concatPrefixes_mem mem_memo_concatPrefixes_tail self_mem_slowBytes_serialize chainKey_mem_serialize_recvChain mem_memo_chainKey_of_serialize_recvList)
theorem prefixTerms_mem_of_ws81Idx1RunInv
    {r : Records} {S : Sem} {g : Ghost} {ms' : List Move}
    {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
    (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let stA₁' := encSt tr₂ stA₁ cl₁
    let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₂ := iniAliceStartState tr₄ r.bob o₂
    encOut tr₂ stA₁ cl₁ (tr₂.length + 2) ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    encOut tr₃ stA₁' cl₂ (tr₃.length + 2) ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    encOut tr₅ stA₂ cl₅ (tr₅.length + 2) ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    (Comparse.serialize (⟨r.alice, encSt tr₅ stA₂ cl₅⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∈
      prefixTerms r (runTraceMoves r ms') (runVis r ms') := by
  obtain ⟨k₁, k₂, k₃, k₄, k₅, hb₁, hb₄, sh₁, sh₄, s₁, s₂, s₅, pq₁, pq₂, pq₅, w₁, w₂, w₅, _, _, _, _, _, _, htr₂, hget₂, htr₃, hget₃, _, _, htr₅, hget₅,
    _, _, rfl, rfl, rfl, henc₂, henc₃, henc₅⟩ := hinv.links
  exact ⟨encOut_mem_prefixTerms_of_getElem? htr₂ hget₂ henc₂, encOut_mem_prefixTerms_of_getElem? htr₃ hget₃ henc₃, encOut_mem_prefixTerms_of_getElem? htr₅ hget₅ henc₅, serialize_encSt_mem_prefixTerms_of_getElem? htr₅ hget₅ henc₅⟩
theorem mem_memo_dhPk_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.DiffieHellman.dhPk sk)).memo) : x.1 = DY.DiffieHellman.dhPk sk ∨ x ∈ (gamma' i S g sk).memo := by
  unfold gamma' at hx
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gDhPk i) (gAll i S g)] at hx
  simp only [gDhPk, concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, CompMemoInjGt.bytes_rec_gAll] at hx; exact hx.imp (congrArg Prod.fst) id
theorem mem_memo_dhPk {i : ExternInterpretation} {S : Sem} {g : Ghost} {sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g sk).memo) : x ∈ (gamma' i S g (DY.DiffieHellman.dhPk sk)).memo := by
  unfold gamma' at hx ⊢
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gDhPk i) (gAll i S g)]
  simp only [gDhPk, concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, CompMemoInjGt.bytes_rec_gAll]; exact Or.inr hx
theorem mem_memo_dh_pack_left {i : ExternInterpretation} {S : Sem} {g : Ghost} {pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g pk).memo) : x ∈ (gamma' i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).memo := by unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gDh i) (gAll i S g)]; simp only [gDh, concretizeDh, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, CompMemoInjGt.bytes_rec_gAll]; exact Or.inr (Or.inl hx)
theorem mem_memo_dh_pack_right {i : ExternInterpretation} {S : Sem} {g : Ghost} {pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g sk).memo) : x ∈ (gamma' i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).memo := by unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gDh i) (gAll i S g)]; simp only [gDh, concretizeDh, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, CompMemoInjGt.bytes_rec_gAll]; exact Or.inr (Or.inr hx)
theorem mem_memo_dh_right {i : ExternInterpretation} {S : Sem} {g : Ghost} {pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g sk).memo) : x ∈ (gamma' i S g (DY.DiffieHellman.dh pk sk)).memo := by
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split <;> first | exact mem_memo_dh_pack_right hx | (split <;> first | exact mem_memo_dh_pack_right hx | exact mem_memo_dh_pack_left (mem_memo_dhPk hx))
theorem mem_memo_agree_right {i : ExternInterpretation} {S : Sem} {g : Ghost} {pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g sk).memo) : x ∈ (gamma' i S g (DY.Libsignal.PQXDH.agree pk sk)).memo := mem_memo_dh_right hx
theorem mem_memo_ek_aliceOut_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₄ tr₅ : ExecTrace} {b : Participant} {ikA ikB spk pqpk : DY.Bytes} {cl₅ pq₅ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (iniAliceOut tr₄ ikA ikB spk pqpk none).ek).memo) : x.1 = (iniAliceOut tr₄ ikA ikB spk pqpk none).ek ∨ x ∈ (gamma' i S g (encOut tr₅ (iniAliceStartState tr₄ b (iniAliceOut tr₄ ikA ikB spk pqpk none)) cl₅ pq₅)).memo := by
  rcases mem_memo_dhPk_cases hx with hx1 | hx_sk
  · exact Or.inl hx1
  · exact Or.inr (mem_memo_rk_of_encOut (mem_memo_hmac_left (mem_memo_hmac_right
      (mem_memo_concat_right (mem_memo_concat_right (mem_memo_concat_left (mem_memo_agree_right hx_sk)))))))
theorem mem_memo_kemEncap_fst_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {pk e : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.PQKem.kemEncap pk e).1).memo) : x.1 = (DY.PQKem.kemEncap pk e).1 ∨ x ∈ (gamma' i S g pk).memo ∨ x ∈ (gamma' i S g e).memo := by
  unfold gamma' at hx
  rw [show (DY.PQKem.kemEncap pk e).1 = ({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gKemEncap i) (gAll i S g)] at hx
  dsimp only [gKemEncap, concretizeKemEncap] at hx; split_ifs at hx
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.mem_append, CompMemoInjGt.bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe <;> [exact Or.inl rfl; exact Or.inr (Or.inl hxpk); exact Or.inr (Or.inr hxe)]
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, CompMemoInjGt.bytes_rec_gAll] at hx
    exact Or.inr hx
theorem mem_memo_kemEncap_snd_of_children {i : ExternInterpretation} {S : Sem} {g : Ghost} {pk e : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g pk).memo ∨ x ∈ (gamma' i S g e).memo) : x ∈ (gamma' i S g (DY.PQKem.kemEncap pk e).2).memo := by
  unfold gamma' at hx ⊢
  rw [show (DY.PQKem.kemEncap pk e).2 = ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (gKemSS i S) (gAll i S g)]
  dsimp only [gKemSS, concretizeKemSS]; split_ifs
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons, List.mem_append, CompMemoInjGt.bytes_rec_gAll]; exact Or.inr hx
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, CompMemoInjGt.bytes_rec_gAll]; exact hx
theorem mem_memo_ct_aliceOut_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₄ tr₅ : ExecTrace} {b : Participant} {ikA ikB spk pqpk : DY.Bytes} {cl₅ pq₅ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (iniAliceOut tr₄ ikA ikB spk pqpk none).ct).memo) : x.1 = (iniAliceOut tr₄ ikA ikB spk pqpk none).ct ∨ x ∈ (gamma' i S g (encOut tr₅ (iniAliceStartState tr₄ b (iniAliceOut tr₄ ikA ikB spk pqpk none)) cl₅ pq₅)).memo := by
  change x ∈ (gamma' i S g (DY.PQKem.kemEncap pqpk (randTerm (tr₄.length + 1) 32)).1).memo at hx
  rcases mem_memo_kemEncap_fst_cases hx with hx1 | hch
  · exact Or.inl hx1
  · exact Or.inr (mem_memo_rk_of_encOut (mem_memo_hmac_left (mem_memo_hmac_right
      (mem_memo_concat_right (mem_memo_concat_right (mem_memo_concat_right (mem_memo_concat_right (mem_memo_kemEncap_snd_of_children hch))))))))
theorem mem_memo_createChain_dh_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} (tr₁ tr₂ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl pq : Nat) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.DiffieHellman.dh (DY.X25519.x25519Key o.spk) (randTerm (tr₁.length + 2) 32))).memo) : x ∈ (gamma' i S g (encOut tr₂ (iniAliceStartState tr₁ b o) cl pq)).memo := mem_memo_cks_of_encOut (mem_memo_hmac_left (mem_memo_hmac_right hx))
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs
