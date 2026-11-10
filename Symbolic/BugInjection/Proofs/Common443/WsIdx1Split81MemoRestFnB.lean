/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnB
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStA
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnTbl
import Init.Data.String
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnB
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusOwn Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnB Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStA Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnTbl Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection.Proofs.Common443.CompExcuse (gamma_concat)
open Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct (gamma_hmac_length)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (not_kdfFree_kdfExtract)
open Symbolic.BugInjection.Proofs.Common443.CompC2RestR38 (gamma_symEnc_eq')
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80 (sendAt)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop (ptAt)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead78 (call4Rng)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 (call0Rng_length)
private theorem toUTF8_eq_ofList (s : String) : s.toUTF8 = List.utf8Encode s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
theorem mem_memo_lit_eq (S : Sem) (g : Ghost) (b : ByteArray) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack)).memo) : assumedInjective x.1 = false ∧ gamma compI0 S g x.1 = ofByteArray b := by unfold gamma' at hx; rw [DY.Bytes.rec_eq gLit0 (gAll compI0 S g)] at hx; simp only [gLit0, concretizeLit, node, List.flatMap_nil, List.mem_singleton] at hx; subst hx; exact ⟨Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_lit_pack_eq b, CompFreshDistinct.gamma_lit compI0 S g b⟩
theorem gamma_lit_whisperRatchet_len (S : Sem) (g : Ghost) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")).length = 14 := by unfold DY.Libsignal.TripleRatchet.lit; rw [CompPlant.gamma_literalToBytes_length, toUTF8_eq_ofList]; decide +kernel
theorem gamma_litByte_len (S : Sem) (g : Ghost) (b : UInt8) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.litByte b)).length = 1 := by unfold DY.Libsignal.TripleRatchet.litByte; rw [CompPlant.gamma_literalToBytes_length]; rfl
set_option maxRecDepth 200000 in
theorem mem_memo_litByte_12_not_rvW (S : Sem) (g : Ghost) {b : UInt8} (hb : b = 1 ∨ b = 2) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.litByte b)).memo) : assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1) := by
  obtain ⟨hni, hval⟩ := mem_memo_lit_eq S g _ hx
  refine ⟨hni, ?_⟩
  rw [hval]
  rcases hb with rfl | rfl <;> decide +kernel
set_option maxRecDepth 200000 in
theorem mem_memo_whisperRatchet_concat_exact (S : Sem) (g : Ghost) {b : UInt8} (hb : b = 1 ∨ b = 2) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte b))).memo) : assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1) := by
  rcases mem_memo_concat_cases hx with hx1 | hx_l | hx_r
  · rw [hx1]; refine ⟨Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _, ?_⟩
    unfold DY.Libsignal.TripleRatchet.lit DY.Libsignal.TripleRatchet.litByte
    rw [gamma_concat, CompC3RestFn38HBA.gamma_literalToBytes_eq, CompC3RestFn38HBA.gamma_literalToBytes_eq, toUTF8_eq_ofList]
    rcases hb with rfl | rfl <;> decide +kernel
  · obtain ⟨hni, hval⟩ := mem_memo_lit_eq S g _ hx_l; exact ⟨hni, by rw [hval, toUTF8_eq_ofList]; decide +kernel⟩
  · exact mem_memo_litByte_12_not_rvW S g hb hx_r
theorem mem_memo_createChain_fst_exact {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1).memo) : x.1 = (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∨ x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.hmac rk (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk))).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_info
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_prk)
  · exact Or.inr (Or.inr (mem_memo_whisperRatchet_concat_exact S g (Or.inl rfl) hx_info))
theorem mem_memo_createChain_snd_exact {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).memo) : x.1 = (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 ∨ x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.hmac rk (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk))).memo ∨ x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_rhs
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_prk)
  · rcases mem_memo_concat_cases hx_rhs with hx1 | hx_rk | hx_info
    · rw [hx1]; refine Or.inr (Or.inr (Or.inr ⟨Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _, ?_⟩))
      unfold DY.Libsignal.TripleRatchet.hkdfBlock1 DY.X25519.agree
      rw [gamma_concat]
      have h1 := gamma_hmac_length S g (DY.Libsignal.TripleRatchet.hmac rk (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key pk) sk)) (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 1))
      have h2 : (gamma compI0 S g (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") (DY.Libsignal.TripleRatchet.litByte 2))).length = 15 := by
        rw [gamma_concat, List.length_append, gamma_lit_whisperRatchet_len, gamma_litByte_len]
      exact not_rvW_of_kdf_prefix (not_kdfFree_kdfExtract _ _) h1
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact Or.inr (Or.inr (Or.inl hx_rk))
    · exact Or.inr (Or.inr (Or.inr (mem_memo_whisperRatchet_concat_exact S g (Or.inr rfl) hx_info)))
theorem mem_memo_kdfCk_fst_exact {S : Sem} {g : Ghost} {ck : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck).1).memo) : x.1 = (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∨ x ∈ (gamma' compI0 S g ck).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_ck | hx_lit
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_ck)
  · exact Or.inr (Or.inr (mem_memo_litByte_12_not_rvW S g (Or.inr rfl) hx_lit))
theorem mem_memo_kdfCk_snd_exact {S : Sem} {g : Ghost} {ck : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck).2).memo) : x.1 = (DY.Libsignal.TripleRatchet.kdfCk ck).2 ∨ x ∈ (gamma' compI0 S g ck).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_ck | hx_lit
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_ck)
  · exact Or.inr (Or.inr (mem_memo_litByte_12_not_rvW S g (Or.inl rfl) hx_lit))
theorem mem_memo_c_ck0_stepNodes0_exact {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).memo) : x ∈ (gamma' compI0 S g rk).memo ∨ x ∈ (gamma' compI0 S g (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk)).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ createChainStepNodes0 rk pk sk := by
  rcases mem_memo_createChain_snd_exact hx with hx1 | hx_prk | hx_rk | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_r | hx_dh
    · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
    · exact Or.inl hx_r
    · exact Or.inr (Or.inl hx_dh)
  · rcases mem_memo_createChain_fst_exact hx_rk with hx1 | hx_prk | hinj
    · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
    · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_r | hx_dh
      · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
      · exact Or.inl hx_r
      · exact Or.inr (Or.inl hx_dh)
    · exact Or.inr (Or.inr (Or.inl hinj))
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_seed0_stepNodes0_exact {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).2).memo) : x ∈ (gamma' compI0 S g rk).memo ∨ x ∈ (gamma' compI0 S g (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk)).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ createChainStepNodes0 rk pk sk := by
  rcases mem_memo_kdfCk_snd_exact hx with hx1 | hx_ck0 | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
  · exact mem_memo_c_ck0_stepNodes0_exact hx_ck0
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_c_ck1_stepNodes0_exact {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).1).memo) : x ∈ (gamma' compI0 S g rk).memo ∨ x ∈ (gamma' compI0 S g (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk)).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ createChainStepNodes0 rk pk sk := by
  rcases mem_memo_kdfCk_fst_exact hx with hx1 | hx_ck0 | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
  · exact mem_memo_c_ck0_stepNodes0_exact hx_ck0
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_salted_cipherKey_exact {S : Sem} {g : Ghost} {salt seed myIk peerIk : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey).memo) : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g seed).memo ∨ x ∈ (gamma' compI0 S g (encOut tr stA cl (tr.length + 2))).memo ∨ x.1 ∈ saltedStepNodes salt seed myIk peerIk (encWire tr stA cl (tr.length + 2)) := by
  rcases mem_memo_trMsgKeys_cipherKey_exact hx with hx1 | hx_prk | hx_info1
  · exact Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1])))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl hx_seed)
  · exact Or.inr (Or.inr (Or.inl (mem_memo_trInfo1_of_encOut hx_info1)))
theorem mem_memo_salted_macKey_exact {S : Sem} {g : Ghost} {salt seed myIk peerIk : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).memo) : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g seed).memo ∨ x ∈ (gamma' compI0 S g (encOut tr stA cl (tr.length + 2))).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ saltedStepNodes salt seed myIk peerIk (encWire tr stA cl (tr.length + 2)) := by
  rcases mem_memo_trMsgKeys_macKey_exact hx with hx1 | hx_prk | hx_ck | hx_info2 | ⟨hni, hnr⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1]))))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1]))))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl hx_seed)
  · rcases mem_memo_salted_cipherKey_exact (myIk := myIk) (peerIk := peerIk) (tr := tr) (stA := stA) (cl := cl) hx_ck with hs | hsd | hout | hnode
    · exact Or.inl hs
    · exact Or.inr (Or.inl hsd)
    · exact Or.inr (Or.inr (Or.inl hout))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hnode)))
  · exact Or.inr (Or.inr (Or.inl (mem_memo_trInfo2_of_encOut hx_info2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hni, hnr⟩)))
theorem mem_memo_salted_iv_exact {S : Sem} {g : Ghost} {salt seed myIk peerIk : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv).memo) : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g seed).memo ∨ x ∈ (gamma' compI0 S g (encOut tr stA cl (tr.length + 2))).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ saltedStepNodes salt seed myIk peerIk (encWire tr stA cl (tr.length + 2)) := by
  rcases mem_memo_trMsgKeys_iv_exact hx with hx1 | hx_prk | hx_mk | hx_info3 | ⟨hni, hnr⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1]))))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1]))))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl hx_seed)
  · exact mem_memo_salted_macKey_exact (myIk := myIk) (peerIk := peerIk) (tr := tr) (stA := stA) (cl := cl) hx_mk
  · exact Or.inr (Or.inr (Or.inl (mem_memo_trInfo3_of_encOut hx_info3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hni, hnr⟩)))
theorem mem_memo_salted_computeMac_exact {S : Sem} {g : Ghost} {salt seed : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey stA.myIk stA.peerIk (encWire tr stA cl (tr.length + 2)))).memo) : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g seed).memo ∨ x ∈ (gamma' compI0 S g (encOut tr stA cl (tr.length + 2))).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ saltedStepNodes salt seed stA.myIk stA.peerIk (encWire tr stA cl (tr.length + 2)) := by
  rcases mem_memo_computeMac_cases hx with hx1 | hx1_full | hx_mk | hx_in
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1_full]))))
  · exact mem_memo_salted_macKey_exact (myIk := stA.myIk) (peerIk := stA.peerIk) (tr := tr) (stA := stA) (cl := cl) hx_mk
  · exact Or.inr (Or.inr (Or.inl (mem_memo_macInput_of_encOut hx_in)))
attribute [local irreducible] setupPublic setupSecret
theorem mem_memo_honestSalts_in_preMemo81 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g salt).memo) : x ∈ preMemo81 r S g ms' := by
  obtain ⟨hout₂, hout₃, hout₅, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv
  rcases hinv.hsalts salt hsalt with rfl | rfl | rfl | rfl
  · exact List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_zeroKey_of_encOut hx⟩
  · rw [← CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ r.bob _ cl₁] at hx
    exact List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_encSalt_of_encOut hx⟩
  · rw [← CompRSchedBSalts.encSalt_self tr₃ _ cl₂] at hx
    exact List.mem_flatMap.mpr ⟨_, hout₃, mem_memo_encSalt_of_encOut hx⟩
  · rw [← CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₄ tr₅ r.bob _ cl₅] at hx
    exact List.mem_flatMap.mpr ⟨_, hout₅, mem_memo_encSalt_of_encOut hx⟩
theorem mem_memo_stepNodes0_ws81Idx1_exact_of_or {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hNe : r.alice ≠ r.bob) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {x : DY.Bytes × DY.Bytes × HwBytes} (h : x ∈ (gamma' compI0 S g (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk).memo ∨ x ∈ (gamma' compI0 S g (DY.DiffieHellman.dh (DY.X25519.x25519Key (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32))) (setupSecret r 2))).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ createChainStepNodes0 (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (setupSecret r 2)) : x ∈ preMemo81 r S g ms' ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ := by
  obtain ⟨hout₂, _, hout₅, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv
  rcases h with hx_rk | hx_dh | hinj | hstep
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, mem_memo_rk_of_encOut hx_rk⟩)
  · rw [dh_bob_ws81_eq hNe tr₁] at hx_dh
    exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_createChain_dh_of_encOut tr₁ tr₂ r.bob _ cl₁ (tr₂.length + 2) hx_dh⟩)
  · exact Or.inr (Or.inl hinj)
  · rw [createChainStepNodes0_eq_bobChainTerms81 hNe tr₁ tr₂ tr₄ cl₁] at hstep; exact Or.inr (Or.inr hstep)
theorem mem_memo_ws81Idx1ChainTerms_exact {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hNe : r.alice ≠ r.bob) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {u : DY.Bytes} (hu : u ∈ ws81Idx1ChainTerms r tr₁ tr₂ tr₄) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g u).memo) : x ∈ preMemo81 r S g ms' ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ := by
  obtain ⟨hout₂, _, hout₅, hser₅⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv; unfold ws81Idx1ChainTerms at hu; dsimp only at hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, mem_memo_rk_of_encOut hx⟩)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hser₅, mem_memo_ck_of_serialize_encSt r.alice r.bob tr₄ tr₅ _ cl₅ hx⟩)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, mem_memo_pqr_of_encOut hx⟩)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact mem_memo_stepNodes0_ws81Idx1_exact_of_or hNe hinv (mem_memo_c_ck0_stepNodes0_exact hx)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact mem_memo_stepNodes0_ws81Idx1_exact_of_or hNe hinv (mem_memo_c_ck1_stepNodes0_exact hx)
  rcases List.mem_singleton.mp hu with rfl
  exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_pt_of_encOut hx⟩)
private theorem finish_salted_cases {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hNe : r.alice ≠ r.bob) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {x : DY.Bytes × DY.Bytes × HwBytes} (h : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (setupSecret r 2)).2).2).memo ∨ x ∈ (gamma' compI0 S g (encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2))).memo ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ saltedStepNodes salt (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (setupSecret r 2)).2).2 (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)).myIk (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)).peerIk (encWire tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2))) : x ∈ preMemo81 r S g ms' ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ ∨ x.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂ := by
  obtain ⟨hout₂, _, _, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv; have hsn_eq := saltedStepNodes_eq_saltedNodes81 hNe tr₁ tr₂ tr₄ cl₁ salt; dsimp only at hsn_eq
  rcases h with hx_salt | hx_seed | hout | hinj | hs
  · exact Or.inl (mem_memo_honestSalts_in_preMemo81 hinv hsalt hx_salt)
  · rcases mem_memo_stepNodes0_ws81Idx1_exact_of_or hNe hinv (mem_memo_seed0_stepNodes0_exact hx_seed) with
      hpre | hinj' | hch
    · exact Or.inl hpre
    · exact Or.inr (Or.inl hinj')
    · exact Or.inr (Or.inr (Or.inl hch))
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, hout⟩)
  · exact Or.inr (Or.inl hinj)
  · rw [hsn_eq] at hs; exact Or.inr (Or.inr (Or.inr (mem_z81Terms_of_honestSalts hinv hsalt hs)))
theorem mem_memo_ws81Idx1SaltTerms_exact {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hNe : r.alice ≠ r.bob) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {u : DY.Bytes} (hu : u ∈ ws81Idx1SaltTerms r tr₁ tr₂ tr₄ cl₁ salt) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g u).memo) : x ∈ preMemo81 r S g ms' ∨ (assumedInjective x.1 = false ∧ ¬ RvW (gamma compI0 S g x.1)) ∨ x.1 ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ ∨ x.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂ := by
  unfold ws81Idx1SaltTerms at hu; dsimp only at hu
  let stA₁ := iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
  rcases List.mem_cons.mp hu with rfl | hu
  · refine finish_salted_cases hNe hinv hsalt ?_
    rcases mem_memo_salted_cipherKey_exact (myIk := stA₁.myIk) (peerIk := stA₁.peerIk)
      (tr := tr₂) (stA := stA₁) (cl := cl₁) hx with a | b | c | d
    · exact Or.inl a
    · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inr (Or.inl c))
    · exact Or.inr (Or.inr (Or.inr (Or.inr d)))
  rcases List.mem_cons.mp hu with rfl | hu
  · exact finish_salted_cases hNe hinv hsalt (mem_memo_salted_macKey_exact (myIk := stA₁.myIk)
      (peerIk := stA₁.peerIk) (tr := tr₂) (stA := stA₁) (cl := cl₁) hx)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact finish_salted_cases hNe hinv hsalt (mem_memo_salted_iv_exact (myIk := stA₁.myIk)
      (peerIk := stA₁.peerIk) (tr := tr₂) (stA := stA₁) (cl := cl₁) hx)
  rcases List.mem_singleton.mp hu with rfl
  exact finish_salted_cases hNe hinv hsalt
    (mem_memo_salted_computeMac_exact (tr := tr₂) (stA := stA₁) (cl := cl₁) hx)
theorem mem_newMemo81_exact_cases {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {x : Row} (hx : x ∈ newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁) : x ∈ preMemo81 r S g ms' ∨ x.1 ∈ extChainTerms81 r tr₁ tr₂ tr₄ cl₁ ∨ x.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂ ∨ (assumedInjective x.1 = false ∧ ¬ RvW x.2.2) := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hopk : p.preKeyId = none := wire6Idx1Bytes_preKeyId hp; obtain ⟨hout₂, _, hout₅, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv; have hv : x.2.2 = gamma compI0 S g x.1 := (sound_of_mem_flatMap hx).2; unfold newMemo81 at hx; rw [split81NewTerms_x81Idx1_eq r ms' p tr₁ tr₂ tr₄ cl₁] at hx; obtain ⟨u, hu, hx_u⟩ := List.mem_flatMap.mp hx; simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
  rcases hu with rfl | rfl | rfl | hu_bob
  · rcases mem_memo_ek_aliceOut_cases (tr₅ := tr₅) (b := r.bob) (cl₅ := cl₅) (pq₅ := tr₅.length + 2) hx_u with hx1 | hx_out₅
    · exact Or.inr (Or.inl (List.mem_cons.mpr (Or.inl hx1)))
    · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, hx_out₅⟩)
  · rcases mem_memo_ct_aliceOut_cases (tr₅ := tr₅) (b := r.bob) (cl₅ := cl₅) (pq₅ := tr₅.length + 2) hx_u with hx1 | hx_out₅
    · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl hx1))))
    · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, hx_out₅⟩)
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, hx_u⟩)
  · rcases mem_bobTerms_x81Idx1_iff hNe hopk hu_bob with hu_ch | ⟨salt, hsalt, hu_salt⟩
    · rcases mem_memo_ws81Idx1ChainTerms_exact hNe hinv hu_ch hx_u with hpre | ⟨hni, hnr⟩ | hch
      · exact Or.inl hpre
      · exact Or.inr (Or.inr (Or.inr ⟨hni, by rw [hv]; exact hnr⟩))
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hch)))
    · rcases mem_memo_ws81Idx1SaltTerms_exact hNe hinv hsalt hu_salt hx_u with hpre | ⟨hni, hnr⟩ | hch | hs
      · exact Or.inl hpre
      · exact Or.inr (Or.inr (Or.inr ⟨hni, by rw [hv]; exact hnr⟩))
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hch)))
      · exact Or.inr (Or.inr (Or.inl hs))
theorem fnOK81_of_extChainTerms81 {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hNe : r.alice ≠ r.bob) {x : DY.Bytes × DY.Bytes × HwBytes} (hu : x.1 ∈ extChainTerms81 r tr₁ tr₂ tr₄ cl₁) : FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x := by
  unfold extChainTerms81 at hu
  rcases List.mem_cons.mp hu with h | hu
  · refine fnOK81_of_dhPk (sk := randTerm tr₄.length 32) h ?_
    rw [h]; exact mem_allTerms81_of_x (by simp [xTerms81, x81Idx1, Census443Defs.iniAliceOut])
  rcases List.mem_cons.mp hu with h | hbob
  · have hct : (x81Idx1 r tr₁ tr₂ tr₄ cl₁).ct =
        (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₄.length + 1) 32)).1 := by
      dsimp only [x81Idx1, Census443Defs.iniAliceOut, DY.Libsignal.PQXDH.aliceAgreement]; rw [CompMemoInjGt.setupPublic_6 hNe]
    refine fnOK81_of_r (by
      rw [h, hct]
      exact (Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr
        (by rw [Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.kemEncap_fst_eq_pack]; simp [DY.BytesView.view_pack])) ?_
    rw [h, hct]; exact List.mem_append_right _ (List.mem_append_left _ (by simp [rTerms81ExtBase]))
  · obtain ⟨k₀, m₀, hu_eq, _⟩ := bobChainTerms81_isKdf_salt32 r S g tr₁ tr₂ tr₄ cl₁ hbob
    exact fnOK81_of_kdf hu_eq
theorem split81RestFnNewOwn : Split81RestFnNewOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown tr_bob hbob x hx hpre _hc
  rcases mem_newMemo81_exact_cases hfits hp hinv hx with hpre' | hext | hz | ⟨hni, hnr⟩
  · exact absurd hpre' hpre
  · exact fnOK81_of_extChainTerms81 hfits.1.1.1 hext
  · exact fnOK81_of_z81 hz
  · exact fnOK81_of_nonInj hni (fun hrv => hnr (rv81_mem_rVals81 hfits hp hinv hown hbob hrv))
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnB
