/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnSt
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStAb
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnTbl
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnWire
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnA

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnSt
open CryptoProofLib.Refinement (ExternInterpretation)
open ByteSpecs DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnTbl Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnWire Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnA Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStA Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStAb Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompRX0Top Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
open Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA (KdfTail6 gamma_literalToBytes_eq gamma_agree_mem_x25519Vals gamma_serializedIk_length)
open Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HB (gamma_setup_len gamma_kemEncap_snd_length' aliceOut_ck_length aliceOut_ck_not_kdfFree gamma_agree_length)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
section NRSt
variable {S : Sem} {g : Ghost}
section TableMems
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnSt ( mem_r40_0 mem_r40_5 mem_r40_10 mem_r40_16 mem_r40_ek mem_r40_ent mem_r40_dhs mem_r40_pt1 mem_r40_c1 mem_r40_c2 mem_r40_pt2 mem_r40_ct1 mem_r40_ct2 mem_r40_kct mem_r40_kss mem_x40_0 mem_x40_5 mem_x40_10 mem_x40_ek mem_x40_dhs mem_x40_ag1 mem_x40_ag2 mem_x40_ag3 mem_x40_ag4 gamma_setupPublic_2_length o40_spk_eq o40_ikA_length o40_ikB_length o40_rk_length o40_ck_not_kdfFree o40_ck_length nrcensusW_storedSecrets_of_mem nrcensusW_aliceOut_of_mem nrcensusW_createChain_spk trStateNRC_iniAliceStartState trStateNRC_encSt trStateNRC_encSt_zero nrcensusW_serAlice nrcensusW_encSalt_self nrcensusW_enc_of_mem)
variable {r : Records} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
theorem mem_r81_0 : randTerm 0 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_0
theorem mem_r81_5 : randTerm 5 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_5
theorem mem_r81_10 : randTerm 10 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_10
theorem mem_r81_16 : randTerm 16 64 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_16
theorem mem_r81_ek1 : randTerm tr₁.length 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_ek
theorem mem_r81_ent1 : randTerm (tr₁.length + 1) 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_ent
theorem mem_r81_dhs1 : randTerm (tr₁.length + 2) 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_dhs
theorem mem_r81_pt1 : randTerm tr₂.length 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_pt1
theorem mem_r81_c1 (h : cl₁ ≠ 0) : randTerm (tr₂.length + 1) cl₁ ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ (mem_r40_c1 h)
theorem mem_r81_c2 (h : cl₂ ≠ 0) : randTerm (tr₃.length + 1) cl₂ ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ (mem_r40_c2 h)
theorem mem_r81_pt2 : randTerm tr₃.length 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_pt2
theorem mem_r81_ct1 : DY.SymEnc.symEnc (keys40 tr₂ (stA1_40 r tr₁) cl₁).cipherKey (keys40 tr₂ (stA1_40 r tr₁) cl₁).iv (randTerm tr₂.length 32) ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_ct1
theorem mem_r81_ct2 : DY.SymEnc.symEnc (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).cipherKey (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).iv (randTerm tr₃.length 32) ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_ct2
theorem mem_r81_kct1 : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).1 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_kct
theorem mem_r81_kss1 : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ mem_r40_kss
theorem mem_r81_bob : randTerm tr_bob.length 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_left _ (.head _))
theorem mem_r81_ek2 : randTerm tr₄.length 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_left _ (.tail _ (.head _)))
theorem mem_r81_ent2 : randTerm (tr₄.length + 1) 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_left _ (.tail _ (.tail _ (.head _))))
theorem mem_r81_dhs2 : randTerm (tr₄.length + 2) 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _)))))
theorem mem_r81_pt5 : randTerm tr₅.length 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
theorem mem_r81_c5 (h : cl₅ ≠ 0) : randTerm (tr₅.length + 1) cl₅ ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_right _ (by simp [coinTerms, h]))
theorem mem_r81_ct5 : DY.SymEnc.symEnc (keys40 tr₅ (stA2_81 r tr₄) cl₅).cipherKey (keys40 tr₅ (stA2_81 r tr₄) cl₅).iv (randTerm tr₅.length 32) ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
theorem mem_r81_kct2 : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₄.length + 1) 32)).1 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
theorem mem_r81_kss2 : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₄.length + 1) 32)).2 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
theorem mem_x81_0 : DY.DiffieHellman.dhPk (randTerm 0 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_0
theorem mem_x81_5 : DY.DiffieHellman.dhPk (randTerm 5 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_5
theorem mem_x81_10 : DY.DiffieHellman.dhPk (randTerm 10 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_10
theorem mem_x81_ek1 : DY.DiffieHellman.dhPk (randTerm tr₁.length 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_ek
theorem mem_x81_dhs1 : DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_dhs
theorem mem_x81_ag1 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm 0 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_ag1
theorem mem_x81_ag1_2 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr₁.length 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_ag2
theorem mem_x81_ag1_3 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr₁.length 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_ag3
theorem mem_x81_ag1_4 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm (tr₁.length + 2) 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_left _ mem_x40_ag4
theorem mem_x81_bob : DY.DiffieHellman.dhPk (randTerm tr_bob.length 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_right (xTerms40 tr₁) (.head _)
theorem mem_x81_ek2 : DY.DiffieHellman.dhPk (randTerm tr₄.length 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_right (xTerms40 tr₁) (.tail _ (.head _))
theorem mem_x81_dhs2 : DY.DiffieHellman.dhPk (randTerm (tr₄.length + 2) 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_right (xTerms40 tr₁) (.tail _ (.tail _ (.head _)))
theorem mem_x81_ag_bob : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (randTerm tr_bob.length 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_right (xTerms40 tr₁) (.tail _ (.tail _ (.tail _ (.head _))))
theorem mem_x81_ag2_2 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr₄.length 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_right (xTerms40 tr₁) (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
theorem mem_x81_ag2_3 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr₄.length 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_right (xTerms40 tr₁) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
theorem mem_x81_ag2_4 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm (tr₄.length + 2) 32) ∈ xTerms81 tr₁ tr_bob tr₄ := List.mem_append_right (xTerms40 tr₁) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
theorem mem_t8_81_mac1 : Census443Defs.encMac tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2) ∈ t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := .head _
theorem mem_t8_81_mac2 : Census443Defs.encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2) ∈ t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := .tail _ (.head _)
theorem mem_t8_81_mac5 : Census443Defs.encMac tr₅ (stA2_81 r tr₄) cl₅ (tr₅.length + 2) ∈ t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := .tail _ (.tail _ (.head _))
end TableMems
theorem nrcensusW_storedSecrets_81 {w : PQXDHSpqrSetup} {r : Records} {ms : List Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfitsP : compFitsPinned w compI0 r) (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ u := nrcensusW_storedSecrets_of_mem hfitsP hc hns hreach (fun _ => mem_allTerms81_of_r) mem_r81_0 mem_r81_5 mem_r81_10 mem_r81_16
theorem nrcensusW_aliceOut81_of_mem {r : Records} (hNe : r.alice ≠ r.bob)
    {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ tr_a : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
    (hent : (gamma compI0 S g (randTerm (tr_a.length + 1) 32)).length = 32)
    (hm_ek : randTerm tr_a.length 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
    (hm_ent : randTerm (tr_a.length + 1) 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
    (hm_kct : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr_a.length + 1) 32)).1 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
    (hm_kss : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr_a.length + 1) 32)).2 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
    (hx_ek : DY.DiffieHellman.dhPk (randTerm tr_a.length 32) ∈ xTerms81 tr₁ tr_bob tr₄)
    (hx_ag2 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr_a.length 32) ∈ xTerms81 tr₁ tr_bob tr₄)
    (hx_ag3 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr_a.length 32) ∈ xTerms81 tr₁ tr_bob tr₄) :
    let o := o40 r tr_a
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ikA ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ikB ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.spk ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ek ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ct ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.rk ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.ck ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.pqr :=
  nrcensusW_aliceOut_of_mem hNe hent (fun _ => mem_allTerms81_of_r)
    mem_r81_0 mem_r81_5 mem_r81_10 mem_r81_16 hm_ek hm_ent hm_kct hm_kss
    (mem_allTerms81_of_x mem_x81_0) (mem_allTerms81_of_x mem_x81_5)
    (mem_allTerms81_of_x mem_x81_10) (mem_allTerms81_of_x hx_ek)
    (mem_allTerms81_of_x mem_x81_ag1) (mem_allTerms81_of_x hx_ag2) (mem_allTerms81_of_x hx_ag3)
theorem nrcensusW_aliceOut1_81 {r : Records} (hNe : r.alice ≠ r.bob)
    (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat)
    (hent₁ : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) :
    let o := o1_81 r tr₁
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ikA ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ikB ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.spk ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ek ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ct ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.rk ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.ck ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.pqr :=
  nrcensusW_aliceOut81_of_mem hNe hent₁ mem_r81_ek1 mem_r81_ent1 mem_r81_kct1 mem_r81_kss1 mem_x81_ek1 mem_x81_ag1_2 mem_x81_ag1_3
theorem nrcensusW_aliceOut2_81 {r : Records} (hNe : r.alice ≠ r.bob)
    (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat)
    (hent₂ : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32) :
    let o := o2_81 r tr₄
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ikA ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ikB ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.spk ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ek ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.ct ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.rk ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.ck ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ o.keys.pqr :=
  nrcensusW_aliceOut81_of_mem hNe hent₂ mem_r81_ek2 mem_r81_ent2 mem_r81_kct2 mem_r81_kss2 mem_x81_ek2 mem_x81_ag2_2 mem_x81_ag2_3
theorem trStateNRC_stA1_81 {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (hent₁ : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : TRStateNRC (allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) S g (stA1_81 r tr₁) := by
  obtain ⟨hikA, hikB, hspk, _, _, hrk, hck, hpqr⟩ :=
    nrcensusW_aliceOut1_81 (S := S) (g := g) hNe tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₁
  have hdhsA : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (randTerm (tr₁.length + 2) 32) := nrcensusW_randTerm81 mem_r81_dhs1
  exact trStateNRC_iniAliceStartState (Or.inr hB) hikA hikB hspk hrk hck hpqr (o40_ikA_length r tr₁) (o40_ikB_length hNe tr₁) (o40_rk_length r tr₁) (o40_ck_not_kdfFree r tr₁) (o40_ck_length r tr₁) hdhsA (mem_allTerms81_of_x mem_x81_dhs1) (nrcensusW_createChain_spk (o40_spk_eq hNe tr₁) (mem_allTerms81_of_x mem_x81_ag1_4) (mem_allTerms81_of_x mem_x81_dhs1) hrk hspk hdhsA)
theorem trStateNRC_stA2_81 {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (hent₂ : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32) : TRStateNRC (allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) S g (stA2_81 r tr₄) := by
  obtain ⟨hikA, hikB, hspk, _, _, hrk, hck, hpqr⟩ :=
    nrcensusW_aliceOut2_81 (S := S) (g := g) hNe tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₂
  have hdhsA : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (randTerm (tr₄.length + 2) 32) := nrcensusW_randTerm81 mem_r81_dhs2
  exact trStateNRC_iniAliceStartState (Or.inr hB) hikA hikB hspk hrk hck hpqr (o40_ikA_length r tr₄) (o40_ikB_length hNe tr₄) (o40_rk_length r tr₄) (o40_ck_not_kdfFree r tr₄) (o40_ck_length r tr₄) hdhsA (mem_allTerms81_of_x mem_x81_dhs2) (nrcensusW_createChain_spk (o40_spk_eq hNe tr₄) (mem_allTerms81_of_x mem_x81_ag2_4) (mem_allTerms81_of_x mem_x81_dhs2) hrk hspk hdhsA)
theorem nrcensusW_spqrRecv_state {allT rT : List DY.Bytes} {st msg : DY.Bytes} {idx : UInt32} {st' : DY.Bytes} (hst : FnCensusW allT rT S g st) (hm : FnCensusW allT rT S g msg) (h : (DY.Spqr.spqrRecv st msg idx).map Prod.fst = some st') : FnCensusW allT rT S g st' := by
  unfold DY.Spqr.spqrRecv at h; split at h
  · cases h
  · cases hv : st.view? DY.Spqr.InitState.SubF with
    | none => rw [hv] at h; injection h with h'; subst h'; exact memoOK_spqrRecvState_pack hst hm
    | some x =>
      rw [hv] at h; rcases x with ⟨authKey, params⟩; dsimp only at h
      cases hd : DY.Spqr.spqrParamsDir? params with
      | none => rw [hd] at h; cases h
      | some dir => rw [hd] at h; injection h with h'; subst h'; exact memoOK_spqrRecvState_pack hst hm
theorem nrcensusW_chainKeyAt {allT rT : List DY.Bytes} :
    ∀ (steps : Nat) {ck : DY.Bytes}, FnCensusW allT rT S g ck → FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.chainKeyAt ck steps)
  | 0, _, hck => hck
  | steps + 1, _, hck => nrcensusW_chainKeyAt steps (nrcensusW_kdfCk hck).1
theorem trStateNRC_bobSt81 {r : Records} (hNe : r.alice ≠ r.bob) (hA : r.alice = "alice") {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hent₁ : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) {spqrMsgIdx₂ : UInt32} {spqr₂' : DY.Bytes} (hrecv : (DY.Spqr.spqrRecv (DY.Spqr.spqrInit (o1_81 r tr₁).keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend (stA40 r tr₁ tr₂ cl₁).spqr (randTerm (tr₃.length + 1) cl₂)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂') : TRStateNRC (allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) S g (bobSt81 r (o1_81 r tr₁) tr_bob (DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs) spqr₂' 1) := by
  obtain ⟨_, hikB, _, _, _, hrk₁, _, hpqr₁⟩ :=
    nrcensusW_aliceOut1_81 (S := S) (g := g) hNe tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₁
  have hpub0_eq := CompSetupSecrecy.setupPublic_0 hNe; have hpub0 : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (setupPublic r 0) := hpub0_eq ▸ nrcensusW_dhPk81 mem_x81_0 (nrcensusW_randTerm81 mem_r81_0)
  have hpub0L : (gamma compI0 S g (setupPublic r 0)).length = 32 := by rw [hpub0_eq]; exact CompFreshDistinct.gamma_dhPk_length S g _
  have hpub2L : (gamma compI0 S g (setupPublic r 2)).length = 32 := o40_ikB_length hNe tr₁; have hdhsA_eq : (stA1_81 r tr₁).dhs = randTerm (tr₁.length + 2) 32 := rfl; have hdhsA : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (randTerm (tr₁.length + 2) 32) := nrcensusW_randTerm81 mem_r81_dhs1; have hpkA := nrcensusW_dhPk81 mem_x81_dhs1 hdhsA; have h10 : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (randTerm 10 32) := nrcensusW_randTerm81 mem_r81_10
  have hdhsB : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (randTerm tr_bob.length 32) := nrcensusW_randTerm81 mem_r81_bob
  have hcc1 : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (DY.Libsignal.TripleRatchet.createChain (o1_81 r tr₁).keys.rk (DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs) (setupSecret r 2)).1 ∧ FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (DY.Libsignal.TripleRatchet.createChain (o1_81 r tr₁).keys.rk (DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs) (setupSecret r 2)).2 := by
    rw [CompSetupSecrecy.setupSecret_2 hNe, hdhsA_eq]
    refine nrcensusW_createChain_dhPk ?_ (mem_allTerms81_of_x mem_x81_10) hrk₁ hpkA h10
    rw [agree_dhPk_comm]; exact mem_allTerms81_of_x mem_x81_ag1_4
  let rk1 := (DY.Libsignal.TripleRatchet.createChain (o1_81 r tr₁).keys.rk (DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs) (setupSecret r 2)).1
  let ck1 := (DY.Libsignal.TripleRatchet.createChain (o1_81 r tr₁).keys.rk (DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs) (setupSecret r 2)).2
  have hcc2 : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (DY.Libsignal.TripleRatchet.createChain rk1 (DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs) (randTerm tr_bob.length 32)).1 ∧ FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (DY.Libsignal.TripleRatchet.createChain rk1 (DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs) (randTerm tr_bob.length 32)).2 := by rw [hdhsA_eq]; exact nrcensusW_createChain_dhPk (mem_allTerms81_of_x mem_x81_ag_bob) (mem_allTerms81_of_x mem_x81_bob) hcc1.1 hpkA hdhsB
  have hck_step := (nrcensusW_kdfCk (nrcensusW_chainKeyAt (1 : UInt32).toNat hcc1.2)).1
  have hrecv_ser := nrcensusW_serialize_recv2 (rk := DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs)
    (ck := (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt ck1 (1 : UInt32).toNat)).1)
    (hdhsA_eq ▸ hpkA) hck_step (not_kdfFree_kdfExtract _ _) (CompFreshDistinct.gamma_hmac_length S g _ _)
  have hstA₁'_spqr := memoOK_spqrSendState (memoOK_spqrInit hpqr₁ nrcensusW_spqrA2B) (nrcensusW_randTerm_coin mem_r81_c1 (fun _ => mem_allTerms81_of_r)); have hspqr₂ := nrcensusW_spqrRecv_state (memoOK_spqrInit hpqr₁ nrcensusW_spqrB2A) (memoOK_spqrSendMsg hstA₁'_spqr (nrcensusW_randTerm_coin mem_r81_c2 (fun _ => mem_allTerms81_of_r))) hrecv
  have hsid : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (DY.Concat.concat (DY.X25519.x25519Key (DY.DiffieHellman.dhPk (stA1_81 r tr₁).dhs)) (o1_81 r tr₁).keys.rk) := by rw [hdhsA_eq, CompPlant.x25519Key_dhPk]; exact nrcensusW_concat (not_rvW_of_x25519_append (gamma_mem_x25519Vals_of_isX (Or.inl ⟨_, rfl⟩)) (o40_rk_length r tr₁)) hpkA hrk₁
  exact {
    peer := Or.inl hA, myIk := nrcensusW_serializedIk hpub2L hikB, peerIk := nrcensusW_serializedIk hpub0L hpub0
    rk := hcc2.1, dhs := hdhsB, cks := hcc2.2, sid := hsid, spqr := hspqr₂, recv := hrecv_ser.1, recvT := Or.inr hrecv_ser.2
    myIkL := gamma_serializedIk_length hpub2L, peerIkL := gamma_serializedIk_length hpub0L
    ns_val := Or.inl rfl, pn_val := rfl }
theorem nrcensusW_enc81 {r : Records} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ tr : ExecTrace}
    {cl₁ cl₂ cl₅ cl : Nat} {stA : DY.Libsignal.TripleRatchet.TRState}
    (hst : TRStateNRC (allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) S g stA)
    (hdhs_pk : DY.DiffieHellman.dhPk stA.dhs ∈ xTerms81 tr₁ tr_bob tr₄)
    (hc : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (randTerm (tr.length + 1) cl))
    (hpt : randTerm tr.length 32 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
    (hct_mem : DY.SymEnc.symEnc (keys40 tr stA cl).cipherKey (keys40 tr stA cl).iv (randTerm tr.length 32) ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
    (hmac_mem : Census443Defs.encMac tr stA cl (tr.length + 2) ∈ t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅)
    (hwL : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr stA cl (tr.length + 2))).length)
    (hwU : (gamma compI0 S g (Census443Defs.encWire tr stA cl (tr.length + 2))).length ≤ 1400) :
    let pq := tr.length + 2
    let akeys := keys40 tr stA cl
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (Census443Defs.encWire tr stA cl pq) ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (Census443Defs.encOut tr stA cl pq) ∧
    FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (Census443Defs.encMac tr stA cl pq) ∧
    (FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ akeys.cipherKey ∧ FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ akeys.macKey ∧
     FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ akeys.iv) :=
  nrcensusW_enc_of_mem hst (mem_allTerms81_of_x hdhs_pk) hc (nrcensusW_randTerm81 hpt) (mem_allTerms81_of_r hct_mem) hct_mem (mem_allTerms81_of_t8 hmac_mem) hwL hwU
theorem nrcensusW_prefixAtom_81 {r : Records} (hNe : r.alice ≠ r.bob) (hA : r.alice = "alice") (hB : r.bob = "bob") {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hent₁ : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) (hent₂ : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32) (hwL₁ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_81 r tr₁) cl₁ (tr₂.length + 2))).length) (hwU₁ : (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_81 r tr₁) cl₁ (tr₂.length + 2))).length ≤ 1400) (hwL₂ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length) (hwU₂ : (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ≤ 1400) (hwL₅ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₅ (stA2_81 r tr₄) cl₅ (tr₅.length + 2))).length) (hwU₅ : (gamma compI0 S g (Census443Defs.encWire tr₅ (stA2_81 r tr₄) cl₅ (tr₅.length + 2))).length ≤ 1400) {u : DY.Bytes} (hu : Split81PrefixAtomAt r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ u) : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ u := by
  have hst1 := trStateNRC_stA1_81 (S := S) (g := g) hNe hB tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₁
  have hst40 : TRStateNRC (allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
      (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) S g (stA40 r tr₁ tr₂ cl₁) :=
    trStateNRC_encSt (tr := tr₂) (Or.inl rfl) hst1 (nrcensusW_randTerm_coin mem_r81_c1 (fun _ => mem_allTerms81_of_r))
  have hst2 := trStateNRC_stA2_81 (S := S) (g := g) hNe hB tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₂
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | ⟨spqrMsgIdx₂, spqr₂', hrecv, rfl⟩
  · exact (nrcensusW_aliceOut1_81 hNe tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₁).2.2.2.1
  · exact (nrcensusW_aliceOut1_81 hNe tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₁).2.2.2.2.1
  · exact (nrcensusW_enc81 hst1 mem_x81_dhs1 (nrcensusW_randTerm_coin mem_r81_c1 (fun _ => mem_allTerms81_of_r)) mem_r81_pt1 mem_r81_ct1 mem_t8_81_mac1 hwL₁ hwU₁).2.1
  · exact (nrcensusW_enc81 hst40 mem_x81_dhs1 (nrcensusW_randTerm_coin mem_r81_c2 (fun _ => mem_allTerms81_of_r)) mem_r81_pt2 mem_r81_ct2 mem_t8_81_mac2 hwL₂ hwU₂).2.1
  · exact (nrcensusW_aliceOut2_81 hNe tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₂).2.2.2.1
  · exact (nrcensusW_aliceOut2_81 hNe tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ hent₂).2.2.2.2.1
  · exact (nrcensusW_enc81 hst2 mem_x81_dhs2 (nrcensusW_randTerm_coin mem_r81_c5 (fun _ => mem_allTerms81_of_r)) mem_r81_pt5 mem_r81_ct5 mem_t8_81_mac5 hwL₅ hwU₅).2.1
  · exact nrcensusW_randTerm81 mem_r81_pt1
  · exact nrcensusW_randTerm81 mem_r81_pt2
  · exact nrcensusW_randTerm81 mem_r81_pt5
  · exact nrcensusW_serAlice hA hst1
  · exact nrcensusW_serAlice hA hst40
  · exact nrcensusW_serAlice hA (trStateNRC_encSt (tr := tr₃) (Or.inr rfl) hst40 (nrcensusW_randTerm_coin mem_r81_c2 (fun _ => mem_allTerms81_of_r)))
  · exact nrcensusW_serAlice hA hst2
  · exact nrcensusW_serAlice hA (trStateNRC_encSt (tr := tr₅) (Or.inl rfl) hst2 (nrcensusW_randTerm_coin mem_r81_c5 (fun _ => mem_allTerms81_of_r)))
  · exact nrcensusW_serialize_local_tr (ls := ⟨r.bob, _⟩) (Or.inr hB) (trStateNRC_bobSt81 hNe hA hent₁ hrecv)
theorem split81RestFnPreOwn : Split81RestFnPreOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; obtain ⟨hwL₁_raw, hwU₁, hwL₂, hwU₂, hwL₅_raw, hwU₅⟩ := split81_wire_bounds hp hinv; have hwL₁ : 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_81 r tr₁) cl₁ (tr₂.length + 2))).length := hwL₁_raw; have hwL₅ : 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₅ (stA2_81 r tr₄) cl₅ (tr₅.length + 2))).length := hwL₅_raw
  obtain ⟨tr_bob, hbob, henum⟩ := split81PrefixEnumAt hinv hown
  refine ⟨tr_bob, hbob, fun x hx => ?_⟩
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hA : r.alice = "alice" := CompFitsNames.compFits_alice hfits; have hB : r.bob = "bob" := CompFitsNames.compFits_bob hfits
  have hent₁L : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [hinv.hent₁]; decide +kernel
  have hent₂L : (gamma compI0 S g (randTerm (tr₄.length + 1) 32)).length = 32 := by rw [hinv.hent₂]; decide +kernel
  have hR : ∀ v, Rv81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ v → RvW v :=
    fun _ hv => rv81_mem_rVals81 hfits hp hinv hown hbob hv
  obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  refine fnCensus81_of_W hR ?_ x hxu
  rcases henum u hu with hatom | hsec
  · exact nrcensusW_prefixAtom_81 hNe hA hB hent₁L hent₂L (by omega) hwU₁ (by omega) hwU₂ (by omega) hwU₅ hatom
  · exact nrcensusW_storedSecrets_81 hfits hinv.compat hinv.mp.2.1.2.1 hinv.reach u hsec
end NRSt
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnSt
