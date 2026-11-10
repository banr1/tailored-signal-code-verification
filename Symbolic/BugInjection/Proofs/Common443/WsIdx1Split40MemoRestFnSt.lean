/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnStA
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnSt
open CryptoProofLib.Refinement (ExternInterpretation)
open ByteSpecs DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnStA Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire Symbolic.BugInjection.Proofs.Common443.CompRX0Top Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZTag Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZVals Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ Symbolic.BugInjection.Proofs.Common443.CompC2RestCore Symbolic.BugInjection.Proofs.Common443.CompC2Rest38 Symbolic.BugInjection.Proofs.Common443.CompC2RestFn Symbolic.BugInjection.Proofs.Common443.CompRWSBobChain Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38
open Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA (KdfTail6 gamma_literalToBytes_eq gamma_agree_mem_x25519Vals gamma_serializedIk_length)
open Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HB (gamma_setup_len gamma_kemEncap_snd_length' aliceOut_ck_length aliceOut_ck_not_kdfFree gamma_agree_length)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
section NRSt
open Symbolic.BugInjection.Proofs.Common443.CompExcuse (trStatePrefixes)
variable {S : Sem} {g : Ghost}
section TableMems
variable {r : Records} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat}
theorem mem_r40_0 : randTerm 0 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.head _))
theorem mem_r40_5 : randTerm 5 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.head _)))
theorem mem_r40_10 : randTerm 10 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.head _))))
theorem mem_r40_16 : randTerm 16 64 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _)))))
theorem mem_r40_ek : randTerm tr₁.length 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
theorem mem_r40_ent : randTerm (tr₁.length + 1) 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
theorem mem_r40_dhs : randTerm (tr₁.length + 2) 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
theorem mem_r40_pt1 : randTerm tr₂.length 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
theorem mem_r40_c1 (h : cl₁ ≠ 0) : randTerm (tr₂.length + 1) cl₁ ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_right _ (by simp [coinTerms, h]))
theorem mem_r40_c2 (h : cl₂ ≠ 0) : randTerm (tr₃.length + 1) cl₂ ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_right _ (by simp [coinTerms, h])
theorem mem_r40_pt2 : randTerm tr₃.length 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))
theorem mem_r40_ct1 : DY.SymEnc.symEnc (keys40 tr₂ (stA1_40 r tr₁) cl₁).cipherKey (keys40 tr₂ (stA1_40 r tr₁) cl₁).iv (randTerm tr₂.length 32) ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))
theorem mem_r40_ct2 : DY.SymEnc.symEnc (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).cipherKey (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).iv (randTerm tr₃.length 32) ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
theorem mem_r40_kct : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).1 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))
theorem mem_r40_kss : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))
theorem mem_x40_0 : DY.DiffieHellman.dhPk (randTerm 0 32) ∈ xTerms40 tr₁ := .head _
theorem mem_x40_5 : DY.DiffieHellman.dhPk (randTerm 5 32) ∈ xTerms40 tr₁ := .tail _ (.head _)
theorem mem_x40_10 : DY.DiffieHellman.dhPk (randTerm 10 32) ∈ xTerms40 tr₁ := .tail _ (.tail _ (.head _))
theorem mem_x40_ek : DY.DiffieHellman.dhPk (randTerm tr₁.length 32) ∈ xTerms40 tr₁ := .tail _ (.tail _ (.tail _ (.head _)))
theorem mem_x40_dhs : DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32) ∈ xTerms40 tr₁ := .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
theorem mem_x40_ag1 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm 0 32) ∈ xTerms40 tr₁ := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
theorem mem_x40_ag2 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr₁.length 32) ∈ xTerms40 tr₁ := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
theorem mem_x40_ag3 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr₁.length 32) ∈ xTerms40 tr₁ := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
theorem mem_x40_ag4 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm (tr₁.length + 2) 32) ∈ xTerms40 tr₁ := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
theorem mem_t8_mac1 : Census443Defs.encMac tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2) ∈ t8Terms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := .head _
theorem mem_t8_mac2 : Census443Defs.encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2) ∈ t8Terms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := .tail _ (.head _)
end TableMems
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStAb ( TRStateNRC nrcensusW_mem_trStatePrefixes nrcensusW_serialize_local_tr)
theorem nrcensusW_storedSecrets_of_mem {allT rT : List DY.Bytes} {w : PQXDHSpqrSetup} {r : Records} {ms : List Move} (hfitsP : compFitsPinned w compI0 r) (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) (hr_sub : ∀ u ∈ rT, u ∈ allT) (h0 : randTerm 0 32 ∈ rT) (h5 : randTerm 5 32 ∈ rT) (h10 : randTerm 10 32 ∈ rT) (h16 : randTerm 16 64 ∈ rT) : ∀ u ∈ storedSecrets (runTraceMoves r ms), FnCensusW allT rT S g u := by
  have hfits : compFits w compI0 r := CompFitsNames.compFits_base hfitsP; have hNe : r.alice ≠ r.bob := hfits.1.1; have hwf : RecordsWF r := hfits.1; have hA : r.alice = "alice" := CompFitsNames.compFits_alice hfitsP; have hB : r.bob = "bob" := CompFitsNames.compFits_bob hfitsP; have hinv := CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach; intro u hu; obtain ⟨j, _, ⟨part, kind, sk⟩, hat, rfl⟩ := CompRX0NBSC38Parts.mem_storedSecrets_iff.mp hu
  have hkind : CompInv.KindOK (runTraceMoves r ms) part ⟨kind, sk⟩ := hinv.stOK part ⟨kind, sk⟩ j hat; dsimp only [CompInv.KindOK] at hkind
  have h32 {idx : Nat} (hr : randTerm idx 32 ∈ rT) (hs : (idx, 32) ∈ setupRandomsAt r) : FnCensusW allT rT S g (randTerm idx 32) ∧
        ((gamma compI0 S g (randTerm idx 32)).length = 32 ∨ (gamma compI0 S g (randTerm idx 32)).length = 64) :=
    ⟨nrcensusW_randTerm (hr_sub _ hr) hr, Or.inl (gamma_setup_len hc hwf hs (by decide))⟩
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hNe hns hkind with ⟨hp, rfl, _⟩ | ⟨hp, rfl, _⟩
    · have ⟨h1, h2⟩ := h32 h0 (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inl rfl)))
      refine nrcensusW_serialize_local_pqxdh (Or.inl (hp.trans hA)) ?_ ?_ <;>
        dsimp only <;> rw [CompSetupSecrecy.setupSecret_0 hNe] <;> [exact h1; exact h2]
    · have ⟨h1, h2⟩ := h32 h5 (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inr (.inl rfl))))
      refine nrcensusW_serialize_local_pqxdh (Or.inr (hp.trans hB)) ?_ ?_ <;>
        dsimp only <;> rw [CompSetupSecrecy.setupSecret_1 hNe] <;> [exact h1; exact h2]
  | signedPrekey =>
    obtain ⟨hp, rfl, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hNe hns hkind; have ⟨h1, h2⟩ := h32 h10 (CompPrefixInvFresh.mem_setupRandomsAt_32 hNe (.inl (.inr (.inr rfl))))
    refine nrcensusW_serialize_local_pqxdh (Or.inr (hp.trans hB)) ?_ ?_ <;>
      dsimp only <;> rw [CompSetupSecrecy.setupSecret_2 hNe] <;> [exact h1; exact h2]
  | pqPrekey =>
    obtain ⟨hp, rfl, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hNe hns hkind
    refine nrcensusW_serialize_local_pqxdh (Or.inr (hp.trans hB)) ?_ ?_ <;>
      dsimp only <;> rw [CompSetupSecrecy.setupSecret_4 hNe]
    · exact nrcensusW_randTerm (hr_sub _ h16) h16
    · exact Or.inr (gamma_setup_len hc hwf (CompPrefixInvFresh.mem_setupRandomsAt_64 r hNe (by simp)) (by decide))
  | oneTimePrekey =>
    obtain ⟨t, rfl, _, hev⟩ := hkind; have h0' := CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hNe h0' with
      ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨hopk_true, _, _⟩
    · cases heq
    · cases heq
    · cases heq
    · cases heq
    · rw [hfits.2.1] at hopk_true; cases hopk_true
theorem nrcensusW_storedSecrets_40 {w : PQXDHSpqrSetup} {r : Records} {ms : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfitsP : compFitsPinned w compI0 r) (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ u := nrcensusW_storedSecrets_of_mem hfitsP hc hns hreach (fun _ => mem_allTerms40_of_r) mem_r40_0 mem_r40_5 mem_r40_10 mem_r40_16
theorem nrcensusW_aliceOut_of_mem {allT rT : List DY.Bytes} {r : Records} (hNe : r.alice ≠ r.bob) {tr_a : ExecTrace}
    (hent : (gamma compI0 S g (randTerm (tr_a.length + 1) 32)).length = 32) (hr_sub : ∀ u ∈ rT, u ∈ allT)
    (h0 : randTerm 0 32 ∈ rT) (h5 : randTerm 5 32 ∈ rT) (h10 : randTerm 10 32 ∈ rT) (h16 : randTerm 16 64 ∈ rT)
    (hm_ek : randTerm tr_a.length 32 ∈ rT) (hm_ent : randTerm (tr_a.length + 1) 32 ∈ rT)
    (hm_kct : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr_a.length + 1) 32)).1 ∈ rT)
    (hm_kss : (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr_a.length + 1) 32)).2 ∈ rT)
    (hx_0 : DY.DiffieHellman.dhPk (randTerm 0 32) ∈ allT) (hx_5 : DY.DiffieHellman.dhPk (randTerm 5 32) ∈ allT)
    (hx_10 : DY.DiffieHellman.dhPk (randTerm 10 32) ∈ allT) (hx_ek : DY.DiffieHellman.dhPk (randTerm tr_a.length 32) ∈ allT)
    (hx_ag1 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm 0 32) ∈ allT)
    (hx_ag2 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr_a.length 32) ∈ allT)
    (hx_ag3 : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr_a.length 32) ∈ allT) :
    let o := o40 r tr_a
    FnCensusW allT rT S g o.ikA ∧ FnCensusW allT rT S g o.ikB ∧ FnCensusW allT rT S g o.spk ∧
    FnCensusW allT rT S g o.ek ∧ FnCensusW allT rT S g o.ct ∧ FnCensusW allT rT S g o.keys.rk ∧
    FnCensusW allT rT S g o.keys.ck ∧ FnCensusW allT rT S g o.keys.pqr := by
  dsimp only [o40, Census443Defs.iniAliceOut]
  rw [CompSetupSecrecy.setupSecret_0 hNe, CompSetupSecrecy.setupPublic_2 hNe, CompSetupSecrecy.setupPublic_4 hNe, CompSetupSecrecy.setupPublic_6 hNe]
  have hsec0 := nrcensusW_randTerm (S := S) (g := g) (hr_sub _ h0) h0
  have hpub2 := nrcensusW_dhPk (S := S) (g := g) hx_5 (nrcensusW_randTerm (hr_sub _ h5) h5)
  have hpub4 := nrcensusW_dhPk (S := S) (g := g) hx_10 (nrcensusW_randTerm (hr_sub _ h10) h10)
  have hpub6 := memoOK_kemPk (nrcensusW_randTerm (S := S) (g := g) (hr_sub _ h16) h16)
  have hek_r := nrcensusW_randTerm (S := S) (g := g) (hr_sub _ hm_ek) hm_ek
  have hent_r := nrcensusW_randTerm (S := S) (g := g) (hr_sub _ hm_ent) hm_ent
  rcases nrcensusW_pqxdhKdf_none (gamma_agree_length _ _) (gamma_agree_length _ _) (gamma_agree_length _ _) (gamma_kemEncap_snd_length' hent) (gamma_agree_mem_x25519Vals _ _) (nrcensusW_agree_dhPk hx_ag1 hx_0 hpub4 hsec0) (nrcensusW_agree_dhPk hx_ag2 hx_ek hpub2 hek_r) (nrcensusW_agree_dhPk hx_ag3 hx_ek hpub4 hek_r)
    (memoOK_kemEncap_snd (fun _ hx => fnokW_of_r ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by rw [Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.kemEncap_snd_eq_pack]; simp [DY.BytesView.view_pack])) (hr_sub _ hm_kss) hm_kss hx) hpub6 hent_r)
    with ⟨hrk, hck, hpqr⟩
  exact ⟨nrcensusW_dhPk hx_0 hsec0, hpub2, hpub4, nrcensusW_dhPk hx_ek hek_r,
    memoOK_kemEncap_fst (fun _ hx => fnokW_of_r ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by rw [Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.kemEncap_fst_eq_pack]; simp [DY.BytesView.view_pack])) (hr_sub _ hm_kct) hm_kct hx) hpub6 hent_r,
    hrk, hck, hpqr⟩
theorem nrcensusW_aliceOut40 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat)
    (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) :
    let o := o40 r tr₁
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ o.ikA ∧ FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ o.ikB ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ o.spk ∧ FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ o.ek ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ o.ct ∧ FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ o.keys.rk ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ o.keys.ck ∧ FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ o.keys.pqr :=
  nrcensusW_aliceOut_of_mem hNe hent (fun _ => mem_allTerms40_of_r)
    mem_r40_0 mem_r40_5 mem_r40_10 mem_r40_16 mem_r40_ek mem_r40_ent mem_r40_kct mem_r40_kss
    (mem_allTerms40_of_x mem_x40_0) (mem_allTerms40_of_x mem_x40_5)
    (mem_allTerms40_of_x mem_x40_10) (mem_allTerms40_of_x mem_x40_ek)
    (mem_allTerms40_of_x mem_x40_ag1) (mem_allTerms40_of_x mem_x40_ag2) (mem_allTerms40_of_x mem_x40_ag3)
theorem nrcensusW_createChain_spk {allT rT : List DY.Bytes} {rk spk dhs : DY.Bytes} (hspk_eq : spk = DY.DiffieHellman.dhPk (randTerm 10 32)) (hag : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) dhs ∈ allT) (hpk_sk : DY.DiffieHellman.dhPk dhs ∈ allT) (hrk : FnCensusW allT rT S g rk) (hspk : FnCensusW allT rT S g spk) (hdhs : FnCensusW allT rT S g dhs) : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.createChain rk spk dhs).1 ∧ FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.createChain rk spk dhs).2 := by subst hspk_eq; exact nrcensusW_createChain_dhPk hag hpk_sk hrk hspk hdhs
theorem gamma_setupPublic_2_length {r : Records} (hNe : r.alice ≠ r.bob) : (gamma compI0 S g (setupPublic r 2)).length = 32 := by rw [CompSetupSecrecy.setupPublic_2 hNe]; exact CompFreshDistinct.gamma_dhPk_length S g _
theorem o40_spk_eq {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) : (o40 r tr₁).spk = DY.DiffieHellman.dhPk (randTerm 10 32) := CompSetupSecrecy.setupPublic_4 hNe
theorem o40_ikA_length (r : Records) (tr₁ : ExecTrace) : (gamma compI0 S g (o40 r tr₁).ikA).length = 32 := CompFreshDistinct.gamma_dhPk_length S g (setupSecret r 0)
theorem o40_ikB_length {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) : (gamma compI0 S g (o40 r tr₁).ikB).length = 32 := gamma_setupPublic_2_length hNe
private theorem census_iniAliceOut_eq : @Census443Defs.iniAliceOut = @CompPrefixInvAlice.iniAliceOut := rfl
theorem o40_rk_length (r : Records) (tr₁ : ExecTrace) : (gamma compI0 S g (o40 r tr₁).keys.rk).length = 32 := by unfold o40; rw [census_iniAliceOut_eq]; exact CompRPreMemo38KdfCensus.aliceOut_rk_length tr₁ _ _ _ _ _
theorem o40_ck_not_kdfFree (r : Records) (tr₁ : ExecTrace) : ¬ KdfFree (gamma compI0 S g (o40 r tr₁).keys.ck) := by unfold o40; rw [census_iniAliceOut_eq]; exact aliceOut_ck_not_kdfFree tr₁ _ _ _ _ _
theorem o40_ck_length (r : Records) (tr₁ : ExecTrace) : (gamma compI0 S g (o40 r tr₁).keys.ck).length = 32 := by unfold o40; rw [census_iniAliceOut_eq]; exact aliceOut_ck_length tr₁ _ _ _ _ _
theorem trStateNRC_iniAliceStartState {allT rT : List DY.Bytes} {tr₁ : ExecTrace} {b : DY.Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (hb : b = "alice" ∨ b = "bob") (hikA : FnCensusW allT rT S g o.ikA) (hikB : FnCensusW allT rT S g o.ikB) (hspk : FnCensusW allT rT S g o.spk) (hrk : FnCensusW allT rT S g o.keys.rk) (hck : FnCensusW allT rT S g o.keys.ck) (hpqr : FnCensusW allT rT S g o.keys.pqr) (hikAL : (gamma compI0 S g o.ikA).length = 32) (hikBL : (gamma compI0 S g o.ikB).length = 32) (hrkL : (gamma compI0 S g o.keys.rk).length = 32) (hck_kf : ¬ KdfFree (gamma compI0 S g o.keys.ck)) (hckL : (gamma compI0 S g o.keys.ck).length = 32) (hdhsA : FnCensusW allT rT S g (randTerm (tr₁.length + 2) 32)) (hdhs_pk : DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32) ∈ allT) (hcc : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr₁.length + 2) 32)).1 ∧ FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr₁.length + 2) 32)).2) : TRStateNRC allT rT S g (Census443Defs.iniAliceStartState tr₁ b o) := by
  obtain ⟨hrecv, hrecvT⟩ := nrcensusW_serialize_recv1 (S := S) (g := g) hspk hck hck_kf hckL; have hdh_x := gamma_mem_x25519Vals_of_isX (S := S) (g := g) (u := DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (Or.inl ⟨_, rfl⟩)
  exact {
    peer := hb, myIk := nrcensusW_serializedIk hikAL hikA, peerIk := nrcensusW_serializedIk hikBL hikB
    rk := hcc.1, dhs := hdhsA, cks := hcc.2
    sid := nrcensusW_concat (not_rvW_of_x25519_append hdh_x hrkL) (nrcensusW_dhPk hdhs_pk hdhsA) hrk
    spqr := memoOK_spqrInit hpqr nrcensusW_spqrA2B, recv := hrecv, recvT := Or.inl hrecvT
    myIkL := gamma_serializedIk_length hikAL, peerIkL := gamma_serializedIk_length hikBL
    ns_val := Or.inl rfl, pn_val := rfl }
theorem trStateNRC_stA1_40 {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : TRStateNRC (allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) S g (stA1_40 r tr₁) := by
  obtain ⟨hikA, hikB, hspk, _, _, hrk, hck, hpqr⟩ := nrcensusW_aliceOut40 (S := S) (g := g) hNe tr₁ tr₂ tr₃ cl₁ cl₂ hent; have hdhsA : FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (randTerm (tr₁.length + 2) 32) := nrcensusW_randTerm40 mem_r40_dhs
  exact trStateNRC_iniAliceStartState (Or.inr hB) hikA hikB hspk hrk hck hpqr (o40_ikA_length r tr₁) (o40_ikB_length hNe tr₁) (o40_rk_length r tr₁) (o40_ck_not_kdfFree r tr₁) (o40_ck_length r tr₁) hdhsA (mem_allTerms40_of_x mem_x40_dhs) (nrcensusW_createChain_spk (o40_spk_eq hNe tr₁) (mem_allTerms40_of_x mem_x40_ag4) (mem_allTerms40_of_x mem_x40_dhs) hrk hspk hdhsA)
theorem trStateNRC_encSt {allT rT : List DY.Bytes} {tr : ExecTrace}
    {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat}
    (hns : stA.ns = 0 ∨ stA.ns = 1)
    (hst : TRStateNRC allT rT S g stA) (hc : FnCensusW allT rT S g (randTerm (tr.length + 1) cl)) :
    TRStateNRC allT rT S g (Census443Defs.encSt tr stA cl) :=
  { hst with
    cks := (nrcensusW_kdfCk hst.cks).1
    spqr := memoOK_spqrSendState hst.spqr hc
    ns_val := by
      rcases hns with h | h
      · exact Or.inr (Or.inl (by change stA.ns + 1 = 1; rw [h]; rfl))
      · exact Or.inr (Or.inr (by change stA.ns + 1 = 2; rw [h]; rfl)) }
theorem trStateNRC_stA40 {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) : TRStateNRC (allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) S g (stA40 r tr₁ tr₂ cl₁) := trStateNRC_encSt (Or.inl rfl) (trStateNRC_stA1_40 hNe hB tr₁ tr₂ tr₃ cl₁ cl₂ hent) (nrcensusW_randTerm_coin mem_r40_c1 (fun _ => mem_allTerms40_of_r))
theorem trStateNRC_encSt_zero {allT rT : List DY.Bytes} (tr : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} (hns : stA.ns = 0 ∨ stA.ns = 1) (hcl : cl = 0) (hst : TRStateNRC allT rT S g stA) : TRStateNRC allT rT S g (Census443Defs.encSt tr stA cl) := trStateNRC_encSt hns hst (hcl ▸ nrcensusW_randTerm_zero (tr.length + 1))
theorem nrcensusW_encSalt_self {allT rT : List DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} (hst : TRStateNRC allT rT S g stA) (hc : FnCensusW allT rT S g (randTerm (tr.length + 1) cl)) : FnCensusW allT rT S g (Census443Defs.encSalt tr stA cl (tr.length + 2)) := by change FnCensusW allT rT S g (CompPrefixInvEnc.encSalt tr stA cl (tr.length + 2)); rw [CompPrefixInvEnc.encSalt_self]; exact nrcensusW_spqrSendKey hst.spqr hc
theorem nrcensusW_enc_of_mem {allT rT : List DY.Bytes} {tr : ExecTrace} {cl : Nat}
    {stA : DY.Libsignal.TripleRatchet.TRState}
    (hst : TRStateNRC allT rT S g stA) (hdhs_pk : DY.DiffieHellman.dhPk stA.dhs ∈ allT)
    (hc : FnCensusW allT rT S g (randTerm (tr.length + 1) cl))
    (hpt : FnCensusW allT rT S g (randTerm tr.length 32))
    (hct_all : DY.SymEnc.symEnc (keys40 tr stA cl).cipherKey (keys40 tr stA cl).iv (randTerm tr.length 32) ∈ allT)
    (hct_mem : DY.SymEnc.symEnc (keys40 tr stA cl).cipherKey (keys40 tr stA cl).iv (randTerm tr.length 32) ∈ rT)
    (hmac_all : Census443Defs.encMac tr stA cl (tr.length + 2) ∈ allT)
    (hwL : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr stA cl (tr.length + 2))).length)
    (hwU : (gamma compI0 S g (Census443Defs.encWire tr stA cl (tr.length + 2))).length ≤ 1400) :
    let pq := tr.length + 2
    let akeys := keys40 tr stA cl
    FnCensusW allT rT S g (Census443Defs.encWire tr stA cl pq) ∧
    FnCensusW allT rT S g (Census443Defs.encOut tr stA cl pq) ∧
    FnCensusW allT rT S g (Census443Defs.encMac tr stA cl pq) ∧
    (FnCensusW allT rT S g akeys.cipherKey ∧ FnCensusW allT rT S g akeys.macKey ∧ FnCensusW allT rT S g akeys.iv) := by
  dsimp only
  have hmk := nrcensusW_trMsgKeys (nrcensusW_encSalt_self hst hc) (nrcensusW_kdfCk hst.cks).2
  have hct := nrcensusW_symEnc hct_all hct_mem hmk.1 hmk.2.2 hpt
  have hrk := nrcensusW_dhPk hdhs_pk hst.dhs
  have hwire : FnCensusW allT rT S g (Census443Defs.encWire tr stA cl (tr.length + 2)) := by
    have h1568 : (gamma compI0 S g (Census443Defs.encWire tr stA cl (tr.length + 2))).length ≠ 1568 := by omega
    unfold Census443Defs.encWire DY.Libsignal.TripleRatchet.trHonestWireMsg
    exact nrcensusW_trWire_of_len hwL h1568 hrk hct (memoOK_spqrSendMsg hst.spqr hc)
  have h1 := hst.myIkL; have h2 := hst.peerIkL
  have hmacIn : FnCensusW allT rT S g
      (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (Census443Defs.encWire tr stA cl (tr.length + 2)))) :=
    nrcensusW_concat (not_rvW_of_len_ge65
      (by rw [List.length_append, gamma_concat_eq, List.length_append]; omega)
      (by rw [List.length_append, gamma_concat_eq, List.length_append]; omega)) hst.myIk
      (nrcensusW_concat (not_rvW_of_len_ge65 (by rw [List.length_append]; omega)
        (by rw [List.length_append]; omega)) hst.peerIk hwire)
  have hmac : FnCensusW allT rT S g (Census443Defs.encMac tr stA cl (tr.length + 2)) := nrcensusW_trunc8 hmac_all (nrcensusW_hmac hmk.2.1 hmacIn)
  have h3 : (gamma compI0 S g (Census443Defs.encMac tr stA cl (tr.length + 2))).length ≤ 8 := gamma_trunc8_length_le _
  have hencOut : FnCensusW allT rT S g (Census443Defs.encOut tr stA cl (tr.length + 2)) :=
    nrcensusW_concat (not_rvW_of_len_ge65 (by rw [List.length_append]; omega)
      (by rw [List.length_append]; omega)) hwire hmac
  exact ⟨hwire, hencOut, hmac, hmk⟩
theorem nrcensusW_enc40 {r : Records} {tr₁ tr₂ tr₃ tr : ExecTrace} {cl₁ cl₂ cl : Nat}
    {stA : DY.Libsignal.TripleRatchet.TRState}
    (hst : TRStateNRC (allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) S g stA)
    (hdhs_pk : DY.DiffieHellman.dhPk stA.dhs ∈ xTerms40 tr₁)
    (hc : FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (randTerm (tr.length + 1) cl))
    (hpt : randTerm tr.length 32 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂)
    (hct_mem : DY.SymEnc.symEnc (keys40 tr stA cl).cipherKey (keys40 tr stA cl).iv (randTerm tr.length 32) ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂)
    (hmac_mem : Census443Defs.encMac tr stA cl (tr.length + 2) ∈ t8Terms40 r tr₁ tr₂ tr₃ cl₁ cl₂)
    (hwL : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr stA cl (tr.length + 2))).length)
    (hwU : (gamma compI0 S g (Census443Defs.encWire tr stA cl (tr.length + 2))).length ≤ 1400) :
    let pq := tr.length + 2
    let akeys := keys40 tr stA cl
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encWire tr stA cl pq) ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encOut tr stA cl pq) ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encMac tr stA cl pq) ∧
    (FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.cipherKey ∧ FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.macKey ∧
     FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.iv) :=
  nrcensusW_enc_of_mem hst (mem_allTerms40_of_x hdhs_pk) hc (nrcensusW_randTerm40 hpt) (mem_allTerms40_of_r hct_mem) hct_mem (mem_allTerms40_of_t8 hmac_mem) hwL hwU
theorem nrcensusW_enc_msg1 {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob")
    (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat)
    (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32)
    (hwL₁ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length)
    (hwU₁ : (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length ≤ 1400) :
    let stA := stA1_40 r tr₁
    let pq := tr₂.length + 2
    let akeys := keys40 tr₂ stA cl₁
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encWire tr₂ stA cl₁ pq) ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encOut tr₂ stA cl₁ pq) ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encMac tr₂ stA cl₁ pq) ∧
    (FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.cipherKey ∧ FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.macKey ∧
     FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.iv) :=
  nrcensusW_enc40 (trStateNRC_stA1_40 hNe hB tr₁ tr₂ tr₃ cl₁ cl₂ hent) mem_x40_dhs (nrcensusW_randTerm_coin mem_r40_c1 (fun _ => mem_allTerms40_of_r)) mem_r40_pt1 mem_r40_ct1 mem_t8_mac1 hwL₁ hwU₁
theorem nrcensusW_enc_msg2 {r : Records} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob")
    (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat)
    (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32)
    (hwL₂ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length)
    (hwU₂ : (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ≤ 1400) :
    let stA' := stA40 r tr₁ tr₂ cl₁
    let pq := tr₃.length + 2
    let akeys := keys40 tr₃ stA' cl₂
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encWire tr₃ stA' cl₂ pq) ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encOut tr₃ stA' cl₂ pq) ∧
    FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (Census443Defs.encMac tr₃ stA' cl₂ pq) ∧
    (FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.cipherKey ∧ FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.macKey ∧
     FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ akeys.iv) :=
  nrcensusW_enc40 (trStateNRC_stA40 hNe hB tr₁ tr₂ tr₃ cl₁ cl₂ hent) mem_x40_dhs (nrcensusW_randTerm_coin mem_r40_c2 (fun _ => mem_allTerms40_of_r)) mem_r40_pt2 mem_r40_ct2 mem_t8_mac2 hwL₂ hwU₂
theorem nrcensusW_serAlice {allT rT : List DY.Bytes} {r : Records}
    {st : DY.Libsignal.TripleRatchet.TRState}
    (hA : r.alice = "alice") (hst : TRStateNRC allT rT S g st) :
    FnCensusW allT rT S g (serAlice r st) :=
  nrcensusW_serialize_local_tr (ls := ⟨r.alice, st⟩) (Or.inl hA) hst
theorem split40PrefixAtom_iff (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (u : DY.Bytes) : Split40PrefixAtom r tr₁ tr₂ tr₃ cl₁ cl₂ u ↔ u = (o40 r tr₁).ek ∨ u = (o40 r tr₁).ct ∨ u = Census443Defs.encOut tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2) ∨ u = Census443Defs.encOut tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2) ∨ u = randTerm tr₂.length 32 ∨ u = randTerm tr₃.length 32 ∨ u = serAlice r (stA1_40 r tr₁) ∨ u = serAlice r (stA40 r tr₁ tr₂ cl₁) ∨ u = serAlice r (Census443Defs.encSt tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂) := Iff.rfl
theorem nrcensusW_prefixAtom_40 {r : Records} (hNe : r.alice ≠ r.bob) (hA : r.alice = "alice") (hB : r.bob = "bob") {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) (hwL₁ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length) (hwU₁ : (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length ≤ 1400) (hwL₂ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length) (hwU₂ : (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ≤ 1400) {u : DY.Bytes} (hu : Split40PrefixAtom r tr₁ tr₂ tr₃ cl₁ cl₂ u) : FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ u := by
  rcases (split40PrefixAtom_iff r tr₁ tr₂ tr₃ cl₁ cl₂ u).mp hu with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (nrcensusW_aliceOut40 hNe tr₁ tr₂ tr₃ cl₁ cl₂ hent).2.2.2.1
  · exact (nrcensusW_aliceOut40 hNe tr₁ tr₂ tr₃ cl₁ cl₂ hent).2.2.2.2.1
  · exact (nrcensusW_enc_msg1 hNe hB tr₁ tr₂ tr₃ cl₁ cl₂ hent hwL₁ hwU₁).2.1
  · exact (nrcensusW_enc_msg2 hNe hB tr₁ tr₂ tr₃ cl₁ cl₂ hent hwL₂ hwU₂).2.1
  · exact nrcensusW_randTerm40 mem_r40_pt1
  · exact nrcensusW_randTerm40 mem_r40_pt2
  · exact nrcensusW_serAlice hA (trStateNRC_stA1_40 hNe hB tr₁ tr₂ tr₃ cl₁ cl₂ hent)
  · exact nrcensusW_serAlice hA (trStateNRC_stA40 hNe hB tr₁ tr₂ tr₃ cl₁ cl₂ hent)
  · exact nrcensusW_serAlice hA (trStateNRC_encSt (tr := tr₃) (Or.inr rfl) (trStateNRC_stA40 hNe hB tr₁ tr₂ tr₃ cl₁ cl₂ hent) (nrcensusW_randTerm_coin mem_r40_c2 (fun _ => mem_allTerms40_of_r)))
theorem fnOK40_preMemo40_of_bounds {r : Records} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hown : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hwL₁ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length) (hwU₁ : (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length ≤ 1400) (hwL₂ : 65 ≤ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length) (hwU₂ : (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ≤ 1400) : ∀ x ∈ preMemo40 r S g ms', FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x := by
  have hentL : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [hinv.hent₁]; decide +kernel
  have henum := split40PrefixEnum r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; have hR := rvW_of_rv40 hfits hp hinv hown; intro x hx; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  refine fnCensus40_of_W hR ?_ x hxu
  rcases henum u hu with hatom | hsec
  · exact nrcensusW_prefixAtom_40 hfits.1.1.1 (CompFitsNames.compFits_alice hfits)
      (CompFitsNames.compFits_bob hfits) hentL hwL₁ hwU₁ hwL₂ hwU₂ hatom
  · exact nrcensusW_storedSecrets_40 hfits hinv.compat hinv.mp.2.1.2.1 hinv.reach u hsec
theorem fnOK40_preMemo40_of_pins {r : Records} {p : PreKeyFields} {ms' : List Move}
    {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat}
    (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p)
    (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hown : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂)
    (hwL₁ : 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length)
    (hwU₁ : (gamma compI0 S g (Census443Defs.encWire tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2))).length ≤ 1400)
    (hwL₂ : 69 ≤ (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length)
    (hwU₂ : (gamma compI0 S g (Census443Defs.encWire tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2))).length ≤ 1400) :
    ∀ x ∈ preMemo40 r S g ms', FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x :=
  fnOK40_preMemo40_of_bounds hfits hp hinv hown (by omega) hwU₁ (by omega) hwU₂
end NRSt
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnSt
