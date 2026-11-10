/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest
public import Symbolic.BugInjection.Proofs.Common443.CompC2RestCore
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC3KdfInjRest38HB
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPlant CompPrefixInvAlice CompPrefixInvBundle CompPrefixInvEnc CompPrefixInvFresh CompPrefixInvStruct CompPrefixInvSwap CompRMemoKnown CompRNoBSC CompRPlantWire CompRX0NBSC38 CompRX0NBSC38Hmc CompRX0NBSC38Parts CompRX0NBSC38Wire CompRX0SS38 CompRX0Top CompRTag CompRI0TermInj CompRSplit38PairCore CompRSplit38UntaggedShape CompRNonInj38Census CompC2KdfInjRest CompC2RestCore Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem hb_aliceId_kdfFree : KdfFree Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId := by decide +kernel
theorem hb_bobId_kdfFree : KdfFree Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId := by decide +kernel
theorem hb_spk_kdfFree : KdfFree Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk := by decide +kernel
theorem tc_aliceId_kdfFree : KdfFree Witnesses.Cheval26SmallSubgroupTorsionComp.setup.aliceId := by decide +kernel
theorem tc_bobId_kdfFree : KdfFree Witnesses.Cheval26SmallSubgroupTorsionComp.setup.bobId := by decide +kernel
theorem tc_spk_kdfFree : KdfFree Witnesses.Cheval26SmallSubgroupTorsionComp.setup.spk := by decide +kernel
theorem ss_b0_kdfFree : KdfFree CompRX0SS38.b0Bytes := by decide +kernel
theorem ss_e0_kdfFree : KdfFree compKyberE0 := by decide +kernel
theorem ss_dhs_kdfFree : ∀ ev ∈ CompRX0SS38.rsT.drop 32, KdfFree (CompRPlantWire.eventBytes ev) := by decide +kernel
theorem ss_pt_len : CompRX0SS38.ptB.length < 16 := by decide +kernel
theorem ss_c_kdfFree : KdfFree CompRX0SS38.cB := by decide +kernel
theorem ss0_kdfFree : KdfFree compKyberSs0 := by decide +kernel
theorem compKyberEncaps_e0 : compKyberEncaps compKyberE0 = compKyberCt0 ++ compKyberSs0 := by unfold compKyberEncaps; simp
theorem kdfFree_kemEncap_snd_of_e0 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE0) : KdfFree (gamma compI0 S g (DY.PQKem.kemEncap pk e).2) := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32, show compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) from rfl, Option.getD_some, he, compKyberEncaps_e0, List.drop_left' Census443Memo.kyberCtVals_lengths.1]; exact ss0_kdfFree
theorem kirc_setup_of_compFits {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost} (hfits : compFits w compI0 r) (hcompat : Compat compI0 r S g) (ha : KdfFree w.aliceId) (hb : KdfFree w.bobId) (hs : KdfFree w.spk) : KdfInjRestCensus compI0 S g (randTerm 0 32) ∧ KdfInjRestCensus compI0 S g (randTerm 5 32) ∧ KdfInjRestCensus compI0 S g (randTerm 10 32) ∧ KdfInjRestCensus compI0 S g (randTerm 16 64) := by
  rcases hfits with ⟨hwf, _, _, _, _, _, hs0_eq, hs1_eq, hs2_eq, _⟩
  have h0_eq : r.fresh 0 32 = secretBytes r 0 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> rfl
  have h1_eq : r.fresh 5 32 = secretBytes r 1 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> rfl
  have h2_eq : r.fresh 10 32 = secretBytes r 2 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> rfl
  have hγ0 : gamma compI0 S g (randTerm 0 32) = w.aliceId := (by rw [gamma_randTerm_eq_of_ne_zero compI0 S g 0 32 (by decide), hcompat.1 (0, 32) (mem_setupRandomsAt_32 hwf.1 (.inl (.inl rfl))), h0_eq, hs0_eq]); have hγ5 : gamma compI0 S g (randTerm 5 32) = w.bobId := (by rw [gamma_randTerm_eq_of_ne_zero compI0 S g 5 32 (by decide), hcompat.1 (5, 32) (mem_setupRandomsAt_32 hwf.1 (.inl (.inr (.inl rfl)))), h1_eq, hs1_eq]); have hγ10 : gamma compI0 S g (randTerm 10 32) = w.spk := (by rw [gamma_randTerm_eq_of_ne_zero compI0 S g 10 32 (by decide), hcompat.1 (10, 32) (mem_setupRandomsAt_32 hwf.1 (.inl (.inr (.inr rfl)))), h2_eq, hs2_eq]); have hγ16 : (gamma compI0 S g (randTerm 16 64)).length = 64 := (by have hp := mem_setupRandomsAt_64 r hwf.1 (ts := 16) (by decide); rw [gamma_randTerm_eq_of_ne_zero compI0 S g 16 64 (by decide), hcompat.1 (16, 64) hp, hwf.2.1 (16, 64) hp])
  exact ⟨kirc_randTerm_of (.inl (hγ0 ▸ ha)), kirc_randTerm_of (.inl (hγ5 ▸ hb)),
    kirc_randTerm_of (.inl (hγ10 ▸ hs)), kirc_randTerm_of (.inr (by rw [hγ16]; decide))⟩
theorem kirc_storedSecrets_of_compFits {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hfits : compFits w compI0 r) (hcompat : Compat compI0 r S g) (ha : KdfFree w.aliceId) (hb : KdfFree w.bobId) (hs : KdfFree w.spk) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), KdfInjRestCensus compI0 S g u := by
  obtain ⟨h0, h5, h10, h16⟩ := kirc_setup_of_compFits hfits hcompat ha hb hs; intro u hu; obtain ⟨ls, rfl, hsk⟩ := mem_storedSecrets_sk_cases hfits.1.1 hfits.2.1 hns hreach hu; refine kirc_serialize_local_pqxdh ?_
  rcases hsk with h | h | h | h <;> rw [h] <;> assumption
theorem kirc_preTerms_split38_of_compFits {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost} (hfits : compFits w compI0 r) (hcompat : Compat compI0 r S g) (ha : KdfFree w.aliceId) (hb_id : KdfFree w.bobId) (hs : KdfFree w.spk) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hns : ∀ m ∈ pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post, m.isSetup = false) (hreach : (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post)).Reachable reachability) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) (hd₀ : let tr₁ := (runMoves pre (setupTrace r)).1; KdfInjRestCensus compI0 S g (randTerm tr₁.length 32) ∧ KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 1) 32) ∧ KdfInjRestCensus compI0 S g (randTerm (tr₁.length + 2) 32)) (he₀ : gamma compI0 S g (randTerm ((runMoves pre (setupTrace r)).1.length + 1) 32) = compKyberE0) (hd₁ : let tr₁ := (runMoves pre (setupTrace r)).1; let tr₂ := (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1; (gamma compI0 S g (randTerm tr₂.length 32)).length < 16 ∧ KdfInjRestCensus compI0 S g (randTerm tr₂.length 32) ∧ KdfInjRestCensus compI0 S g (randTerm (tr₂.length + 1) cl)) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), KdfInjRestCensus compI0 S g u := by
  dsimp only at hd₀ hd₁ ⊢; have hNe : r.alice ≠ r.bob := hfits.1.1; let tr₁ := (runMoves pre (setupTrace r)).1; let tr₂ := (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o; obtain ⟨h0, h5, h10, h16⟩ := kirc_setup_of_compFits hfits hcompat ha hb_id hs; have hss := kdfFree_kemEncap_snd_of_e0 (pk := DY.PQKem.kemPk (randTerm 16 64)) he₀; have ho_out := kirc_aliceOut hNe tr₁ h0 h5 h10 h16 hd₀.1 hd₀.2.1 hss; have hstA : TRStateKIRC compI0 S g stA := (by dsimp only [stA]; rw [ho]; exact trStateKIRC_stA hNe tr₁ h0 h5 h10 h16 hd₀.1 hd₀.2.1 hss hd₀.2.2); refine kirc_prefixTerms ?_ ?_ (kirc_storedSecrets_of_compFits hfits hcompat ha hb_id hs hns hreach) ?_
  · intro v hv hkind u hu_v
    rcases send_terms_split38_mem hNe ho hpre hmid hpost hm₀ hv hkind hu_v with rfl | rfl | rfl
    · rw [ho]; exact ho_out.2.2.2.1
    · rw [ho]; exact ho_out.2.2.2.2.1
    · exact kirc_encOut_self tr₂ cl hstA hd₁.1 hd₁.2.2
  · intro ls hls
    rcases storedStates_split38_cases ho hpre hmid hpost hm₀ hls with hls_eq | hls_eq <;> rw [hls_eq]
    · exact kirc_serialize_local_tr hstA
    · exact kirc_serialize_local_tr (trStateKIRC_encSt tr₂ cl hstA hd₁.2.2)
  · intro v hv hkind u hu_v; rw [pt_terms_split38_mem hNe ho hpre hmid hpost hm₀ hv hkind hu_v]; exact hd₁.2.1
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem split38PairsAt_qKdfInjRest_ss {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} (v : Fin 4) (t : Fin 8) (ha : KdfFree w.aliceId) (hb_id : KdfFree w.bobId) (hs : KdfFree w.spk) (hτ : τ = (.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send sentWireBytes]) : Split38PairsAt QKdfInjRest w τ wire v t := by
  intro r S g p hfits _hp _hopk pre mid post hb shown cl e c'; dsimp only; intro hcompat hrun hvis hpre hmid hpost hm₀ _hbd x₁ _hx₁ x₂ _hx₂ _hc₁ hc₂; let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1;
  have htr_eq := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
    (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  rw [hτ] at hvis; obtain ⟨hm₀_vis, hm₁_vis⟩ := CompRX0NBSC38Wire.split38_forall2_vis_inv hfits.1.1.1 rfl hpre hmid hpost hm₀ CompRX0SS38.rsT_len hvis
  exact qKdfInjRest_of_split38_pre (kirc_preTerms_split38_of_compFits hfits.1 hcompat ha hb_id hs rfl (isSetup_false_split38_swap (w₂ := some (tr₁.length + 3, tr₁.length + 4)) hrun.2.1) (htr_eq ▸ hrun.2.2.1.1) hpre hmid hpost hm₀
      (kirc_draws_of_aliceVis hm₀_vis ss_b0_kdfFree (by rw [CompRX0SS38.rsT_coinHeads_eq]; exact ss_e0_kdfFree) ss_dhs_kdfFree)
      (by rw [(CompRX0Gamma.aliceVis_rng_coins hm₀_vis).2, CompRX0SS38.rsT_coinHeads_eq])
      (kirc_draws_of_encVis hm₁_vis ss_pt_len ss_c_kdfFree)) hc₂
theorem split38PairsHB_qKdfInjRest_vt (v : Fin 4) (t : Fin 8) : Split38PairsAt QKdfInjRest Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes v t :=
  split38PairsAt_qKdfInjRest_ss v t hb_aliceId_kdfFree hb_bobId_kdfFree hb_spk_kdfFree CompRX0SS38.highBitComp_take38
theorem split38PairsHB_qKdfInjRest : Split38PairsAt QKdfInjRest Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0 :=
  split38PairsHB_qKdfInjRest_vt 1 0
theorem split38PairsTC_qKdfInjRest_vt (v : Fin 4) (t : Fin 8) : Split38PairsAt QKdfInjRest Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes v t :=
  split38PairsAt_qKdfInjRest_ss v t tc_aliceId_kdfFree tc_bobId_kdfFree tc_spk_kdfFree CompRX0SS38.torsionComp_take38
theorem split38PairsTC_qKdfInjRest : Split38PairsAt QKdfInjRest Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1 :=
  split38PairsTC_qKdfInjRest_vt 0 1
end Symbolic.BugInjection.Proofs.Common443.CompC3KdfInjRest38HB
