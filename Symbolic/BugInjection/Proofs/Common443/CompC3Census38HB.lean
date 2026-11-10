/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2Census38
public import Symbolic.BugInjection.Proofs.Common443.CompC2RestCore
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestPre38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3KdfInjRest38HB

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC3Census38HB
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompRMemoKnown CompRI0TermInj CompRNonInj38Census CompRQRestCensusZ CompC2Census38 CompC2RestCore CompPrefixInvAlice CompPrefixInvEnc Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
section Gen
variable {S : Sem} {g : Ghost}
theorem census_storedSecrets_gen {w : PQXDHSpqrSetup} {r : Records} {ms : List Move} (hfits : compFits w compI0 r) (hA : r.alice = "alice") (hB : r.bob = "bob") (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), Census compI0 S g u := by
  have hL {ts sz} (hp : (ts, sz) ∈ setupRandomsAt r) (hsz : sz ≠ 0) (h32 : 32 ≤ sz) :
      32 ≤ (gamma compI0 S g (randTerm ts sz)).length := by
    rw [gamma_setup_len hc hfits.1 hp hsz]; exact h32
  intro u hu
  obtain ⟨ls, rfl, ⟨hp, hsk⟩ | ⟨hp, hsk⟩⟩ := mem_storedSecrets_setup_cases hfits.1.1 hfits.2.1 hns hreach hu
  · refine census_serialize_local_pqxdh (participant_size_ne (.inl (hp.trans hA))) ?_ ?_ <;> rw [hsk]
    · exact census_randTerm _ _
    · exact hL (CompPrefixInvFresh.mem_setupRandomsAt_32 hfits.1.1 (.inl (.inl rfl))) (by decide) le_rfl
  · refine census_serialize_local_pqxdh (participant_size_ne (.inr (hp.trans hB))) ?_ ?_
    · rcases hsk with h | h | h <;> rw [h] <;> exact census_randTerm _ _
    · rcases hsk with h | h | h <;> rw [h]
      · exact hL (CompPrefixInvFresh.mem_setupRandomsAt_32 hfits.1.1 (.inl (.inr (.inl rfl)))) (by decide) le_rfl
      · exact hL (CompPrefixInvFresh.mem_setupRandomsAt_32 hfits.1.1 (.inl (.inr (.inr rfl)))) (by decide) le_rfl
      · exact hL (CompPrefixInvFresh.mem_setupRandomsAt_64 r hfits.1.1 (by simp)) (by decide) (by decide)
theorem gamma_x25519Key_dhPk (sk : DY.Bytes) : gamma compI0 S g (DY.X25519.x25519Key (DY.DiffieHellman.dhPk sk)) = compLookupPub (clamp (gamma compI0 S g sk)) := by rw [CompPlant.x25519Key_dhPk, CompFreshDistinct.gamma_dhPk_compI0]
theorem census_torsionVariant {k : DY.Bytes} (v : Fin 4) (t : Fin 8) {pk : HwBytes} (hk : Census compI0 S g k) (hγ : gamma compI0 S g (DY.X25519.x25519Key k) = pk) (hP : ¬ (v = 0 ∧ t = 0) → NonInjOffXZ (variantBytes (DY.Libsignal.Refinement.torsionShift compI0 pk t) v)) : Census compI0 S g (DY.X25519.x25519TorsionVariant k v t) := by
  by_cases hvt : v = 0 ∧ t = 0
  · obtain ⟨rfl, rfl⟩ := hvt; unfold DY.X25519.x25519TorsionVariant; simp only [and_self, ↓reduceIte]; exact census_x25519Key hk
  · have hdef : DY.X25519.x25519TorsionVariant k v t = ({ key := DY.X25519.x25519Key k, variation := v, torsion := t } :
          DY.X25519.Variant.SubF DY.Bytes).pack := by
      unfold DY.X25519.x25519TorsionVariant; simp only [hvt, ite_false]
    rw [hdef]; intro x hx; unfold gamma' at hx; rw [DY.Bytes.rec_eq (gVariant0 compI0) (gAll compI0 S g)] at hx; simp only [gVariant0, concretizeVariant, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, CompPlant.bytes_rec_gAll] at hx
    rcases hx with rfl | hxk
    · intro _; dsimp only; rw [show (gamma' compI0 S g (DY.X25519.x25519Key k)).bytes = pk from hγ]; exact hP hvt
    · exact census_x25519Key hk x hxk
end Gen
section Main
open Symbolic.BugInjection.Proofs.Common443.CompRNoBSC (encSalt_iniAliceStartState_eq_spqrChainKey encMsgKeys mem_bobTerms_x0_iff honestSalts_split_eq x25519Key_torsionVariant_aliceOut_ek)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts (runTrace_split38_swap_eq isSetup_false_split38_swap)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 (encrypt_next_split38_eq)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire (split38_forall2_vis_inv aliceVis_dhs_coin)
theorem nonInj38CensusXZAt_of_trace {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} {bun b₀ pt c sw dhs : HwBytes} {rs' : List MachineEvent} (hτ : τ = (.recv bun :: .rng b₀ :: rs') ++ [.pt pt, .rng c, .send sw]) (hrs : rs'.length = 33) (hdhs : rs'.drop 32 = [.rng dhs]) (hcoin : (CompRX0Gamma.coinHeads (rs'.take 32)).length = 32) (hek : ¬ (v = 0 ∧ t = 0) → NonInjOffXZ (variantBytes (DY.Libsignal.Refinement.torsionShift compI0 (compLookupPub (clamp b₀)) t) v)) : NonInj38CensusXZAt w τ wire v t := by
  intro r S g p hfitsP hp hopk pre mid post hb shown cl e c'; have hfits := hfitsP.1; dsimp only; intro hcompat hmr hvis hpre hmid hpost hm₀ _ x hx _ hai; have hNe : r.alice ≠ r.bob := hfits.1.1; have hA := CompFitsNames.compFits_alice hfitsP; have hB := CompFitsNames.compFits_bob hfitsP; let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1;
  have htr_eq := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
    (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  rw [hτ] at hvis; obtain ⟨hvis₀, _⟩ := split38_forall2_vis_inv hNe rfl hpre hmid hpost hm₀ hrs hvis; obtain ⟨hb0, hcoins, _⟩ := aliceVis_dhs_coin hrs hdhs hvis₀; have hγek : gamma compI0 S g (randTerm tr₁.length 32) = b₀ := List.singleton_inj.mp hb0; have hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := (by rw [CompRX0Gamma.gamma_of_kyberCoins hcoins]; exact hcoin)
  have hpost' : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2)
        (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post :=
    CompPrefixInvSwap.encrypt_next_eq_wrap _ _ _ _ _ _ _ ▸ hpost
  have hpre_ok := census_preTerms_split38 (S := S) (g := g) hNe hA hB rfl hent
    (census_storedSecrets_gen hfits hA hB hcompat (isSetup_false_split38_swap (w₂ := some (tr₁.length + 3, tr₁.length + 4)) hmr.2.1) (htr_eq ▸ hmr.2.2.1.1)) hpre hmid hpost' hm₀
  dsimp only at hpre_ok; have ho_out := census_aliceOut (S := S) (g := g) hNe tr₁ hent; have henc_out := census_encOut_stA (S := S) (g := g) hNe hB tr₁ tr₂ cl hent; have hnew := census_bobTerms_list (S := S) (g := g) hNe hB tr₁ tr₂ cl hent
  have hsalts := honestSalts_split_eq rfl rfl hpre hmid hpost'
    (encrypt_next_split38_eq (cl := cl) (some (tr₁.length + 3, tr₁.length + 4)) hm₀ hmid rfl)
  rcases List.mem_append.mp hx with hx₁ | hx₂
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx₁; exact hpre_ok u hu x hxu hai
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx₂
    have hcu : Census compI0 S g u := by
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
      rcases hu with rfl | rfl | rfl | hu_bob
      · exact census_torsionVariant v t ho_out.2.2.2.1
          ((gamma_x25519Key_dhPk (randTerm tr₁.length 32)).trans (by rw [hγek])) hek
      · exact ho_out.2.2.2.2.1
      · exact henc_out.2.1
      · rw [hsalts] at hu_bob; refine hnew u (mem_bobTerms_x0_iff hNe hopk ?_ rfl rfl u hu_bob); exact x25519Key_torsionVariant_aliceOut_ek _ _ _ _ _ _ v t
    exact hcu x hxu hai
end Main
section HB
open Symbolic.BugInjection.Proofs.Common443.CompRX0SS38
theorem rsT_drop32 : rsT.drop 32 = [.rng (CompRPlantWire.eventBytes ((Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 34).headD (.rng [])))] := rfl
theorem compKyberE0_length' : compKyberE0.length = 32 := by decide +kernel
theorem rsT_coinHeads_length : (CompRX0Gamma.coinHeads (rsT.take 32)).length = 32 := by rw [rsT_coinHeads_eq]; exact compKyberE0_length'
theorem nonInjOffXZ_variant_ekA_one : NonInjOffXZ (variantBytes compEkAPub 1) := by unfold NonInjOffXZ NonInjOff KdfFree; decide +kernel
theorem nonInjOffXZ_ekATorsion : NonInjOffXZ compEkATorsion := by unfold NonInjOffXZ NonInjOff KdfFree; decide +kernel
theorem nonInj38CensusXZ_highBitComp (wire : HwBytes) : NonInj38CensusXZAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) wire 1 0 := by refine nonInj38CensusXZAt_of_trace highBitComp_take38 rsT_len rsT_drop32 rsT_coinHeads_length (fun _ => ?_); rw [clamp_b0_lookup, CompI0Laws.torsionShift_compI0]; simpa using nonInjOffXZ_variant_ekA_one
theorem nonInj38CensusXZ_torsionComp (wire : HwBytes) : NonInj38CensusXZAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) wire 0 1 := by
  refine nonInj38CensusXZAt_of_trace torsionComp_take38 rsT_len rsT_drop32 rsT_coinHeads_length (fun _ => ?_); rw [clamp_b0_lookup, CompI0Laws.torsionShift_compI0]
  have hv0 : variantBytes compEkATorsion 0 = compEkATorsion := by decide +kernel
  simpa [hv0] using nonInjOffXZ_ekATorsion

open Symbolic.BugInjection.Proofs.Common443.CompRNoBSC (encSalt_iniAliceStartState_eq_spqrChainKey encMsgKeys mem_bobTerms_x0_iff honestSalts_split_eq x25519Key_torsionVariant_aliceOut_ek)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts (runTrace_split38_swap_eq isSetup_false_split38_swap)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 (encrypt_next_split38_eq)
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire (aliceVis_dhs_coin)

theorem nonInj38CensusXZAt_of_trace_split {w : PQXDHSpqrSetup} {τ blk₂ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} {bun b₀ pt c sw dhs : HwBytes} {rs' : List MachineEvent}
    (_hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng c, .send sw] blk₂)
    (hτ : τ = (.recv bun :: .rng b₀ :: rs') ++ blk₂)
    (hrs : rs'.length = 33) (hrk : ∀ ev ∈ rs', eventKind ev = .rng) (hdhs : rs'.drop 32 = [.rng dhs])
    (hcoin : (CompRX0Gamma.coinHeads (rs'.take 32)).length = 32)
    (hek : ¬ (v = 0 ∧ t = 0) → NonInjOffXZ (variantBytes (DY.Libsignal.Refinement.torsionShift compI0 (compLookupPub (clamp b₀)) t) v)) :
    NonInj38CensusXZAt w τ wire v t := by
  intro r S g p hfitsP hp hopk pre mid post hb shown cl e c'
  have hfits := hfitsP.1; dsimp only
  intro hcompat hmr hvis hpre hmid hpost hm₀ _ x hx _ hai
  have hNe : r.alice ≠ r.bob := hfits.1.1
  have hA := CompFitsNames.compFits_alice hfitsP
  have hB := CompFitsNames.compFits_bob hfitsP
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  have htr_eq := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
    (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  rw [hτ] at hvis
  obtain ⟨hvis₀, _⟩ := CompC3RestPre38HB.split38_forall2_vis_inv_split hNe rfl hpre hmid hpost hm₀ hrs hrk hvis
  obtain ⟨hb0, hcoins, _⟩ := aliceVis_dhs_coin hrs hdhs hvis₀
  have hγek : gamma compI0 S g (randTerm tr₁.length 32) = b₀ := List.singleton_inj.mp hb0
  have hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by
    rw [CompRX0Gamma.gamma_of_kyberCoins hcoins]; exact hcoin
  have hpost' : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2)
        (some (tr₁.length + 3, tr₁.length + 4))).next tr₂) post :=
    CompPrefixInvSwap.encrypt_next_eq_wrap _ _ _ _ _ _ _ ▸ hpost
  have hpre_ok := census_preTerms_split38 (S := S) (g := g) hNe hA hB rfl hent
    (census_storedSecrets_gen hfits hA hB hcompat (isSetup_false_split38_swap (w₂ := some (tr₁.length + 3, tr₁.length + 4)) hmr.2.1) (htr_eq ▸ hmr.2.2.1.1)) hpre hmid hpost' hm₀
  dsimp only at hpre_ok
  have ho_out := census_aliceOut (S := S) (g := g) hNe tr₁ hent
  have henc_out := census_encOut_stA (S := S) (g := g) hNe hB tr₁ tr₂ cl hent
  have hnew := census_bobTerms_list (S := S) (g := g) hNe hB tr₁ tr₂ cl hent
  have hsalts := honestSalts_split_eq rfl rfl hpre hmid hpost'
    (encrypt_next_split38_eq (cl := cl) (some (tr₁.length + 3, tr₁.length + 4)) hm₀ hmid rfl)
  rcases List.mem_append.mp hx with hx₁ | hx₂
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx₁; exact hpre_ok u hu x hxu hai
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx₂
    have hcu : Census compI0 S g u := by
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
      rcases hu with rfl | rfl | rfl | hu_bob
      · exact census_torsionVariant v t ho_out.2.2.2.1
          ((gamma_x25519Key_dhPk (randTerm tr₁.length 32)).trans (by rw [hγek])) hek
      · exact ho_out.2.2.2.2.1
      · exact henc_out.2.1
      · rw [hsalts] at hu_bob
        refine hnew u (mem_bobTerms_x0_iff hNe hopk ?_ rfl rfl u hu_bob)
        exact x25519Key_torsionVariant_aliceOut_ek _ _ _ _ _ _ v t
    exact hcu x hxu hai

theorem nonInj38CensusXZ_highBitComp_split (wire : HwBytes) {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt ptB, .rng cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    NonInj38CensusXZAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup
      ((.recv bunBytes :: .rng b0Bytes :: rsT) ++ blk₁) wire 1 0 := by
  refine nonInj38CensusXZAt_of_trace_split hcs rfl rsT_len CompC3RestPre38HB.rsT_kind' rsT_drop32 rsT_coinHeads_length (fun _ => ?_)
  rw [clamp_b0_lookup, CompI0Laws.torsionShift_compI0]; simpa using nonInjOffXZ_variant_ekA_one

theorem nonInj38CensusXZ_torsionComp_split (wire : HwBytes) {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt ptB, .rng cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    NonInj38CensusXZAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup
      ((.recv bunBytes :: .rng b0Bytes :: rsT) ++ blk₁) wire 0 1 := by
  refine nonInj38CensusXZAt_of_trace_split hcs rfl rsT_len CompC3RestPre38HB.rsT_kind' rsT_drop32 rsT_coinHeads_length (fun _ => ?_)
  rw [clamp_b0_lookup, CompI0Laws.torsionShift_compI0]
  have hv0 : variantBytes compEkATorsion 0 = compEkATorsion := by decide +kernel
  simpa [hv0] using nonInjOffXZ_ekATorsion

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem kirc_draws_of_encVis_split {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : DY.Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wr : Nat × Nat} {pt c w : HwBytes} {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng c, .send w] blk₁)
    (hm₁ : List.Forall₂ (EventMatchesEntry compI0 r S g) blk₁ (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some wr) true))
    (hpt : pt.length < 16) (hc : ∀ c' ∈ List.inits c, KdfFree c' ∨ c'.length ≠ 32) :
    (gamma compI0 S g (randTerm tr₂.length 32)).length < 16 ∧
      CompC2KdfInjRest.KdfInjRestCensus compI0 S g (randTerm tr₂.length 32) ∧
      CompC2KdfInjRest.KdfInjRestCensus compI0 S g (randTerm (tr₂.length + 1) cl) := by
  obtain ⟨hpt_em, ⟨n, hn, _, hγ, _⟩, _⟩ := CliCoinSplit.encVis_of_coinSplit_send hcs hm₁
  have hpt_lt : (gamma compI0 S g (randTerm tr₂.length 32)).length < 16 :=
    (CompC2KdfInjRest.gamma_of_single rfl rfl hpt_em) ▸ hpt
  have hmem : c.take n ∈ List.inits c := CliCoinSplit.mem_inits_of_take c hn
  exact ⟨hpt_lt, CompC2KdfInjRest.kirc_randTerm_of (.inr (by omega)),
    CompC2KdfInjRest.kirc_randTerm_of (hγ.symm ▸ hc (c.take n) hmem)⟩

theorem split38PairsAt_qKdfInjRest_ss_split {w : PQXDHSpqrSetup} {τ blk₁ : List MachineEvent} {wire : HwBytes} (v : Fin 4) (t : Fin 8)
    (ha : KdfFree w.aliceId) (hb_id : KdfFree w.bobId) (hs : KdfFree w.spk)
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (hτ : τ = (.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) :
    CompRSplit38PairCore.Split38PairsAt CompRNonInj38Census.QKdfInjRest w τ wire v t := by
  intro r S g p hfits _hp _hopk pre mid post hb shown cl e c'; dsimp only
  intro hcompat hrun hvis hpre hmid hpost hm₀ _hbd x₁ _hx₁ x₂ _hx₂ _hc₁ hc₂
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  have htr_eq := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
    (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  rw [hτ] at hvis
  obtain ⟨hm₀_vis, hm₁_vis⟩ := CompC3RestPre38HB.split38_forall2_vis_inv_split hfits.1.1.1 rfl hpre hmid hpost hm₀ CompRX0SS38.rsT_len CompC3RestPre38HB.rsT_kind' hvis
  exact CompC2KdfInjRest.qKdfInjRest_of_split38_pre
    (CompC3KdfInjRest38HB.kirc_preTerms_split38_of_compFits hfits.1 hcompat ha hb_id hs rfl
      (isSetup_false_split38_swap (w₂ := some (tr₁.length + 3, tr₁.length + 4)) hrun.2.1)
      (htr_eq ▸ hrun.2.2.1.1) hpre hmid hpost hm₀
      (CompC2KdfInjRest.kirc_draws_of_aliceVis hm₀_vis CompC3KdfInjRest38HB.ss_b0_kdfFree
        (by rw [CompRX0SS38.rsT_coinHeads_eq]; exact CompC3KdfInjRest38HB.ss_e0_kdfFree)
        CompC3KdfInjRest38HB.ss_dhs_kdfFree)
      (by rw [(CompRX0Gamma.aliceVis_rng_coins hm₀_vis).2, CompRX0SS38.rsT_coinHeads_eq])
      (kirc_draws_of_encVis_split hcs hm₁_vis CompC3KdfInjRest38HB.ss_pt_len CompC3RestPre38HB.cB_inits_kdfFree_or_ne32)) hc₂

theorem split38PairsHB_qKdfInjRest_split {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    CompRSplit38PairCore.Split38PairsAt CompRNonInj38Census.QKdfInjRest
      Witnesses.Cheval26SmallSubgroupHighBitComp.setup
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁)
      CompRPlantWire.highBitWireBytes 1 0 :=
  split38PairsAt_qKdfInjRest_ss_split 1 0 CompC3KdfInjRest38HB.hb_aliceId_kdfFree
    CompC3KdfInjRest38HB.hb_bobId_kdfFree CompC3KdfInjRest38HB.hb_spk_kdfFree hcs rfl

theorem split38PairsTC_qKdfInjRest_split {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    CompRSplit38PairCore.Split38PairsAt CompRNonInj38Census.QKdfInjRest
      Witnesses.Cheval26SmallSubgroupTorsionComp.setup
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁)
      CompRPlantWire.torsionWireBytes 0 1 :=
  split38PairsAt_qKdfInjRest_ss_split 0 1 CompC3KdfInjRest38HB.tc_aliceId_kdfFree
    CompC3KdfInjRest38HB.tc_bobId_kdfFree CompC3KdfInjRest38HB.tc_spk_kdfFree hcs rfl

end HB
end Symbolic.BugInjection.Proofs.Common443.CompC3Census38HB
