/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2RestR38
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplit
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompC3Pre38HB

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC3RestPre38HB
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPlant CompPrefixInvAlice CompPrefixInvBundle CompPrefixInvEnc CompPrefixInvFresh CompPrefixInvStruct CompPrefixInvSwap CompRMemoKnown CompRNoBSC CompRPlantWire CompRX0SS38 CompRX0NBSC38 CompRX0NBSC38Hmc CompRX0NBSC38Parts CompRX0NBSC38Wire CompRX0Top CompRTag CompRI0ShaInj CompRI0TermInj CompRNbscTable CompRNbsc38MacKey CompRNbsc38MacKeyWire CompRSplit38Untagged CompRSplit38ZPin CompRSplit38ZTag CompRSplit38TaggedAgree CompC2PreUntagged38 CompRSplit38PairCore CompRSplit38UntaggedShape CompRNonInj38Census CompRQRestCensusZ CompC2RestCore CompC2Rest38 CompC2RestEntry38 CompC2RestR38 CompC3Pre38HB Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def ssDhsBytes : HwBytes := CompRPlantWire.eventBytes ((Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 34).headD (.rng []))
theorem rsT_drop32 : CompRX0SS38.rsT.drop 32 = [.rng ssDhsBytes] := rfl
theorem compKyberEncaps_e0 : compKyberEncaps compKyberE0 = compKyberCt0 ++ compKyberSs0 := by unfold compKyberEncaps; simp
section RValFacts
private def rValList : List HwBytes :=
  [Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId,
   Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId,
   Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk,
   CompRX0SS38.b0Bytes,
   compKyberE0,
   compKyberSs0,
   ssDhsBytes,
   CompRX0SS38.cB.take 32,
   CompRX0SS38.cB.take 8]
private theorem rValList_all : ∀ v ∈ rValList, RVal v := by
  unfold rValList RVal NonInjOff KdfFree; decide +kernel
theorem rVal_hb_aliceId : RVal Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId :=
  rValList_all _ (by simp [rValList])
theorem rVal_hb_bobId : RVal Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId :=
  rValList_all _ (by simp [rValList])
theorem rVal_hb_spk : RVal Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk :=
  rValList_all _ (by simp [rValList])
theorem rVal_tc_aliceId : RVal Witnesses.Cheval26SmallSubgroupTorsionComp.setup.aliceId := rVal_hb_aliceId
theorem rVal_tc_bobId : RVal Witnesses.Cheval26SmallSubgroupTorsionComp.setup.bobId := rVal_hb_bobId
theorem rVal_tc_spk : RVal Witnesses.Cheval26SmallSubgroupTorsionComp.setup.spk := rVal_hb_spk
theorem rVal_ssB0 : RVal CompRX0SS38.b0Bytes :=
  rValList_all _ (by simp [rValList])
theorem rVal_compKyberE0 : RVal compKyberE0 :=
  rValList_all _ (by simp [rValList])
theorem rVal_compKyberSs0 : RVal compKyberSs0 :=
  rValList_all _ (by simp [rValList])
theorem rVal_ssDhs : RVal ssDhsBytes :=
  rValList_all _ (by simp [rValList])
theorem rVal_ssC : RVal CompRX0SS38.cB := rVal_of_len (by decide +kernel) (by decide +kernel)
theorem cB_inits_len_cases : ∀ c' ∈ List.inits CompRX0SS38.cB,
    c' = CompRX0SS38.cB.take 32 ∨ c' = CompRX0SS38.cB.take 8 ∨ c'.length ≠ 32 ∧ c'.length ≠ 8 := by decide +kernel
theorem cB_take32_rVal : RVal (CompRX0SS38.cB.take 32) :=
  rValList_all _ (by simp [rValList])
theorem cB_take8_rVal : RVal (CompRX0SS38.cB.take 8) :=
  rValList_all _ (by simp [rValList])
theorem rVal_cB_inits (c' : HwBytes) (hc : c' ∈ List.inits CompRX0SS38.cB) : RVal c' := by
  rcases cB_inits_len_cases c' hc with rfl | rfl | ⟨h32, h8⟩
  · exact cB_take32_rVal
  · exact cB_take8_rVal
  · exact rVal_of_len h32 h8
theorem cB_inits_kdfFree_or_ne32 (c' : HwBytes) (hc : c' ∈ List.inits CompRX0SS38.cB) :
    KdfFree c' ∨ c'.length ≠ 32 :=
  if h32 : c'.length = 32 then .inl ((rVal_cB_inits c' hc).1.1 h32) else .inr h32
theorem cB_inits_untagged : ∀ c' ∈ List.inits CompRX0SS38.cB, c'.take 4 ≠ compTag4 := by decide +kernel
theorem rsT_kind' : ∀ ev ∈ CompRX0SS38.rsT, eventKind ev = .rng := by decide +kernel
theorem ptB_eq_compAesPt0 : CompRX0SS38.ptB = compAesPt0 := by decide +kernel
theorem rVal_compAesPt0 : RVal compAesPt0 := rVal_of_len (by decide +kernel) (by decide +kernel)
end RValFacts
theorem rVal_kemEncap_snd_of_e0 {S : Sem} {g : Ghost} {pk e : DY.Bytes} (he : gamma compI0 S g e = compKyberE0) : RVal (gamma compI0 S g (DY.PQKem.kemEncap pk e).2) := by
  have h32 : (gamma compI0 S g e).length = 32 := by rw [he]; decide +kernel
  rw [Census443Memo.gamma_kemEncap_snd_eq h32, show compI0 kyberEncapsSymbol [gamma compI0 S g pk, gamma compI0 S g e] = some (compKyberEncaps (gamma compI0 S g e)) from rfl, Option.getD_some, he, compKyberEncaps_e0, List.drop_left' Census443Memo.kyberCtVals_lengths.1]; exact rVal_compKyberSs0
theorem rVal_compAesPerm_pt0 (k iv : HwBytes) : RVal (compAesPerm k iv compAesPt0) := by
  have hlen : (compAesPerm k iv compAesPt0).length = 16 :=
    CompI0Laws.compAesPerm_length_of_lt_16 k iv compAesPt0 (by decide +kernel)
  exact rVal_of_len (by omega) (by omega)
theorem rVal_symEnc_pt0 {S : Sem} {g : Ghost} {k iv m : DY.Bytes} (hm : gamma compI0 S g m = compAesPt0) : RVal (gamma compI0 S g (DY.SymEnc.symEnc k iv m)) := by rw [gamma_symEnc_eq', hm]; exact rVal_compAesPerm_pt0 _ _
theorem rc_encOut_self_pt0 {S : Sem} {g : Ghost} (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl : Nat) (hst : TRStateRC S g stA) (hpt : gamma compI0 S g (randTerm tr₂.length 32) = compAesPt0) (hc : RC S g (randTerm (tr₂.length + 1) cl)) : RC S g (encOut tr₂ stA cl (tr₂.length + 2)) := by have hmk := rc_trMsgKeys (encSalt_self tr₂ stA cl ▸ rc_spqrSendKey hst.spqr hc) hst.cks; have hct := rc_symEnc (rVal_symEnc_pt0 hpt) hmk.1 hmk.2.2 (rc_randTerm (by rw [hpt]; exact rVal_compAesPt0)); have hdhsPk := rc_dhPk hst.dhs; have hpqMsg := rc_spqrSendMsg hst.spqr hc; dsimp only [encOut, encWire, encMac, DY.Libsignal.TripleRatchet.trHonestWireMsg]; exact rc_concat (rc_trWire hdhsPk hct hpqMsg) (rc_computeMac_trWire hmk.2.1 hst.myIk hst.peerIk hdhsPk hct hpqMsg)
theorem rc_setup_of_rVal {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost} (ha : RVal w.aliceId) (hb : RVal w.bobId) (hspk : RVal w.spk) (hfits : compFitsPinned w compI0 r) (hc : Compat compI0 r S g) : RC S g (randTerm 0 32) ∧ RC S g (randTerm 5 32) ∧ RC S g (randTerm 10 32) ∧ RC S g (randTerm 16 64) := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; refine ⟨rc_randTerm ?_, rc_randTerm ?_, rc_randTerm ?_, rc_randTerm ?_⟩
  · rw [← CompSetupSecrecy.setupSecret_0 hNe, CompRX0Bytes.gamma_setupSecret_0 hNe hc, hfits.1.2.2.2.2.2.2.1]; exact ha
  · rw [← CompSetupSecrecy.setupSecret_1 hNe, CompRX0Bytes.gamma_setupSecret_1 hNe hc, hfits.1.2.2.2.2.2.2.2.1]; exact hb
  · rw [← CompSetupSecrecy.setupSecret_2 hNe, CompRX0Bytes.gamma_setupSecret_2 hNe hc, hfits.1.2.2.2.2.2.2.2.2.1]; exact hspk
  · rw [← CompSetupSecrecy.setupSecret_4 hNe, gamma_setupSecret_4' hNe hc, (CompFitsNames.compFits_secretBytes_fresh hfits).2.1]; exact rVal_fillFresh_16_64
theorem rc_storedSecrets_of_rVal {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (ha : RVal w.aliceId) (hb : RVal w.bobId) (hspk : RVal w.spk) (hfits : compFitsPinned w compI0 r) (hc : Compat compI0 r S g) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), RC S g u := by
  obtain ⟨h0, h5, h10, h16⟩ := rc_setup_of_rVal ha hb hspk hfits hc; intro u hu; obtain ⟨ls, rfl, hsk⟩ := mem_storedSecrets_sk_cases hfits.1.1.1 hfits.1.2.1 hns hreach hu; refine rc_serialize_local_pqxdh ?_
  rcases hsk with h | h | h | h <;> rw [h] <;> assumption
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem rc_preTerms_split38_ss {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost} (ha : RVal w.aliceId) (hb_id : RVal w.bobId) (hspk : RVal w.spk) (hfits : compFitsPinned w compI0 r) (hcompat : Compat compI0 r S g) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) (hns' : ∀ m ∈ pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post, m.isSetup = false) (hreach' : (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post)).Reachable reachability) (hvis' : List.Forall₂ (EventMatchesEntry compI0 r S g) ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes]) (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post))) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), RC S g u := by
  subst ho; dsimp only; have hNe : r.alice ≠ r.bob := hfits.1.1.1; obtain ⟨q₀, hq₀, -⟩ := sentWireBytes_innerWireCanonical.1; obtain ⟨hvis₀, hm₁⟩ := split38_forall2_vis_inv hNe rfl hpre hmid hpost hm₀ CompRX0SS38.rsT_len hvis'; obtain ⟨hb0_s, hcoins, hdhs_s⟩ := aliceVis_dhs_coin CompRX0SS38.rsT_len rsT_drop32 hvis₀; obtain ⟨_, hpt_s, hc_s, _⟩ := encVis_split38_pins CompRX0SS38.sentWireBytes_len hq₀ hm₁; obtain ⟨h0, h5, h10, h16⟩ := rc_setup_of_rVal ha hb_id hspk hfits hcompat; have hekR := rc_randTerm_of_eq (single_eq_inv hb0_s) rVal_ssB0; have he₀ := (CompRX0Gamma.gamma_of_kyberCoins hcoins).trans CompRX0SS38.rsT_coinHeads_eq; have hentR := rc_randTerm_of_eq he₀ rVal_compKyberE0; have hssV := rVal_kemEncap_snd_of_e0 (pk := DY.PQKem.kemPk (randTerm 16 64)) he₀; have hdhsR := rc_randTerm_of_eq (single_eq_inv hdhs_s) rVal_ssDhs; have hpt0 := (single_eq_inv hpt_s).trans ptB_eq_compAesPt0; have hcR := rc_randTerm_of_eq (single_eq_inv hc_s) rVal_ssC; have hout := rc_aliceOut hNe ((runMoves pre (setupTrace r)).1) h0 h5 h10 h16 hekR hentR hssV; have hstA := trStateRC_stA hNe ((runMoves pre (setupTrace r)).1) h0 h5 h10 h16 hekR hentR hssV hdhsR
  have hpost' : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2)
        (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next
        (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post :=
    encrypt_next_eq_wrap _ _ _ _ _ _ _ ▸ hpost
  refine rc_prefixTerms ?_ ?_ (rc_storedSecrets_of_rVal ha hb_id hspk hfits hcompat hns' hreach') ?_
  · intro v hv hkind u hu_v
    rcases send_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v with rfl | rfl | rfl
    · exact hout.2.2.2.1
    · exact hout.2.2.2.2.1
    · exact rc_encOut_self_pt0 _ cl hstA hpt0 hcR
  · intro ls hls
    rcases storedStates_split38_cases rfl hpre hmid hpost' hm₀ hls with hls_eq | hls_eq <;> rw [hls_eq]
    · exact rc_serialize_local_tr hstA
    · exact rc_serialize_local_tr (trStateRC_encSt _ cl hstA hcR)
  · intro v hv hkind u hu_v; rw [pt_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v]; exact rc_randTerm_of_eq hpt0 rVal_compAesPt0
abbrev RestPre38HB : Prop := RestPre38At Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev RestPre38TC : Prop := RestPre38At Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
theorem restPre38At_of_ss {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (ha : RVal w.aliceId) (hb_id : RVal w.bobId) (hspk : RVal w.spk) (hτ : τ = (.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes]) : RestPre38At w τ wire v t := by
  intro r S g p hfits _ _ pre mid post hb shown cl e c'; dsimp only; intro hcompat hmr hvis hpre hmid hpost hm₀ _ u hu x hx; let tr₁ := (runMoves pre (setupTrace r)).1; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1;
  have htr_eq := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
    (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  rw [hτ] at hvis
  have hok := rc_preTerms_split38_ss ha hb_id hspk hfits hcompat rfl
    (isSetup_false_split38_swap (w₂ := some (tr₁.length + 3, tr₁.length + 4)) hmr.2.1)
    (htr_eq ▸ hmr.2.2.1.1) hvis hpre hmid hpost hm₀
  dsimp only at hok; exact hok u hu x hx (CompRPreMemoSound.memo_sound compI0 S g u hx).2
theorem restPre38HB_holds : RestPre38HB := restPre38At_of_ss rVal_hb_aliceId rVal_hb_bobId rVal_hb_spk CompRX0SS38.highBitComp_take38
theorem restPre38TC_holds : RestPre38TC := restPre38At_of_ss rVal_tc_aliceId rVal_tc_bobId rVal_tc_spk CompRX0SS38.torsionComp_take38

private theorem forall2_no_pt_lt_false {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} :
    ∀ {xs ys : List MachineEvent} {us vs : List VisEntry} {v₀ : VisEntry},
      (∀ e ∈ xs, eventKind e ≠ .pt) → v₀.kind = .pt → us.length < xs.length →
      List.Forall₂ (EventMatchesEntry i r S g) (xs ++ ys) (us ++ (v₀ :: vs)) → False
  | [], _, _, _, _, _, _, hlt, _ => by simp at hlt
  | x :: xs, ys, [], vs, v₀, hno, hk, _, List.Forall₂.cons hm _ =>
    hno x (List.mem_cons_self ..) (hm.1.trans hk)
  | _ :: xs, ys, _ :: us, vs, v₀, hno, hk, hlt, List.Forall₂.cons _ hrest =>
    forall2_no_pt_lt_false (fun e he => hno e (List.mem_cons_of_mem _ he)) hk
      (Nat.lt_of_succ_lt_succ hlt) hrest

theorem split38_forall2_vis_inv_split {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles}
    {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1
        (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2)
        (some (e, c'))).next
        (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 =
      iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o)
    {bun b₀ : HwBytes} {rs' blk₂ : List MachineEvent} (hrs' : rs'.length = 33)
    (hrk : ∀ ev ∈ rs', eventKind ev = .rng)
    (hvis : List.Forall₂ (EventMatchesEntry i r S g)
      ((.recv bun :: .rng b₀ :: rs') ++ blk₂)
      (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++
        Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
          ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2)
          (some (e, c')) :: post))) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    let stA := iniAliceStartState tr₁ r.bob o
    List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: .rng b₀ :: rs')
        (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb) ∧
      List.Forall₂ (EventMatchesEntry i r S g) blk₂
        (encVis tr₂ (encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2)) (some (e, c')) true) := by
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  let stA := iniAliceStartState tr₁ r.bob o
  let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))
  change List.Forall₂ (EventMatchesEntry i r S g) ((.recv bun :: .rng b₀ :: rs') ++ blk₂)
    (runVis r (pre ++ m₀ :: mid ++ m₁ :: post)) at hvis
  have henc : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl (tr₂.length + 2) := by
    subst ho; exact encrypt_next_split38_eq (some (e, c')) hm₀ hmid rfl
  have halice : m₀.vis tr₁ = (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).take shown := by
    rw [aliceStart_vis_eq, hm₀]
  rw [runVis_split38_eq hNe hpre hmid hpost, halice, encrypt_vis_eq, henc] at hvis
  have halice_len : (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).length = 35 := by
    rw [aliceVis_iniAliceStartTr]; simp [kyberCoinEntries]
  have hlhs_len : (.recv bun :: .rng b₀ :: rs' : List MachineEvent).length = 35 := by simp [hrs']
  have hno_pt : ∀ ev ∈ (.recv bun :: .rng b₀ :: rs' : List MachineEvent), eventKind ev ≠ .pt := by
    intro ev hev
    rcases List.mem_cons.mp hev with rfl | hev
    · intro h; cases h
    · rcases List.mem_cons.mp hev with rfl | hev
      · intro h; cases h
      · rw [hrk ev hev]; decide
  have hshown : 35 ≤ shown := by
    by_contra hlt
    have hlt' : ((aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).take shown).length <
        (.recv bun :: .rng b₀ :: rs' : List MachineEvent).length := by
      rw [List.length_take, halice_len, hlhs_len]; omega
    have hvis' := hvis
    unfold encVis encDraws at hvis'
    rw [CompPrefixInvFresh.newRandoms_encNextTr] at hvis'
    exact forall2_no_pt_lt_false hno_pt rfl hlt' hvis'
  have htake_eq : (aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb).take shown =
      aliceVis tr₁ (iniAliceStartTr tr₁ r.alice r.bob o) hb :=
    List.take_of_length_le (by omega)
  rw [htake_eq] at hvis
  exact forall2_append_inv (by rw [hlhs_len, halice_len]) hvis

theorem encVis_split38_pins_split {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState}
    {cl pq e c' : Nat} {pt c w : HwBytes} {blk₂ : List MachineEvent} {q₀ : PreKeyFields}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng c, .send w] blk₂)
    (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀)
    (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) blk₂
      (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some (e, c')) true)) :
    [gamma i S g (randTerm tr₂.length 32)] = [pt] ∧
    gamma i S g (randTerm (tr₂.length + 1) cl) ∈ List.inits c ∧
    gamma i S g (encOut tr₂ stA cl pq) = q₀.message := by
  have hsm := CliCoinSplit.sendMatches_of_encVis_split hcs (lastSent_encNextTr tr₂ me sIdx stA cl pq) hm₁
  obtain ⟨_, _, _, _, _, hmsg⟩ := CompRX0Mem.sendMatches_append_inv hsm hlen hq₀
  obtain ⟨hpt, ⟨n, hn, _, hγ, _⟩, _⟩ := CliCoinSplit.encVis_of_coinSplit_send hcs hm₁
  exact ⟨hpt.2, hγ ▸ CliCoinSplit.mem_inits_of_take c hn, hmsg.symm⟩

private theorem encMac_eq'' (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) :
    encMac tr₂ stA cl pq = DY.Libsignal.TripleRatchet.computeMac (encKeys tr₂ stA cl pq).macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq) :=
  rfl

theorem split38_encMac_chain_split {r : Records} {S : Sem} {g : Ghost}
    (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles}
    {shown cl e c' : Nat}
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2)
        (some (e, c'))).next
        (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 =
      iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob
        (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none))
    {bun b₀ pt c wire k P : HwBytes} {rs' blk₂ : List MachineEvent} (hrs' : rs'.length = 33)
    (hrk : ∀ ev ∈ rs', eventKind ev = .rng)
    (hwlen : wire.length < 2 ^ 63)
    (hok : wireMacChainOk k P wire = true)
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng c, .send wire] blk₂)
    (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g)
      ((.recv bun :: .rng b₀ :: rs') ++ blk₂)
      (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++
        Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
          ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2)
          (some (e, c')) :: post))) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let tr₂ := (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1
    let stA := iniAliceStartState tr₁ r.bob o
    gamma compI0 S g (encKeys tr₂ stA cl (tr₂.length + 2)).macKey = k ∧
      gamma compI0 S g (encPrk tr₂ stA cl (tr₂.length + 2)) = P ∧
      k ∈ compHmacKeys32 ∧ P ∈ compHmacKeys32 ∧
      (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA cl (tr₂.length + 2)).macKey
        (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))))).take 4 ≠ compTag4 ∧
      (gamma compI0 S g (encKeys tr₂ stA cl (tr₂.length + 2)).macKey).take 4 ≠ compTag4 := by
  intro tr₁ o tr₂ stA
  obtain ⟨_, hm₁⟩ := split38_forall2_vis_inv_split hNe (o := o) rfl hpre hmid hpost hm₀ hrs' hrk hvis
  cases hq : parsePreKeyWire wire with
  | none =>
    unfold wireMacChainOk at hok; rw [hq] at hok; exact absurd hok Bool.false_ne_true
  | some q₀ =>
    have hpq := macChainOk_of_wire hok hq
    obtain ⟨_, _, hmsg⟩ := encVis_split38_pins_split hcs hwlen hq hm₁
    have hmac : gamma compI0 S g (encMac tr₂ stA cl (tr₂.length + 2)) = msgMac8 q₀ :=
      (gamma_encWire_mac_of_encOut hmsg).2
    obtain ⟨hk, hP, hkK, hPK⟩ := encMac_chain_of_macChainOk S g tr₂ stA cl _ hmac hpq
    have h3 := (macChainOk_spec hpq).2.2.1
    have hu1 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA cl (tr₂.length + 2)).macKey
        (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))))).take 4 ≠ compTag4 := by
      have h := hmac ▸ (macChainOk_spec hpq).1
      rw [encMac_eq'', gamma_computeMac, take4_take8] at h; exact h
    exact ⟨hk, hP, hkK, hPK, hu1, by rw [hk]; exact h3⟩

theorem rc_preTerms_split38_ss_split {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost}
    (ha : RVal w.aliceId) (hb_id : RVal w.bobId) (hspk : RVal w.spk)
    (hfits : compFitsPinned w compI0 r) (hcompat : Compat compI0 r S g)
    {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles}
    {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {blk₁ : List MachineEvent}
    (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    (hns' : ∀ m ∈ pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post, m.isSetup = false)
    (hreach' : (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post)).Reachable reachability)
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (hvis' : List.Forall₂ (EventMatchesEntry compI0 r S g)
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁)
      (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post)))
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), RC S g u := by
  subst ho; dsimp only
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  obtain ⟨q₀, hq₀, -⟩ := sentWireBytes_innerWireCanonical.1
  obtain ⟨hvis₀, hm₁⟩ := split38_forall2_vis_inv_split hNe rfl hpre hmid hpost hm₀ CompRX0SS38.rsT_len rsT_kind' hvis'
  obtain ⟨hb0_s, hcoins, hdhs_s⟩ := aliceVis_dhs_coin CompRX0SS38.rsT_len rsT_drop32 hvis₀
  obtain ⟨hpt_s, hc_in, _⟩ := encVis_split38_pins_split hcs CompRX0SS38.sentWireBytes_len hq₀ hm₁
  obtain ⟨h0, h5, h10, h16⟩ := rc_setup_of_rVal ha hb_id hspk hfits hcompat
  have hekR := rc_randTerm_of_eq (single_eq_inv hb0_s) rVal_ssB0
  have he₀ := (CompRX0Gamma.gamma_of_kyberCoins hcoins).trans CompRX0SS38.rsT_coinHeads_eq
  have hentR := rc_randTerm_of_eq he₀ rVal_compKyberE0
  have hssV := rVal_kemEncap_snd_of_e0 (pk := DY.PQKem.kemPk (randTerm 16 64)) he₀
  have hdhsR := rc_randTerm_of_eq (single_eq_inv hdhs_s) rVal_ssDhs
  have hpt0 := (single_eq_inv hpt_s).trans ptB_eq_compAesPt0
  have hcR := rc_randTerm (rVal_cB_inits _ hc_in)
  have hout := rc_aliceOut hNe ((runMoves pre (setupTrace r)).1) h0 h5 h10 h16 hekR hentR hssV
  have hstA := trStateRC_stA hNe ((runMoves pre (setupTrace r)).1) h0 h5 h10 h16 hekR hentR hssV hdhsR
  have hpost' : MovesFrom InvisibleNoEffect
      ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl
        ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2)
        (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next
        (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post :=
    encrypt_next_eq_wrap _ _ _ _ _ _ _ ▸ hpost
  refine rc_prefixTerms ?_ ?_ (rc_storedSecrets_of_rVal ha hb_id hspk hfits hcompat hns' hreach') ?_
  · intro v hv hkind u hu_v
    rcases send_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v with rfl | rfl | rfl
    · exact hout.2.2.2.1
    · exact hout.2.2.2.2.1
    · exact rc_encOut_self_pt0 _ cl hstA hpt0 hcR
  · intro ls hls
    rcases storedStates_split38_cases rfl hpre hmid hpost' hm₀ hls with hls_eq | hls_eq <;> rw [hls_eq]
    · exact rc_serialize_local_tr hstA
    · exact rc_serialize_local_tr (trStateRC_encSt _ cl hstA hcR)
  · intro v hv hkind u hu_v
    rw [pt_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v]
    exact rc_randTerm_of_eq hpt0 rVal_compAesPt0

theorem restPre38At_of_ss_split {w : PQXDHSpqrSetup} {τ blk₁ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8}
    (ha : RVal w.aliceId) (hb_id : RVal w.bobId) (hspk : RVal w.spk)
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (hτ : τ = (.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) :
    RestPre38At w τ wire v t := by
  intro r S g p hfits _ _ pre mid post hb shown cl e c'; dsimp only
  intro hcompat hmr hvis hpre hmid hpost hm₀ _ u hu x hx
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  have htr_eq := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
    (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  rw [hτ] at hvis
  have hok := rc_preTerms_split38_ss_split ha hb_id hspk hfits hcompat rfl
    (isSetup_false_split38_swap (w₂ := some (tr₁.length + 3, tr₁.length + 4)) hmr.2.1)
    (htr_eq ▸ hmr.2.2.1.1) hcs hvis hpre hmid hpost hm₀
  dsimp only at hok; exact hok u hu x hx (CompRPreMemoSound.memo_sound compI0 S g u hx).2

theorem restPre38HB_split {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    RestPre38At Witnesses.Cheval26SmallSubgroupHighBitComp.setup
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) highBitWireBytes 1 0 :=
  restPre38At_of_ss_split rVal_hb_aliceId rVal_hb_bobId rVal_hb_spk hcs rfl

theorem restPre38TC_split {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    RestPre38At Witnesses.Cheval26SmallSubgroupTorsionComp.setup
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) torsionWireBytes 0 1 :=
  restPre38At_of_ss_split rVal_tc_aliceId rVal_tc_bobId rVal_tc_spk hcs rfl

theorem preNXOK_preTerms_split38_ss_split {w : PQXDHSpqrSetup} {r : Records} {S : Sem} {g : Ghost}
    (ha : w.aliceId = Witnesses.Cheval26WeakState.setup.aliceId)
    (hb_id : w.bobId = Witnesses.Cheval26WeakState.setup.bobId)
    (hs : w.spk = Witnesses.Cheval26WeakState.setup.spk)
    (hfits : compFitsPinned w compI0 r) (hcompat : Compat compI0 r S g)
    {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles}
    {shown cl e c' : Nat} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {blk₁ : List MachineEvent}
    (ho : o = iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
    (hns' : ∀ m ∈ pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post, m.isSetup = false)
    (hreach' : (runTraceMoves r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) :: post)).Reachable reachability)
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (hvis' : List.Forall₂ (EventMatchesEntry compI0 r S g)
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁)
      (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post)))
    (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre)
    (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid)
    (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post)
    (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob o) :
    let tr₁ := (runMoves pre (setupTrace r)).1
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
    let tr₂ := (runMoves mid (m₀.next tr₁)).1
    let pq := tr₂.length + 2
    let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post
    ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), PreNXOK S g u := by
  subst ho; dsimp only
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  obtain ⟨q₀, hq₀, _⟩ := CompRPlantWire.sentWireBytes_innerWireCanonical.1
  obtain ⟨hvis₀, hm₁⟩ := split38_forall2_vis_inv_split hNe rfl hpre hmid hpost hm₀ CompRX0SS38.rsT_len rsT_kind' hvis'
  obtain ⟨hb0_s, hcoins, hdhs_s⟩ := aliceVis_dhs_coin CompRX0SS38.rsT_len CompC3Pre38HB.rsT_drop32 hvis₀
  obtain ⟨hpt_s, hc_in, _⟩ := encVis_split38_pins_split hcs CompRX0SS38.sentWireBytes_len hq₀ hm₁
  have hb0_u := untagged_of_eq (single_eq_inv hb0_s) ssB0Bytes_untagged
  have he0 := (CompRX0Gamma.gamma_of_kyberCoins hcoins).trans CompRX0SS38.rsT_coinHeads_eq
  have he0_u := untagged_of_eq he0 compKyberE0_untagged
  have hdhs_u := untagged_of_eq (single_eq_inv hdhs_s) ssDhsBytes_untagged
  have hpt_eq := single_eq_inv hpt_s
  have hpt_u := untagged_of_eq hpt_eq ssPtBytes_untagged
  have hc_u := untagged_of_eq rfl (cB_inits_untagged _ hc_in)
  obtain ⟨hk, hP, _, _, hu1, hu_mk⟩ := split38_encMac_chain_split (r := r) (S := S) (g := g) hNe hpre hmid hpost hm₀ CompRX0SS38.rsT_len rsT_kind' CompRX0SS38.sentWireBytes_len wireMacChainOk_sentWire hcs hvis'
  have hkdf := split38KdfPins_of_sentMacPin _ _ _ _ _ _ _ _ _ _ hP hk
  obtain ⟨h0, h5, h10, h16⟩ := preNXOK_setupSecrets_of_eq ha hb_id hs hfits hcompat
  have hsec0 : PreNXOK S g (setupSecret r 0) := by rw [CompSetupSecrecy.setupSecret_0 hNe]; exact h0
  have hpub2 : PreNXOK S g (setupPublic r 2) := by rw [CompSetupSecrecy.setupPublic_2 hNe]; exact preNXOK_dhPk h5
  have hpub4 : PreNXOK S g (setupPublic r 4) := by rw [CompSetupSecrecy.setupPublic_4 hNe]; exact preNXOK_dhPk h10
  have hpub6 : PreNXOK S g (setupPublic r 6) := by rw [CompSetupSecrecy.setupPublic_6 hNe]; exact preNXOK_kemPk h16
  obtain ⟨hikA, hikB, hspk, hek, hct, hrk, hck, hpqr⟩ := preNXOK_iniAliceOut _ _ _ _ _ hsec0 hpub2 hpub4 hpub6 hb0_u he0_u hkdf.hpqPrk hkdf.hrk0 hkdf.hck0 hkdf.hpqr0 (kemEncap_fst_untagged_of_e0 he0) (kemEncap_snd_untagged_of_e0 he0)
  have hstA := trStateNX_iniAliceStartState _ r.bob _ hkdf.hchainPrk hdhs_u hikA hikB hspk hrk hck hpqr hkdf.hstARk hkdf.hcks0
  have hsalt := preNXOK_encSalt_ini _ _ _ _ _ hkdf.hencPrk hpqr
  have hstA_enc := trStateNX_encSt ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) cl hstA hc_u hkdf.hcks1
  have hkdf_eq := split38_ss_kdf_eqs _ _ _ _ _ _ _ _ _ _ hP hk
  have henc_out := preNXOK_encOut_pt0 _ _ _ hstA hkdf.hencPrk hsalt hpt_eq hpt_u hc_u hkdf.hseed hkdf.hcipherKey hu_mk hkdf.hiv hu1 hkdf_eq.2.2.2.2.2.2.2.2.2.1 hkdf_eq.2.2.2.2.2.2.2.2.2.2
  have hpost' : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post := encrypt_next_eq_wrap _ _ _ _ _ _ _ ▸ hpost
  refine preNXOK_prefixTerms (fun v hv hkind u hu_v => ?_) (fun ls hls => ?_) (preNXOK_storedSecrets_of_eq ha hb_id hs hfits hcompat hns' hreach') (fun v hv hkind u hu_v => ?_)
  · rcases send_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v with rfl | rfl | rfl <;> [exact hek; exact hct; exact henc_out]
  · rcases storedStates_split38_cases rfl hpre hmid hpost' hm₀ hls with hls_eq | hls_eq <;> rw [hls_eq] <;> [exact preNXOK_serialize_local_tr hstA; exact preNXOK_serialize_local_tr hstA_enc]
  · rw [pt_terms_split38_mem hNe rfl hpre hmid hpost' hm₀ hv hkind hu_v]; exact preNXOK_randTerm hpt_u

theorem split38CtxPairsAt_qPreUntaggedNX_ss_split {w : PQXDHSpqrSetup} {τ blk₁ : List MachineEvent}
    (wire : HwBytes) (v : Fin 4) (t : Fin 8)
    (ha : w.aliceId = Witnesses.Cheval26WeakState.setup.aliceId)
    (hb_id : w.bobId = Witnesses.Cheval26WeakState.setup.bobId)
    (hs : w.spk = Witnesses.Cheval26WeakState.setup.spk)
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (hτ : τ = (.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) :
    Split38CtxPairsAt QPreUntaggedNX w τ wire v t := by
  intro r S g _p hfits _hp _ pre mid post hb shown cl e c'; dsimp only
  intro hcompat hmr hvis hpre hmid hpost hm₀ _ x₁ _ x₂ _ _ _
  let tr₁ := (runMoves pre (setupTrace r)).1
  let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  let pq := tr₂.length + 2
  have htr_eq := runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl pq (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
  rw [hτ] at hvis
  have hpre_ok := preNXOK_preTerms_split38_ss_split ha hb_id hs hfits hcompat rfl
    (isSetup_false_split38_swap (w₂ := some (tr₁.length + 3, tr₁.length + 4)) hmr.2.1)
    (htr_eq ▸ hmr.2.2.1.1) hcs hvis hpre hmid hpost hm₀
  exact ⟨fun hx₁ => let ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx₁; hpre_ok u hu x₁ hxu,
         fun hx₂ => let ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx₂; hpre_ok u hu x₂ hxu⟩

theorem split38CtxPairsHB_qPreUntaggedNX_split {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    Split38CtxPairsAt QPreUntaggedNX Witnesses.Cheval26SmallSubgroupHighBitComp.setup
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁)
      CompRPlantWire.highBitWireBytes 1 0 :=
  split38CtxPairsAt_qPreUntaggedNX_ss_split CompRPlantWire.highBitWireBytes 1 0 rfl rfl rfl hcs rfl

theorem split38CtxPairsTC_qPreUntaggedNX_split {blk₁ : List MachineEvent}
    (hcs : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    Split38CtxPairsAt QPreUntaggedNX Witnesses.Cheval26SmallSubgroupTorsionComp.setup
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁)
      CompRPlantWire.torsionWireBytes 0 1 :=
  split38CtxPairsAt_qPreUntaggedNX_ss_split CompRPlantWire.torsionWireBytes 0 1 rfl rfl rfl hcs rfl

end Symbolic.BugInjection.Proofs.Common443.CompC3RestPre38HB
