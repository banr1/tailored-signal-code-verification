/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC3HB38Defs
public import Symbolic.BugInjection.Proofs.Common443.CompC3Pre38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3Census38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3KdfInjRest38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestPre38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3KdfChild38HB
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.Census443Close
open Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443
theorem nbscHighBitComp : Census443Defs.NbscHighBitComp' := CompC3Nbsc38HB.nbscHighBitComp_of_leaves CompC3Pre38HB.split38CtxPairsHB_qPreUntaggedNX (CompC3Census38HB.nonInj38CensusXZ_highBitComp CompRPlantWire.highBitWireBytes) CompC3KdfInjRest38HB.split38PairsHB_qKdfInjRest CompC3RestPre38HB.restPre38HB_holds CompC3RestFn38HB.rest38FnHB CompC3KdfChild38HB.kdfChild38HB
theorem nbscTorsionComp : Census443Defs.NbscTorsionComp' := CompC3Nbsc38HB.nbscTorsionComp_of_leaves CompC3Pre38HB.split38CtxPairsTC_qPreUntaggedNX (CompC3Census38HB.nonInj38CensusXZ_torsionComp CompRPlantWire.torsionWireBytes) CompC3KdfInjRest38HB.split38PairsTC_qKdfInjRest CompC3RestPre38HB.restPre38TC_holds CompC3RestFn38HB.rest38FnTC CompC3KdfChild38HB.kdfChild38TC
theorem noBsc38HB : CompRX0SS38.NoBsc38HB' := CompRX0SS38.noBsc38HB_of' nbscHighBitComp CompRX0SS38.split38DecompSwapRep_highBitComp
theorem noBsc38TC : CompRX0SS38.NoBsc38TC' := CompRX0SS38.noBsc38TC_of' nbscTorsionComp CompRX0SS38.split38DecompSwapRep_torsionComp

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open CompFreshDistinct CompPrefixInvAlice CompPrefixInvBundle CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRNoBSC CompRPlantWire CompRFaithfulInner CompRX0SS38 CompRX0NBSC38 CompRX0NBSC38Hmc CompRX0NBSC38Parts CompRX0Top CompRX0Gamma CompRX0Mem CompRTag CompRNbsc38VT CompRSplit38PairCore CompRSplit38TaggedAgree CompRSplit38UntaggedShape CompRSplit38ZTag CompRSplit38ZVals CompRSplit38ZPin CompRSplit38QKdf CompRNonInj38Census CompRQRestCensusZ CompC2Rest38 CompC2RestFn CompC2RestEntry38 CompC2KdfKK CompC2KdfChild38Pre CompC3HB38Defs CompC3Nbsc38HB Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem split38_decomp_swap_rep_top_split {r : Records} {S : Sem} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {τ₁ rs' blk₁ : List MachineEvent} {bun b₀ pt c w b : HwBytes}
    {p q₀ : PreKeyFields} (v : Fin 4) (t : Fin 8) (hNe : r.alice ≠ r.bob)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hEq : DY.Libsignal.Refinement.CryptoEquationsHold compI0)
    (hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩)
    (hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩)
    (hcs : Cli.CoinSplit [.pt pt, .rng c, .send w] blk₁)
    (hτ₁ : τ₁ = (.recv bun :: .rng b₀ :: rs') ++ blk₁)
    (hrs_len : rs'.length = 33)
    (hrs_kind : ∀ e ∈ (MachineEvent.rng b₀ :: rs'), eventKind e = .rng)
    (hbun4 : bun[4]? ≠ some 1#8)
    (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag)
    (hw4 : CompRBobInit.hasTag4 w = false)
    (hlen : w.length < 2 ^ 63) (hq₀ : parsePreKeyWire w = some q₀)
    (hbk₀ : q₀.baseKey = ecKey (compLookupPub (clamp b₀)))
    (hkc₀ : Compat compI0 r S g → q₀.kyberCiphertext = some (kyberKey (((compI0 kyberEncapsSymbol [gamma compI0 S g (setupPublic r 6), coinHeads (rs'.take 32)]).getD []).take 1568)))
    (hp : parsePreKeyWire b = some p)
    (hbk : ∀ k : DY.Bytes, DY.X25519.x25519Key k = k → gamma compI0 S g k = compLookupPub (clamp b₀) → p.baseKey.take 33 = ecKey (gamma compI0 S g (DY.X25519.x25519TorsionVariant k v t)))
    (hkc : p.kyberCiphertext = q₀.kyberCiphertext)
    (hpm : p.message = q₀.message)
    (hcan : InnerWireCanonical p)
    (hout : CompRPreKeyWire.PreKeyOuterMatches compI0 r b p)
    (hkvar : ∀ (tr : ExecTrace) (k : DY.Bytes), DY.X25519.x25519Key k = k → k.AttackerKnows tr → (DY.X25519.x25519TorsionVariant k v t).AttackerKnows tr)
    (hex : ExplainsMoves compI0 r S who ok g ms τ₁) :
    ∃ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1
      let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let stA := aliceStartState tr₁ r.bob o
      let ms₀ := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post
      let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
      let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, CompPrefixInvEnc.encOut tr₂ stA cl (tr₂.length + 2)⟩
      ms = ms₀ ∧ Compat compI0 r S g ∧ ModelRun r ms₀ ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms₀) ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (setupTrace r) pre ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₀.next tr₁) mid ∧
      Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ r.alice r.bob o ∧
      bobDoneBaseKeys (runTraceMoves r ms₀) = [] ∧ ExplainsMoves compI0 r S who ok g ms' τ₁ ∧
      x₀ ∈ preKeyRepresentations compI0 r S g ms' b := by
  have hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who g ms
      ((.recv bun :: .rng b₀ :: rs') ++ blk₁) := hτ₁ ▸ hex.1
  obtain ⟨pre, a, idS, hb, shown, mid, cl, e, c', post, ikA, tr₁, tr₂, o, stA, htr₁, ho, hstA, htr₂, hms, hdisj, hek, hct, hekK, hctK, hencK, hnil, hvis₀, hsm, hm₀, hpre, hmid, hpost⟩ :=
    CliCoinSplit.pia_x0_decomp_split hNe hnb hcs hmp (by simp [hrs_len]) hrs_kind hbun4 hw
  have hc : Compat compI0 r S g := hex.1.1
  have hmr : ModelRun r ms := hex.1.2.1
  have hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms) := hex.1.2.2.2.2.2
  rcases hdisj with ⟨hidS, ha, hikA⟩ | ⟨hidS, ha, hikA⟩
  · subst hidS ha hikA ho hstA htr₂ htr₁ hms; rw [hm₀] at hvis₀; obtain ⟨hγek, hγe⟩ := CompRX0Gamma.aliceVis_rng_coins hvis₀
    have hek_γ := CompRX0Gamma.gamma_iniAliceOut_ek_compI0 (S := S) (g := g)
      (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none hγek
    have hcoins : (coinHeads (rs'.take 32)).length = 32 := by simp [coinHeads, hrs_len]
    have hct_γ := CompRX0Gamma.gamma_iniAliceOut_ct (i := compI0) (S := S) (g := g)
      (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      (by rw [hγe]; exact hcoins)
    rw [hγe] at hct_γ
    obtain ⟨hex', hmem'⟩ := CompRX0Join.swap_and_mem_split38 (ek₀ := DY.X25519.x25519TorsionVariant (aliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek v t)
      rfl rfl hek hct hsm rfl rfl hlen hq₀ (hek_γ ▸ hbk₀) (hct_γ ▸ hkc₀ hc) hp
      (hbk _ (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq _) hek_γ) hkc hpm hcan hout hex (hkvar _ _ (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq _) hekK) hctK hencK
    exact ⟨pre, mid, post, hb, shown, cl, e, c', rfl, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hmem'⟩
  · exfalso; subst hidS ha hikA ho hstA; obtain ⟨ek', ct', hL, -⟩ := sendMatches_append_inv hsm hlen hq₀; rw [hL] at hsm; exact CompRX0Bytes.not_sendMatches_bobSelf hNe hEq hc hs1 hs2 w hw4 tr₁ tr₂ r.bob _ _ ek' ct' cl _ hsm

theorem split38DecompSwapRep_highBitComp_split {blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    CompRX0SS38.Split38DecompSwapRep' Witnesses.Cheval26SmallSubgroupHighBitComp.setup
      Witnesses.Cheval26SmallSubgroupHighBitComp.who Witnesses.Cheval26SmallSubgroupHighBitComp.ok
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁)
      Census443Defs.highBitWireBytes 1 0 := by
  intro r S g ms p hfits hnb hex hp; rw [census_highBitWireBytes] at hp ⊢; rw [census_iniAliceOut, census_iniAliceStartState, census_iniAliceStartTr, census_encOut]
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hb, hs, -, -, -, -, hEq, -, -⟩
  have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by rw [hb]; exact highBitComp_compSecretIdx_bobId
  have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by rw [hs]; exact highBitComp_compSecretIdx_spk
  obtain ⟨q₀, hq₀, -⟩ := sentWireBytes_innerWireCanonical.1; have hcan : InnerWireCanonical p := highBitWireBytes_innerWireCanonical.2 p hp; obtain ⟨hpbk, hkc, hpm, -, -⟩ := wirePairOk_spec wirePairOk_highBit hq₀ hp
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hmem'⟩ :=
    split38_decomp_swap_rep_top_split (v := 1) (t := 0) hwf.1 hnb hEq hs1 hs2 hcs rfl rsT_len rsT_kind bunBytes_getElem4_ne sentWireBytes_head_ne sentWireBytes_hasTag4 sentWireBytes_len hq₀ (sentWireBytes_baseKey hq₀)
      (fun _ => by rw [sentWireBytes_kyberCiphertext hq₀, compI0_kyberEncaps_rsT])
      hp
      (fun k hk hγ => by
        rw [gamma_x25519TorsionVariant' S g k 1 0 (by decide), hk, hγ, clamp_b0_lookup]
        exact hpbk)
      hkc hpm hcan (outer_highBit hfits.1 hp) (CompRX0Split38.attackerKnows_torsionVariant 1 0) hex
  obtain ⟨hnb_pre, hnb_mid, hnb_post⟩ := CompRX0Top.noBrkTr_split38 (hms_eq ▸ hnb)
  exact ⟨pre, mid, post, hb_eq, shown, cl, e, c', hc, hmr, hvis, CompRX0SS38.movesFrom_to_census443 hnb_pre hpre, CompRX0SS38.movesFrom_to_census443 hnb_mid hmid, CompRX0SS38.movesFrom_to_census443 hnb_post hpost, hm₀, hnil, hex', hmem'⟩

theorem split38DecompSwapRep_torsionComp_split {blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) :
    CompRX0SS38.Split38DecompSwapRep' Witnesses.Cheval26SmallSubgroupTorsionComp.setup
      Witnesses.Cheval26SmallSubgroupTorsionComp.who Witnesses.Cheval26SmallSubgroupTorsionComp.ok
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁)
      Census443Defs.torsionWireBytes 0 1 := by
  intro r S g ms p hfits hnb hex hp; rw [census_torsionWireBytes] at hp ⊢; rw [census_iniAliceOut, census_iniAliceStartState, census_iniAliceStartTr, census_encOut]
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hb, hs, -, -, -, -, hEq, -, -⟩
  have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by rw [hb]; exact torsionComp_compSecretIdx_bobId
  have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by rw [hs]; exact torsionComp_compSecretIdx_spk
  obtain ⟨q₀, hq₀, -⟩ := sentWireBytes_innerWireCanonical.1; have hcan : InnerWireCanonical p := torsionWireBytes_innerWireCanonical.2 p hp; obtain ⟨hpbk, hkc, hpm, -, -⟩ := wirePairOk_spec wirePairOk_torsion hq₀ hp
  have hv0 : variantBytes compEkATorsion 0 = compEkATorsion := by decide +kernel
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hmem'⟩ :=
    split38_decomp_swap_rep_top_split (v := 0) (t := 1) hwf.1 hnb hEq hs1 hs2 hcs rfl rsT_len rsT_kind bunBytes_getElem4_ne sentWireBytes_head_ne sentWireBytes_hasTag4 sentWireBytes_len hq₀ (sentWireBytes_baseKey hq₀)
      (fun _ => by rw [sentWireBytes_kyberCiphertext hq₀, compI0_kyberEncaps_rsT])
      hp
      (fun k hk hγ => by
        rw [gamma_x25519TorsionVariant' S g k 0 1 (by decide), hk, hγ, clamp_b0_lookup, torsionShift_compEkAPub_one, hv0]
        exact hpbk)
      hkc hpm hcan (outer_torsion hfits.1 hp) (CompRX0Split38.attackerKnows_torsionVariant 0 1) hex
  obtain ⟨hnb_pre, hnb_mid, hnb_post⟩ := CompRX0Top.noBrkTr_split38 (hms_eq ▸ hnb)
  exact ⟨pre, mid, post, hb_eq, shown, cl, e, c', hc, hmr, hvis, CompRX0SS38.movesFrom_to_census443 hnb_pre hpre, CompRX0SS38.movesFrom_to_census443 hnb_mid hmid, CompRX0SS38.movesFrom_to_census443 hnb_post hpost, hm₀, hnil, hex', hmem'⟩

theorem nbsc38At_of_leaves_split {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8}
    (hZ : Split38CtxPairsAt QZNodup5 w τ wire v t)
    (hPre : Split38CtxPairsAt QPreUntaggedNX w τ wire v t)
    (hC : NonInj38CensusXZAt w τ wire v t)
    (hIR : Split38PairsAt QKdfInjRest w τ wire v t)
    (hRP : RestPre38At w τ wire v t)
    (hRF : Rest38FnAt w τ wire v t)
    (hCh : Split38PairsAt QKdfChild2 w τ wire v t) :
    Split38NoClassifiedCollisionAtVT w τ wire v t := by
  have hC' := nonInj38CensusAt_of_XZ hC
  have hRE := rest38EntryAt_of_pre hRP
  have hR := split38PairsAt_qRest_of_fn hC hRE hRF
  have hKK := split38PairsAt_qKdfKK_of_child2 hC' hIR hR hCh
  have hT := taggedW_of_partsT (split38CtxPairsAt_qZInjT_of_nodup hZ) (split38CtxPairsAt_mono qPreUntagged_of_nx hPre) (ctxNonInjOffZ_of_census hC')
  have hU := untaggedW_of_kdf_rest (split38PairsAt_qKdf_of_c (split38PairsAt_qKdfC_of hKK hIR hC')) hR
  exact split38VT_of_weak hT hU

theorem nbscHighBitComp_split {blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (i : ExternInterpretation) (r : Records) (S : Sem)
    (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup i r)
    (g : Ghost) (p : PreKeyFields) (hp : parsePreKeyWire Census443Defs.highBitWireBytes = some p) :
    Census443Defs.NBSC38' r S g 1 0 ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) p := by
  have hi : i = compI0 := hfits.2.1; subst hi
  rw [census_highBitWireBytes] at hp
  obtain ⟨hopk, hidx⟩ := highBitWireBytes_hopk_hidx' hp
  have hvt := nbsc38At_of_leaves_split
    (CompC3Nbsc38HB.split38CtxPairsAt_qZNodup5_of_split hcs rfl)
    (CompC3RestPre38HB.split38CtxPairsHB_qPreUntaggedNX_split hcs)
    (CompC3Census38HB.nonInj38CensusXZ_highBitComp_split CompRPlantWire.highBitWireBytes hcs)
    (CompC3Census38HB.split38PairsHB_qKdfInjRest_split hcs)
    (CompC3RestPre38HB.restPre38HB_split hcs)
    (CompC3RestFn38HB.rest38Fn_of_wirePairOk_split rfl rfl rfl hcs)
    (CompC3KdfChild38HB.split38PairsAt_qKdfChild2_of_sentPrefix_split hcs)
  exact nbsc38'_of_nbsc38 (nbsc38_of_hmc hfits.1.1.1 hopk hidx (hmcAt38_of_classVT hvt hfits hp hopk))

theorem nbscTorsionComp_split {blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (i : ExternInterpretation) (r : Records) (S : Sem)
    (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupTorsionComp.setup i r)
    (g : Ghost) (p : PreKeyFields) (hp : parsePreKeyWire Census443Defs.torsionWireBytes = some p) :
    Census443Defs.NBSC38' r S g 0 1 ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) p := by
  have hi : i = compI0 := hfits.2.1; subst hi
  rw [census_torsionWireBytes] at hp
  obtain ⟨hopk, hidx⟩ := torsionWireBytes_hopk_hidx' hp
  have hvt := nbsc38At_of_leaves_split
    (CompC3Nbsc38HB.split38CtxPairsAt_qZNodup5_of_split hcs rfl)
    (CompC3RestPre38HB.split38CtxPairsTC_qPreUntaggedNX_split hcs)
    (CompC3Census38HB.nonInj38CensusXZ_torsionComp_split CompRPlantWire.torsionWireBytes hcs)
    (CompC3Census38HB.split38PairsTC_qKdfInjRest_split hcs)
    (CompC3RestPre38HB.restPre38TC_split hcs)
    (CompC3RestFn38HB.rest38Fn_of_wirePairOk_split rfl rfl rfl hcs)
    (CompC3KdfChild38HB.split38PairsAt_qKdfChild2_of_sentPrefix_split hcs)
  exact nbsc38'_of_nbsc38 (nbsc38_of_hmc hfits.1.1.1 hopk hidx (hmcAt38_of_classVT hvt hfits hp hopk))

theorem noBsc38HB_split {blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsMoves compI0 r S Witnesses.Cheval26SmallSubgroupHighBitComp.who Witnesses.Cheval26SmallSubgroupHighBitComp.ok g ms
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁))
    (hp : parsePreKeyWire Census443Defs.highBitWireBytes = some p) :
    ∃ g' ms', ExplainsMoves compI0 r S Witnesses.Cheval26SmallSubgroupHighBitComp.who Witnesses.Cheval26SmallSubgroupHighBitComp.ok g' ms'
        ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) ∧
      ∃ x ∈ preKeyRepresentations compI0 r S g' ms' Census443Defs.highBitWireBytes,
        ¬ BobStartCollision compI0 r S g' ms' p x := by
  obtain ⟨pre, mid, post, hb, shown, cl, e, c', hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hx₀⟩ :=
    split38DecompSwapRep_highBitComp_split hcs r S g ms p hfits hnb hex hp
  exact ⟨g, _, hex', _, hx₀, nbscHighBitComp_split hcs compI0 r S hfits g p hp pre mid post hb shown cl e c' hc hmr hvis hpre hmid hpost hm₀ hnil⟩

theorem noBsc38TC_split {blk₁ : List MachineEvent}
    (hcs : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields)
    (hfits : compFitsPinned Witnesses.Cheval26SmallSubgroupTorsionComp.setup compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsMoves compI0 r S Witnesses.Cheval26SmallSubgroupTorsionComp.who Witnesses.Cheval26SmallSubgroupTorsionComp.ok g ms
      ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁))
    (hp : parsePreKeyWire Census443Defs.torsionWireBytes = some p) :
    ∃ g' ms', ExplainsMoves compI0 r S Witnesses.Cheval26SmallSubgroupTorsionComp.who Witnesses.Cheval26SmallSubgroupTorsionComp.ok g' ms'
        ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) ∧
      ∃ x ∈ preKeyRepresentations compI0 r S g' ms' Census443Defs.torsionWireBytes,
        ¬ BobStartCollision compI0 r S g' ms' p x := by
  obtain ⟨pre, mid, post, hb, shown, cl, e, c', hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hx₀⟩ :=
    split38DecompSwapRep_torsionComp_split hcs r S g ms p hfits hnb hex hp
  exact ⟨g, _, hex', _, hx₀, nbscTorsionComp_split hcs compI0 r S hfits g p hp pre mid post hb shown cl e c' hc hmr hvis hpre hmid hpost hm₀ hnil⟩
end Symbolic.BugInjection.Proofs.Common443.Census443Close
