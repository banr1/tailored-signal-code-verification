/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplit
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs
open Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj (KdfFree)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInjOff)
open Symbolic.BugInjection.Proofs.Common443.CompC2RestR38 Symbolic.BugInjection.Proofs.Common443.CompC2Census38 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 (call0Rng_length)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem rngAt1_eq_fast : rngAt 1 = hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng1Chars := by rw [rngAt1_eq_hex, rng1Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
theorem rngAt34_eq_fast : rngAt 34 = hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng34Chars := by rw [rngAt34_eq_hex, rng34Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
set_option maxRecDepth 200000 in theorem rVal_rngAt1 : RVal (rngAt 1) := by rw [rngAt1_eq_fast]; unfold RVal NonInjOff KdfFree; decide +kernel
set_option maxRecDepth 200000 in theorem rVal_rngAt34 : RVal (rngAt 34) := by rw [rngAt34_eq_fast]; unfold RVal NonInjOff KdfFree; decide +kernel
theorem rngAt36_eq_fast : rngAt 36 = hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng36Chars := by rw [rngAt36_eq_hex, rng36Str_eq, Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexBytes_ofList]
set_option maxRecDepth 200000 in
theorem rVal_rngAt36_inits : ∀ c ∈ (rngAt 36).inits, RVal c := by
  rw [rngAt36_eq_fast]; unfold RVal NonInjOff KdfFree; decide +kernel
set_option maxRecDepth 200000 in
theorem rVal_cliCoins2Fast_inits : ∀ c ∈ cliCoins2Fast.inits, RVal c := by
  unfold RVal NonInjOff KdfFree; decide +kernel
theorem rVal_rngAt36 : RVal (rngAt 36) :=
  rVal_of_len (by rw [rngAt36_length]; decide) (by rw [rngAt36_length]; decide)
theorem seg0_35_eq : seg 0 35 = .recv bundle0 :: call0Rng := rfl
theorem seg35_3_eq : seg 35 3 = [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] := rfl
theorem seg38_2_eq : seg 38 2 = [.pt (ptAt 38), .send (sendAt 39)] := rfl
theorem call0Rng_take_1_bytes : ∀ ev ∈ call0Rng.take 1, DY.Libsignal.Composed.Refinement.eventBytes ev = rngAt 1 := by intro ev hev; rw [call0Rng_take_1_eq, List.mem_singleton] at hev; subst hev; rfl
theorem call0Rng_drop_33_bytes : ∀ ev ∈ call0Rng.drop 33, DY.Libsignal.Composed.Refinement.eventBytes ev = rngAt 34 := by intro ev hev; rw [call0Rng_drop_33_eq, List.mem_singleton] at hev; subst hev; rfl
theorem aliceVis_draws_pin_gen {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {a pB : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {hb : DY.Libsignal.PQXDH.BundleHandles} {bun b_ek b_dhs : HwBytes} {rs : List MachineEvent} (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ a pB o) hb)) (hek_ev : ∀ ev ∈ rs.take 1, DY.Libsignal.Composed.Refinement.eventBytes ev = b_ek) (hdhs_ev : ∀ ev ∈ rs.drop 33, DY.Libsignal.Composed.Refinement.eventBytes ev = b_dhs) : gamma compI0 S g (randTerm tr₁.length 32) = b_ek ∧ gamma compI0 S g (randTerm (tr₁.length + 2) 32) = b_dhs := by
  rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr] at hvis
  cases hvis with
  | cons _ hm₁ =>
    cases hm₁ with
    | cons hem_ek hm_rest =>
      rename_i ev_ek rs_tail
      obtain ⟨ev_dhs, hev_dhs_mem, hem_dhs⟩ := forall2_append_drop_exists_left' hm_rest
          ({ rngEntry (randTerm (tr₁.length + 2) 32) with
              anchor := some (tr₁.length + 5) } : VisEntry)
          (List.mem_singleton_self _)
      have hkl : (kyberCoinEntries (randTerm (tr₁.length + 1) 32)).length = 32 := by unfold kyberCoinEntries; simp
      rw [hkl] at hev_dhs_mem
      exact ⟨(gamma_of_single rfl rfl hem_ek).trans (hek_ev ev_ek (by simp)),
        (gamma_of_single rfl rfl hem_dhs).trans (hdhs_ev ev_dhs (by simpa using hev_dhs_mem))⟩
abbrev aliceVis_draws_pin {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {a pB : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {hb : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} := @aliceVis_draws_pin_gen r S g tr₁ a pB o hb bun (rngAt 1) (rngAt 34) rs
theorem encVis_two_pins {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₃ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c' : Nat} {pt w : HwBytes} (hm₂ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .send w] (encVis tr₃ (CompPrefixInvEnc.encNextTr tr₃ me sIdx stA cl pq) (some (e, c')) true)) : gamma i S g (randTerm tr₃.length 32) = pt ∧ cl = 0 := by
  unfold encVis encDraws encSend at hm₂; rw [CompPrefixInvFresh.newRandoms_encNextTr, lastSent_encNextTr] at hm₂
  by_cases hcl : (cl != 0) = true
  · have hlen := hm₂.length_eq; simp [hcl] at hlen
  · refine ⟨gamma_of_single rfl rfl (List.forall₂_cons.mp hm₂).1, ?_⟩
    rcases Nat.eq_zero_or_pos cl with rfl | hpos
    · rfl
    · exact absurd (bne_iff_ne.mpr (Nat.ne_of_gt hpos)) hcl
theorem gamma_randTerm_zero {S : Sem} {g : Ghost} (idx : Nat) : gamma compI0 S g (randTerm idx 0) = [] := by unfold gamma gamma' randTerm; rw [DY.Bytes.rec_eq (gRandom g) (gAll compI0 S g)]; rfl
theorem rVal_randTerm_zero {S : Sem} {g : Ghost} (idx : Nat) : RVal (gamma compI0 S g (randTerm idx 0)) := by
  rw [gamma_randTerm_zero]; exact rVal_of_len (by decide) (by decide)
theorem mem_inits_tail_of_take {α : Type} :
    ∀ (xs : List α) {n : Nat}, n ≠ 0 → n ≤ xs.length → xs.take n ∈ (List.inits xs).tail
  | [], _, hn0, hle => absurd (Nat.le_zero.mp hle) hn0
  | x :: xs, n + 1, _, hle => by
    simp only [List.length_cons] at hle
    simp only [List.take_succ_cons, List.inits_cons, List.tail_cons, List.mem_map]
    exact ⟨xs.take n, Symbolic.BugInjection.Proofs.Common443.CliCoinSplit.mem_inits_of_take xs (by omega), rfl⟩

theorem encVis_coinSplit_pins {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c' : Nat} {pt coins w : HwBytes} {b1 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng coins, .send w] b1)
    (hm₁ : List.Forall₂ (EventMatchesEntry compI0 r S g) b1 (encVis tr₂ (CompPrefixInvEnc.encNextTr tr₂ me sIdx stA cl pq) (some (e, c')) true)) :
    gamma compI0 S g (randTerm tr₂.length 32) = pt ∧
    gamma compI0 S g (randTerm (tr₂.length + 1) cl) ∈ coins.inits ∧
    (cl ≠ 0 → gamma compI0 S g (randTerm (tr₂.length + 1) cl) ∈ coins.inits.tail) := by
  obtain ⟨hpt_s, ⟨n, hn_le, hcl_iff, hc_eq, _⟩, _⟩ := Symbolic.BugInjection.Proofs.Common443.CliCoinSplit.encVis_of_coinSplit_send hc1 hm₁
  refine ⟨gamma_of_single rfl rfl hpt_s, ?_, fun hcl => ?_⟩
  · rw [hc_eq]
    exact Symbolic.BugInjection.Proofs.Common443.CliCoinSplit.mem_inits_of_take coins hn_le
  · rw [hc_eq]
    exact mem_inits_tail_of_take coins (fun hn0 => hcl (hcl_iff.mpr hn0)) hn_le

theorem split40_draw_eqs {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hlinks : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) : gamma compI0 S g (randTerm tr₁.length 32) = rngAt 1 ∧ gamma compI0 S g (randTerm (tr₁.length + 2) 32) = rngAt 34 ∧ gamma compI0 S g (randTerm tr₂.length 32) = compAesPt1 ∧ gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (rngAt 36).inits ∧ (cl₁ ≠ 0 → gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (rngAt 36).inits.tail) ∧ gamma compI0 S g (randTerm tr₃.length 32) = compAesPt2 ∧ gamma compI0 S g (randTerm (tr₃.length + 1) cl₂) ∈ cliCoins2Fast.inits ∧ (cl₂ ≠ 0 → gamma compI0 S g (randTerm (tr₃.length + 1) cl₂) ∈ cliCoins2Fast.inits.tail) := by
  obtain ⟨b1, b2, hc1, hc2, hmp_comp⟩ := hinv.mp.2.2.2.2.2
  obtain ⟨_, _, _, _, hb₁, sh₁, _, _, _, _, _, _, _, _, _, _, hm₀, hm₁, hm₂, hvis₀, hvis₁, hvis₂⟩ := decomp40_of_mp_links hc1 hc2 (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp_comp) hlinks
  let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  have hvis₀' : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bundle0 :: call0Rng) (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ r.alice r.bob o₁) hb₁) := by
    rw [seg0_35_eq, aliceStart_vis_eq, hm₀] at hvis₀
    have halice_len : (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ r.alice r.bob o₁) hb₁).length = 35 := by rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr]; simp [kyberCoinEntries]
    have htot := hvis₀.length_eq
    have hlhs : (.recv bundle0 :: call0Rng : List MachineEvent).length = 35 := by simp [call0Rng_length]
    rw [hlhs, List.length_take, halice_len] at htot
    rwa [List.take_of_length_le (by rw [halice_len]; omega)] at hvis₀
  obtain ⟨hek_pin, hdhs_pin⟩ := aliceVis_draws_pin hvis₀' call0Rng_take_1_bytes call0Rng_drop_33_bytes; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38.encrypt_vis_eq, hm₁] at hvis₁; rw [Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38.encrypt_vis_eq, hm₂] at hvis₂
  have hc1' : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1 := seg35_3_eq ▸ hc1
  obtain ⟨hpt₁_raw, hc₁_mem, hc₁_ne⟩ := encVis_coinSplit_pins hc1' hvis₁
  obtain ⟨hpt₂_raw, hc₂_mem, hc₂_ne⟩ := encVis_coinSplit_pins hc2 hvis₂
  exact ⟨hek_pin, hdhs_pin, hpt₁_raw.trans ptAt35_eq_compAesPt1, hc₁_mem, hc₁_ne, hpt₂_raw.trans ptAt38_eq_compAesPt2, hc₂_mem, hc₂_ne⟩
theorem split40DrawPinsOwn : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Split40DrawPins r S g tr₁ tr₂ tr₃ cl₁ cl₂ := by intro r S g _p ms' tr₁ tr₂ tr₃ cl₁ cl₂ _hfits _hp hinv hlinks; obtain ⟨hek_pin, hdhs_pin, hpt₁_pin, hc₁_mem, _, hpt₂_pin, hc₂_mem, _⟩ := split40_draw_eqs hinv hlinks; exact ⟨hek_pin ▸ rVal_rngAt1, hdhs_pin ▸ rVal_rngAt34, hpt₁_pin, rVal_rngAt36_inits _ hc₁_mem, hpt₂_pin, rVal_cliCoins2Fast_inits _ hc₂_mem⟩
attribute [local irreducible] bundle0 call0Rng ptAt Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.ptAt rngAt sendAt setupPublic setupSecret
theorem census_honestSalts_40 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hNe : r.alice ≠ r.bob) (hB : r.bob = "bob") (hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') : Census compI0 S g salt := by
  have ho := census_aliceOut (S := S) (g := g) hNe tr₁ hent; have hst₁' := trStateC_encSt tr₂ cl₁ (trStateC_stA (S := S) (g := g) hNe hB tr₁ hent)
  rcases hinv.hsalts salt hsalt with rfl | rfl | rfl
  · exact census_zeroKey
  · exact census_spqrChainKey ho.2.2.2.2.2.2.2 census_spqrA2B (census_spqrIdx 1)
  · exact census_spqrSendKey hst₁'.spqr (census_randTerm (tr₃.length + 1) cl₂)
theorem split40NewCensusOwn : ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ u ∈ split40NewTerms r ms' p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂), Census compI0 S g u := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv _hlinks u hu; have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hB : r.bob = "bob" := CompFitsNames.compFits_bob hfits
  have hent : (gamma compI0 S g (randTerm (tr₁.length + 1) 32)).length = 32 := by rw [hinv.hent₁]; decide +kernel
  have ho := census_aliceOut (S := S) (g := g) hNe tr₁ hent; have hst₁ := trStateC_stA (S := S) (g := g) hNe hB tr₁ hent; have hst₁' := trStateC_encSt tr₂ cl₁ hst₁
  have hsalt₂ : Census compI0 S g (CompPrefixInvEnc.encSalt tr₃ (CompPrefixInvEnc.encSt tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ r.bob (CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)) := by rw [CompPrefixInvEnc.encSalt_self]; exact census_spqrSendKey hst₁'.spqr (census_randTerm (tr₃.length + 1) cl₂)
  have henc₂ := census_enc tr₃ cl₂ (tr₃.length + 2) hst₁' hsalt₂ (encWire_len_ge33 _ _ _ _)
  rcases mem_split40NewTerms_iff.mp hu with rfl | rfl | rfl | hbt
  · exact ho.2.2.2.1
  · exact ho.2.2.2.2.1
  · exact henc₂.2.1
  · rcases mem_bobTerms_x40Idx1_iff hNe (wire3Idx1Bytes_preKeyId hp) hbt with
      hextra | ⟨salt, hsalt, hsalt_u⟩
    · simp only [ws40Idx1ExtraTerms, List.mem_cons, List.not_mem_nil, or_false] at hextra
      rcases hextra with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ho.2.2.2.2.2.1
      · exact ho.2.2.2.2.2.2.1
      · exact ho.2.2.2.2.2.2.2
      · exact hst₁.cks
      · exact (trStateC_encSt tr₃ cl₂ hst₁').cks
      · exact (census_kdfCk hst₁.cks).2
      · exact census_randTerm tr₃.length 32
    · have hmk := census_trMsgKeys (census_honestSalts_40 hNe hB hent hinv hsalt)
        (census_kdfCk hst₁'.cks).2
      simp only [ws40Idx1SaltTerms, List.mem_cons, List.not_mem_nil, or_false] at hsalt_u
      rcases hsalt_u with rfl | rfl | rfl | rfl
      · exact hmk.1
      · exact hmk.2.1
      · exact hmk.2.2
      · exact henc₂.2.2 _ hmk.2.1
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewCensus
