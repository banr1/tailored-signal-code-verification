/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40Aux
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40
open ByteSpecs open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Refinement DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompFitsNames Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40Aux Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
attribute [local irreducible] setupPublic setupSecret
def ptAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.pt b) => b | _ => []
def rngAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.rng b) => b | _ => []
def sendAt (n : Nat) : HwBytes :=
  match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with
  | some (.send b) => b | _ => []
def RngEventSafe (e : MachineEvent) : Prop :=
  match e with
  | .rng b => (∀ t ∈ ([11, 16, 17] : List Nat), b ≠ fillFresh t 64) ∧ Untagged4 b
  | _ => True
instance (e : MachineEvent) : Decidable (RngEventSafe e) := by unfold RngEventSafe; cases e <;> infer_instance
theorem seg0_eq : seg 0 35 = .recv (wireAt 0) :: (seg 0 35).tail := rfl
theorem seg35_eq : seg 35 3 = [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] := rfl
theorem seg38_eq : seg 38 2 = [.pt (ptAt 38), .send (sendAt 39)] := rfl
theorem seg0_tail_safe : ∀ e ∈ (seg 0 35).tail, RngEventSafe e := by decide
theorem seg0_tail_ne_fillFresh64 : ∀ b : HwBytes, .rng b ∈ (seg 0 35).tail → ∀ t ∈ ([11, 16, 17] : List Nat), b ≠ fillFresh t 64 := fun b hb => (seg0_tail_safe (.rng b) hb).1
theorem seg0_tail_untagged4 : ∀ b : HwBytes, .rng b ∈ (seg 0 35).tail → Untagged4 b := fun b hb => (seg0_tail_safe (.rng b) hb).2
theorem ptAt35_len_ne_64 : (ptAt 35).length ≠ 64 := by decide
theorem ptAt35_untagged4 : Untagged4 (ptAt 35) := by decide
set_option maxRecDepth 20000 in theorem rngAt36_ne_fillFresh64 : ∀ t ∈ ([11, 16, 17] : List Nat), rngAt 36 ≠ fillFresh t 64 := by decide
set_option maxRecDepth 20000 in theorem rngAt36_untagged4 : Untagged4 (rngAt 36) := by decide
theorem ptAt38_len_ne_64 : (ptAt 38).length ≠ 64 := by decide
theorem ptAt38_untagged4 : Untagged4 (ptAt 38) := by decide
theorem compKyberE1_untagged4 : Untagged4 compKyberE1 := by decide
theorem setup_aliceId_untagged4 : Untagged4 setup.aliceId := by decide
theorem setup_bobId_untagged4 : Untagged4 setup.bobId := by decide
theorem setup_spk_untagged4 : Untagged4 setup.spk := by decide
theorem take_eq_self_of_forall2_length {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} {n : Nat} (h : List.Forall₂ R as (bs.take n)) (hlen : bs.length ≤ as.length) : bs.take n = bs := by
  have h1 := h.length_eq; rw [List.length_take] at h1; exact List.take_of_length_le (by omega)
theorem aliceVis_iniAliceStartTr_length (tr₁ : ExecTrace) (a b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hb : DY.Libsignal.PQXDH.BundleHandles) : (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ a b o) hb).length = 35 := by rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr]; rfl
set_option maxRecDepth 20000 in
theorem rngAt36_inits_safe : ∀ c ∈ (rngAt 36).inits, RngEventSafe (.rng c) := by decide
set_option maxRecDepth 20000 in
theorem cliCoins2Fast_inits_safe : ∀ c ∈ cliCoins2Fast.inits, RngEventSafe (.rng c) := by decide

theorem draws_of_encVis_two {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₃ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wr : Nat × Nat} {pt w : HwBytes} (hm₂ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .send w] (encVis tr₃ (CompPrefixInvEnc.encNextTr tr₃ me sIdx stA cl pq) (some wr) true)) (hpt_len : pt.length ≠ 64) (hpt_u : Untagged4 pt) : cl = 0 ∧ CompFreshDistinct.FreshSafeTerm i S g (randTerm tr₃.length 32) ∧ RandUntaggedTerm i S g (randTerm tr₃.length 32) ∧ (g.σ tr₃.length 32).length ≠ 64 ∧ CompFreshDistinct.FreshSafeTerm i S g (randTerm (tr₃.length + 1) cl) ∧ RandUntaggedTerm i S g (randTerm (tr₃.length + 1) cl) := by
  unfold encVis encSend at hm₂; rw [newRandoms_encNextTr, CompPrefixInvEnc.lastSent_encNextTr] at hm₂
  by_cases hcl : cl = 0
  · subst hcl
    simp only [encDraws, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.filter_cons, List.filter_nil, List.map_nil, List.cons_append, List.nil_append] at hm₂
    rcases hm₂ with (_ | ⟨hem_pt, _ | ⟨_, _⟩⟩)
    have hpt_f := freshSafeTerm_randTerm_of_single_pt_len hem_pt hpt_len
    exact ⟨rfl, hpt_f.1, randUntaggedTerm_randTerm_of_single_pt hem_pt hpt_u, (hpt_f.2 (by decide)).2,
      freshSafeTerm_randTerm_zero i S g (tr₃.length + 1), randUntaggedTerm_randTerm_zero i S g (tr₃.length + 1)⟩
  · have hne : (cl != 0) = true := bne_iff_ne.mpr hcl
    simp only [encDraws, List.filter_cons, hne, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hm₂
    rcases hm₂ with (_ | ⟨_, _ | ⟨_, hnil⟩⟩); cases hnil

theorem mem_inits_of_take {α : Type} :
    ∀ (xs : List α) {n : Nat}, n ≤ xs.length → xs.take n ∈ List.inits xs
  | [], 0, _ => by simp
  | _ :: _, 0, _ => by simp
  | x :: xs, n + 1, hn => by
    simp only [List.length_cons] at hn
    simp only [List.take_succ_cons, List.inits_cons, List.mem_cons, List.mem_map]
    exact Or.inr ⟨xs.take n, mem_inits_of_take xs (by omega), rfl⟩

theorem mem_inits_of_prefix {α : Type} {c coins : List α} (hpref : c <+: coins) : c ∈ coins.inits := by
  obtain ⟨t, ht⟩ := hpref
  have hlen : c.length ≤ coins.length := by rw [← ht, List.length_append]; omega
  have htake : coins.take c.length = c := by rw [← ht, List.take_left]
  rw [← htake]
  exact mem_inits_of_take coins hlen

theorem draws_of_encVis_coinSplit {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState}
    {cl pq : Nat} {wr : Nat × Nat} {pt coins w : HwBytes} {b1 : List MachineEvent}
    (hc1 : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt pt, .rng coins, .send w] b1)
    (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) b1 (encVis tr₂ (CompPrefixInvEnc.encNextTr tr₂ me sIdx stA cl pq) (some wr) true))
    (hpt_len : pt.length ≠ 64) (hpt_u : Untagged4 pt)
    (hcoins : ∀ c ∈ coins.inits, (∀ t ∈ ([11, 16, 17] : List Nat), c ≠ fillFresh t 64) ∧ Untagged4 c) :
    CompFreshDistinct.FreshSafeTerm i S g (randTerm tr₂.length 32) ∧
    RandUntaggedTerm i S g (randTerm tr₂.length 32) ∧
    (g.σ tr₂.length 32).length ≠ 64 ∧
    CompFreshDistinct.FreshSafeTerm i S g (randTerm (tr₂.length + 1) cl) ∧
    RandUntaggedTerm i S g (randTerm (tr₂.length + 1) cl) := by
  have ⟨bs, _, hpref, hblk⟩ : ∃ bs : List HwBytes, (∀ p ∈ bs, p ≠ []) ∧ bs.flatten <+: coins ∧ b1 = .pt pt :: (bs.map MachineEvent.rng ++ [.send w]) := by
    cases hc1 with
    | keep _ h1 =>
      cases h1 with
      | keep hne _ => exact absurd rfl (hne coins)
      | @split _ pieces _ _ hne hpre h2 =>
        cases h2 with
        | keep _ h3 => cases h3; exact ⟨pieces, hne, hpre, rfl⟩
  subst hblk
  cases bs with
  | nil =>
    obtain ⟨-, h1, h2, h3, h4, h5⟩ := draws_of_encVis_two hm₁ hpt_len hpt_u
    exact ⟨h1, h2, h3, h4, h5⟩
  | cons c bs' =>
    cases bs' with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hpref
      have hc_mem : c ∈ coins.inits := mem_inits_of_prefix hpref
      obtain ⟨hc_f, hc_u⟩ := hcoins c hc_mem
      have hd_f := freshSafeTerm_draws_of_encVis hm₁ hpt_len hc_f
      have hd_u := randUntaggedTerm_draws_of_encVis hm₁ hpt_u hc_u
      exact ⟨hd_f.2.1, hd_u.1, hd_f.2.2.1, hd_f.2.2.2.1, hd_u.2⟩
    | cons c2 bs'' =>
      have hlen := hm₁.length_eq
      unfold encVis encSend encDraws at hlen
      rw [newRandoms_encNextTr, CompPrefixInvEnc.lastSent_encNextTr] at hlen
      by_cases hcl : cl = 0 <;> simp [hcl] at hlen

theorem pref40 : WsIdx1PrefDefs.Pref40Hyp := by
  intro r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ hpre; have hwf : RecordsWF r := hpre.fits.1.1; have hopk : r.withOpk = false := hpre.fits.1.2.1; have hsec3_eq : secretBytes r 3 = fillFresh 11 64 := hpre.fits.2.2.1.1; have hsec4_eq : secretBytes r 4 = fillFresh 16 64 := hpre.fits.2.2.1.2.1; have hsec5_eq : secretBytes r 5 = fillFresh 17 64 := hpre.fits.2.2.1.2.2
  have ha_ne : r.alice.toUTF8.size ≠ 64 := by rw [hpre.fits.2.2.2.1.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.2]; decide
  have hb_ne : r.bob.toUTF8.size ≠ 64 := by rw [hpre.fits.2.2.2.1.2, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.2]; decide
  have ha_len : r.alice.utf8ByteSize + r.alice.toUTF8.size < 28 := by rw [hpre.fits.2.2.2.1.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.2]; decide
  have hb_len : r.bob.utf8ByteSize + r.bob.toUTF8.size < 28 := by rw [hpre.fits.2.2.2.1.2, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.2]; decide
  have hsec0_u : Untagged4 (secretBytes r 0) := hpre.fits.1.2.2.2.2.2.2.1 ▸ setup_aliceId_untagged4; have hsec1_u : Untagged4 (secretBytes r 1) := hpre.fits.1.2.2.2.2.2.2.2.1 ▸ setup_bobId_untagged4; have hsec2_u : Untagged4 (secretBytes r 2) := hpre.fits.1.2.2.2.2.2.2.2.2.1 ▸ setup_spk_untagged4
  obtain ⟨b1, b2, hc1, hc2, hmp_comp⟩ := hpre.mp.2.2.2.2.2
  have hmp_cref := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp_comp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnext₀, hnext₁, hnext₂, hvis₀, hvis₁, hvis₂⟩ := decomp40_of_mp_links hc1 hc2 hmp_cref hpre.links; rw [CompRX0NBSC38Parts.aliceStart_vis_eq, hnext₀] at hvis₀
  rw [take_eq_self_of_forall2_length hvis₀ (by rw [aliceVis_iniAliceStartTr_length]; decide), seg0_eq] at hvis₀
  have hd₀_f := freshSafeTerm_draws_of_aliceVis hvis₀ seg0_tail_ne_fillFresh64; have hd₀_u := randUntaggedTerm_draws_of_aliceVis hvis₀ seg0_tail_untagged4 (randUntaggedTerm_randTerm_of_gamma_eq hpre.hent₁ compKyberE1_untagged4); rw [CompRX0NBSC38Parts.encrypt_vis_eq, hnext₁] at hvis₁
  have hc1' : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1 := seg35_eq ▸ hc1
  obtain ⟨hm₁_f, hm₁_u, hm₁_len, hcoins₁_f, hcoins₁_u⟩ := draws_of_encVis_coinSplit hc1' hvis₁ ptAt35_len_ne_64 ptAt35_untagged4 (fun c hc => rngAt36_inits_safe c hc)
  rw [CompRX0NBSC38Parts.encrypt_vis_eq, hnext₂] at hvis₂
  obtain ⟨hm₂_f, hm₂_u, hm₂_len, hcoins₂_f, hcoins₂_u⟩ := draws_of_encVis_coinSplit hc2 hvis₂ ptAt38_len_ne_64 ptAt38_untagged4 (fun c hc => cliCoins2Fast_inits_safe c hc)
  have hsec_f := freshSafeTerm_setupSecret hpre.compat hwf hsec3_eq hsec4_eq hsec5_eq; have hpub_f := freshSafeTerm_setupPublic hpre.compat hwf hsec3_eq hsec4_eq hsec5_eq
  have hpub2_key_f : CompFreshDistinct.FreshSafeTerm compI0 S g (DY.X25519.x25519Key (setupPublic r 2)) := by rw [x25519Key_setupPublic_2 hwf.1]; exact hpub_f 2
  have hpub4_key_f : CompFreshDistinct.FreshSafeTerm compI0 S g (DY.X25519.x25519Key (setupPublic r 4)) := by rw [x25519Key_setupPublic_4 hwf.1]; exact hpub_f 4
  have hsec_u := randUntaggedTerm_setupSecret hpre.compat hwf hopk hsec0_u hsec1_u hsec2_u hsec3_eq hsec4_eq hsec5_eq; have hpub_u := randUntaggedTerm_setupPublic hpre.compat hwf hopk hsec0_u hsec1_u hsec2_u hsec3_eq hsec4_eq hsec5_eq
  have hpub2_key_u : RandUntaggedTerm compI0 S g (DY.X25519.x25519Key (setupPublic r 2)) := by rw [x25519Key_setupPublic_2 hwf.1]; exact hpub_u 2
  have hpub4_key_u : RandUntaggedTerm compI0 S g (DY.X25519.x25519Key (setupPublic r 4)) := by rw [x25519Key_setupPublic_4 hwf.1]; exact hpub_u 4
  have hfs := fresh_session (tr₁ := tr₁) (tr₂ := tr₂) (tr₃ := tr₃) (cl₁ := cl₁) (cl₃ := cl₂)
    (a := r.alice) (b := r.bob) ha_ne hb_ne (hsec_f 0) (hpub_f 2) hpub2_key_f (hpub_f 4) hpub4_key_f (hpub_f 6)
    hd₀_f.1 hd₀_f.2.2.1 hd₀_f.2.2.2.2.1 hm₁_f hcoins₁_f hm₁_len hm₂_f hcoins₂_f hm₂_len
  have hru := randUntagged_session (i := compI0) (S := S) (g := g)
    (tr₁ := tr₁) (tr₂ := tr₂) (tr₃ := tr₃) (cl₁ := cl₁) (cl₃ := cl₂) (a := r.alice) (b := r.bob)
    (hsec_u 0) (hpub_u 2) hpub2_key_u (hpub_u 4) hpub4_key_u (hpub_u 6)
    hd₀_u.1 hd₀_u.2.1 hd₀_u.2.2 hm₁_u hcoins₁_u hm₂_u hcoins₂_u
  refine { hdhs₁ := wsFreshSafeTerm_iff.mpr ⟨hd₀_f.2.2.2.2.1, hd₀_u.2.2⟩
           hm₁ := wsFreshSafeTerm_iff.mpr ⟨hm₁_f, hm₁_u⟩, hm₁_len := hm₁_len
           hcoins₁ := wsFreshSafeTerm_iff.mpr ⟨hcoins₁_f, hcoins₁_u⟩
           hm₂ := wsFreshSafeTerm_iff.mpr ⟨hm₂_f, hm₂_u⟩, hm₂_len := hm₂_len
           hcoins₂ := wsFreshSafeTerm_iff.mpr ⟨hcoins₂_f, hcoins₂_u⟩
           hpref_safe := fun u hu => wsFreshSafeTerm_iff.mpr ?_ }
  rcases split40PrefixEnumOn_of_mp_links hwf.1 hc1 hc2 hmp_cref hpre.links u hu with hatom | hsec_mem
  · unfold Split40PrefixAtom at hatom
    rw [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, census_encOut_eq] at hatom
    rcases hatom with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hfs.1, hru.1⟩
    · exact ⟨hfs.2.1, hru.2.1⟩
    · exact ⟨hfs.2.2.1, hru.2.2.1⟩
    · exact ⟨hfs.2.2.2.1, hru.2.2.2.1⟩
    · exact ⟨hm₁_f, hm₁_u⟩
    · exact ⟨hm₂_f, hm₂_u⟩
    · exact ⟨hfs.2.2.2.2.1, hru.2.2.2.2.1⟩
    · exact ⟨hfs.2.2.2.2.2.1, hru.2.2.2.2.2.1⟩
    · exact ⟨hfs.2.2.2.2.2.2, hru.2.2.2.2.2.2⟩
  · exact ⟨freshSafeTerm_storedSecrets_of_no_setup hpre.compat hwf hopk ha_len hb_len
      hsec3_eq hsec4_eq hsec5_eq hmp_cref.2.1.2.1 hpre.reach u hsec_mem,
      randUntaggedTerm_storedSecrets_of_no_setup hpre.compat hwf hopk hsec0_u hsec1_u hsec2_u
      hsec3_eq hsec4_eq hsec5_eq hmp_cref.2.1.2.1 hpre.reach u hsec_mem⟩
end Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40
