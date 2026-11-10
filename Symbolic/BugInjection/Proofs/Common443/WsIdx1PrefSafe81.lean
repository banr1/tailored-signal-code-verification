/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe81Aux
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumAux
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81Core
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe81
open ByteSpecs open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Refinement DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompFitsNames Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40Aux Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe81Aux Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40 hiding ptAt sendAt
attribute [local irreducible] setupPublic setupSecret
set_option maxRecDepth 200000 in
theorem rngAt79_inits_safe : ∀ c ∈ (rngAt 79).inits, RngEventSafe (.rng c) := by decide
def Split81PrefixEnumPre : Prop := ∀ {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}, WS81Idx1Pre r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Split81PrefixEnumOn r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅
set_option maxHeartbeats 800000 in
theorem ws81Idx1Fresh_of_enumOn {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hpre : WS81Idx1Pre r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) (henum : Split81PrefixEnumOn r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : WS81Idx1Fresh r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ := by
  have hwf : RecordsWF r := hpre.fits.1.1; have hopk : r.withOpk = false := hpre.fits.1.2.1; have hsec3_eq : secretBytes r 3 = fillFresh 11 64 := hpre.fits.2.2.1.1; have hsec4_eq : secretBytes r 4 = fillFresh 16 64 := hpre.fits.2.2.1.2.1; have hsec5_eq : secretBytes r 5 = fillFresh 17 64 := hpre.fits.2.2.1.2.2
  have ha_ne : r.alice.toUTF8.size ≠ 64 := by rw [hpre.fits.2.2.2.1.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.2]; decide
  have hb_ne : r.bob.toUTF8.size ≠ 64 := by rw [hpre.fits.2.2.2.1.2, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.2]; decide
  have ha_len : r.alice.utf8ByteSize + r.alice.toUTF8.size < 28 := by rw [hpre.fits.2.2.2.1.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.2]; decide
  have hb_len : r.bob.utf8ByteSize + r.bob.toUTF8.size < 28 := by rw [hpre.fits.2.2.2.1.2, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.2]; decide
  have hsec0_u : Untagged4 (secretBytes r 0) := hpre.fits.1.2.2.2.2.2.2.1 ▸ setup_aliceId_untagged4; have hsec1_u : Untagged4 (secretBytes r 1) := hpre.fits.1.2.2.2.2.2.2.2.1 ▸ setup_bobId_untagged4; have hsec2_u : Untagged4 (secretBytes r 2) := hpre.fits.1.2.2.2.2.2.2.2.2.1 ▸ setup_spk_untagged4
  obtain ⟨b1, b2, b5, hc1, hc2, hc5, hmp_comp⟩ := hpre.mp.2.2.2.2.2
  have hmp_cref := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp_comp
  obtain ⟨ms₄₃, pre₄, mid₅, post₅, m₄, me₅, sIdx₅, cl₅', pq₅, e₅, c₅, tr₄', tr₅',
    hms, hmp₄₃, htr₄_raw, htr₅', _, _, hpre₄, hmid₅, hpost₅, _, hvis₄, hvis₅⟩ :=
    WsIdx1Decomp81Core.decomp45_raw hc5 hmp_cref
  obtain ⟨ms₄₀, pre₃, post₃, b_bob, a_bob, kh, regIdxA, mh, pqIdx, spqrMsgIdx, sh_bob, tr_bob, _,
    hms₄₃, hmp₄₀, htr_bob_eq, hpre₃, hpost₃, _, _⟩ := WsIdx1Decomp81Core.decomp43_step hc1 hc2 hmp₄₃
  obtain ⟨pre₀, mid₁, mid₂, post₂, m₀, m₁, m₂, hms₄₀, hpre₀, hmid₁, hmid₂, hpost₂, hvis₀, hvis₁, hvis₂⟩ := decomp40_moves hc1 hc2 hmp₄₀
  let m₃ := Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob
  obtain ⟨m₅, hm₅_def⟩ : ∃ m₅, m₅ = Move.encrypt me₅ sIdx₅ cl₅' pq₅ (some (e₅, c₅)) := ⟨_, rfl⟩; rw [← hm₅_def] at hms hpost₅
  let mid₃ := post₂ ++ pre₃; let mid₄ := post₃ ++ pre₄
  have hrun_ms₄₀ : runTraceMoves r ms₄₀ = (runMoves post₂ (m₂.next (runMoves mid₂
      (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1 := by
    rw [hms₄₀, xpl_runTrace_eq]; simp only [List.append_assoc, List.cons_append, runMoves_append_fst, runMoves]
  have htr_bob_mid₃ : tr_bob = (runMoves mid₃ (m₂.next (runMoves mid₂
      (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1 := by
    dsimp only [mid₃]; rw [htr_bob_eq, hrun_ms₄₀, runMoves_append_fst]
  rw [htr_bob_mid₃] at hpost₃
  have hmid₃ : Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₂.next (runMoves mid₂
      (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1) mid₃ := by
    dsimp only [mid₃]; rw [movesFrom_append, ← hrun_ms₄₀]; exact ⟨hpost₂, hpre₃⟩
  have hrun_ms₄₃ : runTraceMoves r ms₄₃ = (runMoves post₃ (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂
      (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1)).1 := by
    rw [hms₄₃, xpl_runTrace_eq, runMoves_append_fst, runMoves_append_fst, ← xpl_runTrace_eq r ms₄₀, runMoves, ← htr_bob_eq, htr_bob_mid₃]
  have htr₄'_eq : tr₄' = (runMoves mid₄ (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂
      (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1)).1 := by
    rw [htr₄_raw, hrun_ms₄₃, ← runMoves_append_fst]
  rw [htr₄'_eq] at hmid₅ htr₅' hvis₄; rw [htr₅'] at hpost₅
  have hmid₄ : Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect (m₃.next (runMoves mid₃ (m₂.next (runMoves mid₂
      (m₁.next (runMoves mid₁ (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1) mid₄ := by
    dsimp only [mid₄]; rw [movesFrom_append, ← hrun_ms₄₃]; exact ⟨hpost₃, hpre₄⟩
  have hms' : ms' = pre₀ ++ m₀ :: mid₁ ++ m₁ :: mid₂ ++ m₂ :: mid₃ ++ m₃ :: mid₄ ++ m₄ :: mid₅ ++ m₅ :: post₅ := by dsimp only [mid₃, mid₄, m₃]; rw [hms, hms₄₃, hms₄₀]; simp only [List.append_assoc, List.cons_append]
  obtain ⟨hb₁, hb₂, sh₁, sh₂, s₁, s₂, s₅, rfl, rfl, rfl, rfl, rfl, htr₁, htr₂, htr₃, htr₄, htr₅,
    hnext₀, hnext₁, hnext₂, hnext₄, hnext₅⟩ :=
    WsIdx1Prefix81Enum.decomp81_links_pin hms' hpre₀ hmid₁ hmid₂ hmid₃ hmid₄ hmid₅ hpost₅
      (fun _ _ _ _ _ _ h => by dsimp only [m₃] at h; cases h)
      (fun _ _ _ _ _ h => by dsimp only [m₃] at h; cases h) hpre.links
  cases hm₅_def; rw [← htr₁] at hvis₀ hvis₁ hvis₂ hvis₄ htr₅'; rw [← htr₂] at hvis₁ hvis₂ hvis₄ htr₅'; rw [← htr₃] at hvis₂ hvis₄ htr₅'; rw [← htr₄, ← WsIdx1Decomp81Core.seg43_shape] at hvis₄; rw [← htr₄] at htr₅'; rw [htr₅'.trans htr₅.symm, hnext₅] at hvis₅; rw [CompRX0NBSC38Parts.aliceStart_vis_eq, hnext₀] at hvis₀
  rw [take_eq_self_of_forall2_length hvis₀ (by rw [aliceVis_iniAliceStartTr_length]; decide), seg0_eq] at hvis₀
  have hd₀_f := freshSafeTerm_draws_of_aliceVis hvis₀ seg0_tail_ne_fillFresh64; have hd₀_u := randUntaggedTerm_draws_of_aliceVis hvis₀ seg0_tail_untagged4 (randUntaggedTerm_randTerm_of_gamma_eq hpre.hent₁ compKyberE1_untagged4); rw [CompRX0NBSC38Parts.encrypt_vis_eq, hnext₁] at hvis₁
  have hc1' : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1 := seg35_eq ▸ hc1
  obtain ⟨hm₁_f, hm₁_u, hm₁_len, hcoins₁_f, hcoins₁_u⟩ := draws_of_encVis_coinSplit hc1' hvis₁ ptAt35_len_ne_64 ptAt35_untagged4 (fun c hc => rngAt36_inits_safe c hc)
  rw [CompRX0NBSC38Parts.encrypt_vis_eq, hnext₂] at hvis₂
  obtain ⟨hm₂_f, hm₂_u, hm₂_len, hcoins₂_f, hcoins₂_u⟩ := draws_of_encVis_coinSplit hc2 hvis₂ ptAt38_len_ne_64 ptAt38_untagged4 (fun c hc => cliCoins2Fast_inits_safe c hc)
  rw [CompRX0NBSC38Parts.aliceStart_vis_eq, hnext₄] at hvis₄
  rw [take_eq_self_of_forall2_length hvis₄ (by rw [aliceVis_iniAliceStartTr_length]; decide), seg43_eq] at hvis₄
  have hd₄_f := freshSafeTerm_draws_of_aliceVis hvis₄ seg43_tail_ne_fillFresh64; have hd₄_u := randUntaggedTerm_draws_of_aliceVis hvis₄ seg43_tail_untagged4 (randUntaggedTerm_randTerm_of_gamma_eq hpre.hent₂ compKyberE2_untagged4)
  have hc5' : DY.Libsignal.Composed.Refinement.Cli.CoinSplit [.pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] b5 := hc5
  obtain ⟨hm₅_f, hm₅_u, hm₅_len, hcoins₅_f, hcoins₅_u⟩ := draws_of_encVis_coinSplit hc5' hvis₅ ptAt78_len_ne_64 ptAt78_untagged4 (fun c hc => rngAt79_inits_safe c hc)
  have hsec_f := freshSafeTerm_setupSecret hpre.compat hwf hsec3_eq hsec4_eq hsec5_eq; have hpub_f := freshSafeTerm_setupPublic hpre.compat hwf hsec3_eq hsec4_eq hsec5_eq
  have hpub2_key_f : CompFreshDistinct.FreshSafeTerm compI0 S g (DY.X25519.x25519Key (setupPublic r 2)) := by rw [x25519Key_setupPublic_2 hwf.1]; exact hpub_f 2
  have hpub4_key_f : CompFreshDistinct.FreshSafeTerm compI0 S g (DY.X25519.x25519Key (setupPublic r 4)) := by rw [x25519Key_setupPublic_4 hwf.1]; exact hpub_f 4
  have hsec_u := randUntaggedTerm_setupSecret hpre.compat hwf hopk hsec0_u hsec1_u hsec2_u hsec3_eq hsec4_eq hsec5_eq; have hpub_u := randUntaggedTerm_setupPublic hpre.compat hwf hopk hsec0_u hsec1_u hsec2_u hsec3_eq hsec4_eq hsec5_eq
  have hpub2_key_u : RandUntaggedTerm compI0 S g (DY.X25519.x25519Key (setupPublic r 2)) := by rw [x25519Key_setupPublic_2 hwf.1]; exact hpub_u 2
  have hpub4_key_u : RandUntaggedTerm compI0 S g (DY.X25519.x25519Key (setupPublic r 4)) := by rw [x25519Key_setupPublic_4 hwf.1]; exact hpub_u 4
  have hfs₁ := fresh_session (tr₁ := tr₁) (tr₂ := tr₂) (tr₃ := tr₃) (cl₁ := cl₁) (cl₃ := cl₂)
    (a := r.alice) (b := r.bob) ha_ne hb_ne (hsec_f 0) (hpub_f 2) hpub2_key_f (hpub_f 4) hpub4_key_f (hpub_f 6)
    hd₀_f.1 hd₀_f.2.2.1 hd₀_f.2.2.2.2.1 hm₁_f hcoins₁_f hm₁_len hm₂_f hcoins₂_f hm₂_len
  have hru₁ := randUntagged_session (i := compI0) (S := S) (g := g)
    (tr₁ := tr₁) (tr₂ := tr₂) (tr₃ := tr₃) (cl₁ := cl₁) (cl₃ := cl₂) (a := r.alice) (b := r.bob)
    (hsec_u 0) (hpub_u 2) hpub2_key_u (hpub_u 4) hpub4_key_u (hpub_u 6)
    hd₀_u.1 hd₀_u.2.1 hd₀_u.2.2 hm₁_u hcoins₁_u hm₂_u hcoins₂_u
  have hfs₂ := fresh_session (tr₁ := tr₄) (tr₂ := tr₅) (tr₃ := tr₅) (cl₁ := cl₅) (cl₃ := cl₅)
    (a := r.alice) (b := r.bob) ha_ne hb_ne (hsec_f 0) (hpub_f 2) hpub2_key_f (hpub_f 4) hpub4_key_f (hpub_f 6)
    hd₄_f.1 hd₄_f.2.2.1 hd₄_f.2.2.2.2.1 hm₅_f hcoins₅_f hm₅_len hm₅_f hcoins₅_f hm₅_len
  have hru₂ := randUntagged_session (i := compI0) (S := S) (g := g)
    (tr₁ := tr₄) (tr₂ := tr₅) (tr₃ := tr₅) (cl₁ := cl₅) (cl₃ := cl₅) (a := r.alice) (b := r.bob)
    (hsec_u 0) (hpub_u 2) hpub2_key_u (hpub_u 4) hpub4_key_u (hpub_u 6)
    hd₄_u.1 hd₄_u.2.1 hd₄_u.2.2 hm₅_u hcoins₅_u hm₅_u hcoins₅_u
  have ho₁_f := freshSafeTerm_aliceOut (tr₁ := tr₁) (hsec_f 0) (hpub_f 2) hpub2_key_f (hpub_f 4) hpub4_key_f (hpub_f 6) hd₀_f.1 hd₀_f.2.2.1; have hstA₁_f := freshSafeTerm_iniAliceStartState (tr₁ := tr₁) (b := r.bob) (hsec_f 0) (hpub_f 2) hpub2_key_f (hpub_f 4) hpub4_key_f (hpub_f 6) hd₀_f.1 hd₀_f.2.2.1 hd₀_f.2.2.2.2.1
  have ho₁_u := randUntaggedTerm_aliceOut (i := compI0) (S := S) (g := g) (tr₁ := tr₁) (hsec_u 0) (hpub_u 2) hpub2_key_u (hpub_u 4) hpub4_key_u (hpub_u 6) hd₀_u.1 hd₀_u.2.1; have hstA₁_u := trStateRandUntagged_iniAliceStartState (i := compI0) (S := S) (g := g) tr₁ r.bob _ ho₁_u.1 ho₁_u.2.1 ho₁_u.2.2.1 hpub4_key_u ho₁_u.2.2.2.2.2.2.1 ho₁_u.2.2.2.2.2.2.2.1 ho₁_u.2.2.2.2.2.2.2.2 hd₀_u.2.2
  refine { hdhs₁ := wsFreshSafeTerm_iff.mpr ⟨hd₀_f.2.2.2.2.1, hd₀_u.2.2⟩
           hm₁ := wsFreshSafeTerm_iff.mpr ⟨hm₁_f, hm₁_u⟩, hm₁_len := hm₁_len
           hcoins₁ := wsFreshSafeTerm_iff.mpr ⟨hcoins₁_f, hcoins₁_u⟩
           hm₂ := wsFreshSafeTerm_iff.mpr ⟨hm₂_f, hm₂_u⟩, hm₂_len := hm₂_len
           hcoins₂ := wsFreshSafeTerm_iff.mpr ⟨hcoins₂_f, hcoins₂_u⟩
           hek₂_safe := wsFreshSafeTerm_iff.mpr ⟨hd₄_f.1, hd₄_u.1⟩
           hent₂_safe := wsFreshSafeTerm_iff.mpr ⟨hd₄_f.2.2.1, hd₄_u.2.1⟩
           hpref_safe := fun u hu => wsFreshSafeTerm_iff.mpr ?_ }
  rcases henum u hu with hatom | hsec_mem
  · unfold Split81PrefixAtom at hatom
    rw [census_iniAliceOut_eq, census_iniAliceStartState_eq, census_encSt_eq, census_encOut_eq] at hatom
    rcases hatom with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | ⟨tr_bob, spqrMsgIdx₂, spqr₂', hγ_bob, hspqr₂, rfl⟩
    · exact ⟨hfs₁.1, hru₁.1⟩
    · exact ⟨hfs₁.2.1, hru₁.2.1⟩
    · exact ⟨hfs₁.2.2.1, hru₁.2.2.1⟩
    · exact ⟨hfs₁.2.2.2.1, hru₁.2.2.2.1⟩
    · exact ⟨hfs₂.1, hru₂.1⟩
    · exact ⟨hfs₂.2.1, hru₂.2.1⟩
    · exact ⟨hfs₂.2.2.1, hru₂.2.2.1⟩
    · exact ⟨hm₁_f, hm₁_u⟩
    · exact ⟨hm₂_f, hm₂_u⟩
    · exact ⟨hm₅_f, hm₅_u⟩
    · exact ⟨hfs₁.2.2.2.2.1, hru₁.2.2.2.2.1⟩
    · exact ⟨hfs₁.2.2.2.2.2.1, hru₁.2.2.2.2.2.1⟩
    · exact ⟨hfs₁.2.2.2.2.2.2, hru₁.2.2.2.2.2.2⟩
    · exact ⟨hfs₂.2.2.2.2.1, hru₂.2.2.2.2.1⟩
    · exact ⟨hfs₂.2.2.2.2.2.1, hru₂.2.2.2.2.2.1⟩
    · exact ⟨freshSafeTerm_serBob_bobSt81 (st_spqr := CompPrefixInvEnc.encSt tr₂ _ cl₁)
        hb_ne ha_ne (hpub_f 0) (hpub_f 2) (hsec_f 2)
        ho₁_f.2.2.2.2.2.2.1 ho₁_f.2.2.2.2.2.2.2.2 hstA₁_f.2.2.2.1
        (freshSafeTerm_spqrSendState hstA₁_f.2.2.2.2.2.2 hcoins₁_f) hcoins₂_f hγ_bob hspqr₂,
      randUntaggedTerm_serBob_bobSt81 (st_spqr := CompPrefixInvEnc.encSt tr₂ _ cl₁) (hpub_u 0) (hpub_u 2) (hsec_u 2) ho₁_u.2.2.2.2.2.2.1 ho₁_u.2.2.2.2.2.2.2.2 hstA₁_u.dhs (trStateRandUntagged_encSt tr₂ cl₁ hstA₁_u hcoins₁_u).spqr hcoins₂_u hγ_bob hspqr₂⟩
  · exact ⟨freshSafeTerm_storedSecrets_of_no_setup hpre.compat hwf hopk ha_len hb_len
      hsec3_eq hsec4_eq hsec5_eq hmp_cref.2.1.2.1 hpre.reach u hsec_mem,
      randUntaggedTerm_storedSecrets_of_no_setup hpre.compat hwf hopk hsec0_u hsec1_u hsec2_u
      hsec3_eq hsec4_eq hsec5_eq hmp_cref.2.1.2.1 hpre.reach u hsec_mem⟩
theorem pref81_of_enum (hE : Split81PrefixEnumPre) : WsIdx1PrefDefs.Pref81Idx1Hyp := fun _ _ _ _ _ _ _ _ _ _ _ _ hpre => ws81Idx1Fresh_of_enumOn hpre (hE hpre)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe81
