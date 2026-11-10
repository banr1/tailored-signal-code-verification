/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtCoins
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8
import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber

/-!
# Plaintext Collision Absence on `.send` Events

Proves `not_nextEventCollides_send`: no `.send` run event in `EvictedChainSkippedKeyCli.trace`
satisfies `NextEventCollides` after an explained prefix under `evictedCompFitsPinned`, since every
non-random `assumedInjective` memo entry is either attacker-known or has at least 8 concrete bytes
while `.send` inputs have length in `1..7` and never occur as an infix of `coins`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtNoCollision

open DY (ExecTrace)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Refinement (sha256CompressFunction)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Explains
   BytesMatchEntry MemoCollisionOn
   ptEntryAt plaintextTerms prefixTerms randTerm runTrace setupTrace setupRandomsAt
   gamma gamma' gDhPk gDh gKdf0 gSym0 gKemEncap gKemSS
   concretizeDhPk concretizeDh concretizeKdf concretizeSym concretizeKemEncap concretizeKemSS
   node opaqueNode assumedInjective)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides PrefixExplainingGhosts)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compKyberEncaps_length)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_dhPk ms_pack_dh ms_pack_kdf ms_pack_sym ms_pack_kemEncap ms_pack_kemSS)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (assumedInjective_eq_true_iff)
open Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (length_hmacWith_32)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase
  (runSteps_le randAt_of_le_of_lt randAt_setupTrace_mem_setupRandomsAt prefixTerms_termRandAt)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAux
  (RandAt pack_of_view_eq_some memo_entry_inv gamma'_randTerm_32 gamma_randTerm_of_ne_zero)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0
  (evictedI0 evictedHooks0 evictedCompFitsPinned
   evictedLookupPub_length evictedLookupDh_length)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.I0Laws
  (evictedI0_publicKey evictedI0_agreement evictedI0_aesEncrypt evictedI0_kyberEncaps
   evictedAesPerm_length)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtCoins
  (matchesEvents_coinDrawn_infix evicted_send_input_facts)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtTrunc8
  (Trunc8RowOK prefixTerms_trunc8OK)

private theorem setupRandomsAt_size_ge_32 {r : ProtocolSetup} (hNe : r.alice ≠ r.bob) {p : Nat × Nat}
    (hp : p ∈ setupRandomsAt r) : 32 ≤ p.2 := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hNe] at hp
  rcases List.mem_append.mp hp with hfixed | hopk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
    rcases hfixed with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · split at hopk
    · simp only [List.mem_singleton] at hopk
      rcases hopk with rfl
      decide
    · cases hopk

private theorem nonRandom_assumedInjective_evictedI0
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (u sh : DY.Bytes)
    (hinj : assumedInjective u = true)
    (hnot_known : ¬ u.AttackerKnows tr)
    (hss32 : ∀ x : DY.PQKem.SharedSecret.SubF DY.Bytes,
      u = x.pack → (gamma evictedI0 S g x.entropy).length = 32)
    (htrunc8 : Trunc8RowOK tr (u, sh, gamma evictedI0 S g u))
    (hlen_pos : 0 < (gamma evictedI0 S g u).length)
    (hlen_lt8 : (gamma evictedI0 S g u).length < 8) :
    ∃ rnd : DY.Random.Random DY.Bytes, u.view? DY.Random.Random = some rnd ∧ rnd.size ≠ 0 := by
  rcases (assumedInjective_eq_true_iff u).mp hinj with
    hrnd | hdhPk | hdh | hkdf | hsym | htrunc | hencap | hss
  · exact hrnd
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdhPk
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma evictedI0 S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_dhPk evictedI0 S g x]
      dsimp only [gDhPk, concretizeDhPk, node]
      rw [evictedI0_publicKey, Option.getD_some]
      exact evictedLookupPub_length _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hdh
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma evictedI0 S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_dh evictedI0 S g x]
      dsimp only [gDh, concretizeDh, node]
      rw [evictedI0_agreement, Option.getD_some]
      exact evictedLookupDh_length _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hkdf
    rcases pack_of_view_eq_some hx with rfl
    have hg : (gamma evictedI0 S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_kdf evictedI0 S g x]
      exact length_hmacWith_32 (sha256CompressFunction evictedI0) _ _
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsym
    rcases pack_of_view_eq_some hx with rfl
    have hg : 16 ≤ (gamma evictedI0 S g x.pack).length := by
      unfold gamma
      rw [ms_pack_sym evictedI0 S g x]
      dsimp only [gSym0, concretizeSym, node]
      rw [evictedI0_aesEncrypt, Option.getD_some, evictedAesPerm_length]
      omega
    omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp htrunc
    rcases pack_of_view_eq_some hx with rfl
    rcases htrunc8 x rfl with hkn | hge8
    · exact absurd hkn hnot_known
    · dsimp only at hge8
      omega
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hencap
    rcases pack_of_view_eq_some hx with rfl
    unfold gamma at hlen_pos hlen_lt8
    rw [ms_pack_kemEncap evictedI0 S g x] at hlen_pos hlen_lt8
    dsimp only [gKemEncap, concretizeKemEncap] at hlen_pos hlen_lt8
    split at hlen_pos
    · rename_i h32
      simp only [h32, ↓reduceIte, node, evictedI0_kyberEncaps, Option.getD_some,
        List.length_take, compKyberEncaps_length] at hlen_lt8
      omega
    · dsimp only [opaqueNode] at hlen_pos
      cases hlen_pos
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hss
    rcases pack_of_view_eq_some hx with rfl
    have he32 : (gamma' evictedI0 S g x.entropy).bytes.length = 32 := hss32 x rfl
    have hg : (gamma evictedI0 S g x.pack).length = 32 := by
      unfold gamma
      rw [ms_pack_kemSS evictedI0 S g x]
      dsimp only [gKemSS, concretizeKemSS]
      simp only [he32, ↓reduceIte, node, evictedI0_kyberEncaps, Option.getD_some,
        List.length_drop, compKyberEncaps_length]
    omega

theorem not_nextEventCollides_send
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent)
    (hfit : evictedCompFitsPinned (evictedI0, evictedHooks0) r)
    (hsplit : Symbolic.BugInjection.Synthetic.Witnesses.EvictedChainSkippedKeyCli.trace = evs₁ ++ .run ev :: evs₂)
    (hex : Explains evictedI0 r S g ss vis evs₁)
    (hsend : ∃ peer, ev.cmd = .send peer) :
    ¬ NextEventCollides evictedI0 r S g ss vis evs₁ ev := by
  obtain ⟨⟨hlen_pos, hlen_lt8⟩, hno_infix⟩ := evicted_send_input_facts hsplit hsend
  obtain ⟨peer, hcmd⟩ := hsend
  unfold NextEventCollides
  rw [hcmd]
  rintro ⟨heme, hghosts⟩
  let tr := runTrace r ss
  have hgpt : gamma evictedI0 S g (randTerm tr.length 32) = ev.input := by
    unfold BytesMatchEntry ptEntryAt at heme
    dsimp only [List.map] at heme
    exact List.head_eq_of_cons_eq heme.2
  have hg_mem : g ∈ PrefixExplainingGhosts evictedI0 r S g ss evs₁ :=
    ⟨rfl, vis, hex⟩
  have hmcol := hghosts g hg_mem
  unfold MemoCollisionOn ptEntryAt at hmcol
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hmcol
  obtain ⟨x₁, hx₁_new, x₂, hx₂_terms, hsh_ne, _, hx₁_pts_imp, _, hbytes_eq⟩ := hmcol
  have ⟨hmemo_pt, hgam_pt_σ⟩ := gamma'_randTerm_32 evictedI0 S g tr.length
  rw [hmemo_pt] at hx₁_new
  rcases List.mem_singleton.mp hx₁_new with rfl
  have hx₁_in_pts :
      randTerm tr.length 32 ∈ plaintextTerms vis ++ [randTerm tr.length 32] :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨hx₂_not_pts, hx₂_inj, hx₂_not_known⟩ := hx₁_pts_imp hx₁_in_pts
  have hb_sigma : g.σ tr.length 32 = ev.input := hgam_pt_σ.symm.trans hgpt
  have hx₂_bytes : x₂.2.2 = ev.input := hbytes_eq.symm.trans hb_sigma
  have hx₂_in_pre :
      x₂ ∈ (prefixTerms r tr vis).flatMap (fun t => (gamma' evictedI0 S g t).memo) := by
    rcases List.mem_append.mp hx₂_terms with hpre | hnew
    · exact hpre
    · rw [hmemo_pt] at hnew
      rcases List.mem_singleton.mp hnew with rfl
      exact absurd rfl hsh_ne
  obtain ⟨t₀, ht₀, hx₂_memo⟩ := List.mem_flatMap.mp hx₂_in_pre
  rcases x₂ with ⟨u, sh, v⟩
  dsimp only at hx₂_not_pts hx₂_inj hx₂_not_known hx₂_bytes
  cases hx₂_bytes
  obtain ⟨hgam_u, hss32⟩ := memo_entry_inv evictedI0 S g t₀ u sh ev.input hx₂_memo
  have htrunc_row : Trunc8RowOK tr (u, sh, gamma evictedI0 S g u) := by
    rw [← hgam_u]
    exact prefixTerms_trunc8OK hex ht₀ (u, sh, ev.input) hx₂_memo
  have hlen_u_pos : 0 < (gamma evictedI0 S g u).length := hgam_u ▸ hlen_pos
  have hlen_u_lt8 : (gamma evictedI0 S g u).length < 8 := hgam_u ▸ hlen_lt8
  obtain ⟨rnd, hview, hsz_ne⟩ :=
    nonRandom_assumedInjective_evictedI0 S g tr u sh
      hx₂_inj hx₂_not_known hss32 htrunc_row hlen_u_pos hlen_u_lt8
  have hpack_u : u = rnd.pack := pack_of_view_eq_some hview
  obtain ⟨hgam_rnd, hrnd_eq⟩ := gamma_randTerm_of_ne_zero evictedI0 S g rnd hsz_ne
  have hb_eq_σ : ev.input = g.σ rnd.timestamp rnd.size := by
    rw [hgam_u, hpack_u, hgam_rnd]
  have hu_eq_rand : u = randTerm rnd.timestamp rnd.size := hpack_u.trans hrnd_eq
  have hwf := hfit.1.1.1
  have hNe : r.alice ≠ r.bob := hwf.1
  have hrnd : RandAt tr rnd.timestamp rnd.size :=
    prefixTerms_termRandAt hex ht₀ u sh ev.input rnd hx₂_memo hview
  by_cases hsetup : rnd.timestamp < (setupTrace r).length
  · have hrnd_s : RandAt (setupTrace r) rnd.timestamp rnd.size :=
      randAt_of_le_of_lt (runSteps_le ss _) hsetup hrnd
    have hsetup_mem := randAt_setupTrace_mem_setupRandomsAt hNe hrnd_s
    have hfresh_eq : g.σ rnd.timestamp rnd.size = r.fresh rnd.timestamp rnd.size :=
      hex.1.1 (rnd.timestamp, rnd.size) hsetup_mem
    have hfresh_b : ev.input = r.fresh rnd.timestamp rnd.size :=
      hb_eq_σ.trans hfresh_eq
    have hfresh_len : (r.fresh rnd.timestamp rnd.size).length = rnd.size :=
      hwf.2.1 (rnd.timestamp, rnd.size) hsetup_mem
    have hge32 : 32 ≤ rnd.size := setupRandomsAt_size_ge_32 hNe hsetup_mem
    have hlen_eq : ev.input.length = rnd.size := by
      rw [hfresh_b, hfresh_len]
    omega
  · rcases matchesEvents_coinDrawn_infix hsz_ne hex.2.2.2 (Nat.not_lt.mp hsetup) hrnd with
      hpt_mem | ⟨v_rng, hv_mem, hv_kind, hsz32, hv_term⟩ |
        ⟨rEv, hrEv_mem, p, hp_infix, v_rng, _, _, hv_lay, hv_terms, hbme⟩
    · exact hx₂_not_pts (List.mem_append_left _ (hu_eq_rand ▸ hpt_mem))
    · have hlen32 : (g.σ rnd.timestamp rnd.size).length = rnd.size :=
        hex.2.1.1 v_rng hv_mem hv_kind rnd.timestamp rnd.size hsz_ne hv_term
      have hlen_eq : ev.input.length = rnd.size := by
        rw [hb_eq_σ, hlen32]
      omega
    · unfold BytesMatchEntry at hbme
      rw [hv_lay, hv_terms] at hbme
      dsimp only [List.map] at hbme
      have hp_eq : gamma evictedI0 S g (randTerm rnd.timestamp rnd.size) = p :=
        List.head_eq_of_cons_eq hbme.2
      have hb_eq_p : ev.input = p := by
        rw [hgam_u, hu_eq_rand, hp_eq]
      exact hno_infix rEv hrEv_mem (hb_eq_p ▸ hp_infix)

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.PtNoCollision
