/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepBase
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins

/-!
# Per-query `CloseByState` step lemmas for `corr`, `transmit`, and `chall`

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves `CloseByState` preservation across `corr`, `transmit`, and `chall` queries under `SimInv`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

theorem HonestEntryInv.toC {P : Params PQ PQC} {Inv : PQ → Prop} {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {epExp : ℕ → BitVec 256} {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInv P Dh encT epExp wc) : HonestEntryInvC P Inv Dh encT epExp wc := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, hd, body, h8, h9, h10, h11, h12, _, h13⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, hd, body, h8, h9, h10, h11, h12, h13⟩

theorem SimInv.toC {P : Params PQ PQC} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))} {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)} {ec : Party → BitVec 256}
    {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp) :
    SimInvC P (fun _ => True) ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp :=
  { h with
    hhon := fun wc hwc => ⟨(h.hhon wc hwc).1.toC, (h.hhon wc hwc).2⟩
    hpqInv := fun _ => trivial }

theorem SimInv.mono_r {P : Params PQ PQC} {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r r' : ℕ}
    {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256}
    {winBefore : ℕ → Bool}
    {epExp : ℕ → BitVec 256}
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hle : r' ≤ r) :
    SimInv P ℓ Dh encPt encT qep q r' x₀ s_R s s_fig8 ec winBefore epExp :=
  { hinv with
    hamb := by have := hinv.hamb; omega
    hamb_strict := fun h => by have := hinv.hamb_strict h; omega
    hidx_le := fun Q => by have := hinv.hidx_le Q; omega
    hhon_len := by have := hinv.hhon_len; omega }

theorem stepR_D0_eq_of_simInvC (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hq : ∀ Qw, q_sm ≠ .inl (.inr Qw)) :
    stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R := by
  refine stepR_configD0_eq_configR1Inj P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep q_sm s_R hq ?_
  intro h10
  rw [hinv.hmeta.hepoch_R] at h10
  rw [hinv.hst_R .A, expectedGhost_chainEpochs]
  exact chainsEpochInvA_contains_zero_false hinv.hchainsA h10

theorem toGhost_congr (P : Params PQ PQC) (s₁ s₂ : SimState PQ Pt ℓ)
    (R : Party) (st : Fig8St Pt)
    (hpn : s₁.pn R = s₂.pn R)
    (hchains : s₁.chains R = s₂.chains R)
    (hunack : R = .A → s₁.unackA = s₂.unackA)
    (hpq : s₁.pq R = s₂.pq R)
    (hep : s₁.mir.epoch R = s₂.mir.epoch R) :
    toGhost P s₁ R st = toGhost P s₂ R st := by
  unfold toGhost
  have hua : (R == Party.A && s₁.unackA) = (R == Party.A && s₂.unackA) := by
    cases R with
    | A => simp [hunack rfl]
    | B => rfl
  simp only [hpn, hchains, hua, hpq, hep]

theorem expectedGhost_congr (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (spkKey : PublicKey)
    (s₁ s₂ : SimState PQ Pt ℓ) (R : Party) (st : Fig8St Pt) (c_eager : BitVec 256)
    (hpn : s₁.pn R = s₂.pn R)
    (hchains : (resolveSim spkKey s₁).chains R = (resolveSim spkKey s₂).chains R)
    (hunack : R = .A → s₁.unackA = s₂.unackA)
    (hpq : s₁.pq R = s₂.pq R)
    (hep : s₁.mir.epoch R = s₂.mir.epoch R)
    (hidx : s₁.mir.idx R = s₂.mir.idx R) :
    expectedGhost P Dh encPt spkKey s₁ R st c_eager =
      expectedGhost P Dh encPt spkKey s₂ R st c_eager := by
  have hinw : inReceiveOnlyEpoch s₁.mir R = inReceiveOnlyEpoch s₂.mir R := by simp [inReceiveOnlyEpoch, hep]
  have htg : toGhost P (resolveSim spkKey s₁) R st = toGhost P (resolveSim spkKey s₂) R st :=
    toGhost_congr P (resolveSim spkKey s₁) (resolveSim spkKey s₂) R st
      hpn hchains hunack hpq hep
  unfold expectedGhost
  dsimp only
  rw [hinw, htg, hidx]

theorem map_epoch_resolve_list (cs : List GhostChain) (k : PublicKey) :
    (cs.map fun g => if g.key.isNone then { g with key := some k } else g).map (·.epoch) =
      cs.map (·.epoch) := by
  rw [List.map_map]
  refine List.map_congr_left fun g _ => ?_
  dsimp only [Function.comp_apply]
  split <;> rfl

theorem simCorr_preserves_simInvC (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r : ℕ)
    (Q : Party) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hcorr_mir : s.mir.corrAllowed Q = true)
    (hinw_mir : inReceiveOnlyEpoch s.mir Q = false)
    (hnospk_mir : SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q = true) :
    let figSt := s_fig8.st Q
    let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    let s' : SimState PQ Pt ℓ := { s with mir := s.mir.afterCorr Q, chains := chains }
    s_R.st Q = toGhost (P := P) { s with chains := chains } Q figSt ∧
    SimInvC P Inv ℓ Dh encPt encT qep q (r - 1) x₀
      (s_R.afterCorr Q) s' (s_fig8.afterCorr Q) ec winBefore epExp := by
  intro figSt chains s'
  have hB0 : Q = .B → s.mir.epoch .B = 0 → figSt.γ = .exp x₀ := by
    intro hQB hep0
    subst hQB
    rcases hinv.hspur .B with ⟨rk_base, T_base, _, hnot_inw, _⟩
    have hγ := (hnot_inw hinw_mir).1
    rw [hep0, hinv.hepExp0] at hγ
    exact hγ
  have hres_eq : resolveSim (encT (Dh.dh x₀ Dh.base)) s' =
      { resolveSim (encT (Dh.dh x₀ Dh.base)) s with mir := s.mir.afterCorr Q } :=
    resolveSim_afterCorr_B_epoch0 Dh encT (encT (Dh.dh x₀ Dh.base)) s Q figSt x₀ rfl hB0
  have hans_eq : s_R.st Q = toGhost (P := P) { s with chains := chains } Q figSt := by
    rw [hinv.hst_R Q, expectedGhost_of_inWin_false _ _ _ _ _ _ _ _ hinw_mir]
    cases Q with
    | B =>
      rw [resolveSim_eq_self_of_B]
      exact (toGhost_congr P { s with chains := chains } s .B figSt rfl
        (by dsimp [chains]; split <;> (try cases figSt.γ) <;> simp [Function.update_of_ne (by decide : Party.B ≠ Party.A)])
        (fun h => nomatch h) rfl rfl).symm
    | A =>
      have h10 : 10 ≤ s.mir.epoch .A := by
        unfold SM.noAliceCorrWhileAliceBelowEpoch10 at hnospk_mir
        simpa using hnospk_mir
      have hchains_A : chains = s.chains := by dsimp [chains]
      rw [hchains_A]
      exact resolveSim_eq_self_of_no_none P _ s .A figSt (chainsEpochInvA_no_none hinv.hchainsA h10)
  have hchains_ep : ∀ R, (chains R).map (·.epoch) = (s.chains R).map (·.epoch) := by
    intro R
    dsimp only [chains]
    split
    · cases figSt.γ with
      | pub _ => rfl
      | exp x =>
        dsimp only
        cases R with
        | A =>
          rw [Function.update_self]
          exact map_epoch_resolve_list (s.chains .A) (encT (Dh.dh x Dh.base))
        | B =>
          rw [Function.update_of_ne (by decide : Party.B ≠ Party.A)]
    · rfl
  refine ⟨hans_eq,
    { hmeta := hinv.hmeta.afterCorr_preserves Q chains
      hcomp := comp_healedBy_false_afterCorr s.mir 3 Q hcorr_mir hinv.hcomp
      hec := hinv.hec
      hwinBefore := hinv.hwinBefore
      hamb := by have := hinv.hamb; dsimp [s']; omega
      hamb_strict := fun h => by have := hinv.hamb_strict h; dsimp [s']; omega
      hidx_le := fun R => by
        change s.mir.idx R + (r - 1) ≤ q
        have := hinv.hidx_le R; omega
      hhon_len := by have := hinv.hhon_len; dsimp [s']; omega
      hep_le := hinv.hep_le
      hep_adj := hinv.hep_adj
      hst_R := by
        intro R
        change s_R.st R = expectedGhost P Dh encPt (encT (Dh.dh x₀ Dh.base)) s' R (s_fig8.st R) (ec R)
        rw [hinv.hst_R R]
        refine expectedGhost_congr P Dh encPt (encT (Dh.dh x₀ Dh.base)) s s' R (s_fig8.st R) (ec R)
          rfl ?_ (fun _ => rfl) rfl rfl rfl
        rw [hres_eq]
      hst_id := hinv.hst_id
      htcur := hinv.htcur
      hepExp0 := hinv.hepExp0
      hspur := by
        intro R
        rcases hinv.hspur R with ⟨rk_base, T_base, h1, h2, h3⟩
        refine ⟨rk_base, T_base, h1, h2, ?_⟩
        intro wc hwc hsend hep_le hnot_mem
        rw [hchains_ep R] at hnot_mem
        exact h3 wc hwc hsend hep_le hnot_mem
      hchainsA := by
        dsimp only [s', chains]
        split
        · cases figSt.γ with
          | pub _ => exact hinv.hchainsA
          | exp x =>
            dsimp only
            rw [Function.update_self]
            exact chainsEpochInvA_resolve hinv.hchainsA (encT (Dh.dh x Dh.base))
        · exact hinv.hchainsA
      hchainsA_ep := by
        change (chains .A).map (·.epoch) = epListA (s.mir.epoch .A / 2)
        rw [hchains_ep .A]
        exact hinv.hchainsA_ep
      hchainsB_ep := by
        change (chains .B).map (·.epoch) = epListB ((s.mir.epoch .B + 1) / 2)
        rw [hchains_ep .B]
        exact hinv.hchainsB_ep
      hchainsB_none := by
        have hB : chains .B = s.chains .B := by
          dsimp only [chains]
          split
          · cases figSt.γ <;> simp [Function.update_of_ne (by decide : Party.B ≠ Party.A)]
          · rfl
        dsimp only [s']
        rw [hB]
        exact hinv.hchainsB_none
      hchains_sync := by
        intro R g' hg'
        by_cases hcond : (Q == Party.B && s.mir.epoch Party.B == 0) = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨hQB, hep0⟩
          have hγ0 : figSt.γ = .exp x₀ := hB0 hQB hep0
          have hchains_eq : chains = Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
              if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) } else g) := by
            simp [chains, hQB, hep0, hγ0]
          cases R with
          | B =>
            change g' ∈ chains .B at hg'
            rw [hchains_eq, Function.update_of_ne (by decide : Party.B ≠ Party.A)] at hg'
            exact hinv.hchains_sync .B g' hg'
          | A =>
            change g' ∈ chains .A at hg'
            rw [hchains_eq, Function.update_self, List.mem_map] at hg'
            rcases hg' with ⟨g, hg, rfl⟩
            rcases hinv.hchains_sync .A g hg with ⟨hgep, hgsend, hgkey, v, hvR, hsync⟩
            have heq_ep : (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) } else g).epoch =
                g.epoch := by split <;> rfl
            have heq_key :
                (if (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) } else g).key.isNone then
                  some (encT (Dh.dh x₀ Dh.base))
                else (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) } else g).key) =
                (if g.key.isNone then some (encT (Dh.dh x₀ Dh.base)) else g.key) := by
              cases hk : g.key <;> simp [hk]
            have hsync' : ChainSync (if g.key.isNone then { g with key := some (encT (Dh.dh x₀ Dh.base)) } else g) v := by
              split
              · exact ⟨hsync.last_eq, hsync.last_lt, hsync.nodup_skipped,
                  hsync.len_skipped, hsync.mem_skipped, hsync.skippedKeys_le⟩
              · exact hsync
            rw [heq_ep, heq_key]
            exact ⟨hgep, hgsend, hgkey, v, hvR, hsync'⟩
        · have hchains_eq : chains = s.chains := by simp [chains, hcond]
          change g' ∈ chains R at hg'
          rw [hchains_eq] at hg'
          exact hinv.hchains_sync R g' hg'
      hhon := hinv.hhon
      htrans_hon := hinv.htrans_hon
      hcoll := hinv.hcoll
      hcorrB0 := hcorrB0_afterCorr hB0 hinv.hcorrB0
      hpqInv := hinv.hpqInv }⟩

/-- One-step `CloseByState` reduction for `corr` queries. -/
theorem closeByState_corr_step {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : SpqrOffCorrectLocal P.spqr)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r)
    (post : α → Bool)
    (Q : Party)
    (cont : Option (GhostState PQ) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inr Q))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  have hD0 := stepR_D0_eq_of_simInv P ℓ Dh encPt encT decT lam qep q r x₀ (.inr Q)
    s_R s s_fig8 ec winBefore epExp hinv (by rintro ⟨_, _⟩ ⟨⟩)
  have hwin_R := hinv.hmeta.hwin_R
  have hwin_mir := hinv.hmeta.hwin_mir
  have hwin_fig8 := hinv.hmeta.hwin_fig8
  have hstop := hinv.hmeta.hstop
  have hcorr_R := hinv.hmeta.corrAllowed_R Q
  have hcorr_fig8 := hinv.hmeta.corrAllowed_fig8 Q
  have hinw_R := hinv.hmeta.inWindow_R Q
  have hnospk_R := hinv.hmeta.noSpkCorr_R Q
  by_cases hguard : (!(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) = true
  · have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inr Q) s_R = pure (none, s_R) := by
      rw [stepR_corr_eq]
      change pure (if (s_R.win || !s_R.corrAllowed Q || (true && inWindow s_R Q) || !noAliceCorrWhileAliceBelowEpoch10 s_R Q) = true
        then (none, s_R) else (some (s_R.st Q), s_R.afterCorr Q)) = pure (none, s_R)
      rw [hwin_R, hcorr_R, hinw_R, hnospk_R, Bool.false_or, Bool.true_and, hguard, ite_eq_left rfl]
    have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) (s, s_fig8) ec =
        pure (none, ((s, s_fig8), ec)) := by
      intro k
      change stepSimEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q (s, s_fig8) ec = _
      unfold stepSimEagerCorr
      rw [stepSim_corr_eq]
      unfold simCorrPure
      dsimp only
      rw [hstop, ite_eq_right Bool.false_ne_true, hwin_mir, Bool.false_or, hguard, ite_eq_left rfl,
          pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
    exact closeByState_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inr Q) cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore none
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R s s_fig8 ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))
  · have hguard_f : (!(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q)) = false :=
      Bool.eq_false_iff.mpr hguard
    have hcorr_mir : s.mir.corrAllowed Q = true := by
      revert hguard_f; cases s.mir.corrAllowed Q <;> simp
    have hinw_mir : inReceiveOnlyEpoch s.mir Q = false := by
      revert hguard_f; cases inReceiveOnlyEpoch s.mir Q <;> simp
    have hnospk_mir : SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q = true := by
      revert hguard_f; cases SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q <;> simp
    set figSt := s_fig8.st Q
    set chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
        match figSt.γ with
        | .exp x => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
            if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
        | _ => s.chains
      else s.chains
    set s' : SimState PQ Pt ℓ := { s with mir := s.mir.afterCorr Q, chains := chains }
    set s_R' := s_R.afterCorr Q
    set s_fig8' := s_fig8.afterCorr Q
    rcases simCorr_preserves_simInvC P (fun _ => True) ℓ Dh encPt encT qep q r Q x₀
      s_R s s_fig8 ec winBefore epExp hinv.toC hcorr_mir hinw_mir hnospk_mir with ⟨hans_eq, hsimC⟩
    have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        (.inr Q) s_R = pure (some (s_R.st Q), s_R') := by
      rw [stepR_corr_eq]
      change pure (if (s_R.win || !s_R.corrAllowed Q || (true && inWindow s_R Q) || !noAliceCorrWhileAliceBelowEpoch10 s_R Q) = true
        then (none, s_R) else (some (s_R.st Q), s_R.afterCorr Q)) = pure (some (s_R.st Q), s_R')
      rw [hwin_R, hcorr_R, hinw_R, hnospk_R, Bool.false_or, Bool.true_and, hguard_f,
          ite_eq_right Bool.false_ne_true]
    have hcorrPure_fig8 : corrPure Q s_fig8 = (some figSt, s_fig8') := by
      unfold corrPure
      rw [hwin_fig8, hcorr_fig8, hcorr_mir]
      rfl
    have hupd_ec : updateAllEagerCoins s.mir s'.mir (fun _ => false) ec = pure ec :=
      updateAllEagerCoins_same_inWin s.mir (s.mir.afterCorr Q) ec rfl rfl hinv.hec
    have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k (.inr Q) (s, s_fig8) ec =
        pure (some (s_R.st Q), ((s', s_fig8'), ec)) := by
      intro k
      change stepSimEagerCorr P ℓ Dh encPt encT decT idOf lam qep k Q (s, s_fig8) ec = _
      unfold stepSimEagerCorr
      rw [stepSim_corr_eq]
      have hsimCorr : simCorrPure P Dh encT Q (s, s_fig8) = (some (s_R.st Q), s', s_fig8') := by
        unfold simCorrPure
        dsimp only
        rw [ite_eq_right (by rw [hstop]; decide), hwin_mir, Bool.false_or, hguard_f,
            ite_eq_right Bool.false_ne_true, hcorrPure_fig8]
        dsimp only
        rw [hans_eq]
        rfl
      rw [hsimCorr, pure_bind, hupd_ec, pure_bind]
    have hrem : remWin qep s'.mir ≤ remWin qep s.mir := by
      simp [remWin, s', winCount_afterCorr_eq]
    refine closeByState_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
      (.inr Q) cont s_R s_R' s s' s_fig8 s_fig8' ec ec winBefore (some (s_R.st Q))
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl hrem ?_
    exact ih (some (s_R.st Q)) s_R' s' s_fig8' ec winBefore epExp { hsimC with hhon := hinv.hhon }

private theorem closeByState_inr_same_amb_bind_const_R {α γ : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s s' : SimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      N >>= fun _ => pure (ans, s_R'))
    (hstepSim : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (s, s_fig8) ec =
      pure (ans, ((s', s_fig8'), ec')))
    (hstepWin : ∀ idx, ¬ idx < s.amb →
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (s, s_fig8) ec =
        pure (ans, ((s', s_fig8'), ec')))
    (hamb : s'.amb = s.amb)
    (hrem : remWin qep s'.mir ≤ remWin qep s.mir)
    (hcont : CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont ans) s_R' s' s_fig8' ec' winBefore) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R s s_fig8 ec winBefore := by
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_
    (closeByRefines_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) hcont)
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _
  · simp only [runSimEager_inr_bind, hstepSim, pure_bind]
  · intro idx _
    exact evalDist_runWinAt_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep
      q_sm cont (s, s_fig8) ec ans (s', s_fig8') ec' hamb hstepWin winBefore idx
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _

private theorem closeByState_inr_same_amb_bind_const_sim {α γ β : Type}
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (N : ProbComp γ) (M : ProbComp β)
    (fR : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (fS : γ → (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm ×
      ((SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
        (Party → BitVec 256)))
    (hans : ∀ x, (fR x).1 = (fS x).1)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      N >>= fun x => pure (fR x))
    (hstepSim : stepSimEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (s, s_fig8) ec =
      N >>= fun x => M >>= fun _ => pure (fS x))
    (hstepWin : ∀ idx, ¬ idx < s.amb →
      stepSimEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (s, s_fig8) ec =
        N >>= fun x => M >>= fun _ => pure (fS x))
    (hamb : ∀ x, (fS x).2.1.1.amb = s.amb)
    (hrem : ∀ x, remWin qep (fS x).2.1.1.mir ≤ remWin qep s.mir)
    (hcont : ∀ x, CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont (fS x).1) (fR x).2 (fS x).2.1.1 (fS x).2.1.2 (fS x).2.2 winBefore) :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R s s_fig8 ec winBefore := by
  unfold CloseByState
  refine closeByRefines_congr_all ?_ ?_ ?_ ?_
    (closeByRefines_bind (q + 1) (stepSlack P encPt Dh q qep δ (remWin qep s.mir)) N
      (fun x => closeByRefines_mono_d (stepSlack_mono P encPt Dh q qep δ (hrem x)) (hcont x)))
  · simp only [runRCont_inr_bind, hstepR, bind_assoc, pure_bind, hans]
  · simp only [runSimEager_inr_bind, hstepSim, bind_assoc, pure_bind]
    refine evalDist_bind_congr N _ _ fun x => ?_
    exact OracleComp.evalDist_bind_const _ _
  · intro idx _
    unfold runWinAt
    cases idx with
    | zero =>
      rw [runSimEager_inr_bind, hstepSim]
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr N _ _ fun x => ?_
      exact OracleComp.evalDist_bind_const _ _
    | succ j =>
      dsimp only
      simp only [hamb]
      split
      · exact (OracleComp.evalDist_bind_const _ _).symm
      · rename_i hnot
        rw [runSimEager_inr_bind, hstepWin j hnot]
        simp only [bind_assoc, pure_bind]
        refine evalDist_bind_congr N _ _ fun x => ?_
        exact OracleComp.evalDist_bind_const _ _
  · simp only [runRCont_inr_bind, hD0, hstepR, bind_assoc, pure_bind, hans]

def samCoin {Coins : Type} [SampleableType Coins] (r : Option Coins) : ProbComp Coins :=
  match r with
  | some rq => pure rq
  | none => ($ᵗ Coins : ProbComp Coins)

theorem samIfNec_bind_eq {Coins β : Type} [SampleableType Coins]
    (r : Option Coins) (f : Coins × Bool → ProbComp β) :
    SM.samIfNec r >>= f = samCoin r >>= fun rq => f (rq, r.isSome) := by
  cases r <;> simp [SM.samIfNec, samCoin, map_eq_bind_pure_comp]

theorem sendsIn_of_inWin_false {ℓ : ℕ}
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hnoBob : SM.noBobSendInEpoch0 mir Q = true) (hinw : inReceiveOnlyEpoch mir Q = false) :
    Q.sendsIn (mir.epoch Q) = true ∧ 1 ≤ mir.epoch Q := by
  unfold inReceiveOnlyEpoch at hinw
  have hs : Q.sendsIn (mir.epoch Q) = true := by
    revert hinw; cases Q.sendsIn (mir.epoch Q) <;> simp
  refine ⟨hs, ?_⟩
  cases h0 : mir.epoch Q with
  | zero =>
    unfold SM.noBobSendInEpoch0 at hnoBob
    cases Q with
    | A => rw [h0] at hs; revert hs; decide
    | B => simp [h0] at hnoBob
  | succ n => omega

theorem sendsIn_succ_of_inWin_true {ℓ : ℕ}
    (mir : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (Q : Party)
    (hinw : inReceiveOnlyEpoch mir Q = true) :
    Q.sendsIn (mir.epoch Q) = false ∧ Q.sendsIn (mir.epoch Q + 1) = true := by
  unfold inReceiveOnlyEpoch at hinw
  have hs : Q.sendsIn (mir.epoch Q) = false := by
    revert hinw; cases Q.sendsIn (mir.epoch Q) <;> simp
  exact ⟨hs, sendsIn_succ_of_not_sendsIn Q (mir.epoch Q) hs⟩

theorem maxActiveEp_eq_of_epoch_eq {ℓ : ℕ}
    (mir mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (R : Party)
    (h : mir'.epoch R = mir.epoch R) :
    maxActiveEp mir' R = maxActiveEp mir R := by
  simp [maxActiveEp, inReceiveOnlyEpoch, h]

theorem maxActiveEp_send_inWin_eq {ℓ : ℕ}
    (mir mir' : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (Q R : Party)
    (hinw : inReceiveOnlyEpoch mir Q = true)
    (hep : mir'.epoch = Function.update mir.epoch Q (mir.epoch Q + 1)) :
    maxActiveEp mir' R = maxActiveEp mir R := by
  by_cases hRQ : R = Q
  · subst hRQ
    have hs := (sendsIn_succ_of_inWin_true mir R hinw).2
    have hinw' : inReceiveOnlyEpoch mir' R = false := by
      simp [inReceiveOnlyEpoch, hep, Function.update_self, hs]
    simp [maxActiveEp, hinw, hinw', hep, Function.update_self]
  · simp [maxActiveEp, inReceiveOnlyEpoch, hep, Function.update_of_ne hRQ]

theorem epMgmt_of_sendsIn_succ_false {St Msg C : Type}
    (s : SM.GameState St Msg C) (Δ qep : ℕ) (Q : Party) (bad : Bool)
    {s₁ : SM.GameState St Msg C}
    (hs : Q.sendsIn (s.epoch Q + 1) = false)
    (hep : s.epMgmt Δ qep Q bad = some s₁) :
    s₁ = s ∧ s.epoch Q ≤ qep := by
  unfold SM.GameState.epMgmt at hep
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
  split at hep
  · cases hep
  · rename_i hnot_lt
    injection hep with hs₁
    exact ⟨hs₁.symm, Nat.le_of_not_lt hnot_lt⟩

theorem epMgmt_of_sendsIn_succ_true {St Msg C : Type}
    (s : SM.GameState St Msg C) (Δ qep : ℕ) (Q : Party) (bad : Bool)
    {s₁ : SM.GameState St Msg C}
    (hs : Q.sendsIn (s.epoch Q + 1) = true)
    (hep : s.epMgmt Δ qep Q bad = some s₁) :
    s₁.epoch = Function.update s.epoch Q (s.epoch Q + 1) ∧
    s₁.idx = Function.update s.idx Q 0 ∧
    s₁.st = s.st ∧
    s₁.corrs = s.corrs ∧
    s₁.maxAcc = s.maxAcc ∧
    s₁.trans = s.trans ∧
    s.epoch Q + 1 ≤ qep := by
  unfold SM.GameState.epMgmt at hep
  simp only [hs, ↓reduceIte] at hep
  split at hep
  · cases hep
  · rename_i hnot_lt
    injection hep with hs₁
    subst hs₁
    by_cases hcond : (bad && !s.safeCh Δ Q) = true <;>
      simp [hcond, SM.GameState.leak, Nat.le_of_not_lt hnot_lt]

private theorem senderOf_eq_of_sendsIn {Q : Party} {t : ℕ}
    (h1 : 1 ≤ t) (hs : Q.sendsIn t = true) :
    Party.senderOf t = Q := by
  cases Q <;> simp [Party.sendsIn, Party.senderOf] at hs ⊢ <;> omega

theorem sendsIn_other_false_of_sendsIn {Q : Party} {t : ℕ}
    (hs : Q.sendsIn t = true) :
    Q.other.sendsIn t = false := by
  cases Q <;> simp [Party.other, Party.sendsIn] at hs ⊢ <;> omega

theorem honestEntryInvC_of_lAead_enc (P : Params PQ PQC) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hrt : RoundTrip.RtHyp P ℓ)
    (epExp : ℕ → BitVec 256) (Q : Party) (t i : ℕ)
    (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hi1 : 1 ≤ i) (hi32 : i < 2 ^ 32)
    (seed : BitVec 256) (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg)) :
    let T := Dh.dh (epExp t) Dh.base
    let ct_aead := ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
      seed (i, (t, some T)) (pub, m)
    let c : Fig8C Pt := ((t, some T), (i, ct_aead))
    HonestEntryInvC P Inv Dh encT epExp (LibsignalSim.toWire c, c) := by
  intro T ct_aead c
  have hsender : Party.senderOf t = Q := by
    cases Q <;> simp [Party.sendsIn, Party.senderOf] at hsends ⊢ <;> omega
  set h_hdr := lHeader encT i (t, some T) pub
  set mk := deriveMessageKeys P.C.F (some pub.salt) (keyToBytes32 seed)
  set body := ((cbcPkcs7EncryptOnly P.C.E ℓ).enc (mk.1.1, mk.1.2) m).toList.flatMap blockToBytesLE
  set ser := (signalWireCodec P.codec).encode h_hdr body
  set tag := (hmacScheme P.C.F).tag mk.2 ((lIds idOf t).toList ++ ser)
  have hct_eq : ct_aead = ((ser, tag), pub.salt) := rfl
  have hc_eq : c = ((t, some T), (i, ((ser, tag), pub.salt))) := rfl
  set w := LibsignalSim.toWire c
  have hw_eq : w = ser ++ tagBytes tag := rfl
  have hser_ge1 : 1 ≤ ser.length := length_signalWireCodec_encode_ge_one P.codec h_hdr body
  have htag_len : (tagBytes tag).length = 8 := length_tagBytes tag
  have hw_len : ¬ w.length < 9 := by
    rw [hw_eq, List.length_append, htag_len]
    omega
  have hw_sub : w.length - 8 = ser.length := by
    rw [hw_eq, List.length_append, htag_len]
    omega
  have htake : w.take (w.length - 8) = ser := by
    rw [hw_sub, hw_eq, List.take_left]
  have hdrop : bytesToWord64LE (w.drop (w.length - 8)) = tag := by
    rw [hw_sub, hw_eq, List.drop_left, tag8_tagBytes]
  have hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h_hdr, body) := by
    rw [htake]
    refine RoundTrip.RtHyp.parse hrt h_hdr body rfl
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (RoundTrip.length_cbcBody _)
    change RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
  have hctr : h_hdr.counter.toNat + 1 = i := by
    change (BitVec.ofNat 32 (i - 1)).toNat + 1 = i
    have hlt : i - 1 < 4294967296 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega
  have hsa : RoundTrip.SentAddrs P pub.addrs := by
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
  have hw32 : w.length < 2 ^ 32 := by
    rw [hw_eq, List.length_append, htag_len]
    exact RoundTrip.RtHyp.encode_length_lt hrt h_hdr body
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) hsa (RoundTrip.length_cbcBody _)
  refine ⟨rfl, hw_len, ht_ge1, ?_, hi1, hi32, rfl, h_hdr, body, hparse, rfl, rfl, hctr, ?_, hw32⟩
  · rw [htake, hdrop]; rfl
  · rw [hsender]
    change addressCheckPasses pub.addrs (P.expectedAddrs Q.other) = true
    rw [haddrs_pub]
    exact addrsOk_send_other P Q unackA

theorem lFig8_send_step_not_inWinC (P : Params PQ PQC) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hrt : RoundTrip.RtHyp P ℓ)
    (epExp : ℕ → BitVec 256) (Q : Party) (st : Fig8St Pt) (t : ℕ)
    (hst_id : st.id = Q) (htcur : st.tcur = t) (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hγ : st.γ = .exp (epExp t)) (hTcur : st.curCkaMsg = some (Dh.dh (epExp t) Dh.base))
    (v : RatchetSenderState (BitVec 256)) (hvS : st.vS = some v) (hv_lt : v.lastIndex + 1 < 2 ^ 32)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg)) :
    let res := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka
    let st' := res.1
    let c := res.2
    st'.id = Q ∧ st'.root = st.root ∧ st'.tcur = t ∧ st'.γ = .exp (epExp t) ∧
    st'.curCkaMsg = some (Dh.dh (epExp t) Dh.base) ∧ st'.vR = st.vR ∧
    (∃ v', st'.vS = some v' ∧ v'.lastIndex = v.lastIndex + 1) ∧
    c.1 = (t, some (Dh.dh (epExp t) Dh.base)) ∧ c.2.1 = v.lastIndex + 1 ∧
    HonestEntryInvC P Inv Dh encT epExp (LibsignalSim.toWire c, c) := by
  have hnot_succ : st.id.sendsIn (st.tcur + 1) = false := by
    rw [hst_id, htcur]
    exact sendsIn_succ_of_sendsIn Q t hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG
  dsimp only
  rw [hnot_succ, ite_eq_right Bool.false_ne_true, hvS, htcur, hTcur]
  refine ⟨hst_id, rfl, rfl, hγ, rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, ?_⟩
  exact honestEntryInvC_of_lAead_enc P Inv Dh encT idOf hrt epExp Q t (v.lastIndex + 1)
    ht_ge1 hsends (by omega) hv_lt _ pub m unackA haddrs_pub hspqr_send

theorem lFig8_send_step_inWinC (P : Params PQ PQC) (Inv : PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hrt : RoundTrip.RtHyp P ℓ)
    (epExp : ℕ → BitVec 256) (Q : Party) (st : Fig8St Pt) (t : ℕ) (T_other : Pt)
    (hst_id : st.id = Q) (htcur : st.tcur + 1 = t) (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hγ : st.γ = .pub T_other)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) (hc_cka : c_cka = epExp t) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg)) :
    let res := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka
    let st' := res.1
    let c := res.2
    st'.id = Q ∧
    st'.root = (rootKdf P.C.F st.root (encPt (Dh.dh (epExp t) T_other))).1 ∧
    st'.tcur = t ∧ st'.γ = .exp (epExp t) ∧
    st'.curCkaMsg = some (Dh.dh (epExp t) Dh.base) ∧ st'.vR = st.vR ∧
    (∃ v', st'.vS = some v' ∧ v'.lastIndex = 1) ∧
    c.1 = (t, some (Dh.dh (epExp t) Dh.base)) ∧ c.2.1 = 1 ∧
    HonestEntryInvC P Inv Dh encT epExp (LibsignalSim.toWire c, c) := by
  have hsends_succ : st.id.sendsIn (st.tcur + 1) = true := by
    rw [hst_id, htcur]; exact hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG dhScheme
  dsimp only
  rw [hsends_succ, ite_eq_left rfl, hγ, hc_cka, htcur]
  dsimp only
  rw [Nat.zero_add]
  refine ⟨hst_id, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, ?_⟩
  exact honestEntryInvC_of_lAead_enc P Inv Dh encT idOf hrt epExp Q t 1
    ht_ge1 hsends (by decide) (by decide) _ pub m unackA haddrs_pub hspqr_send

set_option maxHeartbeats 800000 in
theorem simSendStep_preserves_simInvC_core
    (P : Params PQ PQC) (Inv Inv' : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hq32 : q < 2 ^ 32) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : PQC)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvC P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hspqr_tot : (P.spqr.send (s.pq Q) rq).isSome)
    (hnp : P.spqr.sendPanics (s.pq Q) rq = false)
    (hpq'_inv : ∀ pq' salt pqMsg, P.spqr.send (s.pq Q) rq = some (pq', salt, pqMsg) →
      ∀ R, Inv' (Function.update s.pq Q pq' R))
    (hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q = true)
    (hep_mir : s.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true) :
    let fR := chal.elim
      (transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep Q m₀ rq bad s_R)
      (fun m₁ => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep SM.Config.h1 Q m₀ m₁ rq bad s_R)
    let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq (ec Q) (s, s_fig8)
    let ec' := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
    fR.1 = res.1 ∧
    res.2.1.amb = s.amb ∧
    remWin qep res.2.1.mir ≤ remWin qep s.mir ∧
    (inReceiveOnlyEpoch s.mir Q = true → updateAllEagerCoins s.mir res.2.1.mir (· == Q) ec = pure ec') ∧
    (inReceiveOnlyEpoch s.mir Q = false →
      updateAllEagerCoins s.mir res.2.1.mir (fun _ => false) ec = pure ec' ∧
      ∀ (c_cka : BitVec 256), simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (s, s_fig8) = res) ∧
    SimInvC P Inv' ℓ Dh encPt encT qep q (r - 1) x₀ fR.2 res.2.1 res.2.2 ec' winBefore epExp ∧
    (PosUniq s → HonestIdxLe s → PosUniq res.2.1 ∧ HonestIdxLe res.2.1) ∧
    (SpqrOffCorrectLocal P.spqr →
      (∀ wc ∈ s.honest, HonestEntryInv P Dh encT epExp wc) →
      ∀ wc ∈ res.2.1.honest, HonestEntryInv P Dh encT epExp wc) ∧
    (∃ (pub : LibsignalMsgPublicPart) (m_enc : Plain ℓ) (w : List (BitVec 8)),
      let c := ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) (pub, m_enc) (ec Q)).2
      res.1 = some w ∧
      res.2.1.honest = (w, c) :: s.honest ∧
      res.2.2.st = Function.update s_fig8.st Q
        ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) (pub, m_enc) (ec Q)).1 ∧
      RoundTrip.SentPq P pub.pqmsg ∧
      RoundTrip.SentAddrs P pub.addrs) := by
  intro fR res ec'
  rcases hinv.hmeta.epMgmt_some Q qep bad hep_mir with
    ⟨s_R₁, s_fig8₁, hep_R, hep_fig8, hst_R₁, hst_fig8₁, hmeta₁⟩
  set pn := if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1) else s.pn Q
  rcases Option.isSome_iff_exists.mp hspqr_tot with ⟨⟨pq', salt, pqMsg⟩, hspqr⟩
  set addrs := if Q == Party.A && s.unackA then P.addrAB else none
  set pub : LibsignalMsgPublicPart := ⟨pn, pqMsg, effectiveHkdfSalt32 salt, addrs⟩
  have hmk : LibsignalSim.mkPub (P := P) s Q rq pn = some (pq', pub) := by
    simp [LibsignalSim.mkPub, hspqr, pub, addrs]
  have hpub_pq : RoundTrip.SentPq P pub.pqmsg := Or.inr ⟨_, _, _, _, hspqr⟩
  have hpub_addr : RoundTrip.SentAddrs P pub.addrs := by
    change RoundTrip.SentAddrs P (if (Q == Party.A && s.unackA) = true then P.addrAB else none)
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  set m_enc : Plain ℓ := chal.elim m₀ (fun m₁ => if s_R.b then m₁ else m₀)
  set sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  set out_fig8 := sm.send (s_fig8.st Q) (pub, m_enc) (ec Q)
  set st_fig8' := out_fig8.1
  set c := out_fig8.2
  set w := LibsignalSim.toWire c
  set out_R := P.send (s_R.st Q) m_enc.toList rq
  set st_R' := out_R.1
  set w_R := out_R.2
  set rec_R : SM.Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s_R₁.epoch Q, s_R₁.idx Q + 1⟩, m_enc, w_R⟩
  set rec_mir : SM.Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
  set rec_fig8 : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, m_enc), c⟩
  set s_R' := s_R₁.record 3 Q st_R' rec_R chal.isSome
  set s_fig8' := s_fig8₁.record 3 Q st_fig8' rec_fig8 chal.isSome
  set s' : SimState PQ Pt ℓ :=
    { s with mir := s₁.record 3 Q () rec_mir chal.isSome,
             pq := Function.update s.pq Q pq',
             pn := Function.update s.pn Q pn,
             honest := (w, c) :: s.honest }
  have hfR_eq : fR = (some w_R, s_R') := by
    dsimp only [fR, s_R', rec_R, w_R, st_R', out_R, m_enc]
    cases hchal : chal with
    | none =>
      unfold transmitPure
      rw [hep_R]
      dsimp only [Option.elim, Option.isSome]
      rw [hst_R₁]
      rfl
    | some m₁ =>
      have hsafe_R : (!s_R₁.safeCh 3 Q) = false := by
        rw [hmeta₁.safeCh_R 3 Q, hsafeCh (by simp [hchal])]; rfl
      have hcond_R : (!s_R₁.safeCh 3 Q || !(SM.Config.h1 (Msg := Plain ℓ)).challAllowedIn (s_R₁.epoch Q)) = false := by
        rw [hsafe_R]; rfl
      dsimp only [Option.elim, Option.isSome]
      unfold challPure
      rw [hep_R]
      dsimp only
      rw [hcond_R, ite_eq_right Bool.false_ne_true, hst_R₁]
      rfl
  have hres_c : ∀ (c_cka : BitVec 256),
      simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (s, s_fig8) =
      let out := sm.send (s_fig8.st Q) (pub, m_enc) c_cka
      let w_c := LibsignalSim.toWire out.2
      let rec_m : SM.Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w_c⟩
      (some w_c,
        ({ s with mir := s₁.record 3 Q () rec_m chal.isSome,
                  pq := Function.update s.pq Q pq',
                  pn := Function.update s.pn Q pn,
                  honest := (w_c, out.2) :: s.honest },
         s_fig8₁.record 3 Q out.1 ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, m_enc), out.2⟩ chal.isSome)) := by
    intro c_cka
    unfold simSendStep
    dsimp only
    change (match LibsignalSim.mkPub (P := P) s Q rq pn with | none => _ | some (pq', pub) => _) = _
    rw [hmk]
    dsimp only [m_enc]
    cases hchal : chal with
    | none =>
      unfold transmitPure
      rw [hep_fig8]
      dsimp only [Option.elim, Option.isSome]
      rw [hst_fig8₁]
    | some m₁ =>
      have hsafe_f : (!s_fig8₁.safeCh 3 Q) = false := by
        rw [hmeta₁.safeCh_fig8 3 Q, hsafeCh (by simp [hchal])]; rfl
      have hcond_f : (!s_fig8₁.safeCh 3 Q || !(SM.Config.h1 (Msg := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s_fig8₁.epoch Q)) = false := by
        rw [hsafe_f]; rfl
      have hmb : (if s_fig8.b = true then (pub, m₁) else (pub, m₀)) =
          (pub, if s_R.b = true then m₁ else m₀) := by
        rw [← hinv.hmeta.hb]
        cases s_R.b <;> rfl
      have hz_eq : challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka bad s_fig8 =
          let out := sm.send (s_fig8.st Q) (pub, if s_R.b = true then m₁ else m₀) c_cka
          (some out.2, s_fig8₁.record 3 Q out.1
            ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, if s_R.b = true then m₁ else m₀), out.2⟩ true) := by
        unfold challPure
        rw [hep_fig8]
        dsimp only
        rw [hcond_f, ite_eq_right Bool.false_ne_true, hst_fig8₁]
        change (let m := if s_fig8.b = true then (pub, m₁) else (pub, m₀);
          let out := sm.send (s_fig8.st Q) m c_cka;
          (some out.2, s_fig8₁.record 3 Q out.1 ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, m, out.2⟩ true)) = _
        rw [hmb]
      dsimp only [Option.elim, Option.isSome]
      rw [hz_eq]
  have hres_eq : res = (some w, (s', s_fig8')) := hres_c (ec Q)
  set spkKey := encT (Dh.dh x₀ Dh.base)
  have hM := libX25519Rel_model hX
  letI : DecidableEq PQ := Classical.decEq PQ
  have hs'_ep : s'.mir.epoch = s₁.epoch := rfl
  have hs'_idx_Q : s'.mir.idx Q = s₁.idx Q + 1 := by
    change Function.update s₁.idx Q (s₁.idx Q + 1) Q = s₁.idx Q + 1
    exact Function.update_self Q (s₁.idx Q + 1) s₁.idx
  have hcore :
      w_R = w ∧
      st_R' = toGhost P (resolveSim spkKey s') Q st_fig8' ∧
      inReceiveOnlyEpoch s'.mir Q = false ∧
      inReceiveOnlyEpoch s'.mir Q.other = inReceiveOnlyEpoch s.mir Q.other ∧
      (∀ R, maxActiveEp s'.mir R = maxActiveEp s.mir R) ∧
      Q.sendsIn (s₁.epoch Q) = true ∧
      1 ≤ s₁.epoch Q ∧
      s₁.epoch Q ≤ qep ∧
      s₁.epoch Q.other = s.mir.epoch Q.other ∧
      s₁.idx Q.other = s.mir.idx Q.other ∧
      (s₁.epoch Q = s.mir.epoch Q ∧ s₁.idx Q = s.mir.idx Q ∨ s₁.epoch Q = s.mir.epoch Q + 1 ∧ s₁.idx Q = 0) ∧
      s'.mir.idx Q + (r - 1) ≤ q ∧
      (∀ R, s.mir.epoch R ≤ s'.mir.epoch R) ∧
      (∀ R, (inReceiveOnlyEpoch s'.mir R = true → s'.mir.epoch R ≤ s'.mir.epoch R.other) ∧
        s'.mir.epoch R ≤ s'.mir.epoch R.other + 1) ∧
      st_fig8'.id = Q ∧
      st_fig8'.tcur = s₁.epoch Q ∧
      st_fig8'.vR = (s_fig8.st Q).vR ∧
      c.1 = (s₁.epoch Q, some (Dh.dh (epExp (s₁.epoch Q)) Dh.base)) ∧
      c.2.1 = s₁.idx Q + 1 ∧
      HonestEntryInvC P Inv' Dh encT epExp (w, c) ∧
      (SpqrOffCorrectLocal P.spqr → HonestEntryInv P Dh encT epExp (w, c)) ∧
      ChainsEpochInvA (s'.mir.epoch .A) (s.chains .A) ∧
      (s.chains .A).map (·.epoch) = epListA (s'.mir.epoch .A / 2) ∧
      (s.chains .B).map (·.epoch) = epListB ((s'.mir.epoch .B + 1) / 2) ∧
      (inReceiveOnlyEpoch s.mir Q = false → ∀ (c_cka : BitVec 256), sm.send (s_fig8.st Q) (pub, m_enc) c_cka = out_fig8) ∧
      (∃ rk_base T_base,
        (inReceiveOnlyEpoch s'.mir Q = true →
          st_fig8'.root = rk_base ∧ st_fig8'.γ = .pub T_base ∧ T_base ≠ 0 ∧
          epExp (s'.mir.epoch Q + 1) = ec' Q) ∧
        (inReceiveOnlyEpoch s'.mir Q = false →
          st_fig8'.γ = .exp (epExp (s'.mir.epoch Q)) ∧
          (0 < s'.mir.epoch Q →
            st_fig8'.root = (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (s'.mir.epoch Q)) T_base))).1 ∧
            st_fig8'.curCkaMsg = some (Dh.dh (epExp (s'.mir.epoch Q)) Dh.base)) ∧
          ∃ vS, st_fig8'.vS = some vS ∧ vS.lastIndex = s'.mir.idx Q) ∧
        (∀ wc ∈ (w, c) :: s.honest, Party.senderOf wc.2.1.1 = Q.other →
          wc.2.1.1 ≤ s'.mir.epoch Q → wc.2.1.1 ∉ (s.chains Q).map (·.epoch) →
          0 < s'.mir.epoch Q ∧
          spurBadSingle P encPt Dh Q rk_base T_base wc.1 wc.2.2.2.2 (epExp wc.2.1.1)
            (epExp (maxActiveEp s'.mir Q)) = false)) := by
    cases hinw : inReceiveOnlyEpoch s.mir Q with
    | false =>
      rcases sendsIn_of_inWin_false s.mir Q hnoBob_mir hinw with ⟨hsends, ht_ge1⟩
      have hsends_succ : Q.sendsIn (s.mir.epoch Q + 1) = false :=
        sendsIn_succ_of_sendsIn Q (s.mir.epoch Q) hsends
      rcases epMgmt_of_sendsIn_succ_false s.mir 3 qep Q bad hsends_succ hep_mir with ⟨hs₁_eq, hep_le_qep⟩
      subst hs₁_eq
      have hpn_eq : pn = s.pn Q := ite_eq_right (not_not.mpr rfl)
      have hpn_upd : Function.update s.pn Q pn = s.pn := by
        rw [hpn_eq]; exact Function.update_eq_self Q s.pn
      rcases hinv.hspur Q with ⟨rk_base, T_base, _, hinw_f, hspur_hon⟩
      rcases hinw_f hinw with ⟨hγ, hpos_ep, v, hvS, hv_last⟩
      rcases hpos_ep (by omega) with ⟨hroot, hTcur⟩
      have hidx_Q := hinv.hidx_le Q
      have hv_lt : v.lastIndex + 1 < 2 ^ 32 := by omega
      have hstep_fig8 := lFig8_send_step_not_inWinC P Inv' Dh encPt encT idOf lam hrt
        epExp Q (s_fig8.st Q) (s.mir.epoch Q) (hinv.hst_id Q) (hinv.htcur Q) ht_ge1 hsends
        hγ hTcur v hvS hv_lt pub m_enc (ec Q) s.unackA rfl hspqr
      rcases hstep_fig8 with ⟨hid', hroot', htcur', hγ', hTcur', hvR', ⟨v', hvS', hv'_last⟩, hc1, hc2, hhon_wc⟩
      have hhon_wc_off : SpqrOffCorrectLocal P.spqr → HonestEntryInv P Dh encT epExp (w, c) :=
        fun hS_off => (lFig8_send_step_not_inWin P Dh encPt encT idOf lam hrt hS_off
          epExp Q (s_fig8.st Q) (s.mir.epoch Q) (hinv.hst_id Q) (hinv.htcur Q) ht_ge1 hsends
          hγ hTcur v hvS hv_lt pub m_enc (ec Q) s.unackA rfl hspqr rfl).2.2.2.2.2.2.2.2.2
      have hT_pub : ((s_fig8.st Q).curCkaMsg.map encT).getD dummyKey =
          (KeyPair.generate P.C (epExp (s.mir.epoch Q))).publicKey := by
        rw [hTcur, Option.map_some, Option.getD_some, keyPair_generate_publicKey hX]
      have hsend_ghost := send_toGhost_eq P Dh encPt encT idOf lam hid
        (resolveSim spkKey s) Q (s_fig8.st Q) (hinv.hst_id Q) (hinv.htcur Q).symm
        (epExp (s.mir.epoch Q)) hγ v hvS (by omega) hT_pub
        (by rw [hinv.htcur Q]; exact hsends) m_enc rq pq' salt pqMsg hspqr hnp
        s'.mir (hinv.htcur Q).symm ((w, c) :: s.honest) (ec Q)
      have hst_R_eq : s_R.st Q = toGhost P (resolveSim spkKey s) Q (s_fig8.st Q) := by
        rw [hinv.hst_R Q, expectedGhost_of_inWin_false _ _ _ _ _ _ _ _ hinw]
      have hpub_eq : (⟨(resolveSim spkKey s).pn Q, pqMsg, effectiveHkdfSalt32 salt,
          if Q == Party.A && (resolveSim spkKey s).unackA then P.addrAB else none⟩ : LibsignalMsgPublicPart) = pub := by
        simp [pub, hpn_eq, resolveSim_pn, resolveSim_unackA, addrs]
      have hres_s'_eq :
          { (resolveSim spkKey s) with
              mir := s'.mir,
              pq := Function.update (resolveSim spkKey s).pq Q pq',
              honest := (w, c) :: s.honest } = resolveSim spkKey s' := by
        simp [s', resolveSim, hpn_upd]
      rw [← hst_R_eq] at hsend_ghost
      dsimp only at hsend_ghost
      rw [hpub_eq, hres_s'_eq] at hsend_ghost
      have hout_R_eq : out_R = (toGhost P (resolveSim spkKey s') Q st_fig8', w) := hsend_ghost
      have hw_R_eq : w_R = w := congrArg Prod.snd hout_R_eq
      have hst_R'_eq : st_R' = toGhost P (resolveSim spkKey s') Q st_fig8' := congrArg Prod.fst hout_R_eq
      have hcoins_eq : ∀ c_cka, sm.send (s_fig8.st Q) (pub, m_enc) c_cka = out_fig8 := by
        intro c_cka
        exact scheme_send_coins_eq_of_not_sendsIn _ _ _ (s_fig8.st Q) (pub, m_enc) c_cka (ec Q)
          (by rw [hinv.hst_id Q, hinv.htcur Q]; exact hsends_succ)
      have hinw'_eq : ∀ R, inReceiveOnlyEpoch s'.mir R = inReceiveOnlyEpoch s.mir R := fun R => by
        dsimp [inReceiveOnlyEpoch]; rw [hs'_ep]
      have hmaxActive : ∀ R, maxActiveEp s'.mir R = maxActiveEp s.mir R :=
        fun R => maxActiveEp_eq_of_epoch_eq s'.mir s.mir R (congrFun hs'_ep R)
      refine ⟨hw_R_eq, hst_R'_eq, by rw [hinw'_eq Q, hinw], hinw'_eq Q.other, hmaxActive,
        hsends, ht_ge1, hep_le_qep,
        rfl, rfl, Or.inl ⟨rfl, rfl⟩, ?_, fun _ => le_rfl, hinv.hep_adj, hid', htcur', hvR', hc1, ?_,
        hhon_wc, hhon_wc_off, hinv.hchainsA, hinv.hchainsA_ep, hinv.hchainsB_ep, fun _ => hcoins_eq,
        ⟨rk_base, T_base, ?_, ?_, ?_⟩⟩
      · rw [hs'_idx_Q]; omega
      · rw [hc2, hv_last]
      · intro h; rw [hinw'_eq Q, hinw] at h; cases h
      · intro _
        rw [hs'_ep, hs'_idx_Q]
        exact ⟨hγ', fun _ => ⟨by rw [hroot', hroot], hTcur'⟩, v', hvS', by rw [hv'_last, hv_last]⟩
      · intro wc hwc hsender hle hnot_mem
        rw [hs'_ep] at hle ⊢
        rw [hmaxActive Q]
        rcases List.mem_cons.mp hwc with rfl | hwc
        · have hsender_Q : Party.senderOf c.1.1 = Q := by
            rw [congrArg Prod.fst hc1]
            exact senderOf_eq_of_sendsIn ht_ge1 hsends
          rw [hsender_Q] at hsender
          cases Q <;> cases hsender
        · exact hspur_hon wc hwc hsender hle hnot_mem
    | true =>
      rcases sendsIn_succ_of_inWin_true s.mir Q hinw with ⟨hrecv, hsends_succ⟩
      rcases epMgmt_of_sendsIn_succ_true s.mir 3 qep Q bad hsends_succ hep_mir with
        ⟨hs₁_ep, hs₁_idx, _, _, _, _, hep_le_qep⟩
      have hs₁_ep_Q : s₁.epoch Q = s.mir.epoch Q + 1 := by
        rw [hs₁_ep, Function.update_self]
      have hs₁_ep_other : s₁.epoch Q.other = s.mir.epoch Q.other := by
        rw [hs₁_ep, Function.update_of_ne (Party.other_ne Q)]
      have hs₁_idx_Q : s₁.idx Q = 0 := by
        rw [hs₁_idx, Function.update_self]
      have hs₁_idx_other : s₁.idx Q.other = s.mir.idx Q.other := by
        rw [hs₁_idx, Function.update_of_ne (Party.other_ne Q)]
      have hpn_eq : pn = BitVec.ofNat 32 (s.mir.idx Q - 1) :=
        ite_eq_left (by omega)
      rcases hinv.hspur Q with ⟨rk_base, T_base, hinw_t, _, hspur_hon⟩
      rcases hinw_t hinw with ⟨hroot, hγ, hT_ne0, hepExp_ec⟩
      have ht_ge1 : 1 ≤ s₁.epoch Q := by omega
      have hsends_s₁ : Q.sendsIn (s₁.epoch Q) = true := by
        rw [hs₁_ep_Q]; exact hsends_succ
      have hstep_fig8 := lFig8_send_step_inWinC P Inv' Dh encPt encT idOf lam hrt
        epExp Q (s_fig8.st Q) (s₁.epoch Q) T_base (hinv.hst_id Q)
        (by rw [hinv.htcur Q, hs₁_ep_Q]) ht_ge1 hsends_s₁ hγ pub m_enc (ec Q)
        (by rw [hs₁_ep_Q, hepExp_ec]) s.unackA rfl hspqr
      rcases hstep_fig8 with ⟨hid', hroot', htcur', hγ', hTcur', hvR', ⟨v', hvS', hv'_last⟩, hc1, hc2, hhon_wc⟩
      have hhon_wc_off : SpqrOffCorrectLocal P.spqr → HonestEntryInv P Dh encT epExp (w, c) :=
        fun hS_off => (lFig8_send_step_inWin P Dh encPt encT idOf lam hrt hS_off
          epExp Q (s_fig8.st Q) (s₁.epoch Q) T_base (hinv.hst_id Q)
          (by rw [hinv.htcur Q, hs₁_ep_Q]) ht_ge1 hsends_s₁ hγ pub m_enc (ec Q)
          (by rw [hs₁_ep_Q, hepExp_ec]) s.unackA rfl hspqr rfl).2.2.2.2.2.2.2.2.2
      have hsend_ghost := send_withEager_toGhost_eq P Dh encPt encT idOf lam hX hid
        (resolveSim spkKey s) Q (s_fig8.st Q) (hinv.hst_id Q) (hinv.htcur Q).symm
        T_base hγ (by rw [hinv.htcur Q]; exact hrecv) pn m_enc rq pq' salt pqMsg hspqr
        hnp
        s'.mir (by rw [hs'_ep, hs₁_ep_Q, hinv.htcur Q])
        ((w, c) :: s.honest) (ec Q)
      have hst_R_eq : s_R.st Q =
          withEager (toGhost P (resolveSim spkKey s) Q (s_fig8.st Q))
            ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (ec Q) T_base)).1
            (some ⟨KeyPair.generate P.C (ec Q),
              ⟨((rootPRNG P.C.F encPt).up (s_fig8.st Q).root (Dh.dh (ec Q) T_base)).2, 0⟩⟩) pn := by
        rw [hinv.hst_R Q, expectedGhost_of_inWin_true _ _ _ _ _ _ _ _ T_base hinw hγ, hpn_eq]
      have hpub_eq : (⟨pn, pqMsg, effectiveHkdfSalt32 salt,
          if Q == Party.A && (resolveSim spkKey s).unackA then P.addrAB else none⟩ : LibsignalMsgPublicPart) = pub := by
        simp [pub, resolveSim_unackA, addrs]
      have hres_s'_eq :
          { (resolveSim spkKey s) with
              mir := s'.mir,
              pq := Function.update (resolveSim spkKey s).pq Q pq',
              pn := Function.update (resolveSim spkKey s).pn Q pn,
              honest := (w, c) :: s.honest } = resolveSim spkKey s' := by
        simp [s', resolveSim]
      dsimp only at hsend_ghost
      rw [← hst_R_eq, hpub_eq, hres_s'_eq] at hsend_ghost
      have hout_R_eq : out_R = (toGhost P (resolveSim spkKey s') Q st_fig8', w) := hsend_ghost
      have hw_R_eq : w_R = w := congrArg Prod.snd hout_R_eq
      have hst_R'_eq : st_R' = toGhost P (resolveSim spkKey s') Q st_fig8' := congrArg Prod.fst hout_R_eq
      have hinw'_Q : inReceiveOnlyEpoch s'.mir Q = false := by
        dsimp [inReceiveOnlyEpoch]; rw [hs'_ep, hsends_s₁]; rfl
      have hinw'_other : inReceiveOnlyEpoch s'.mir Q.other = inReceiveOnlyEpoch s.mir Q.other := by
        dsimp [inReceiveOnlyEpoch]; rw [hs'_ep, hs₁_ep_other]
      have hmaxActive : ∀ R, maxActiveEp s'.mir R = maxActiveEp s.mir R :=
        fun R => maxActiveEp_send_inWin_eq s.mir s'.mir Q R hinw (by rw [hs'_ep, hs₁_ep])
      have hep_Q_le_other : s.mir.epoch Q ≤ s.mir.epoch Q.other := (hinv.hep_adj Q).1 hinw
      have hs₁_le_qep : s₁.epoch Q ≤ qep := by rw [hs₁_ep_Q]; exact hep_le_qep
      refine ⟨hw_R_eq, hst_R'_eq, hinw'_Q, hinw'_other, hmaxActive, hsends_s₁, ht_ge1, hs₁_le_qep,
        hs₁_ep_other, hs₁_idx_other, Or.inr ⟨hs₁_ep_Q, hs₁_idx_Q⟩, ?_, ?_, ?_, hid', htcur', hvR', hc1, ?_,
        hhon_wc, hhon_wc_off, ?_, ?_, ?_, (fun h => by cases h), ⟨rk_base, T_base, ?_, ?_, ?_⟩⟩
      · rw [hs'_idx_Q, hs₁_idx_Q]
        have := hinv.hidx_le Q
        omega
      · intro R
        rw [hs'_ep]
        by_cases hRQ : R = Q
        · subst hRQ; omega
        · rw [hs₁_ep, Function.update_of_ne hRQ]
      · intro R
        by_cases hRQ : R = Q
        · subst hRQ
          refine ⟨(fun h => by rw [hinw'_Q] at h; cases h), ?_⟩
          rw [hs'_ep, hs₁_ep_Q, hs₁_ep_other]
          omega
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          have hadj_O := (hinv.hep_adj Q.other).2
          rw [Party.other_other] at hadj_O
          rw [hs'_ep, Party.other_other, hs₁_ep_other, hs₁_ep_Q]
          exact ⟨fun _ => hadj_O, by omega⟩
      · rw [hc2, hs₁_idx_Q]
      · rw [hs'_ep]
        cases Q with
        | A =>
          rw [hs₁_ep_Q]
          exact chainsEpochInvA_send_step hinv.hchainsA hsends_succ
        | B =>
          change s₁.epoch .A = s.mir.epoch .A at hs₁_ep_other
          rw [hs₁_ep_other]
          exact hinv.hchainsA
      · rw [hs'_ep]
        cases Q with
        | A =>
          have hmod : (s.mir.epoch .A + 1) % 2 = 1 := by
            simpa [Party.sendsIn] using hsends_succ
          have hdiv : (s.mir.epoch .A + 1) / 2 = s.mir.epoch .A / 2 := by omega
          rw [hs₁_ep_Q, hdiv]
          exact hinv.hchainsA_ep
        | B =>
          change s₁.epoch .A = s.mir.epoch .A at hs₁_ep_other
          rw [hs₁_ep_other]
          exact hinv.hchainsA_ep
      · rw [hs'_ep]
        cases Q with
        | A =>
          change s₁.epoch .B = s.mir.epoch .B at hs₁_ep_other
          rw [hs₁_ep_other]
          exact hinv.hchainsB_ep
        | B =>
          have hmod : (s.mir.epoch .B + 1) % 2 = 0 := by
            simpa [Party.sendsIn] using hsends_succ
          have hdiv : (s.mir.epoch .B + 1 + 1) / 2 = (s.mir.epoch .B + 1) / 2 := by omega
          rw [hs₁_ep_Q, hdiv]
          exact hinv.hchainsB_ep
      · intro h; rw [hinw'_Q] at h; cases h
      · intro _
        rw [hs'_ep, hs'_idx_Q]
        refine ⟨hγ', fun _ => ⟨by rw [hroot', hroot], hTcur'⟩, v', hvS', ?_⟩
        rw [hv'_last, hs₁_idx_Q]
      · intro wc hwc hsender hle hnot_mem
        rw [hs'_ep] at hle ⊢
        rw [hmaxActive Q]
        rcases List.mem_cons.mp hwc with rfl | hwc
        · have hsender_Q : Party.senderOf c.1.1 = Q := by
            rw [congrArg Prod.fst hc1]
            exact senderOf_eq_of_sendsIn ht_ge1 hsends_s₁
          rw [hsender_Q] at hsender
          cases Q <;> cases hsender
        · have hwc_sends : (Party.senderOf wc.2.1.1).sendsIn wc.2.1.1 = true :=
            (hinv.hhon wc hwc).2.2.1
          rw [hsender] at hwc_sends
          have hne_s₁ : wc.2.1.1 ≠ s₁.epoch Q := by
            intro heq
            rw [heq] at hwc_sends
            have := sendsIn_other_false_of_sendsIn hsends_s₁
            rw [this] at hwc_sends
            cases hwc_sends
          have hle_old : wc.2.1.1 ≤ s.mir.epoch Q := by omega
          rcases hspur_hon wc hwc hsender hle_old hnot_mem with ⟨_, hbad⟩
          exact ⟨by omega, hbad⟩
  rcases hcore with ⟨hw_R_eq, hst_R'_eq, hinw'_Q, hinw'_other, hmaxActive, hsends_s₁, ht_ge1,
    hep_le_qep, hs₁_ep_other, hs₁_idx_other, hs₁_cases, hidx_Q_bound, hep_mono, hep_adj', hid', htcur',
    hvR', hc1, hc2, hhon_wc, hhon_wc_off, hchainsA', hchainsA_ep', hchainsB_ep', hcoins_eq, hspur'_Q⟩
  have hrem : remWin qep s'.mir ≤ remWin qep s.mir := by
    dsimp [remWin, s']
    rw [winCount_record_eq, winCount_epMgmt_eq hep_mir]
  have hupd_true : inReceiveOnlyEpoch s.mir Q = true →
      updateAllEagerCoins s.mir s'.mir (· == Q) ec = pure ec' := by
    intro hinw
    dsimp only [ec']
    rw [hinw, ite_eq_left rfl]
    exact (updateAllEagerCoins_send_inWin Q s.mir s'.mir ec hinw hinw'_Q hinw'_other hinv.hec).1
  have hupd_false : inReceiveOnlyEpoch s.mir Q = false →
      updateAllEagerCoins s.mir s'.mir (fun _ => false) ec = pure ec' ∧
      ∀ (c_cka : BitVec 256), simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (s, s_fig8) =
        res := by
    intro hinw
    dsimp only [ec']
    rw [hinw, ite_eq_right Bool.false_ne_true]
    have hA : inReceiveOnlyEpoch s'.mir .A = inReceiveOnlyEpoch s.mir .A := by
      cases Q with
      | A => rw [hinw'_Q, hinw]
      | B => exact hinw'_other
    have hB : inReceiveOnlyEpoch s'.mir .B = inReceiveOnlyEpoch s.mir .B := by
      cases Q with
      | A => exact hinw'_other
      | B => rw [hinw'_Q, hinw]
    refine ⟨updateAllEagerCoins_same_inWin s.mir s'.mir ec hA hB hinv.hec, fun c_cka => ?_⟩
    rw [hres_c c_cka]
    dsimp only
    rw [hcoins_eq hinw c_cka, hres_eq]
  have hf1 : fR.1 = res.1 := by
    rw [congrArg Prod.fst hfR_eq, congrArg Prod.fst hres_eq, hw_R_eq]
  have hf2 : res.2.1.amb = s.amb := by
    rw [congrArg (fun x => x.2.1.amb) hres_eq]
  have hres_mir : res.2.1.mir = s'.mir := congrArg (fun x => x.2.1.mir) hres_eq
  refine ⟨hf1, hf2, hres_mir.symm ▸ hrem, hres_mir.symm ▸ hupd_true, hres_mir.symm ▸ hupd_false, ?_⟩
  have hfR2 : fR.2 = s_R' := congrArg Prod.snd hfR_eq
  have hres1 : res.1 = some w := congrArg Prod.fst hres_eq
  have hres21 : res.2.1 = s' := congrArg (fun x => x.2.1) hres_eq
  have hres22 : res.2.2 = s_fig8' := congrArg (fun x => x.2.2) hres_eq
  rw [hfR2, hres21, hres22]
  have hc1_ep : c.1.1 = s₁.epoch Q := congrArg Prod.fst hc1
  have hsender_Q : Party.senderOf c.1.1 = Q := by
    rw [hc1_ep]; exact senderOf_eq_of_sendsIn ht_ge1 hsends_s₁
  suffices hsimC :
      SimInvC P Inv' ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore epExp by
    refine ⟨hsimC, ?_, ?_, ?_⟩
    · intro huniq hidx
      have hold_bound : ∀ wc ∈ s.honest, wc.2.1.1 = s₁.epoch Q → wc.2.2.1 ≤ s₁.idx Q := by
        intro wc hwc heq_ep
        have hle_old := (hinv.hhon wc hwc).2.2.2
        have hsend_wc : Party.senderOf wc.2.1.1 = Q := by
          rw [heq_ep, ← hc1_ep, hsender_Q]
        rw [hsend_wc, heq_ep] at hle_old
        rcases hs₁_cases with ⟨hep_eq, hidx_eq⟩ | ⟨hep_succ, _⟩
        · rw [hidx_eq]
          have h := hidx wc hwc (by rw [hsend_wc, heq_ep, hep_eq])
          rwa [hsend_wc] at h
        · omega
      refine ⟨?_, ?_⟩
      · intro wc₁ h₁ wc₂ h₂ ht hi
        rcases List.mem_cons.mp h₁ with rfl | h₁
        · rcases List.mem_cons.mp h₂ with rfl | h₂
          · rfl
          · exfalso
            have hle := hold_bound wc₂ h₂ (by rw [← ht, hc1_ep])
            dsimp only at hi
            rw [hc2] at hi
            omega
        · rcases List.mem_cons.mp h₂ with rfl | h₂
          · exfalso
            have hle := hold_bound wc₁ h₁ (by rw [ht, hc1_ep])
            dsimp only at hi
            rw [hc2] at hi
            omega
          · exact huniq wc₁ h₁ wc₂ h₂ ht hi
      · intro wc hwc ht
        rcases List.mem_cons.mp hwc with rfl | hwc
        · dsimp only
          rw [hsender_Q, hs'_idx_Q, hc2]
        · by_cases hRQ : Party.senderOf wc.2.1.1 = Q
          · rw [hRQ] at ht ⊢
            change wc.2.1.1 = s₁.epoch Q at ht
            have hle := hold_bound wc hwc ht
            rw [hs'_idx_Q]
            omega
          · have hRO : Party.senderOf wc.2.1.1 = Q.other := by
              cases Q <;> cases h : Party.senderOf wc.2.1.1 <;>
                first | exact absurd h hRQ | rfl
            have hep_O : s'.mir.epoch (Party.senderOf wc.2.1.1) = s.mir.epoch (Party.senderOf wc.2.1.1) := by
              rw [hRO]; exact hs₁_ep_other
            have hidx_O : s'.mir.idx (Party.senderOf wc.2.1.1) = s.mir.idx (Party.senderOf wc.2.1.1) := by
              rw [hRO]
              change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
              rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
            rw [hep_O] at ht
            rw [hidx_O]
            exact hidx wc hwc ht
    · intro hS_off hold wc hwc
      rcases List.mem_cons.mp hwc with rfl | hwc
      · exact hhon_wc_off hS_off
      · exact hold wc hwc
    · refine ⟨pub, m_enc, w, hres1, rfl, ?_, hpub_pq, hpub_addr⟩
      funext R
      change Function.update s_fig8₁.st Q st_fig8' R = Function.update s_fig8.st Q st_fig8' R
      by_cases hRQ : R = Q
      · subst hRQ; simp
      · simp [Function.update_of_ne hRQ, hst_fig8₁]
  have hmeta' : SameMeta s_R' s' s_fig8' := by
    have hrec_R_eq : rec_R = ⟨⟨Q, s_R₁.epoch Q, s_R₁.idx Q + 1⟩, m_enc, w⟩ := by
      simp [rec_R, hw_R_eq]
    have hs'_eq : s' = {
        mir := s₁.record 3 Q () rec_mir chal.isSome,
        pq := Function.update s.pq Q pq', pn := Function.update s.pn Q pn,
        unackA := s.unackA, honest := (w, c) :: s.honest,
        chains := s.chains, amb := s.amb, stopped := false } := by
      simp [s', hinv.hmeta.hstop]
    change SameMeta (s_R₁.record 3 Q st_R' rec_R chal.isSome) s'
      (s_fig8₁.record 3 Q st_fig8' ⟨⟨Q, s_fig8₁.epoch Q, s_fig8₁.idx Q + 1⟩, (pub, m_enc), c⟩ chal.isSome)
    rw [hrec_R_eq, hs'_eq]
    exact hmeta₁.record_preserves Q st_R' st_fig8' m_enc m₀ (pub, m_enc) c chal.isSome
      (Function.update s.pq Q pq') (Function.update s.pn Q pn) s.unackA
      ((w, c) :: s.honest) s.chains s.amb
  have hcomp₁ : ∀ p ∈ s₁.comp, SM.healedBy s₁.tL 3 p.epoch = false :=
    comp_healedBy_false_epMgmt hinv.hcomp hep_mir
  have hcomp' : ∀ p ∈ s'.mir.comp, SM.healedBy s'.mir.tL 3 p.epoch = false :=
    comp_healedBy_false_record s₁ 3 Q () rec_mir chal.isSome rfl hcomp₁
  have hec' : ValidEagerCoins s'.mir ec' := by
    dsimp only [ec']
    cases hinw : inReceiveOnlyEpoch s.mir Q with
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      intro R hR
      by_cases hRQ : R = Q
      · subst hRQ; rw [hinw'_Q] at hR; exact hinv.hec R (hinw ▸ hR)
      · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
        subst hRO; rw [hinw'_other] at hR; exact hinv.hec Q.other hR
    | true =>
      rw [ite_eq_left rfl]
      exact (updateAllEagerCoins_send_inWin Q s.mir s'.mir ec hinw hinw'_Q hinw'_other hinv.hec).2
  refine
    { hmeta := hmeta'
      hcomp := hcomp'
      hec := hec'
      hwinBefore := hinv.hwinBefore
      hamb := by have := hinv.hamb; dsimp [s']; omega
      hamb_strict := by
        rintro (hA | hB)
        · by_cases hpos : 0 < s.mir.epoch .A ∨ 0 < s.mir.epoch .B
          · have := hinv.hamb_strict hpos; dsimp [s']; omega
          · have hA0 : s.mir.epoch .A = 0 := by omega
            have hB0 : s.mir.epoch .B = 0 := by omega
            have hQA : Q = .A := by
              cases Q with
              | A => rfl
              | B =>
                change 0 < s₁.epoch .A at hA
                change s₁.epoch .A = s.mir.epoch .A at hs₁_ep_other
                rw [hs₁_ep_other] at hA; omega
            subst hQA
            have := hinv.hamb
            dsimp [s']; omega
        · have := hinv.hamb
          dsimp [s']; omega
      hidx_le := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ; exact hidx_Q_bound
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          have hidx_eq : s'.mir.idx Q.other = s.mir.idx Q.other := by
            change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
            rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
          rw [hidx_eq]
          have := hinv.hidx_le Q.other
          omega
      hhon_len := by
        change (s.honest.length + 1) + (r - 1) ≤ q
        have := hinv.hhon_len
        omega
      hep_le := by
        intro R
        change s₁.epoch R ≤ qep
        by_cases hRQ : R = Q
        · subst hRQ; exact hep_le_qep
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO; rw [hs₁_ep_other]; exact hinv.hep_le Q.other
      hep_adj := hep_adj'
      hst_R := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          have hst_R'_self : s_R'.st R = st_R' := by
            change (Function.update s_R₁.st R st_R') R = st_R'
            exact Function.update_self R st_R' s_R₁.st
          have hst_f'_self : s_fig8'.st R = st_fig8' := by
            change (Function.update s_fig8₁.st R st_fig8') R = st_fig8'
            exact Function.update_self R st_fig8' s_fig8₁.st
          rw [hst_R'_self, hst_f'_self, expectedGhost_of_inWin_false _ _ _ _ _ _ _ _ hinw'_Q, hst_R'_eq]
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          have hst_R'_other : s_R'.st Q.other = s_R.st Q.other := by
            change (Function.update s_R₁.st Q st_R') Q.other = s_R.st Q.other
            rw [Function.update_of_ne (Party.other_ne Q), hst_R₁]
          have hst_f'_other : s_fig8'.st Q.other = s_fig8.st Q.other := by
            change (Function.update s_fig8₁.st Q st_fig8') Q.other = s_fig8.st Q.other
            rw [Function.update_of_ne (Party.other_ne Q), hst_fig8₁]
          have hec'_other : ec' Q.other = ec Q.other := by
            dsimp [ec']; split <;> simp [Function.update_of_ne (Party.other_ne Q)]
          have hidx'_other : s'.mir.idx Q.other = s.mir.idx Q.other := by
            change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
            rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
          rw [hst_R'_other, hst_f'_other, hec'_other, hinv.hst_R Q.other]
          exact (expectedGhost_congr P Dh encPt spkKey s' s Q.other (s_fig8.st Q.other) (ec Q.other)
            (Function.update_of_ne (Party.other_ne Q) pn s.pn) rfl (fun _ => rfl)
            (Function.update_of_ne (Party.other_ne Q) pq' s.pq) hs₁_ep_other hidx'_other).symm
      hst_id := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          change (Function.update s_fig8₁.st R st_fig8' R).id = R
          rw [Function.update_self, hid']
        · change (Function.update s_fig8₁.st Q st_fig8' R).id = R
          rw [Function.update_of_ne hRQ, hst_fig8₁]
          exact hinv.hst_id R
      htcur := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          change (Function.update s_fig8₁.st R st_fig8' R).tcur = s₁.epoch R
          rw [Function.update_self, htcur']
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          change (Function.update s_fig8₁.st Q st_fig8' Q.other).tcur = s₁.epoch Q.other
          rw [Function.update_of_ne (Party.other_ne Q), hst_fig8₁, hs₁_ep_other]
          exact hinv.htcur Q.other
      hepExp0 := hinv.hepExp0
      hspur := by
        intro R
        by_cases hRQ : R = Q
        · subst hRQ
          have hst_f'_self : s_fig8'.st R = st_fig8' := by
            change (Function.update s_fig8₁.st R st_fig8') R = st_fig8'
            exact Function.update_self R st_fig8' s_fig8₁.st
          rw [hst_f'_self]
          exact hspur'_Q
        · have hRO : R = Q.other := by cases Q <;> cases R <;> first | contradiction | rfl
          subst hRO
          have hst_f'_other : s_fig8'.st Q.other = s_fig8.st Q.other := by
            change (Function.update s_fig8₁.st Q st_fig8') Q.other = s_fig8.st Q.other
            rw [Function.update_of_ne (Party.other_ne Q), hst_fig8₁]
          have hec'_other : ec' Q.other = ec Q.other := by
            dsimp [ec']; split <;> simp [Function.update_of_ne (Party.other_ne Q)]
          have hep'_other : s'.mir.epoch Q.other = s.mir.epoch Q.other := hs₁_ep_other
          have hidx'_other : s'.mir.idx Q.other = s.mir.idx Q.other := by
            change (Function.update s₁.idx Q (s₁.idx Q + 1)) Q.other = s.mir.idx Q.other
            rw [Function.update_of_ne (Party.other_ne Q), hs₁_idx_other]
          rcases hinv.hspur Q.other with ⟨rk_base, T_base, hinw_t, hinw_f, hspur_hon⟩
          refine ⟨rk_base, T_base, ?_, ?_, ?_⟩
          · rw [hinw'_other, hst_f'_other, hep'_other, hec'_other]
            exact hinw_t
          · rw [hinw'_other, hst_f'_other, hep'_other, hidx'_other]
            exact hinw_f
          · intro wc hwc hsender hle hnot_mem
            rw [hep'_other] at hle ⊢
            rw [hmaxActive Q.other]
            rcases List.mem_cons.mp hwc with rfl | hwc
            · exfalso
              have hc1_ep : c.1.1 = s₁.epoch Q := congrArg Prod.fst hc1
              rw [hc1_ep] at hle hnot_mem
              have hadj_O : s.mir.epoch Q.other ≤ s₁.epoch Q + 1 := by
                have h := (hep_adj' Q.other).2
                rw [hs'_ep, Party.other_other, hs₁_ep_other] at h
                exact h
              have hrecv_O : Q.other.sendsIn (s₁.epoch Q) = false :=
                sendsIn_other_false_of_sendsIn hsends_s₁
              have hmem := mem_chains_epoch_of_adj Q.other (s.mir.epoch Q.other) (s₁.epoch Q)
                (s.chains Q.other)
                (fun hA => by rw [hA]; exact hinv.hchainsA_ep)
                (fun hB => by rw [hB]; exact hinv.hchainsB_ep)
                ht_ge1 hle hadj_O hrecv_O
              exact hnot_mem hmem
            · exact hspur_hon wc hwc hsender hle hnot_mem
      hchainsA := hchainsA'
      hchainsA_ep := hchainsA_ep'
      hchainsB_ep := hchainsB_ep'
      hchainsB_none := hinv.hchainsB_none
      hchains_sync := by
        intro R g hg
        rcases hinv.hchains_sync R g hg with ⟨hgep, hgsend, hgkey, v, hvR, hsync⟩
        have hvR_eq : (s_fig8'.st R).vR = (s_fig8.st R).vR := by
          by_cases hRQ : R = Q
          · subst hRQ
            change (Function.update s_fig8₁.st R st_fig8' R).vR = (s_fig8.st R).vR
            rw [Function.update_self, hvR']
          · change (Function.update s_fig8₁.st Q st_fig8' R).vR = (s_fig8.st R).vR
            rw [Function.update_of_ne hRQ, hst_fig8₁]
        exact ⟨Nat.le_trans hgep (hep_mono R), hgsend, hgkey, v, by rw [hvR_eq]; exact hvR, hsync⟩
      hhon := by
        intro wc hwc
        rw [hmaxActive .A, hmaxActive .B]
        rcases List.mem_cons.mp hwc with rfl | hwc
        · have hc1_ep : c.1.1 = s₁.epoch Q := congrArg Prod.fst hc1
          have hsender_Q : Party.senderOf c.1.1 = Q := by
            rw [hc1_ep]; exact senderOf_eq_of_sendsIn ht_ge1 hsends_s₁
          have hle_self : s₁.epoch Q ≤ maxActiveEp s.mir Q := by
            rw [← hmaxActive Q, ← hs'_ep]
            dsimp [maxActiveEp]; split <;> omega
          have hle_max : s₁.epoch Q ≤ max (maxActiveEp s.mir .A) (maxActiveEp s.mir .B) := by
            cases Q with
            | A => exact Nat.le_trans hle_self (Nat.le_max_left _ _)
            | B => exact Nat.le_trans hle_self (Nat.le_max_right _ _)
          refine ⟨hhon_wc, ?_, ?_, ?_⟩
          · rw [hc1_ep]; exact hle_max
          · rw [hsender_Q, hc1_ep]; exact hsends_s₁
          · rw [hsender_Q, hc1_ep]; exact le_rfl
        · rcases hinv.hhon wc hwc with ⟨h1, h2, h3, h4⟩
          exact ⟨h1, h2, h3, Nat.le_trans h4 (hep_mono (Party.senderOf wc.2.1.1))⟩
      htrans_hon := by
        intro rec_f hrec
        have htrans_eq : s_fig8'.trans = rec_fig8 :: s_fig8.trans := by
          change rec_fig8 :: s_fig8₁.trans = rec_fig8 :: s_fig8.trans
          have htr : s_fig8₁.trans = s_fig8.trans := by
            unfold SM.GameState.epMgmt at hep_fig8
            split at hep_fig8
            · split at hep_fig8
              · cases hep_fig8
              · injection hep_fig8 with h; subst h; dsimp only; split <;> rfl
            · split at hep_fig8
              · cases hep_fig8
              · injection hep_fig8 with h; subst h; rfl
          rw [htr]
        rw [htrans_eq] at hrec
        rcases List.mem_cons.mp hrec with rfl | hrec
        · have hc1_ep : c.1.1 = s₁.epoch Q := congrArg Prod.fst hc1
          have hsender_Q : Party.senderOf c.1.1 = Q := by
            rw [hc1_ep]; exact senderOf_eq_of_sendsIn ht_ge1 hsends_s₁
          refine ⟨List.mem_cons_self, hsender_Q.symm, ?_, ?_⟩
          · change s_fig8₁.epoch Q = c.1.1
            rw [hmeta₁.hepoch_fig8, hc1_ep]
          · change s_fig8₁.idx Q + 1 = c.2.1
            rw [hmeta₁.hidx_fig8, hc2]
        · rcases hinv.htrans_hon rec_f hrec with ⟨h1, h2, h3, h4⟩
          exact ⟨List.mem_cons_of_mem _ h1, h2, h3, h4⟩
      hcoll := by
        intro t₁ t₂ h₁ h₂ hdh
        rw [hmaxActive .A, hmaxActive .B] at h₁ h₂
        exact hinv.hcoll t₁ t₂ h₁ h₂ hdh
      hcorrB0 := by dsimp only [s']; exact hcorrB0_epMgmt_record hep_mir hinv.hcorrB0
      hpqInv := hpq'_inv pq' salt pqMsg hspqr }

private theorem simSendStep_preserves_simInv
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hS : SpqrOffCorrectLocal P.spqr)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hq32 : q < 2 ^ 32) (hr : 0 < r)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))) (rq : PQC)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q = true)
    (hep_mir : s.mir.epMgmt 3 qep Q bad = some s₁)
    (hsafeCh : chal.isSome = true → s₁.safeCh 3 Q = true) :
    let fR := chal.elim
      (transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep Q m₀ rq bad s_R)
      (fun m₁ => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep SM.Config.h1 Q m₀ m₁ rq bad s_R)
    let res := simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq (ec Q) (s, s_fig8)
    let ec' := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
    fR.1 = res.1 ∧
    res.2.1.amb = s.amb ∧
    remWin qep res.2.1.mir ≤ remWin qep s.mir ∧
    (inReceiveOnlyEpoch s.mir Q = true → updateAllEagerCoins s.mir res.2.1.mir (· == Q) ec = pure ec') ∧
    (inReceiveOnlyEpoch s.mir Q = false →
      updateAllEagerCoins s.mir res.2.1.mir (fun _ => false) ec = pure ec' ∧
      ∀ (c_cka : BitVec 256), simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal bad s₁ rq c_cka (s, s_fig8) = res) ∧
    SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ fR.2 res.2.1 res.2.2 ec' winBefore epExp := by
  have hc := simSendStep_preserves_simInvC_core P (fun _ => True) (fun _ => True) ℓ Dh
    encPt encT decT idOf hX hrt hid lam qep q r hq32 hr Q m₀ chal bad s₁ rq x₀
    s_R s s_fig8 ec winBefore epExp hinv.toC (hS.1 (s.pq Q) rq) (hS.2.2.1 (s.pq Q) rq)
    (fun _ _ _ _ _ => trivial) hnoBob_mir hep_mir hsafeCh
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    { hc.2.2.2.2.2.1 with
      hhon := fun wc hwc =>
        ⟨hc.2.2.2.2.2.2.2.1 hS (fun wc' hwc' => (hinv.hhon wc' hwc').1) wc hwc,
         (hc.2.2.2.2.2.1.hhon wc hwc).2⟩ }⟩

/-- One-step `CloseByState` reduction for `transmit` queries. -/
theorem closeByState_transmit_step {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : SpqrOffCorrectLocal P.spqr)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r)
    (post : α → Bool)
    (Q : Party) (m : Plain ℓ) (rc : Option PQC)
    (cont : Option (List (BitVec 8)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inl (.inl (Q, m, rc))))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  set q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain :=
    .inl (.inl (.inl (.inl (Q, m, rc))))
  have hD0 := stepR_D0_eq_of_simInv P ℓ Dh encPt encT decT lam qep q r x₀ q_sm
    s_R s s_fig8 ec winBefore epExp hinv (by intro _ h; dsimp [q_sm] at h; nomatch h)
  have hwin_R := hinv.hmeta.hwin_R
  have hwin_mir := hinv.hmeta.hwin_mir
  have hwin_fig8 := hinv.hmeta.hwin_fig8
  have hstop := hinv.hmeta.hstop
  have hnoBob_R := hinv.hmeta.noBobEpoch0_R Q
  by_cases hguard : (!(SM.noBobSendInEpoch0 s.mir Q)) = true
  · have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        q_sm s_R = pure (none, s_R) := by
      rw [stepR_transmit_eq]
      change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = pure (none, s_R)
      rw [hnoBob_R, hwin_R, hguard, Bool.true_or, ite_eq_left rfl]
    have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
        pure (none, ((s, s_fig8), ec)) := by
      intro k
      change stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec = _
      unfold stepSimEagerTransmit
      dsimp only
      rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, Bool.not_true, Bool.and_false,
          ite_eq_right Bool.false_ne_true, stepSim_transmit_eq P ℓ Dh encPt encT decT idOf lam qep k hS.1 Q m rc (s, s_fig8) hwin_fig8]
      dsimp only
      rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, ite_eq_left rfl,
          pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
    exact closeByState_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
      q_sm cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore none
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R s s_fig8 ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))
  · have hguard_f : (!(SM.noBobSendInEpoch0 s.mir Q)) = false := Bool.eq_false_iff.mpr hguard
    have hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q = true := by
      revert hguard_f; cases SM.noBobSendInEpoch0 s.mir Q <;> simp
    cases hep_mir : s.mir.epMgmt 3 qep Q rc.isSome with
    | none =>
      have hep_R : s_R.epMgmt 3 qep Q rc.isSome = none :=
        hinv.hmeta.epMgmt_none Q qep rc.isSome hep_mir
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          q_sm s_R = samCoin rc >>= fun _ => pure (none, s_R) := by
        rw [stepR_transmit_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
            samIfNec_bind_eq]
        congr 1; funext rq
        unfold transmitPure
        rw [hep_R]
      have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
          pure (none, ((s, s_fig8), ec)) := by
        intro k
        change stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec = _
        unfold stepSimEagerTransmit
        dsimp only
        have hsim : stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) = pure (none, (s, s_fig8)) := by
          rw [stepSim_transmit_eq P ℓ Dh encPt encT decT idOf lam qep k hS.1 Q m rc (s, s_fig8) hwin_fig8]
          dsimp only
          rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true, hep_mir]
        split
        · rw [hep_mir]
          change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
          rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
        · change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
          rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
      exact closeByState_inr_same_amb_bind_const_R P ℓ Dh encPt encT decT idOf lam qep q δ post
        q_sm cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (samCoin rc) none
        hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
        (ih none s_R s s_fig8 ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))
    | some s₁ =>
      let fR := fun rq => transmitPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep Q m rq rc.isSome s_R
      let res := fun rq => simSendStep P ℓ Dh encPt encT idOf lam qep Q m none rc.isSome s₁ rq (ec Q) (s, s_fig8)
      let ec' := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
      let fS := fun rq => ((res rq).1, ((res rq).2, ec'))
      have hpres := fun rq => simSendStep_preserves_simInv P ℓ Dh encPt encT decT idOf
        hX hrt hS hid lam qep q r hq32 hr Q m none rc.isSome s₁ rq x₀ s_R s s_fig8 ec winBefore epExp
        hinv hnoBob_mir hep_mir (fun h => by cases h)
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          q_sm s_R = samCoin rc >>= fun rq => pure (fR rq) := by
        rw [stepR_transmit_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
            samIfNec_bind_eq]
      cases hinw : inReceiveOnlyEpoch s.mir Q with
      | true =>
        have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
            samCoin rc >>= fun rq => pure (fS rq) := by
          intro k
          change stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec = _
          unfold stepSimEagerTransmit
          dsimp only
          rw [hwin_fig8, hinw, hstop, hwin_mir, hguard_f, Bool.not_false, Bool.true_and,
              Bool.false_or, Bool.false_or, Bool.not_false, Bool.and_true, ite_eq_left rfl, hep_mir]
          dsimp only
          change (samCoin rc >>= _) = _
          congr 1; funext rq
          rw [(hpres rq).2.2.2.1 hinw, pure_bind]
        exact closeByState_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep q δ post
          q_sm cont s_R s s_fig8 ec winBefore (samCoin rc) fR fS
          (fun rq => (hpres rq).1) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx))
          (fun rq => (hpres rq).2.1) (fun rq => (hpres rq).2.2.1)
          (fun rq => ih (fS rq).1 (fR rq).2 (fS rq).2.1.1 (fS rq).2.1.2 (fS rq).2.2 winBefore epExp (hpres rq).2.2.2.2.2)
      | false =>
        have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
            samCoin rc >>= fun rq => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (fS rq) := by
          intro k
          change stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m rc (s, s_fig8) ec = _
          unfold stepSimEagerTransmit
          dsimp only
          rw [hinw, Bool.and_false, Bool.false_and, ite_eq_right Bool.false_ne_true,
              stepSim_transmit_eq P ℓ Dh encPt encT decT idOf lam qep k hS.1 Q m rc (s, s_fig8) hwin_fig8]
          dsimp only
          rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true, hep_mir]
          dsimp only
          change ((samCoin rc >>= _) >>= _) = _
          simp only [bind_assoc, pure_bind]
          congr 1; funext rq
          congr 1; funext c_cka
          rcases (hpres rq).2.2.2.2.1 hinw with ⟨hupd, hcoins⟩
          rw [hcoins c_cka, hupd, pure_bind]
        exact closeByState_inr_same_amb_bind_const_sim P ℓ Dh encPt encT decT idOf lam qep q δ post
          q_sm cont s_R s s_fig8 ec winBefore (samCoin rc) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) fR fS
          (fun rq => (hpres rq).1) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx))
          (fun rq => (hpres rq).2.1) (fun rq => (hpres rq).2.2.1)
          (fun rq => ih (fS rq).1 (fR rq).2 (fS rq).2.1.1 (fS rq).2.1.2 (fS rq).2.2 winBefore epExp (hpres rq).2.2.2.2.2)

/-- One-step `CloseByState` reduction for `chall` queries. -/
theorem closeByState_chall_step {α : Type} (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : SpqrOffCorrectLocal P.spqr)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (lam : Pt) (qep q r : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (hr : 0 < r)
    (post : α → Bool)
    (Q : Party) (m₀ m₁ : Plain ℓ) (rc : Option PQC)
    (cont : Option (List (BitVec 8)) → SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInv P ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (ih : ∀ ans s_R' s' s_fig8' ec' winBefore' epExp',
      SimInv P ℓ Dh encPt encT qep q (r - 1) x₀ s_R' s' s_fig8' ec' winBefore' epExp' →
      CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post (cont ans) s_R' s' s_fig8' ec' winBefore') :
    CloseByState P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))))) >>= cont)
      s_R s s_fig8 ec winBefore := by
  set q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain :=
    .inl (.inl (.inl (.inr (Q, m₀, m₁, rc))))
  have hD0 := stepR_D0_eq_of_simInv P ℓ Dh encPt encT decT lam qep q r x₀ q_sm
    s_R s s_fig8 ec winBefore epExp hinv (by intro _ h; dsimp [q_sm] at h; nomatch h)
  have hwin_R := hinv.hmeta.hwin_R
  have hwin_mir := hinv.hmeta.hwin_mir
  have hwin_fig8 := hinv.hmeta.hwin_fig8
  have hstop := hinv.hmeta.hstop
  have hnoBob_R := hinv.hmeta.noBobEpoch0_R Q
  by_cases hguard : (!(SM.noBobSendInEpoch0 s.mir Q)) = true
  · have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
        q_sm s_R = pure (none, s_R) := by
      rw [stepR_chall_eq]
      change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = pure (none, s_R)
      rw [hnoBob_R, hwin_R, hguard, Bool.true_or, ite_eq_left rfl]
    have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
        pure (none, ((s, s_fig8), ec)) := by
      intro k
      change stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec = _
      unfold stepSimEagerChall
      dsimp only
      rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, Bool.not_true, Bool.and_false,
          ite_eq_right Bool.false_ne_true, stepSim_chall_eq P ℓ Dh encPt encT decT idOf lam qep k hS.1 Q m₀ m₁ rc (s, s_fig8) hwin_fig8]
      dsimp only
      rw [hstop, hwin_mir, hguard, Bool.false_or, Bool.false_or, ite_eq_left rfl,
          pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
    exact closeByState_inr_same_amb_pure P ℓ Dh encPt encT decT idOf lam qep q δ post
      q_sm cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore none
      hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
      (ih none s_R s s_fig8 ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))
  · have hguard_f : (!(SM.noBobSendInEpoch0 s.mir Q)) = false := Bool.eq_false_iff.mpr hguard
    have hnoBob_mir : SM.noBobSendInEpoch0 s.mir Q = true := by
      revert hguard_f; cases SM.noBobSendInEpoch0 s.mir Q <;> simp
    cases hep_mir : s.mir.epMgmt 3 qep Q rc.isSome with
    | none =>
      have hep_R : s_R.epMgmt 3 qep Q rc.isSome = none :=
        hinv.hmeta.epMgmt_none Q qep rc.isSome hep_mir
      have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
          q_sm s_R = samCoin rc >>= fun _ => pure (none, s_R) := by
        rw [stepR_chall_eq]
        change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
        rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
            samIfNec_bind_eq]
        congr 1; funext rq
        unfold challPure
        rw [hep_R]
      have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
          pure (none, ((s, s_fig8), ec)) := by
        intro k
        change stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec = _
        unfold stepSimEagerChall
        dsimp only
        have hsim : stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) = pure (none, (s, s_fig8)) := by
          rw [stepSim_chall_eq P ℓ Dh encPt encT decT idOf lam qep k hS.1 Q m₀ m₁ rc (s, s_fig8) hwin_fig8]
          dsimp only
          rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true, hep_mir]
        split
        · rw [hep_mir]
          change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
          rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
        · change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
          rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
      exact closeByState_inr_same_amb_bind_const_R P ℓ Dh encPt encT decT idOf lam qep q δ post
        q_sm cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (samCoin rc) none
        hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
        (ih none s_R s s_fig8 ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))
    | some s₁ =>
      rcases hinv.hmeta.epMgmt_some Q qep rc.isSome hep_mir with
        ⟨s_R₁, s_fig8₁, hep_R, hep_fig8, hst_R₁, hst_fig8₁, hmeta₁⟩
      by_cases hsafe_neg : (!(s₁.safeCh 3 Q)) = true
      · have hsafe_R : s_R₁.safeCh 3 Q = s₁.safeCh 3 Q := hmeta₁.safeCh_R 3 Q
        have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            q_sm s_R = samCoin rc >>= fun _ => pure (none, s_R) := by
          rw [stepR_chall_eq]
          change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
          rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
              samIfNec_bind_eq]
          congr 1; funext rq
          unfold challPure
          rw [hep_R]
          dsimp only
          rw [hsafe_R, hsafe_neg, Bool.true_or, ite_eq_left rfl]
        have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
            pure (none, ((s, s_fig8), ec)) := by
          intro k
          change stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec = _
          unfold stepSimEagerChall
          dsimp only
          have hsim : stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) = pure (none, (s, s_fig8)) := by
            rw [stepSim_chall_eq P ℓ Dh encPt encT decT idOf lam qep k hS.1 Q m₀ m₁ rc (s, s_fig8) hwin_fig8]
            dsimp only
            rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true,
                hep_mir]
            dsimp only
            rw [hsafe_neg, ite_eq_left rfl]
          split
          · rw [hep_mir]
            dsimp only
            rw [hsafe_neg, ite_eq_left rfl]
            change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
            rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
          · change (stepSim P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) >>= _) = _
            rw [hsim, pure_bind, updateAllEagerCoins_self_unused s.mir ec hinv.hec, pure_bind]
        exact closeByState_inr_same_amb_bind_const_R P ℓ Dh encPt encT decT idOf lam qep q δ post
          q_sm cont s_R s_R s s s_fig8 s_fig8 ec ec winBefore (samCoin rc) none
          hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx)) rfl le_rfl
          (ih none s_R s s_fig8 ec winBefore epExp (hinv.mono_r (Nat.sub_le r 1)))
      · have hsafe_f : (!(s₁.safeCh 3 Q)) = false := Bool.eq_false_iff.mpr hsafe_neg
        have hsafeCh : s₁.safeCh 3 Q = true := by
          revert hsafe_f; cases s₁.safeCh 3 Q <;> simp
        let fR := fun rq => challPure (libsignalSessionScheme P ℓ encPt lam).sendPart 3 qep
          SM.Config.h1 Q m₀ m₁ rq rc.isSome s_R
        let res := fun rq => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) rc.isSome s₁ rq (ec Q) (s, s_fig8)
        let ec' := if inReceiveOnlyEpoch s.mir Q then Function.update ec Q 0 else ec
        let fS := fun rq => ((res rq).1, ((res rq).2, ec'))
        have hpres := fun rq => simSendStep_preserves_simInv P ℓ Dh encPt encT decT idOf
          hX hrt hS hid lam qep q r hq32 hr Q m₀ (some m₁) rc.isSome s₁ rq x₀ s_R s s_fig8 ec winBefore epExp
          hinv hnoBob_mir hep_mir (fun _ => hsafeCh)
        have hstepR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
            q_sm s_R = samCoin rc >>= fun rq => pure (fR rq) := by
          rw [stepR_chall_eq]
          change (if (!noBobSendInEpoch0 s_R Q || s_R.win) = true then pure (none, s_R) else _) = _
          rw [hnoBob_R, hwin_R, hguard_f, Bool.false_or, ite_eq_right Bool.false_ne_true,
              samIfNec_bind_eq]
          rfl
        cases hinw : inReceiveOnlyEpoch s.mir Q with
        | true =>
          have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
              samCoin rc >>= fun rq => pure (fS rq) := by
            intro k
            change stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec = _
            unfold stepSimEagerChall
            dsimp only
            rw [hwin_fig8, hinw, hstop, hwin_mir, hguard_f, Bool.not_false, Bool.true_and,
                Bool.false_or, Bool.false_or, Bool.not_false, Bool.and_true, ite_eq_left rfl, hep_mir]
            dsimp only
            rw [hsafe_f, ite_eq_right Bool.false_ne_true]
            change (samCoin rc >>= _) = _
            congr 1; funext rq
            rw [(hpres rq).2.2.2.1 hinw, pure_bind]
          exact closeByState_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep q δ post
            q_sm cont s_R s s_fig8 ec winBefore (samCoin rc) fR fS
            (fun rq => (hpres rq).1) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx))
            (fun rq => (hpres rq).2.1) (fun rq => (hpres rq).2.2.1)
            (fun rq => ih (fS rq).1 (fR rq).2 (fS rq).2.1.1 (fS rq).2.1.2 (fS rq).2.2 winBefore epExp (hpres rq).2.2.2.2.2)
        | false =>
          have hstepSim : ∀ k, stepSimEager P ℓ Dh encPt encT decT idOf lam qep k q_sm (s, s_fig8) ec =
              samCoin rc >>= fun rq => ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (fS rq) := by
            intro k
            change stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ rc (s, s_fig8) ec = _
            unfold stepSimEagerChall
            dsimp only
            rw [hinw, Bool.and_false, Bool.false_and, ite_eq_right Bool.false_ne_true,
                stepSim_chall_eq P ℓ Dh encPt encT decT idOf lam qep k hS.1 Q m₀ m₁ rc (s, s_fig8) hwin_fig8]
            dsimp only
            rw [hstop, hwin_mir, hguard_f, Bool.false_or, Bool.false_or, ite_eq_right Bool.false_ne_true, hep_mir]
            dsimp only
            rw [hsafe_f, ite_eq_right Bool.false_ne_true]
            change ((samCoin rc >>= _) >>= _) = _
            simp only [bind_assoc, pure_bind]
            congr 1; funext rq
            congr 1; funext c_cka
            rcases (hpres rq).2.2.2.2.1 hinw with ⟨hupd, hcoins⟩
            rw [hcoins c_cka, hupd, pure_bind]
          exact closeByState_inr_same_amb_bind_const_sim P ℓ Dh encPt encT decT idOf lam qep q δ post
            q_sm cont s_R s s_fig8 ec winBefore (samCoin rc) ($ᵗ BitVec 256 : ProbComp (BitVec 256)) fR fS
            (fun rq => (hpres rq).1) hD0 hstepR (hstepSim none) (fun idx _ => hstepSim (some idx))
            (fun rq => (hpres rq).2.1) (fun rq => (hpres rq).2.2.1)
            (fun rq => ih (fS rq).1 (fR rq).2 (fS rq).2.1.1 (fS rq).2.1.2 (fS rq).2.2 winBefore epExp (hpres rq).2.2.2.2.2)

end CryptoGames.LibsignalSM.Proofs.Refinement
