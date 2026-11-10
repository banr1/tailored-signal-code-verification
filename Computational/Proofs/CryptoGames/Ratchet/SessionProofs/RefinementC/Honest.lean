/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Honest

/-!
# Honest entries without salt binding

Uniqueness and lookup lemmas for `HonestEntryInvC` without salt binding, derived from `PosUniq` and used by the `RefinementC` deliver and inject steps.
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
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-- Under `PosUniq` and injective non-colliding ratchet keys, any two honest entries for the same wire coincide. -/
theorem honestEntryInvC_unique (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (epExp : ℕ → BitVec 256)
    (s : SimState PQ Pt ℓ) (huniq : PosUniq s)
    {w : List (BitVec 8)} {c₁ c₂ : Fig8C Pt}
    (hmem₁ : (w, c₁) ∈ s.honest) (hmem₂ : (w, c₂) ∈ s.honest)
    (h₁ : HonestEntryInvC P Inv Dh encT epExp (w, c₁))
    (h₂ : HonestEntryInvC P Inv Dh encT epExp (w, c₂))
    (hcoll : Dh.dh (epExp c₁.1.1) Dh.base = Dh.dh (epExp c₂.1.1) Dh.base → c₁.1.1 = c₂.1.1) :
    c₁ = c₂ := by
  rcases h₁ with ⟨_, _, _, _, _, _, _, h_hdr₁, body₁, hparse₁, _, hsrk₁, hctr₁, _⟩
  rcases h₂ with ⟨_, _, _, _, _, _, _, h_hdr₂, body₂, hparse₂, _, hsrk₂, hctr₂, _⟩
  have hhb : (h_hdr₁, body₁) = (h_hdr₂, body₂) := Option.some.inj (hparse₁.symm.trans hparse₂)
  rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
  have ht : c₁.1.1 = c₂.1.1 := hcoll (hinj (hsrk₁.symm.trans hsrk₂))
  have hi : c₁.2.1 = c₂.2.1 := hctr₁.symm.trans hctr₂
  exact congrArg Prod.snd (huniq (w, c₁) hmem₁ (w, c₂) hmem₂ ht hi)

/-- Any honest record `(w, c)` sent by `Q.other` is the record found by `simRecvC` for `w`. -/
theorem honestC_eq_some_of_memC (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (epExp : ℕ → BitVec 256) (M : ℕ)
    (s : SimState PQ Pt ℓ) (huniq : PosUniq s) (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hmem : (w, c) ∈ s.honest)
    (hsender : Party.senderOf c.1.1 = Q.other)
    (hhon : ∀ wc ∈ s.honest, HonestEntryInvC P Inv Dh encT epExp wc ∧ wc.2.1.1 ≤ M)
    (hcoll : ∀ t₁ t₂, t₁ ≤ M → t₂ ≤ M →
      Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂) :
    (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c := by
  cases hfind : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp hfind (w, c) hmem
    simp [hsender] at hnone
  | some wc' =>
    dsimp only [Option.map]
    congr 1
    have hmem' := List.mem_of_find?_eq_some hfind
    have hpred' := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred'
    rcases wc' with ⟨w', c'⟩
    dsimp only at hpred' ⊢
    rcases hpred' with ⟨rfl, _⟩
    exact honestEntryInvC_unique P Inv Dh encT hinj epExp s huniq hmem' hmem
      (hhon (w', c') hmem').1 (hhon (w', c) hmem).1
      (hcoll c'.1.1 c.1.1 (hhon (w', c') hmem').2 (hhon (w', c) hmem).2)

/-- An honest wire in transit to `Q` matches its Fig. 8 in-transit record, is found by `simRecvC`, and steps `fwdPure` as Fig. 8 `deliver`. -/
theorem deliver_inTransit_syncC (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (epExp : ℕ → BitVec 256) (M : ℕ)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hmeta : SameMeta s_R s s_fig8) (huniq : PosUniq s)
    (hhon : ∀ wc ∈ s.honest, HonestEntryInvC P Inv Dh encT epExp wc ∧ wc.2.1.1 ≤ M)
    (htrans_hon : ∀ r ∈ s_fig8.trans,
      (LibsignalSim.toWire r.ct, r.ct) ∈ s.honest ∧ r.pos.sender = Party.senderOf r.ct.1.1)
    (hcoll : ∀ t₁ t₂, t₁ ≤ M → t₂ ≤ M →
      Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂)
    (Q : Party) (w : List (BitVec 8))
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : s.mir.inTransit Q.other w = some r_mir) :
    (∃ r_R, s_R.inTransit Q.other w = some r_R ∧ r_R.pos = r_mir.pos) ∧
    ∃ c r_fig8,
      (w, c) ∈ s.honest ∧
      Party.senderOf c.1.1 = Q.other ∧
      s_fig8.inTransit Q.other c = some r_fig8 ∧
      r_fig8.pos = r_mir.pos ∧
      (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c ∧
      ∀ {Key : Type} (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
        (Δ qep : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ)),
        fwdPure sm Δ qep cfg s Q c s_fig8 = deliverPure sm cfg Q c s_fig8 := by
  have hR_map := hmeta.inTransit_R_map Q.other w
  rw [htr_mir, Option.map_some] at hR_map
  rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, hpair_R⟩
  have hpos_R : r_R.pos = r_mir.pos := congrArg Prod.fst hpair_R
  have hmir_mem : r_mir ∈ s.mir.trans := List.mem_of_find?_eq_some htr_mir
  have hmir_pred := List.find?_some htr_mir
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmir_pred
  have hmap_mem : (r_mir.pos, w) ∈ s_fig8.trans.map (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
    rw [← hmeta.htrans_fig8, ← hmir_pred.2]
    exact List.mem_map_of_mem hmir_mem
  rw [List.mem_map] at hmap_mem
  rcases hmap_mem with ⟨r₀, hr₀, hpair₀⟩
  have hpos₀ : r₀.pos = r_mir.pos := congrArg Prod.fst hpair₀
  have hw₀ : LibsignalSim.toWire r₀.ct = w := congrArg Prod.snd hpair₀
  set c := r₀.ct
  have hc_mem : (w, c) ∈ s.honest := by
    rw [← hw₀]
    exact (htrans_hon r₀ hr₀).1
  have hc_sender : Party.senderOf c.1.1 = Q.other := by
    rw [← (htrans_hon r₀ hr₀).2, hpos₀, hmir_pred.1]
  have hiff : ∀ r ∈ s_fig8.trans, decide (r.ct = c) = decide (LibsignalSim.toWire r.ct = w) := by
    intro r hr
    by_cases hrc : r.ct = c
    · simp [hrc, hw₀]
    · have hne_w : LibsignalSim.toWire r.ct ≠ w := by
        intro heq_w
        have hmem_r : (w, r.ct) ∈ s.honest := by
          rw [← heq_w]
          exact (htrans_hon r hr).1
        exact hrc (honestEntryInvC_unique P Inv Dh encT hinj epExp s huniq hmem_r hc_mem
          (hhon (w, r.ct) hmem_r).1 (hhon (w, c) hc_mem).1
          (hcoll r.ct.1.1 c.1.1 (hhon (w, r.ct) hmem_r).2 (hhon (w, c) hc_mem).2))
      simp [hrc, hne_w]
  have hfig8_map := (WP2A.H3.find_fig8_eq_of_map hmeta.htrans_fig8 Q.other w c hiff).symm
  change (s_fig8.inTransit Q.other c).map (fun r => (r.pos, LibsignalSim.toWire r.ct)) =
    (s.mir.inTransit Q.other w).map (fun r => (r.pos, r.ct)) at hfig8_map
  rw [htr_mir, Option.map_some] at hfig8_map
  rcases Option.map_eq_some_iff.mp hfig8_map with ⟨r_fig8, hr_fig8, hpair_fig8⟩
  have hpos_fig8 : r_fig8.pos = r_mir.pos := congrArg Prod.fst hpair_fig8
  refine ⟨⟨r_R, hr_R, hpos_R⟩, c, r_fig8, hc_mem, hc_sender, hr_fig8, hpos_fig8,
    honestC_eq_some_of_memC P Inv Dh encT hinj epExp M s huniq Q w c hc_mem hc_sender hhon hcoll, ?_⟩
  intro Key sm Δ qep cfg
  unfold fwdPure
  have hany : s.honest.any (fun wc => decide (wc.2 = c) && (s.mir.inTransit Q.other wc.1).isSome) = true := by
    rw [List.any_eq_true]
    exact ⟨(w, c), hc_mem, by simp [htr_mir]⟩
  rw [hany]
  rfl

end CryptoGames.LibsignalSM.Proofs.Refinement
