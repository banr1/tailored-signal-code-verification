/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2RestCore

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2Rest38
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRNoBSC CompRPlantWire CompRTag CompRI0TermInj CompRSplit38PairCore CompRSplit38UntaggedShape CompRNonInj38Census CompRQRestCensusZ CompC2RestCore Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def RestEntry (S : Sem) (g : Ghost) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := DhPtNotLow S g x.1 ∧ (IsTrunc8 x.1 → ZVal x.2.2) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → ¬ IsX x.1 → ¬ IsTrunc8 x.1 → NonInjOff x.2.2 ∧ x.2.2 ∉ x25519Vals)
section Sep
variable {S : Sem} {g : Ghost}
theorem zVal_of_isKdf {u : DY.Bytes} (h : IsKdf u) : ZVal (gamma compI0 S g u) := by obtain ⟨k, m, rfl⟩ := h; exact zVal_kdfExtract k m
theorem shapeAgree_of_zVal_nonInjOff {u₁ u₂ : DY.Bytes} (h₁ : ZVal (gamma compI0 S g u₁)) (h₂ : NonInjOff (gamma compI0 S g u₂)) : ShapeAgree S g u₁ u₂ :=
  shapeAgree_of_gamma_ne fun he => not_zVal_of_nonInjOff h₂ (he ▸ h₁)
theorem shapeAgree_of_x_not_mem {u₁ u₂ : DY.Bytes} (h₁ : IsX u₁) (h₂ : gamma compI0 S g u₂ ∉ x25519Vals) : ShapeAgree S g u₁ u₂ :=
  shapeAgree_of_gamma_ne fun he => h₂ (he ▸ gamma_mem_x25519Vals_of_isX h₁)
theorem shapeAgree_of_x_nonInjOffXZ {u₁ u₂ : DY.Bytes} (h₁ : IsX u₁) (hd : DhPtNotLow S g u₁) (h₂ : NonInjOffXZ (gamma compI0 S g u₂)) : ShapeAgree S g u₁ u₂ := by apply shapeAgree_of_gamma_ne; intro he; have hm := gamma_mem_x25519Vals_of_isX (S := S) (g := g) h₁; rw [he] at hm; exact gamma_x_ne_zeroDh h₁ hd (he.trans (h₂.2 (x25519Vals_length _ hm) hm))
end Sep
def QRestNR : PairQ := fun S g known pts x₁ x₂ =>
  assumedInjective x₁.1 ≠ assumedInjective x₂.1 → ¬ IsKdf x₁.1 → ¬ IsX x₁.1 → ¬ IsTrunc8 x₁.1 → ¬ IsKdf x₂.1 → ¬ IsX x₂.1 → ¬ IsTrunc8 x₂.1 → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → ShapeAgree S g x₁.1 x₂.1
def QRestRR : PairQ := fun S g known pts x₁ x₂ =>
  assumedInjective x₁.1 = true → assumedInjective x₂.1 = true → ¬ IsKdf x₁.1 → ¬ IsX x₁.1 → ¬ IsTrunc8 x₁.1 → ¬ IsKdf x₂.1 → ¬ IsX x₂.1 → ¬ IsTrunc8 x₂.1 → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → ShapeAgree S g x₁.1 x₂.1
def QRestXX : PairQ := fun S g known pts x₁ x₂ =>
  IsX x₁.1 → IsX x₂.1 → ¬ CrossSep x₁.1 x₂.1 → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → ShapeAgree S g x₁.1 x₂.1
def QRestTT : PairQ := fun S g known pts x₁ x₂ =>
  IsTrunc8 x₁.1 → IsTrunc8 x₂.1 → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → ShapeAgree S g x₁.1 x₂.1
theorem qRest_of_entries (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (hv₁ : x₁.2.2 = gamma compI0 S g x₁.1) (hv₂ : x₂.2.2 = gamma compI0 S g x₂.1) (hN₁ : assumedInjective x₁.1 = false → NonInjOffXZ x₁.2.2) (hN₂ : assumedInjective x₂.1 = false → NonInjOffXZ x₂.2.2) (hE₁ : RestEntry S g x₁) (hE₂ : RestEntry S g x₂) (hNR : QRestNR S g known pts x₁ x₂) (hRR : QRestRR S g known pts x₁ x₂) (hXX : QRestXX S g known pts x₁ x₂) (hTT : QRestTT S g known pts x₁ x₂) : QRest S g known pts x₁ x₂ := by
  intro hK₁ hc hs hu; obtain ⟨hD₁, hT₁', hR₁'⟩ := hE₁; obtain ⟨hD₂, hT₂', hR₂'⟩ := hE₂; rw [hv₁] at hN₁ hT₁' hR₁'; rw [hv₂] at hN₂ hT₂' hR₂'
  by_cases hX₁ : IsX x₁.1
  · by_cases hK₂ : IsKdf x₂.1
    · exact absurd (Or.inr (Or.inl ⟨hX₁, hK₂⟩)) hc
    by_cases hX₂ : IsX x₂.1
    · exact hXX hX₁ hX₂ hc hs hu
    by_cases hT₂ : IsTrunc8 x₂.1
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr hX₁, hT₂⟩))))) hc
    rcases Bool.eq_false_or_eq_true (assumedInjective x₂.1) with hai₂ | hai₂
    · exact shapeAgree_of_x_not_mem hX₁ (hR₂' hai₂ hK₂ hX₂ hT₂).2
    · exact shapeAgree_of_x_nonInjOffXZ hX₁ hD₁ (hN₂ hai₂)
  by_cases hT₁ : IsTrunc8 x₁.1
  · by_cases hK₂ : IsKdf x₂.1
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hT₁, Or.inl hK₂⟩))))) hc
    by_cases hX₂ : IsX x₂.1
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hT₁, Or.inr hX₂⟩))))) hc
    by_cases hT₂ : IsTrunc8 x₂.1
    · exact hTT hT₁ hT₂ hs hu
    rcases Bool.eq_false_or_eq_true (assumedInjective x₂.1) with hai₂ | hai₂
    · exact shapeAgree_of_zVal_nonInjOff (hT₁' hT₁) (hR₂' hai₂ hK₂ hX₂ hT₂).1
    · exact shapeAgree_of_zVal_nonInjOff (hT₁' hT₁) (hN₂ hai₂).1
  have hoff₁ : NonInjOff (gamma compI0 S g x₁.1) := by rcases Bool.eq_false_or_eq_true (assumedInjective x₁.1) with hai₁ | hai₁ <;> [exact (hR₁' hai₁ hK₁ hX₁ hT₁).1; exact (hN₁ hai₁).1]
  by_cases hK₂ : IsKdf x₂.1
  · exact (shapeAgree_of_zVal_nonInjOff (zVal_of_isKdf hK₂) hoff₁).symm
  by_cases hX₂ : IsX x₂.1
  · rcases Bool.eq_false_or_eq_true (assumedInjective x₁.1) with hai₁ | hai₁
    · exact (shapeAgree_of_x_not_mem hX₂ (hR₁' hai₁ hK₁ hX₁ hT₁).2).symm
    · exact (shapeAgree_of_x_nonInjOffXZ hX₂ hD₂ (hN₁ hai₁)).symm
  by_cases hT₂ : IsTrunc8 x₂.1
  · exact (shapeAgree_of_zVal_nonInjOff (hT₂' hT₂) hoff₁).symm
  rcases Bool.eq_false_or_eq_true (assumedInjective x₁.1) with hai₁ | hai₁ <;>
    rcases Bool.eq_false_or_eq_true (assumedInjective x₂.1) with hai₂ | hai₂
  · exact hRR hai₁ hai₂ hK₁ hX₁ hT₁ hK₂ hX₂ hT₂ hs hu
  · exact hNR (by rw [hai₁, hai₂]; decide) hK₁ hX₁ hT₁ hK₂ hX₂ hT₂ hs hu
  · exact hNR (by rw [hai₁, hai₂]; decide) hK₁ hX₁ hT₁ hK₂ hX₂ hT₂ hs hu
  · exfalso; rcases hs.1 with h | h <;> [rw [hai₁] at h; rw [hai₂] at h] <;> exact absurd h (by decide)
def Rest38EntryAt (w : PQXDHSpqrSetup) (τ : List MachineEvent) (wire : HwBytes) (v : Fin 4) (t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields), compFitsPinned w compI0 r → parsePreKeyWire wire = some p → p.preKeyId = none → ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩;
      Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ (runVis r ms) →
      MovesFrom InvisibleNoEffect (setupTrace r) pre → MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
      MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o → bobDoneBaseKeys (runTraceMoves r ms) = [] →
      let memo := fun u => (gamma' compI0 S g u).memo;
      let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo; let newMemo := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap memo;
      ∀ x ∈ preMemo ++ newMemo, CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x → RestEntry S g x
theorem split38PairsAt_qRest_of_entries {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hN : NonInj38CensusXZAt w τ wire v t) (hE : Rest38EntryAt w τ wire v t) (hNR : Split38PairsAt QRestNR w τ wire v t) (hRR : Split38PairsAt QRestRR w τ wire v t) (hXX : Split38PairsAt QRestXX w τ wire v t) (hTT : Split38PairsAt QRestTT w τ wire v t) : Split38PairsAt QRest w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have hN' := hN r S g p hfits hp hopk pre mid post hb shown cl e c'; have hE' := hE r S g p hfits hp hopk pre mid post hb shown cl e c'; have hNR' := hNR r S g p hfits hp hopk pre mid post hb shown cl e c'; have hRR' := hRR r S g p hfits hp hopk pre mid post hb shown cl e c'; have hXX' := hXX r S g p hfits hp hopk pre mid post hb shown cl e c'; have hTT' := hTT r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at hN' hE' hNR' hRR' hXX' hTT' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨u₁, hxu₁⟩ := exists_memo_of_mem1 hx₁; obtain ⟨u₂, hxu₂⟩ := exists_memo_of_mem hx₂; obtain ⟨-, hv₁⟩ := CompRPreMemoSound.memo_sound compI0 S g u₁ hxu₁; obtain ⟨-, hv₂⟩ := CompRPreMemoSound.memo_sound compI0 S g u₂ hxu₂; exact qRest_of_entries S g _ _ x₁ x₂ hv₁ hv₂ (hN' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ (List.mem_append_right _ hx₁) hc₁) (hN' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₂ hx₂ hc₂) (hE' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ (List.mem_append_right _ hx₁) hc₁) (hE' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₂ hx₂ hc₂) (hNR' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂) (hRR' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂) (hXX' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂) (hTT' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂)
end Symbolic.BugInjection.Proofs.Common443.CompC2Rest38
