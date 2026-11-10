/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2Rest38

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2RestFn
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRNoBSC CompRPlantWire CompRTag CompRI0TermInj CompRSplit38PairCore CompRSplit38UntaggedShape CompRNonInj38Census CompRQRestCensusZ CompC2RestCore CompC2Rest38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def RestFnEntry (F : HwBytes → DY.Bytes) (Rv : HwBytes → Prop) (S : Sem) (g : Ghost) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := ((IsX x.1 ∨ IsTrunc8 x.1 ∨ (assumedInjective x.1 = true ∧ ¬ IsKdf x.1)) → (gamma' compI0 S g x.1).shape = F x.2.2) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → ¬ IsX x.1 → ¬ IsTrunc8 x.1 → Rv x.2.2) ∧ (assumedInjective x.1 = false → ¬ Rv x.2.2)
section Pair
variable {F : HwBytes → DY.Bytes} {Rv : HwBytes → Prop} {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {pts : List DY.Bytes} {x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes}
theorem shapeAgree_of_fn (hv₁ : x₁.2.2 = gamma compI0 S g x₁.1) (hv₂ : x₂.2.2 = gamma compI0 S g x₂.1) (h₁ : (gamma' compI0 S g x₁.1).shape = F x₁.2.2) (h₂ : (gamma' compI0 S g x₂.1).shape = F x₂.2.2) : ShapeAgree S g x₁.1 x₂.1 :=
  fun he => by rw [h₁, h₂, hv₁, hv₂, he]
theorem qRestNR_of_fn (hv₁ : x₁.2.2 = gamma compI0 S g x₁.1) (hv₂ : x₂.2.2 = gamma compI0 S g x₂.1) (hE₁ : RestFnEntry F Rv S g x₁) (hE₂ : RestFnEntry F Rv S g x₂) : QRestNR S g known pts x₁ x₂ := by
  intro hne hK₁ hX₁ hT₁ hK₂ hX₂ hT₂ _ _; apply shapeAgree_of_gamma_ne; intro he
  rcases Bool.eq_false_or_eq_true (assumedInjective x₁.1) with h₁ | h₁ <;>
    rcases Bool.eq_false_or_eq_true (assumedInjective x₂.1) with h₂ | h₂
  · exact hne (h₁.trans h₂.symm)
  · have hr := hE₁.2.1 h₁ hK₁ hX₁ hT₁; rw [hv₁, he, ← hv₂] at hr; exact hE₂.2.2 h₂ hr
  · have hr := hE₂.2.1 h₂ hK₂ hX₂ hT₂; rw [hv₂, ← he, ← hv₁] at hr; exact hE₁.2.2 h₁ hr
  · exact hne (h₁.trans h₂.symm)
theorem qRestRR_of_fn (hv₁ : x₁.2.2 = gamma compI0 S g x₁.1) (hv₂ : x₂.2.2 = gamma compI0 S g x₂.1) (hE₁ : RestFnEntry F Rv S g x₁) (hE₂ : RestFnEntry F Rv S g x₂) : QRestRR S g known pts x₁ x₂ :=
  fun h₁ h₂ hK₁ _ _ hK₂ _ _ _ _ =>
    shapeAgree_of_fn hv₁ hv₂ (hE₁.1 (Or.inr (Or.inr ⟨h₁, hK₁⟩))) (hE₂.1 (Or.inr (Or.inr ⟨h₂, hK₂⟩)))
theorem qRestXX_of_fn (hv₁ : x₁.2.2 = gamma compI0 S g x₁.1) (hv₂ : x₂.2.2 = gamma compI0 S g x₂.1) (hE₁ : RestFnEntry F Rv S g x₁) (hE₂ : RestFnEntry F Rv S g x₂) : QRestXX S g known pts x₁ x₂ :=
  fun hX₁ hX₂ _ _ _ => shapeAgree_of_fn hv₁ hv₂ (hE₁.1 (Or.inl hX₁)) (hE₂.1 (Or.inl hX₂))
theorem qRestTT_of_fn (hv₁ : x₁.2.2 = gamma compI0 S g x₁.1) (hv₂ : x₂.2.2 = gamma compI0 S g x₂.1) (hE₁ : RestFnEntry F Rv S g x₁) (hE₂ : RestFnEntry F Rv S g x₂) : QRestTT S g known pts x₁ x₂ :=
  fun hT₁ hT₂ _ _ => shapeAgree_of_fn hv₁ hv₂ (hE₁.1 (Or.inr (Or.inl hT₁))) (hE₂.1 (Or.inr (Or.inl hT₂)))
end Pair
def Rest38FnAt (w : PQXDHSpqrSetup) (τ : List MachineEvent) (wire : HwBytes) (v : Fin 4) (t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields), compFitsPinned w compI0 r → parsePreKeyWire wire = some p → p.preKeyId = none → ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩;
      Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ (runVis r ms) →
      MovesFrom InvisibleNoEffect (setupTrace r) pre → MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
      MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o → bobDoneBaseKeys (runTraceMoves r ms) = [] →
      let memo := fun u => (gamma' compI0 S g u).memo;
      let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo; let newMemo := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap memo;
      ∃ (F : HwBytes → DY.Bytes) (Rv : HwBytes → Prop), ∀ x ∈ preMemo ++ newMemo, CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x → RestFnEntry F Rv S g x
theorem split38PairsAt_of_fn {Q : PairQ} (hQ : ∀ (F : HwBytes → DY.Bytes) (Rv : HwBytes → Prop) (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes), x₁.2.2 = gamma compI0 S g x₁.1 → x₂.2.2 = gamma compI0 S g x₂.1 → RestFnEntry F Rv S g x₁ → RestFnEntry F Rv S g x₂ → Q S g known pts x₁ x₂) {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : Rest38FnAt w τ wire v t) : Split38PairsAt Q w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h' := h r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at h' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨F, Rv, hF⟩ := h' hcompat hrun hvis hpre hmid hpost hm₀ hbd; obtain ⟨u₁, hxu₁⟩ := exists_memo_of_mem1 hx₁; obtain ⟨u₂, hxu₂⟩ := exists_memo_of_mem hx₂; obtain ⟨-, hv₁⟩ := CompRPreMemoSound.memo_sound compI0 S g u₁ hxu₁; obtain ⟨-, hv₂⟩ := CompRPreMemoSound.memo_sound compI0 S g u₂ hxu₂; exact hQ F Rv S g _ _ x₁ x₂ hv₁ hv₂ (hF x₁ (List.mem_append_right _ hx₁) hc₁) (hF x₂ hx₂ hc₂)
theorem split38PairsAt_qRest_of_fn {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hN : NonInj38CensusXZAt w τ wire v t) (hE : Rest38EntryAt w τ wire v t) (hF : Rest38FnAt w τ wire v t) : Split38PairsAt QRest w τ wire v t :=
  split38PairsAt_qRest_of_entries hN hE
    (split38PairsAt_of_fn (fun _ _ _ _ _ _ _ _ hv₁ hv₂ h₁ h₂ => qRestNR_of_fn hv₁ hv₂ h₁ h₂) hF)
    (split38PairsAt_of_fn (fun _ _ _ _ _ _ _ _ hv₁ hv₂ h₁ h₂ => qRestRR_of_fn hv₁ hv₂ h₁ h₂) hF)
    (split38PairsAt_of_fn (fun _ _ _ _ _ _ _ _ hv₁ hv₂ h₁ h₂ => qRestXX_of_fn hv₁ hv₂ h₁ h₂) hF)
    (split38PairsAt_of_fn (fun _ _ _ _ _ _ _ _ hv₁ hv₂ h₁ h₂ => qRestTT_of_fn hv₁ hv₂ h₁ h₂) hF)
end Symbolic.BugInjection.Proofs.Common443.CompC2RestFn
