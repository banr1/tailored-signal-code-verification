/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38QKdf
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc (zeroSaltedTermsStA)
open Symbolic.BugInjection.Proofs.Common443.CompRTag Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRWs81KdfHead Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.BugInjection.Proofs.Common443.CompRSplit38KdfHead Symbolic.BugInjection.Proofs.Common443.CompRSplit38QKdf Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def NonInjOff (v : HwBytes) : Prop := (v.length = 32 → KdfFree v) ∧
  (v.length = 8 → v.take 4 ≠ compTag4 ∧ v ∉ rowDigests.map (·.take 8))
def ZVal (v : HwBytes) : Prop := (v.length = 32 ∧ ¬ KdfFree v) ∨
  (v.length = 8 ∧ (v.take 4 = compTag4 ∨ v ∈ rowDigests.map (·.take 8)))
section Val
variable {S : Sem} {g : Ghost}
theorem not_kdfFree_kdfExtract (k m : DY.Bytes) : ¬ KdfFree (gamma compI0 S g (DY.KdfExtract.kdfExtract k m)) :=
  fun h => gamma_kdfExtract_ne_of_kdfFree (S := S) (g := g) (k := k) (m := m) h rfl
theorem zVal_kdfExtract (k m : DY.Bytes) : ZVal (gamma compI0 S g (DY.KdfExtract.kdfExtract k m)) := Or.inl ⟨gamma_kdfExtract_length k m, not_kdfFree_kdfExtract k m⟩
theorem zVal_trunc8_kdfExtract (k m : DY.Bytes) : ZVal (gamma compI0 S g (DY.Trunc.trunc8 (DY.KdfExtract.kdfExtract k m))) := by
  rw [gamma_trunc8_eq]; have hl := gamma_kdfExtract_length (S := S) (g := g) k m; refine Or.inr ⟨by rw [List.length_take, hl]; rfl, ?_⟩
  rcases gamma_kdfExtract_tag_or_row (S := S) (g := g) k m with h | h
  · left; rw [List.take_take, show min 4 8 = 4 from rfl, h]
  · right; exact List.mem_map.mpr ⟨_, h, rfl⟩
theorem not_zVal_of_nonInjOff {v : HwBytes} (h : NonInjOff v) : ¬ ZVal v := by
  rintro (⟨hl, hk⟩ | ⟨hl, ht | hr⟩)
  · exact hk (h.1 hl)
  · exact (h.2 hl).1 ht
  · exact (h.2 hl).2 hr
theorem zVal_of_mem_zeroSalted {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {u : DY.Bytes} (hu : u ∈ zeroSaltedTermsStA tr₂ stA cl pq) : ZVal (gamma compI0 S g u) := by
  unfold zeroSaltedTermsStA at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact zVal_kdfExtract _ _
  · exact zVal_kdfExtract _ _
  · exact zVal_kdfExtract _ _
  · exact zVal_kdfExtract _ _
  · exact zVal_kdfExtract _ _
  · exact zVal_trunc8_kdfExtract _ _
theorem kdfFree_or_len_of_nonInjOff {v : HwBytes} (h : NonInjOff v) : KdfFree v ∨ v.length ≠ 32 := by
  by_cases hl : v.length = 32
  · exact Or.inl (h.1 hl)
  · exact Or.inr hl
end Val
def NonInj38CensusAt (w : PQXDHSpqrSetup) (τ : List MachineEvent) (wire : HwBytes) (v : Fin 4) (t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields), compFitsPinned w compI0 r → parsePreKeyWire wire = some p → p.preKeyId = none → ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩;
      Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ (runVis r ms) → MovesFrom InvisibleNoEffect (setupTrace r) pre →
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
      MovesFrom InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
      bobDoneBaseKeys (runTraceMoves r ms) = [] →
      let memo := fun u => (gamma' compI0 S g u).memo;
      let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo; let newMemo := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap memo;
      ∀ x ∈ preMemo ++ newMemo, CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x → assumedInjective x.1 = false → NonInjOff x.2.2
theorem exists_memo_of_mem1 {S : Sem} {g : Ghost} {L : List DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ L.flatMap (fun u => (gamma' compI0 S g u).memo)) : ∃ u, x ∈ (gamma' compI0 S g u).memo := by obtain ⟨u, _, hum⟩ := List.mem_flatMap.mp hx; exact ⟨u, hum⟩
theorem exists_memo_of_mem {S : Sem} {g : Ghost} {L₁ L₂ : List DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ L₁.flatMap (fun u => (gamma' compI0 S g u).memo) ++ L₂.flatMap (fun u => (gamma' compI0 S g u).memo)) : ∃ u, x ∈ (gamma' compI0 S g u).memo := by
  rcases List.mem_append.mp hx with hm | hm
  · exact exists_memo_of_mem1 hm
  · exact exists_memo_of_mem1 hm
theorem qNonInjOffZ_of_off (S : Sem) (g : Ghost) (pm : List (DY.Bytes × DY.Bytes × HwBytes)) {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (u₂ : DY.Bytes) (hxu₂ : x₂ ∈ (gamma' compI0 S g u₂).memo) (u₁ : DY.Bytes) (hxu₁ : x₁ ∈ (gamma' compI0 S g u₁).memo) (h₁ : assumedInjective x₁.1 = false → NonInjOff x₁.2.2) (h₂ : assumedInjective x₂.1 = false → NonInjOff x₂.2.2) : QNonInjOffZ S g pm (zeroSaltedTermsStA tr₂ stA cl pq) x₁ x₂ := by
  obtain ⟨-, hv₁⟩ := CompRPreMemoSound.memo_sound compI0 S g u₁ hxu₁; obtain ⟨-, hv₂⟩ := CompRPreMemoSound.memo_sound compI0 S g u₂ hxu₂; refine ⟨fun hai hz he => ?_, fun hai hz he => ?_⟩
  · have hZ : ZVal x₂.2.2 := by rw [hv₂]; exact zVal_of_mem_zeroSalted hz
    exact not_zVal_of_nonInjOff (h₁ hai) (he ▸ hZ)
  · have hZ : ZVal x₁.2.2 := by rw [hv₁]; exact zVal_of_mem_zeroSalted hz
    exact not_zVal_of_nonInjOff (h₂ hai) (he ▸ hZ)
theorem ctxNonInjOffZ_of_census {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : NonInj38CensusAt w τ wire v t) : Split38CtxPairsAt QNonInjOffZ w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h' := h r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at h' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; have hc := h' hcompat hrun hvis hpre hmid hpost hm₀ hbd; obtain ⟨u₁, hxu₁⟩ := exists_memo_of_mem1 hx₁; obtain ⟨u₂, hxu₂⟩ := exists_memo_of_mem hx₂; exact qNonInjOffZ_of_off S g _ x₁ x₂ u₂ hxu₂ u₁ hxu₁ (hc x₁ (List.mem_append_right _ hx₁) hc₁) (hc x₂ hx₂ hc₂)
def QKdfKK : PairQ := fun S g known pts x₁ x₂ =>
  ∀ k₁ m₁ k₂ m₂ : DY.Bytes, x₁.1 = DY.KdfExtract.kdfExtract k₁ m₁ → x₂.1 = DY.KdfExtract.kdfExtract k₂ m₂ → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1 → UPar S g k₁ k₂ ∧ UPar S g m₁ m₂
def QKdfInjRest : PairQ := fun S g known pts x₁ x₂ =>
  ∀ k m : DY.Bytes, x₁.1 = DY.KdfExtract.kdfExtract k m → ¬ IsKdf x₂.1 → ¬ IsX x₂.1 → ¬ IsTrunc8 x₂.1 → assumedInjective x₂.1 = true → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1 → KdfFree (gamma compI0 S g x₂.1) ∨ (gamma compI0 S g x₂.1).length ≠ 32
theorem qKdfC_of (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (u₂ : DY.Bytes) (hxu₂ : x₂ ∈ (gamma' compI0 S g u₂).memo) (hKK : QKdfKK S g known pts x₁ x₂) (hR : QKdfInjRest S g known pts x₁ x₂) (hN : assumedInjective x₂.1 = false → NonInjOff x₂.2.2) : QKdfC S g known pts x₁ x₂ := by
  intro k m hk hs hu he; obtain ⟨-, hv₂⟩ := CompRPreMemoSound.memo_sound compI0 S g u₂ hxu₂
  by_cases hK : IsKdf x₂.1
  · obtain ⟨k₂, m₂, hk₂⟩ := hK; obtain ⟨hKk, hKm⟩ := hKK k m k₂ m₂ hk hk₂ hs hu he; exact Or.inl ⟨k₂, m₂, hk₂, hKk, hKm⟩
  by_cases hX : IsX x₂.1
  · rcases hX with ⟨s, hs'⟩ | ⟨p, s, hp'⟩
    · exact Or.inr (Or.inl ⟨s, hs'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, s, hp'⟩))
  by_cases hT : IsTrunc8 x₂.1
  · obtain ⟨a, ha⟩ := hT; refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); rw [ha, gamma_trunc8_eq, List.length_take]; omega
  cases hai : assumedInjective x₂.1
  · rcases kdfFree_or_len_of_nonInjOff (hN hai) with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hv₂]; exact h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hv₂]; exact h)))))
  · rcases hR k m hk hK hX hT hai hs hu he with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem split38PairsAt_qKdfC_of {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hKK : Split38PairsAt QKdfKK w τ wire v t) (hR : Split38PairsAt QKdfInjRest w τ wire v t) (hN : NonInj38CensusAt w τ wire v t) : Split38PairsAt QKdfC w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have hKK' := hKK r S g p hfits hp hopk pre mid post hb shown cl e c'; have hR' := hR r S g p hfits hp hopk pre mid post hb shown cl e c'; have hN' := hN r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at hKK' hR' hN' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨u₂, hxu₂⟩ := exists_memo_of_mem hx₂; exact qKdfC_of S g _ _ x₁ x₂ u₂ hxu₂ (hKK' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂) (hR' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂) (hN' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₂ hx₂ hc₂)
end Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census
