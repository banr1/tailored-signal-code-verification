/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census
public import Symbolic.BugInjection.Proofs.Common443.CompRWs81KdfHead
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompC2KdfKK
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj (shape_kdfExtract gamma_kdfExtract)
open Symbolic.BugInjection.Proofs.Common443.CompRWs81KdfHead (UPar hmac_key_untagged hmac_msg_untagged)
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore (PairSide QUntagged)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (QKdfKK)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemo38KdfCensus (KdfSalt32)
variable {S : Sem} {g : Ghost}
theorem memo_kdfExtract (k m : DY.Bytes) : (gamma' compI0 S g (DY.KdfExtract.kdfExtract k m)).memo = (DY.KdfExtract.kdfExtract k m, (gamma' compI0 S g (DY.KdfExtract.kdfExtract k m)).shape, gamma compI0 S g (DY.KdfExtract.kdfExtract k m)) :: ((gamma' compI0 S g k).memo ++ (gamma' compI0 S g m).memo) := by have h := CompRPreMemoSound.ms_pack_kdf compI0 S g ⟨k, m⟩; unfold gamma; rw [show DY.KdfExtract.kdfExtract k m = (⟨k, m⟩ : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl, h]; simp [gKdf0, concretizeKdf, node]
def selfE (S : Sem) (g : Ghost) (c : DY.Bytes) : DY.Bytes × DY.Bytes × HwBytes := (c, (gamma' compI0 S g c).shape, gamma compI0 S g c)
theorem kdfPartnerC_of_pair (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (u₂ : DY.Bytes) (hxu₂ : x₂ ∈ (gamma' compI0 S g u₂).memo) (hKK : QKdfKK S g known pts x₁ x₂) (hR : CompRNonInj38Census.QKdfInjRest S g known pts x₁ x₂) (hN : assumedInjective x₂.1 = false → (x₂.2.2.length = 32 → CompRI0TermInj.KdfFree x₂.2.2) ∧ (x₂.2.2.length = 8 → x₂.2.2.take 4 ≠ compTag4)) (k m : DY.Bytes) (hk : x₁.1 = DY.KdfExtract.kdfExtract k m) (hps : PairSide known pts x₁ x₂) (hu : (gamma compI0 S g x₁.1).take 4 ≠ compTag4) (he : gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1) : CompRSplit38QKdf.KdfPartnerC S g k m x₂.1 := by
  obtain ⟨-, hv₂⟩ := CompRPreMemoSound.memo_sound compI0 S g u₂ hxu₂
  rcases Classical.em (CompRSplit38UntaggedShape.IsKdf x₂.1) with ⟨k₂, m₂, hk₂⟩ | hK
  · obtain ⟨hKk, hKm⟩ := hKK k m k₂ m₂ hk hk₂ hps hu he; exact Or.inl ⟨k₂, m₂, hk₂, hKk, hKm⟩
  rcases Classical.em (CompRSplit38UntaggedShape.IsX x₂.1) with (⟨s, hs'⟩ | ⟨p, s, hp'⟩) | hX
  · exact Or.inr (Or.inl ⟨s, hs'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, s, hp'⟩))
  rcases Classical.em (CompRSplit38UntaggedShape.IsTrunc8 x₂.1) with ⟨a, ha⟩ | hT
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); rw [ha, CompFreshDistinct.gamma_trunc8_eq, List.length_take]; omega
  cases hai : assumedInjective x₂.1
  · rcases Classical.em (x₂.2.2.length = 32) with hl | hl
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hv₂ ▸ (hN hai).1 hl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hv₂ ▸ hl)))))
  · exact (hR k m hk hK hX hT hai hps hu he).elim
      (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
      (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem qUntagged_of_pair (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (u₂ : DY.Bytes) (hxu₂ : x₂ ∈ (gamma' compI0 S g u₂).memo) (hs₁ : KdfSalt32 S g x₁) (hs₂ : KdfSalt32 S g x₂) (hN : assumedInjective x₂.1 = false → (x₂.2.2.length = 32 → CompRI0TermInj.KdfFree x₂.2.2) ∧ (x₂.2.2.length = 8 → x₂.2.2.take 4 ≠ compTag4)) (hKK : QKdfKK S g known pts x₁ x₂) (hR : CompRNonInj38Census.QKdfInjRest S g known pts x₁ x₂) (hNK : CompRSplit38UntaggedShape.QRest S g known pts x₁ x₂) : QUntagged S g known pts x₁ x₂ := CompRSplit38UntaggedShape.qUntagged_of_kdf_rest S g known pts x₁ x₂ (CompRSplit38KdfHead.qKdf_of_head S g known pts x₁ x₂
      (CompRSplit38KdfHead.qKdfHead_of_32 S g known pts x₁ x₂ fun k m hk hps hu he =>
        CompRSplit38QKdf.kdfPartner32_of_c (hs₁ k m hk) hs₂ (kdfPartnerC_of_pair known pts x₁ x₂ u₂ hxu₂ hKK hR hN k m hk hps hu he))) hNK
theorem memo_closed_flatMap (L : List DY.Bytes) (x : DY.Bytes × DY.Bytes × HwBytes) (hx : x ∈ L.flatMap (fun u => (gamma' compI0 S g u).memo)) : ∀ e ∈ (gamma' compI0 S g x.1).memo, e ∈ L.flatMap (fun u => (gamma' compI0 S g u).memo) := by
  obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
  exact fun e he => List.mem_flatMap.mpr ⟨t, ht, CompRPreMemoSound.memo_trans compI0 S g t hxt e he⟩
theorem memo_concat (a b : DY.Bytes) : (gamma' compI0 S g (DY.Concat.concat a b)).memo = (DY.Concat.concat a b, (gamma' compI0 S g (DY.Concat.concat a b)).shape, gamma compI0 S g (DY.Concat.concat a b)) :: ((gamma' compI0 S g a).memo ++ (gamma' compI0 S g b).memo) := by have h := CompRPreMemoSound.ms_pack_concat compI0 S g ⟨a, b⟩; unfold gamma; rw [show DY.Concat.concat a b = (⟨a, b⟩ : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, h]; simp [gConcat0, concretizeConcat, node]
inductive ChildOK2 (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) : DY.Bytes → DY.Bytes → Prop
  | upar {c₁ c₂ : DY.Bytes} (h : UPar S g c₁ c₂) : ChildOK2 S g known pts c₁ c₂
  | self {c₁ c₂ : DY.Bytes} (hs₁ : selfE S g c₁ ∈ (gamma' compI0 S g c₁).memo)
      (hs₂ : selfE S g c₂ ∈ (gamma' compI0 S g c₂).memo)
      (hps : PairSide known pts (selfE S g c₁) (selfE S g c₂)) : ChildOK2 S g known pts c₁ c₂
  | concat {a₁ a₂ b₁ b₂ : DY.Bytes}
      (hl : (gamma compI0 S g a₁).length = (gamma compI0 S g a₂).length)
      (hA : ChildOK2 S g known pts a₁ a₂)
      (hbu : (gamma compI0 S g (DY.Concat.concat a₁ b₁)).take 4 ≠ compTag4 → (gamma compI0 S g b₁).take 4 ≠ compTag4)
      (hB : ChildOK2 S g known pts b₁ b₂) :
      ChildOK2 S g known pts (DY.Concat.concat a₁ b₁) (DY.Concat.concat a₂ b₂)
def QKdfChild2 (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) : Prop := ∀ k₁ m₁ k₂ m₂ : DY.Bytes, x₁.1 = DY.KdfExtract.kdfExtract k₁ m₁ → x₂.1 = DY.KdfExtract.kdfExtract k₂ m₂ → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1 → ChildOK2 S g known pts k₁ k₂ ∧ ChildOK2 S g known pts m₁ m₂
theorem qKdfKK_of_child2 (known : DY.Bytes → Prop) (pts : List DY.Bytes) (N A : DY.Bytes × DY.Bytes × HwBytes → Prop) (hNc : ∀ x, N x → ∀ e ∈ (gamma' compI0 S g x.1).memo, N e) (hAc : ∀ x, A x → ∀ e ∈ (gamma' compI0 S g x.1).memo, A e) (hC : ∀ x₁ x₂, N x₁ → A x₂ → QKdfChild2 S g known pts x₁ x₂) (hQ : ∀ x₁ x₂, N x₁ → A x₂ → QKdfKK S g known pts x₁ x₂ → QUntagged S g known pts x₁ x₂) : ∀ x₁ x₂, N x₁ → A x₂ → QKdfKK S g known pts x₁ x₂ := by
  suffices H : ∀ n x₁ x₂, (gamma' compI0 S g x₁.1).memo.length ≤ n → N x₁ → A x₂ → QKdfKK S g known pts x₁ x₂ from
    fun x₁ x₂ h₁ h₂ => H _ x₁ x₂ (Nat.le_refl _) h₁ h₂
  intro n
  induction n with
  | zero =>
    intro x₁ x₂ hn _ _ k₁ m₁ _ _ h₁ _ _ _ _; rw [h₁, memo_kdfExtract] at hn; simp at hn
  | succ n ih =>
    intro x₁ x₂ hn hN₁ hA₂ k₁ m₁ k₂ m₂ h₁ h₂ hps hu he; obtain ⟨cK, cM⟩ := hC x₁ x₂ hN₁ hA₂ k₁ m₁ k₂ m₂ h₁ h₂ hps hu he; have hm₁ : ∀ e ∈ (gamma' compI0 S g (DY.KdfExtract.kdfExtract k₁ m₁)).memo, N e := h₁ ▸ hNc x₁ hN₁; have hm₂ : ∀ e ∈ (gamma' compI0 S g (DY.KdfExtract.kdfExtract k₂ m₂)).memo, A e := h₂ ▸ hAc x₂ hA₂
    have hlen : (gamma' compI0 S g x₁.1).memo.length =
        (gamma' compI0 S g k₁).memo.length + (gamma' compI0 S g m₁).memo.length + 1 := by
      rw [h₁, memo_kdfExtract, List.length_cons, List.length_append]
    have child : ∀ c₁ c₂ : DY.Bytes, ChildOK2 S g known pts c₁ c₂ → (∀ e ∈ (gamma' compI0 S g c₁).memo, N e) → (∀ e ∈ (gamma' compI0 S g c₂).memo, A e) →
        (gamma' compI0 S g c₁).memo.length ≤ n → UPar S g c₁ c₂ := by
      intro c₁ c₂ hc
      induction hc with
      | upar h => intro _ _ _; exact h
      | @self d₁ d₂ hs₁ hs₂ hps' =>
        intro hN hA hl
        by_cases hdu : (gamma compI0 S g d₁).take 4 = compTag4
        · exact .base fun _ hu' => absurd hdu hu'
        · exact UPar.of_shapeAgree (hQ _ _ (hN _ hs₁) (hA _ hs₂) (ih (selfE S g d₁) (selfE S g d₂) hl (hN _ hs₁) (hA _ hs₂)) hps' hdu)
      | @concat a₁ a₂ b₁ b₂ hl' _ hbu _ ihA ihB =>
        intro hN hA hl; rw [memo_concat] at hl; simp only [List.length_cons, List.length_append] at hl
        refine .concat hl' (ihA ?_ ?_ (by omega)) hbu (ihB ?_ ?_ (by omega)) <;>
          (intro e he'; first | exact hN e (by rw [memo_concat]; simp [he']) | exact hA e (by rw [memo_concat]; simp [he']))
    refine ⟨child k₁ k₂ cK ?_ ?_ (by omega), child m₁ m₂ cM ?_ ?_ (by omega)⟩ <;>
      (intro e he'; first | exact hm₁ e (by rw [memo_kdfExtract]; simp [he']) | exact hm₂ e (by rw [memo_kdfExtract]; simp [he']))
theorem qKdfKK_lists2 (known : DY.Bytes → Prop) (pts : List DY.Bytes) (Lp Ln : List DY.Bytes) (C : DY.Bytes × DY.Bytes × HwBytes → Prop) (hCl : ∀ x ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), C x) (hS : ∀ x ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), C x → KdfSalt32 S g x) (hN : ∀ x ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), C x → assumedInjective x.1 = false → (x.2.2.length = 32 → CompRI0TermInj.KdfFree x.2.2) ∧ (x.2.2.length = 8 → x.2.2.take 4 ≠ compTag4)) (hR : ∀ x₁ ∈ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), ∀ x₂ ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), C x₁ → C x₂ → CompRNonInj38Census.QKdfInjRest S g known pts x₁ x₂) (hNK : ∀ x₁ ∈ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), ∀ x₂ ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), C x₁ → C x₂ → CompRSplit38UntaggedShape.QRest S g known pts x₁ x₂) (hCh : ∀ x₁ ∈ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), ∀ x₂ ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), C x₁ → C x₂ → QKdfChild2 S g known pts x₁ x₂) : ∀ x₁ ∈ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), ∀ x₂ ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo), C x₁ → C x₂ → QKdfKK S g known pts x₁ x₂ := by
  have hNA : ∀ x ∈ Ln.flatMap (fun u => (gamma' compI0 S g u).memo),
      x ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo) :=
    fun _ hx => List.mem_append_right _ hx
  intro x₁ hx₁ x₂ hx₂ _ _
  refine qKdfKK_of_child2 known pts
    (fun x => x ∈ Ln.flatMap (fun u => (gamma' compI0 S g u).memo))
    (fun x => x ∈ Lp.flatMap (fun u => (gamma' compI0 S g u).memo) ++ Ln.flatMap (fun u => (gamma' compI0 S g u).memo))
    (fun x hx => memo_closed_flatMap Ln x hx)
    (fun x hx e he => (List.mem_append.mp hx).elim
      (fun h => List.mem_append_left _ (memo_closed_flatMap Lp x h e he))
      (fun h => List.mem_append_right _ (memo_closed_flatMap Ln x h e he)))
    (fun y₁ y₂ hy₁ hy₂ => hCh y₁ hy₁ y₂ hy₂ (hCl y₁ (hNA y₁ hy₁)) (hCl y₂ hy₂))
    (fun y₁ y₂ hy₁ hy₂ hKK =>
      let ⟨u₂, hyu₂⟩ := CompRNonInj38Census.exists_memo_of_mem hy₂;
      qUntagged_of_pair known pts y₁ y₂ u₂ hyu₂ (hS y₁ (hNA y₁ hy₁) (hCl y₁ (hNA y₁ hy₁))) (hS y₂ hy₂ (hCl y₂ hy₂)) (hN y₂ hy₂ (hCl y₂ hy₂)) hKK (hR y₁ hy₁ y₂ hy₂ (hCl y₁ (hNA y₁ hy₁)) (hCl y₂ hy₂)) (hNK y₁ hy₁ y₂ hy₂ (hCl y₁ (hNA y₁ hy₁)) (hCl y₂ hy₂))) x₁ x₂ hx₁ hx₂
section Split38b
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore (Split38PairsAt)
open Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census (NonInj38CensusAt NonInjOff)
theorem split38PairsAt_qKdfKK_of_child2 {w : PQXDHSpqrSetup} {τ : List DY.Libsignal.HwEvents.MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hN : NonInj38CensusAt w τ wire v t) (hR : Split38PairsAt CompRNonInj38Census.QKdfInjRest w τ wire v t) (hNK : Split38PairsAt CompRSplit38UntaggedShape.QRest w τ wire v t) (hCh : Split38PairsAt QKdfChild2 w τ wire v t) : Split38PairsAt QKdfKK w τ wire v t := by
  intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have hN' := hN r S g p hfits hp hopk pre mid post hb shown cl e c'; have hR' := hR r S g p hfits hp hopk pre mid post hb shown cl e c'; have hNK' := hNK r S g p hfits hp hopk pre mid post hb shown cl e c'; have hCh' := hCh r S g p hfits hp hopk pre mid post hb shown cl e c'; have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hcen := CompRSplit38QKdf.kdfSalt32_of_split38MemoClass (S := S) (g := g) hNe pre mid post hb shown cl e c'; dsimp only at hN' hR' hNK' hCh' hcen ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd
  exact qKdfKK_lists2 _ _ _ _ _
    (fun _ hx => CompRNbsc38VT.split38MemoClass_of_preOrNewMemo hNe hopk hpre hmid hpost hm₀ hx)
    (fun x _ hc => hcen hrun hpre hmid hpost hm₀ x hc)
    (fun x hx hc hai => let ⟨h32, h8⟩ := hN' hcompat hrun hvis hpre hmid hpost hm₀ hbd x hx hc hai;
      ⟨h32, fun hl => (h8 hl).1⟩)
    (hR' hcompat hrun hvis hpre hmid hpost hm₀ hbd)
    (hNK' hcompat hrun hvis hpre hmid hpost hm₀ hbd)
    (hCh' hcompat hrun hvis hpre hmid hpost hm₀ hbd)
end Split38b
end Symbolic.BugInjection.Proofs.Common443.CompC2KdfKK
