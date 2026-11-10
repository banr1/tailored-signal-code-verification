/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZTag
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc (zeroSaltedTermsStA)
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def QZInjT : CtxQ := fun S g _ Z x₁ x₂ =>
  x₁.1 ∈ Z → x₂.1 ∈ Z → (gamma compI0 S g x₁.1).take 4 = compTag4 → gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1 → x₁.1 = x₂.1
theorem qTagged_of_partsT (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (pm : List (DY.Bytes × DY.Bytes × HwBytes)) (Z : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (u₁ u₂ : DY.Bytes) (hxu₁ : x₁ ∈ (gamma' compI0 S g u₁).memo) (hxu₂ : x₂ ∈ (gamma' compI0 S g u₂).memo) (hc₁ : x₁ ∈ pm ∨ assumedInjective x₁.1 = false ∨ x₁.1 ∈ Z) (hc₂ : x₂ ∈ pm ∨ assumedInjective x₂.1 = false ∨ x₂.1 ∈ Z) (hZ : QZInjT S g pm Z x₁ x₂) (hP : QPreUntagged S g pm Z x₁ x₂) (hN : QNonInjOffZ S g pm Z x₁ x₂) : QTagged S g known pts x₁ x₂ := by
  intro hs ht hv; have ht₂ : x₂.2.2.take 4 = compTag4 := hv ▸ ht
  rcases nonInj_or_z_of_tagged hc₁ hP.1 ht with h₁ | h₁ <;>
    rcases nonInj_or_z_of_tagged hc₂ hP.2 ht₂ with h₂ | h₂
  · exfalso
    rcases hs.1 with h | h
    · rw [h₁] at h; cases h
    · rw [h₂] at h; cases h
  · exact absurd hv (hN.1 h₁ h₂)
  · exact absurd hv (hN.2 h₂ h₁)
  · obtain ⟨hs₁, hv₁⟩ := CompRPreMemoSound.memo_sound compI0 S g u₁ hxu₁; obtain ⟨hs₂, hv₂⟩ := CompRPreMemoSound.memo_sound compI0 S g u₂ hxu₂; have he := hZ h₁ h₂ (by rw [← hv₁]; exact ht) (by rw [← hv₁, ← hv₂]; exact hv); rw [hs₁, hs₂, he]
theorem taggedW_of_partsT {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hZ : Split38CtxPairsAt QZInjT w τ wire v t) (hP : Split38CtxPairsAt QPreUntagged w τ wire v t) (hN : Split38CtxPairsAt QNonInjOffZ w τ wire v t) : Split38PairsAt QTagged w τ wire v t := by
  intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have hZ' := hZ r S g p hfits hp hopk pre mid post hb shown cl e c'; have hP' := hP r S g p hfits hp hopk pre mid post hb shown cl e c'; have hN' := hN r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at hZ' hP' hN' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; have z := hZ' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; have pp := hP' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; have nn := hN' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨u₁, _, hxu₁⟩ := List.mem_flatMap.mp hx₁
  obtain ⟨u₂, hxu₂⟩ : ∃ u₂, x₂ ∈ (gamma' compI0 S g u₂).memo := by
    rcases List.mem_append.mp hx₂ with hm | hm <;>
    · obtain ⟨u, _, hum⟩ := List.mem_flatMap.mp hm; exact ⟨u, hum⟩
  exact qTagged_of_partsT S g _ _ _ _ x₁ x₂ u₁ u₂ hxu₁ hxu₂ hc₁ hc₂ z pp nn
theorem split38CtxPairsAt_mono_z {R₁ R₂ : CtxQ} {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : ∀ (S : Sem) (g : Ghost) (pm : List (DY.Bytes × DY.Bytes × HwBytes)) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes), R₁ S g pm (zeroSaltedTermsStA tr₂ stA cl pq) x₁ x₂ → R₂ S g pm (zeroSaltedTermsStA tr₂ stA cl pq) x₁ x₂) (h₁ : Split38CtxPairsAt R₁ w τ wire v t) : Split38CtxPairsAt R₂ w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h₁' := h₁ r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at h₁' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; exact h _ _ _ _ _ _ _ _ _ (h₁' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂)
theorem zeroSalted_eq (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : zeroSaltedTermsStA tr₂ stA cl pq = (zeroSaltedTermsStA tr₂ stA cl pq).take 5 ++ [DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq)] :=
  rfl
theorem gamma_length_take5 (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : ∀ u ∈ (zeroSaltedTermsStA tr₂ stA cl pq).take 5, (gamma compI0 S g u).length = 32 := by
  intro u hu; simp only [zeroSaltedTermsStA, List.take, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl <;> exact gamma_hmac_length S g _ _
theorem gamma_length_zmac (S : Sem) (g : Ghost) (mk a b w : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk a b w)).length = 8 := by rw [CompRNbsc38MacKey.gamma_computeMac, List.length_take, gamma_hmac_length]; rfl
def QZInj5T : CtxQ := fun S g _ Z x₁ x₂ =>
  x₁.1 ∈ Z.take 5 → x₂.1 ∈ Z.take 5 → (gamma compI0 S g x₁.1).take 4 = compTag4 → gamma compI0 S g x₁.1 = gamma compI0 S g x₂.1 → x₁.1 = x₂.1
theorem qZInjT_of_5 (S : Sem) (g : Ghost) (pm : List (DY.Bytes × DY.Bytes × HwBytes)) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (h : QZInj5T S g pm (zeroSaltedTermsStA tr₂ stA cl pq) x₁ x₂) : QZInjT S g pm (zeroSaltedTermsStA tr₂ stA cl pq) x₁ x₂ := by
  intro h₁ h₂ ht he; rw [zeroSalted_eq] at h₁ h₂; have hL := gamma_length_take5 S g tr₂ stA cl pq
  rcases List.mem_append.mp h₁ with h₁ | h₁ <;> rcases List.mem_append.mp h₂ with h₂ | h₂
  · exact h h₁ h₂ ht he
  · exfalso; rw [List.mem_singleton] at h₂; have l₁ := hL _ h₁; rw [he, h₂, gamma_length_zmac] at l₁; cases l₁
  · exfalso; rw [List.mem_singleton] at h₁; have l₂ := hL _ h₂; rw [← he, h₁, gamma_length_zmac] at l₂; cases l₂
  · rw [List.mem_singleton] at h₁ h₂; rw [h₁, h₂]
theorem split38CtxPairsAt_qZInjT_of_5 {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : Split38CtxPairsAt QZInj5T w τ wire v t) : Split38CtxPairsAt QZInjT w τ wire v t :=
  split38CtxPairsAt_mono_z (fun S g pm tr₂ stA cl pq x₁ x₂ hx => qZInjT_of_5 S g pm tr₂ stA cl pq x₁ x₂ hx) h
def QZNodup5 : CtxQ := fun S g _ Z _ _ => ((Z.take 5).map (gamma compI0 S g)).Nodup
theorem qZInj5T_of_nodup (S : Sem) (g : Ghost) (pm : List (DY.Bytes × DY.Bytes × HwBytes)) (Z : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (h : QZNodup5 S g pm Z x₁ x₂) : QZInj5T S g pm Z x₁ x₂ :=
  fun h₁ h₂ _ he => List.inj_on_of_nodup_map h h₁ h₂ he
theorem split38CtxPairsAt_qZInjT_of_nodup {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : Split38CtxPairsAt QZNodup5 w τ wire v t) : Split38CtxPairsAt QZInjT w τ wire v t :=
  split38CtxPairsAt_qZInjT_of_5
    (split38CtxPairsAt_mono (fun S g pm Z x₁ x₂ hx => qZInj5T_of_nodup S g pm Z x₁ x₂ hx) h)
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZTag
