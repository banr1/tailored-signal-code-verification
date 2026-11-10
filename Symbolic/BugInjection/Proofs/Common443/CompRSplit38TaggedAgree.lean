/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc (zeroSaltedTermsStA)
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
abbrev CtxQ : Type := Sem → Ghost → List (DY.Bytes × DY.Bytes × HwBytes) → List DY.Bytes → DY.Bytes × DY.Bytes × HwBytes → DY.Bytes × DY.Bytes × HwBytes → Prop
def Split38CtxPairsAt (R : CtxQ) (w : PQXDHSpqrSetup) (τ : List MachineEvent) (wire : HwBytes) (v : Fin 4) (t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields), compFitsPinned w compI0 r → parsePreKeyWire wire = some p → p.preKeyId = none → ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩;
      Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ (runVis r ms) → MovesFrom InvisibleNoEffect (setupTrace r) pre →
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
      MovesFrom InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
      bobDoneBaseKeys (runTraceMoves r ms) = [] →
      let memo := fun u => (gamma' compI0 S g u).memo;
      let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo; let newMemo := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap memo;
      ∀ x₁ ∈ newMemo, ∀ x₂ ∈ preMemo ++ newMemo, CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x₁ → CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x₂ → R S g preMemo (zeroSaltedTermsStA tr₂ stA cl pq) x₁ x₂
def QPreUntagged : CtxQ := fun _ _ pm _ x₁ x₂ =>
  (x₁ ∈ pm → assumedInjective x₁.1 = true → x₁.2.2.take 4 ≠ compTag4) ∧ (x₂ ∈ pm → assumedInjective x₂.1 = true → x₂.2.2.take 4 ≠ compTag4)
def QNonInjOffZ : CtxQ := fun _ _ _ Z x₁ x₂ =>
  (assumedInjective x₁.1 = false → x₂.1 ∈ Z → x₁.2.2 ≠ x₂.2.2) ∧ (assumedInjective x₂.1 = false → x₁.1 ∈ Z → x₁.2.2 ≠ x₂.2.2)
theorem nonInj_or_z_of_tagged {pm : List (DY.Bytes × DY.Bytes × HwBytes)} {Z : List DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hc : x ∈ pm ∨ assumedInjective x.1 = false ∨ x.1 ∈ Z) (hP : x ∈ pm → assumedInjective x.1 = true → x.2.2.take 4 ≠ compTag4) (ht : x.2.2.take 4 = compTag4) : assumedInjective x.1 = false ∨ x.1 ∈ Z := by
  rcases hc with h | h | h
  · cases hi : assumedInjective x.1
    · exact Or.inl rfl
    · exact absurd ht (hP h hi)
  · exact Or.inl h
  · exact Or.inr h
def QPreUntaggedNX : CtxQ := fun _ _ pm _ x₁ x₂ =>
  (x₁ ∈ pm → assumedInjective x₁.1 = true → x₁.2.2 ∉ CompRI0TermInj.x25519Vals → x₁.2.2.take 4 ≠ compTag4) ∧ (x₂ ∈ pm → assumedInjective x₂.1 = true → x₂.2.2 ∉ CompRI0TermInj.x25519Vals → x₂.2.2.take 4 ≠ compTag4)
theorem qPreUntagged_of_nx (S : Sem) (g : Ghost) (pm : List (DY.Bytes × DY.Bytes × HwBytes)) (Z : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (h : QPreUntaggedNX S g pm Z x₁ x₂) : QPreUntagged S g pm Z x₁ x₂ := by
  refine ⟨fun hm hi => ?_, fun hm hi => ?_⟩
  · by_cases hx : x₁.2.2 ∈ CompRI0TermInj.x25519Vals
    · exact CompRI0TermInj.x25519Vals_untagged _ hx
    · exact h.1 hm hi hx
  · by_cases hx : x₂.2.2 ∈ CompRI0TermInj.x25519Vals
    · exact CompRI0TermInj.x25519Vals_untagged _ hx
    · exact h.2 hm hi hx
theorem split38CtxPairsAt_mono {R₁ R₂ : CtxQ} {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hR : ∀ (S : Sem) (g : Ghost) (pm : List (DY.Bytes × DY.Bytes × HwBytes)) (Z : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes), R₁ S g pm Z x₁ x₂ → R₂ S g pm Z x₁ x₂) (h : Split38CtxPairsAt R₁ w τ wire v t) : Split38CtxPairsAt R₂ w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h' := h r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at h' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; exact hR S g _ _ x₁ x₂ (h' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂)
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38TaggedAgree
