/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VTDefs
public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged
public import Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRPlantWire Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def PairSide (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) : Prop := (assumedInjective x₁.1 ∨ assumedInjective x₂.1) ∧ (x₁.1 ∈ pts → x₂.1 ∉ pts ∧ assumedInjective x₂.1 ∧ ¬ known x₂.1) ∧ (x₂.1 ∈ pts → x₁.1 ∉ pts ∧ assumedInjective x₁.1 ∧ ¬ known x₁.1)
theorem pairSide_of_collides {known : DY.Bytes → Prop} {pts : List DY.Bytes} {x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes} (h : CompRNbsc38VT.MemoPairCollides known pts x₁ x₂) : PairSide known pts x₁ x₂ := ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩
abbrev PairQ : Type := Sem → Ghost → (DY.Bytes → Prop) → List DY.Bytes → DY.Bytes × DY.Bytes × HwBytes → DY.Bytes × DY.Bytes × HwBytes → Prop
def Split38PairsAt (Q : PairQ) (w : PQXDHSpqrSetup) (τ : List MachineEvent) (wire : HwBytes) (v : Fin 4) (t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields), compFitsPinned w compI0 r → parsePreKeyWire wire = some p → p.preKeyId = none → ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩;
      Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ (runVis r ms) → MovesFrom InvisibleNoEffect (setupTrace r) pre →
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
      MovesFrom InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o →
      bobDoneBaseKeys (runTraceMoves r ms) = [] →
      let memo := fun u => (gamma' compI0 S g u).memo;
      let preMemo := (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap memo; let newMemo := ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap memo;
      let known := fun u : DY.Bytes => u.AttackerKnows (runTraceMoves r ms');
      let pts := plaintextTerms (runVis r ms');
      ∀ x₁ ∈ newMemo, ∀ x₂ ∈ preMemo ++ newMemo, CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x₁ → CompRNbsc38VT.Split38MemoClass r S g ms' tr₁ tr₂ cl x₂ → Q S g known pts x₁ x₂
theorem split38PairsAt_mono {Q₁ Q₂ : PairQ} {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hQ : ∀ (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (u₁ u₂ : DY.Bytes), x₁ ∈ (gamma' compI0 S g u₁).memo → x₂ ∈ (gamma' compI0 S g u₂).memo → Q₁ S g known pts x₁ x₂ → Q₂ S g known pts x₁ x₂) (h : Split38PairsAt Q₁ w τ wire v t) : Split38PairsAt Q₂ w τ wire v t := by
  intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h' := h r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at h' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; have hq := h' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; obtain ⟨u₁, _, hxu₁⟩ := List.mem_flatMap.mp hx₁
  obtain ⟨u₂, hxu₂⟩ : ∃ u₂, x₂ ∈ (gamma' compI0 S g u₂).memo := by
    rcases List.mem_append.mp hx₂ with hm | hm <;>
    · obtain ⟨u, _, hum⟩ := List.mem_flatMap.mp hm; exact ⟨u, hum⟩
  exact hQ S g _ _ x₁ x₂ u₁ u₂ hxu₁ hxu₂ hq
theorem split38PairsAt_and {Q₁ Q₂ : PairQ} {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h₁ : Split38PairsAt Q₁ w τ wire v t) (h₂ : Split38PairsAt Q₂ w τ wire v t) : Split38PairsAt (fun S g known pts x₁ x₂ => Q₁ S g known pts x₁ x₂ ∧ Q₂ S g known pts x₁ x₂) w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h₁' := h₁ r S g p hfits hp hopk pre mid post hb shown cl e c'; have h₂' := h₂ r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at h₁' h₂' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; exact ⟨h₁' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂, h₂' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂⟩
theorem split38PairsAt_of₂ {Q₁ Q₂ Q : PairQ} {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hQ : ∀ (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (u₁ u₂ : DY.Bytes), x₁ ∈ (gamma' compI0 S g u₁).memo → x₂ ∈ (gamma' compI0 S g u₂).memo → Q₁ S g known pts x₁ x₂ → Q₂ S g known pts x₁ x₂ → Q S g known pts x₁ x₂) (h₁ : Split38PairsAt Q₁ w τ wire v t) (h₂ : Split38PairsAt Q₂ w τ wire v t) : Split38PairsAt Q w τ wire v t :=
  split38PairsAt_mono (fun S g known pts x₁ x₂ u₁ u₂ hxu₁ hxu₂ h =>
    hQ S g known pts x₁ x₂ u₁ u₂ hxu₁ hxu₂ h.1 h.2) (split38PairsAt_and h₁ h₂)
def QVT : PairQ := fun _ _ known pts x₁ x₂ => ¬ CompRNbsc38VT.MemoPairCollides known pts x₁ x₂
def QTagged : PairQ := fun _ _ known pts x₁ x₂ =>
  PairSide known pts x₁ x₂ → x₁.2.2.take 4 = compTag4 → x₁.2.2 = x₂.2.2 → x₁.2.1 = x₂.2.1
def QUntagged : PairQ := fun S g known pts x₁ x₂ =>
  PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → CompRI0TermInj.ShapeAgree S g x₁.1 x₂.1
def QKdf : PairQ := fun S g known pts x₁ x₂ =>
  ∀ k m : DY.Bytes, x₁.1 = DY.KdfExtract.kdfExtract k m → PairSide known pts x₁ x₂ → (gamma compI0 S g x₁.1).take 4 ≠ compTag4 → CompRI0TermInj.ShapeAgree S g x₁.1 x₂.1
theorem split38VT_of_pairsVT {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : Split38PairsAt QVT w τ wire v t) : CompRNbsc38VT.Split38NoClassifiedCollisionAtVT w τ wire v t := by intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h' := h r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at h' ⊢; intro hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂; exact h' hcompat hrun hvis hpre hmid hpost hm₀ hbd x₁ hx₁ x₂ hx₂ hc₁ hc₂
theorem qvt_of_weak (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (pts : List DY.Bytes) (x₁ x₂ : DY.Bytes × DY.Bytes × HwBytes) (u₁ u₂ : DY.Bytes) (hxu₁ : x₁ ∈ (gamma' compI0 S g u₁).memo) (hxu₂ : x₂ ∈ (gamma' compI0 S g u₂).memo) (hT : QTagged S g known pts x₁ x₂) (hU : QUntagged S g known pts x₁ x₂) : QVT S g known pts x₁ x₂ := by
  intro hcol; have hs := pairSide_of_collides hcol
  by_cases ht : x₁.2.2.take 4 = compTag4
  · exact hcol.1 (hT hs ht hcol.2.2.2.2)
  · obtain ⟨hs₁, hv₁⟩ := CompRPreMemoSound.memo_sound compI0 S g u₁ hxu₁; obtain ⟨hs₂, hv₂⟩ := CompRPreMemoSound.memo_sound compI0 S g u₂ hxu₂; have hsa := hU hs (by rw [← hv₁]; exact ht); apply hcol.1; rw [hs₁, hs₂]; exact hsa (by rw [← hv₁, ← hv₂]; exact hcol.2.2.2.2)
theorem split38VT_of_weak {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hT : Split38PairsAt QTagged w τ wire v t) (hU : Split38PairsAt QUntagged w τ wire v t) : CompRNbsc38VT.Split38NoClassifiedCollisionAtVT w τ wire v t :=
  split38VT_of_pairsVT (split38PairsAt_of₂ qvt_of_weak hT hU)
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38PairCore
