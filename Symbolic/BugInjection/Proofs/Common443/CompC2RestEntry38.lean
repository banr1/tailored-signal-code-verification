/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2RestFn
import Symbolic.DYBridge.DY.Bytes.Basic

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2RestEntry38
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRNoBSC CompRPlantWire CompRX0NBSC38Hmc CompRTag CompRI0TermInj CompRSplit38PairCore CompRSplit38UntaggedShape CompRNonInj38Census CompRQRestCensusZ CompC2RestCore CompC2Rest38 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem ai_dh_pack (p s : DY.Bytes) : assumedInjective (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) = true := by unfold assumedInjective; rw [DY.BytesView.view_pack]; simp
theorem ai_trunc8 (a : DY.Bytes) : assumedInjective (DY.Trunc.trunc8 a) = true := by unfold assumedInjective; rw [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]; simp
section ViewNone
theorem not_isDh_kdf (a b : DY.Bytes) : ¬ IsDh (DY.KdfExtract.kdfExtract a b) := by
  rintro ⟨p, s, h⟩
  have hv : (DY.KdfExtract.kdfExtract a b).view? DY.DiffieHellman.Dh.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [h, DY.BytesView.view_pack] at hv; cases hv
theorem not_isDh_tr8 (a : DY.Bytes) : ¬ IsDh (DY.Trunc.trunc8 a) := by
  rintro ⟨p, s, h⟩
  have hv : (DY.Trunc.trunc8 a).view? DY.DiffieHellman.Dh.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [h, DY.BytesView.view_pack] at hv; cases hv
theorem not_isTrunc8_kdf (k m : DY.Bytes) : ¬ IsTrunc8 (DY.KdfExtract.kdfExtract k m) := by
  rintro ⟨a, h⟩
  have hv : (DY.KdfExtract.kdfExtract k m).view? DY.Trunc.Trunc8.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
  rw [h, show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack] at hv; cases hv
end ViewNone
section Entry
variable {S : Sem} {g : Ghost}
theorem restEntry_of_nonInj {x : DY.Bytes × DY.Bytes × HwBytes} (h : assumedInjective x.1 = false) : RestEntry S g x :=
  ⟨dhPtNotLow_of_not_dh (fun ⟨_, _, hps⟩ => by rw [hps, ai_dh_pack] at h; cases h),
   (fun ⟨_, ha⟩ => by rw [ha, ai_trunc8] at h; cases h),
   (fun hai => by rw [h] at hai; cases hai)⟩
theorem restEntry_of_kdf {x : DY.Bytes × DY.Bytes × HwBytes} {k m : DY.Bytes} (hx : x.1 = DY.KdfExtract.kdfExtract k m) : RestEntry S g x := ⟨hx ▸ dhPtNotLow_of_not_dh (not_isDh_kdf k m),
   fun hT => absurd (hx ▸ hT) (not_isTrunc8_kdf k m),
   fun _ hK => absurd ⟨k, m, hx⟩ hK⟩
theorem restEntry_of_trunc8_kdf {x : DY.Bytes × DY.Bytes × HwBytes} {k m : DY.Bytes} (hx : x.1 = DY.Trunc.trunc8 (DY.KdfExtract.kdfExtract k m)) (hv : x.2.2 = gamma compI0 S g x.1) : RestEntry S g x := ⟨hx ▸ dhPtNotLow_of_not_dh (not_isDh_tr8 _),
   fun _ => by rw [hv, hx]; exact zVal_trunc8_kdfExtract k m,
   fun _ _ _ hT => absurd ⟨_, hx⟩ hT⟩
theorem restEntry_of_zeroSalted {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hu : x.1 ∈ zeroSaltedTermsStA tr₂ stA cl pq) (hv : x.2.2 = gamma compI0 S g x.1) : RestEntry S g x := by
  unfold zeroSaltedTermsStA at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with h | h | h | h | h | h <;> first | exact restEntry_of_kdf h | exact restEntry_of_trunc8_kdf h hv
end Entry
def RestPre38At (w : PQXDHSpqrSetup) (τ : List MachineEvent) (wire : HwBytes) (_v : Fin 4) (_t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields), compFitsPinned w compI0 r → parsePreKeyWire wire = some p → p.preKeyId = none → ∀ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let ms := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post;
      Compat compI0 r S g → ModelRun r ms → List.Forall₂ (EventMatchesEntry compI0 r S g) τ (runVis r ms) →
      MovesFrom InvisibleNoEffect (setupTrace r) pre → MovesFrom InvisibleNoEffect (m₀.next tr₁) mid →
      MovesFrom InvisibleNoEffect ((Move.encrypt r.alice (tr₁.length + 8) cl pq (some (e, c'))).next tr₂) post →
      m₀.next tr₁ = iniAliceStartTr tr₁ r.alice r.bob o → bobDoneBaseKeys (runTraceMoves r ms) = [] →
      ∀ u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'), CompRMemoKnown.MemoOK compI0 S g (RestEntry S g) u
theorem rest38EntryAt_of_pre {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (h : RestPre38At w τ wire v t) : Rest38EntryAt w τ wire v t := by
  intro r S g p hfits hp hopk pre mid post hb shown cl e c'; have h' := h r S g p hfits hp hopk pre mid post hb shown cl e c'; dsimp only at h' ⊢; intro hC hmr hF hpre hmid hpost hm₀ hbob x hx hcl
  rcases hcl with hpm | hni | hz
  · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hpm; exact h' hC hmr hF hpre hmid hpost hm₀ hbob u hu x hxu
  · exact restEntry_of_nonInj hni
  · have hv : x.2.2 = gamma compI0 S g x.1 := by rcases List.mem_append.mp hx with hx' | hx' <;> (obtain ⟨u, _, hxu⟩ := List.mem_flatMap.mp hx'; exact (CompRPreMemoSound.memo_sound compI0 S g u hxu).2)
    exact restEntry_of_zeroSalted hz hv
end Symbolic.BugInjection.Proofs.Common443.CompC2RestEntry38
