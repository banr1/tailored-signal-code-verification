/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import Computational.Proofs.SignalPqxdh.Security.FgGapDhD
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpk -- shake: keep

/-!
# Case D (`DH4`) pre-sampled `KeyInd` implementation

Pre-sampled variant `pqxdhKeyIndFgPreImplOpk sIdx oIdx optU optV` of `pqxdhKeyIndFgImpl`, which
uses `uSk` as the ephemeral secret of initiator slot `sIdx` and `vSk` as the one-time prekey
secret of OPK slot `oIdx`, together with the pre-sampling equivalence
`evalDist_runKeyIndFgSim_eq_preSample_dh4`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh.Opk

open Proofs.SignalPqxdh.Security.FgGapDh

def OpkKeysMono {S : Setup} (st st' : KeyIndState S) : Prop :=
  ∀ key : ℕ × ℕ × ℕ, st.opkEntries.any (fun (k, _) => k == key) = true →
    st'.opkEntries.any (fun (k, _) => k == key) = true

theorem pqxdhKeyIndFgPreImpl_opkMono {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run hst)) :
    OpkKeysMono hst.base x.2.base := by
  have unchanged : x.2.base.opkEntries = hst.base.opkEntries → OpkKeysMono hst.base x.2.base := by
    intro hO key h; unfold OpkKeysMono at *; rw [hO]; exact h
  refine mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 targetIdx targetSpkIdx optUsk optVsk P q hst x hx
    (fun _ _ hO _ => unchanged hO)
    (fun _ _ _ _ hB => unchanged (by rw [hB]))
    (fun _ _ _ _ _ hB => unchanged (by rw [hB]))
    (fun _ _ _ _ _ _ _ hB => unchanged (by rw [hB]))
    (fun _ _ _ _ _ _ _ hB key h => by rw [hB]; simp [List.any_cons, h])
    (fun _ _ _ hB => unchanged (by rw [hB]))
    (fun _ _ _ _ _ _ hO key h => ?_)
    (fun _ _ _ _ _ _ _ hO _ => unchanged hO)
    (fun _ _ hB => unchanged (by rw [hB]))
  rw [hO]
  rw [List.any_map, List.any_eq_true] at *
  rcases h with ⟨y0, hy0, hk⟩; refine ⟨y0, hy0, ?_⟩
  rcases y0 with ⟨idx, e⟩
  dsimp only [Function.comp_apply] at hk ⊢
  split_ifs <;> exact hk

noncomputable def fgPreGenOPK (targetOpkIdx : ℕ) (optVsk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) :
    StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
    return .noneResp
  let opkSk ← liftM (match optVsk with
    | some vSk => if opkFlatIdx S u j o == targetOpkIdx then pure vSk else sampleScalar32
    | none => sampleScalar32)
  let opkPk := P.x25519Base opkSk
  let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
  set { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries }
  return .pkResp opkPk

/-- Case D pre-sampled implementation: `uSk` as the ephemeral secret of initiator slot
    `targetIdx`, `vSk` as the OPK secret of OPK slot `targetOpkIdx`. -/
noncomputable def pqxdhKeyIndFgPreImplOpk (targetIdx targetOpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .genOPK u j o => liftFgBase (fgPreGenOPK targetOpkIdx optVsk S P u j o)
  | q => pqxdhKeyIndFgPreImpl false targetIdx (noSpkIdx S) optUsk none S P q

theorem pqxdhKeyIndFgPreImplOpk_none_eq {S : Setup} (targetIdx targetOpkIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) :
    pqxdhKeyIndFgPreImplOpk targetIdx targetOpkIdx optUsk none S P =
      pqxdhKeyIndFgPreImpl false targetIdx (noSpkIdx S) optUsk none S P := by
  funext q
  cases q <;> rfl

def hasFiredOpk (S : Setup) (oIdx : ℕ) (hst : KeyIndFgCutoffState S) : Prop :=
  ∃ (u₀ : Fin S.N_id) (j₀ : Fin S.N_recv) (o₀ : Fin S.N_opk),
    opkFlatIdx S u₀ j₀ o₀ = oIdx ∧
    hst.base.opkEntries.any (fun (k, _) => k == (u₀.val, j₀.val, o₀.val)) = true

theorem opkEntries_any_of_hasFiredOpk (S : Setup) (oIdx : ℕ) (hst : KeyIndFgCutoffState S)
    (hFired : hasFiredOpk S oIdx hst) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hb : (opkFlatIdx S u j o == oIdx) = true) :
    hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) = true := by
  rcases hFired with ⟨u₀, j₀, o₀, hidx₀, hany₀⟩
  have heq : opkSlotFlatIdx S (u.val, j.val, o.val) = opkSlotFlatIdx S (u₀.val, j₀.val, o₀.val) :=
    (beq_iff_eq.mp hb).trans hidx₀.symm
  have hk := opkSlotFlatIdx_inj S j.isLt o.isLt j₀.isLt o₀.isLt heq
  rw [hk]; exact hany₀

theorem hasFiredOpk_of_mono {S : Setup} (oIdx : ℕ) (hst hst' : KeyIndFgCutoffState S)
    (hM : OpkKeysMono hst.base hst'.base) (h : hasFiredOpk S oIdx hst) :
    hasFiredOpk S oIdx hst' := by
  rcases h with ⟨u₀, j₀, o₀, h1, h2⟩
  exact ⟨u₀, j₀, o₀, h1, hM _ h2⟩

theorem pqxdhKeyIndFgPreImplOpk_preserves {S : Setup} (targetIdx targetOpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgPreImplOpk targetIdx targetOpkIdx optUsk optVsk S P q).run hst)) :
    OpkKeysMono hst.base x.2.base ∧
    (∀ sIdx, hasFiredSess S sIdx hst → hasFiredSess S sIdx x.2) := by
  cases q
  case genOPK u j o =>
    unfold pqxdhKeyIndFgPreImplOpk fgPreGenOPK at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨opkSk, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      refine ⟨fun key h => by rw [hB]; simp [List.any_cons, h],
        fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact ⟨fun key h => by rw [hB]; exact h,
        fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
  all_goals exact
    ⟨pqxdhKeyIndFgPreImpl_opkMono false targetIdx (noSpkIdx S) optUsk none P _ hst x hx,
     (pqxdhKeyIndFgPreImpl_preserves_hasFired false targetIdx (noSpkIdx S)
       optUsk none P _ hst x hx).2.2⟩

theorem evalDist_preSample_V_opk {S : Setup} {α : Type}
    (targetIdx targetOpkIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImplOpk targetIdx targetOpkIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImplOpk targetIdx targetOpkIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredOpk S targetOpkIdx)
    (pqxdhKeyIndFgPreImplOpk targetIdx targetOpkIdx optUsk none S P)
    (fun vSk => pqxdhKeyIndFgPreImplOpk targetIdx targetOpkIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx => hasFiredOpk_of_mono targetOpkIdx s x.2
      (pqxdhKeyIndFgPreImplOpk_preserves targetIdx targetOpkIdx optUsk none P q s x hx).1 hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q
    case genOPK u j o =>
      unfold pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hSlot : (opkFlatIdx S u j o == targetOpkIdx) = true
      · have hany := opkEntries_any_of_hasFiredOpk S targetOpkIdx s hFired u j o hSlot
        simp [hany]
      · cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
        · simp [hSlot]
        · rfl
    all_goals rfl
  · cases q
    case genOPK u j o =>
      by_cases hSlot : (opkFlatIdx S u j o == targetOpkIdx) = true
      · unfold pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun vSk x hx => ?_⟩
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind,
              support_pure, Set.mem_singleton_iff] at hx
            have hB := (Prod.mk.inj hx).2
            exact ⟨u, j, o, beq_iff_eq.mp hSlot, by rw [hB]; simp⟩
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        unfold pqxdhKeyIndFgPreImplOpk fgPreGenOPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
        · simp [hSlot]
        · rfl
    all_goals exact Or.inl (fun _ => rfl)

theorem evalDist_runKeyIndFgSim_eq_preSample_dh4 {S : Setup}
    (sIdx oIdx : ℕ) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImplOpk sIdx oIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runKeyIndFgSim S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgPreImpl false sIdx (noSpkIdx S) (some uSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] := by
    intro uSk
    rw [← pqxdhKeyIndFgPreImplOpk_none_eq sIdx oIdx (some uSk) P]
    exact evalDist_preSample_V_opk sIdx oIdx (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh3_pqxdhKeyIndFgPreImpl sIdx (noSpkIdx S) none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgPreImpl_none_none_eq]
  simp only [pure_bind]

end Proofs.SignalPqxdh.Security.FgGapDh.Opk
