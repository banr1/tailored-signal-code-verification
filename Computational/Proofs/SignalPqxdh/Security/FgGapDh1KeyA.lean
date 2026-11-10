/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyCD
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# One-Key `GapDhWithSign` Coupling for Case A

**Checked by Lean.** Proves the per-slot `GapDhWithSign` bound for Case A (`DH1 = CDH(ik_U*, spk_V*)`)
by embedding the challenge identity key with signing access into principal slot `uIdx` and coupling
with a ghost two-key `FgSimInvDh1` state.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security.FgGapDh1Key

/-! ## Support Preservation and `clearTargetSecIKAsign` Commutation -/

def PreStepPreserves1KeyAux {S : Setup} (hst hst' : KeyIndFgCutoffState S) : Prop :=
  ((∀ kv ∈ hst.base.principals, kv.2.secIKAsign = kv.2.secIKA0) →
    ∀ kv ∈ hst'.base.principals, kv.2.secIKAsign = kv.2.secIKA0) ∧
  (∀ k, (bundleSignedMessages k hst.base.spkBundles).length ≤
    (bundleSignedMessages k hst'.base.spkBundles).length)

theorem preStepPreserves1KeyAux_of_eq {S : Setup} {hst hst' : KeyIndFgCutoffState S}
    (hPrin : hst'.base.principals = hst.base.principals)
    (hSpk : hst'.base.spkBundles = hst.base.spkBundles) :
    PreStepPreserves1KeyAux hst hst' :=
  ⟨fun h kv hkv => h kv (hPrin ▸ hkv), fun _ => hSpk ▸ Nat.le_refl _⟩

theorem pqxdhKeyIndFgPreImpl_preserves_1KeyAux_of_ne_initPrin {S : Setup}
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (optU optV : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u) (hst : KeyIndFgCutoffState S) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optU optV S P q).run hst),
      PreStepPreserves1KeyAux hst x.2 := by
  intro x hx
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | corruptIK u =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    | some pu =>
      rcases pu with ⟨_, _⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      refine ⟨fun hSec kv hkv => ?_, fun _ => by rw [hB]⟩
      rw [hB] at hkv
      rcases List.mem_map.mp hkv with ⟨⟨idx, e⟩, heMem, hMapEq⟩
      have h0 := hSec (idx, e) heMem
      by_cases hIdx : (idx == u.val) = true <;>
        simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hMapEq <;>
        (subst hMapEq; exact h0)
  | genSPK u j =>
    unfold pqxdhKeyIndFgPreImpl fgPreGenSPK at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
      | some p =>
        rcases p with ⟨_, _⟩
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff]
        rintro ⟨_, _, _, _, _, _, _, _, hEq⟩
        have hB := (Prod.mk.inj hEq).2
        refine ⟨fun hSec kv hkv => hSec kv (by rw [hB] at hkv; exact hkv), fun k => ?_⟩
        rw [hB]
        by_cases hku : u.val = k
        · subst hku
          rw [bundleSignedMessages_cons_eq, List.length_cons, List.length_cons]
          omega
        · rw [bundleSignedMessages_cons_of_ne k u.val j.val _ _ (beq_eq_false_iff_ne.mpr hku)]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | genOPK u j o =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl fgPreInitiate at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases hst.base.sessions.any (fun e => e.sid == .sendOPK u i)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
        | some p =>
          rcases p with ⟨_, _⟩; dsimp only
          cases koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
            hst.base.advKeys bundle
          · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
              Set.mem_singleton_iff]
            intro hEq; have hB := (Prod.mk.inj hEq).2
            exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
              MonadAttach.mem_support_bind]
            rintro ⟨_, _, kemCoins, _, hb⟩; revert hb
            split_ifs
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq; have hB := (Prod.mk.inj hEq).2
              exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
            · cases P.kemEncaps bundle.pqspkB kemCoins with
              | none =>
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                intro hEq; have hB := (Prod.mk.inj hEq).2
                exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
              | some sc =>
                rcases sc with ⟨_, _⟩; dsimp only
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  bind_assoc, pure_bind, MonadAttach.mem_support_bind]
                rintro ⟨⟨_, _⟩, _, _, _, hb⟩; revert hb
                cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
                · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                  intro hEq; have hB := (Prod.mk.inj hEq).2
                  exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
      · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl fgPreInitiate at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
        | some p =>
          rcases p with ⟨_, _⟩; dsimp only
          cases koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
            hst.base.advKeys bundle
          · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
              Set.mem_singleton_iff]
            intro hEq; have hB := (Prod.mk.inj hEq).2
            exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
              MonadAttach.mem_support_bind]
            rintro ⟨_, _, kemCoins, _, hb⟩; revert hb
            split_ifs
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq; have hB := (Prod.mk.inj hEq).2
              exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
            · cases P.kemEncaps bundle.pqspkB kemCoins with
              | none =>
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                intro hEq; have hB := (Prod.mk.inj hEq).2
                exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
              | some sc =>
                rcases sc with ⟨_, _⟩; dsimp only
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  bind_assoc, pure_bind, MonadAttach.mem_support_bind]
                rintro ⟨⟨_, _⟩, _, _, _, hb⟩; revert hb
                cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
                · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                  intro hEq; have hB := (Prod.mk.inj hEq).2
                  exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
      · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | acceptOPK k j o hdr =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs with h1 h2 h2b
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
      | some kp =>
        rcases kp with ⟨_, _⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
            intro hEq; have hB := (Prod.mk.inj hEq).2
            exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
          | some op =>
            rcases op with ⟨_, _⟩; dsimp only
            split_ifs with h3
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq; have hB := (Prod.mk.inj hEq).2
              exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
            · cases Model.acceptKeys P _ with
              | none =>
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                intro hEq; have hB := (Prod.mk.inj hEq).2
                exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
              | some _ =>
                dsimp only
                cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                | none =>
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                  intro hEq; have hB := (Prod.mk.inj hEq).2
                  exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
                | some _ =>
                  dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    bind_assoc, pure_bind, MonadAttach.mem_support_bind]
                  rintro ⟨⟨_, _⟩, _, y, hy, hb⟩
                  rcases mem_support_recordKeyIndResp P _ _ y hy with ⟨hP, hS, _⟩
                  revert hb
                  cases findHonestPrincipal P hst.base.principals hdr.ikAPk <;>
                  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                    intro hEq; have hB := (Prod.mk.inj hEq).2
                    exact preStepPreserves1KeyAux_of_eq (by rw [hB, hP]) (by rw [hB, hS])
  | acceptNoOPK k j l hdr =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs with h1 h2 h2b
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
      | some kp =>
        rcases kp with ⟨_, _⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          cases Model.acceptKeys P _ with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
            intro hEq; have hB := (Prod.mk.inj hEq).2
            exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
          | some _ =>
            dsimp only
            cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
            | none =>
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq; have hB := (Prod.mk.inj hEq).2
              exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
            | some _ =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind, MonadAttach.mem_support_bind]
              rintro ⟨⟨_, _⟩, _, y, hy, hb⟩
              rcases mem_support_recordKeyIndResp P _ _ y hy with ⟨hP, hS, _⟩
              revert hb
              cases findHonestPrincipal P hst.base.principals hdr.ikAPk <;>
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                intro hEq; have hB := (Prod.mk.inj hEq).2
                exact preStepPreserves1KeyAux_of_eq (by rw [hB, hP]) (by rw [hB, hS])
  | testSession sid =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases isKeyIndSessionTestable hst.base sid
    · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hst.base.sessions.find? (fun e => e.sid == sid) with
      | some _ =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
      | none =>
        cases hst.base.respSessions.find? (fun r => r.sid == sid) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
        | some _ =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | revealSessionKey sid =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      by_cases he : e.tested = true
      · simp only [he, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
      · simp only [he, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    | none =>
      cases hst.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
      | some r =>
        by_cases hr : r.tested = true
        · simp only [hr, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
        · simp only [hr, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | roQuery secrets =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self, StateT.run_set,
      StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨_, _⟩, _, hEq⟩
    have hB := (Prod.mk.inj hEq).2
    exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | revealDhSecrets =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
    have hB := (Prod.mk.inj hb).2
    exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | registerKey sk =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl registerAdvKey at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
  | revealSpkSk u j =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact preStepPreserves1KeyAux_of_eq (by rw [hB]) (by rw [hB])
    | some _ =>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact ⟨fun h kv hkv => h kv (by rw [hB] at hkv; exact hkv), fun k => by
        rw [hB, bundleSignedMessages_map_revealed]⟩

theorem any_idx_map_clearTargetPrinSecSign (tIdx uVal : ℕ)
    (L : List (Nat × PrincipalEntry)) :
    (L.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))).any
      (fun (idx, _) => idx == uVal) =
      L.any (fun (idx, _) => idx == uVal) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, e⟩
    simp only [List.map_cons, List.any_cons, ih]

theorem fgKeyIndStepPure_corruptIK_clearTargetSecIKAsign_of_ne (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (u : Fin S.N_id)
    (hNe : (u.val == tIdx) = false) (st : FgKeyIndSimState S) :
    fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V (.corruptIK u)
      (clearTargetSecIKAsign tIdx st) =
      (fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V (.corruptIK u) st >>=
        fun p => pure (p.1, clearTargetSecIKAsign tIdx p.2)) := by
  dsimp only [fgKeyIndStepPure]
  simp only [clearTargetSecIKAsign_base_principals, find?_idx_map_clearTargetPrinSecSign]
  cases hF : st.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    dsimp only [Option.map]; simp only [pure_bind]
  | some p =>
    rcases p with ⟨u0, entry⟩
    dsimp only [Option.map]; simp only [pure_bind]
    have hu0 : u0 = u.val :=
      beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
    have hu0Ne : (u0 == tIdx) = false := by rw [hu0]; exact hNe
    have hEntry : clearTargetPrinSecSign tIdx u0 entry = entry := by
      unfold clearTargetPrinSecSign; simp [hu0Ne]
    rw [hEntry]
    have hMap :
        (st.base.principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e))).map
          (fun (idx, e) => if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) =
        (st.base.principals.map
          (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))).map
          (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) := by
      rw [List.map_map, List.map_map]
      congr 1; funext ⟨idx, e⟩
      dsimp only [Function.comp_def]
      unfold clearTargetPrinSecSign
      by_cases h1 : (idx == u.val) = true <;> by_cases h2 : (idx == tIdx) = true <;> simp [h1, h2]
    simp only [clearTargetSecIKAsign, clearTargetSecIKAsignBase, hMap]

theorem fgKeyIndStepPure_genSPK_clearTargetSecIKAsign_of_ne (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hNe : (u.val == tIdx) = false) (st : FgKeyIndSimState S) :
    fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V (.genSPK u j)
      (clearTargetSecIKAsign tIdx st) =
      (fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V (.genSPK u j) st >>=
        fun p => pure (p.1, clearTargetSecIKAsign tIdx p.2)) := by
  dsimp only [fgKeyIndStepPure]
  simp only [clearTargetSecIKAsign_base_spkBundles, clearTargetSecIKAsign_base_principals,
    find?_idx_map_clearTargetPrinSecSign]
  by_cases hAny : (st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
  · simp only [hAny, ↓reduceIte, pure_bind]
  · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
    cases hF : st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      dsimp only [Option.map]; simp only [pure_bind]
    | some p =>
      rcases p with ⟨u0, uEntry⟩
      dsimp only [Option.map]
      have hu0 : u0 = u.val :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
      have hu0Ne : (u0 == tIdx) = false := by rw [hu0]; exact hNe
      have hEntry : clearTargetPrinSecSign tIdx u0 uEntry = uEntry := by
        unfold clearTargetPrinSecSign; simp [hu0Ne]
      rw [hEntry]
      simp only [bind_assoc, pure_bind]
      rfl

def isDelegatedQuery1Key {S : Setup} (tIdx : ℕ) : KeyIndQuery S → Bool
  | .initPrin _  => false
  | .corruptIK u => !(u.val == tIdx)
  | .genSPK u _  => !(u.val == tIdx)
  | _            => true

theorem fgKeyIndStepPure_clearTargetSecIKAsign_delegated (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S)
    (hq : isDelegatedQuery1Key tIdx q = true) (st : FgKeyIndSimState S) :
    fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q
      (clearTargetSecIKAsign tIdx st) =
      (fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st >>=
        fun p => pure (p.1, clearTargetSecIKAsign tIdx p.2)) := by
  cases q with
  | initPrin _ => cases hq
  | corruptIK u =>
    have hNe : (u.val == tIdx) = false := by simpa [isDelegatedQuery1Key] using hq
    exact fgKeyIndStepPure_corruptIK_clearTargetSecIKAsign_of_ne P ddh useDh1 targetIdx
      targetSpkIdx tIdx S maxLen U V u hNe st
  | genSPK u j =>
    have hNe : (u.val == tIdx) = false := by simpa [isDelegatedQuery1Key] using hq
    exact fgKeyIndStepPure_genSPK_clearTargetSecIKAsign_of_ne P ddh useDh1 targetIdx
      targetSpkIdx tIdx S maxLen U V u j hNe st
  | _ =>
    exact fgKeyIndStepPure_clearTargetSecIKAsign P ddh useDh1 targetIdx targetSpkIdx tIdx S maxLen
      U V _ rfl st

/-! ## Case A Coupling and `GapDhWithSign` Bound -/

theorem pqxdhKeyIndFgPreImpl1Key_preserves_deadDh1Full {S : Setup} (P : Primitives)
    (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh1Full uIdx bIdx hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadDh1Full uIdx bIdx x.2 = true := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · intro x hx
    unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      unfold deadDh1Full at hDead ⊢
      rcases Bool.or_eq_true_iff.mp hDead with hD | hR
      · refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
        unfold deadDh1 at hD ⊢
        cases hFP : hst.base.principals.find? (fun (u0, _) => u0 == uIdx) with
        | none => rw [hFP] at hD; cases hD
        | some p0 =>
          rcases p0 with ⟨u0, e0⟩
          rw [hFP] at hD
          have hu0Mem : (u0, e0) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
          have hu0Eq : u0 = uIdx :=
            beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == uIdx) hFP)
          have hNeU : (u.val == uIdx) = false := by
            cases hEqB : (u.val == uIdx)
            · rfl
            · have hT2 : (u0 == u.val) = true := by
                rw [beq_iff_eq] at hEqB ⊢; rw [hu0Eq, hEqB]
              have hAnyT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
                List.any_eq_true.mpr ⟨(u0, e0), hu0Mem, hT2⟩
              rw [hAny] at hAnyT; cases hAnyT
          rw [hB]
          dsimp only [List.find?]
          rw [hNeU, hFP]
          exact hD
      · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
        rw [spkTargetRevealed_eq_of_spkBundles_eq bIdx (hst1 := hst) (hst2 := x.2) (by rw [hB])]
        exact hR
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      unfold deadDh1Full at hDead ⊢
      rw [deadDh1_eq_of_principals uIdx (hst1 := hst) (hst2 := x.2) (by rw [hB]),
        spkTargetRevealed_eq_of_spkBundles_eq bIdx (hst1 := hst) (hst2 := x.2) (by rw [hB])]
      exact hDead
  · rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin true uIdx bIdx (some uSk) (some vSk) P q hNe]
    exact pqxdhKeyIndFgPreImpl_preserves_deadDh1Full P uIdx bIdx uSk vSk q hst hDead

/-- One-key Case A simulation invariant coupling `st.sim` with a ghost two-key `FgSimInvDh1` state
    via `clearTargetSecIKAsign`. -/
def FgSimInvDh1_1Key (S : Setup) (b : QueryBudget) (P : Primitives) (R : FgSlotReps P)
    (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S) : Prop :=
  ∃ stGhost : FgKeyIndSimState S,
    st.sim = clearTargetSecIKAsign uIdx stGhost ∧
    FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst stGhost ∧
    2 * min S.N_spk_tot S.N_recv ≤
      (bundleSignedMessages uIdx hst.base.spkBundles).length + 2 * st.sigBudget ∧
    (∀ kv ∈ hst.base.principals, kv.2.secIKAsign = kv.2.secIKA0)

theorem fgSimInvDh1_1Key_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ) (uSk vSk : Bytes) (secb : Bool) :
    FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk b.q_total
      (KeyIndFgCutoffState.empty S secb) (FgKeyInd1KeySimState.empty S secb) :=
  ⟨_root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb, rfl,
    fgSimInvDh1_empty S b P R uIdx bIdx uSk vSk secb,
    by simp [KeyIndFgCutoffState.empty, FgKeyInd1KeySimState.empty, bundleSignedMessages],
    fun _ h => False.elim (List.not_mem_nil h)⟩

theorem fgSimInvDh1_1Key_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (R : FgSlotReps P) (maxLen uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (a : Bool) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDead : deadDh1Full uIdx bIdx hst = false)
    (hInv : FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk rem hst st) :
    𝒟[(pure (badKeyIndFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog) : ProbComp Bool)] {true} ≤
      𝒟[(pure (P.pow8 (pureExtractCdhFromSimState S P P.isValidDhTriple true b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) st.sim) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hGhostInv, _, _⟩
  have hExtEq : pureExtractCdhFromSimState S P P.isValidDhTriple true b.q_total
      (P.x25519Base uSk) (P.x25519Base vSk) st.sim =
      pureExtractCdhFromSimState S P P.isValidDhTriple true b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) stGhost := by
    rw [hSimEq]; rfl
  rw [hExtEq]
  exact fgSimInvDh1_terminal_le S b P hP R maxLen uIdx bIdx uSk vSk a rem hst stGhost hDead
    hGhostInv

theorem fgStepCoupling_dh1_initPrin_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDeadFull : deadDh1Full uIdx bIdx hst = false)
    (hInv : FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hContFull : ∀ r hst' st', deadDh1Full uIdx bIdx hst' = false →
      FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.initPrin u)).run hst
      >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u)).run st >>= k2] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hGhostInv, hBudget, hSecEq⟩
  have hGhostInv0 := hGhostInv
  rcases hGhostInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hDead : deadDh1 uIdx hst = false := (Bool.or_eq_false_iff.mp hDeadFull).1
  have hRevF : spkTargetRevealed bIdx hst = false := (Bool.or_eq_false_iff.mp hDeadFull).2
  have hPrinAnyEq : st.sim.base.principals.any (fun (idx, _) => idx == u.val) =
      hst.base.principals.any (fun (idx, _) => idx == u.val) := by
    rw [hSimEq, clearTargetSecIKAsign_base_principals, any_idx_map_clearTargetPrinSecSign,
      hBaseEq]
    dsimp only [eraseStateFg]
    exact any_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key liftFgBase fgKeyInd1KeySimImpl
    fgKeyInd1KeyStepPure fgInitPrin1KeyPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.true_and,
    hPrinAnyEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hTgt : (u.val == uIdx) = true
    · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        evalDist_sampleScalar32_const]
      let entry1 : PrincipalEntry := {
        secIKA0 := uSk, ikAPk := P.x25519Base uSk,
        secIKAsign := uSk, ikSignPk := P.x25519Base uSk, corrupted := false }
      let entryGhost : PrincipalEntry := {
        secIKA0 := [], ikAPk := P.x25519Base uSk,
        secIKAsign := uSk, ikSignPk := P.x25519Base uSk, corrupted := false }
      let stGhost' : FgKeyIndSimState S :=
        { stGhost with base :=
          { stGhost.base with principals := (u.val, entryGhost) :: stGhost.base.principals } }
      apply hContFull (.initPrinResp (P.x25519Base uSk) (P.x25519Base uSk))
      · unfold deadDh1Full
        have hD1 : deadDh1 uIdx { hst with base :=
            { hst.base with principals := (u.val, entry1) :: hst.base.principals } } = false := by
          unfold deadDh1; dsimp only [List.find?]; rw [hTgt]
        have hR1 : spkTargetRevealed bIdx { hst with base :=
            { hst.base with principals := (u.val, entry1) :: hst.base.principals } } = false :=
          Eq.trans (spkTargetRevealed_eq_of_spkBundles_eq bIdx (hst2 := hst) rfl) hRevF
        rw [hD1, hR1]; rfl
      · refine ⟨stGhost', ?_, ?_, hBudget, ?_⟩
        · rw [hSimEq]
          dsimp only [stGhost', clearTargetSecIKAsign, clearTargetSecIKAsignBase,
            clearTargetPrinSecSign, entryGhost, List.map]
          rw [hTgt]
          rfl
        · refine ⟨?_, hAdvEq, hCache, by dsimp [stGhost']; omega, by dsimp; omega, ?_, hSpkV, ?_,
            hSpks, hOpks, hSess⟩
          · dsimp only [stGhost', entryGhost]
            rw [hBaseEq]
            dsimp only [eraseStateFg, erasePrincipalsFg, erasePrincipalEntryFg, List.map]
            rw [hTgt]
            rfl
          · exact ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
              hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨huSk, rfl, fun _ => rfl⟩
            · exact hPrins kv hMem
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · rfl
          · exact hSecEq kv hMem
    · have hTgtF : (u.val == uIdx) = false := Bool.eq_false_iff.mpr hTgt
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun sk hSk => ?_)
      have hLen0 : sk.length = 32 := length_of_mem_support_sampleScalar32 hSk
      let entry1 : PrincipalEntry := {
        secIKA0 := sk, ikAPk := P.x25519Base sk,
        secIKAsign := sk, ikSignPk := P.x25519Base sk, corrupted := false }
      let stGhost' : FgKeyIndSimState S :=
        { stGhost with base :=
          { stGhost.base with principals := (u.val, entry1) :: stGhost.base.principals } }
      apply hContFull (.initPrinResp (P.x25519Base sk) (P.x25519Base sk))
      · unfold deadDh1Full
        have hD1 : deadDh1 uIdx { hst with base :=
            { hst.base with principals := (u.val, entry1) :: hst.base.principals } } = false := by
          unfold deadDh1 at hDead ⊢; dsimp only [List.find?]; rw [hTgtF]; exact hDead
        have hR1 : spkTargetRevealed bIdx { hst with base :=
            { hst.base with principals := (u.val, entry1) :: hst.base.principals } } = false :=
          Eq.trans (spkTargetRevealed_eq_of_spkBundles_eq bIdx (hst2 := hst) rfl) hRevF
        rw [hD1, hR1]; rfl
      · refine ⟨stGhost', ?_, ?_, hBudget, ?_⟩
        · rw [hSimEq]
          dsimp only [stGhost', clearTargetSecIKAsign, clearTargetSecIKAsignBase,
            clearTargetPrinSecSign, entry1, List.map]
          rw [hTgtF]
          rfl
        · refine ⟨?_, hAdvEq, hCache, by dsimp [stGhost']; omega, by dsimp; omega, ?_, hSpkV, ?_,
            hSpks, hOpks, hSess⟩
          · dsimp only [stGhost', entry1]
            rw [hBaseEq]
            dsimp only [eraseStateFg, erasePrincipalsFg, erasePrincipalEntryFg, List.map]
            rw [hTgtF]
            rfl
          · exact ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
              hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hLen0, rfl, fun h => by rw [hTgtF] at h; cases h⟩
            · exact hPrins kv hMem
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · rfl
          · exact hSecEq kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact hContFull .noneResp hst st hDeadFull
      ⟨stGhost, hSimEq, ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hSpkV, hPrins,
        hSpks, hOpks, hSess⟩, hBudget, hSecEq⟩

theorem fgStepCoupling_dh1_corruptIK_tgt_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (u : Fin S.N_id) (hTgt : (u.val == uIdx) = true)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDeadFull : deadDh1Full uIdx bIdx hst = false)
    (hInv : FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hContFull : ∀ r hst' st', deadDh1Full uIdx bIdx hst' = false →
      FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadContFull : ∀ r hst', deadDh1Full uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run hst
      >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u)).run st >>= k2] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hGhostInv, hBudget, hSecEq⟩
  rcases hGhostInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hPrinFind : st.sim.base.principals.find? (fun (idx, _) => idx == u.val) =
      ((hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e))).map
        (fun (idx, e) => (idx, clearTargetPrinSecSign uIdx idx e)) := by
    rw [hSimEq, clearTargetSecIKAsign_base_principals, find?_idx_map_clearTargetPrinSecSign,
      hBaseEq]
    dsimp only [eraseStateFg]
    simp only [↓reduceIte]
    rw [find?_idx_erasePrincipalsFg]
  unfold pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase
    fgKeyInd1KeySimImpl fgKeyInd1KeyStepPure fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinFind, bind_assoc, pure_bind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    dsimp only [Option.map]
    simp only [StateT.run_pure, pure_bind]
    exact hContFull .noneResp hst st hDeadFull
      ⟨stGhost, hSimEq, ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hSpkV, hPrins,
        hSpks, hOpks, hSess⟩, hBudget, hSecEq⟩
  | some p =>
    rcases p with ⟨u0, entry⟩
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    have hD1 : deadDh1 uIdx { hst with base := { hst.base with
        principals := hst.base.principals.map (fun (idx, e) =>
          if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) } } = true :=
      deadDh1_map_corrupted_eq_true_of_eq uIdx u.val hTgt hst u0 entry hF
    rw [hDeadContFull _ _ (Bool.or_eq_true_iff.mpr (Or.inl hD1))]
    exact zero_le

theorem fgStepCoupling_dh1_genSPK_tgt_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hTgtPrin : (u.val == uIdx) = true)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDeadFull : deadDh1Full uIdx bIdx hst = false)
    (hInv : FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hContFull : ∀ r hst' st', deadDh1Full uIdx bIdx hst' = false →
      FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadContFull : ∀ r hst', deadDh1Full uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run hst
      >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j)).run st >>= k2] {true} := by
  rcases hInv with ⟨stGhost, hSimEq, hGhostInv, hBudget, hSecEq⟩
  rcases hGhostInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks,
    hOpks, hSess⟩
  have hDead : deadDh1 uIdx hst = false := (Bool.or_eq_false_iff.mp hDeadFull).1
  have hPrinFind : st.sim.base.principals.find? (fun (idx, _) => idx == u.val) =
      ((hst.base.principals.find? (fun (idx, _) => idx == u.val)).map
        (fun (idx, e) => (idx, erasePrincipalEntryFg uIdx idx e))).map
        (fun (idx, e) => (idx, clearTargetPrinSecSign uIdx idx e)) := by
    rw [hSimEq, clearTargetSecIKAsign_base_principals, find?_idx_map_clearTargetPrinSecSign,
      hBaseEq]
    dsimp only [eraseStateFg]
    simp only [↓reduceIte]
    rw [find?_idx_erasePrincipalsFg]
  have hSpkAnyEq : st.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) =
      hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) := by
    rw [hSimEq, clearTargetSecIKAsign_base_spkBundles, hBaseEq]
    exact any_idx_eraseSpkBundlesFg S bIdx (u.val, j.val) hst.base.spkBundles
  unfold pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
    fgKeyInd1KeySimImpl fgKeyInd1KeyStepPure fgGenSPK1KeyPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.true_and, hTgtPrin, ↓reduceIte,
    hSpkAnyEq, hPrinFind, bind_assoc, pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      dsimp only [Option.map]
      simp only [StateT.run_pure, pure_bind]
      exact hContFull .noneResp hst st hDeadFull
        ⟨stGhost, hSimEq, ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hSpkV, hPrins,
          hSpks, hOpks, hSess⟩, hBudget, hSecEq⟩
    | some p =>
      rcases p with ⟨u0, uEntry⟩
      dsimp only [Option.map]
      simp only [clearTargetPrinSecSign_ikAPk, erasePrincipalEntryFg_ikAPk]
      let dummyB : SpkBundleEntry :=
        { spkSk := [], spkPk := [], spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := [] }
      have huEq : u.val = uIdx := beq_iff_eq.mp hTgtPrin
      have hLenPlus2 :
          (bundleSignedMessages uIdx hst.base.spkBundles).length + 2 ≤
            2 * min S.N_spk_tot S.N_recv := by
        rw [← huEq]
        exact bundleSignedMessages_length_add_two_le S u j dummyB hst.base.spkBundles
          hValidEc.2.1 hAny
      have hBudPos : 1 ≤ st.sigBudget := by omega
      have hBudZeroF : (st.sigBudget == 0) = false := by
        cases hEq0 : (st.sigBudget == 0)
        · rfl
        · have := beq_iff_eq.mp hEq0; omega
      have huMem : (u0, uEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
      have hu0Eq : u0 = u.val :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hFP)
      have hu0Tgt : (u0 == uIdx) = true := by rw [hu0Eq]; exact hTgtPrin
      have hSignEq : uEntry.secIKAsign = uSk := by
        rw [hSecEq (u0, uEntry) huMem, (hPrins (u0, uEntry) huMem).2.2 hu0Tgt]
      simp only [hBudZeroF, Bool.false_eq_true, ↓reduceIte, hSignEq]
      by_cases hTgt : (FgGapDh.spkBundleFlatIdx S u j == bIdx) = true
      · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, sampleKemKeyGen, bind_assoc, pure_bind,
          evalDist_sampleScalar32_const]
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun seedKem _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        let spkPk := P.x25519Base vSk
        let pqspkPk := (P.kemKeyGen seedKem).1
        let pqspkSk := (P.kemKeyGen seedKem).2
        let bEntry1 : SpkBundleEntry := {
          spkSk := vSk, spkPk := spkPk,
          spkSig := P.sigSign uSk (encodeEC spkPk) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uSk (encodeKEM pqspkPk) rPq }
        let bEntrySim : SpkBundleEntry := { bEntry1 with spkSk := [] }
        let bundleOut : PreKeyBundleInput := {
          ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
          spkSig := bEntry1.spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
          pqspkB := pqspkPk, pqspkSig := bEntry1.pqspkSig }
        let hst' : KeyIndFgCutoffState S :=
          { hst with base :=
            { hst.base with spkBundles := ((u.val, j.val), bEntry1) :: hst.base.spkBundles } }
        let stGhost' : FgKeyIndSimState S :=
          { stGhost with base :=
            { stGhost.base with
              spkBundles := ((u.val, j.val), bEntrySim) :: stGhost.base.spkBundles } }
        have hTgtVal : (FgGapDh.spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = true := hTgt
        have hSpkV' : spkTargetIsV bIdx (P.x25519Base vSk) hst' = true := by
          unfold spkTargetIsV at hSpkV ⊢
          simp [hst', List.all_cons, bEntry1, spkPk, hSpkV]
        have hD1' : deadDh1 uIdx hst' = false := by
          unfold deadDh1 at hDead ⊢; exact hDead
        have hInvGhost' : FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' stGhost' := by
          refine ⟨?_, hAdvEq, hCache, by dsimp [stGhost']; omega, by dsimp [hst']; omega,
            ⟨hValidEc.1,
              (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
              hValidEc.2.2.1, hValidEc.2.2.2⟩,
            hSpkV', hPrins, ?_, hOpks, hSess⟩
          · dsimp only [stGhost', hst', bEntrySim, bEntry1]
            rw [hBaseEq]
            dsimp only [eraseStateFg, eraseSpkBundlesFg, eraseSpkBundleEntryFg, List.map]
            rw [hTgtVal]
            rfl
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hvSk, rfl, fun _ => rfl⟩
            · exact hSpks kv hMem
        by_cases hRev' : spkTargetRevealed bIdx hst' = true
        · rw [hDeadContFull (.bundleResp bundleOut) hst' (Bool.or_eq_true_iff.mpr (Or.inr hRev'))]
          exact zero_le
        · refine hContFull (.bundleResp bundleOut) hst' _ ?_
            ⟨stGhost', ?_, hInvGhost', ?_, hSecEq⟩
          · unfold deadDh1Full; simp [hD1', Bool.eq_false_iff.mpr hRev']
          · rw [hSimEq]; rfl
          · dsimp only [hst']
            rw [huEq, bundleSignedMessages_cons_eq, List.length_cons, List.length_cons]
            omega
      · have hTgtF : (FgGapDh.spkBundleFlatIdx S u j == bIdx) = false :=
          Bool.eq_false_iff.mpr hTgt
        have hTgtValF : (FgGapDh.spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := hTgtF
        simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, sampleKemKeyGen,
          bind_assoc, pure_bind]
        refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun spkSk hSpk => ?_)
        have hSpkLen : spkSk.length = 32 := length_of_mem_support_sampleScalar32 hSpk
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun seedKem _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        let spkPk := P.x25519Base spkSk
        let pqspkPk := (P.kemKeyGen seedKem).1
        let pqspkSk := (P.kemKeyGen seedKem).2
        let bEntry1 : SpkBundleEntry := {
          spkSk := spkSk, spkPk := spkPk,
          spkSig := P.sigSign uSk (encodeEC spkPk) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uSk (encodeKEM pqspkPk) rPq }
        let bundleOut : PreKeyBundleInput := {
          ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
          spkSig := bEntry1.spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
          pqspkB := pqspkPk, pqspkSig := bEntry1.pqspkSig }
        let hst' : KeyIndFgCutoffState S :=
          { hst with base :=
            { hst.base with spkBundles := ((u.val, j.val), bEntry1) :: hst.base.spkBundles } }
        let stGhost' : FgKeyIndSimState S :=
          { stGhost with base :=
            { stGhost.base with spkBundles := ((u.val, j.val), bEntry1) :: stGhost.base.spkBundles } }
        have hSpkV' : spkTargetIsV bIdx (P.x25519Base vSk) hst' = true := by
          unfold spkTargetIsV at hSpkV ⊢
          simp [hst', List.all_cons, hTgtValF, hSpkV]
        have hD1' : deadDh1 uIdx hst' = false := by
          unfold deadDh1 at hDead ⊢; exact hDead
        have hInvGhost' : FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' stGhost' := by
          refine ⟨?_, hAdvEq, hCache, by dsimp [stGhost']; omega, by dsimp [hst']; omega,
            ⟨hValidEc.1,
              (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
              hValidEc.2.2.1, hValidEc.2.2.2⟩,
            hSpkV', hPrins, ?_, hOpks, hSess⟩
          · dsimp only [stGhost', hst', bEntry1]
            rw [hBaseEq]
            dsimp only [eraseStateFg, eraseSpkBundlesFg, eraseSpkBundleEntryFg, List.map]
            rw [hTgtValF]
            rfl
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hSpkLen, rfl, fun h => by rw [hTgtValF] at h; cases h⟩
            · exact hSpks kv hMem
        by_cases hRev' : spkTargetRevealed bIdx hst' = true
        · rw [hDeadContFull (.bundleResp bundleOut) hst' (Bool.or_eq_true_iff.mpr (Or.inr hRev'))]
          exact zero_le
        · refine hContFull (.bundleResp bundleOut) hst' _ ?_
            ⟨stGhost', ?_, hInvGhost', ?_, hSecEq⟩
          · unfold deadDh1Full; simp [hD1', Bool.eq_false_iff.mpr hRev']
          · rw [hSimEq]; rfl
          · dsimp only [hst']
            rw [huEq, bundleSignedMessages_cons_eq, List.length_cons, List.length_cons]
            omega
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact hContFull .noneResp hst st hDeadFull
      ⟨stGhost, hSimEq, ⟨hBaseEq, hAdvEq, hCache, by omega, by omega, hValidEc, hSpkV, hPrins,
        hSpks, hOpks, hSess⟩, hBudget, hSecEq⟩

theorem fgKeyInd1KeySimImpl_true_run_delegated {S : Setup} (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (uIdx bIdx maxLen : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (hq : isDelegatedQuery1Key uIdx q = true)
    (st : FgKeyInd1KeySimState S) (stGhost : FgKeyIndSimState S)
    (hSimEq : st.sim = clearTargetSecIKAsign uIdx stGhost) :
    (fgKeyInd1KeySimImpl P uSk ddh true uIdx bIdx S maxLen U V q).run st =
      ((fgKeyIndSimImpl P ddh true uIdx bIdx S maxLen U V q).run stGhost >>=
        fun p => pure (p.1, { st with sim := clearTargetSecIKAsign uIdx p.2 })) := by
  have hStep : (fgKeyInd1KeySimImpl P uSk ddh true uIdx bIdx S maxLen U V q).run st =
      (fgKeyIndStepPure P ddh true uIdx bIdx S maxLen U V q st.sim >>=
        fun p => pure (p.1, { st with sim := p.2 })) := by
    cases q with
    | initPrin _ => cases hq
    | genSPK u j =>
      have hNe : (u.val == uIdx) = false := by simpa [isDelegatedQuery1Key] using hq
      unfold fgKeyInd1KeySimImpl fgKeyInd1KeyStepPure fgGenSPK1KeyPure
      simp [hNe]
    | _ =>
      unfold fgKeyInd1KeySimImpl fgKeyInd1KeyStepPure
      rfl
  have hRhs : (fgKeyIndSimImpl P ddh true uIdx bIdx S maxLen U V q).run stGhost =
      fgKeyIndStepPure P ddh true uIdx bIdx S maxLen U V q stGhost := by
    unfold fgKeyIndSimImpl; simp
  rw [hStep, hRhs, hSimEq,
    fgKeyIndStepPure_clearTargetSecIKAsign_delegated P ddh true uIdx bIdx uIdx S maxLen U V q hq
      stGhost]
  simp only [bind_assoc, pure_bind]

theorem fgStepCoupling_dh1_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hDeadFull : deadDh1Full uIdx bIdx hst = false)
    (hInv : FgSimInvDh1_1Key S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk)
      uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeySimState S → ProbComp Bool)
    (hContFull : ∀ r hst' st', deadDh1Full uIdx bIdx hst' = false →
      FgSimInvDh1_1Key S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk)
        uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadContFull : ∀ r hst', deadDh1Full uIdx bIdx hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true}
      ≤
      𝒟[(fgKeyInd1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk
  have hCases :
      (∃ u, q = .initPrin u) ∨
      (∃ u, q = .corruptIK u ∧ (u.val == uIdx) = true) ∨
      (∃ u j, q = .genSPK u j ∧ (u.val == uIdx) = true) ∨
      (isDelegatedQuery1Key uIdx q = true ∧ ∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | corruptIK u =>
      by_cases h : (u.val == uIdx) = true
      · exact Or.inr (Or.inl ⟨u, rfl, h⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [isDelegatedQuery1Key, h], fun _ hc => by cases hc⟩))
    | genSPK u j =>
      by_cases h : (u.val == uIdx) = true
      · exact Or.inr (Or.inr (Or.inl ⟨u, j, rfl, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by simp [isDelegatedQuery1Key, h], fun _ hc => by cases hc⟩))
    | _ => exact Or.inr (Or.inr (Or.inr ⟨rfl, fun _ hc => by cases hc⟩))
  rcases hCases with ⟨u, rfl⟩ | ⟨u, rfl, hTgt⟩ | ⟨u, j, rfl, hTgt⟩ | ⟨hDel, hNeInit⟩
  · exact fgStepCoupling_dh1_initPrin_1Key S b P R uIdx bIdx uSk vSk huSk u rem hst st
      hDeadFull hInv k1 k2 hContFull
  · exact fgStepCoupling_dh1_corruptIK_tgt_1Key S b P R uIdx bIdx uSk vSk u hTgt rem hst st
      hDeadFull hInv k1 k2 hContFull hDeadContFull
  · exact fgStepCoupling_dh1_genSPK_tgt_1Key S b P R uIdx bIdx uSk vSk hvSk u j hTgt rem hst st
      hDeadFull hInv k1 k2 hContFull hDeadContFull
  · rcases hInv with ⟨stGhost, hSimEq, hGhostInv, hBudget, hSecEq⟩
    rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin true uIdx bIdx (some uSk) (some vSk) P q hNeInit,
      fgKeyInd1KeySimImpl_true_run_delegated P uSk P.isValidDhTriple uIdx bIdx b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q hDel st stGhost hSimEq]
    simp only [bind_assoc, pure_bind]
    let k1' : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool :=
      open scoped Classical in
      fun p => if PreStepPreserves1KeyAux hst p.2 then k1 p else pure false
    have hLhsEq :
        𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] =
        𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1'] := by
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
      have hAux := pqxdhKeyIndFgPreImpl_preserves_1KeyAux_of_ne_initPrin true uIdx bIdx
        (some uSk) (some vSk) P q hNeInit hst x hx
      simp only [k1', hAux, ↓reduceIte]
    rw [hLhsEq]
    refine fgStepCoupling_dh1 S b P hP uIdx bIdx uSk vSk huSk hvSk q rem hst stGhost hDeadFull
      hGhostInv k1' (fun p => k2 (p.1, { st with sim := clearTargetSecIKAsign uIdx p.2 }))
      (fun r hst' stGhost' hDF' hGInv' => ?_) (fun r hst' hDF' => ?_)
    · dsimp only [k1']
      split_ifs with hAux
      · exact hContFull r hst' { st with sim := clearTargetSecIKAsign uIdx stGhost' } hDF'
          ⟨stGhost', rfl, hGInv', by dsimp only; have := hAux.2 uIdx; omega, hAux.1 hSecEq⟩
      · simp
    · dsimp only [k1']
      split_ifs with hAux
      · exact hDeadContFull r hst' hDF'
      · simp

/-- Per-slot Case A (`DH1`) bound on `badKeyIndFgDh1At` in `runKeyIndFgSim1Key` against
    `GapDhWithSignReal`. -/
theorem prob_badKeyIndFgDh1At_1Key_le_gapDhWithSign (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (uIdx : ℕ) (_huIdx : uIdx ∈ Finset.range S.N_id)
    (bIdx : ℕ) (_hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh1At P b.q_ro uIdx bIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhAdvAt true uIdx bIdx S b A) := by
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim1Key_eq_preSample_dh1 uIdx bIdx P A.1
    (fun x => pure (badKeyIndFgDh1At P b.q_ro uIdx bIdx x.2.2.base x.2.2.advRoLog))]
  rw [gapDhWithSignExp_fgKeyInd1KeyGapDhAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  let R := FgSlotReps.ofDh1 P hP uSk vSk huLen hvLen
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadDh1Full uIdx bIdx)
    (FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk)
    (pqxdhKeyIndFgPreImpl1Key true uIdx bIdx (some uSk) (some vSk) S P)
    (fgKeyInd1KeySimImpl P uSk P.isValidDhTriple true uIdx bIdx S b.q_total (P.x25519Base uSk)
      (P.x25519Base vSk))
    (fun q s1 hD x hx =>
      pqxdhKeyIndFgPreImpl1Key_preserves_deadDh1Full P uIdx bIdx uSk vSk q s1 hD x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh1_1Key S b P hP uIdx bIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1 k2
        hCont hDeadCont)
    (fun x => pure (badKeyIndFgDh1At P b.q_ro uIdx bIdx x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdhFromSimState S P P.isValidDhTriple true b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2.sim) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun a s1 hD =>
      by simp [badKeyIndFgDh1At_eq_false_of_deadDh1Full P b.q_ro uIdx bIdx s1 hD])
    (fun a rem s1 s2 hDF hInv =>
      fgSimInvDh1_1Key_terminal_le S b P hP R b.q_ro uIdx bIdx uSk vSk a rem s1 s2 hDF hInv)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyInd1KeySimState.empty S secb)
    (fgSimInvDh1_1Key_empty S b P R uIdx bIdx uSk vSk secb)

end Proofs.SignalPqxdh.Security.FgGapDh1Key
