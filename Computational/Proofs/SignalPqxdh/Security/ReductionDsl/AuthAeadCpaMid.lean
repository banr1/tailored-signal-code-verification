/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.RedProg2Sim
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaShallow
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaLeaves
import VCVio.EvalDist.Monad.Basic

/-!
# Shallow Runner Characterization for the `AeadIndCpa` Reduction

Relates the shallow `aeadCpaReductionAuthFixed` stage runners to the generic
`TwoStageCostedReduction` runners and proves experiment-level congruence `aeadIndCpaExp_congr`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp

abbrev CpaPI (S : Setup) : Nat → (Bytes × Bytes × Bytes) → AuthCpaPausePayload S →
    AuthHybridStateFixed S → Prop :=
  fun n c p h => CpaPauseInv n c p h

theorem cpaSendResToStep_leaf (S : Setup) (n : Nat) (x : CpaSendRes S) (hx : CpaSendLeaf n x) :
    PreStepInvP (R := AuthResponse) (fun n h => CpaInv n h) (CpaPI S) n (cpaSendResToStep x) := by
  rcases x with ⟨r, h⟩ | ⟨ad, m0, m1, p, h⟩
  · exact hx
  · exact hx

theorem stepMidCpa_leaves (S : Setup) (idx n : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (hI : CpaInv n hst) :
    HoldsOnLeaves (PreStepInvP (fun n h => CpaInv n h) (CpaPI S) n) (stepMidCpa S idx q hst) := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepMidCpa, cpaSendShOpk]
    split
    · exact HoldsOnLeaves.pure (hI.mono (Nat.le_succ n))
    · exact HoldsOnLeaves.map _
        (tryPauseAuthCpaSendFixedPrim_leaves S true idx n _ u b m0 m1 hst hI).toHoldsOnLeaves
        (fun x hx => cpaSendResToStep_leaf S n x hx)
  case sendNoOPK u i b m0 m1 =>
    simp only [stepMidCpa, cpaSendShNoOpk]
    split
    · exact HoldsOnLeaves.pure (hI.mono (Nat.le_succ n))
    · exact HoldsOnLeaves.map _
        (tryPauseAuthCpaSendFixedPrim_leaves S true idx n _ u b m0 m1 hst hI).toHoldsOnLeaves
        (fun x hx => cpaSendResToStep_leaf S n x hx)
  all_goals
    exact HoldsOnLeaves.map _ (stepAuthCpaNonSendPrim_leaves S n _ hst hI).toHoldsOnLeaves
      (fun x hx => hx)

def Gcpa {S : Setup} :
    Option (Bytes × Bytes × Bytes) ×
      RedProg2State (authSpec S) Bool (AuthCpaPausePayload S) (AuthHybridStateFixed S) →
    AuthCpaPauseResult S Bool
  | (_, .done a h) => .done a h
  | (some c, .paused _ p h k) => .paused c.1 c.2.1 c.2.2 p h k
  | (none, .paused _ p h k) => .paused p.ad p.m0 p.m1 p h k

theorem stepUntilCpa_eq (S : Setup) (idx : Nat) (mx : OracleComp (unifSpec + authSpec S) Bool)
    (fuel : Nat) (hst : AuthHybridStateFixed S) :
    stepUntilAuthCpaChallengeFixedPrim idx S false mx fuel hst =
      Gcpa <$> stepUntilPauseFuel false (stepMidCpa S idx) mx fuel hst := by
  refine stepUntilPauseFuel_char false (stepMidCpa S idx) Gcpa
    (fun mx fuel h => stepUntilAuthCpaChallengeFixedPrim idx S false mx fuel h) ?_ ?_ ?_ ?_
    mx fuel hst
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [stepUntilAuthCpaChallengeFixedPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k s
    simp only [stepUntilAuthCpaChallengeFixedPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [stepUntilAuthCpaChallengeFixedPrim]
    rw [OracleComp.construct_query_bind]
    cases gq
    case sendOPK u i b m0 m1 =>
      simp only [stepMidCpa, cpaSendShOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        refine bind_congr fun x => ?_
        rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> rfl
    case sendNoOPK u i b m0 m1 =>
      simp only [stepMidCpa, cpaSendShNoOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        refine bind_congr fun x => ?_
        rcases x with ⟨r, h⟩ | ⟨ad, m0', m1', p, h⟩ <;> rfl
    all_goals
      simp only [stepMidCpa]
      rw [bind_map_left]

theorem runWithPrimStepFuel_eq (S : Setup) (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (fuel : Nat) (hst : AuthHybridStateFixed S) :
    runWithPrimStepFuel false (stepAuthCpaCutoffPrim idx S) mx fuel hst =
      runWithFuelPrim false (stepAuthCpaCutoffPrim idx S) mx fuel hst := by
  have := runWithFuelPrim_char false (stepAuthCpaCutoffPrim idx S) id
    (fun mx fuel h => runWithPrimStepFuel false (stepAuthCpaCutoffPrim idx S) mx fuel h)
    (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind]
      rfl)
    (fun gq k s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind])
    mx fuel hst
  rw [this, id_map]

/-- Two `AeadIndCpaAdv` adversaries whose `choose` stages are pushforwards of a common computation
    agreeing on `I`-leaves and whose `dist` stages agree on the mapped states induce equal experiments. -/
theorem aeadIndCpaExp_congr (P : Primitives) (A B : AeadIndCpaAdv) {α : Type}
    (m : OracleComp PrimBaseSpec α) (I : α → Prop) (hm : HoldsOnLeaves I m)
    (FA : α → Bytes × Bytes × Bytes × A.State) (FB : α → Bytes × Bytes × Bytes × B.State)
    (hA : A.choose = FA <$> m) (hB : B.choose = FB <$> m)
    (hOut : ∀ x, I x → (FB x).1 = (FA x).1 ∧ (FB x).2.1 = (FA x).2.1 ∧
      (FB x).2.2.1 = (FA x).2.2.1)
    (hDist : ∀ x, I x → ∀ c, B.dist (FB x).2.2.2 c = A.dist (FA x).2.2.2 c) :
    aeadIndCpaExp P B = aeadIndCpaExp P A := by
  unfold aeadIndCpaExp
  refine bind_congr fun b => bind_congr fun mk => ?_
  rw [hA, hB, simulateQ_map, simulateQ_map, bind_map_left, bind_map_left]
  refine (SignalPqxdh.Security.ReductionDsl.HoldsOnLeaves.simulateQ (primBaseImpl P)
    ⟨hm.bind_congr⟩).bind_congr _ _ (fun x hx => ?_)
  obtain ⟨h1, h2, h3⟩ := hOut x hx
  have h4 := hDist x hx
  rcases hFA : FA x with ⟨ad, m0, m1, sA⟩
  rcases hFB : FB x with ⟨ad', m0', m1', sB⟩
  rw [hFA, hFB] at h1 h2 h3
  rw [hFA, hFB] at h4
  simp only at h1 h2 h3 h4
  subst h1 h2 h3
  simp only [h4]

theorem finalizeAuthFixedPrim_true_eq (S : Setup) (b' : Bool) (st : AuthHybridState S)
    (hw : st.base.hasWonAuth = false) :
    AuthSubHops1to3.finalizeAuthFixedPrim S true b' st = finalizeAeadCpaGameNoAuthPrim S b' st := by
  simp only [AuthSubHops1to3.finalizeAuthFixedPrim, finalizeAeadCpaGameNoAuthPrim, hw,
    Bool.false_eq_true, ↓reduceIte, AuthSubHops1to3.allHonestEcPksAuthPrim,
    allHonestEcPksAuthPrim, AuthSubHops1to3.hasBadKemShCrRecordsPure, hasBadKemShCrRecordsPure,
    AuthSubHops1to3.allChallengedCleanPure, allChallengedCleanPure, beq_true,
    authSubHops1to3_mapMPrim_eq]
  rfl

abbrev CpaSlotPI (S : Setup) (idx : Nat) :
    Nat → (Bytes × Bytes × Bytes) → AuthCpaPausePayload S → CpaSlotSt S → Prop :=
  fun n c p sh => CpaSlotPauseInv idx n c p sh

theorem cpaSlotSendResToStep_leaf (S : Setup) (idx n : Nat) (x : CpaSlotSendRes S)
    (hx : CpaSlotSendLeaf idx n x) :
    PreStepInvP (R := AuthResponse) (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx) n
      (cpaSlotSendResToStep x) := by
  rcases x with ⟨r, sh⟩ | ⟨ad, m0, m1, p, sh⟩
  · exact hx
  · exact hx

theorem stepMidCpaSlot_leaves (S : Setup) (idx n : Nat) (q : AuthQuery S)
    (shst : CpaSlotSt S) (hI : CpaSlotInv n shst) :
    HoldsOnLeaves (PreStepInvP (fun n sh => CpaSlotInv n sh) (CpaSlotPI S idx) n)
      (stepMidCpaSlot S idx q shst) := by
  cases q
  case sendOPK u i b m0 m1 =>
    simp only [stepMidCpaSlot, cpaSendSlotShOpk]
    split
    · exact HoldsOnLeaves.pure (hI.mono (Nat.le_succ n))
    · exact HoldsOnLeaves.map _
        (cpaTryPauseSendSlotPrim_leaves S true idx n _ u b m0 m1 shst hI).toHoldsOnLeaves
        (fun x hx => cpaSlotSendResToStep_leaf S idx n x hx)
  case sendNoOPK u i b m0 m1 =>
    simp only [stepMidCpaSlot, cpaSendSlotShNoOpk]
    split
    · exact HoldsOnLeaves.pure (hI.mono (Nat.le_succ n))
    · exact HoldsOnLeaves.map _
        (cpaTryPauseSendSlotPrim_leaves S true idx n _ u b m0 m1 shst hI).toHoldsOnLeaves
        (fun x hx => cpaSlotSendResToStep_leaf S idx n x hx)
  all_goals
    exact HoldsOnLeaves.map _
      (stepAuthCpaNonSendPrim_ideal_leaves S n _ shst.2 hI.inv hI.ideal_le).toHoldsOnLeaves
      (fun x ⟨hinv, hideal⟩ => ⟨hinv, hideal, Nat.le_trans hI.slot_le (Nat.le_succ n)⟩)

def GcpaSlot {S : Setup} :
    Option (Bytes × Bytes × Bytes) ×
      RedProg2State (authSpec S) Bool (AuthCpaPausePayload S) (CpaSlotSt S) →
    CpaSlotPauseRes S Bool
  | (_, .done a sh) => .done a sh
  | (some c, .paused _ p sh k) => .paused c.1 c.2.1 c.2.2 p sh k
  | (none, .paused _ p sh k) => .paused p.ad p.m0 p.m1 p sh k

theorem stepUntilCpaSlot_eq (S : Setup) (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (fuel : Nat) (shst : CpaSlotSt S) :
    cpaStepUntilChallengeSlotPrim idx S false mx fuel shst =
      GcpaSlot <$> stepUntilPauseFuel false (stepMidCpaSlot S idx) mx fuel shst := by
  refine stepUntilPauseFuel_char false (stepMidCpaSlot S idx) GcpaSlot
    (fun mx fuel sh => cpaStepUntilChallengeSlotPrim idx S false mx fuel sh) ?_ ?_ ?_ ?_
    mx fuel shst
  · intro a fuel s; rfl
  · intro uq k fuel s
    simp only [cpaStepUntilChallengeSlotPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k s
    simp only [cpaStepUntilChallengeSlotPrim]
    rw [OracleComp.construct_query_bind]
    rfl
  · intro gq k fuel s
    simp only [cpaStepUntilChallengeSlotPrim]
    rw [OracleComp.construct_query_bind]
    cases gq
    case sendOPK u i b m0 m1 =>
      simp only [stepMidCpaSlot, cpaSendSlotShOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        refine bind_congr fun x => ?_
        rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
    case sendNoOPK u i b m0 m1 =>
      simp only [stepMidCpaSlot, cpaSendSlotShNoOpk]
      split
      · simp only [map_pure, pure_bind]; rfl
      · rw [bind_map_left]
        refine bind_congr fun x => ?_
        rcases x with ⟨r, sh⟩ | ⟨ad, m0', m1', p, sh⟩ <;> rfl
    all_goals
      simp only [stepMidCpaSlot]
      rw [bind_map_left]

theorem runWithPrimStepFuelSlot_eq (S : Setup) (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) Bool) (fuel : Nat) (shst : CpaSlotSt S) :
    runWithPrimStepFuel false (cpaStepCutoffSlotPrim idx S) mx fuel shst =
      runWithFuelPrim false (cpaStepCutoffSlotPrim idx S) mx fuel shst := by
  have := runWithFuelPrim_char false (cpaStepCutoffSlotPrim idx S) id
    (fun mx fuel sh => runWithPrimStepFuel false (cpaStepCutoffSlotPrim idx S) mx fuel sh)
    (fun _ _ _ => rfl)
    (fun uq k fuel s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind]
      rfl)
    (fun gq k s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind]; rfl)
    (fun gq k fuel s => by
      simp only [runWithPrimStepFuel]; rw [OracleComp.construct_query_bind])
    mx fuel shst
  rw [this, id_map]

end SignalPqxdh.Security.ReductionDsl.AuthAead
