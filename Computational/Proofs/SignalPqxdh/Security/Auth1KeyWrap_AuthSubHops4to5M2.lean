/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C2
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key all-sessions forgery reduction step

One-key (`pqxdhAuthImpl1KeyG`) counterparts of `pqxdhAuthForgeAllImpl`, `authIntForgeAllExp`,
and `auth_hop_G3_8_split_g5_le_forgeAll` from `AuthSubHops4to5M2`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

/-- `split(.g3_8, stage, true)` oracle implementation (`stage ∈ {.g3_8, .g5}`) on
    `AuthHybridStateFixed S × Bool` that accumulates the all-sessions forgery flag in `.2`. -/
def pqxdhAuthForgeAllImpl1Key (withForge : Bool) (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S × Bool) ProbComp) := fun q =>
  StateT.mk fun ⟨hst, forged⟩ =>
    match q with
    | .recvOPK k j o msg =>
      match prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
      | none => pure (.noneResp, ({ hst with recvCount := hst.recvCount + 1 }, forged))
      | some prep =>
        (fun ((res?, mkSaltCache'), forgedHere) =>
          let (resp, hst') := prep.finish res?
          (resp, ({
            toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache :=
                mkSaltCache' },
            forged || forgedHere))) <$>
          evalAuthRecvScheduleForgeAll withForge stage P prep.hstDec
            hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
    | .recvNoOPK k j l msg =>
      match prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
      | none => pure (.noneResp, ({ hst with recvCount := hst.recvCount + 1 }, forged))
      | some prep =>
        (fun ((res?, mkSaltCache'), forgedHere) =>
          let (resp, hst') := prep.finish res?
          (resp, ({
            toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache :=
                mkSaltCache' },
            forged || forgedHere))) <$>
          evalAuthRecvScheduleForgeAll withForge stage P prep.hstDec
            hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
    | qOther =>
      (fun (resp, hst') => (resp, (hst', forged))) <$>
        (pqxdhAuthHybridSplitFixedImpl1Key .g3_8 .g3_8 true true S P qOther).run hst

/-- All-sessions forgery experiment: run `A` against `split(.g3_8, .g5, true)` and return whether
    `authIntForgedAll` ever held. -/
noncomputable def authIntForgeAllExp1Key (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := (AuthHybridStateFixed.empty S secb, false)
  let impl :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
          ProbComp) +
    pqxdhAuthForgeAllImpl1Key true .g5 S P
  let (_b', _finalSt, forged) ← (simulateQ impl A.run).run initSt
  return forged

theorem pqxdhAuthForgeAllImpl_fst1Key (withForge : Bool) (stage : AuthHybridStage)
    (hStage : stage = .g3_8 ∨ stage = .g5)
    (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (forged : Bool)
    {β : Type} (f : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp β) :
    ((pqxdhAuthForgeAllImpl1Key withForge stage S P q).run (hst, forged) >>=
      fun p => f (p.1, p.2.1)) =
    ((pqxdhAuthHybridSplitFixedImpl1Key .g3_8 stage true true S P q).run hst >>= f) := by
  have hIdeal : stage.idealMsgKeys = true := by rcases hStage with rfl | rfl <;> rfl
  cases q with
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthForgeAllImpl1Key, pqxdhAuthHybridSplitFixedImpl1Key, StateT.run_mk]
    simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind,
      pqxdhAuthHybridFixedImpl_recvOPK_eq1Key stage hIdeal]
    cases prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
    | none => simp
    | some prep =>
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      exact evalAuthRecvScheduleForgeAll_fst withForge stage hStage P prep.hstDec
        hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        (fun x => f ((prep.finish x.1).1,
          {
            toAuthHybridState := (prep.finish x.1).2, recvCount := hst.recvCount + 1, mkSaltCache :=
                x.2 }))
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthForgeAllImpl1Key, pqxdhAuthHybridSplitFixedImpl1Key, StateT.run_mk]
    simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind,
      pqxdhAuthHybridFixedImpl_recvNoOPK_eq1Key stage hIdeal]
    cases prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
    | none => simp
    | some prep =>
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      exact evalAuthRecvScheduleForgeAll_fst withForge stage hStage P prep.hstDec
        hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        (fun x => f ((prep.finish x.1).1,
          {
            toAuthHybridState := (prep.finish x.1).2, recvCount := hst.recvCount + 1, mkSaltCache :=
                x.2 }))
  | _ =>
    have hg38 : AuthHybridStage.g3_8.idealMsgKeys = true := rfl
    dsimp only [pqxdhAuthForgeAllImpl1Key, StateT.run_mk]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    unfold pqxdhAuthHybridSplitFixedImpl1Key
    simp [hIdeal, hg38]

theorem simulateQ_pqxdhAuthForgeAllImpl_fst1Key {α β : Type}
    (withForge : Bool) (stage : AuthHybridStage) (hStage : stage = .g3_8 ∨ stage = .g5)
    (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S) (forged : Bool)
    (f : α × AuthHybridStateFixed S → ProbComp β) :
    let implForge :=
        (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
            ProbComp) +
      pqxdhAuthForgeAllImpl1Key withForge stage S P
    let implSplit := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridSplitFixedImpl1Key .g3_8 stage true true S P
    ((simulateQ implForge oa).run (hst, forged) >>= fun p => f (p.1, p.2.1)) =
      ((simulateQ implSplit oa).run hst >>= f) := by
  intro implForge implSplit
  induction oa using OracleComp.inductionOn generalizing hst forged with
  | pure a => simp
  | query_bind q mx ih =>
    rcases q with uq | aq
    · dsimp only [implForge, implSplit]
      rw [FgGapDh.simulateQ_run_query_inl, FgGapDh.simulateQ_run_query_inl, bind_assoc, bind_assoc]
      congr 1; funext u; exact ih u hst forged
    · dsimp only [implForge, implSplit]
      rw [FgGapDh.simulateQ_run_query_inr, FgGapDh.simulateQ_run_query_inr, bind_assoc, bind_assoc]
      rw [← pqxdhAuthForgeAllImpl_fst1Key withForge stage hStage S P aq hst forged
        (fun y => (simulateQ implSplit (mx y.1)).run y.2 >>= f)]
      congr 1; funext ⟨r, hst', forged'⟩; exact ih r hst' forged'

theorem pqxdhAuthForgeAllImpl_bad_mono1Key (withForge : Bool) (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (q : AuthQuery S)
    (s6 : AuthHybridStateFixed S × Bool) (hBad : s6.2 = true) :
    ∀ y ∈ support ((pqxdhAuthForgeAllImpl1Key withForge stage S P q).run s6),
      y.2.2 = true := by
  rcases s6 with ⟨hst, forged⟩; dsimp only at hBad; subst hBad; intro y hy
  cases q with
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthForgeAllImpl1Key, StateT.run_mk] at hy
    cases hprep : prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
    | none => simp only [hprep, support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
    | some prep =>
      simp only [hprep, support_map, Set.mem_image] at hy
      rcases hy with ⟨⟨⟨res?, mkSaltCache'⟩, forgedHere⟩, _, rfl⟩; simp
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthForgeAllImpl1Key, StateT.run_mk] at hy
    cases hprep : prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
    | none => simp only [hprep, support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
    | some prep =>
      simp only [hprep, support_map, Set.mem_image] at hy
      rcases hy with ⟨⟨⟨res?, mkSaltCache'⟩, forgedHere⟩, _, rfl⟩; simp
  | _ =>
    dsimp only [pqxdhAuthForgeAllImpl1Key, StateT.run_mk] at hy
    simp only [support_map, Set.mem_image] at hy; rcases hy with ⟨⟨resp, hst'⟩, _, rfl⟩; rfl

theorem relProbUpToBad_pqxdhAuthForgeAll_step1Key
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P) (q : AuthQuery S)
    (s5 s6 : AuthHybridStateFixed S × Bool)
    (hAgree : s5 = s6 ∧ s6.2 = false ∧ IdealSessionsAeadValid P s5.1) :
    RelProbUpToBad
      (fun y5 y6 => y5.1 = y6.1 ∧ y5.2 = y6.2 ∧ y6.2.2 = false ∧ IdealSessionsAeadValid P y5.2.1)
      (fun y6 => y6.2.2)
      ((pqxdhAuthForgeAllImpl1Key false .g3_8 S P q).run s5)
      ((pqxdhAuthForgeAllImpl1Key true .g5 S P q).run s6) := by
  rcases hAgree with ⟨rfl, hForged, hInv⟩; rcases s5 with ⟨hst, forged⟩
  dsimp only at hForged hInv; subst hForged
  cases q with
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthForgeAllImpl1Key, StateT.run_mk]
    cases hprep : prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
    | none => exact RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, hInv⟩
    | some prep =>
      simp only [map_eq_bind_pure_comp, Function.comp_def]
      have hId :=
          prepareAuthHybridRecvOPK_idealSessions true P k j o msg hst.toAuthHybridState hprep
      have hDecInv : ∀ s ∈ prep.hstDec.idealSessions,
          s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧
              initSessionSlotIdx s.sid < S.N_send_tot := by
        rw [hId.1]; exact hInv
      refine RelProbUpToBad.bind_rel
        (relProbUpToBad_evalAuthRecvScheduleForgeAll P hWF prep.hstDec hDecInv
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg)
        (fun b6 hb6 y6 hy6 => by
          simp only [support_pure, Set.mem_singleton_iff] at hy6; subst hy6; simp [hb6])
        (fun b5 b6 ⟨hEq1, hEq2, hEq3, hEq4⟩ => ?_)
      rcases b5 with ⟨⟨res5?, mkSaltCache5'⟩, forged5⟩
      rcases b6 with ⟨⟨res6?, mkSaltCache6'⟩, forged6⟩
      dsimp only at hEq1 hEq2 hEq3 hEq4; cases hEq1; subst hEq2 hEq3 hEq4
      refine RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, ?_⟩
      unfold IdealSessionsAeadValid; dsimp only; rw [hId.2 res5?]; exact hInv
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthForgeAllImpl1Key, StateT.run_mk]
    cases hprep : prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
    | none => exact RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, hInv⟩
    | some prep =>
      simp only [map_eq_bind_pure_comp, Function.comp_def]
      have hId :=
          prepareAuthHybridRecvNoOPK_idealSessions true P k j l msg hst.toAuthHybridState hprep
      have hDecInv : ∀ s ∈ prep.hstDec.idealSessions,
          s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧
              initSessionSlotIdx s.sid < S.N_send_tot := by
        rw [hId.1]; exact hInv
      refine RelProbUpToBad.bind_rel
        (relProbUpToBad_evalAuthRecvScheduleForgeAll P hWF prep.hstDec hDecInv
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg)
        (fun b6 hb6 y6 hy6 => by
          simp only [support_pure, Set.mem_singleton_iff] at hy6; subst hy6; simp [hb6])
        (fun b5 b6 ⟨hEq1, hEq2, hEq3, hEq4⟩ => ?_)
      rcases b5 with ⟨⟨res5?, mkSaltCache5'⟩, forged5⟩
      rcases b6 with ⟨⟨res6?, mkSaltCache6'⟩, forged6⟩
      dsimp only at hEq1 hEq2 hEq3 hEq4; cases hEq1; subst hEq2 hEq3 hEq4
      refine RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, ?_⟩
      unfold IdealSessionsAeadValid; dsimp only; rw [hId.2 res5?]; exact hInv
  | _ =>
    dsimp only [pqxdhAuthForgeAllImpl1Key, StateT.run_mk]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine RelProbUpToBad.bind_same_of_support _ (fun ⟨resp, hst'⟩ hp => ?_)
    exact RelProbUpToBad.of_pure
      ⟨rfl, rfl, rfl,
          idealSessionsAeadValid_nonRecvSplitFixed1Key .g3_8 .g3_8 rfl true true P _ hst hInv hp⟩

/-- Bounds the `G3.8 → split(.g3_8, .g5, true)` game distance by `authIntForgeAllExp1Key`. -/
theorem auth_hop_G3_8_split_g5_le_forgeAll1Key (S : Setup) (P : Primitives)
    (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    |(𝒟[authFixedExpG3_8_1Key S P A] {true}).toReal -
     (𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A] {true}).toReal| ≤
      (𝒟[authIntForgeAllExp1Key S P A] {true}).toReal := by
  let impl5 :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
          ProbComp) +
    pqxdhAuthForgeAllImpl1Key false .g3_8 S P
  let impl6 :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
          ProbComp) +
    pqxdhAuthForgeAllImpl1Key true .g5 S P
  let fin (secb : Bool) (p : Bool × (AuthHybridStateFixed S × Bool)) : ProbComp Bool :=
    let (b', finalSt, _) := p
    let allChallengedClean := finalSt.toAuthHybridState.base.sessions.all (fun s =>
      !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)
    if hasEcPkCollisionAuth P finalSt.toAuthHybridState || hasBadSigAuth finalSt.toAuthHybridState
        ||
       hasKemPkCollisionAuth finalSt.toAuthHybridState || hasBadKemShCrAuth P
           finalSt.toAuthHybridState then
      $ᵗ Bool
    else if true && finalSt.toAuthHybridState.base.hasWonAuth then pure true
    else if !allChallengedClean then $ᵗ Bool
    else pure (b' == secb)
  have hG38 : authFixedExpG3_8_1Key S P A =
      ($ᵗ Bool >>= fun secb =>
        (simulateQ impl5 A.run).run (AuthHybridStateFixed.empty S secb, false) >>= fin secb) := by
    unfold authFixedExpG3_8_1Key
    rw [← authSplitFixedExp_same_true1Key .g3_8 S P A]
    unfold authSplitFixedExp1Key; congr 1; funext secb
    exact (simulateQ_pqxdhAuthForgeAllImpl_fst1Key false .g3_8 (Or.inl rfl) S P A.run
      (AuthHybridStateFixed.empty S secb) false (fun q => fin secb (q.1, q.2, false))).symm
  have hG5 : authSplitFixedExp1Key .g3_8 .g5 true S P A =
      ($ᵗ Bool >>= fun secb =>
        (simulateQ impl6 A.run).run (AuthHybridStateFixed.empty S secb, false) >>= fin secb) := by
    unfold authSplitFixedExp1Key; congr 1; funext secb
    exact (simulateQ_pqxdhAuthForgeAllImpl_fst1Key true .g5 (Or.inr rfl) S P A.run
      (AuthHybridStateFixed.empty S secb) false (fun q => fin secb (q.1, q.2, false))).symm
  rw [hG38, hG5]
  refine evalDist_outer_bind_abs_sub_le' ($ᵗ Bool)
    (fun secb => (simulateQ impl5 A.run).run (AuthHybridStateFixed.empty S secb, false))
    (fun secb => (simulateQ impl6 A.run).run (AuthHybridStateFixed.empty S secb, false))
    (fun _secb p => p.2.2) fin fin (fun secb => ?_)
  have hSim := simulateQ_relProbUpToBad
    (pqxdhAuthForgeAllImpl1Key false .g3_8 S P)
    (pqxdhAuthForgeAllImpl1Key true .g5 S P)
    (fun s5 s6 => s5 = s6 ∧ s6.2 = false ∧ IdealSessionsAeadValid P s5.1)
    (fun s6 => s6.2)
    (pqxdhAuthForgeAllImpl_bad_mono1Key true .g5 S P)
    (relProbUpToBad_pqxdhAuthForgeAll_step1Key S P hWF)
    A.run (AuthHybridStateFixed.empty S secb, false) (AuthHybridStateFixed.empty S secb, false)
    ⟨rfl, rfl, idealSessionsAeadValid_empty S P secb⟩
  exact RelProbUpToBad.evalDist_bind_le hSim (fun _ _ ⟨_, _, hFalse, _⟩ => hFalse) (fin secb)
      (fin secb)
    (fun x5 x6 ⟨h1, h2, _, _⟩ => by
      rcases x5 with ⟨b5, s5, f5⟩; rcases x6 with ⟨b6, s6, f6⟩
      dsimp only at h1 h2; cases h1; cases h2; rfl)

end SignalPqxdh.Security
