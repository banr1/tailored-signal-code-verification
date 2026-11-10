/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingE
public import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` Cutoff Oracle Wrapper and Trace Monotonicity

Defines `pqxdhAuthAdvStageImpl1Key` over `pqxdhAuthHybridKoskImpl1Key` and proves state-extension
and `isAuthG3Abort` monotonicity for the one-key `Auth` `G3 -> G3.5` hop.
-/

@[expose] public section

set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

/-- Stage-parameterized one-key `Auth` oracle wrapper recording `advRoLog` and `respRecs`. -/
def pqxdhAuthAdvStageImpl1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthAdvCutoffState S) ProbComp) := fun q =>
  match q with
  | .roQuery secrets => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl1Key stage true true S P (.roQuery secrets)).run hst.hyb
    return (resp, { hst with hyb := h', advRoLog := secrets :: hst.advRoLog }))
  | .recvOPK k j o msg => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl1Key stage true true S P (.recvOPK k j o msg)).run hst.hyb
    let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
      msg.hdr.ekAPk }
    return (resp, { hst with hyb := h', respRecs := rRec :: hst.respRecs }))
  | .recvNoOPK k j l msg => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl1Key stage true true S P (.recvNoOPK k j l msg)).run
      hst.hyb
    let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
      msg.hdr.ekAPk }
    return (resp, { hst with hyb := h', respRecs := rRec :: hst.respRecs }))
  | q => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl1Key stage true true S P q).run hst.hyb
    return (resp, { hst with hyb := h' }))

theorem map_hyb_pqxdhAuthAdvStageImpl1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthAdvCutoffState S) :
    Prod.map id AuthAdvCutoffState.hyb <$> ((pqxdhAuthAdvStageImpl1Key stage S P q).run hst) =
      (pqxdhAuthHybridKoskImpl1Key stage true true S P q).run hst.hyb := by
  cases q <;> simp [pqxdhAuthAdvStageImpl1Key, StateT.run_mk, Prod.map]

theorem map_hyb_fullAuthAdvStageImpl1Key (stage : AuthHybridStage) (S : Setup) (P : Primitives)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthAdvCutoffState S) :
    Prod.map id AuthAdvCutoffState.hyb <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthAdvCutoffState S) ProbComp) +
        pqxdhAuthAdvStageImpl1Key stage S P) q).run hst =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S) ProbComp) +
      pqxdhAuthHybridKoskImpl1Key stage true true S P) q).run hst.hyb := by
  cases q with
  | inl uq => simp [QueryImpl.liftTarget, StateT.run_monadLift, Prod.map]
  | inr gq => exact map_hyb_pqxdhAuthAdvStageImpl1Key stage S P gq hst

theorem simulateQ_map_hyb_fullAuthAdvStageImpl1Key (stage : AuthHybridStage) (S : Setup) (P :
    Primitives)
    {α : Type} (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthAdvCutoffState S) :
    let fullAdv := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthAdvCutoffState S) ProbComp) + pqxdhAuthAdvStageImpl1Key stage S P
    let fullHyb := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthHybridState S) ProbComp) + pqxdhAuthHybridKoskImpl1Key stage true true S P
    Prod.map id AuthAdvCutoffState.hyb <$> ((simulateQ fullAdv oa).run hst) =
      (simulateQ fullHyb oa).run hst.hyb :=
  _root_.Proofs.SignalPqxdh.Security.map_proj_simulateQ
    AuthAdvCutoffState.hyb
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthAdvCutoffState S) ProbComp) + pqxdhAuthAdvStageImpl1Key stage S P)
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthHybridState S) ProbComp) + pqxdhAuthHybridKoskImpl1Key stage true true S P)
    (map_hyb_fullAuthAdvStageImpl1Key stage S P)
    oa hst

theorem authKoskExpAtStage_eq_bind_finalizeAuthKosk1Key (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage1Key stage S P A = (do
      let secb ← $ᵗ Bool
      let initSt := AuthHybridState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridState S)
        ProbComp) +
        pqxdhAuthHybridKoskImpl1Key stage true true S P
      let (b', finalSt) ← (simulateQ impl A.run).run initSt
      finalizeAuthKosk S P secb b' finalSt) := rfl

theorem authKoskExpAtStage_eq_advStage1Key (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    authKoskExpAtStage1Key stage S P A = (do
      let secb ← $ᵗ Bool
      let initSt := AuthAdvCutoffState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthAdvCutoffState S)
        ProbComp) +
        pqxdhAuthAdvStageImpl1Key stage S P
      let (b', finalHst) ← (simulateQ impl A.run).run initSt
      finalizeAuthKosk S P secb b' finalHst.hyb) := by
  rw [authKoskExpAtStage_eq_bind_finalizeAuthKosk1Key]
  apply bind_congr; intro secb
  have hsim := simulateQ_map_hyb_fullAuthAdvStageImpl1Key stage S P A.run
    (AuthAdvCutoffState.empty S secb)
  dsimp only [AuthAdvCutoffState.hyb_empty] at hsim ⊢
  rw [← hsim, bind_map_left]
  rfl

theorem authFixedAdvG3_sub_G3_5_le_two_mul_abs_sub1Key
    (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    |authFixedAdvG3_1Key S P A - authFixedAdvG3_5_1Key S P A| ≤
      2 * |(𝒟[authKoskExpAtStage1Key .g3_5 S P A] {true}).toReal -
           (𝒟[authKoskExpAtStage1Key .g3 S P A] {true}).toReal| := by
  have hG3 : authFixedAdvG3_1Key S P A = (𝒟[authKoskExpAtStage1Key .g3 S P A].boolBias).toReal := by
    change authFixedAdvAtStage1Key .g3 S P A = _
    rw [authFixedAdvAtStage_eq_authKoskAdvAtStage1Key .g3 S P A]
    rfl
  have hG35 : authFixedAdvG3_5_1Key S P A = (𝒟[authKoskExpAtStage1Key .g3_5 S P A].boolBias).toReal := by
    change authFixedAdvAtStage1Key .g3_5 S P A = _
    rw [authFixedAdvAtStage_eq_authKoskAdvAtStage1Key .g3_5 S P A]
    rfl
  rw [hG3, hG35, abs_sub_comm (𝒟[authKoskExpAtStage1Key .g3_5 S P A] {true}).toReal]
  exact abs_sub_boolBias_toReal_le_two_mul_abs_sub
    (authKoskExpAtStage1Key .g3 S P A) (authKoskExpAtStage1Key .g3_5 S P A)

private theorem map_prin_ikAPk_corrupt {P : Primitives} (u : ℕ)
    (principals : List (Nat × PrincipalEntry)) :
    (principals.map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e))).map
        (fun (_, e) => P.pow8 e.ikAPk) =
    principals.map (fun (_, e) => P.pow8 e.ikAPk) := by
  rw [List.map_map]
  congr 1; funext ⟨idx, e⟩
  dsimp only [Function.comp_apply]
  split_ifs <;> rfl

private theorem map_opk_opkPk_consume {P : Primitives} (key : Nat × Nat × Nat)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) :
    (opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e))).map
        (fun (_, o) => P.pow8 o.opkPk) =
    opkEntries.map (fun (_, o) => P.pow8 o.opkPk) := by
  rw [List.map_map]
  congr 1; funext ⟨idx, e⟩
  dsimp only [Function.comp_apply]
  split_ifs <;> rfl

private theorem state_eq_of_liftM {σ α : Type} (mx : ProbComp α) (s : σ) :
    ∀ p ∈ support ((liftM mx : StateT σ ProbComp α).run s), p.2 = s := by
  intro p hp
  simp only [StateT.run_monadLift, monadLift_self, support_bind, Set.mem_iUnion,
    mem_support_pure_iff] at hp
  rcases hp with ⟨_, _, rfl⟩; rfl

private theorem authHybridExtends_bind_state_eq {S : Setup} {α β : Type} (P : Primitives)
    {m1 : StateT (AuthHybridState S) ProbComp α}
    {f : α → StateT (AuthHybridState S) ProbComp β}
    (hst : AuthHybridState S)
    {y : β × AuthHybridState S}
    (hy : y ∈ support ((m1 >>= f).run hst))
    (h1 : ∀ p ∈ support (m1.run hst), p.2 = hst)
    (h2 : ∀ a, ∀ y ∈ support ((f a).run hst), AuthHybridExtends P hst y.2) :
    AuthHybridExtends P hst y.2 := by
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hy
  rcases hy with ⟨⟨a, hst'⟩, hp, hy'⟩
  rw [h1 (a, hst') hp] at hy'
  exact h2 a y hy'

private theorem authHybridExtends_pure_noneResp {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pure AuthResponse.noneResp : StateT (AuthHybridState S) ProbComp
      AuthResponse).run hst)) :
    AuthHybridExtends P hst y.2 := by
  rw [StateT.run_pure, mem_support_pure_iff] at hy
  rcases hy with ⟨_, rfl⟩
  exact AuthHybridExtends.refl P hst

private theorem authHybridExtends_if_noneResp {S : Setup} (P : Primitives) (c : Prop) [Decidable c]
    (m : StateT (AuthHybridState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    {y : AuthResponse × AuthHybridState S}
    (h : y ∈ support (m.run hst) → AuthHybridExtends P hst y.2)
    (hy : y ∈ support ((if c then pure AuthResponse.noneResp else m).run hst)) :
    AuthHybridExtends P hst y.2 := by
  split_ifs at hy
  · exact authHybridExtends_pure_noneResp P hst hy
  · exact h hy

private theorem authHybridExtends_of_liftAuthBase {S : Setup} (P : Primitives)
    (m : StateT (AuthState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (h : ∀ p ∈ support (m.run hst.base),
      AuthHybridExtends P hst { hst with base := p.2 })
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((liftAuthBase m).run hst)) :
    AuthHybridExtends P hst y.2 := by
  unfold liftAuthBase at hy
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
    support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hp, _, rfl⟩
  exact h (resp, base') hp

theorem authHybridExtends_pqxdhAuthHybridKoskImpl1Key {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst)) :
    AuthHybridExtends P hst y.2 := by
  unfold pqxdhAuthHybridKoskImpl1Key at hy
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
  cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only at hy
    split_ifs at hy
    · exact authHybridExtends_pure_noneResp P hst hy
    · exact authHybridExtends_runAuthHybridSendKosk stage useRo P (.sendOPK u i) u bundle m0 m1 hst
        hy
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only at hy
    split_ifs at hy
    · exact authHybridExtends_pure_noneResp P hst hy
    · exact authHybridExtends_runAuthHybridSendKosk stage useRo P (.sendNoOPK u i) u bundle m0 m1
        hst hy
  | recvOPK k j o msg =>
    dsimp only at hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none =>
            rw [hFk] at hy; exact authHybridExtends_pure_noneResp P hst hy
          | some ke =>
            rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
            cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
            | none =>
              rw [hFb] at hy; exact authHybridExtends_pure_noneResp P hst hy
            | some kb =>
              rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
              cases hFo : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
                o.val)) with
              | none =>
                rw [hFo] at hy; exact authHybridExtends_pure_noneResp P hst hy
              | some oo =>
                rcases oo with ⟨_, oEntry⟩; rw [hFo] at hy; dsimp only at hy
                refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
                refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
                cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                    | none =>
                      rw [hDec] at hy; exact authHybridExtends_pure_noneResp P hst hy
                    | some ss =>
                      rw [hDec] at hy; dsimp only at hy
                      rw [StateT.run_bind, StateT.run_set, pure_bind] at hy
                      refine AuthHybridExtends.trans ?_
                        (authHybridExtends_bind_state_eq P _ hy
                          (state_eq_of_liftM _ _) (fun schedRes y hy => ?_))
                      · exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                          List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                          List.sublist_cons_self _ _⟩
                      · cases schedRes with
                      | none =>
                        exact authHybridExtends_pure_noneResp P _ hy
                      | some out =>
                        rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                        dsimp only at hy
                        cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                        | none =>
                          rw [hFS] at hy; dsimp only at hy
                          rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                            mem_support_pure_iff] at hy
                          rcases hy with ⟨_, rfl⟩
                          refine ⟨List.Sublist.refl _, List.Sublist.refl _, ?_,
                            List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                              List.Sublist.refl _⟩
                          dsimp only; rw [map_opk_opkPk_consume]
                        | some se =>
                          rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
                          split_ifs at hy <;>
                            (rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                              mem_support_pure_iff] at hy;
                             rcases hy with ⟨_, rfl⟩;
                             refine ⟨List.Sublist.refl _, List.Sublist.refl _, ?_,
                               List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                                 List.Sublist.refl _⟩;
                             dsimp only; rw [map_opk_opkPk_consume])
  | recvNoOPK k j l msg =>
    dsimp only at hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none =>
            rw [hFk] at hy; exact authHybridExtends_pure_noneResp P hst hy
          | some ke =>
            rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
            cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
            | none =>
              rw [hFb] at hy; exact authHybridExtends_pure_noneResp P hst hy
            | some kb =>
              rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
              refine authHybridExtends_if_noneResp P _ _ hst (fun hy => ?_) hy
              cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                | none =>
                  rw [hDec] at hy; exact authHybridExtends_pure_noneResp P hst hy
                | some ss =>
                  rw [hDec] at hy; dsimp only at hy
                  rw [StateT.run_bind, StateT.run_set, pure_bind] at hy
                  refine AuthHybridExtends.trans ?_
                    (authHybridExtends_bind_state_eq P _ hy
                      (state_eq_of_liftM _ _) (fun schedRes y hy => ?_))
                  · exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                      List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                      List.sublist_cons_self _ _⟩
                  · cases schedRes with
                  | none =>
                    exact authHybridExtends_pure_noneResp P _ hy
                  | some out =>
                    rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                    dsimp only at hy
                    cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                    | none =>
                      rw [hFS] at hy; dsimp only at hy
                      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                        mem_support_pure_iff] at hy
                      rcases hy with ⟨_, rfl⟩
                      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                          List.Sublist.refl _⟩
                    | some se =>
                      rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
                      split_ifs at hy <;>
                        (rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                          mem_support_pure_iff] at hy;
                         rcases hy with ⟨_, rfl⟩;
                         exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                           List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                             List.Sublist.refl _⟩)
  | initPrin u =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨sec0, _, secSign, _, _, rfl⟩
      exact ⟨List.sublist_cons_self _ _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | corruptIK u =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hp; dsimp only at hp
      rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    | some ue =>
      rcases ue with ⟨_, entry⟩; rw [hF] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩
      refine ⟨?_, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
      dsimp only; rw [map_prin_ikAPk_corrupt]
  | genSPK u j =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hF] at hp; dsimp only at hp
        rw [StateT.run_pure, mem_support_pure_iff] at hp
        rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
      | some ue =>
        rcases ue with ⟨_, uEntry⟩; rw [hF] at hp; dsimp only at hp
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
        rcases hp with ⟨spkSk, _, rSpk, _, ⟨pqPk, pqSk⟩, _, rPq, _, _, rfl⟩
        exact ⟨List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _,
          List.sublist_cons_self _ _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | genOPK u j o =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · simp only [StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨opkSk, _, _, rfl⟩
      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.sublist_cons_self _ _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | registerKey sk =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    cases hReg : registerAdvKey P hst.base.advKeys sk with
    | none =>
      rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    | some pa =>
      rcases pa with ⟨pk, advKeys'⟩; rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; dsimp only
      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | roQuery secrets =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; dsimp only
      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | roRootQuery rk dh =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; dsimp only
      exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | revealDhSecrets =>
    refine authHybridExtends_of_liftAuthBase P _ hst (fun p hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact AuthHybridExtends.refl P hst)

theorem isAuthG3Abort_mono_pqxdhAuthAdvStageImpl1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvCutoffState S)
    (hAb : isAuthG3Abort P s.hyb = true)
    (y : AuthResponse × AuthAdvCutoffState S)
    (hy : y ∈ support ((pqxdhAuthAdvStageImpl1Key stage S P q).run s)) :
    isAuthG3Abort P y.2.hyb = true := by
  have hyHyb : (y.1, y.2.hyb) ∈ support ((pqxdhAuthHybridKoskImpl1Key stage true true S P q).run
    s.hyb) := by
    cases q <;>
      (simp only [pqxdhAuthAdvStageImpl1Key, StateT.run_mk, support_bind, Set.mem_iUnion,
        mem_support_pure_iff] at hy;
       rcases hy with ⟨⟨resp, h'⟩, hh', rfl⟩;
       exact hh')
  exact isAuthG3Abort_mono_of_extends P (authHybridExtends_pqxdhAuthHybridKoskImpl1Key stage true true P
    q s.hyb hyHyb) hAb

end Proofs.SignalPqxdh.Security
