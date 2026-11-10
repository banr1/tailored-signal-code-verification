/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2b
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthGapDhHopC2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyCut_AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` Hybrid Run-Invariant Preservation

Proves that `pqxdhAuthHybridKoskImpl1Key` and `pqxdhAuthAdvStageImpl1Key` preserve
`ValidAuthHybridRunInv` across all one-key `Auth` queries.
-/

@[expose] public section
set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

private theorem map_prin_keys_corrupt (u : ℕ)
    (principals : List (Nat × PrincipalEntry)) :
    (principals.map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e))).map
        (fun (idx, e) => (idx, e.secIKA0, e.ikAPk)) =
    principals.map (fun (idx, e) => (idx, e.secIKA0, e.ikAPk)) := by
  rw [List.map_map]; congr 1; funext ⟨idx, e⟩
  dsimp only [Function.comp_apply]
  split_ifs <;> rfl
private theorem map_opk_keys_consume (key : Nat × Nat × Nat)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) :
    (opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e))).map
        (fun (idx, o) => (idx, o.opkSk, o.opkPk)) =
    opkEntries.map (fun (idx, o) => (idx, o.opkSk, o.opkPk)) := by
  rw [List.map_map]; congr 1; funext ⟨idx, e⟩
  dsimp only [Function.comp_apply]
  split_ifs <;> rfl

private theorem state_eq_of_liftM_c2b {σ α : Type} (mx : ProbComp α) (s : σ) :
    ∀ p ∈ support ((liftM mx : StateT σ ProbComp α).run s), p.2 = s := by
  intro p hp
  simp only [StateT.run_monadLift, monadLift_self, support_bind, Set.mem_iUnion,
    mem_support_pure_iff] at hp
  rcases hp with ⟨_, _, rfl⟩; rfl

private theorem prop_bind_state_eq_c2b {σ α β : Type} {Q : σ → Prop}
    {m1 : StateT σ ProbComp α} {f : α → StateT σ ProbComp β} (s : σ)
    {y : β × σ} (hy : y ∈ support ((m1 >>= f).run s))
    (h1 : ∀ p ∈ support (m1.run s), p.2 = s)
    (h2 : ∀ a, ∀ y ∈ support ((f a).run s), Q y.2) :
    Q y.2 := by
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hy; rcases hy with ⟨⟨a, s'⟩, hp, hy'⟩
  rw [h1 (a, s') hp] at hy'; exact h2 a y hy'
private theorem prop_pure_noneResp_c2b {S : Setup} {Q : AuthHybridState S → Prop}
    (hst : AuthHybridState S) (hRefl : Q hst) {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pure AuthResponse.noneResp : StateT (AuthHybridState S) ProbComp
      AuthResponse).run hst)) :
    Q y.2 := by
  rw [StateT.run_pure, mem_support_pure_iff] at hy; rcases hy with ⟨_, rfl⟩
  exact hRefl
private theorem prop_if_noneResp_c2b {S : Setup} {Q : AuthHybridState S → Prop}
    (c : Prop) [Decidable c]
    (m : StateT (AuthHybridState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (hRefl : Q hst) {y : AuthResponse × AuthHybridState S}
    (h : y ∈ support (m.run hst) → Q y.2)
    (hy : y ∈ support ((if c then pure AuthResponse.noneResp else m).run hst)) :
    Q y.2 := by
  split_ifs at hy
  · exact prop_pure_noneResp_c2b hst hRefl hy
  · exact h hy
private theorem prop_set_bind_c2b {σ α : Type} {Q : σ → Prop}
    (s1 s0 : σ) {f : PUnit → StateT σ ProbComp α} {y : α × σ}
    (hy : y ∈ support ((set s1 >>= f).run s0))
    (hk : y ∈ support ((f PUnit.unit).run s1) → Q y.2) :
    Q y.2 := by
  rw [StateT.run_bind, StateT.run_set, pure_bind] at hy; exact hk hy
private theorem prop_set_pure_c2b {σ α : Type} {Q : σ → Prop}
    (s1 s0 : σ) (a : α) {y : α × σ}
    (h1 : Q s1)
    (hy : y ∈ support ((set s1 >>= fun _ => pure a : StateT σ ProbComp α).run s0)) :
    Q y.2 := by
  rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hy
  rcases hy with ⟨_, rfl⟩; exact h1
private theorem prop_ite_set_pure_c2b {σ α : Type} {Q : σ → Prop}
    (c : Prop) [Decidable c] (s1 s2 s0 : σ) (a1 a2 : α) {y : α × σ}
    (h1 : c → Q s1) (h2 : ¬c → Q s2)
    (hy : y ∈ support ((if c then (set s1 >>= fun _ => pure a1)
                        else (set s2 >>= fun _ => pure a2) : StateT σ ProbComp α).run s0)) :
    Q y.2 := by
  split_ifs at hy with hc
  · exact prop_set_pure_c2b s1 s0 a1 (h1 hc) hy
  · exact prop_set_pure_c2b s2 s0 a2 (h2 hc) hy

private theorem prop_bind_state_eq_same_c2b {σ α β : Type} {Q : σ → Prop}
    {m1 : StateT σ ProbComp α} {f : α → StateT σ ProbComp β} (s : σ)
    {y : β × σ} (hy : y ∈ support ((m1 >>= f).run s))
    (h1 : ∀ p ∈ support (m1.run s), p.2 = s)
    (h2 : ∀ a, y ∈ support ((f a).run s) → Q y.2) :
    Q y.2 := by
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hy; rcases hy with ⟨⟨a, s'⟩, hp, hy'⟩
  rw [h1 (a, s') hp] at hy'; exact h2 a hy'

private theorem prop_of_liftAuthBase_c2b {S : Setup} {Q : AuthHybridState S → Prop}
    (m : StateT (AuthState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (h : ∀ p ∈ support (m.run hst.base), Q { hst with base := p.2 })
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((liftAuthBase m).run hst)) :
    Q y.2 := by
  unfold liftAuthBase at hy
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
    support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hp, _, rfl⟩; exact h (resp, base') hp

theorem authHybridTraceSub_pqxdhAuthHybridKoskImpl1Key {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst)) :
    AuthHybridTraceSub hst y.2 := by
  have hRefl := AuthHybridTraceSub.refl hst; unfold pqxdhAuthHybridKoskImpl1Key at hy
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hy; dsimp only at hy
  refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy; cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only at hy; refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    exact authHybridTraceSub_runAuthHybridSendKosk stage useRo P (.sendOPK u i) u bundle m0 m1 hst
      hy
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only at hy; refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    exact authHybridTraceSub_runAuthHybridSendKosk stage useRo P (.sendNoOPK u i) u bundle m0 m1 hst
      hy
  | recvOPK k j o msg =>
    dsimp only at hy; refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => rw [hFk] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
    | some ke =>
      rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
      cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => rw [hFb] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
      | some kb =>
        rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
        cases hFo : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => rw [hFo] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
        | some oo =>
          rcases oo with ⟨_, oEntry⟩; rw [hFo] at hy; dsimp only at hy
          refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
          refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
          cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => rw [hDec] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
          | some ss =>
            rw [hDec] at hy; dsimp only at hy; refine prop_set_bind_c2b _ hst hy (fun hy => ?_)
            refine prop_bind_state_eq_c2b _ hy (state_eq_of_liftM_c2b _ _) (fun schedRes y hy => ?_)
            cases schedRes with
            | none =>
              dsimp only at hy; refine prop_pure_noneResp_c2b _ ?_ hy
              exact ⟨AuthBaseTraceSub.refl _, List.Sublist.refl _, List.sublist_cons_self _ _,
                List.Sublist.refl _⟩
            | some out =>
              rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only at hy
              have hSubOpk :
                  (hst.base.opkEntries.map (fun (idx, o) => (idx, o.opkSk, o.opkPk))).Sublist
                    ((hst.base.opkEntries.map (fun (idx, e) =>
                      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else
                        (idx, e))).map
                        (fun (idx, o) => (idx, o.opkSk, o.opkPk))) := by
                rw [map_opk_keys_consume]
              cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
              | none =>
                rw [hFS] at hy; dsimp only at hy; refine prop_set_pure_c2b _ _ _ ?_ hy
                exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, hSubOpk, List.Sublist.refl _,
                  List.Sublist.refl _⟩,
                  List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
              | some se =>
                rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
                refine prop_ite_set_pure_c2b _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_) hy
                · exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, hSubOpk, List.Sublist.refl _,
                    List.Sublist.refl _⟩,
                    List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
                · exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, hSubOpk, List.Sublist.refl _,
                    List.Sublist.refl _⟩,
                    List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
  | recvNoOPK k j l msg =>
    dsimp only at hy; refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => rw [hFk] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
    | some ke =>
      rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
      cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => rw [hFb] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
      | some kb =>
        rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
        refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
        cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => rw [hDec] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
        | some ss =>
          rw [hDec] at hy; dsimp only at hy; refine prop_set_bind_c2b _ hst hy (fun hy => ?_)
          refine prop_bind_state_eq_c2b _ hy (state_eq_of_liftM_c2b _ _) (fun schedRes y hy => ?_)
          cases schedRes with
          | none =>
            dsimp only at hy; refine prop_pure_noneResp_c2b _ ?_ hy
            exact ⟨AuthBaseTraceSub.refl _, List.Sublist.refl _, List.sublist_cons_self _ _,
              List.Sublist.refl _⟩
          | some out =>
            rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only at hy
            cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
            | none =>
              rw [hFS] at hy; dsimp only at hy; refine prop_set_pure_c2b _ _ _ ?_ hy
              exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                List.Sublist.refl _, List.Sublist.refl _⟩,
                List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
            | some se =>
              rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
              refine prop_ite_set_pure_c2b _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_) hy
              · exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                  List.Sublist.refl _, List.Sublist.refl _⟩,
                  List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
              · exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                  List.Sublist.refl _, List.Sublist.refl _⟩,
                  List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
  | initPrin u =>
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hRefl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨sec0, _, secSign, _, _, rfl⟩
      exact ⟨⟨List.sublist_cons_self _ _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | corruptIK u =>
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hRefl
    | some ue =>
      rcases ue with ⟨_, entry⟩; rw [hF] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩
      refine ⟨⟨?_, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl
        _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
      dsimp only; rw [map_prin_keys_corrupt]
  | genSPK u j =>
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hRefl
    · cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
        rcases hp with ⟨_, rfl⟩; exact hRefl
      | some ue =>
        rcases ue with ⟨_, uEntry⟩; rw [hF] at hp; dsimp only at hp
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
        rcases hp with ⟨spkSk, _, rSpk, _, ⟨pqPk, pqSk⟩, _, rPq, _, _, rfl⟩
        exact ⟨⟨List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _,
          List.Sublist.refl _, List.Sublist.refl _⟩,
          List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | genOPK u j o =>
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hRefl
    · simp only [StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨opkSk, _, _, rfl⟩
      exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.sublist_cons_self _ _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | registerKey sk =>
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    cases hReg : registerAdvKey P hst.base.advKeys sk with
    | none =>
      rw [hReg] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hRefl
    | some pa =>
      rcases pa with ⟨pk, advKeys'⟩; rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; dsimp only
      have hSubAdv : hst.base.advKeys.Sublist advKeys' := by
        unfold registerAdvKey at hReg
        split_ifs at hReg
        injection hReg with hPair
        injection hPair with _ hAdvEq
        rw [← hAdvEq]; exact List.sublist_cons_self _ _
      exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        hSubAdv, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | roQuery secrets =>
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hRefl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩
      exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | roRootQuery rk dh =>
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hRefl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩
      exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  | revealDhSecrets =>
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl1KeyG at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact hRefl)

theorem validAuthKeyStoresFull_pqxdhAuthHybridKoskImpl1Key {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridState S) (hV : ValidAuthKeyStoresFull S P hst.base)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst)) :
    ValidAuthKeyStoresFull S P y.2.base := by
  rcases hV with ⟨⟨hVP, hVS, hVO, hPrins, hSpks, hOpks, hAdvs⟩, hVSess, hUsed⟩
  have hV : ValidAuthKeyStoresFull S P hst.base := ⟨⟨hVP, hVS, hVO, hPrins, hSpks, hOpks, hAdvs⟩,
    hVSess, hUsed⟩
  unfold pqxdhAuthHybridKoskImpl1Key at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
    hy => ?_) hy
  cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    exact validAuthKeyStoresFull_runAuthHybridSendKosk stage useRo P (.sendOPK u i) trivial u bundle
      m0 m1 hst hV hy
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    exact validAuthKeyStoresFull_runAuthHybridSendKosk stage useRo P (.sendNoOPK u i) trivial u
      bundle m0 m1 hst hV hy
  | recvOPK k j o msg =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none =>
      rw [hFk] at hy; exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base)
        hst hV hy
    | some ke =>
      rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
      cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none =>
        rw [hFb] at hy; exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P
          s.base) hst hV hy
      | some kb =>
        rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
        cases hFo : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none =>
          rw [hFo] at hy; exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P
            s.base) hst hV hy
        | some oo =>
          rcases oo with ⟨_, oEntry⟩; rw [hFo] at hy; dsimp only at hy
          refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV
            (fun hy => ?_) hy
          refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV
            (fun hy => ?_) hy
          cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none =>
            rw [hDec] at hy; exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P
              s.base) hst hV hy
          | some ss =>
            rw [hDec] at hy; dsimp only at hy
            refine prop_set_bind_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst hy (fun
              hy => ?_)
            refine prop_bind_state_eq_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hy
              (state_eq_of_liftM_c2b _ _) (fun schedRes y hy => ?_)
            cases schedRes with
            | none =>
              dsimp only at hy
              rw [StateT.run_pure, mem_support_pure_iff] at hy; rcases hy with ⟨_, rfl⟩; exact hV
            | some out =>
              rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only at hy
              have hVO' : ValidOpkEntries S (hst.base.opkEntries.map (fun (idx, e) =>
                  if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx,
                      e))) :=
                (validOpkEntries_map_consumed S P (k.val, j.val, o.val) hst.base.opkEntries hVO).1
              have hOpks' : ∀ kv ∈ hst.base.opkEntries.map (fun (idx, e) =>
                  if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx,
                    e)),
                  kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk := by
                intro kv hkv; rcases List.mem_map.mp hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
                have hO := hOpks (idx, e) heMem; dsimp only at hEq
                split_ifs at hEq <;> (subst hEq; exact hO)
              cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
              | none =>
                rw [hFS] at hy; dsimp only at hy
                refine prop_set_pure_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ _ ?_
                  hy
                exact ⟨⟨hVP, hVS, hVO', hPrins, hSpks, hOpks', hAdvs⟩, hVSess, hUsed⟩
              | some se =>
                rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
                refine prop_ite_set_pure_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ _
                  _ _ _ (fun _ => ?_) (fun _ => ?_) hy
                · exact ⟨⟨hVP, hVS, hVO', hPrins, hSpks, hOpks', hAdvs⟩, hVSess, hUsed⟩
                · exact ⟨⟨hVP, hVS, hVO', hPrins, hSpks, hOpks', hAdvs⟩, hVSess, hUsed⟩
  | recvNoOPK k j l msg =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none =>
      rw [hFk] at hy; exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base)
        hst hV hy
    | some ke =>
      rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
      cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none =>
        rw [hFb] at hy; exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P
          s.base) hst hV hy
      | some kb =>
        rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
        refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV
          (fun hy => ?_) hy
        cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none =>
          rw [hDec] at hy; exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P
            s.base) hst hV hy
        | some ss =>
          rw [hDec] at hy; dsimp only at hy
          refine prop_set_bind_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst hy (fun
            hy => ?_)
          refine prop_bind_state_eq_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hy
            (state_eq_of_liftM_c2b _ _) (fun schedRes y hy => ?_)
          cases schedRes with
          | none =>
            dsimp only at hy
            rw [StateT.run_pure, mem_support_pure_iff] at hy; rcases hy with ⟨_, rfl⟩; exact hV
          | some out =>
            rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only at hy
            cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
            | none =>
              rw [hFS] at hy; dsimp only at hy
              refine prop_set_pure_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ _ ?_ hy
              exact validAuthKeyStoresFull_of_fields_eq hV
            | some se =>
              rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
              refine prop_ite_set_pure_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ _ _
                _ _ (fun _ => ?_) (fun _ => ?_) hy
              · exact validAuthKeyStoresFull_of_fields_eq hV
              · exact validAuthKeyStoresFull_of_fields_eq hV
  | initPrin u =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst (fun p
      hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp; cases hFresh : hst.base.principals.any (fun (idx, _) => idx == u.val) with
    | true =>
      rw [hFresh] at hp; simp only [↓reduceIte] at hp
      rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact hV
    | false =>
      rw [hFresh] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨sec0, hSec0, secSign, _, _, rfl⟩
      have hLen0 : sec0.length = 32 := length_of_mem_support_sampleScalar32 hSec0
      refine ⟨⟨(validPrincipals_cons S u _ hst.base.principals hVP hFresh).1, hVS, hVO, ?_, ?_,
        hOpks, hAdvs⟩, hVSess, hUsed⟩
      · intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen0, rfl⟩
        · exact hPrins kv hMem
      · intro kv hkv
        rcases hSpks kv hkv with ⟨h1, h2, ⟨uE, huE⟩, h4⟩
        exact ⟨h1, h2, ⟨uE, List.mem_cons_of_mem _ huE⟩, h4⟩
  | corruptIK u =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst (fun p
      hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp; cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hV
    | some ue =>
      rcases ue with ⟨_, entry⟩; rw [hF] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩
      have hVP' := (validPrincipals_map_corrupted S P u.val hst.base.principals hVP).1
      refine ⟨⟨hVP', hVS, hVO, ?_, ?_, hOpks, hAdvs⟩, hVSess, hUsed⟩
      · intro kv hkv
        rcases List.mem_map.mp hkv with ⟨⟨idx, e⟩, heMem, hEq⟩; have hP0 := hPrins (idx, e) heMem
        dsimp only at hEq
        split_ifs at hEq <;> (subst hEq; exact hP0)
      · intro kv hkv
        rcases hSpks kv hkv with ⟨h1, h2, ⟨uE, huE⟩, h4⟩
        refine ⟨h1, h2, ⟨if kv.1.1 == u.val then { uE with corrupted := true } else uE, ?_⟩, h4⟩
        have hMap := List.mem_map_of_mem (f := fun ((idx, e) : Nat × PrincipalEntry) =>
          if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) huE
        dsimp only at hMap
        split_ifs at hMap ⊢ <;> exact hMap
  | genSPK u j =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst (fun p
      hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    cases hFresh : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) with
    | true =>
      rw [hFresh] at hp; simp only [↓reduceIte] at hp
      rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact hV
    | false =>
      rw [hFresh] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
      cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
        rcases hp with ⟨_, rfl⟩; exact hV
      | some ue =>
        rcases ue with ⟨u0, uEntry⟩; rw [hF] at hp; dsimp only at hp
        have hu0Mem : (u0, uEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hF
        have hu0Eq : u0 = u.val :=
          beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
        subst hu0Eq
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
        rcases hp with ⟨spkSk, hSpkSk, rSpk, _, ⟨pqPk, pqSk⟩, hPq, rPq, _, _, rfl⟩
        have hSpkLen : spkSk.length = 32 := length_of_mem_support_sampleScalar32 hSpkSk
        have hKemSeed : ∃ kpCoins, (P.kemKeyGen kpCoins).1 = pqPk ∧ (P.kemKeyGen kpCoins).2 =
            pqSk := by
          unfold sampleKemKeyGen at hPq
          simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hPq
          rcases hPq with ⟨seed, _, hEq⟩
          exact ⟨seed, congrArg Prod.fst hEq.symm, congrArg Prod.snd hEq.symm⟩
        refine ⟨⟨hVP, (validSpkBundles_cons S u j _ hst.base.spkBundles hVS hFresh).1, hVO, hPrins,
          ?_, hOpks, hAdvs⟩, hVSess, hUsed⟩
        intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hSpkLen, rfl, ⟨uEntry, hu0Mem⟩, hKemSeed⟩
        · exact hSpks kv hMem
  | genOPK u j o =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst (fun p
      hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    cases hFresh : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) with
    | true =>
      rw [hFresh] at hp; simp only [↓reduceIte] at hp
      rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact hV
    | false =>
      rw [hFresh] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
      simp only [StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨opkSk, hOpkSk, _, rfl⟩
      have hOpkLen : opkSk.length = 32 := length_of_mem_support_sampleScalar32 hOpkSk
      refine ⟨⟨hVP, hVS, (validOpkEntries_cons S u j o _ hst.base.opkEntries hVO hFresh).1, hPrins,
        hSpks, ?_, hAdvs⟩, hVSess, hUsed⟩
      intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
      · exact ⟨hOpkLen, rfl⟩
      · exact hOpks kv hMem
  | registerKey sk =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst (fun p
      hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp; cases hReg : registerAdvKey P hst.base.advKeys sk with
    | none =>
      rw [hReg] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hV
    | some pa =>
      rcases pa with ⟨pk, advKeys'⟩; rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; unfold registerAdvKey at hReg
      cases hLenNe : (sk.length != 32) with
      | true => rw [hLenNe] at hReg; nomatch hReg
      | false =>
        rw [hLenNe] at hReg; simp only [Bool.false_eq_true, ↓reduceIte] at hReg
        have hLenEq : sk.length = 32 := by revert hLenNe; simp
        injection hReg with hPair
        injection hPair with hPk hAdv'
        subst hPk; subst hAdv'; refine ⟨⟨hVP, hVS, hVO, hPrins, hSpks, hOpks, ?_⟩, hVSess, hUsed⟩
        intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLenEq, rfl⟩
        · exact hAdvs kv hMem
  | roQuery secrets =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst (fun p
      hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hV
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; exact validAuthKeyStoresFull_of_fields_eq hV
  | roRootQuery rk dh =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst (fun p
      hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact hV
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; exact validAuthKeyStoresFull_of_fields_eq hV
  | revealDhSecrets =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst (fun p
      hp => ?_) hy
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact hV)

theorem validAllIdealAuthSessions_pqxdhAuthHybridKoskImpl1Key {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridState S) (hKS : ValidAuthKeyStores S P hst.base)
    (hV : ValidAllIdealAuthSessions S P hst)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst)) :
    ValidAllIdealAuthSessions S P y.2 := by
  have hSub := authHybridTraceSub_pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth P q hst hy
  unfold pqxdhAuthHybridKoskImpl1Key at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine prop_if_noneResp_c2b (Q := ValidAllIdealAuthSessions S P) _ _ hst hV (fun hy => ?_) hy
  cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := ValidAllIdealAuthSessions S P) _ _ hst hV (fun hy => ?_) hy
    exact validAllIdealAuthSessions_runAuthHybridSendKosk stage useRo P (.sendOPK u i) u rfl bundle
      m0 m1 hst hKS hV hy
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := ValidAllIdealAuthSessions S P) _ _ hst hV (fun hy => ?_) hy
    exact validAllIdealAuthSessions_runAuthHybridSendKosk stage useRo P (.sendNoOPK u i) u rfl
      bundle m0 m1 hst hKS hV hy
  | recvOPK k j o msg =>
    refine validAllIdealAuthSessions_of_traceSub P hSub ?_ hV; dsimp only at hy
    refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst rfl (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst rfl (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst rfl (fun
      hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none =>
      rw [hFk] at hy; exact prop_pure_noneResp_c2b (Q := fun s => s.idealSessions =
        hst.idealSessions) hst rfl hy
    | some ke =>
      rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
      cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none =>
        rw [hFb] at hy; exact prop_pure_noneResp_c2b (Q := fun s => s.idealSessions =
          hst.idealSessions) hst rfl hy
      | some kb =>
        rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
        cases hFo : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none =>
          rw [hFo] at hy; exact prop_pure_noneResp_c2b (Q := fun s => s.idealSessions =
            hst.idealSessions) hst rfl hy
        | some oo =>
          rcases oo with ⟨_, oEntry⟩; rw [hFo] at hy; dsimp only at hy
          refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst
            rfl (fun hy => ?_) hy
          refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst
            rfl (fun hy => ?_) hy
          cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none =>
            rw [hDec] at hy; exact prop_pure_noneResp_c2b (Q := fun s => s.idealSessions =
              hst.idealSessions) hst rfl hy
          | some ss =>
            rw [hDec] at hy; dsimp only at hy
            refine prop_set_bind_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ hst hy
              (fun hy => ?_)
            refine prop_bind_state_eq_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ hy
              (state_eq_of_liftM_c2b _ _) (fun schedRes y hy => ?_)
            cases schedRes with
            | none =>
              dsimp only at hy; rw [StateT.run_pure, mem_support_pure_iff] at hy; rcases hy with ⟨_,
                rfl⟩; rfl
            | some out =>
              rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only at hy
              cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
              | none =>
                rw [hFS] at hy; dsimp only at hy
                exact prop_set_pure_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ _
                  rfl hy
              | some se =>
                rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
                exact prop_ite_set_pure_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _
                  _ _ _ _ (fun _ => rfl) (fun _ => rfl) hy
  | recvNoOPK k j l msg =>
    refine validAllIdealAuthSessions_of_traceSub P hSub ?_ hV; dsimp only at hy
    refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst rfl (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst rfl (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst rfl (fun
      hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none =>
      rw [hFk] at hy; exact prop_pure_noneResp_c2b (Q := fun s => s.idealSessions =
        hst.idealSessions) hst rfl hy
    | some ke =>
      rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
      cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none =>
        rw [hFb] at hy; exact prop_pure_noneResp_c2b (Q := fun s => s.idealSessions =
          hst.idealSessions) hst rfl hy
      | some kb =>
        rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
        refine prop_if_noneResp_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ hst rfl
          (fun hy => ?_) hy
        cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none =>
          rw [hDec] at hy; exact prop_pure_noneResp_c2b (Q := fun s => s.idealSessions =
            hst.idealSessions) hst rfl hy
        | some ss =>
          rw [hDec] at hy; dsimp only at hy
          refine prop_set_bind_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ hst hy (fun
            hy => ?_)
          refine prop_bind_state_eq_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ hy
            (state_eq_of_liftM_c2b _ _) (fun schedRes y hy => ?_)
          cases schedRes with
          | none =>
            dsimp only at hy; rw [StateT.run_pure, mem_support_pure_iff] at hy; rcases hy with ⟨_,
              rfl⟩; rfl
          | some out =>
            rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only at hy
            cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
            | none =>
              rw [hFS] at hy; dsimp only at hy
              exact prop_set_pure_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ _ rfl
                hy
            | some se =>
              rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
              exact prop_ite_set_pure_c2b (Q := fun s => s.idealSessions = hst.idealSessions) _ _ _
                _ _ _ (fun _ => rfl) (fun _ => rfl) hy
  | initPrin u =>
    exact validAllIdealAuthSessions_of_traceSub P hSub (prop_of_liftAuthBase_c2b (Q := fun s =>
      s.idealSessions = hst.idealSessions) _ hst (fun _ _ => rfl) hy) hV
  | corruptIK u =>
    exact validAllIdealAuthSessions_of_traceSub P hSub (prop_of_liftAuthBase_c2b (Q := fun s =>
      s.idealSessions = hst.idealSessions) _ hst (fun _ _ => rfl) hy) hV
  | genSPK u j =>
    exact validAllIdealAuthSessions_of_traceSub P hSub (prop_of_liftAuthBase_c2b (Q := fun s =>
      s.idealSessions = hst.idealSessions) _ hst (fun _ _ => rfl) hy) hV
  | genOPK u j o =>
    exact validAllIdealAuthSessions_of_traceSub P hSub (prop_of_liftAuthBase_c2b (Q := fun s =>
      s.idealSessions = hst.idealSessions) _ hst (fun _ _ => rfl) hy) hV
  | registerKey sk =>
    exact validAllIdealAuthSessions_of_traceSub P hSub (prop_of_liftAuthBase_c2b (Q := fun s =>
      s.idealSessions = hst.idealSessions) _ hst (fun _ _ => rfl) hy) hV
  | roQuery secrets =>
    exact validAllIdealAuthSessions_of_traceSub P hSub (prop_of_liftAuthBase_c2b (Q := fun s =>
      s.idealSessions = hst.idealSessions) _ hst (fun _ _ => rfl) hy) hV
  | roRootQuery rk dh =>
    exact validAllIdealAuthSessions_of_traceSub P hSub (prop_of_liftAuthBase_c2b (Q := fun s =>
      s.idealSessions = hst.idealSessions) _ hst (fun _ _ => rfl) hy) hV
  | revealDhSecrets =>
    exact validAllIdealAuthSessions_of_traceSub P hSub (prop_of_liftAuthBase_c2b (Q := fun s =>
      s.idealSessions = hst.idealSessions) _ hst (fun _ _ => rfl) hy) hV

theorem validSentEvents_pqxdhAuthHybridKoskImpl1Key {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridState S) (hV : ValidSentEvents S P hst)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst)) :
    ValidSentEvents S P y.2 := by
  have hSub := authHybridTraceSub_pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth P q hst hy
  unfold pqxdhAuthHybridKoskImpl1Key at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy; cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    exact validSentEvents_runAuthHybridSendKosk stage useRo P (.sendOPK u i) u rfl bundle m0 m1 hst
      hV hy
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    exact validSentEvents_runAuthHybridSendKosk stage useRo P (.sendNoOPK u i) u rfl bundle m0 m1
      hst hV hy
  | recvOPK k j o msg =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => rw [hFk] at hy; exact prop_pure_noneResp_c2b (Q := ValidSentEvents S P) hst hV hy
    | some ke =>
      rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
      cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => rw [hFb] at hy; exact prop_pure_noneResp_c2b (Q := ValidSentEvents S P) hst hV hy
      | some kb =>
        rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
        cases hFo : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => rw [hFo] at hy; exact prop_pure_noneResp_c2b (Q := ValidSentEvents S P) hst hV hy
        | some oo =>
          rcases oo with ⟨_, oEntry⟩; rw [hFo] at hy; dsimp only at hy
          refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
          refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
          cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none =>
            rw [hDec] at hy; exact prop_pure_noneResp_c2b (Q := ValidSentEvents S P) hst hV hy
          | some ss =>
            rw [hDec] at hy; dsimp only at hy
            refine prop_set_bind_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst hy (fun
              hy => ?_) rfl
            refine prop_bind_state_eq_same_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _
              hy
              (state_eq_of_liftM_c2b _ _) (fun schedRes hy => ?_)
            cases schedRes with
            | none =>
              dsimp only at hy; rw [StateT.run_pure, mem_support_pure_iff] at hy
              rcases hy with ⟨_, rfl⟩; intro hEq
              exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
            | some out =>
              rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only at hy
              cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
              | none =>
                rw [hFS] at hy; dsimp only at hy
                refine prop_set_pure_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ _ _
                  (fun hEq => ?_) hy
                exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
              | some se =>
                rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
                refine prop_ite_set_pure_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ _ _
                  _ _ _
                  (fun _ hEq => ?_) (fun _ hEq => ?_) hy
                · refine ⟨fun s' hs' => ?_, fun s' hs' => ?_⟩
                  · rw [← hEq] at hs'; dsimp only at hs'
                    rcases mem_consumeMatchingSentOPK_snd P _ hst.base.sentOPKEvents hs' with ⟨s0,
                      hs0, rfl | rfl⟩
                    · exact validSentOPKEvent_of_traceSub P hSub (hV.1 s' hs0)
                    · exact validSentOPKEvent_with_matched P y.2 true (validSentOPKEvent_of_traceSub
                        P hSub (hV.1 s0 hs0))
                  · rw [← hEq] at hs'; dsimp only at hs'
                    exact validSentNoOPKEvent_of_traceSub P hSub (hV.2 s' hs')
                · exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | recvNoOPK k j l msg =>
    dsimp only at hy
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    cases hFk : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => rw [hFk] at hy; exact prop_pure_noneResp_c2b (Q := ValidSentEvents S P) hst hV hy
    | some ke =>
      rcases ke with ⟨_, kEntry⟩; rw [hFk] at hy; dsimp only at hy
      cases hFb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => rw [hFb] at hy; exact prop_pure_noneResp_c2b (Q := ValidSentEvents S P) hst hV hy
      | some kb =>
        rcases kb with ⟨_, bEntry⟩; rw [hFb] at hy; dsimp only at hy
        refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
        cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => rw [hDec] at hy; exact prop_pure_noneResp_c2b (Q := ValidSentEvents S P) hst hV hy
        | some ss =>
          rw [hDec] at hy; dsimp only at hy
          refine prop_set_bind_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst hy (fun
            hy => ?_) rfl
          refine prop_bind_state_eq_same_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hy
            (state_eq_of_liftM_c2b _ _) (fun schedRes hy => ?_)
          cases schedRes with
          | none =>
            dsimp only at hy; rw [StateT.run_pure, mem_support_pure_iff] at hy
            rcases hy with ⟨_, rfl⟩; intro hEq
            exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
          | some out =>
            rcases out with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only at hy
            cases hFS : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
            | none =>
              rw [hFS] at hy; dsimp only at hy
              refine prop_set_pure_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ _ _ (fun
                hEq => ?_) hy
              exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
            | some se =>
              rcases se with ⟨_, senderEntry⟩; rw [hFS] at hy; dsimp only at hy
              refine prop_ite_set_pure_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ _ _ _
                _ _
                (fun _ hEq => ?_) (fun _ hEq => ?_) hy
              · refine ⟨fun s' hs' => ?_, fun s' hs' => ?_⟩
                · rw [← hEq] at hs'; dsimp only at hs'
                  exact validSentOPKEvent_of_traceSub P hSub (hV.1 s' hs')
                · rw [← hEq] at hs'; dsimp only at hs'
                  rcases mem_consumeMatchingSentNoOPK_snd P _ hst.base.sentNoOPKEvents hs' with ⟨s0,
                    hs0, rfl | rfl⟩
                  · exact validSentNoOPKEvent_of_traceSub P hSub (hV.2 s' hs0)
                  · exact validSentNoOPKEvent_with_matched P y.2 true
                      (validSentNoOPKEvent_of_traceSub P hSub (hV.2 s0 hs0))
              · exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | initPrin u =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst (fun p
      hp hEq => ?_) hy rfl
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure,
        bind_assoc, pure_bind, support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨_, _, _, _, _, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | corruptIK u =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst (fun p
      hp hEq => ?_) hy rfl
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp
        with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
    | some ue =>
      rcases ue with ⟨_, _⟩; rw [hF] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp;
        rcases hp with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | genSPK u j =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst (fun p
      hp hEq => ?_) hy rfl
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
    · cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp
          with ⟨_, rfl⟩
        exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
      | some ue =>
        rcases ue with ⟨_, _⟩; rw [hF] at hp; dsimp only at hp
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure,
          bind_assoc, pure_bind, support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
        rcases hp with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, _, rfl⟩
        exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | genOPK u j o =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst (fun p
      hp hEq => ?_) hy rfl
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure,
        bind_assoc, pure_bind, support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨_, _, _, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | registerKey sk =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst (fun p
      hp hEq => ?_) hy rfl
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    cases hReg : registerAdvKey P hst.base.advKeys sk with
    | none =>
      rw [hReg] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp
        with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
    | some pa =>
      rcases pa with ⟨_, _⟩; rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp;
        rcases hp with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | roQuery secrets =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst (fun p
      hp hEq => ?_) hy rfl
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure,
        bind_assoc, pure_bind, support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | roRootQuery rk dh =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst (fun p
      hp hEq => ?_) hy rfl
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure,
        bind_assoc, pure_bind, support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩
      exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV
  | revealDhSecrets =>
    refine prop_of_liftAuthBase_c2b (Q := fun s => s = y.2 → ValidSentEvents S P y.2) _ hst (fun p
      hp hEq => ?_) hy rfl
    unfold pqxdhAuthImpl1KeyG at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩;
       exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV)

theorem validAuthHybridRunInv_pqxdhAuthHybridKoskImpl1Key {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridState S) (hInv : ValidAuthHybridRunInv S P hst)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth S P q).run hst)) :
    ValidAuthHybridRunInv S P y.2 :=
  ⟨validAuthKeyStoresFull_pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth P q hst hInv.1 hy,
   validAllIdealAuthSessions_pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth P q hst hInv.1.1 hInv.2.1
     hy,
   validSentEvents_pqxdhAuthHybridKoskImpl1Key stage useRo checkAuth P q hst hInv.2.2 hy⟩
theorem validAuthHybridRunInv_pqxdhAuthAdvStageImpl1Key {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvCutoffState S)
    (hInv : ValidAuthHybridRunInv S P s.hyb)
    {y : AuthResponse × AuthAdvCutoffState S}
    (hy : y ∈ support ((pqxdhAuthAdvStageImpl1Key stage S P q).run s)) :
    ValidAuthHybridRunInv S P y.2.hyb := by
  cases q <;> {
    simp only [pqxdhAuthAdvStageImpl1Key, StateT.run_mk, support_bind, Set.mem_iUnion,
      mem_support_pure_iff] at hy
    rcases hy with ⟨⟨resp, hyb'⟩, hHyb, rfl⟩
    exact validAuthHybridRunInv_pqxdhAuthHybridKoskImpl1Key stage true true P _ s.hyb hInv hHyb
  }
end Proofs.SignalPqxdh.Security
