/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC2
import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` hop `G3 → G3.5`: trace monotonicity and hybrid run invariant

Establishes trace-sublist monotonicity (`AuthHybridTraceSub`) and the inductive run invariant
`ValidAuthHybridRunInv` across `pqxdhAuthHybridKoskImpl` and `pqxdhAuthAdvStageImpl`.
-/

@[expose] public section
set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

/-! ## Trace monotonicity -/

/-- Trace-sublist monotonicity relation on `AuthState S` along `pqxdhAuthHybridKoskImpl`. -/
structure AuthBaseTraceSub {S : Setup} (st1 st2 : AuthState S) : Prop where
  prin_keys_sub :
    (st1.principals.map (fun (idx, e) => (idx, e.secIKA0, e.ikAPk))).Sublist
      (st2.principals.map (fun (idx, e) => (idx, e.secIKA0, e.ikAPk)))
  spkBundles_sub : st1.spkBundles.Sublist st2.spkBundles
  opk_keys_sub :
    (st1.opkEntries.map (fun (idx, o) => (idx, o.opkSk, o.opkPk))).Sublist
      (st2.opkEntries.map (fun (idx, o) => (idx, o.opkSk, o.opkPk)))
  advKeys_sub : st1.advKeys.Sublist st2.advKeys
  sessions_sub : st1.sessions.Sublist st2.sessions
theorem AuthBaseTraceSub.refl {S : Setup} (st : AuthState S) :
    AuthBaseTraceSub st st :=
  ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
   List.Sublist.refl _, List.Sublist.refl _⟩
theorem AuthBaseTraceSub.trans {S : Setup} {st1 st2 st3 : AuthState S}
    (h12 : AuthBaseTraceSub st1 st2) (h23 : AuthBaseTraceSub st2 st3) :
    AuthBaseTraceSub st1 st3 :=
  ⟨h12.prin_keys_sub.trans h23.prin_keys_sub,
   h12.spkBundles_sub.trans h23.spkBundles_sub,
   h12.opk_keys_sub.trans h23.opk_keys_sub,
   h12.advKeys_sub.trans h23.advKeys_sub,
   h12.sessions_sub.trans h23.sessions_sub⟩
theorem AuthBaseTraceSub.subPrin {S : Setup} {st1 st2 : AuthState S}
    (hSub : AuthBaseTraceSub st1 st2) :
    ∀ x ∈ st1.principals,
      (x.1, x.2.ikAPk) ∈ st2.principals.map (fun (idx, e) => (idx, e.ikAPk)) := by
  intro ⟨u, e1⟩ hMem1
  have hMap1 : (u, e1.secIKA0, e1.ikAPk) ∈
      st1.principals.map (fun (idx, e) => (idx, e.secIKA0, e.ikAPk)) :=
    List.mem_map_of_mem hMem1
  have hMap2 := hSub.prin_keys_sub.subset hMap1
  rcases List.mem_map.mp hMap2 with ⟨⟨u2, e2⟩, hMem2, hEq⟩
  injection hEq with hu hRest
  injection hRest with _ hIk
  subst hu; rw [← hIk]
  exact List.mem_map_of_mem hMem2
theorem AuthBaseTraceSub.exists_prin {S : Setup} {st1 st2 : AuthState S}
    (hSub : AuthBaseTraceSub st1 st2) {u : Nat} {e1 : PrincipalEntry}
    (hMem1 : (u, e1) ∈ st1.principals) :
    ∃ e2 : PrincipalEntry,
      (u, e2) ∈ st2.principals ∧ e2.secIKA0 = e1.secIKA0 ∧ e2.ikAPk = e1.ikAPk := by
  have hMap1 : (u, e1.secIKA0, e1.ikAPk) ∈
      st1.principals.map (fun (idx, e) => (idx, e.secIKA0, e.ikAPk)) :=
    List.mem_map_of_mem hMem1
  have hMap2 := hSub.prin_keys_sub.subset hMap1
  rcases List.mem_map.mp hMap2 with ⟨⟨u2, e2⟩, hMem2, hEq⟩
  injection hEq with hu hRest
  injection hRest with hSec hIk
  subst hu; exact ⟨e2, hMem2, hSec, hIk⟩
theorem AuthBaseTraceSub.subSpk {S : Setup} (P : Primitives) {st1 st2 : AuthState S}
    (hSub : AuthBaseTraceSub st1 st2) :
    ∀ x ∈ st1.spkBundles,
      (x.1, P.pow8 x.2.spkPk) ∈ st2.spkBundles.map (fun (idx, b) => (idx, P.pow8 b.spkPk)) := by
  intro ⟨idx, b⟩ hMem1; exact List.mem_map_of_mem (hSub.spkBundles_sub.subset hMem1)
theorem AuthBaseTraceSub.subAdv {S : Setup} {st1 st2 : AuthState S}
    (hSub : AuthBaseTraceSub st1 st2) :
    ∀ x ∈ st1.advKeys, x ∈ st2.advKeys :=
  fun _ hx => hSub.advKeys_sub.subset hx
structure AuthHybridTraceSub {S : Setup} (hst1 hst2 : AuthHybridState S) : Prop where
  base_sub          : AuthBaseTraceSub hst1.base hst2.base
  initRecs_sub      : hst1.initKemRecs.Sublist hst2.initKemRecs
  recvRecs_sub      : hst1.recvKemRecs.Sublist hst2.recvKemRecs
  idealSessions_sub : hst1.idealSessions.Sublist hst2.idealSessions
theorem AuthHybridTraceSub.refl {S : Setup} (hst : AuthHybridState S) :
    AuthHybridTraceSub hst hst :=
  ⟨AuthBaseTraceSub.refl hst.base, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
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
private theorem sublist_ite_cons_self_c2b {α : Type} (c : Prop) [Decidable c] (a : α) (l : List α) :
    l.Sublist (if c then a :: l else l) := by
  split_ifs
  · exact List.sublist_cons_self a l
  · exact List.Sublist.refl l
private theorem state_eq_of_liftM_c2b {σ α : Type} (mx : ProbComp α) (s : σ) :
    ∀ p ∈ support ((liftM mx : StateT σ ProbComp α).run s), p.2 = s := by
  intro p hp
  simp only [StateT.run_monadLift, monadLift_self, support_bind, Set.mem_iUnion,
    mem_support_pure_iff] at hp
  rcases hp with ⟨_, _, rfl⟩; rfl
private theorem state_eq_of_pure_c2b {σ α : Type} (a : α) (s : σ) :
    ∀ p ∈ support ((pure a : StateT σ ProbComp α).run s), p.2 = s := by
  intro p hp; simp only [StateT.run_pure, mem_support_pure_iff] at hp
  rcases hp with ⟨_, rfl⟩; rfl
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
private theorem prop_set_ite_pure_c2b {σ α : Type} {Q : σ → Prop}
    (s1 s0 : σ) (c : Prop) [Decidable c] (a1 a2 : α) {y : α × σ}
    (h1 : Q s1)
    (hy : y ∈ support ((set s1 >>= fun _ => if c then pure a1 else pure a2 : StateT σ ProbComp
      α).run s0)) :
    Q y.2 := by
  rw [StateT.run_bind, StateT.run_set, pure_bind] at hy
  split_ifs at hy <;>
    (rw [StateT.run_pure, mem_support_pure_iff] at hy; rcases hy with ⟨_, rfl⟩; exact h1)
private theorem eq_of_set_ite_pure_c2b {σ α : Type}
    (s1 s0 : σ) (c : Prop) [Decidable c] (a1 a2 : α) {y : α × σ}
    (hy : y ∈ support ((set s1 >>= fun _ => if c then pure a1 else pure a2 : StateT σ ProbComp
      α).run s0)) :
    y.2 = s1 :=
  prop_set_ite_pure_c2b (Q := fun s => s = s1) s1 s0 c a1 a2 rfl hy
private theorem prop_bind_state_eq_same_c2b {σ α β : Type} {Q : σ → Prop}
    {m1 : StateT σ ProbComp α} {f : α → StateT σ ProbComp β} (s : σ)
    {y : β × σ} (hy : y ∈ support ((m1 >>= f).run s))
    (h1 : ∀ p ∈ support (m1.run s), p.2 = s)
    (h2 : ∀ a, y ∈ support ((f a).run s) → Q y.2) :
    Q y.2 := by
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hy; rcases hy with ⟨⟨a, s'⟩, hp, hy'⟩
  rw [h1 (a, s') hp] at hy'; exact h2 a hy'
private theorem prop_ite_bind1_c2b {S : Setup} {α β : Type} {Q : AuthHybridState S → Prop}
    {c : Prop} [Decidable c]
    {d1 : ProbComp α} {g : α → β} {d2 : ProbComp β}
    {f : β → StateT (AuthHybridState S) ProbComp AuthResponse}
    (hst : AuthHybridState S) {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((if c then (do let dk ← liftM d1; let x ← pure (g dk); f x)
                        else (do let x ← liftM d2; f x)).run hst))
    (hk : ∀ x, ∀ y ∈ support ((f x).run hst), Q y.2) :
    Q y.2 := by
  split_ifs at hy
  · refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun dk y hy => ?_)
    exact prop_bind_state_eq_c2b hst hy (state_eq_of_pure_c2b _ hst) (fun x y hy => hk x y hy)
  · exact prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun x y hy => hk x y hy)
private theorem prop_ite_bind2_c2b {S : Setup} {α1 α2 β : Type} {Q : AuthHybridState S → Prop}
    {c : Prop} [Decidable c]
    {d1 : ProbComp α1} {d2 : ProbComp α2} {g : α1 → α2 → β} {d3 : ProbComp β}
    {f : β → StateT (AuthHybridState S) ProbComp AuthResponse}
    (hst : AuthHybridState S) {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((if c then
      (do let r ← liftM d1; let c' ← liftM d2; let x ← pure (g r c'); f x)
                        else (do let x ← liftM d3; f x)).run hst))
    (hk : ∀ x, ∀ y ∈ support ((f x).run hst), Q y.2) :
    Q y.2 := by
  split_ifs at hy
  · refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun r y hy => ?_)
    refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun c' y hy => ?_)
    exact prop_bind_state_eq_c2b hst hy (state_eq_of_pure_c2b _ hst) (fun x y hy => hk x y hy)
  · exact prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun x y hy => hk x y hy)
private theorem prop_ite_bind3_c2b {S : Setup} {α1 α2 β : Type} {Q : AuthHybridState S → Prop}
    {c : Prop} [Decidable c]
    {d1 : ProbComp α1} {d2 : ProbComp α2} {g : α1 → α2 → β} {v : β}
    {f : β → StateT (AuthHybridState S) ProbComp AuthResponse}
    (hst : AuthHybridState S) {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((if c then
      (do let ms ← liftM d1; let cn ← liftM d2; let x ← pure (g ms cn); f x)
                        else (do let x ← pure v; f x)).run hst))
    (hk : ∀ x, ∀ y ∈ support ((f x).run hst), Q y.2) :
    Q y.2 := by
  split_ifs at hy
  · refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun ms y hy => ?_)
    refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun cn y hy => ?_)
    exact prop_bind_state_eq_c2b hst hy (state_eq_of_pure_c2b _ hst) (fun x y hy => hk x y hy)
  · exact prop_bind_state_eq_c2b hst hy (state_eq_of_pure_c2b _ hst) (fun x y hy => hk x y hy)
private theorem prop_ite_bind4_c2b {S : Setup} {α β : Type} {Q : AuthHybridState S → Prop}
    {c : Prop} [Decidable c]
    {d1 : ProbComp α} {v : α}
    {f : α → StateT (AuthHybridState S) ProbComp β}
    (hst : AuthHybridState S) {y : β × AuthHybridState S}
    (hy : y ∈ support ((if c then (do let x ← liftM d1; f x)
                        else (do let x ← pure v; f x)).run hst))
    (hk : ∀ x, ∀ y ∈ support ((f x).run hst), Q y.2) :
    Q y.2 := by
  split_ifs at hy
  · exact prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun x y hy => hk x y hy)
  · exact prop_bind_state_eq_c2b hst hy (state_eq_of_pure_c2b _ hst) (fun x y hy => hk x y hy)
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
private theorem prop_bind_liftM_mem_c2b {σ α β : Type} {Q : σ → Prop}
    {d : ProbComp α} {f : α → StateT σ ProbComp β} (s : σ)
    {y : β × σ} (hy : y ∈ support ((liftM d >>= f).run s))
    (hk : ∀ a ∈ support d, ∀ y ∈ support ((f a).run s), Q y.2) :
    Q y.2 := by
  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
    support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy
  rcases hy with ⟨⟨a, s'⟩, ⟨a', ha', hEq⟩, hy'⟩
  injection hEq with h1 h2; subst h1; subst h2
  exact hk a ha' y hy'
theorem authHybridTraceSub_runAuthHybridSendKosk {S : Setup} (stage : AuthHybridStage)
    (useRo : Bool) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridState S)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((runAuthHybridSendKosk stage useRo S P sid u bundle m0 m1).run hst)) :
    AuthHybridTraceSub hst y.2 := by
  have hRefl := AuthHybridTraceSub.refl hst; unfold runAuthHybridSendKosk at hy
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hy; dsimp only at hy
  refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
  refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    rw [hF] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
  | some ue =>
    rcases ue with ⟨_, uEntry⟩; rw [hF] at hy; dsimp only at hy
    refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun ekASk y hy => ?_)
    refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun kemCoins y hy => ?_)
    refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun ephASk y hy => ?_)
    refine prop_bind_state_eq_c2b hst hy (state_eq_of_liftM_c2b _ hst) (fun spqrCoins y hy => ?_)
    refine prop_if_noneResp_c2b _ _ hst hRefl (fun hy => ?_) hy
    cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
    | none =>
      rw [hKem] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
    | some ssCt =>
      rcases ssCt with ⟨ss, kemCt⟩; rw [hKem] at hy; dsimp only at hy
      refine prop_ite_bind1_c2b hst hy (fun drRo y hy => ?_); rcases drRo with ⟨drKey, roCache'⟩
      refine prop_ite_bind2_c2b hst hy (fun rkRo y hy => ?_)
      rcases rkRo with ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      refine prop_ite_bind3_c2b hst hy (fun mkCk y hy => ?_); rcases mkCk with ⟨mkSeed, ck1_1⟩
      cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
      | none =>
        rw [hSpqr] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
      | some spqrOut =>
        rcases spqrOut with ⟨_, spqrSalt?, pqRatchetMsg⟩; rw [hSpqr] at hy; dsimp only at hy
        refine prop_ite_bind4_c2b hst hy (fun deriveMessageKeys y hy => ?_)
        refine prop_set_ite_pure_c2b _ hst _ _ _ ?_ hy
        exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
          List.Sublist.refl _, List.sublist_cons_self _ _⟩,
          List.sublist_cons_self _ _, List.Sublist.refl _,
          sublist_ite_cons_self_c2b _ _ _⟩
theorem authHybridTraceSub_pqxdhAuthHybridKoskImpl {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S) (hst : AuthHybridState S)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst)) :
    AuthHybridTraceSub hst y.2 := by
  have hRefl := AuthHybridTraceSub.refl hst; unfold pqxdhAuthHybridKoskImpl at hy
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
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl at hp
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
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl at hp
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
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl at hp
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
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl at hp
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
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl at hp
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
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl at hp
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
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl at hp
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
    refine prop_of_liftAuthBase_c2b _ hst (fun p hp => ?_) hy; unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact hRefl)
/-! ## Key-store invariant -/
private theorem prop_if_noneResp_false_c2b {S : Setup} {Q : AuthHybridState S → Prop}
    (c : Bool)
    (m : StateT (AuthHybridState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (hRefl : Q hst) {y : AuthResponse × AuthHybridState S}
    (h : c = false → y ∈ support (m.run hst) → Q y.2)
    (hy : y ∈ support ((if c then pure AuthResponse.noneResp else m).run hst)) :
    Q y.2 := by
  cases hc : c
  · rw [hc] at hy; exact h hc hy
  · rw [hc] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
private theorem prop_if_not_noneResp_true_c2b {S : Setup} {Q : AuthHybridState S → Prop}
    (c : Bool)
    (m : StateT (AuthHybridState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (hRefl : Q hst) {y : AuthResponse × AuthHybridState S}
    (h : c = true → y ∈ support (m.run hst) → Q y.2)
    (hy : y ∈ support ((if !c then pure AuthResponse.noneResp else m).run hst)) :
    Q y.2 := by
  cases hc : c
  · rw [hc] at hy; exact prop_pure_noneResp_c2b hst hRefl hy
  · rw [hc] at hy; exact h hc hy
/-- Key-store invariant combining `ValidAuthKeyStores` and `ValidSessionIds`. -/
def ValidAuthKeyStoresFull (S : Setup) (P : Primitives) (st : AuthState S) : Prop :=
  ValidAuthKeyStores S P st ∧
  ValidSessionIds S ((sessPksAuth S P st).map Prod.fst) ∧
  st.usedSendSessions = (sessPksAuth S P st).map Prod.fst
theorem validAuthKeyStoresFull_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidAuthKeyStoresFull S P (AuthState.empty S secb) := by
  have hNil := validEcLists_nil S; exact ⟨validAuthKeyStores_empty S P secb, hNil.2.2.2, rfl⟩
theorem validAuthKeyStoresFull_lengths_le (S : Setup) (P : Primitives) (st : AuthState S)
    (hV : ValidAuthKeyStoresFull S P st) :
    st.principals.length ≤ S.N_dh ∧
    st.spkBundles.length ≤ S.N_dh ∧
    st.opkEntries.length ≤ S.N_dh ∧
    st.sessions.length ≤ S.N_dh := by
  have hTag := validTaggedPks_ecTaggedFromLists S P
    st.principals st.spkBundles st.opkEntries (sessPksAuth S P st)
    ⟨hV.1.1, hV.1.2.1, hV.1.2.2.1, hV.2.1⟩
  have hLen := validTaggedPks_length_le_fg hTag; unfold ecTaggedFromLists sessPksAuth at hLen
  simp only [List.length_append, List.length_map] at hLen
  exact ⟨by omega, by omega, by omega, by omega⟩
theorem validAuthKeyStores_of_fields_eq {S : Setup} {P : Primitives} {st1 st2 : AuthState S}
    (hV : ValidAuthKeyStores S P st1)
    (hPrin : st2.principals = st1.principals := by rfl)
    (hSpk : st2.spkBundles = st1.spkBundles := by rfl)
    (hOpk : st2.opkEntries = st1.opkEntries := by rfl)
    (hAdv : st2.advKeys = st1.advKeys := by rfl) :
    ValidAuthKeyStores S P st2 := by
  rcases hV with ⟨hVP, hVS, hVO, hPrins, hSpks, hOpks, hAdvs⟩
  refine ⟨by rw [hPrin]; exact hVP, by rw [hSpk]; exact hVS, by rw [hOpk]; exact hVO,
    by rw [hPrin]; exact hPrins, ?_, by rw [hOpk]; exact hOpks, by rw [hAdv]; exact hAdvs⟩
  rw [hSpk, hPrin]; exact hSpks
theorem validAuthKeyStoresFull_of_fields_eq {S : Setup} {P : Primitives} {st1 st2 : AuthState S}
    (hV : ValidAuthKeyStoresFull S P st1)
    (hPrin : st2.principals = st1.principals := by rfl)
    (hSpk : st2.spkBundles = st1.spkBundles := by rfl)
    (hOpk : st2.opkEntries = st1.opkEntries := by rfl)
    (hAdv : st2.advKeys = st1.advKeys := by rfl)
    (hSess : st2.sessions = st1.sessions := by rfl)
    (hUsed : st2.usedSendSessions = st1.usedSendSessions := by rfl) :
    ValidAuthKeyStoresFull S P st2 := by
  refine ⟨validAuthKeyStores_of_fields_eq hV.1 hPrin hSpk hOpk hAdv, ?_, ?_⟩
  · unfold sessPksAuth; rw [hSess]; exact hV.2.1
  · unfold sessPksAuth; rw [hUsed, hSess]; exact hV.2.2
theorem validAuthKeyStoresFull_runAuthHybridSendKosk {S : Setup} (stage : AuthHybridStage)
    (useRo : Bool) (P : Primitives) (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) (hV : ValidAuthKeyStoresFull S P hst.base)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((runAuthHybridSendKosk stage useRo S P sid u bundle m0 m1).run hst)) :
    ValidAuthKeyStoresFull S P y.2.base := by
  unfold runAuthHybridSendKosk at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
    hy => ?_) hy
  refine prop_if_noneResp_false_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV
    (fun hContains hy => ?_) hy
  have hFresh' : ((sessPksAuth S P hst.base).map Prod.fst).any (fun s => s == sid) = false := by
    rw [← hV.2.2]; revert hContains; simp; rintro h x hx rfl; exact h hx
  have hCons := validSessionIds_cons S sid ((sessPksAuth S P hst.base).map Prod.fst) hSend hV.2.1
    hFresh'
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    rw [hF] at hy
    exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hV hy
  | some ue =>
    rcases ue with ⟨_, uEntry⟩; rw [hF] at hy; dsimp only at hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    refine prop_bind_state_eq_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hy
      (state_eq_of_liftM_c2b _ hst) (fun ekASk y hy => ?_)
    refine prop_bind_state_eq_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hy
      (state_eq_of_liftM_c2b _ hst) (fun kemCoins y hy => ?_)
    refine prop_bind_state_eq_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hy
      (state_eq_of_liftM_c2b _ hst) (fun ephASk y hy => ?_)
    refine prop_bind_state_eq_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hy
      (state_eq_of_liftM_c2b _ hst) (fun spqrCoins y hy => ?_)
    refine prop_if_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ _ hst hV (fun
      hy => ?_) hy
    cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
    | none =>
      rw [hKem] at hy
      exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hV hy
    | some ssCt =>
      rcases ssCt with ⟨ss, kemCt⟩; rw [hKem] at hy; dsimp only at hy
      refine prop_ite_bind1_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hy (fun drRo y
        hy => ?_)
      rcases drRo with ⟨drKey, roCache'⟩
      refine prop_ite_bind2_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hy (fun rkRo y
        hy => ?_)
      rcases rkRo with ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      refine prop_ite_bind3_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hy (fun mkCk y
        hy => ?_)
      rcases mkCk with ⟨mkSeed, ck1_1⟩; cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
      | none =>
        rw [hSpqr] at hy
        exact prop_pure_noneResp_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hV hy
      | some spqrOut =>
        rcases spqrOut with ⟨_, spqrSalt?, pqRatchetMsg⟩; rw [hSpqr] at hy; dsimp only at hy
        refine prop_ite_bind4_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) hst hy (fun
          deriveMessageKeys y hy => ?_)
        refine prop_set_ite_pure_c2b (Q := fun s => ValidAuthKeyStoresFull S P s.base) _ hst _ _ _
          ?_ hy
        refine ⟨validAuthKeyStores_of_fields_eq hV.1, ?_, ?_⟩
        · unfold sessPksAuth; dsimp only [List.map]; exact hCons.1
        · rw [hV.2.2]; rfl
theorem validAuthKeyStoresFull_pqxdhAuthHybridKoskImpl {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridState S) (hV : ValidAuthKeyStoresFull S P hst.base)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst)) :
    ValidAuthKeyStoresFull S P y.2.base := by
  rcases hV with ⟨⟨hVP, hVS, hVO, hPrins, hSpks, hOpks, hAdvs⟩, hVSess, hUsed⟩
  have hV : ValidAuthKeyStoresFull S P hst.base := ⟨⟨hVP, hVS, hVO, hPrins, hSpks, hOpks, hAdvs⟩,
    hVSess, hUsed⟩
  unfold pqxdhAuthHybridKoskImpl at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp
    dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact hV)
/-! ## Ideal-session and responder handshake invariants -/
theorem koskBundleOk_imp_validPeerKeys {S : Setup} (P : Primitives) (st : AuthState S)
    (hKS : ValidAuthKeyStores S P st) (bundle : PreKeyBundleInput)
    (hKosk : koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle = true) :
    (∃ skB, skB.length = 32 ∧ P.pow8 bundle.ikB = P.pow8 (P.x25519Base skB)) ∧
    (∃ skSpk, skSpk.length = 32 ∧ P.pow8 bundle.spkB = P.pow8 (P.x25519Base skSpk)) ∧
    (∀ opkPk, bundle.opkB?.map Prod.snd = some opkPk →
      ∃ skOpk, skOpk.length = 32 ∧ P.pow8 opkPk = P.pow8 (P.x25519Base skOpk)) := by
  rcases hKS with ⟨_, _, _, hPrins, hSpks, hOpks, hAdvs⟩; unfold koskBundleOk at hKosk
  rcases Bool.and_eq_true_iff.mp hKosk with ⟨hKosk12, hKosk3⟩
  rcases Bool.and_eq_true_iff.mp hKosk12 with ⟨hKosk1, hKosk2⟩; refine ⟨?_, ?_, ?_⟩
  · rcases Bool.or_eq_true_iff.mp hKosk1 with hId | hAdv
    · unfold isGameIdKey findHonestPrincipal at hId
      cases hF : st.principals.find? (fun (_, e) => P.pow8 bundle.ikB == P.pow8 e.ikAPk) with
      | none => rw [hF] at hId; nomatch hId
      | some ke =>
        rcases ke with ⟨k, e⟩; have hMem := List.mem_of_find?_eq_some hF
        have hPow : P.pow8 bundle.ikB = P.pow8 e.ikAPk :=
          beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => P.pow8 bundle.ikB
            == P.pow8 x.2.ikAPk) hF)
        rcases hPrins (k, e) hMem with ⟨hLen, hPk⟩
        exact ⟨e.secIKA0, hLen, by rw [hPow, hPk]⟩
    · unfold isAdvRegistered at hAdv
      rcases List.any_eq_true.mp hAdv with ⟨⟨sk, pk'⟩, hMem, hPow⟩
      rcases hAdvs (sk, pk') hMem with ⟨hLen, hPk⟩; dsimp only at hLen hPk
      exact ⟨sk, hLen, by rw [beq_iff_eq.mp hPow, hPk]⟩
  · rcases Bool.or_eq_true_iff.mp hKosk2 with hSpk | hAdv
    · unfold isGameSpk at hSpk
      rcases List.any_eq_true.mp hSpk with ⟨⟨idx, b⟩, hMem, hPow⟩
      rcases hSpks (idx, b) hMem with ⟨hLen, hPk, _, _⟩
      exact ⟨b.spkSk, hLen, by rw [← beq_iff_eq.mp hPow, hPk]⟩
    · unfold isAdvRegistered at hAdv
      rcases List.any_eq_true.mp hAdv with ⟨⟨sk, pk'⟩, hMem, hPow⟩
      rcases hAdvs (sk, pk') hMem with ⟨hLen, hPk⟩; dsimp only at hLen hPk
      exact ⟨sk, hLen, by rw [beq_iff_eq.mp hPow, hPk]⟩
  · intro opkPk hMap
    cases hOpk : bundle.opkB? with
    | none => rw [hOpk] at hMap; nomatch hMap
    | some idPk =>
      rcases idPk with ⟨_, opkPk0⟩; rw [hOpk, Option.map_some, Option.some.injEq] at hMap
      subst hMap; rw [hOpk] at hKosk3
      dsimp only at hKosk3; rcases Bool.or_eq_true_iff.mp hKosk3 with hOpkG | hAdv
      · unfold isGameOpk at hOpkG
        rcases List.any_eq_true.mp hOpkG with ⟨⟨idx, o⟩, hMem, hPow⟩
        rcases hOpks (idx, o) hMem with ⟨hLen, hPk⟩
        exact ⟨o.opkSk, hLen, by rw [← beq_iff_eq.mp hPow, hPk]⟩
      · unfold isAdvRegistered at hAdv
        rcases List.any_eq_true.mp hAdv with ⟨⟨sk, pk'⟩, hMem, hPow⟩
        rcases hAdvs (sk, pk') hMem with ⟨hLen, hPk⟩; dsimp only at hLen hPk
        exact ⟨sk, hLen, by rw [beq_iff_eq.mp hPow, hPk]⟩
theorem isGameSpk_or_isAdvRegistered_mono_of_traceSub {S : Setup} (P : Primitives)
    {st1 st2 : AuthState S} (hSub : AuthBaseTraceSub st1 st2) (pk : Bytes)
    (h : (isGameSpk P st1.spkBundles pk || isAdvRegistered P st1.advKeys pk) = true) :
    (isGameSpk P st2.spkBundles pk || isAdvRegistered P st2.advKeys pk) = true := by
  rcases Bool.or_eq_true_iff.mp h with hG | hA
  · refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
    unfold isGameSpk at hG ⊢; rcases List.any_eq_true.mp hG with ⟨x, hx, hPred⟩
    exact List.any_eq_true.mpr ⟨x, hSub.spkBundles_sub.subset hx, hPred⟩
  · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
    unfold isAdvRegistered at hA ⊢; rcases List.any_eq_true.mp hA with ⟨x, hx, hPred⟩
    exact List.any_eq_true.mpr ⟨x, hSub.advKeys_sub.subset hx, hPred⟩
theorem validIdealAuthSession_of_traceSub {S : Setup} (P : Primitives)
    {hst1 hst2 : AuthHybridState S} (hSub : AuthHybridTraceSub hst1 hst2)
    {s : IdealAuthSession S} {sessEntry : AuthInitiatorEntry S}
    {u : Nat} {uEntry1 : PrincipalEntry} {kemCoins ss_s : Bytes}
    {initRec : _root_.SignalPqxdh.Security.InitKemRecord S}
    (hV : ValidIdealAuthSession S P hst1 s sessEntry u uEntry1 kemCoins ss_s initRec) :
    ∃ uEntry2 : PrincipalEntry,
      uEntry2.secIKA0 = uEntry1.secIKA0 ∧
      uEntry2.ikAPk = uEntry1.ikAPk ∧
      ValidIdealAuthSession S P hst2 s sessEntry u uEntry2 kemCoins ss_s initRec := by
  rcases hV with ⟨h1, h2, h3, h4, h5, h6, h7, h8, huMem1, h10, h11, h12, hiMem1, h14, h15, h16, h17,
    h18, h19⟩
  rcases hSub.base_sub.exists_prin huMem1 with ⟨uEntry2, huMem2, hSecEq, hIkEq⟩
  exact ⟨uEntry2, hSecEq, hIkEq,
    hSub.base_sub.sessions_sub.subset h1, h2, h3, h4, h5, h6, h7, h8,
    huMem2, h10, by rw [hIkEq, h11], h12, hSub.initRecs_sub.subset hiMem1,
    h14, h15, h16, h17, h18, h19⟩
def ValidAllIdealAuthSessions (S : Setup) (P : Primitives) (hst : AuthHybridState S) : Prop :=
  ∀ s ∈ hst.idealSessions,
    ∃ (sessEntry : AuthInitiatorEntry S) (u : Nat) (uEntry : PrincipalEntry)
      (kemCoins ss_s : Bytes) (initRec : _root_.SignalPqxdh.Security.InitKemRecord S),
      ValidIdealAuthSession S P hst s sessEntry u uEntry kemCoins ss_s initRec ∧
      (isGameSpk P hst.base.spkBundles sessEntry.peerSpkPk ||
       isAdvRegistered P hst.base.advKeys sessEntry.peerSpkPk) = true
theorem validAllIdealAuthSessions_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidAllIdealAuthSessions S P (AuthHybridState.empty S secb) := by
  intro s hs; nomatch hs
theorem validAllIdealAuthSessions_of_traceSub {S : Setup} (P : Primitives)
    {hst1 hst2 : AuthHybridState S} (hSub : AuthHybridTraceSub hst1 hst2)
    (hIdEq : hst2.idealSessions = hst1.idealSessions)
    (hV : ValidAllIdealAuthSessions S P hst1) :
    ValidAllIdealAuthSessions S P hst2 := by
  intro s hs2; rw [hIdEq] at hs2
  rcases hV s hs2 with ⟨sessEntry, u, uEntry1, kemCoins, ss_s, initRec, hVi1, hSpk1⟩
  rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨uEntry2, _, _, hVi2⟩
  exact ⟨sessEntry, u, uEntry2, kemCoins, ss_s, initRec, hVi2,
    isGameSpk_or_isAdvRegistered_mono_of_traceSub P hSub.base_sub _ hSpk1⟩
private theorem mem_ite_cons_c2b {α : Type} (c : Prop) [Decidable c] (a : α) (l : List α) {x : α}
    (h : x ∈ if c then a :: l else l) : x = a ∨ x ∈ l := by
  split_ifs at h
  · exact List.mem_cons.mp h
  · exact Or.inr h
private theorem mem_ite_cons_self_of_cond_c2b {α : Type} {c : Bool} (hc : c = true) (a : α) (l :
  List α) :
    a ∈ (if c = true then a :: l else l) := by
  simp [hc]
theorem validAllIdealAuthSessions_runAuthHybridSendKosk {S : Setup} (stage : AuthHybridStage)
    (useRo : Bool) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (hSender : sessionSenderIdx sid = u.val)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) (hKS : ValidAuthKeyStores S P hst.base)
    (hV : ValidAllIdealAuthSessions S P hst)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((runAuthHybridSendKosk stage useRo S P sid u bundle m0 m1).run hst)) :
    ValidAllIdealAuthSessions S P y.2 := by
  unfold runAuthHybridSendKosk at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine prop_if_noneResp_c2b (Q := ValidAllIdealAuthSessions S P) _ _ hst hV (fun hy => ?_) hy
  refine prop_if_noneResp_c2b (Q := ValidAllIdealAuthSessions S P) _ _ hst hV (fun hy => ?_) hy
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    rw [hF] at hy; exact prop_pure_noneResp_c2b hst hV hy
  | some ue =>
    rcases ue with ⟨u0, uEntry⟩; rw [hF] at hy; dsimp only at hy
    have hu0Mem : (u0, uEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hF
    have hu0Eq : u0 = u.val :=
      beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
    subst hu0Eq
    refine prop_if_noneResp_c2b (Q := ValidAllIdealAuthSessions S P) _ _ hst hV (fun hy => ?_) hy
    refine prop_if_not_noneResp_true_c2b (Q := ValidAllIdealAuthSessions S P) _ _ hst hV (fun hKosk
      hy => ?_) hy
    have hPeerKeys := koskBundleOk_imp_validPeerKeys P hst.base hKS bundle hKosk
    have hSpkReg : (isGameSpk P hst.base.spkBundles bundle.spkB || isAdvRegistered P
        hst.base.advKeys bundle.spkB) = true := by
      unfold koskBundleOk at hKosk
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hKosk).1).2
    refine prop_bind_liftM_mem_c2b (Q := ValidAllIdealAuthSessions S P) hst hy (fun ekASk hekASk y
      hy => ?_)
    have hekLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hekASk
    refine prop_bind_state_eq_c2b (Q := ValidAllIdealAuthSessions S P) hst hy (state_eq_of_liftM_c2b
      _ hst) (fun kemCoins y hy => ?_)
    refine prop_bind_state_eq_c2b (Q := ValidAllIdealAuthSessions S P) hst hy (state_eq_of_liftM_c2b
      _ hst) (fun ephASk y hy => ?_)
    refine prop_bind_state_eq_c2b (Q := ValidAllIdealAuthSessions S P) hst hy (state_eq_of_liftM_c2b
      _ hst) (fun spqrCoins y hy => ?_)
    refine prop_if_noneResp_c2b (Q := ValidAllIdealAuthSessions S P) _ _ hst hV (fun hy => ?_) hy
    cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
    | none =>
      rw [hKem] at hy; exact prop_pure_noneResp_c2b hst hV hy
    | some ssCt =>
      rcases ssCt with ⟨ss, kemCt⟩; rw [hKem] at hy; dsimp only at hy
      refine prop_ite_bind1_c2b (Q := ValidAllIdealAuthSessions S P) hst hy (fun drRo y hy => ?_)
      rcases drRo with ⟨drKey, roCache'⟩
      refine prop_ite_bind2_c2b (Q := ValidAllIdealAuthSessions S P) hst hy (fun rkRo y hy => ?_)
      rcases rkRo with ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      refine prop_ite_bind3_c2b (Q := ValidAllIdealAuthSessions S P) hst hy (fun mkCk y hy => ?_)
      rcases mkCk with ⟨mkSeed, ck1_1⟩; cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
      | none =>
        rw [hSpqr] at hy; exact prop_pure_noneResp_c2b hst hV hy
      | some spqrOut =>
        rcases spqrOut with ⟨_, spqrSalt?, pqRatchetMsg⟩; rw [hSpqr] at hy; dsimp only at hy
        refine prop_ite_bind4_c2b (Q := ValidAllIdealAuthSessions S P) hst hy (fun deriveMessageKeys y hy =>
          ?_)
        have hyEq := eq_of_set_ite_pure_c2b _ hst _ _ _ hy
        have hSub : AuthHybridTraceSub hst y.2 := by
          rw [hyEq]
          exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl
            _, List.sublist_cons_self _ _⟩, List.sublist_cons_self _ _, List.Sublist.refl _,
            sublist_ite_cons_self_c2b _ _ _⟩
        intro s hs; have hs' : s ∈ y.2.idealSessions := hs
        rw [hyEq] at hs'; dsimp only at hs'; rcases mem_ite_cons_c2b _ _ _ hs' with rfl | hsOld
        · rw [hyEq]
          exact ⟨_, u.val, uEntry, kemCoins, ss, _,
            ⟨List.mem_cons_self, rfl, hekLen, rfl, rfl, rfl, rfl, rfl,
             hu0Mem, hSender, rfl, hKem, List.mem_cons_self, rfl, rfl, rfl,
             hPeerKeys.1, hPeerKeys.2.1, hPeerKeys.2.2⟩,
            hSpkReg⟩
        · rcases hV s hsOld with ⟨sessEntry, u1, uEntry1, kc1, ss1, ir1, hVi1, hSpk1⟩
          rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨uEntry2, _, _, hVi2⟩
          exact ⟨sessEntry, u1, uEntry2, kc1, ss1, ir1, hVi2,
            isGameSpk_or_isAdvRegistered_mono_of_traceSub P hSub.base_sub _ hSpk1⟩
theorem validAllIdealAuthSessions_pqxdhAuthHybridKoskImpl {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridState S) (hKS : ValidAuthKeyStores S P hst.base)
    (hV : ValidAllIdealAuthSessions S P hst)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst)) :
    ValidAllIdealAuthSessions S P y.2 := by
  have hSub := authHybridTraceSub_pqxdhAuthHybridKoskImpl stage useRo checkAuth P q hst hy
  unfold pqxdhAuthHybridKoskImpl at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
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
/-! ## Sent-event and combined run invariants -/
def ValidSentOPKEvent (S : Setup) (P : Primitives) (hst : AuthHybridState S)
    (s_ev : SentOPKEvent) : Prop :=
  ∃ (st0 : AuthState S) (u : Fin S.N_id) (uEntry0 pEntry0 : PrincipalEntry)
    (k_s : Nat) (bundle : PreKeyBundleInput) (opkId : KeyId)
    (opkPk ekAPk kemCt msgPlain : Bytes)
    (sessEntry : AuthInitiatorEntry S) (idealEntry : IdealAuthSession S),
    AuthBaseTraceSub st0 hst.base ∧
    st0.principals.find? (fun (idx, _) => idx == u.val) = some (u.val, uEntry0) ∧
    findHonestPrincipal P st0.principals bundle.ikB = some (k_s, pEntry0) ∧
    bundle.opkB? = some (opkId, opkPk) ∧
    (isGameSpk P st0.spkBundles bundle.spkB || isAdvRegistered P st0.advKeys bundle.spkB) = true ∧
    sessEntry ∈ hst.base.sessions ∧
    sessionSenderIdx sessEntry.sid = u.val ∧
    sessEntry.peerSpkPk = bundle.spkB ∧
    (s_ev.a0 = uEntry0.ikAPk ∧ s_ev.b0 = pEntry0.ikAPk ∧ s_ev.sb = bundle.spkB ∧
     s_ev.ob = opkPk ∧ s_ev.a1 = ekAPk ∧ s_ev.pk1 = bundle.pqspkB ∧
     s_ev.ct = kemCt ∧ s_ev.m = msgPlain) ∧
    (idealEntry.ikAPk = uEntry0.ikAPk ∧ idealEntry.peerIkPk = bundle.ikB ∧
     idealEntry.peerSpkPk = bundle.spkB ∧ idealEntry.peerOpkPk? = some opkPk ∧
     idealEntry.ekAPk = ekAPk ∧ idealEntry.peerPqspkPk = bundle.pqspkB ∧
     idealEntry.kemCt = kemCt) ∧
    ((!pEntry0.corrupted ||
      (checkBundleSpkHonIdeal P st0.principals st0.spkBundles bundle &&
       (checkBundleProvenanceExact P st0.principals st0.spkBundles st0.opkEntries bundle).2.2)) =
         true →
     idealEntry ∈ hst.idealSessions)
def ValidSentNoOPKEvent (S : Setup) (P : Primitives) (hst : AuthHybridState S)
    (s_ev : SentNoOPKEvent) : Prop :=
  ∃ (st0 : AuthState S) (u : Fin S.N_id) (uEntry0 pEntry0 : PrincipalEntry)
    (k_s : Nat) (bundle : PreKeyBundleInput)
    (ekAPk kemCt msgPlain : Bytes)
    (sessEntry : AuthInitiatorEntry S) (idealEntry : IdealAuthSession S),
    AuthBaseTraceSub st0 hst.base ∧
    st0.principals.find? (fun (idx, _) => idx == u.val) = some (u.val, uEntry0) ∧
    findHonestPrincipal P st0.principals bundle.ikB = some (k_s, pEntry0) ∧
    bundle.opkB? = none ∧
    (isGameSpk P st0.spkBundles bundle.spkB || isAdvRegistered P st0.advKeys bundle.spkB) = true ∧
    sessEntry ∈ hst.base.sessions ∧
    sessionSenderIdx sessEntry.sid = u.val ∧
    sessEntry.peerSpkPk = bundle.spkB ∧
    (s_ev.a0 = uEntry0.ikAPk ∧ s_ev.b0 = pEntry0.ikAPk ∧ s_ev.sb = bundle.spkB ∧
     s_ev.a1 = ekAPk ∧ s_ev.pk1 = bundle.pqspkB ∧
     s_ev.ct = kemCt ∧ s_ev.m = msgPlain) ∧
    (idealEntry.ikAPk = uEntry0.ikAPk ∧ idealEntry.peerIkPk = bundle.ikB ∧
     idealEntry.peerSpkPk = bundle.spkB ∧ idealEntry.peerOpkPk? = none ∧
     idealEntry.ekAPk = ekAPk ∧ idealEntry.peerPqspkPk = bundle.pqspkB ∧
     idealEntry.kemCt = kemCt) ∧
    ((!pEntry0.corrupted ||
      (checkBundleSpkHonIdeal P st0.principals st0.spkBundles bundle &&
       (checkBundleProvenanceExact P st0.principals st0.spkBundles st0.opkEntries bundle).2.2)) =
         true →
     idealEntry ∈ hst.idealSessions)
theorem validSentOPKEvent_of_traceSub {S : Setup} (P : Primitives)
    {hst1 hst2 : AuthHybridState S} (hSub : AuthHybridTraceSub hst1 hst2)
    {s_ev : SentOPKEvent} (hV : ValidSentOPKEvent S P hst1 s_ev) :
    ValidSentOPKEvent S P hst2 s_ev := by
  rcases hV with ⟨st0, u, uEntry0, pEntry0, k_s, bundle, opkId, opkPk, ekAPk, kemCt, msgPlain,
    sessEntry, idealEntry, hSub0, hFU, hFP, hOpk, hKosk, hSess, hSend, hSpk, hsEv, hIdeal, hMemId⟩
  exact ⟨st0, u, uEntry0, pEntry0, k_s, bundle, opkId, opkPk, ekAPk, kemCt, msgPlain,
    sessEntry, idealEntry, hSub0.trans hSub.base_sub, hFU, hFP, hOpk, hKosk,
    hSub.base_sub.sessions_sub.subset hSess, hSend, hSpk, hsEv, hIdeal,
    fun hCond => hSub.idealSessions_sub.subset (hMemId hCond)⟩
theorem validSentNoOPKEvent_of_traceSub {S : Setup} (P : Primitives)
    {hst1 hst2 : AuthHybridState S} (hSub : AuthHybridTraceSub hst1 hst2)
    {s_ev : SentNoOPKEvent} (hV : ValidSentNoOPKEvent S P hst1 s_ev) :
    ValidSentNoOPKEvent S P hst2 s_ev := by
  rcases hV with ⟨st0, u, uEntry0, pEntry0, k_s, bundle, ekAPk, kemCt, msgPlain,
    sessEntry, idealEntry, hSub0, hFU, hFP, hOpk, hKosk, hSess, hSend, hSpk, hsEv, hIdeal, hMemId⟩
  exact ⟨st0, u, uEntry0, pEntry0, k_s, bundle, ekAPk, kemCt, msgPlain,
    sessEntry, idealEntry, hSub0.trans hSub.base_sub, hFU, hFP, hOpk, hKosk,
    hSub.base_sub.sessions_sub.subset hSess, hSend, hSpk, hsEv, hIdeal,
    fun hCond => hSub.idealSessions_sub.subset (hMemId hCond)⟩
theorem validSentOPKEvent_with_matched {S : Setup} (P : Primitives) (hst : AuthHybridState S)
    {s_ev : SentOPKEvent} (m : Bool) (hV : ValidSentOPKEvent S P hst s_ev) :
    ValidSentOPKEvent S P hst { s_ev with matched := m } := by
  rcases hV with ⟨st0, u, uEntry0, pEntry0, k_s, bundle, opkId, opkPk, ekAPk, kemCt, msgPlain,
    sessEntry, idealEntry, hSub0, hFU, hFP, hOpk, hKosk, hSess, hSend, hSpk, hsEv, hIdeal, hMemId⟩
  exact ⟨st0, u, uEntry0, pEntry0, k_s, bundle, opkId, opkPk, ekAPk, kemCt, msgPlain,
    sessEntry, idealEntry, hSub0, hFU, hFP, hOpk, hKosk, hSess, hSend, hSpk, hsEv, hIdeal, hMemId⟩
theorem validSentNoOPKEvent_with_matched {S : Setup} (P : Primitives) (hst : AuthHybridState S)
    {s_ev : SentNoOPKEvent} (m : Bool) (hV : ValidSentNoOPKEvent S P hst s_ev) :
    ValidSentNoOPKEvent S P hst { s_ev with matched := m } := by
  rcases hV with ⟨st0, u, uEntry0, pEntry0, k_s, bundle, ekAPk, kemCt, msgPlain,
    sessEntry, idealEntry, hSub0, hFU, hFP, hOpk, hKosk, hSess, hSend, hSpk, hsEv, hIdeal, hMemId⟩
  exact ⟨st0, u, uEntry0, pEntry0, k_s, bundle, ekAPk, kemCt, msgPlain,
    sessEntry, idealEntry, hSub0, hFU, hFP, hOpk, hKosk, hSess, hSend, hSpk, hsEv, hIdeal, hMemId⟩
theorem mem_consumeMatchingSentOPK_snd (P : Primitives) (r : RecvdOPKEvent) :
    ∀ (l : List SentOPKEvent) {s' : SentOPKEvent},
      s' ∈ (consumeMatchingSentOPK P r l).2 →
      ∃ s ∈ l, s' = s ∨ s' = { s with matched := true }
  | [], _, hs' => nomatch hs'
  | s :: rest, s', hs' => by
    unfold consumeMatchingSentOPK at hs'
    split_ifs at hs'
    · rcases List.mem_cons.mp hs' with hEq | hMem
      · exact ⟨s, List.mem_cons_self, Or.inr hEq⟩
      · exact ⟨s', List.mem_cons_of_mem _ hMem, Or.inl rfl⟩
    · rcases List.mem_cons.mp hs' with hEq | hMem
      · exact ⟨s, List.mem_cons_self, Or.inl hEq⟩
      · rcases mem_consumeMatchingSentOPK_snd P r rest hMem with ⟨s0, hs0, hEq⟩
        exact ⟨s0, List.mem_cons_of_mem _ hs0, hEq⟩
theorem mem_consumeMatchingSentNoOPK_snd (P : Primitives) (r : RecvdNoOPKEvent) :
    ∀ (l : List SentNoOPKEvent) {s' : SentNoOPKEvent},
      s' ∈ (consumeMatchingSentNoOPK P r l).2 →
      ∃ s ∈ l, s' = s ∨ s' = { s with matched := true }
  | [], _, hs' => nomatch hs'
  | s :: rest, s', hs' => by
    unfold consumeMatchingSentNoOPK at hs'
    split_ifs at hs'
    · rcases List.mem_cons.mp hs' with hEq | hMem
      · exact ⟨s, List.mem_cons_self, Or.inr hEq⟩
      · exact ⟨s', List.mem_cons_of_mem _ hMem, Or.inl rfl⟩
    · rcases List.mem_cons.mp hs' with hEq | hMem
      · exact ⟨s, List.mem_cons_self, Or.inl hEq⟩
      · rcases mem_consumeMatchingSentNoOPK_snd P r rest hMem with ⟨s0, hs0, hEq⟩
        exact ⟨s0, List.mem_cons_of_mem _ hs0, hEq⟩
def ValidSentEvents (S : Setup) (P : Primitives) (hst : AuthHybridState S) : Prop :=
  (∀ s_ev ∈ hst.base.sentOPKEvents, ValidSentOPKEvent S P hst s_ev) ∧
  (∀ s_ev ∈ hst.base.sentNoOPKEvents, ValidSentNoOPKEvent S P hst s_ev)
theorem validSentEvents_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidSentEvents S P (AuthHybridState.empty S secb) :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
theorem validSentEvents_of_traceSub_and_eq {S : Setup} (P : Primitives)
    {hst1 hst2 : AuthHybridState S} (hSub : AuthHybridTraceSub hst1 hst2)
    (hOPK : hst2.base.sentOPKEvents = hst1.base.sentOPKEvents)
    (hNoOPK : hst2.base.sentNoOPKEvents = hst1.base.sentNoOPKEvents)
    (hV : ValidSentEvents S P hst1) :
    ValidSentEvents S P hst2 := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [hOPK] at hs; exact validSentOPKEvent_of_traceSub P hSub (hV.1 s hs)
  · rw [hNoOPK] at hs; exact validSentNoOPKEvent_of_traceSub P hSub (hV.2 s hs)
theorem validSentEvents_runAuthHybridSendKosk {S : Setup} (stage : AuthHybridStage)
    (useRo : Bool) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (hSender : sessionSenderIdx sid = u.val)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) (hV : ValidSentEvents S P hst)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((runAuthHybridSendKosk stage useRo S P sid u bundle m0 m1).run hst)) :
    ValidSentEvents S P y.2 := by
  unfold runAuthHybridSendKosk at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
  dsimp only at hy
  refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
  refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    rw [hF] at hy; exact prop_pure_noneResp_c2b hst hV hy
  | some ue =>
    rcases ue with ⟨u0, uEntry⟩; rw [hF] at hy; dsimp only at hy
    have hu0Eq : u0 = u.val :=
      beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hF)
    subst hu0Eq; refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    refine prop_if_not_noneResp_true_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hKosk hy => ?_)
      hy
    have hSpkReg : (isGameSpk P hst.base.spkBundles bundle.spkB || isAdvRegistered P
        hst.base.advKeys bundle.spkB) = true := by
      unfold koskBundleOk at hKosk
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hKosk).1).2
    refine prop_bind_state_eq_c2b (Q := ValidSentEvents S P) hst hy (state_eq_of_liftM_c2b _ hst)
      (fun ekASk y hy => ?_)
    refine prop_bind_state_eq_c2b (Q := ValidSentEvents S P) hst hy (state_eq_of_liftM_c2b _ hst)
      (fun kemCoins y hy => ?_)
    refine prop_bind_state_eq_c2b (Q := ValidSentEvents S P) hst hy (state_eq_of_liftM_c2b _ hst)
      (fun ephASk y hy => ?_)
    refine prop_bind_state_eq_c2b (Q := ValidSentEvents S P) hst hy (state_eq_of_liftM_c2b _ hst)
      (fun spqrCoins y hy => ?_)
    refine prop_if_noneResp_c2b (Q := ValidSentEvents S P) _ _ hst hV (fun hy => ?_) hy
    cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
    | none =>
      rw [hKem] at hy; exact prop_pure_noneResp_c2b hst hV hy
    | some ssCt =>
      rcases ssCt with ⟨ss, kemCt⟩; rw [hKem] at hy; dsimp only at hy
      refine prop_ite_bind1_c2b (Q := ValidSentEvents S P) hst hy (fun drRo y hy => ?_)
      rcases drRo with ⟨drKey, roCache'⟩
      refine prop_ite_bind2_c2b (Q := ValidSentEvents S P) hst hy (fun rkRo y hy => ?_)
      rcases rkRo with ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      refine prop_ite_bind3_c2b (Q := ValidSentEvents S P) hst hy (fun mkCk y hy => ?_)
      rcases mkCk with ⟨mkSeed, ck1_1⟩; cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
      | none =>
        rw [hSpqr] at hy; exact prop_pure_noneResp_c2b hst hV hy
      | some spqrOut =>
        rcases spqrOut with ⟨_, spqrSalt?, pqRatchetMsg⟩; rw [hSpqr] at hy; dsimp only at hy
        refine prop_ite_bind4_c2b (Q := ValidSentEvents S P) hst hy (fun deriveMessageKeys y hy => ?_)
        have hyEq := eq_of_set_ite_pure_c2b _ hst _ _ _ hy
        have hSub : AuthHybridTraceSub hst y.2 := by
          rw [hyEq]
          exact ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl
            _, List.sublist_cons_self _ _⟩, List.sublist_cons_self _ _, List.Sublist.refl _,
            sublist_ite_cons_self_c2b _ _ _⟩
        refine ⟨fun s_ev hs => ?_, fun s_ev hs => ?_⟩
        · have hs' : s_ev ∈ y.2.base.sentOPKEvents := hs
          rw [hyEq] at hs'; dsimp only at hs'
          cases hFP : findHonestPrincipal P hst.base.principals bundle.ikB with
          | none =>
            rw [hFP] at hs'; dsimp only at hs'
            exact validSentOPKEvent_of_traceSub P hSub (hV.1 s_ev hs')
          | some kp =>
            rcases kp with ⟨k_s, pEntry0⟩; cases hOpk : bundle.opkB? with
            | none =>
              rw [hFP, hOpk] at hs'; dsimp only at hs'
              exact validSentOPKEvent_of_traceSub P hSub (hV.1 s_ev hs')
            | some idPk =>
              rcases idPk with ⟨opkId, opkPk⟩; rw [hFP, hOpk] at hs'; dsimp only at hs'
              rcases List.mem_cons.mp hs' with rfl | hsOld
              · refine ⟨hst.base, u, uEntry, pEntry0, k_s, bundle, opkId, opkPk,
                  P.x25519Base ekASk, kemCt, _, _,
                  { sid := sid, ikAPk := uEntry.ikAPk, peerIkPk := bundle.ikB, peerSpkPk :=
                    bundle.spkB,
                    peerOpkPk? := Option.map Prod.snd bundle.opkB?, ekAPk := P.x25519Base ekASk,
                      peerPqspkPk := bundle.pqspkB,
                    kemCt := kemCt, ephAPk := P.x25519Base ephASk, spqrSalt? := spqrSalt?,
                      pqRatchetMsg := pqRatchetMsg,
                    ad := firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk) pqRatchetMsg,
                    aeadCt := P.aeadEnc deriveMessageKeys (firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base
                      ephASk) pqRatchetMsg)
                      (if (match findHonestPrincipal P hst.base.principals bundle.ikB with
                        | some (_, pEntry) => !pEntry.corrupted | none => false) = true
                       then if stage.idealFreshAead = true then m0 else if hst.base.secb = true then
                         m1 else m0 else m0),
                    msgPlain := (if (match findHonestPrincipal P hst.base.principals bundle.ikB with
                      | some (_, pEntry) => !pEntry.corrupted | none => false) = true
                       then if stage.idealFreshAead = true then m0 else if hst.base.secb = true then
                         m1 else m0 else m0),
                    drKey := drKey, rk1 := rk1, ck1_0 := ck1_0, mkSeed := mkSeed, ck1_1 := ck1_1,
                      deriveMessageKeys := deriveMessageKeys },
                  hSub.base_sub, hF, hFP, hOpk, hSpkReg,
                  by rw [hyEq]; exact List.mem_cons_self, hSender, rfl,
                  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
                  ⟨rfl, rfl, rfl, by rw [hOpk]; rfl, rfl, rfl, rfl⟩,
                  fun hCond => ?_⟩
                rw [hyEq]; dsimp only
                have hCond' :
                    ((match findHonestPrincipal P hst.base.principals bundle.ikB with
                      | some (_, pEntry) => !pEntry.corrupted
                      | none => false) ||
                     ((findHonestPrincipal P hst.base.principals bundle.ikB).isSome &&
                      checkBundleSpkHonIdeal P hst.base.principals hst.base.spkBundles bundle &&
                      (checkBundleProvenanceExact P hst.base.principals hst.base.spkBundles
                          hst.base.opkEntries bundle).2.2)) = true := by
                  rw [hFP]; dsimp only [Option.isSome]; simpa [Bool.true_and] using hCond
                exact mem_ite_cons_self_of_cond_c2b hCond' _ _
              · exact validSentOPKEvent_of_traceSub P hSub (hV.1 s_ev hsOld)
        · have hs' : s_ev ∈ y.2.base.sentNoOPKEvents := hs
          rw [hyEq] at hs'; dsimp only at hs'
          cases hFP : findHonestPrincipal P hst.base.principals bundle.ikB with
          | none =>
            rw [hFP] at hs'; dsimp only at hs'
            exact validSentNoOPKEvent_of_traceSub P hSub (hV.2 s_ev hs')
          | some kp =>
            rcases kp with ⟨k_s, pEntry0⟩; cases hOpk : bundle.opkB? with
            | some idPk =>
              rcases idPk with ⟨opkId, opkPk⟩; rw [hFP, hOpk] at hs'; dsimp only at hs'
              exact validSentNoOPKEvent_of_traceSub P hSub (hV.2 s_ev hs')
            | none =>
              rw [hFP, hOpk] at hs'; dsimp only at hs'; rcases List.mem_cons.mp hs' with rfl | hsOld
              · refine ⟨hst.base, u, uEntry, pEntry0, k_s, bundle,
                  P.x25519Base ekASk, kemCt, _, _,
                  { sid := sid, ikAPk := uEntry.ikAPk, peerIkPk := bundle.ikB, peerSpkPk :=
                    bundle.spkB,
                    peerOpkPk? := Option.map Prod.snd bundle.opkB?, ekAPk := P.x25519Base ekASk,
                      peerPqspkPk := bundle.pqspkB,
                    kemCt := kemCt, ephAPk := P.x25519Base ephASk, spqrSalt? := spqrSalt?,
                      pqRatchetMsg := pqRatchetMsg,
                    ad := firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base ephASk) pqRatchetMsg,
                    aeadCt := P.aeadEnc deriveMessageKeys (firstMsgAD uEntry.ikAPk bundle.ikB (P.x25519Base
                      ephASk) pqRatchetMsg)
                      (if (match findHonestPrincipal P hst.base.principals bundle.ikB with
                        | some (_, pEntry) => !pEntry.corrupted | none => false) = true
                       then if stage.idealFreshAead = true then m0 else if hst.base.secb = true then
                         m1 else m0 else m0),
                    msgPlain := (if (match findHonestPrincipal P hst.base.principals bundle.ikB with
                      | some (_, pEntry) => !pEntry.corrupted | none => false) = true
                       then if stage.idealFreshAead = true then m0 else if hst.base.secb = true then
                         m1 else m0 else m0),
                    drKey := drKey, rk1 := rk1, ck1_0 := ck1_0, mkSeed := mkSeed, ck1_1 := ck1_1,
                      deriveMessageKeys := deriveMessageKeys },
                  hSub.base_sub, hF, hFP, hOpk, hSpkReg,
                  by rw [hyEq]; exact List.mem_cons_self, hSender, rfl,
                  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
                  ⟨rfl, rfl, rfl, by rw [hOpk]; rfl, rfl, rfl, rfl⟩,
                  fun hCond => ?_⟩
                rw [hyEq]; dsimp only
                have hCond' :
                    ((match findHonestPrincipal P hst.base.principals bundle.ikB with
                      | some (_, pEntry) => !pEntry.corrupted
                      | none => false) ||
                     ((findHonestPrincipal P hst.base.principals bundle.ikB).isSome &&
                      checkBundleSpkHonIdeal P hst.base.principals hst.base.spkBundles bundle &&
                      (checkBundleProvenanceExact P hst.base.principals hst.base.spkBundles
                          hst.base.opkEntries bundle).2.2)) = true := by
                  rw [hFP]; dsimp only [Option.isSome]; simpa [Bool.true_and] using hCond
                exact mem_ite_cons_self_of_cond_c2b hCond' _ _
              · exact validSentNoOPKEvent_of_traceSub P hSub (hV.2 s_ev hsOld)
theorem validSentEvents_pqxdhAuthHybridKoskImpl {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridState S) (hV : ValidSentEvents S P hst)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst)) :
    ValidSentEvents S P y.2 := by
  have hSub := authHybridTraceSub_pqxdhAuthHybridKoskImpl stage useRo checkAuth P q hst hy
  unfold pqxdhAuthHybridKoskImpl at hy; rw [StateT.run_bind, StateT.run_get, pure_bind] at hy
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
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
    unfold pqxdhAuthImpl at hp; rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only
      at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩;
       exact validSentEvents_of_traceSub_and_eq P hSub (by rw [← hEq]) (by rw [← hEq]) hV)
/-- Combined inductive run invariant of `pqxdhAuthHybridKoskImpl` and `pqxdhAuthAdvStageImpl`. -/
def ValidAuthHybridRunInv (S : Setup) (P : Primitives) (hst : AuthHybridState S) : Prop :=
  ValidAuthKeyStoresFull S P hst.base ∧
  ValidAllIdealAuthSessions S P hst ∧
  ValidSentEvents S P hst
theorem validAuthHybridRunInv_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidAuthHybridRunInv S P (AuthHybridState.empty S secb) :=
  ⟨validAuthKeyStoresFull_empty S P secb,
   validAllIdealAuthSessions_empty S P secb,
   validSentEvents_empty S P secb⟩
theorem validAuthHybridRunInv_pqxdhAuthHybridKoskImpl {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridState S) (hInv : ValidAuthHybridRunInv S P hst)
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst)) :
    ValidAuthHybridRunInv S P y.2 :=
  ⟨validAuthKeyStoresFull_pqxdhAuthHybridKoskImpl stage useRo checkAuth P q hst hInv.1 hy,
   validAllIdealAuthSessions_pqxdhAuthHybridKoskImpl stage useRo checkAuth P q hst hInv.1.1 hInv.2.1
     hy,
   validSentEvents_pqxdhAuthHybridKoskImpl stage useRo checkAuth P q hst hInv.2.2 hy⟩
theorem validAuthHybridRunInv_pqxdhAuthAdvStageImpl {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvCutoffState S)
    (hInv : ValidAuthHybridRunInv S P s.hyb)
    {y : AuthResponse × AuthAdvCutoffState S}
    (hy : y ∈ support ((pqxdhAuthAdvStageImpl stage S P q).run s)) :
    ValidAuthHybridRunInv S P y.2.hyb := by
  cases q <;> {
    simp only [pqxdhAuthAdvStageImpl, StateT.run_mk, support_bind, Set.mem_iUnion,
      mem_support_pure_iff] at hy
    rcases hy with ⟨⟨resp, hyb'⟩, hHyb, rfl⟩
    exact validAuthHybridRunInv_pqxdhAuthHybridKoskImpl stage true true P _ s.hyb hInv hHyb
  }
end Proofs.SignalPqxdh.Security
