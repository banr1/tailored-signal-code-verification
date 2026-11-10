/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopA
public import Computational.Proofs.SignalPqxdh.Security.SigHop
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHop
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthGapDhHopA
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyA

/-!
# One-Key `Auth` Simulator Validity and Primitive Bridging

Proves simulator state invariants and `PrimBaseSpec` equivalence for `pqxdhAuthSimImpl1Key` over
the shared-scalar identity-key oracle `pqxdhAuthImpl1KeyG`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open MeasureTheory
open SignalPqxdh
open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

theorem pqxdhAuthSimImpl_sendOPK_pres1Key (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes) (st : AuthState
      S) :
    SatisfiesAt (InitPostAuth P b st) st (pqxdhAuthSimImpl1Key S P (.sendOPK u i b m0 m1)) := by
  unfold pqxdhAuthSimImpl1Key; dsimp only
  by_cases h : b.opkB?.isNone = true
  · simp only [h, ↓reduceIte]; exact SatisfiesAt.pure _ _ _ (initPostAuth_refl P b st)
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact runAuthSendSim_pres S P (.sendOPK u i) u b m0 m1 st

theorem pqxdhAuthSimImpl_sendNoOPK_pres1Key (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes) (st :
      AuthState S) :
    SatisfiesAt (InitPostAuth P b st) st (pqxdhAuthSimImpl1Key S P (.sendNoOPK u i b m0 m1)) := by
  unfold pqxdhAuthSimImpl1Key; dsimp only
  by_cases h : b.opkB?.isSome = true
  · simp only [h, ↓reduceIte]; exact SatisfiesAt.pure _ _ _ (initPostAuth_refl P b st)
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact runAuthSendSim_pres S P (.sendNoOPK u i) u b m0 m1 st

theorem pqxdhAuthSimImpl_recvNoOPK_pres_proj1Key (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) (st : AuthState S) :
    PreservesAt (fun s : AuthState S => (s.principals, s.spkBundles, s.opkEntries, s.advKeys)) st
      (pqxdhAuthSimImpl1Key S P (.recvNoOPK k j l msg)) := by
  unfold pqxdhAuthSimImpl1Key; dsimp only; prove_preserves_at

theorem pqxdhAuthSimImpl_validAuthSim_step1Key (S : Setup) (P : Primitives)
    (q : AuthQuery S) (st : AuthState S) (hV : ValidAuthSim S P st) :
    ∀ x ∈ support ((pqxdhAuthSimImpl1Key S P q).run st), ValidAuthSim S P x.2 := by
  rcases hV with ⟨hVP, hVS, hVO, hAdv⟩
  let proj := fun s : AuthState S => (s.principals, s.spkBundles, s.opkEntries, s.advKeys)
  have h_from_proj : ∀ m : StateT (AuthState S) ProbComp AuthResponse,
      PreservesAt proj st m →
      ∀ x ∈ support (m.run st), ValidAuthSim S P x.2 := by
    intro m hp x hx
    have hs := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst hs
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) hs
    have hp3 : x.2.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hs
    have hp4 : x.2.advKeys = st.advKeys := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hs
    exact ⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hAdv⟩
  cases q with
  | initPrin u =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨secIKA0, _, rfl⟩
      exact ⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hAdv⟩
    · simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
  | corruptIK u =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
    | some p =>
      rcases p with ⟨_, entry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      have h_corr := validPrincipals_map_corrupted S P u.val st.principals hVP
      intro x hx
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
      exact ⟨h_corr.1, hVS, hVO, hAdv⟩
  | genSPK u j =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        exact ⟨hVP, (validSpkBundles_cons S u j _ st.spkBundles hVS hFresh).1, hVO, hAdv⟩
    · simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
  | genOPK u j o =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨opkSk, _, rfl⟩
      exact ⟨hVP, hVS, (validOpkEntries_cons S u j o _ st.opkEntries hVO hFresh).1, hAdv⟩
    · simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
  | recvOPK k j o msg =>
    let projOpk := fun s : AuthState S =>
      (s.principals, s.spkBundles, s.opkEntries.map Prod.fst, s.advKeys)
    have h_step : ∀ (s : AuthState S) u t rc rrc,
        projOpk { s with
          opkEntries := s.opkEntries.map (fun (idx, e) =>
            if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
          usedRecvOPK := u, seenKyberBaseKeys := t, roCache := rc, rootRoCache := rrc } = projOpk s
            := by
      intro s u t rc rrc
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
      dsimp only [projOpk]
      rw [List.map_map]
      refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projOpk st (pqxdhAuthSimImpl1Key S P (.recvOPK k j o msg)) := by
      unfold pqxdhAuthSimImpl1Key; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _ _ _ _ _)
        | split)
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp3 : x.2.opkEntries.map Prod.fst = st.opkEntries.map Prod.fst :=
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp4 : x.2.advKeys = st.advKeys :=
      congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    refine ⟨hp1 ▸ hVP, hp2 ▸ hVS, ⟨?_, ?_⟩, hp4 ▸ hAdv⟩
    · intro e he
      have he_fst : e.1 ∈ st.opkEntries.map Prod.fst := by
        rw [← hp3]; exact List.mem_map_of_mem he
      rw [List.mem_map] at he_fst
      rcases he_fst with ⟨e', he', heq⟩
      rw [← heq]; exact hVO.1 e' he'
    · have h_slot : x.2.opkEntries.map (fun e => ecOpkSlotIdx S e.1) =
          st.opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map (ecOpkSlotIdx S)) hp3
      rw [h_slot]; exact hVO.2
  | registerKey sk =>
    unfold pqxdhAuthSimImpl1Key; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · intro x hx
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hVP, hVS, hVO, hAdv⟩
    · intro x hx
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨hVP, hVS, hVO, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · rfl
      · exact hAdv e he'
  | sendOPK u i bnd m0 m1 =>
    apply h_from_proj
    unfold pqxdhAuthSimImpl1Key; dsimp only
    split
    · exact PreservesAt.pure _ _ _
    · exact runAuthSendSim_pres_proj S P (.sendOPK u i) u bnd m0 m1 st
  | sendNoOPK u i bnd m0 m1 =>
    apply h_from_proj
    unfold pqxdhAuthSimImpl1Key; dsimp only
    split
    · exact PreservesAt.pure _ _ _
    · exact runAuthSendSim_pres_proj S P (.sendNoOPK u i) u bnd m0 m1 st
  | recvNoOPK k j l msg =>
    exact h_from_proj _ (pqxdhAuthSimImpl_recvNoOPK_pres_proj1Key S P k j l msg st)
  | roQuery _ | roRootQuery _ _ | revealDhSecrets =>
    apply h_from_proj
    unfold pqxdhAuthSimImpl1Key pqxdhAuthImpl1KeyG; dsimp only; prove_preserves_at

noncomputable def runAuthWithProv1Key (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthWithProvImpl1Key S P prov
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalSt)

@[simp]
theorem runAuthWithProv_checkBundleProvenance1Key (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    runAuthWithProv1Key (checkBundleProvenance P) S P A = runAuthSim1Key true true S P A := by
  unfold runAuthWithProv1Key runAuthSim1Key
  rw [pqxdhAuthWithProvImpl1Key_checkBundleProvenance, SignalPqxdh.pqxdhAuthImpl1KeyG_true_true]

end Proofs.SignalPqxdh.Security
