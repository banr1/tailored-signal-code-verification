/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.CollisionsC
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key EC collision step bound

One-key (`pqxdhAuthImpl1KeyG`) counterpart of the per-query EC public-key collision step bound
`pqxdhAuthImpl_ec_step` from `Collisions`.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

theorem pqxdhAuthImpl_ec_step1Key (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (st : AuthState S) (s1 s2 : Nat)
    (hV : ValidAuthEc S P st) :
    (∀ x ∈ support ((pqxdhAuthImpl1KeyG useRo checkAuth S P q).run st), ValidAuthEc S P x.2) ∧
    probExpect ((pqxdhAuthImpl1KeyG useRo checkAuth S P q).run st)
      (fun x => ecPairPotential P (ecTaggedAuth S P x.2) s1 s2) ≤
      ecPairPotential P (ecTaggedAuth S P st) s1 s2 := by
  let proj := fun s : AuthState S =>
    (s.principals, s.spkBundles, s.opkEntries, s.sessions, s.usedSendSessions)
  have h_from_proj : ∀ s : AuthState S, proj s = proj st →
      ValidAuthEc S P s ∧ ecTaggedAuth S P s = ecTaggedAuth S P st := by
    intro s hs
    have hp : s.principals = st.principals := congrArg Prod.fst hs
    have hsb : s.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) hs
    have hop : s.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hs
    have hss : s.sessions = st.sessions := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) hs
    have hus : s.usedSendSessions = st.usedSendSessions :=
      congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) hs
    refine ⟨?_, ?_⟩
    · unfold ValidAuthEc ValidEcLists sessPksAuth at hV ⊢
      rw [hp, hsb, hop, hss, hus]; exact hV
    · unfold ecTaggedAuth sessPksAuth; rw [hp, hsb, hop, hss]
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hUsed⟩
  cases q with
  | initPrin u =>
    unfold pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨secIKA0, _, rfl⟩
        exact ⟨⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hVSess⟩, hUsed⟩
      · simp only [probExpect_bind, probExpect_pure]
        have hNotIn := (validPrincipals_cons S u
          { secIKA0 := [], ikAPk := [], secIKAsign := [], ikSignPk := [], corrupted := false }
          st.principals hVP hFresh).2
        exact probExpect_ecTaggedFromLists_cons_prin_le S P hP u
          st.principals st.spkBundles st.opkEntries (sessPksAuth S P st) hNotIn
          (fun sk => {
            secIKA0 := sk, ikAPk := P.x25519Base sk,
            secIKAsign := sk, ikSignPk := P.x25519Base sk, corrupted := false })
          (fun _ => rfl) s1 s2
    · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
      hUsed]
  | corruptIK u =>
    unfold pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
          hUsed]
    | some p =>
      rcases p with ⟨_, entry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, probExpect_pure]
      have h_corr := validPrincipals_map_corrupted S P u.val st.principals hVP
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact ⟨⟨h_corr.1, hVS, hVO, hVSess⟩, hUsed⟩
      · unfold ecTaggedAuth ecTaggedFromLists
        dsimp only [sessPksAuth]
        rw [h_corr.2]
  | genSPK u j =>
    unfold pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO,
            hVSess, hUsed]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
          rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
          exact ⟨⟨hVP, (validSpkBundles_cons S u j _ st.spkBundles hVS hFresh).1, hVO, hVSess⟩,
              hUsed⟩
        · simp only [probExpect_bind, probExpect_pure]
          rw [probExpect_swap sampleScalar32 sampleRandom64]
          apply probExpect_const_le_of_support; intro rSpk _
          rw [probExpect_swap sampleScalar32 (sampleKemKeyGen P)]
          apply probExpect_const_le_of_support; rintro ⟨pqspkPk, pqspkSk⟩ _
          rw [probExpect_swap sampleScalar32 sampleRandom64]
          apply probExpect_const_le_of_support; intro rPq _
          have hNotIn := (validSpkBundles_cons S u j
            { spkSk := [], spkPk := [], spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := [] }
            st.spkBundles hVS hFresh).2
          exact probExpect_ecTaggedFromLists_cons_spk_le S P hP u j
            st.principals st.spkBundles st.opkEntries (sessPksAuth S P st) hVP hNotIn
            (fun spkSk => {
              spkSk := spkSk, spkPk := P.x25519Base spkSk,
              spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base spkSk)) rSpk,
              pqspkSk := pqspkSk, pqspkPk := pqspkPk,
              pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq })
            (fun _ => rfl) s1 s2
    · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
      hUsed]
  | genOPK u j o =>
    unfold pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨opkSk, _, rfl⟩
        exact ⟨⟨hVP, hVS, (validOpkEntries_cons S u j o _ st.opkEntries hVO hFresh).1, hVSess⟩,
            hUsed⟩
      · simp only [probExpect_bind, probExpect_pure]
        have hNotIn := (validOpkEntries_cons S u j o
          { opkSk := [], opkPk := [], consumed := false }
          st.opkEntries hVO hFresh).2
        exact probExpect_ecTaggedFromLists_cons_opk_le S P hP u j o
          st.principals st.spkBundles st.opkEntries (sessPksAuth S P st) hVP hVS hNotIn
          (fun opkSk => { opkSk := opkSk, opkPk := P.x25519Base opkSk, consumed := false })
          (fun _ => rfl) s1 s2
    · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
      hUsed]
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runAuthSend_ec_step useRo S P hP (.sendOPK u i) trivial u bundle m0 m1 st s1 s2 ⟨⟨hVP,
          hVS, hVO, hVSess⟩, hUsed⟩
    · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
      hUsed]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthImpl1KeyG; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runAuthSend_ec_step useRo S P hP (.sendNoOPK u i) trivial u bundle m0 m1 st s1 s2
          ⟨⟨hVP, hVS, hVO, hVSess⟩, hUsed⟩
    · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
      hUsed]
  | recvOPK k j o msg =>
    let projOpk := fun s : AuthState S =>
      (s.principals, s.spkBundles,
       s.opkEntries.map (fun (idx, o) => (ecOpkSlotIdx S idx, P.pow8 o.opkPk)),
       s.opkEntries.map Prod.fst,
       s.sessions, s.usedSendSessions)
    have h_step1 : ∀ (s : AuthState S) w u t so ro rc rrc,
        projOpk { s with
          hasWonAuth := w,
          opkEntries := s.opkEntries.map (fun (idx, e) =>
            if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e)),
          usedRecvOPK := u, seenKyberBaseKeys := t, sentOPKEvents := so,
          recvdOPKEvents := ro, roCache := rc, rootRoCache := rrc } = projOpk s := by
      intro s w u t so ro rc rrc
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl)))) <;> (
        dsimp only [projOpk]
        rw [List.map_map]
        refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
        simp only [Function.comp_def]; split_ifs <;> rfl)
    have hp : PreservesAt projOpk st (pqxdhAuthImpl1KeyG useRo checkAuth S P (.recvOPK k j o msg)) := by
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; exact h_step1 _ _ _ _ _ _ _ _)
        | split)
    suffices h_supp : ∀ x ∈ support ((pqxdhAuthImpl1KeyG useRo checkAuth S P (.recvOPK k j o msg)).run
        st),
        ValidAuthEc S P x.2 ∧ ecTaggedAuth S P x.2 = ecTaggedAuth S P st by
      refine ⟨fun x hx => (h_supp x hx).1, ?_⟩
      exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_supp x hx).2])
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp3 : x.2.opkEntries.map (fun (idx, o) => (ecOpkSlotIdx S idx, P.pow8 o.opkPk)) =
        st.opkEntries.map (fun (idx, o) => (ecOpkSlotIdx S idx, P.pow8 o.opkPk)) :=
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp4 : x.2.opkEntries.map Prod.fst = st.opkEntries.map Prod.fst :=
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp5 : sessPksAuth S P x.2 = sessPksAuth S P st := by
      have hsess : x.2.sessions = st.sessions :=
        congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
      unfold sessPksAuth; rw [hsess]
    have hp6 : x.2.usedSendSessions = st.usedSendSessions :=
      congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    refine ⟨⟨⟨hp1 ▸ hVP, hp2 ▸ hVS, ⟨?_, ?_⟩, hp5 ▸ hVSess⟩, ?_⟩, ?_⟩
    · intro e he
      have he_fst : e.1 ∈ st.opkEntries.map Prod.fst := by
        rw [← hp4]; exact List.mem_map_of_mem he
      rw [List.mem_map] at he_fst
      rcases he_fst with ⟨e', he', heq⟩
      rw [← heq]; exact hVO.1 e' he'
    · have h_slot : x.2.opkEntries.map (fun e => ecOpkSlotIdx S e.1) =
          st.opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map (ecOpkSlotIdx S)) hp4
      rw [h_slot]; exact hVO.2
    · rw [hp6, hp5, hUsed]
    · unfold ecTaggedAuth ecTaggedFromLists
      rw [hp1, hp2, hp3, hp5]
  | recvNoOPK k j l msg =>
    have hp : PreservesAt proj st (pqxdhAuthImpl1KeyG useRo checkAuth S P (.recvNoOPK k j l msg)) := by
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | roQuery secrets =>
    have hp : PreservesAt proj st (pqxdhAuthImpl1KeyG useRo checkAuth S P (.roQuery secrets)) := by
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | roRootQuery rk dh =>
    have hp : PreservesAt proj st (pqxdhAuthImpl1KeyG useRo checkAuth S P (.roRootQuery rk dh)) := by
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | revealDhSecrets =>
    have hp : PreservesAt proj st (pqxdhAuthImpl1KeyG useRo checkAuth S P .revealDhSecrets) := by
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | registerKey sk =>
    have hp : PreservesAt proj st (pqxdhAuthImpl1KeyG useRo checkAuth S P (.registerKey sk)) := by
      unfold pqxdhAuthImpl1KeyG; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | (split; try dsimp only))
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])

end SignalPqxdh.Security

namespace SignalPqxdh

end SignalPqxdh
