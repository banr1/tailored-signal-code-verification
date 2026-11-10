/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.CollisionsC
import VCVio.EvalDist.Monad.Basic

@[expose] public section

/-!
# EC and KEM Public-Key Collision Bounds

Completes the EC public-key collision supermartingale bounds for `KeyInd` and `Auth` and derives
the closed-form birthday bounds for the X25519 (`G0 → G0_1`) and KEM (`G2 → G2_1`)
collision-elimination hops.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

def ValidPrincipalsSk (P : Primitives) (principals : List (Nat × PrincipalEntry)) : Prop :=
  ∀ e ∈ principals, e.2.secIKA0.length = 32 ∧ e.2.ikAPk = P.x25519Base e.2.secIKA0

def ValidAdvKeysSk (P : Primitives) (advKeys : List (Bytes × Bytes)) : Prop :=
  ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1

def ValidKeyIndDh2 (S : Setup) (P : Primitives) (st : KeyIndState S) : Prop :=
  ValidKeyIndEc S st ∧
  ValidPrincipalsSk P st.principals ∧
  ValidAdvKeysSk P st.advKeys

theorem validKeyIndDh2_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidKeyIndDh2 S P (KeyIndState.empty S secb) :=
  ⟨validEcLists_nil S,
   fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h)⟩

theorem exists_skB_of_koskBundleOk (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput)
    (hVP_sk : ValidPrincipalsSk P principals)
    (hAdv_sk : ValidAdvKeysSk P advKeys)
    (hKosk : (!koskBundleOk P principals spkBundles opkEntries advKeys bundle) = false) :
    ∃ skB : Bytes, skB.length = 32 ∧ P.pow8 (P.x25519Base skB) = P.pow8 bundle.ikB := by
  have hKosk' : koskBundleOk P principals spkBundles opkEntries advKeys bundle = true := by
    simpa using hKosk
  unfold koskBundleOk at hKosk'
  have hIdOrAdv : (isGameIdKey P principals bundle.ikB ||
    isAdvRegistered P advKeys bundle.ikB) = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hKosk').1).1
  rcases Bool.or_eq_true_iff.mp hIdOrAdv with hId | hAdv
  · unfold isGameIdKey findHonestPrincipal at hId
    rcases Option.isSome_iff_exists.mp hId with ⟨⟨idx, entry⟩, hFind⟩
    have hMem := List.mem_of_find?_eq_some hFind
    have hPow := beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hFind).1
    rcases hVP_sk (idx, entry) hMem with ⟨hLen, hPk⟩
    exact ⟨entry.secIKA0, hLen, by rw [← hPk, hPow]⟩
  · unfold isAdvRegistered at hAdv
    rcases List.any_eq_true.mp hAdv with ⟨⟨sk, pk'⟩, hMem, hBeq⟩
    have hPow := beq_iff_eq.mp hBeq
    rcases hAdv_sk (sk, pk') hMem with ⟨hLen, hPk⟩
    exact ⟨sk, hLen, by rw [← hPk, hPow]⟩

theorem runKeyIndInitiate_dh2_step (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (sid : SessionId S) (hSend : IsSendSessionId S sid) (u : Fin S.N_id) (bundle :
        PreKeyBundleInput)
    (st : KeyIndState S) (s1 s2 : Nat)
    (hV : ValidKeyIndDh2 S P st) :
    (∀ x ∈ support ((runKeyIndInitiate useRo S P sid u bundle).run st), ValidKeyIndDh2 S P x.2) ∧
    probExpect ((runKeyIndInitiate useRo S P sid u bundle).run st)
      (fun x => dh2UpperPairPotential (dh2TaggedKeyInd S P x.2) s1 s2) ≤
      dh2UpperPairPotential (dh2TaggedKeyInd S P st) s1 s2 := by
  have hEcStep := (runKeyIndInitiate_ec_step useRo S P hP sid hSend u bundle st 0 0 hV.1).1
  have hp_keys : PreservesAt (fun s : KeyIndState S => (s.principals, s.advKeys)) st
      (runKeyIndInitiate useRo S P sid u bundle) :=
    PreservesAt.runKeyIndInitiate _ st useRo P sid u bundle (fun _ _ => rfl)
  refine ⟨fun x hx => ?_, ?_⟩
  · have h_eq := hp_keys x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.advKeys = st.advKeys := congrArg Prod.snd h_eq
    exact ⟨hEcStep x hx, hp1 ▸ hV.2.1, hp2 ▸ hV.2.2⟩
  · rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hVP_sk, hAdv_sk⟩
    unfold runKeyIndInitiate; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.sessions.any (fun e => e.sid == sid)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hFresh' : ((sessPksKeyInd S st).map Prod.fst).any (fun s => s == sid) = false := by
        simpa [sessPksKeyInd, List.any_map, Function.comp_def] using hFresh
      have hCons :=
          validSessionIds_cons S sid ((sessPksKeyInd S st).map Prod.fst) hSend hVSess hFresh'
      have hNotInDh2 : ecSessSlotIdx S sid ∉ (dh2TaggedKeyInd S P st).map Prod.fst := by
        rw [map_fst_dh2TaggedKeyInd]; exact hCons.2
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp [StateT.run_pure, probExpect_pure]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        cases hKosk : !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_self, bind_assoc, pure_bind]
          rcases exists_skB_of_koskBundleOk P st.principals st.spkBundles st.opkEntries
            st.advKeys bundle hVP_sk hAdv_sk hKosk with ⟨skB, hSkB, hPowB⟩
          cases !(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC bundle.spkB)
              bundle.spkSig &&
              P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                  bundle.pqspkSig)
          · simp only [Bool.false_eq_true, ↓reduceIte, probExpect_bind]
            rw [probExpect_swap sampleScalar32 sampleCoins32]
            apply probExpect_const_le_of_support; intro kemCoins _
            cases P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              simp only [StateT.run_pure, probExpect_pure]
              exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
            | some val =>
              rcases val with ⟨ss, kemCt⟩
              dsimp only
              refine le_trans (probExpect_mono_of_support sampleScalar32 _
                (fun ekASk => dh2UpperPairPotential
                  ((ecSessSlotIdx S sid,
                      P.x25519 ekASk bundle.ikB) :: dh2TaggedKeyInd S P st) s1 s2) ?_) ?_
              · intro ekASk _
                apply probExpect_const_le_of_support; intro x hx
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
                rcases hx with ⟨⟨drKeyReal, roCache'⟩, _, hx⟩
                split at hx <;>
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
                swap; rcases hx with ⟨drKeyRand, _, hx⟩; all_goals
                cases hHon : findHonestPrincipal P st.principals bundle.ikB <;> (
                  rw [hHon] at hx
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
                  subst hx
                  simp [dh2TaggedKeyInd, sessDh2sKeyInd])
              · exact probExpect_dh2UpperPairPotential_cons_fresh_le P hP
                  (dh2TaggedKeyInd S P st) (ecSessSlotIdx S sid) bundle.ikB skB hSkB hPowB s1 s2
                      hNotInDh2
          · simp only [↓reduceIte, StateT.run_pure, probExpect_bind, probExpect_pure]
            apply probExpect_const_le_of_support; intro _ _
            exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
        · simp [StateT.run_pure, probExpect_pure]
    · simp [StateT.run_pure, probExpect_pure]

theorem pqxdhKeyIndImpl_dh2_step (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : KeyIndQuery S) (st : KeyIndState S) (s1 s2 : Nat)
    (hV : ValidKeyIndDh2 S P st) :
    (∀ x ∈ support ((pqxdhKeyIndImpl useRo S P q).run st), ValidKeyIndDh2 S P x.2) ∧
    probExpect ((pqxdhKeyIndImpl useRo S P q).run st)
      (fun x => dh2UpperPairPotential (dh2TaggedKeyInd S P x.2) s1 s2) ≤
      dh2UpperPairPotential (dh2TaggedKeyInd S P st) s1 s2 := by
  have hEcStep := (pqxdhKeyIndImpl_ec_step useRo S P hP q st 0 0 hV.1).1
  let proj := fun s : KeyIndState S => (s.principals, s.advKeys, s.sessions)
  have h_from_proj : ∀ s : KeyIndState S, proj s = proj st →
      ValidPrincipalsSk P s.principals ∧ ValidAdvKeysSk P s.advKeys ∧
      dh2TaggedKeyInd S P s = dh2TaggedKeyInd S P st := by
    intro s hs
    have hp1 : s.principals = st.principals := congrArg Prod.fst hs
    have hp2 : s.advKeys = st.advKeys := congrArg (Prod.fst ∘ Prod.snd) hs
    have hp3 : s.sessions = st.sessions := congrArg (Prod.snd ∘ Prod.snd) hs
    refine ⟨hp1 ▸ hV.2.1, hp2 ▸ hV.2.2, ?_⟩
    unfold dh2TaggedKeyInd sessDh2sKeyInd; rw [hp3]
  let projDh2 := fun s : KeyIndState S => (s.principals, s.advKeys, dh2TaggedKeyInd S P s)
  have h_from_projDh2 : ∀ s : KeyIndState S, projDh2 s = projDh2 st →
      ValidPrincipalsSk P s.principals ∧ ValidAdvKeysSk P s.advKeys ∧
      dh2TaggedKeyInd S P s = dh2TaggedKeyInd S P st := by
    intro s hs
    have hp1 : s.principals = st.principals := congrArg Prod.fst hs
    have hp2 : s.advKeys = st.advKeys := congrArg (Prod.fst ∘ Prod.snd) hs
    have hp3 : dh2TaggedKeyInd S P s = dh2TaggedKeyInd S P st := congrArg (Prod.snd ∘ Prod.snd) hs
    exact ⟨hp1 ▸ hV.2.1, hp2 ▸ hV.2.2, hp3⟩
  cases q with
  | initPrin u =>
    refine ⟨fun x hx => ⟨hEcStep x hx, ?_⟩, ?_⟩
    · unfold pqxdhKeyIndImpl at hx; dsimp only at hx
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
      cases hFresh : st.principals.any (fun (idx, _) => idx == u.val)
      · rw [hFresh] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨secIKA0, hSec0, secIKAsign, _, rfl⟩
        refine ⟨?_, hV.2.2⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | hmem
        · exact ⟨length_of_mem_support_sampleScalar32_coll hSec0, rfl⟩
        · exact hV.2.1 e hmem
      · rw [hFresh] at hx
        simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact ⟨hV.2.1, hV.2.2⟩
    · unfold pqxdhKeyIndImpl; dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases st.principals.any (fun (idx, _) => idx == u.val)
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          probExpect_bind, probExpect_pure]
        apply probExpect_const_le_of_support; intro _ _
        exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
      · simp [StateT.run_pure, probExpect_pure]
  | corruptIK u =>
    refine ⟨fun x hx => ⟨hEcStep x hx, ?_⟩, ?_⟩
    · unfold pqxdhKeyIndImpl at hx; dsimp only at hx
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
      cases hFind : st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hFind] at hx
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact ⟨hV.2.1, hV.2.2⟩
      | some p =>
        rcases p with ⟨_, entry⟩
        rw [hFind] at hx; dsimp only at hx
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨?_, hV.2.2⟩
        intro e he
        rw [List.mem_map] at he
        rcases he with ⟨⟨idx, e0⟩, he0, heq⟩
        have h0 := hV.2.1 (idx, e0) he0
        dsimp only at heq
        split_ifs at heq <;> (subst heq; exact h0)
    · unfold pqxdhKeyIndImpl; dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, probExpect_pure]
      | some p =>
        rcases p with ⟨_, entry⟩
        dsimp only
        simp [StateT.run_set, probExpect_pure, dh2TaggedKeyInd, sessDh2sKeyInd]
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_dh2_step useRo S P hP (.sendOPK u i) trivial u bundle st s1 s2 hV
    · simp [StateT.run_pure, probExpect_pure, ValidKeyIndDh2, hV.1, hV.2.1, hV.2.2]
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_dh2_step useRo S P hP (.sendNoOPK u i) trivial u bundle st s1 s2 hV
    · simp [StateT.run_pure, probExpect_pure, ValidKeyIndDh2, hV.1, hV.2.1, hV.2.2]
  | testSession sid =>
    have h_step : ∀ (s : KeyIndState S),
        projDh2 { s with sessions := s.sessions.map (fun e =>
          if e.sid == sid then { e with tested := true } else e) } = projDh2 s := by
      intro s
      refine Prod.ext rfl (Prod.ext rfl ?_)
      simp only [projDh2, dh2TaggedKeyInd, sessDh2sKeyInd, List.map_map]
      refine List.map_congr_left (fun e _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projDh2 st (pqxdhKeyIndImpl useRo S P (.testSession sid)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _)
        | (split; try dsimp only))
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_projDh2 x.2 (hp x hx)).1, (h_from_projDh2 x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx =>
        by rw [(h_from_projDh2 x.2 (hp x hx)).2.2])
  | revealSessionKey sid =>
    have h_step : ∀ (s : KeyIndState S),
        projDh2 { s with sessions := s.sessions.map (fun e =>
          if e.sid == sid then { e with revealed := true } else e) } = projDh2 s := by
      intro s
      refine Prod.ext rfl (Prod.ext rfl ?_)
      simp only [projDh2, dh2TaggedKeyInd, sessDh2sKeyInd, List.map_map]
      refine List.map_congr_left (fun e _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projDh2 st (pqxdhKeyIndImpl useRo S P (.revealSessionKey sid)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _)
        | (split; try dsimp only))
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_projDh2 x.2 (hp x hx)).1, (h_from_projDh2 x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx =>
        by rw [(h_from_projDh2 x.2 (hp x hx)).2.2])
  | registerKey sk =>
    refine ⟨fun x hx => ⟨hEcStep x hx, ?_⟩, ?_⟩
    · unfold pqxdhKeyIndImpl registerAdvKey at hx; dsimp only at hx
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
      by_cases hLen : (sk.length != 32) = true
      · rw [hLen] at hx
        simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        subst hx; exact ⟨hV.2.1, hV.2.2⟩
      · rw [Bool.not_eq_true] at hLen
        rw [hLen] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hx
        subst hx
        have hSkLen : sk.length = 32 := by
          simpa [bne_iff_ne] using hLen
        refine ⟨hV.2.1, ?_⟩
        intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hmem
        · exact ⟨hSkLen, rfl⟩
        · exact hV.2.2 kv hmem
    · unfold pqxdhKeyIndImpl registerAdvKey; dsimp only
      simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hLen : (sk.length != 32) = true
      · simp [hLen, StateT.run_pure, probExpect_pure]
      · simp only [Bool.not_eq_true] at hLen
        simp [hLen, StateT.run_set, probExpect_pure, dh2TaggedKeyInd, sessDh2sKeyInd]
  | genSPK u j =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.genSPK u j)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | (split; try dsimp only))
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_proj x.2 (hp x hx)).1, (h_from_proj x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2.2])
  | genOPK u j o =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.genOPK u j o)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | (split; try dsimp only))
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_proj x.2 (hp x hx)).1, (h_from_proj x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2.2])
  | acceptOPK k j o hdr =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.acceptOPK k j o hdr)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | (split; try dsimp only))
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_proj x.2 (hp x hx)).1, (h_from_proj x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2.2])
  | acceptNoOPK k j l hdr =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.acceptNoOPK k j l hdr)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | (split; try dsimp only))
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_proj x.2 (hp x hx)).1, (h_from_proj x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2.2])
  | roQuery secrets =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.roQuery secrets)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | split)
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_proj x.2 (hp x hx)).1, (h_from_proj x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2.2])
  | revealDhSecrets =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P .revealDhSecrets) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | split)
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_proj x.2 (hp x hx)).1, (h_from_proj x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2.2])
  | revealSpkSk u j =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.revealSpkSk u j)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | (split; try dsimp only))
    refine ⟨fun x hx =>
        ⟨hEcStep x hx, (h_from_proj x.2 (hp x hx)).1, (h_from_proj x.2 (hp x hx)).2.1⟩, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2.2])

def hasKeyIndEcPairCollAt (S : Setup) (P : Primitives) (st : KeyIndState S) (s1 s2 : Nat) : Bool :=
  if s2 < s1 then
    hasTaggedPairCollAt (ecTaggedKeyInd S P st) s1 s2
  else if S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2 then
    hasUpperTaggedPairCollAt (dh2TaggedKeyInd S P st) s1 s2
  else
    false

noncomputable def ecKeyIndPairPotential (S : Setup) (P : Primitives)
    (st : KeyIndState S) (s1 s2 : Nat) : ℝ≥0∞ :=
  if s2 < s1 then
    ecPairPotential P (ecTaggedKeyInd S P st) s1 s2
  else if s1 < s2 then
    dh2UpperPairPotential (dh2TaggedKeyInd S P st) s1 s2
  else
    0

theorem evalDist_hasKeyIndEcPairCollAt_le_potential (S : Setup) (P : Primitives)
    (st : KeyIndState S) (s1 s2 : Nat) :
    𝒟[(pure (hasKeyIndEcPairCollAt S P st s1 s2) : ProbComp Bool)] {true} ≤
      ecKeyIndPairPotential S P st s1 s2 := by
  unfold hasKeyIndEcPairCollAt ecKeyIndPairPotential
  by_cases h1 : s2 < s1
  · simp only [h1, ↓reduceIte]
    exact evalDist_hasTaggedPairCollAt_le_potential P (ecTaggedKeyInd S P st) s1 s2
  · simp only [h1, ↓reduceIte]
    by_cases h2 : S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2
    · simp only [h2, ↓reduceIte]
      exact evalDist_hasUpperTaggedPairCollAt_le_potential (dh2TaggedKeyInd S P st) s1 s2
    · simp [h2]

theorem ecKeyIndPairPotential_empty_le (S : Setup) (P : Primitives) (secb : Bool) (s1 s2 : Nat) :
    ecKeyIndPairPotential S P (KeyIndState.empty S secb) s1 s2 ≤ ENNReal.ofReal Pfixed_pk_ec := by
  unfold ecKeyIndPairPotential
  split_ifs
  · exact ecPairPotential_nil_le P s1 s2
  · exact dh2UpperPairPotential_nil_le s1 s2
  · simp

theorem pqxdhKeyIndImpl_combined_ec_step (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : KeyIndQuery S) (st : KeyIndState S) (s1 s2 : Nat)
    (hV : ValidKeyIndDh2 S P st) :
    probExpect ((pqxdhKeyIndImpl useRo S P q).run st)
      (fun x => ecKeyIndPairPotential S P x.2 s1 s2) ≤
      ecKeyIndPairPotential S P st s1 s2 := by
  unfold ecKeyIndPairPotential
  split_ifs
  · exact (pqxdhKeyIndImpl_ec_step useRo S P hP q st s1 s2 hV.1).2
  · exact (pqxdhKeyIndImpl_dh2_step useRo S P hP q st s1 s2 hV).2
  · simp [probExpect_const]

theorem simulateQ_valid_and_ecKeyIndPairPotential_le (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (s1 s2 : Nat)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) (st : KeyIndState S)
    (hV : ValidKeyIndDh2 S P st) :
    (∀ x ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT
        (KeyIndState S) ProbComp) +
        pqxdhKeyIndImpl useRo S P) oa).run st), ValidKeyIndDh2 S P x.2) ∧
    probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState
        S) ProbComp) +
        pqxdhKeyIndImpl useRo S P) oa).run st)
      (fun x => ecKeyIndPairPotential S P x.2 s1 s2) ≤
      ecKeyIndPairPotential S P st s1 s2 := by
  let fullImpl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl useRo S P
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    refine ⟨?_, ?_⟩
    · intro x hx
      simp [StateT.run_pure] at hx
      rcases hx with ⟨_, rfl⟩
      exact hV
    · simp [StateT.run_pure, probExpect_pure]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      have hrun :
          (simulateQ fullImpl (liftM (OracleSpec.query (Sum.inl uq)) >>= oa)).run st =
          (do let u ← liftM (unifSpec.query uq); (simulateQ fullImpl (oa u)).run st) := by
        simp [fullImpl, simulateQ_bind, QueryImpl.liftTarget, StateT.run_bind, StateT.run_monadLift]
      rw [hrun]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨u, _, hx⟩
        exact (ih u st hV).1 x hx
      · rw [probExpect_bind]
        exact probExpect_const_le_of_support _ _ _ (fun u _ => (ih u st hV).2)
    | inr gq =>
      have hrun :
          (simulateQ fullImpl (liftM (OracleSpec.query (Sum.inr gq)) >>= oa)).run st =
          (do
            let y ← (pqxdhKeyIndImpl useRo S P gq).run st
            (simulateQ fullImpl (oa y.1)).run y.2) := by
        simp [fullImpl, simulateQ_bind, StateT.run_bind]
      rw [hrun]
      have hV_step := (pqxdhKeyIndImpl_dh2_step useRo S P hP gq st 0 0 hV).1
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨y, hy, hx⟩
        exact (ih y.1 y.2 (hV_step y hy)).1 x hx
      · rw [probExpect_bind]
        calc probExpect ((pqxdhKeyIndImpl useRo S P gq).run st)
              (fun y => probExpect ((simulateQ fullImpl (oa y.1)).run y.2)
                (fun x => ecKeyIndPairPotential S P x.2 s1 s2))
            ≤ probExpect ((pqxdhKeyIndImpl useRo S P gq).run st)
                (fun y => ecKeyIndPairPotential S P y.2 s1 s2) :=
              probExpect_mono_of_support _ _ _ (fun y hy => (ih y.1 y.2 (hV_step y hy)).2)
          _ ≤ ecKeyIndPairPotential S P st s1 s2 :=
              pqxdhKeyIndImpl_combined_ec_step useRo S P hP gq st s1 s2 hV

theorem hasEcPkCollisionKeyInd_imp_any_double_range (S : Setup) (P : Primitives)
    (st : KeyIndState S) (hV : ValidKeyIndDh2 S P st)
    (hdup : hasEcPkCollisionKeyInd P st = true) :
    ((List.range S.N_dh).any (fun s1 =>
      (List.range S.N_dh).any (fun s2 =>
        hasKeyIndEcPairCollAt S P st s1 s2))) = true := by
  unfold hasEcPkCollisionKeyInd at hdup
  rcases Bool.or_eq_true_iff.mp hdup with hEc | hDh2
  · rw [← map_snd_ecTaggedKeyInd S P st] at hEc
    have hVTag := validTaggedPks_ecTaggedFromLists S P
      st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st) hV.1
    have hAny := hasDuplicateBytes_map_snd_imp_any_double_range S.N_dh (ecTaggedKeyInd S P st)
        hVTag hEc
    simp only [List.any_eq_true, List.mem_range] at hAny ⊢
    rcases hAny with ⟨s1, hs1, s2, hs2, hColl⟩
    have hlt : s2 < s1 := of_decide_eq_true (Bool.and_eq_true_iff.mp hColl).1
    refine ⟨s1, hs1, s2, hs2, ?_⟩
    unfold hasKeyIndEcPairCollAt
    simp [hlt, hColl]
  · rw [← map_snd_dh2TaggedKeyInd S P st] at hDh2
    have hVTag := validTaggedPks_dh2TaggedKeyInd S P st hV.1.2.2.2
    have hAny := hasDuplicateBytes_map_snd_imp_any_upper_double_range S.N_dh (dh2TaggedKeyInd S P
        st) hVTag hDh2
    simp only [List.any_eq_true, List.mem_range] at hAny ⊢
    rcases hAny with ⟨s1, hs1, s2, hs2, hColl⟩
    have hlt : s1 < s2 := of_decide_eq_true (Bool.and_eq_true_iff.mp hColl).1
    have hnot : ¬ (s2 < s1) := by omega
    have hge : S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 :=
      ge_offset_of_hasUpperTaggedPairCollAt_dh2TaggedKeyInd S P st hColl
    refine ⟨s1, hs1, s2, hs2, ?_⟩
    unfold hasKeyIndEcPairCollAt
    simp [hnot, hge, hlt, hColl]

theorem ecCollProbKeyInd_le_bound (useRo : Bool) (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    ecCollProbKeyInd useRo S P A ≤
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  unfold ecCollProbKeyInd
  let fullImpl :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl useRo S P
  let runSim := runKeyIndSim useRo S P A
  have hSim := fun s1 s2 secb =>
    simulateQ_valid_and_ecKeyIndPairPotential_le useRo S P hCWF s1 s2 A.run
      (KeyIndState.empty S secb) (validKeyIndDh2_empty S P secb)
  have hV_runSim : ∀ x ∈ support runSim, ValidKeyIndDh2 S P x.2.2 := by
    intro x hx
    simp only [runSim, runKeyIndSim, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨secb, _, ⟨b', finalSt⟩, hmem, rfl⟩
    exact (hSim 0 0 secb).1 (b', finalSt) hmem
  have hPair_base : ∀ s1 s2 : Nat,
      (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true}).toReal ≤
      Pfixed_pk_ec := by
    intro s1 s2
    have h_enn :
        𝒟[runSim >>= fun (_, _, finalSt) =>
          pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true} ≤
        ENNReal.ofReal Pfixed_pk_ec := by
      rw [evalDist_bind_true_eq_probExpect]
      simp only [runSim, runKeyIndSim, probExpect_bind, probExpect_pure]
      apply probExpect_const_le_of_support; intro secb _
      calc probExpect ((simulateQ fullImpl A.run).run (KeyIndState.empty S secb))
            (fun x => 𝒟[(pure (hasKeyIndEcPairCollAt S P x.2 s1 s2) : ProbComp Bool)] {true})
          ≤ probExpect ((simulateQ fullImpl A.run).run (KeyIndState.empty S secb))
              (fun x => ecKeyIndPairPotential S P x.2 s1 s2) :=
            probExpect_mono_of_support _ _ _ (fun x _ =>
              evalDist_hasKeyIndEcPairCollAt_le_potential S P x.2 s1 s2)
        _ ≤ ecKeyIndPairPotential S P (KeyIndState.empty S secb) s1 s2 := (hSim s1 s2 secb).2
        _ ≤ ENNReal.ofReal Pfixed_pk_ec := ecKeyIndPairPotential_empty_le S P secb s1 s2
    have hreal := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr h_enn
    rwa [ENNReal.toReal_ofReal pfixed_pk_ec_nonneg] at hreal
  have hPair_le : ∀ s1 s2 : Nat,
      (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true}).toReal ≤
      if s2 < s1 then Pfixed_pk_ec
      else if S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2 then Pfixed_pk_ec
      else 0 := by
    intro s1 s2
    by_cases h1 : s2 < s1
    · simp only [h1, ↓reduceIte]; exact hPair_base s1 s2
    · simp only [h1, ↓reduceIte]
      by_cases h2 : S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2
      · simp only [h2, and_self, ↓reduceIte]; exact hPair_base s1 s2
      · have h0 : 𝒟[runSim >>= fun (_, _, finalSt) =>
            pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true} ≤ 0 := by
          rw [evalDist_bind_true_eq_probExpect]
          refine probExpect_const_le_of_support _ _ 0 (fun _ _ => ?_)
          simp [hasKeyIndEcPairCollAt, h1, h2]
        simp only [le_antisymm h0 zero_le, h2, ↓reduceIte, ENNReal.toReal_zero, le_rfl]
  calc (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasEcPkCollisionKeyInd P finalSt)] {true}).toReal
      ≤ (𝒟[runSim >>= fun (_, _, finalSt) =>
          pure ((List.range S.N_dh).any (fun s1 =>
            (List.range S.N_dh).any (fun s2 =>
              hasKeyIndEcPairCollAt S P finalSt s1 s2)))] {true}).toReal :=
        toReal_bind_bool_mono_of_support runSim _ _ (fun x hx hdup =>
          hasEcPkCollisionKeyInd_imp_any_double_range S P x.2.2 (hV_runSim x hx) hdup)
    _ ≤ ∑ s1 ∈ Finset.range S.N_dh,
          (𝒟[runSim >>= fun (_, _, finalSt) =>
            pure ((List.range S.N_dh).any (fun s2 =>
              hasKeyIndEcPairCollAt S P finalSt s1 s2))] {true}).toReal :=
        toReal_any_range_le_sum runSim S.N_dh
          (fun s1 x => (List.range S.N_dh).any (fun s2 => hasKeyIndEcPairCollAt S P x.2.2 s1 s2))
    _ ≤ ∑ s1 ∈ Finset.range S.N_dh,
          ∑ s2 ∈ Finset.range S.N_dh,
            (𝒟[runSim >>= fun (_, _, finalSt) =>
              pure (hasKeyIndEcPairCollAt S P finalSt s1 s2)] {true}).toReal :=
        Finset.sum_le_sum (fun s1 _ =>
          toReal_any_range_le_sum runSim S.N_dh
            (fun s2 x => hasKeyIndEcPairCollAt S P x.2.2 s1 s2))
    _ ≤ ∑ s1 ∈ Finset.range S.N_dh,
          ∑ s2 ∈ Finset.range S.N_dh,
            (if s2 < s1 then Pfixed_pk_ec
             else if S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2 then Pfixed_pk_ec
             else 0) :=
        Finset.sum_le_sum (fun s1 _ => Finset.sum_le_sum (fun s2 _ => hPair_le s1 s2))
    _ = ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
        rw [sum_keyIndEcGrid_const]
        unfold Pfixed_pk_ec
        ring

/-! ## `Auth` EC collision bound -/

def sessPksAuth (S : Setup) (P : Primitives) (st : AuthState S) : List (SessionId S × Bytes) :=
  st.sessions.map (fun s => (s.sid, P.x25519Base s.ekASk))

def ecTaggedAuth (S : Setup) (P : Primitives) (st : AuthState S) : List (Nat × Bytes) :=
  ecTaggedFromLists S P st.principals st.spkBundles st.opkEntries (sessPksAuth S P st)

def ValidAuthEc (S : Setup) (P : Primitives) (st : AuthState S) : Prop :=
  ValidEcLists S st.principals st.spkBundles st.opkEntries ((sessPksAuth S P st).map Prod.fst) ∧
  st.usedSendSessions = (sessPksAuth S P st).map Prod.fst

theorem map_snd_ecTaggedAuth (S : Setup) (P : Primitives) (st : AuthState S) :
    (ecTaggedAuth S P st).map Prod.snd = allHonestEcPksAuth P st := by
  unfold ecTaggedAuth ecTaggedFromLists sessPksAuth allHonestEcPksAuth
  simp [HasAuthState.toAuthState, List.map_append, List.map_map, Function.comp_def]

theorem runAuthSend_ec_step (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (sid : SessionId S) (hSend : IsSendSessionId S sid) (u : Fin S.N_id) (bundle :
        PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) (s1 s2 : Nat)
    (hV : ValidAuthEc S P st) :
    (∀ x ∈ support ((runAuthSend useRo S P sid u bundle m0 m1).run st), ValidAuthEc S P x.2) ∧
    probExpect ((runAuthSend useRo S P sid u bundle m0 m1).run st)
      (fun x => ecPairPotential P (ecTaggedAuth S P x.2) s1 s2) ≤
      ecPairPotential P (ecTaggedAuth S P st) s1 s2 := by
  rcases hV with ⟨⟨hVP, hVS, hVO, hVSess⟩, hUsed⟩
  unfold runAuthSend; dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (m0.length != m1.length)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFresh : st.usedSendSessions.contains sid
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hFresh' : ((sessPksAuth S P st).map Prod.fst).any (fun s => s == sid) = false := by
        rw [← hUsed]; revert hFresh; simp; rintro h x hx rfl; exact h hx
      have hCons :=
          validSessionIds_cons S sid ((sessPksAuth S P st).map Prod.fst) hSend hVSess hFresh'
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO,
            hVSess, hUsed]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        refine (let P_goal (m : StateT (AuthState S) ProbComp AuthResponse) :=
          (∀ x ∈ support (m.run st), ValidAuthEc S P x.2) ∧
          probExpect (m.run st) (fun x => ecPairPotential P (ecTaggedAuth S P x.2) s1 s2) ≤
            ecPairPotential P (ecTaggedAuth S P st) s1 s2
          fun {c} [Decidable c] {t e} (he : P_goal e) (ht : P_goal t) =>
            show P_goal (if c then t else e) by split_ifs <;> assumption) ?_ ?_
        · cases !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle
          · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
              monadLift_self, bind_assoc, pure_bind]
            cases hSig : !(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC
                bundle.spkB) bundle.spkSig &&
                P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                    bundle.pqspkSig)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              refine ⟨?_, ?_⟩
              · intro x hx
                simp only [MonadAttach.mem_support_bind] at hx
                rcases hx with ⟨ekASk, _, kemCoins, _, ephASk, _, spqrCoins, _, hx⟩
                cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
                | none =>
                  rw [hEnc] at hx
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
                  subst hx; exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hUsed⟩
                | some val =>
                  rcases val with ⟨ss, kemCt⟩
                  rw [hEnc] at hx; dsimp only at hx
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                    bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
                  rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
                  cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none =>
                    rw [hSpqr] at hx
                    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
                    subst hx; exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hUsed⟩
                  | some spqrVal =>
                    rcases spqrVal with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                    rw [hSpqr] at hx; dsimp only at hx
                    simp only [StateT.run_bind, StateT.run_set, pure_bind] at hx
                    have hx_st : x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
                        x.2.opkEntries = st.opkEntries ∧
                        (sessPksAuth S P x.2).map Prod.fst =
                            sid :: (sessPksAuth S P st).map Prod.fst ∧
                        x.2.usedSendSessions = sid :: st.usedSendSessions := by
                      cases hHon : (findHonestPrincipal P st.principals bundle.ikB).isSome <;> (
                        rw [hHon] at hx
                        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                          support_pure, Set.mem_singleton_iff] at hx
                        subst hx
                        simp [sessPksAuth])
                    rcases hx_st with ⟨hp1, hp2, hp3, hp4, hp5⟩
                    refine ⟨⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hCons.1⟩, ?_⟩
                    rw [hp5, hp4, hUsed]
              · simp only [probExpect_bind]
                rw [probExpect_swap sampleScalar32 sampleCoins32]
                apply probExpect_const_le_of_support; intro kemCoins _
                rw [probExpect_swap sampleScalar32 sampleScalar32]
                apply probExpect_const_le_of_support; intro ephASk _
                rw [probExpect_swap sampleScalar32 sampleCoins32]
                apply probExpect_const_le_of_support; intro spqrCoins _
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none =>
                  simp only [StateT.run_pure, probExpect_pure]
                  exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
                | some val =>
                  rcases val with ⟨ss, kemCt⟩
                  dsimp only
                  refine le_trans (probExpect_mono_of_support sampleScalar32 _
                    (fun ekASk => ecPairPotential P
                      (ecTaggedFromLists S P st.principals st.spkBundles st.opkEntries
                        ((sid, P.x25519Base ekASk) :: sessPksAuth S P st)) s1 s2) ?_) ?_
                  · intro ekASk _
                    apply probExpect_const_le_of_support; intro x hx
                    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                      bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
                    rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
                    cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none =>
                      have hSome := hP.spqrInitSend_some drKey.pqrKey spqrCoins
                      rw [hSpqr] at hSome; cases hSome
                    | some spqrVal =>
                      rcases spqrVal with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                      rw [hSpqr] at hx; dsimp only at hx
                      simp only [StateT.run_bind, StateT.run_set, pure_bind] at hx
                      cases hHon : (findHonestPrincipal P st.principals bundle.ikB).isSome <;> (
                        rw [hHon] at hx
                        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                          support_pure, Set.mem_singleton_iff] at hx
                        subst hx
                        simp [ecTaggedAuth, sessPksAuth])
                  · exact probExpect_ecTaggedFromLists_cons_sess_le S P hP sid
                      st.principals st.spkBundles st.opkEntries (sessPksAuth S P st)
                      hVP hVS hVO hCons.2 s1 s2
            · simp only [↓reduceIte, StateT.run_pure, probExpect_bind, probExpect_pure]
              refine ⟨?_, ?_⟩
              · intro x hx
                simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
                rcases hx with ⟨_, _, _, _, _, _, _, _, rfl⟩
                exact ⟨⟨hVP, hVS, hVO, hVSess⟩, hUsed⟩
              · apply probExpect_const_le_of_support; intro _ _
                apply probExpect_const_le_of_support; intro _ _
                apply probExpect_const_le_of_support; intro _ _
                exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
          · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO,
            hVSess, hUsed]
        · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO,
          hVSess, hUsed]
    · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
      hUsed]
  · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess, hUsed]

theorem pqxdhAuthImpl_ec_step (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : AuthQuery S) (st : AuthState S) (s1 s2 : Nat)
    (hV : ValidAuthEc S P st) :
    (∀ x ∈ support ((pqxdhAuthImpl useRo checkAuth S P q).run st), ValidAuthEc S P x.2) ∧
    probExpect ((pqxdhAuthImpl useRo checkAuth S P q).run st)
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
    unfold pqxdhAuthImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨secIKA0, _, secIKAsign, _, rfl⟩
        exact ⟨⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hVSess⟩, hUsed⟩
      · simp only [probExpect_bind, probExpect_pure]
        rw [probExpect_swap sampleScalar32 sampleScalar32]
        apply probExpect_const_le_of_support
        intro secIKAsign _
        have hNotIn := (validPrincipals_cons S u
          { secIKA0 := [], ikAPk := [], secIKAsign := [], ikSignPk := [], corrupted := false }
          st.principals hVP hFresh).2
        exact probExpect_ecTaggedFromLists_cons_prin_le S P hP u
          st.principals st.spkBundles st.opkEntries (sessPksAuth S P st) hNotIn
          (fun sk => {
            secIKA0 := sk, ikAPk := P.x25519Base sk,
            secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false })
          (fun _ => rfl) s1 s2
    · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
      hUsed]
  | corruptIK u =>
    unfold pqxdhAuthImpl; dsimp only
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
    unfold pqxdhAuthImpl; dsimp only
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
    unfold pqxdhAuthImpl; dsimp only
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
    unfold pqxdhAuthImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runAuthSend_ec_step useRo S P hP (.sendOPK u i) trivial u bundle m0 m1 st s1 s2 ⟨⟨hVP,
          hVS, hVO, hVSess⟩, hUsed⟩
    · simp [StateT.run_pure, probExpect_pure, ValidAuthEc, ValidEcLists, hVP, hVS, hVO, hVSess,
      hUsed]
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthImpl; dsimp only
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
    have hp : PreservesAt projOpk st (pqxdhAuthImpl useRo checkAuth S P (.recvOPK k j o msg)) := by
      unfold pqxdhAuthImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; exact h_step1 _ _ _ _ _ _ _ _)
        | split)
    suffices h_supp : ∀ x ∈ support ((pqxdhAuthImpl useRo checkAuth S P (.recvOPK k j o msg)).run
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
    have hp : PreservesAt proj st (pqxdhAuthImpl useRo checkAuth S P (.recvNoOPK k j l msg)) := by
      unfold pqxdhAuthImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | roQuery secrets =>
    have hp : PreservesAt proj st (pqxdhAuthImpl useRo checkAuth S P (.roQuery secrets)) := by
      unfold pqxdhAuthImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | roRootQuery rk dh =>
    have hp : PreservesAt proj st (pqxdhAuthImpl useRo checkAuth S P (.roRootQuery rk dh)) := by
      unfold pqxdhAuthImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | revealDhSecrets =>
    have hp : PreservesAt proj st (pqxdhAuthImpl useRo checkAuth S P .revealDhSecrets) := by
      unfold pqxdhAuthImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | registerKey sk =>
    have hp : PreservesAt proj st (pqxdhAuthImpl useRo checkAuth S P (.registerKey sk)) := by
      unfold pqxdhAuthImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | (split; try dsimp only))
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])

/-! ## Closed-form birthday bounds -/

theorem keyIndCore_hop_ecColl_le (useRo : Bool) (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    |(𝒟[pqxdhKeyIndExpCore useRo S P A].boolBias).toReal -
     (𝒟[keyIndExpG0_1Core useRo S P A].boolBias).toReal| ≤
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 :=
  (keyIndCore_hop_ecColl_le_prob useRo S P A).trans (ecCollProbKeyInd_le_bound useRo S P hCWF A)

/-- Closed-form X25519 collision-elimination bound for `KeyInd` (`G0 → G0_1`). -/
theorem keyInd_hop_G0_G0_1_le (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    |keyIndAdvG0 S P A - keyIndAdvG0_1 S P A| ≤
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 :=
  keyIndCore_hop_ecColl_le true S P hCWF A

theorem keyIndCore_hop_kemColl_le (useRo : Bool) (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    |(𝒟[keyIndExpG1Core useRo S P A].boolBias).toReal -
     (𝒟[keyIndExpG2_1Core useRo S P A].boolBias).toReal| ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 :=
  (keyIndCore_hop_kemColl_le_prob useRo S P A).trans (kemCollProbKeyInd_le_bound useRo S P hCWF A)

/-- Closed-form KEM public-key collision-elimination bound for `KeyInd` (`G2 → G2_1`). -/
theorem keyInd_hop_G2_G2_1_le (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    |keyIndAdvG2 S P A - keyIndAdvG2_1 S P A| ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 :=
  keyIndCore_hop_kemColl_le true S P hCWF A

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (boolBias_le_add_two_mul_boolDist abs_sub_boolBias_toReal_le_two_mul_abs_sub gapDh_nonneg aeadIndCpa_nonneg sigEufCma_nonneg keyIndAdvantage_nonneg authAdvantage_nonneg Pfixed_pk_ec Pfixed_pk_kem pfixed_pk_ec_nonneg pfixed_pk_kem_nonneg keyIndExpG0 keyIndExpG1 keyIndExpG2 keyIndExpG3 keyIndAdvG0 keyIndAdvG1 keyIndAdvG2 keyIndAdvG3 keyIndAdvG0_eq keyIndAdvG1_eq_G2 authExpG0 authExpG1 abs_sub_boolBias_abort_or_le abs_sub_boolBias_abort_le toReal_any_range_le_sum runKeyIndSim runAuthSim ecCollProbKeyInd kemCollProbKeyInd keyIndExpG0_1Core keyIndExpG1Core keyIndExpG2_1Core keyIndExpG2_1 keyIndAdvG0_1 keyIndAdvG2_1 keyIndCore_hop_ecColl_le_prob keyInd_hop_G2_G2_1_le_prob ecCollProbKeyInd_le_bound kemCollProbKeyInd_le_bound allInitDh2sKeyInd)

end SignalPqxdh
