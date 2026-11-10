/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3G2
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import Computational.Proofs.SignalPqxdh.Security.SigHopA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# PQXDH authentication sub-hop 1 (`G3.5 → G3.6`, `RootKdfRO`)

Proves `hop_G3_5_G3_6` by coupling adjacent `authRkCutoffExp` hybrids via `authRkTrackedImpl` and
bounding bad `rootRoCache` collisions across all `S.N_sess_tot` sessions.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

namespace SignalPqxdh.Security.AuthSubHops1to3

/-! ## Tracked step and projection bridge -/

def authRkStepTracked (S : Setup) (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (stT : AuthRkTrackedState S) :
    ProbComp (AuthResponse × AuthRkTrackedState S) :=
  match q with
  | .sendOPK u i bundle m0 m1 => do
    if bundle.opkB?.isNone then
      pure (.noneResp, stT)
    else
      let (resp, hst') ← authRkSendWith S P sampRkAt useIdealRkAt (.sendOPK u i) u bundle m0 m1
          stT.1
      pure (resp, (hst', stT.2))
  | .sendNoOPK u i bundle m0 m1 => do
    if bundle.opkB?.isSome then
      pure (.noneResp, stT)
    else
      let (resp, hst') ← authRkSendWith S P sampRkAt useIdealRkAt (.sendNoOPK u i) u bundle m0 m1
          stT.1
      pure (resp, (hst', stT.2))
  | .recvOPK k j o msg =>
    authRkRecvTracked S P sampRkAt useIdealRkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg stT.1.toAuthHybridState) stT
  | .recvNoOPK k j l msg =>
    authRkRecvTracked S P sampRkAt useIdealRkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg stT.1.toAuthHybridState) stT
  | q => do
    let (resp, hst') ← authCkOtherStep S P q stT.1
    pure (resp, (hst', stT.2))

def authRkTrackedImpl (S : Setup) (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool) :
    QueryImpl (authSpec S) (StateT (AuthRkTrackedState S) ProbComp) :=
  fun q => StateT.mk (authRkStepTracked S P sampRkAt useIdealRkAt q)

theorem bind_authRkRecvTracked_fst {S : Setup} {β : Type} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (stT : AuthRkTrackedState S)
    (f : AuthResponse × AuthHybridStateFixed S → ProbComp β) :
    (authRkRecvTracked S P sampRkAt useIdealRkAt msg prep? stT >>= fun y => f (y.1, y.2.1)) =
      (authRkRecvWith S P sampRkAt useIdealRkAt msg prep? stT.1 >>= f) := by
  rcases stT with ⟨hst, extra⟩
  unfold authRkRecvTracked authRkRecvWith
  cases prep? with
  | none => simp only [pure_bind]
  | some prep =>
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · split <;> simp only [bind_assoc, pure_bind] <;> rfl
        · simp only [bind_assoc, pure_bind]; rfl
      | none =>
        dsimp only [finishAuthRecvUnmatchedAfterRk]
        simp only [bind_assoc]
        congr 1; funext rk; congr 1; funext ck; congr 1; funext pk
        split <;> simp only [bind_assoc, pure_bind] <;> rfl
    · simp only [bind_assoc, pure_bind]; rfl

theorem bind_authRkStepTracked_fst {S : Setup} {β : Type} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (stT : AuthRkTrackedState S)
    (f : AuthResponse × AuthHybridStateFixed S → ProbComp β) :
    (authRkStepTracked S P sampRkAt useIdealRkAt q stT >>= fun y => f (y.1, y.2.1)) =
      (authRkStepWith S P sampRkAt useIdealRkAt q stT.1 >>= f) := by
  cases q <;> unfold authRkStepTracked authRkStepWith <;> dsimp only
  case sendOPK => split <;> simp only [bind_assoc, pure_bind]
  case sendNoOPK => split <;> simp only [bind_assoc, pure_bind]
  case recvOPK => exact bind_authRkRecvTracked_fst P sampRkAt useIdealRkAt _ _ stT f
  case recvNoOPK => exact bind_authRkRecvTracked_fst P sampRkAt useIdealRkAt _ _ stT f
  all_goals simp only [bind_assoc, pure_bind]

theorem bind_simulateQ_authRkTrackedImpl {S : Setup} {α β : Type} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (oa : OracleComp (unifSpec + authSpec S) α)
    (stT : AuthRkTrackedState S)
    (fin : α × AuthHybridStateFixed S → ProbComp β) :
    (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthRkTrackedState S) ProbComp) +
        authRkTrackedImpl S P sampRkAt useIdealRkAt) oa).run stT) >>= fun y => fin (y.1, y.2.1)) =
      (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthHybridStateFixed S) ProbComp) +
        (fun q => StateT.mk (authRkStepWith S P sampRkAt useIdealRkAt q))) oa).run stT.1) >>= fin)
            := by
  induction oa using OracleComp.inductionOn generalizing stT with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t mx ih =>
    rcases t with uq | gq
    · rw [simulateQ_run_query_inl_local, simulateQ_run_query_inl_local, bind_assoc, bind_assoc]
      congr 1; funext u; exact ih u stT
    · rw [simulateQ_run_query_inr_local, simulateQ_run_query_inr_local, bind_assoc, bind_assoc]
      dsimp only [authRkTrackedImpl, StateT.run_mk]
      have hSub :
          (authRkStepTracked S P sampRkAt useIdealRkAt gq stT >>= fun x =>
            (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT (AuthRkTrackedState S) ProbComp) +
              authRkTrackedImpl S P sampRkAt useIdealRkAt) (mx x.1)).run x.2 >>=
              fun y => fin (y.1, y.2.1)) =
          (authRkStepTracked S P sampRkAt useIdealRkAt gq stT >>= fun x =>
            (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
              (StateT (AuthHybridStateFixed S) ProbComp) +
              (fun q => StateT.mk (authRkStepWith S P sampRkAt useIdealRkAt q))) (mx x.1)).run
                  x.2.1 >>= fin) := by
        congr 1; funext x; exact ih x.1 x.2
      rw [hSub]
      exact bind_authRkStepTracked_fst P sampRkAt useIdealRkAt gq stT
        (fun y => (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthHybridStateFixed S) ProbComp) +
          (fun q => StateT.mk (authRkStepWith S P sampRkAt useIdealRkAt q))) (mx y.1)).run y.2 >>=
              fin)

theorem RelProbUpToBad.liftTracked {S : Setup} {P : Primitives} {rkStar : Bytes} {idx : Nat}
    {extra5 extra6 : List ((Bytes × Bytes) × (Bytes × Bytes))}
    (hNoRkExtra : cacheHasRk rkStar extra6 = false)
    (m5 m6 : ProbComp (AuthResponse × AuthHybridStateFixed S))
    (hRel : RelProbUpToBad
      (fun y5 y6 => y5.1 = y6.1 ∧ AgreeOffRkAuth P rkStar idx y5.2 y6.2)
      (fun y6 => cacheHasRk rkStar y6.2.toAuthHybridState.base.rootRoCache) m5 m6) :
    RelProbUpToBad
      (fun y5 y6 => y5.1 = y6.1 ∧ AgreeOffRkAuthTracked P rkStar idx y5.2 y6.2)
      (fun y6 => badRkTracked rkStar y6.2)
      (do let (resp, hst') ← m5; pure (resp, (hst', extra5)))
      (do let (resp, hst') ← m6; pure (resp, (hst', extra6))) := by
  refine RelProbUpToBad.bind_rel hRel
    (fun b6 hBad y6 hy6 => by
      simp only [support_pure, Set.mem_singleton_iff] at hy6
      subst hy6; unfold badRkTracked; simp [hBad])
    (fun y5 y6 ⟨h1, h2⟩ => RelProbUpToBad.of_pure ⟨h1, h2, hNoRkExtra⟩)

theorem relProbUpToBad_authRkStepTracked {S : Setup} (P : Primitives) (hP :
    CryptoWellFormedPrimitivesδ P)
    (rkStar : Bytes) (idx : Nat) (q : AuthQuery S)
    (s5 s6 : AuthRkTrackedState S)
    (hAg : AgreeOffRkAuthTracked P rkStar idx s5 s6)
    (hKem : hasKemPkCollisionAuth s6.1.toAuthHybridState = false) :
    RelProbUpToBad
      (fun y5 y6 => y5.1 = y6.1 ∧ AgreeOffRkAuthTracked P rkStar idx y5.2 y6.2)
      (fun y6 => badRkTracked rkStar y6.2)
      (authRkStepTracked S P (fun s => if s == idx then pure rkStar else sampleBytes32)
        (fun s => decide (s < idx)) q s5)
      (authRkStepTracked S P (fun _ => sampleBytes32)
        (fun s => decide (s < idx + 1)) q s6) := by
  by_cases hOPK : ∃ u i bundle m0 m1, q = .sendOPK u i bundle m0 m1
  · rcases hOPK with ⟨u, i, bundle, m0, m1, rfl⟩
    unfold authRkStepTracked; dsimp only
    split
    · exact RelProbUpToBad.of_pure ⟨rfl, hAg⟩
    · exact RelProbUpToBad.liftTracked hAg.2 _ _
        (relProbUpToBad_authRkSendWith P hP rkStar idx (.sendOPK u i) u bundle m0 m1 rfl s5.1 s6.1
            hAg.1)
  · by_cases hNoOPK : ∃ u i bundle m0 m1, q = .sendNoOPK u i bundle m0 m1
    · rcases hNoOPK with ⟨u, i, bundle, m0, m1, rfl⟩
      unfold authRkStepTracked; dsimp only
      split
      · exact RelProbUpToBad.of_pure ⟨rfl, hAg⟩
      · exact RelProbUpToBad.liftTracked hAg.2 _ _
          (relProbUpToBad_authRkSendWith P hP rkStar idx (.sendNoOPK u i) u bundle m0 m1 rfl s5.1
              s6.1 hAg.1)
    · by_cases hRecvOPK : ∃ k j o msg, q = .recvOPK k j o msg
      · rcases hRecvOPK with ⟨k, j, o, msg, rfl⟩
        rcases hAg.1 with ⟨c5, h5Eq, _⟩
        unfold authRkStepTracked; dsimp only
        refine relProbUpToBad_authRkRecvTracked P hP rkStar idx msg _ _ s5 s6 hAg hKem ?_
        rw [h5Eq]; exact prepareAuthHybridRecvOPK_rel P idx rkStar c5 s6.1 k j o msg
      · by_cases hRecvNoOPK : ∃ k j l msg, q = .recvNoOPK k j l msg
        · rcases hRecvNoOPK with ⟨k, j, l, msg, rfl⟩
          rcases hAg.1 with ⟨c5, h5Eq, _⟩
          unfold authRkStepTracked; dsimp only
          refine relProbUpToBad_authRkRecvTracked P hP rkStar idx msg _ _ s5 s6 hAg hKem ?_
          rw [h5Eq]; exact prepareAuthHybridRecvNoOPK_rel P idx rkStar c5 s6.1 k j l msg
        · have hStep5 : authRkStepTracked S P (fun s => if s == idx then pure rkStar else
            sampleBytes32)
              (fun s => decide (s < idx)) q s5 =
              (do let (resp, hst') ← authCkOtherStep S P q s5.1; pure (resp, (hst', s5.2))) := by
            cases q with
            | sendOPK u i b m0 m1 => exact False.elim (hOPK ⟨u, i, b, m0, m1, rfl⟩)
            | sendNoOPK u i b m0 m1 => exact False.elim (hNoOPK ⟨u, i, b, m0, m1, rfl⟩)
            | recvOPK k j o msg => exact False.elim (hRecvOPK ⟨k, j, o, msg, rfl⟩)
            | recvNoOPK k j l msg => exact False.elim (hRecvNoOPK ⟨k, j, l, msg, rfl⟩)
            | _ => rfl
          have hStep6 : authRkStepTracked S P (fun _ => sampleBytes32)
              (fun s => decide (s < idx + 1)) q s6 =
              (do let (resp, hst') ← authCkOtherStep S P q s6.1; pure (resp, (hst', s6.2))) := by
            cases q with
            | sendOPK u i b m0 m1 => exact False.elim (hOPK ⟨u, i, b, m0, m1, rfl⟩)
            | sendNoOPK u i b m0 m1 => exact False.elim (hNoOPK ⟨u, i, b, m0, m1, rfl⟩)
            | recvOPK k j o msg => exact False.elim (hRecvOPK ⟨k, j, o, msg, rfl⟩)
            | recvNoOPK k j l msg => exact False.elim (hRecvNoOPK ⟨k, j, l, msg, rfl⟩)
            | _ => rfl
          rw [hStep5, hStep6]
          exact RelProbUpToBad.liftTracked hAg.2 _ _
            (relProbUpToBad_authCkOtherStep P rkStar idx q s5.1 s6.1 hAg.1
              (fun u i b m0 m1 h => hOPK ⟨u, i, b, m0, m1, h⟩)
              (fun u i b m0 m1 h => hNoOPK ⟨u, i, b, m0, m1, h⟩)
              (fun k j o msg h => hRecvOPK ⟨k, j, o, msg, h⟩)
              (fun k j l msg h => hRecvNoOPK ⟨k, j, l, msg, h⟩))

/-! ## Bad-event monotonicity and cache length bounds -/

theorem finishAuthRecvRkTracked_bad_and_len {S : Setup} (P : Primitives)
    (hst : AuthHybridStateFixed S) (extra : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 ck1_0 : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (recvCount' : Nat)
    (hWf : PreparedAuthRecvCacheWf hst.toAuthHybridState prep)
    (hStep : rootRoCache' = prep.hstDec.base.rootRoCache ∨ ∃ e, rootRoCache' = e ::
        prep.hstDec.base.rootRoCache) :
    let out := (finishAuthRecvRkTracked P msg prep drKey rk1 ck1_0 roCache' rootRoCache' recvCount'
        extra).2
    (∀ rkStar, badRkTracked rkStar out = (cacheHasRk rkStar rootRoCache' || cacheHasRk rkStar
        extra)) ∧
    out.1.toAuthHybridState.base.rootRoCache.length + out.2.length = rootRoCache'.length +
        extra.length := by
  intro out
  have hBaseC : prep.hstDec.base.rootRoCache = hst.toAuthHybridState.base.rootRoCache := by
    rw [hWf.base_eq]
  have hNone : (prep.finish none).2.base.rootRoCache = prep.hstDec.base.rootRoCache := by
    rw [hWf.finish_rootRoCache none, ← hBaseC]
  unfold out finishAuthRecvRkTracked finishAuthRecvRk
  dsimp only
  cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none =>
    dsimp only
    refine ⟨fun rkStar => ?_, ?_⟩
    · unfold badRkTracked; dsimp only; rw [hNone]
      exact newRootRoEntry_cacheHasRk rkStar rootRoCache' prep.hstDec.base.rootRoCache extra hStep
    · rw [hNone]
      exact newRootRoEntry_length rootRoCache' prep.hstDec.base.rootRoCache extra hStep
  | some p =>
    rcases p with ⟨pqrStB, spqrSalt?⟩
    dsimp only
    cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
      (firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
    | none =>
      dsimp only
      refine ⟨fun rkStar => ?_, ?_⟩
      · unfold badRkTracked; dsimp only; rw [hNone]
        exact newRootRoEntry_cacheHasRk rkStar rootRoCache' prep.hstDec.base.rootRoCache extra hStep
      · rw [hNone]
        exact newRootRoEntry_length rootRoCache' prep.hstDec.base.rootRoCache extra hStep
    | some pt =>
      dsimp only
      have hSome : (prep.finish (some (drKey, rk1, P.chainKdfNext ck1_0, pt, roCache',
          rootRoCache'))).2.base.rootRoCache = rootRoCache' :=
        hWf.finish_rootRoCache (some (drKey, rk1, P.chainKdfNext ck1_0, pt, roCache', rootRoCache'))
      refine ⟨fun rkStar => ?_, ?_⟩
      · unfold badRkTracked; dsimp only; rw [hSome]
      · rw [hSome]

theorem cacheHasRk_mono_step (rkStar : Bytes)
    {c c' : List ((Bytes × Bytes) × (Bytes × Bytes))}
    (hStep : c' = c ∨ ∃ e, c' = e :: c) :
    cacheHasRk rkStar c = true → cacheHasRk rkStar c' = true := by
  intro h
  rcases hStep with rfl | ⟨e, rfl⟩
  · exact h
  · unfold cacheHasRk at h ⊢; simp [h]

theorem badRkTracked_mono_step {S : Setup} (rkStar : Bytes)
    (stT : AuthRkTrackedState S)
    {c' : List ((Bytes × Bytes) × (Bytes × Bytes))}
    (hStep : c' = stT.1.toAuthHybridState.base.rootRoCache ∨
      ∃ e, c' = e :: stT.1.toAuthHybridState.base.rootRoCache)
    (hBad : badRkTracked rkStar stT = true) :
    (cacheHasRk rkStar c' || cacheHasRk rkStar stT.2) = true := by
  unfold badRkTracked at hBad
  simp only [Bool.or_eq_true] at hBad ⊢
  rcases hBad with h1 | h2
  · exact Or.inl (cacheHasRk_mono_step rkStar hStep h1)
  · exact Or.inr h2

theorem authRkRecvTracked_bad_and_len {S : Setup} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (stT : AuthRkTrackedState S)
    (hWf? : ∀ prep, prep? = some prep → PreparedAuthRecvCacheWf stT.1.toAuthHybridState prep) :
    ∀ y ∈ support (authRkRecvTracked S P sampRkAt useIdealRkAt msg prep? stT),
      (∀ rkStar, badRkTracked rkStar stT = true → badRkTracked rkStar y.2 = true) ∧
      y.2.1.toAuthHybridState.base.rootRoCache.length + y.2.2.length ≤
        stT.1.toAuthHybridState.base.rootRoCache.length + stT.2.length + 1 := by
  rcases stT with ⟨hst, extra⟩
  unfold authRkRecvTracked
  cases hPrep : prep? with
  | none =>
    intro y hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨fun rkStar h => h, ?_⟩
    dsimp only; omega
  | some prep =>
    have hWf := hWf? prep hPrep
    have hBaseC : prep.hstDec.base.rootRoCache = hst.toAuthHybridState.base.rootRoCache := by
      rw [hWf.base_eq]
    dsimp only
    have hFinish : ∀ (drKey : DRKey) (rk1 ck1_0 : Bytes) (roCache' : List (Bytes × DRKey))
        (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
        (hStep : rootRoCache' = prep.hstDec.base.rootRoCache ∨ ∃ e, rootRoCache' = e ::
            prep.hstDec.base.rootRoCache),
        let y := finishAuthRecvRkTracked P msg prep drKey rk1 ck1_0 roCache' rootRoCache'
            (hst.recvCount + 1) extra
        (∀ rkStar, badRkTracked rkStar (hst, extra) = true → badRkTracked rkStar y.2 = true) ∧
        y.2.1.toAuthHybridState.base.rootRoCache.length + y.2.2.length ≤
          hst.toAuthHybridState.base.rootRoCache.length + extra.length + 1 := by
      intro drKey rk1 ck1_0 roCache' rootRoCache' hStep
      have ⟨hB, hL⟩ := finishAuthRecvRkTracked_bad_and_len P hst extra msg prep
        drKey rk1 ck1_0 roCache' rootRoCache' (hst.recvCount + 1) hWf hStep
      refine ⟨fun rkStar hBad => ?_, ?_⟩
      · rw [hB rkStar]
        exact badRkTracked_mono_step rkStar (hst, extra) (hBaseC ▸ hStep) hBad
      · rw [hL]
        rcases hStep with hEq | ⟨e, hEq⟩ <;> [rw [hEq, hBaseC]; (rw [hEq, List.length_cons,
            hBaseC])] <;> omega
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · split
          · intro y hy; simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
            exact hFinish _ _ _ _ _ (Or.inl rfl)
          · intro y hy
            simp only [pure_bind, MonadAttach.mem_support_bind, support_pure,
                Set.mem_singleton_iff] at hy
            rcases hy with ⟨r, _, c, _, rfl⟩
            exact hFinish _ _ _ _ _ (Or.inl rfl)
        · intro y hy
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
          rcases hy with ⟨⟨⟨rk1, ck1_0⟩, c'⟩, hc', rfl⟩
          exact hFinish _ _ _ _ _ (evalRootKdfOrRo_StepCache hc')
      | none =>
        dsimp only
        intro y hy
        simp only [MonadAttach.mem_support_bind] at hy
        rcases hy with ⟨rk, _, ck, _, pk, _, hy⟩
        split at hy
        · simp only [pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
            at hy
          rcases hy with ⟨r, _, c, _, rfl⟩
          exact hFinish _ _ _ _ _ (Or.inl rfl)
        · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
          rcases hy with ⟨⟨⟨rk1, ck1_0⟩, c'⟩, hc', rfl⟩
          exact hFinish _ _ _ _ _ (evalRootKdfOrRo_StepCache hc')
    · intro y hy
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, c'⟩, hc', rfl⟩
      exact hFinish _ _ _ _ _ (evalRootKdfOrRo_StepCache hc')

def AllSupport {α : Type} (Q : α → Prop) (m : ProbComp α) : Prop :=
  ∀ y ∈ support m, Q y

theorem allSupport_pure {α : Type} {Q : α → Prop} {x : α} (h : Q x) :
    AllSupport Q (pure x) := by
  intro y hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact h

theorem allSupport_bind_pure_left {α β : Type} {Q : β → Prop} {a : α} {f : α → ProbComp β}
    (h : AllSupport Q (f a)) :
    AllSupport Q (pure a >>= f) := by
  unfold AllSupport; rw [pure_bind]; exact h

theorem allSupport_bind {α β : Type} {Q : β → Prop} {m : ProbComp α} {f : α → ProbComp β}
    (h : ∀ x ∈ support m, AllSupport Q (f x)) :
    AllSupport Q (m >>= f) := by
  intro y hy; simp only [MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨x, hx, hy'⟩; exact h x hx y hy'

theorem authRkSendWith_bad_mono {S : Setup} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    ∀ y ∈ support (authRkSendWith S P sampRkAt useIdealRkAt sid u bundle m0 m1 hst),
      y.2.toAuthHybridState.base.rootRoCache = hst.toAuthHybridState.base.rootRoCache ∨
      ∃ e, y.2.toAuthHybridState.base.rootRoCache = e :: hst.toAuthHybridState.base.rootRoCache :=
          by
  change AllSupport _ _
  unfold authRkSendWith finishAuthSendAfterRk; dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat (first
    | (with_reducible apply allSupport_pure;
       dsimp only [finishAuthHybridSend];
       first
       | exact Or.inl rfl
       | exact evalRootKdfOrRo_StepCache (by assumption))
    | with_reducible apply allSupport_bind_pure_left
    | with_reducible apply allSupport_bind_assoc
    | (with_reducible apply allSupport_bind; intro _ _)
    | split)

theorem authRkStepTracked_bad_and_len {S : Setup} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (stT : AuthRkTrackedState S) :
    ∀ y ∈ support (authRkStepTracked S P sampRkAt useIdealRkAt q stT),
      (∀ rkStar, badRkTracked rkStar stT = true → badRkTracked rkStar y.2 = true) ∧
      y.2.1.toAuthHybridState.base.rootRoCache.length + y.2.2.length ≤
        stT.1.toAuthHybridState.base.rootRoCache.length + stT.2.length +
        (if isAuthSendQueryB (.inr q) then 1 else 0) +
        (if isAuthRecvQueryB (.inr q) then 1 else 0) +
        (if isAuthRoRootQueryB (.inr q) then 1 else 0) := by
  by_cases hOPK : ∃ u i bundle m0 m1, q = .sendOPK u i bundle m0 m1
  · rcases hOPK with ⟨u, i, bundle, m0, m1, rfl⟩
    unfold authRkStepTracked isAuthSendQueryB isAuthRecvQueryB isAuthRoRootQueryB
    simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero]
    split
    · intro y hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
      exact ⟨fun _ h => h, by dsimp only; omega⟩
    · intro y hy
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨⟨resp, hst'⟩, hSend, rfl⟩
      have hStep := authRkSendWith_bad_mono P sampRkAt useIdealRkAt
        (.sendOPK u i) u bundle m0 m1 stT.1 (resp, hst') hSend
      have hLen := authRkSendWith_rootRoCache_length_le P sampRkAt useIdealRkAt
        (.sendOPK u i) u bundle m0 m1 stT.1 (resp, hst') hSend
      exact ⟨fun rkStar hBad => badRkTracked_mono_step rkStar stT hStep hBad,
        by dsimp only at hLen ⊢; omega⟩
  · by_cases hNoOPK : ∃ u i bundle m0 m1, q = .sendNoOPK u i bundle m0 m1
    · rcases hNoOPK with ⟨u, i, bundle, m0, m1, rfl⟩
      unfold authRkStepTracked isAuthSendQueryB isAuthRecvQueryB isAuthRoRootQueryB
      simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero]
      split
      · intro y hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy
        exact ⟨fun _ h => h, by dsimp only; omega⟩
      · intro y hy
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
        rcases hy with ⟨⟨resp, hst'⟩, hSend, rfl⟩
        have hStep := authRkSendWith_bad_mono P sampRkAt useIdealRkAt
          (.sendNoOPK u i) u bundle m0 m1 stT.1 (resp, hst') hSend
        have hLen := authRkSendWith_rootRoCache_length_le P sampRkAt useIdealRkAt
          (.sendNoOPK u i) u bundle m0 m1 stT.1 (resp, hst') hSend
        exact ⟨fun rkStar hBad => badRkTracked_mono_step rkStar stT hStep hBad,
          by dsimp only at hLen ⊢; omega⟩
    · by_cases hRecvOPK : ∃ k j o msg, q = .recvOPK k j o msg
      · rcases hRecvOPK with ⟨k, j, o, msg, rfl⟩
        unfold authRkStepTracked isAuthSendQueryB isAuthRecvQueryB isAuthRoRootQueryB
        simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero]
        exact authRkRecvTracked_bad_and_len P sampRkAt useIdealRkAt msg _ stT
          (prepareAuthHybridRecvOPK_cacheWf true P k j o msg stT.1.toAuthHybridState)
      · by_cases hRecvNoOPK : ∃ k j l msg, q = .recvNoOPK k j l msg
        · rcases hRecvNoOPK with ⟨k, j, l, msg, rfl⟩
          unfold authRkStepTracked isAuthSendQueryB isAuthRecvQueryB isAuthRoRootQueryB
          simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero]
          exact authRkRecvTracked_bad_and_len P sampRkAt useIdealRkAt msg _ stT
            (prepareAuthHybridRecvNoOPK_cacheWf true P k j l msg stT.1.toAuthHybridState)
        · by_cases hRo : ∃ rk dh, q = .roRootQuery rk dh
          · rcases hRo with ⟨rk, dh, rfl⟩
            unfold authRkStepTracked isAuthSendQueryB isAuthRecvQueryB isAuthRoRootQueryB
            simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero]
            rw [authCkOtherStep_roRootQuery_eq]
            split
            · intro y hy; simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy; subst hy
              exact ⟨fun _ h => h, by dsimp only; omega⟩
            intro y hy
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff,
                bind_assoc, pure_bind] at hy
            rcases hy with ⟨x, hx, rfl⟩
            have hStep := evalRootKdfOrRo_StepCache hx
            have hLen := evalRootKdfOrRo_length_le P rk dh stT.1.toAuthHybridState.base.rootRoCache
                x hx
            exact ⟨fun rkStar hBad => badRkTracked_mono_step rkStar stT hStep hBad,
              by dsimp only; omega⟩
          · have hOther : IsAuthOtherNonRoRoot q :=
              ⟨fun u i b m0 m1 h => hOPK ⟨u, i, b, m0, m1, h⟩,
               fun u i b m0 m1 h => hNoOPK ⟨u, i, b, m0, m1, h⟩,
               fun k j o msg h => hRecvOPK ⟨k, j, o, msg, h⟩,
               fun k j l msg h => hRecvNoOPK ⟨k, j, l, msg, h⟩,
               fun rk dh h => hRo ⟨rk, dh, h⟩⟩
            have hStepEq : authRkStepTracked S P sampRkAt useIdealRkAt q stT =
                (do let (resp, hst') ← authCkOtherStep S P q stT.1; pure (resp, (hst', stT.2))) :=
                    by
              cases q with
              | sendOPK u i b m0 m1 => exact False.elim (hOPK ⟨u, i, b, m0, m1, rfl⟩)
              | sendNoOPK u i b m0 m1 => exact False.elim (hNoOPK ⟨u, i, b, m0, m1, rfl⟩)
              | recvOPK k j o msg => exact False.elim (hRecvOPK ⟨k, j, o, msg, rfl⟩)
              | recvNoOPK k j l msg => exact False.elim (hRecvNoOPK ⟨k, j, l, msg, rfl⟩)
              | _ => rfl
            rw [hStepEq]
            intro y hy
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
            rcases hy with ⟨⟨resp, hst'⟩, hOtherStep, rfl⟩
            have hEq := authCkOtherStep_preserves_rootRoCache P q hOther stT.1 (resp, hst')
                hOtherStep
            exact ⟨fun rkStar hBad => badRkTracked_mono_step rkStar stT (Or.inl hEq) hBad,
              by dsimp only; rw [hEq]; omega⟩

theorem simulateQ_authRkTrackedImpl_bad_mono {S : Setup} {α : Type} (P : Primitives)
    (rkStar : Bytes) (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (oa : OracleComp (unifSpec + authSpec S) α)
    (stT : AuthRkTrackedState S)
    (hBad : badRkTracked rkStar stT = true) :
    ∀ y ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthRkTrackedState S) ProbComp) +
      authRkTrackedImpl S P sampRkAt useIdealRkAt) oa).run stT),
      badRkTracked rkStar y.2 = true :=
  simulateQ_bad_mono (authRkTrackedImpl S P sampRkAt useIdealRkAt) (badRkTracked rkStar)
    (fun q s6 hb y hy => (authRkStepTracked_bad_and_len P sampRkAt useIdealRkAt q s6 y hy).1 rkStar
        hb)
    oa stT hBad

theorem simulateQ_authRkTrackedImpl_length_le {S : Setup} {α : Type} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (oa : OracleComp (unifSpec + authSpec S) α)
    (stT : AuthRkTrackedState S) (nSend nRecv nRoRoot : Nat)
    (hSend : IsQueryBoundP oa (fun q => isAuthSendQueryB q = true) nSend)
    (hRecv : IsQueryBoundP oa (fun q => isAuthRecvQueryB q = true) nRecv)
    (hRoRoot : IsQueryBoundP oa (fun q => isAuthRoRootQueryB q = true) nRoRoot) :
    ∀ y ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthRkTrackedState S) ProbComp) +
      authRkTrackedImpl S P sampRkAt useIdealRkAt) oa).run stT),
      y.2.1.toAuthHybridState.base.rootRoCache.length + y.2.2.length ≤
        stT.1.toAuthHybridState.base.rootRoCache.length + stT.2.length + nSend + nRecv + nRoRoot :=
            by
  induction oa using OracleComp.inductionOn generalizing stT nSend nRecv nRoRoot with
  | pure a =>
    intro y hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; dsimp only; omega
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hSend hRecv hRoRoot
    rcases t with uq | gq
    · intro y hy
      rw [simulateQ_run_query_inl_local] at hy
      simp only [MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨u, _, hy'⟩
      have hS' := hSend.2 u
      have hRc' := hRecv.2 u
      have hR' := hRoRoot.2 u
      simp only [isAuthSendQueryB, isAuthRecvQueryB, isAuthRoRootQueryB, Bool.false_eq_true,
          ↓reduceIte] at hS' hRc' hR'
      exact ih u stT nSend nRecv nRoRoot hS' hRc' hR' y hy'
    · intro y hy
      rw [simulateQ_run_query_inr_local] at hy
      simp only [MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨⟨r, stT'⟩, hstep, hy'⟩
      have hStepLen := (authRkStepTracked_bad_and_len P sampRkAt useIdealRkAt gq stT (r, stT')
          hstep).2
      have hIH := ih r stT'
        (if isAuthSendQueryB (.inr gq) = true then nSend - 1 else nSend)
        (if isAuthRecvQueryB (.inr gq) = true then nRecv - 1 else nRecv)
        (if isAuthRoRootQueryB (.inr gq) = true then nRoRoot - 1 else nRoRoot)
        (hSend.2 r) (hRecv.2 r) (hRoRoot.2 r) y hy'
      have h1 := hSend.1; have h2 := hRecv.1; have h3 := hRoRoot.1
      by_cases hs : isAuthSendQueryB (.inr gq) = true <;>
        by_cases hrc : isAuthRecvQueryB (.inr gq) = true <;>
        by_cases hr : isAuthRoRootQueryB (.inr gq) = true <;>
        simp only [hs, hrc, hr, Bool.false_eq_true, not_true_eq_false, false_or, ↓reduceIte]
          at h1 h2 h3 hStepLen hIH <;>
        omega

theorem hasDuplicateBytes_map_of_eq_or_cons {α : Type} (f : α → Bytes) {l l' : List α}
    (h : l' = l ∨ ∃ e, l' = e :: l)
    (hDup : hasDuplicateBytes (l.map f) = true) :
    hasDuplicateBytes (l'.map f) = true := by
  rcases h with rfl | ⟨e, rfl⟩
  · exact hDup
  · simp only [List.map_cons, hasDuplicateBytes, hDup, Bool.or_true]

theorem prepareAuthHybridRecvOPK_spkBundles {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    ∀ prep, prepareAuthHybridRecvOPK true P k j o msg hst = some prep →
      ∀ res?, (prep.finish res?).2.base.spkBundles = hst.base.spkBundles := by
  unfold prepareAuthHybridRecvOPK; dsimp only
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split
  · split; · intro _ h; cases h
    split; · intro _ h; cases h
    split
    · intro _ h; cases h
    · intro prep h res?; injection h with h; subst h
      unfold finishAuthHybridRecvOPK
      cases res? with
      | none => rfl
      | some r =>
        rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
        cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
        | none => rfl
        | some p => rcases p with ⟨_, senderEntry⟩; dsimp only; split <;> rfl
  · intro _ h; cases h

theorem prepareAuthHybridRecvNoOPK_spkBundles {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    ∀ prep, prepareAuthHybridRecvNoOPK true P k j l msg hst = some prep →
      ∀ res?, (prep.finish res?).2.base.spkBundles = hst.base.spkBundles := by
  unfold prepareAuthHybridRecvNoOPK; dsimp only
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split
  · split; · intro _ h; cases h
    split
    · intro _ h; cases h
    · intro prep h res?; injection h with h; subst h
      unfold finishAuthHybridRecvNoOPK
      cases res? with
      | none => rfl
      | some r =>
        rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
        cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
        | none => rfl
        | some p => rcases p with ⟨_, senderEntry⟩; dsimp only; split <;> rfl
  · intro _ h; cases h

theorem authRkRecvTracked_spkBundles {S : Setup} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (stT : AuthRkTrackedState S)
    (hSpk? : ∀ prep, prep? = some prep → ∀ res?, (prep.finish res?).2.base.spkBundles =
        stT.1.toAuthHybridState.base.spkBundles) :
    ∀ y ∈ support (authRkRecvTracked S P sampRkAt useIdealRkAt msg prep? stT),
      y.2.1.toAuthHybridState.base.spkBundles = stT.1.toAuthHybridState.base.spkBundles := by
  rcases stT with ⟨hst, extra⟩
  unfold authRkRecvTracked
  cases hPrep : prep? with
  | none =>
    intro y hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
  | some prep =>
    have hSpk := hSpk? prep hPrep
    change AllSupport _ _
    dsimp only
    repeat (first
      | (with_reducible apply allSupport_pure;
         unfold finishAuthRecvRkTracked finishAuthRecvRk;
         exact hSpk _)
      | with_reducible apply allSupport_bind_pure_left
      | with_reducible apply allSupport_bind_assoc
      | (with_reducible apply allSupport_bind; intro _ _)
      | split)

theorem authRkSendWith_spkBundles {S : Setup} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    ∀ y ∈ support (authRkSendWith S P sampRkAt useIdealRkAt sid u bundle m0 m1 hst),
      y.2.toAuthHybridState.base.spkBundles = hst.toAuthHybridState.base.spkBundles := by
  change AllSupport _ _
  unfold authRkSendWith finishAuthSendAfterRk; dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat (first
    | ((with_reducible apply allSupport_pure); rfl)
    | with_reducible apply allSupport_bind_pure_left
    | with_reducible apply allSupport_bind_assoc
    | (with_reducible apply allSupport_bind; intro _ _)
    | split)

theorem pqxdhAuthImpl_other_spkBundles {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hOther : IsAuthOtherNonRoRoot q) (st : AuthState S) :
    ∀ y ∈ support ((pqxdhAuthImpl true true S P q).run st),
      y.2.spkBundles = st.spkBundles ∨ ∃ e, y.2.spkBundles = e :: st.spkBundles := by
  cases q with
  | sendOPK u i bundle m0 m1 => exact False.elim (hOther.1 u i bundle m0 m1 rfl)
  | sendNoOPK u i bundle m0 m1 => exact False.elim (hOther.2.1 u i bundle m0 m1 rfl)
  | recvOPK k j o msg => exact False.elim (hOther.2.2.1 k j o msg rfl)
  | recvNoOPK k j l msg => exact False.elim (hOther.2.2.2.1 k j l msg rfl)
  | roRootQuery rk dh => exact False.elim (hOther.2.2.2.2 rk dh rfl)
  | initPrin u =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy; subst hy; exact
        Or.inl rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure,
        bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
            at hy
      rcases hy with ⟨_, _, _, _, rfl⟩; exact Or.inl rfl
  | corruptIK u =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy <;> (simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hy; subst hy; exact Or.inl rfl)
  | genSPK u j =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy; subst hy; exact
        Or.inl rfl
    · split at hy
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure,
          bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
              at hy
        rcases hy with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, rfl⟩; exact Or.inr ⟨_, rfl⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy; subst hy; exact
          Or.inl rfl
  | genOPK u j o =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy; subst hy; exact
        Or.inl rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure,
        bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
            at hy
      rcases hy with ⟨_, _, rfl⟩; exact Or.inl rfl
  | registerKey sk =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hy
    split at hy <;> (simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hy; subst hy; exact Or.inl rfl)
  | roQuery secrets =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨_, _, rfl⟩; exact Or.inl rfl
  | revealDhSecrets =>
    intro y hy; unfold pqxdhAuthImpl at hy; dsimp only at hy
    simp only [↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact Or.inl rfl

theorem authRkStepTracked_hasKemPkCollisionAuth_mono {S : Setup} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (q : AuthQuery S) (stT : AuthRkTrackedState S)
    (hKem : hasKemPkCollisionAuth stT.1.toAuthHybridState = true) :
    ∀ y ∈ support (authRkStepTracked S P sampRkAt useIdealRkAt q stT),
      hasKemPkCollisionAuth y.2.1.toAuthHybridState = true := by
  have hStep : ∀ y ∈ support (authRkStepTracked S P sampRkAt useIdealRkAt q stT),
      y.2.1.toAuthHybridState.base.spkBundles = stT.1.toAuthHybridState.base.spkBundles ∨
      ∃ e, y.2.1.toAuthHybridState.base.spkBundles = e :: stT.1.toAuthHybridState.base.spkBundles
          := by
    by_cases hOPK : ∃ u i bundle m0 m1, q = .sendOPK u i bundle m0 m1
    · rcases hOPK with ⟨u, i, bundle, m0, m1, rfl⟩
      unfold authRkStepTracked; dsimp only; split
      · intro y hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact Or.inl
          rfl
      · intro y hy; simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
          at hy
        rcases hy with ⟨⟨resp, hst'⟩, hSend, rfl⟩
        exact Or.inl (authRkSendWith_spkBundles P sampRkAt useIdealRkAt (.sendOPK u i) u bundle m0
            m1 stT.1 (resp, hst') hSend)
    · by_cases hNoOPK : ∃ u i bundle m0 m1, q = .sendNoOPK u i bundle m0 m1
      · rcases hNoOPK with ⟨u, i, bundle, m0, m1, rfl⟩
        unfold authRkStepTracked; dsimp only; split
        · intro y hy; simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact Or.inl
            rfl
        · intro y hy; simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
            at hy
          rcases hy with ⟨⟨resp, hst'⟩, hSend, rfl⟩
          exact Or.inl (authRkSendWith_spkBundles P sampRkAt useIdealRkAt (.sendNoOPK u i) u bundle
              m0 m1 stT.1 (resp, hst') hSend)
      · by_cases hRecvOPK : ∃ k j o msg, q = .recvOPK k j o msg
        · rcases hRecvOPK with ⟨k, j, o, msg, rfl⟩
          unfold authRkStepTracked; dsimp only
          intro y hy
          exact Or.inl (authRkRecvTracked_spkBundles P sampRkAt useIdealRkAt msg _ stT
            (prepareAuthHybridRecvOPK_spkBundles P k j o msg stT.1.toAuthHybridState) y hy)
        · by_cases hRecvNoOPK : ∃ k j l msg, q = .recvNoOPK k j l msg
          · rcases hRecvNoOPK with ⟨k, j, l, msg, rfl⟩
            unfold authRkStepTracked; dsimp only
            intro y hy
            exact Or.inl (authRkRecvTracked_spkBundles P sampRkAt useIdealRkAt msg _ stT
              (prepareAuthHybridRecvNoOPK_spkBundles P k j l msg stT.1.toAuthHybridState) y hy)
          · by_cases hRo : ∃ rk dh, q = .roRootQuery rk dh
            · rcases hRo with ⟨rk, dh, rfl⟩
              unfold authRkStepTracked; dsimp only; rw [authCkOtherStep_roRootQuery_eq]
              split
              · intro y hy; simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hy
                subst hy; exact Or.inl rfl
              intro y hy; simp only [MonadAttach.mem_support_bind, support_pure,
                  Set.mem_singleton_iff, bind_assoc, pure_bind] at hy
              rcases hy with ⟨_, _, rfl⟩; exact Or.inl rfl
            · have hOther : IsAuthOtherNonRoRoot q :=
                ⟨fun u i b m0 m1 h => hOPK ⟨u, i, b, m0, m1, h⟩,
                 fun u i b m0 m1 h => hNoOPK ⟨u, i, b, m0, m1, h⟩,
                 fun k j o msg h => hRecvOPK ⟨k, j, o, msg, h⟩,
                 fun k j l msg h => hRecvNoOPK ⟨k, j, l, msg, h⟩,
                 fun rk dh h => hRo ⟨rk, dh, h⟩⟩
              have hStepEq : authRkStepTracked S P sampRkAt useIdealRkAt q stT =
                  (do let (resp, hst') ← authCkOtherStep S P q stT.1; pure (resp, (hst', stT.2)))
                      := by
                cases q with
                | sendOPK u i b m0 m1 => exact False.elim (hOPK ⟨u, i, b, m0, m1, rfl⟩)
                | sendNoOPK u i b m0 m1 => exact False.elim (hNoOPK ⟨u, i, b, m0, m1, rfl⟩)
                | recvOPK k j o msg => exact False.elim (hRecvOPK ⟨k, j, o, msg, rfl⟩)
                | recvNoOPK k j l msg => exact False.elim (hRecvNoOPK ⟨k, j, l, msg, rfl⟩)
                | _ => rfl
              rw [hStepEq]; intro y hy
              simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
              rcases hy with ⟨⟨resp, hst'⟩, hOtherStep, rfl⟩
              unfold authCkOtherStep at hOtherStep
              split at hOtherStep
              · simp only [support_pure, Set.mem_singleton_iff] at hOtherStep
                rcases Prod.mk.inj hOtherStep with ⟨rfl, rfl⟩; exact Or.inl rfl
              simp only [MonadAttach.mem_support_bind, support_pure,
                  Set.mem_singleton_iff] at hOtherStep
              rcases hOtherStep with ⟨p, hbase, hEq⟩
              rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
              exact pqxdhAuthImpl_other_spkBundles P q hOther stT.1.toAuthHybridState.base p hbase
  intro y hy
  unfold hasKemPkCollisionAuth allHonestKemPksAuth HasAuthState.toAuthState at hKem ⊢
  exact hasDuplicateBytes_map_of_eq_or_cons (fun (_, b) => b.pqspkPk) (hStep y hy) hKem

theorem simulateQ_authRkTrackedImpl_hasKemPkCollisionAuth_mono {S : Setup} {α : Type} (P :
    Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (oa : OracleComp (unifSpec + authSpec S) α)
    (stT : AuthRkTrackedState S)
    (hKem : hasKemPkCollisionAuth stT.1.toAuthHybridState = true) :
    ∀ y ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthRkTrackedState S) ProbComp) +
      authRkTrackedImpl S P sampRkAt useIdealRkAt) oa).run stT),
      hasKemPkCollisionAuth y.2.1.toAuthHybridState = true :=
  simulateQ_bad_mono (authRkTrackedImpl S P sampRkAt useIdealRkAt)
    (fun s => hasKemPkCollisionAuth s.1.toAuthHybridState)
    (fun q s hb y hy => authRkStepTracked_hasKemPkCollisionAuth_mono P sampRkAt useIdealRkAt q s hb
        y hy)
    oa stT hKem

theorem finalizeAuthFixed_of_hasKemPkCollisionAuth {S : Setup} (P : Primitives)
    (secb b' : Bool) (hst : AuthHybridState S)
    (hKem : hasKemPkCollisionAuth hst = true) :
    finalizeAuthFixed P secb b' hst = $ᵗ Bool := by
  unfold finalizeAuthFixed
  simp [hKem]

theorem probExpect_simulateQ_tracked_of_hasKemPkCollisionAuth {S : Setup} (P : Primitives)
    (sampRkAt : Nat → ProbComp Bytes) (useIdealRkAt : Nat → Bool)
    (secb : Bool) (oa : OracleComp (unifSpec + authSpec S) Bool)
    (stT : AuthRkTrackedState S)
    (hKem : hasKemPkCollisionAuth stT.1.toAuthHybridState = true) :
    probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthRkTrackedState S) ProbComp) +
      authRkTrackedImpl S P sampRkAt useIdealRkAt) oa).run stT)
      (fun y => 𝒟[finalizeAuthFixed P secb y.1 y.2.1.toAuthHybridState] {true}) =
    𝒟[$ᵗ Bool] {true} := by
  refine probExpect_eq_const_of_support _ _ (𝒟[$ᵗ Bool] {true}) (fun y hy => ?_)
  rw [finalizeAuthFixed_of_hasKemPkCollisionAuth P secb y.1 y.2.1.toAuthHybridState
    (simulateQ_authRkTrackedImpl_hasKemPkCollisionAuth_mono P sampRkAt useIdealRkAt oa stT hKem y
        hy)]

/-! ## Cutoff step bound and `hop_G3_5_G3_6` -/

theorem simulateQ_authRkTrackedImpl_probExpect_le {S : Setup} (P : Primitives) (hP :
    CryptoWellFormedPrimitivesδ P)
    (rkStar : Bytes) (idx : Nat) (secb : Bool)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (s5 s6 : AuthRkTrackedState S)
    (hAg : AgreeOffRkAuthTracked P rkStar idx s5 s6) :
    let full5 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthRkTrackedState S)
        ProbComp) +
      authRkTrackedImpl S P (fun s => if s == idx then pure rkStar else sampleBytes32) (fun s =>
          decide (s < idx))
    let full6 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthRkTrackedState S)
        ProbComp) +
      authRkTrackedImpl S P (fun _ => sampleBytes32) (fun s => decide (s < idx + 1))
    let fin : Bool × AuthRkTrackedState S → ℝ≥0∞ :=
      fun x => 𝒟[finalizeAuthFixed P secb x.1 x.2.1.toAuthHybridState] {true}
    probExpect ((simulateQ full5 oa).run s5) fin ≤
      probExpect ((simulateQ full6 oa).run s6) (fun x => if badRkTracked rkStar x.2 then 1 else fin
          x) ∧
    probExpect ((simulateQ full6 oa).run s6) (fun x => if badRkTracked rkStar x.2 then 0 else fin
        x) ≤
      probExpect ((simulateQ full5 oa).run s5) fin := by
  intro full5 full6 fin
  induction oa using OracleComp.inductionOn generalizing s5 s6 with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
    have hNotBad : badRkTracked rkStar s6 = false := AgreeOffRkAuthTracked.not_bad hAg
    have hFinEq : fin (a, s5) = fin (a, s6) := by
      dsimp only [fin]
      rw [AgreeOffRkAuth.finalize_eq P secb a hAg.1]
    simp [hNotBad, hFinEq]
  | query_bind t mx ih =>
    by_cases hKem : hasKemPkCollisionAuth s6.1.toAuthHybridState = false
    · rcases t with uq | gq
      · refine ⟨?_, ?_⟩
        · dsimp only [full5, full6]
          rw [simulateQ_run_query_inl_local, simulateQ_run_query_inl_local, probExpect_bind,
              probExpect_bind]
          exact probExpect_mono_of_support _ _ _ (fun u _ => (ih u s5 s6 hAg).1)
        · dsimp only [full5, full6]
          rw [simulateQ_run_query_inl_local, simulateQ_run_query_inl_local, probExpect_bind,
              probExpect_bind]
          exact probExpect_mono_of_support _ _ _ (fun u _ => (ih u s5 s6 hAg).2)
      · have hStep := relProbUpToBad_authRkStepTracked P hP rkStar idx gq s5 s6 hAg hKem
        refine ⟨?_, ?_⟩
        · dsimp only [full5, full6]
          rw [simulateQ_run_query_inr_local, simulateQ_run_query_inr_local, probExpect_bind,
              probExpect_bind]
          refine hStep.1 _ _
            (fun y5 => probExpect_const_le_of_support _ _ 1 (fun _ _ => MeasureTheory.prob_le_one))
            (fun y6 hb => probExpect_eq_const_of_support _ _ 1 (fun x hx => by
              have hb' := simulateQ_authRkTrackedImpl_bad_mono P rkStar
                (fun _ => sampleBytes32) (fun s => decide (s < idx + 1)) (mx y6.1) y6.2 hb x hx
              simp [hb']))
            (fun y5 y6 ⟨hr, hAg'⟩ => by rw [hr]; exact (ih y6.1 y5.2 y6.2 hAg').1)
        · dsimp only [full5, full6]
          rw [simulateQ_run_query_inr_local, simulateQ_run_query_inr_local, probExpect_bind,
              probExpect_bind]
          refine hStep.2 _ _
            (fun y6 hb => probExpect_eq_zero_of_support _ _ (fun x hx => by
              have hb' := simulateQ_authRkTrackedImpl_bad_mono P rkStar
                (fun _ => sampleBytes32) (fun s => decide (s < idx + 1)) (mx y6.1) y6.2 hb x hx
              simp [hb']))
            (fun y5 y6 ⟨hr, hAg'⟩ => by rw [hr]; exact (ih y6.1 y5.2 y6.2 hAg').2)
    · have hKem6 : hasKemPkCollisionAuth s6.1.toAuthHybridState = true :=
        Bool.eq_true_of_not_eq_false hKem
      have hKem5 : hasKemPkCollisionAuth s5.1.toAuthHybridState = true :=
        (AgreeOffRkAuth.hasKemPkCollisionAuth_eq hAg.1).trans hKem6
      let qm := (liftM (OracleSpec.query t) : OracleComp (unifSpec + authSpec S) _) >>= mx
      have hE5 : probExpect ((simulateQ full5 qm).run s5) fin =
          𝒟[$ᵗ Bool] {true} :=
        probExpect_simulateQ_tracked_of_hasKemPkCollisionAuth P _ _ secb qm s5 hKem5
      change (probExpect ((simulateQ full5 qm).run s5) fin ≤
          probExpect ((simulateQ full6 qm).run s6) (fun x => if badRkTracked rkStar x.2 then 1 else
              fin x)) ∧
        (probExpect ((simulateQ full6 qm).run s6) (fun x => if badRkTracked rkStar x.2 then 0 else
            fin x) ≤
          probExpect ((simulateQ full5 qm).run s5) fin)
      rw [hE5]
      refine ⟨?_, ?_⟩
      · calc 𝒟[$ᵗ Bool] {true}
            = probExpect ((simulateQ full6 qm).run s6) (fun _ => 𝒟[$ᵗ Bool] {true}) :=
              (probExpect_const _ _).symm
          _ ≤ probExpect ((simulateQ full6 qm).run s6)
                (fun x => if badRkTracked rkStar x.2 then 1 else fin x) := by
              refine probExpect_mono_of_support _ _ _ (fun x hx => ?_)
              have hKemX := simulateQ_authRkTrackedImpl_hasKemPkCollisionAuth_mono P _ _ qm s6
                  hKem6 x hx
              have hFinX : fin x = 𝒟[$ᵗ Bool] {true} := by
                dsimp only [fin]
                rw [finalizeAuthFixed_of_hasKemPkCollisionAuth P secb x.1 x.2.1.toAuthHybridState
                    hKemX]
              cases badRkTracked rkStar x.2
              · simp [hFinX]
              · simp only [↓reduceIte]; exact MeasureTheory.prob_le_one
      · calc probExpect ((simulateQ full6 qm).run s6)
                (fun x => if badRkTracked rkStar x.2 then 0 else fin x)
            ≤ probExpect ((simulateQ full6 qm).run s6) (fun _ => 𝒟[$ᵗ Bool] {true}) := by
              refine probExpect_mono_of_support _ _ _ (fun x hx => ?_)
              have hKemX := simulateQ_authRkTrackedImpl_hasKemPkCollisionAuth_mono P _ _ qm s6
                  hKem6 x hx
              have hFinX : fin x = 𝒟[$ᵗ Bool] {true} := by
                dsimp only [fin]
                rw [finalizeAuthFixed_of_hasKemPkCollisionAuth P secb x.1 x.2.1.toAuthHybridState
                    hKemX]
              cases badRkTracked rkStar x.2
              · simp [hFinX]
              · simp
          _ = 𝒟[$ᵗ Bool] {true} := probExpect_const _ _

theorem simulateQ_authRkTrackedImpl_evalDist_bind_le {S : Setup} (P : Primitives) (hP :
    CryptoWellFormedPrimitivesδ P)
    (rkStar : Bytes) (idx : Nat) (secb : Bool)
    (oa : OracleComp (unifSpec + authSpec S) Bool)
    (s5 s6 : AuthRkTrackedState S)
    (hAg : AgreeOffRkAuthTracked P rkStar idx s5 s6) :
    let full5 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthRkTrackedState S)
        ProbComp) +
      authRkTrackedImpl S P (fun s => if s == idx then pure rkStar else sampleBytes32) (fun s =>
          decide (s < idx))
    let full6 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthRkTrackedState S)
        ProbComp) +
      authRkTrackedImpl S P (fun _ => sampleBytes32) (fun s => decide (s < idx + 1))
    let fin : Bool × AuthRkTrackedState S → ProbComp Bool :=
      fun x => finalizeAuthFixed P secb x.1 x.2.1.toAuthHybridState
    𝒟[(simulateQ full5 oa).run s5 >>= fin] {true} ≤
      𝒟[(simulateQ full6 oa).run s6 >>= fin] {true} +
      𝒟[(simulateQ full6 oa).run s6 >>= fun x => pure (badRkTracked rkStar x.2)] {true} ∧
    𝒟[(simulateQ full6 oa).run s6 >>= fin] {true} ≤
      𝒟[(simulateQ full5 oa).run s5 >>= fin] {true} +
      𝒟[(simulateQ full6 oa).run s6 >>= fun x => pure (badRkTracked rkStar x.2)] {true} := by
  intro full5 full6 fin
  let m5 := (simulateQ full5 oa).run s5
  let m6 := (simulateQ full6 oa).run s6
  have ⟨hLe1, hLe2⟩ := simulateQ_authRkTrackedImpl_probExpect_le P hP rkStar idx secb oa s5 s6 hAg
  let _ : MeasurableSpace (Bool × AuthRkTrackedState S) := ⊤
  have _ : DiscreteMeasurableSpace (Bool × AuthRkTrackedState S) := ⟨fun _ => trivial⟩
  have h5 : 𝒟[m5 >>= fin] {true} = probExpect m5 (fun x => 𝒟[fin x] {true}) := by
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
            Measurable.of_discrete.aemeasurable]
  have h6 : 𝒟[m6 >>= fin] {true} = probExpect m6 (fun x => 𝒟[fin x] {true}) := by
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
            Measurable.of_discrete.aemeasurable]
  have hbad : 𝒟[m6 >>= fun x => pure (badRkTracked rkStar x.2)] {true} =
      probExpect m6 (fun x => 𝒟[(pure (badRkTracked rkStar x.2) : ProbComp Bool)] {true}) :=
    evalDist_bind_true_eq_probExpect m6 (fun x => badRkTracked rkStar x.2)
  rw [h5, h6, hbad]
  refine ⟨?_, ?_⟩
  · calc probExpect m5 (fun x => 𝒟[fin x] {true})
        ≤ probExpect m6 (fun x => if badRkTracked rkStar x.2 then 1 else 𝒟[fin x] {true}) := hLe1
      _ ≤ probExpect m6 (fun x => 𝒟[fin x] {true}) +
          probExpect m6 (fun x => 𝒟[(pure (badRkTracked rkStar x.2) : ProbComp Bool)] {true}) := by
          apply probExpect_add_le
          intro x; cases badRkTracked rkStar x.2 <;> simp
  · calc probExpect m6 (fun x => 𝒟[fin x] {true})
        ≤ probExpect m6 (fun x => if badRkTracked rkStar x.2 then 0 else 𝒟[fin x] {true}) +
          probExpect m6 (fun x => 𝒟[(pure (badRkTracked rkStar x.2) : ProbComp Bool)] {true}) := by
          apply probExpect_add_le
          intro x; cases badRkTracked rkStar x.2 <;> simp
      _ ≤ probExpect m5 (fun x => 𝒟[fin x] {true}) +
          probExpect m6 (fun x => 𝒟[(pure (badRkTracked rkStar x.2) : ProbComp Bool)] {true}) :=
          add_le_add hLe2 le_rfl

theorem badRkTracked_eq_cacheHasRk_append {S : Setup} (rkStar : Bytes) (stT : AuthRkTrackedState S)
    :
    badRkTracked rkStar stT =
      cacheHasRk rkStar (stT.1.toAuthHybridState.base.rootRoCache ++ stT.2) := by
  unfold badRkTracked cacheHasRk
  rw [List.any_append]

theorem evalDist_bind_sampleBytes32_badRkTracked_le {S : Setup} {α : Type}
    (m6 : ProbComp (α × AuthRkTrackedState S)) (K : Nat)
    (hLen : ∀ y ∈ support m6, y.2.1.toAuthHybridState.base.rootRoCache.length + y.2.2.length ≤ K) :
    𝒟[m6 >>= fun y => sampleBytes32 >>= fun rk => pure (badRkTracked rk y.2)] {true} ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256) := by
  let _ : MeasurableSpace (α × AuthRkTrackedState S) := ⊤
  have _ : DiscreteMeasurableSpace (α × AuthRkTrackedState S) := ⟨fun _ => trivial⟩
  have hEq : 𝒟[m6 >>= fun y => sampleBytes32 >>= fun rk => pure (badRkTracked rk y.2)] {true} =
      probExpect m6 (fun y => 𝒟[sampleBytes32 >>= fun rk => pure (badRkTracked rk y.2)] {true}) :=
          by
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
            Measurable.of_discrete.aemeasurable]
  rw [hEq]
  calc probExpect m6 (fun y => 𝒟[sampleBytes32 >>= fun rk => pure (badRkTracked rk y.2)] {true})
      ≤ probExpect m6 (fun _ => (K : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256)) := by
        apply probExpect_mono_of_support
        intro y hy
        simp only [badRkTracked_eq_cacheHasRk_append]
        calc 𝒟[sampleBytes32 >>= fun rk => pure (cacheHasRk rk
            (y.2.1.toAuthHybridState.base.rootRoCache ++ y.2.2))] {true}
            ≤ ((y.2.1.toAuthHybridState.base.rootRoCache ++ y.2.2).length : ℝ≥0∞) * ENNReal.ofReal
                (1 / (2 : ℝ) ^ 256) :=
              evalDist_sampleBytes32_cacheHasRk_le _
          _ ≤ (K : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256) := by
              rw [List.length_append]
              exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hLen y hy)) zero_le
    _ = (K : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256) :=
        probExpect_const m6 _

theorem authRkCutoffExp_step_le (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (idx : Nat) :
    |(𝒟[authRkCutoffExp S P idx A.1] {true}).toReal -
     (𝒟[authRkCutoffExp S P (idx + 1) A.1] {true}).toReal| ≤
      ((b.q_roRoot : ℝ) + (S.N_sess_tot : ℝ)) * (1 / (2 : ℝ) ^ 256) := by
  let mx : ProbComp (Bytes × Bool) := do
    let rkStar ← sampleBytes32
    let secb ← $ᵗ Bool
    pure (rkStar, secb)
  let full5 (rkStar : Bytes) :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthRkTrackedState S) ProbComp) +
      authRkTrackedImpl S P (fun s => if s == idx then pure rkStar else sampleBytes32) (fun s =>
          decide (s < idx))
  let full6 :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthRkTrackedState S) ProbComp) +
      authRkTrackedImpl S P (fun _ => sampleBytes32) (fun s => decide (s < idx + 1))
  let m5 (p : Bytes × Bool) : ProbComp (Bool × AuthRkTrackedState S) :=
    (simulateQ (full5 p.1) A.1.run).run (AuthHybridStateFixed.empty S p.2, [])
  let m6 (p : Bytes × Bool) : ProbComp (Bool × AuthRkTrackedState S) :=
    (simulateQ full6 A.1.run).run (AuthHybridStateFixed.empty S p.2, [])
  let fin (p : Bytes × Bool) (x : Bool × AuthRkTrackedState S) : ProbComp Bool :=
    finalizeAuthFixed P p.2 x.1 x.2.1.toAuthHybridState
  have hExp5 : 𝒟[authRkCutoffExp S P idx A.1] = 𝒟[mx >>= fun p => m5 p >>= fin p] := by
    rw [← evalDist_preSample_authRk_eq_cutoff S P idx A.1]
    simp only [mx, m5, fin, bind_assoc, pure_bind]
    refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun rkStar _ => ?_)
    refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
    rw [bind_simulateQ_authRkTrackedImpl P
      (fun s => if s == idx then pure rkStar else sampleBytes32) (fun s => decide (s < idx))
      A.1.run (AuthHybridStateFixed.empty S secb, [])
      (fun y => finalizeAuthFixed P secb y.1 y.2.toAuthHybridState)]
    rfl
  have hExp6 : 𝒟[authRkCutoffExp S P (idx + 1) A.1] = 𝒟[mx >>= fun p => m6 p >>= fin p] := by
    rw [← OracleComp.evalDist_bind_const sampleBytes32 (authRkCutoffExp S P (idx + 1) A.1)]
    unfold authRkCutoffExp
    simp only [mx, m6, fin, bind_assoc, pure_bind]
    refine OracleComp.evalDist_bind_congr_of_support sampleBytes32 _ _ (fun rkStar _ => ?_)
    refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
    rw [bind_simulateQ_authRkTrackedImpl P
      (fun _ => sampleBytes32) (fun s => decide (s < idx + 1))
      A.1.run (AuthHybridStateFixed.empty S secb, [])
      (fun y => finalizeAuthFixed P secb y.1 y.2.toAuthHybridState)]
    rfl
  rw [hExp5, hExp6]
  have hOuter :
      |(𝒟[mx >>= fun p => m5 p >>= fin p] {true}).toReal -
       (𝒟[mx >>= fun p => m6 p >>= fin p] {true}).toReal| ≤
      (𝒟[mx >>= fun p => m6 p >>= fun x => pure (badRkTracked p.1 x.2)] {true}).toReal := by
    let _ : MeasurableSpace (Bytes × Bool) := ⊤
    have _ : DiscreteMeasurableSpace (Bytes × Bool) := ⟨fun _ => trivial⟩
    have hEq : ∀ (f : Bytes × Bool → ProbComp Bool),
        𝒟[mx >>= f] {true} = probExpect mx (fun p => 𝒟[f p] {true}) := by
      intro f; unfold probExpect
      rw [evalDist_bind_of_discrete,
          MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
              Measurable.of_discrete.aemeasurable]
    have hPoint : ∀ p : Bytes × Bool,
        𝒟[m5 p >>= fin p] {true} ≤
          𝒟[m6 p >>= fin p] {true} + 𝒟[m6 p >>= fun x => pure (badRkTracked p.1 x.2)] {true} ∧
        𝒟[m6 p >>= fin p] {true} ≤
          𝒟[m5 p >>= fin p] {true} + 𝒟[m6 p >>= fun x => pure (badRkTracked p.1 x.2)] {true} :=
      fun p => simulateQ_authRkTrackedImpl_evalDist_bind_le P hP p.1 idx p.2 A.1.run
        (AuthHybridStateFixed.empty S p.2, []) (AuthHybridStateFixed.empty S p.2, [])
        ⟨AgreeOffRkAuth.empty P p.1 idx p.2, rfl⟩
    have h1 : 𝒟[mx >>= fun p => m5 p >>= fin p] {true} ≤
        𝒟[mx >>= fun p => m6 p >>= fin p] {true} +
        𝒟[mx >>= fun p => m6 p >>= fun x => pure (badRkTracked p.1 x.2)] {true} := by
      rw [hEq, hEq, hEq]
      exact probExpect_add_le mx _ _ _ (fun p => (hPoint p).1)
    have h2 : 𝒟[mx >>= fun p => m6 p >>= fin p] {true} ≤
        𝒟[mx >>= fun p => m5 p >>= fin p] {true} +
        𝒟[mx >>= fun p => m6 p >>= fun x => pure (badRkTracked p.1 x.2)] {true} := by
      rw [hEq, hEq, hEq]
      exact probExpect_add_le mx _ _ _ (fun p => (hPoint p).2)
    have hfin5 : 𝒟[mx >>= fun p => m5 p >>= fin p] {true} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one
    have hfin6 : 𝒟[mx >>= fun p => m6 p >>= fin p] {true} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one
    have hfinBad : 𝒟[mx >>= fun p => m6 p >>= fun x => pure (badRkTracked p.1 x.2)] {true} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one
    have h1r := (ENNReal.toReal_le_toReal hfin5 (ENNReal.add_ne_top.mpr ⟨hfin6, hfinBad⟩)).mpr h1
    have h2r := (ENNReal.toReal_le_toReal hfin6 (ENNReal.add_ne_top.mpr ⟨hfin5, hfinBad⟩)).mpr h2
    rw [ENNReal.toReal_add hfin6 hfinBad] at h1r
    rw [ENNReal.toReal_add hfin5 hfinBad] at h2r
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hSwap :
      𝒟[mx >>= fun p => m6 p >>= fun x => pure (badRkTracked p.1 x.2)] =
      𝒟[(do
          let secb ← $ᵗ Bool
          let x ← (simulateQ full6 A.1.run).run (AuthHybridStateFixed.empty S secb, [])
          let rkStar ← sampleBytes32
          pure (badRkTracked rkStar x.2))] := by
    simp only [mx, m6, bind_assoc, pure_bind]
    rw [OracleComp.evalDist_bind_bind_swap sampleBytes32 ($ᵗ Bool)]
    refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
    exact OracleComp.evalDist_bind_bind_swap sampleBytes32
      ((simulateQ full6 A.1.run).run (AuthHybridStateFixed.empty S secb, []))
      (fun rkStar x => pure (badRkTracked rkStar x.2))
  have hSend : IsQueryBoundP A.1.run (fun q => isAuthSendQueryB q = true) S.N_send_tot := by
    simpa only [isAuthSendQueryB_eq_true_iff] using A.2.2.1
  have hRecv : IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  have hRoRoot : IsQueryBoundP A.1.run (fun q => isAuthRoRootQueryB q = true) b.q_roRoot := by
    simpa only [isAuthRoRootQueryB_eq_true_iff] using A.2.2.2.2.1
  let K : Nat := b.q_roRoot + S.N_sess_tot
  have hBadBound :
      𝒟[(do
          let secb ← $ᵗ Bool
          let x ← (simulateQ full6 A.1.run).run (AuthHybridStateFixed.empty S secb, [])
          let rkStar ← sampleBytes32
          pure (badRkTracked rkStar x.2))] {true} ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256) := by
    let mAll : ProbComp (Bool × AuthRkTrackedState S) := do
      let secb ← $ᵗ Bool
      (simulateQ full6 A.1.run).run (AuthHybridStateFixed.empty S secb, [])
    have hAssoc :
        (do
          let secb ← $ᵗ Bool
          let x ← (simulateQ full6 A.1.run).run (AuthHybridStateFixed.empty S secb, [])
          let rkStar ← sampleBytes32
          pure (badRkTracked rkStar x.2)) =
        (mAll >>= fun x => sampleBytes32 >>= fun rkStar => pure (badRkTracked rkStar x.2)) := by
      simp [mAll, bind_assoc]
    rw [hAssoc]
    refine evalDist_bind_sampleBytes32_badRkTracked_le mAll K (fun y hy => ?_)
    simp only [mAll, MonadAttach.mem_support_bind] at hy
    rcases hy with ⟨secb, _, hy⟩
    have hLen := simulateQ_authRkTrackedImpl_length_le P
      (fun _ => sampleBytes32) (fun s => decide (s < idx + 1))
      A.1.run (AuthHybridStateFixed.empty S secb, []) S.N_send_tot S.N_recv_tot b.q_roRoot
      hSend hRecv hRoRoot y hy
    have hInit : (AuthHybridStateFixed.empty S secb).toAuthHybridState.base.rootRoCache.length = 0
        := rfl
    have hSess : S.N_sess_tot = S.N_send_tot + S.N_recv_tot := rfl
    dsimp only at hLen
    rw [hInit, List.length_nil] at hLen
    omega
  have hKFin : (K : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ) ^ 256) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top K) ENNReal.ofReal_ne_top
  have hBadReal :
      (𝒟[mx >>= fun p => m6 p >>= fun x => pure (badRkTracked p.1 x.2)] {true}).toReal ≤
      ((b.q_roRoot : ℝ) + (S.N_sess_tot : ℝ)) * (1 / (2 : ℝ) ^ 256) := by
    rw [hSwap]
    have hle := (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one) hKFin).mpr hBadBound
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at hle
    have hKCast : (K : ℝ) = (b.q_roRoot : ℝ) + (S.N_sess_tot : ℝ) := by
      dsimp only [K]; push_cast; rfl
    rw [hKCast] at hle
    exact hle
  exact le_trans hOuter hBadReal

/-- Sub-hop 1 (`G3.5 → G3.6`, `RootKdfRO`): replacing `evalRootKdfOrRo` with uniform keys loses at
    most `rootKdfRoTermReal S b.q_roRoot`. -/
theorem hop_G3_5_G3_6 (S : Setup) : AuthHopG3_5G3_6Stmt S := by
  intro P hP b A
  change |authFixedAdvAtStage .g3_5 S P A.val - authFixedAdvAtStage .g3_6 S P A.val| ≤
    rootKdfRoTermReal S b.q_roRoot
  rw [← authRkCutoffAdv_zero_eq_g3_5 S P A.val,
      ← authRkCutoffAdv_end_eq_g3_6 S P b A]
  let term : ℝ := 2 * (((b.q_roRoot : ℝ) + (S.N_sess_tot : ℝ)) * (1 / (2 : ℝ) ^ 256))
  have hStepAdv : ∀ idx : Nat,
      |authRkCutoffAdv S P idx A.1 - authRkCutoffAdv S P (idx + 1) A.1| ≤ term := by
    intro idx
    calc |authRkCutoffAdv S P idx A.1 - authRkCutoffAdv S P (idx + 1) A.1|
        ≤ 2 * |(𝒟[authRkCutoffExp S P idx A.1] {true}).toReal -
               (𝒟[authRkCutoffExp S P (idx + 1) A.1] {true}).toReal| :=
          abs_sub_boolBias_toReal_le_two_mul_abs_sub
            (authRkCutoffExp S P idx A.1) (authRkCutoffExp S P (idx + 1) A.1)
      _ ≤ term :=
          mul_le_mul_of_nonneg_left (authRkCutoffExp_step_le S P hP b A idx) (by norm_num)
  calc |authRkCutoffAdv S P 0 A.1 - authRkCutoffAdv S P S.N_sess_tot A.1|
      ≤ ∑ idx ∈ Finset.range S.N_sess_tot,
          |authRkCutoffAdv S P idx A.1 - authRkCutoffAdv S P (idx + 1) A.1| :=
        abs_sub_le_sum_range_postHandshake S.N_sess_tot (fun idx => authRkCutoffAdv S P idx A.1)
    _ ≤ ∑ _idx ∈ Finset.range S.N_sess_tot, term :=
        Finset.sum_le_sum (fun idx _ => hStepAdv idx)
    _ = (S.N_sess_tot : ℝ) * term := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = rootKdfRoTermReal S b.q_roRoot := by
        dsimp only [term, rootKdfRoTermReal]
        ring

end SignalPqxdh.Security.AuthSubHops1to3

theorem _root_.SignalPqxdh.Security.hop_G3_5_G3_6 (S : Setup) : AuthHopG3_5G3_6Stmt S :=
  SignalPqxdh.Security.AuthSubHops1to3.hop_G3_5_G3_6 S
