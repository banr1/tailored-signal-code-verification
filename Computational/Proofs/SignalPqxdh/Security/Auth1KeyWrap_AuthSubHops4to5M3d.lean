/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M3c
public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacHA2
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M2
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M3d
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthPrfHmacHA2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M1
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5M3a
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key multi-user `INT-CTXT` hop `G3.8 → G5`

One-key (`pqxdhAuthImpl1KeyG`) counterparts of the multi-key `INT-CTXT` coupling and
`G3.8 → split(.g3_8, .g5, true)` hop bounds in `AuthSubHops4to5M3d`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

private theorem muInv_of_recv_none_local {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} {keys : List (Nat × MessageKeys)}
    {chal : List (Nat × (Bytes × Bytes))}
    (hInv : MuInv S P hst (projectMuState P hst) keys chal) :
    MuInv S P { hst with recvCount := hst.recvCount + 1 }
      { projectMuState P hst with recvCount := hst.recvCount + 1 } keys chal :=
  ⟨rfl, hInv.hValid, hInv.hSess, hInv.hFresh, hInv.hChalLt, hInv.hRecv.succ⟩

private theorem muInv_of_recv_finish_local {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} {keys keys' : List (Nat × MessageKeys)}
    {chal : List (Nat × (Bytes × Bytes))}
    (hInv : MuInv S P hst (projectMuState P hst) keys chal)
    (hst' : AuthHybridState S) (cache' : AuthMkSaltCache S)
    (hV : ValidAuthLengths S hst')
    (hUsed : hst'.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions)
    (hIdeal : hst'.idealSessions = hst.toAuthHybridState.idealSessions)
    (hKeys : ∀ i, i < S.N_send_tot → keys'.lookup i = keys.lookup i)
    (hRecv : MuRecvInv S (hst.recvCount + 1) cache' keys') :
    MuInv S P { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache := cache' }
      { toAuthHybridState := projectMuHybrid P hst', recvCount := hst.recvCount + 1,
        mkSaltCache := maskMuCache cache' } keys' chal := by
  refine ⟨rfl, hV, ?_, ?_, hInv.hChalLt, hRecv⟩
  · intro s hs; dsimp only at hs ⊢; rw [hIdeal] at hs; rw [hUsed]
    rcases hInv.hSess s hs with ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, (hKeys _ h3).trans h4, h5⟩
  · intro sid hSend hNot; dsimp only at hNot ⊢; rw [hUsed] at hNot
    rcases hInv.hFresh sid hSend hNot with ⟨h1, h2⟩
    exact ⟨(hKeys _ (initSessionSlotIdx_lt_of_isSend hSend)).trans h1, h2⟩

theorem relProbDom_stepAuthMu1Key {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst hst6 : AuthHybridStateFixed S)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes)))
    (hInv : MuInv S P hst hst6 keys chal)
    (hNoWin : hst.toAuthHybridState.base.hasWonAuth = false) :
    RelProbDom
      (fun p5 p6 => p5.1 = p6.1.1 ∧ p5.2.2 = false ∧ p6.2.2.2 = false ∧
        MuInv S P p5.2.1 p6.1.2 p6.2.1 p6.2.2.1)
      (fun p6 => p6.2.2.2)
      ((pqxdhAuthForgeAllImpl1Key true .g5 S P q).run (hst, false))
      (runMu P (stepAuthMuPrim1Key S q hst6) (keys, chal, false)) := by
  have hStage : (AuthHybridStage.g3_8).idealMsgKeys = true := rfl
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthForgeAllImpl1Key stepAuthMuPrim1Key pqxdhAuthHybridSplitFixedImpl1Key
        pqxdhAuthHybridKoskImpl1Key
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      simpa only [map_eq_bind_pure_comp, Function.comp_def]
          using relProbDom_runAuthSend_mu P (.sendOPK u i) trivial
        (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
        u bundle m0 m1 hst hst6 keys chal hInv
    · rcases hInv.hProj with rfl
      simp only [↓reduceIte, StateT.run_pure, pure_bind, map_pure, runMu_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv.of_base_eq rfl hInv.hValid rfl rfl rfl rfl⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthForgeAllImpl1Key stepAuthMuPrim1Key pqxdhAuthHybridSplitFixedImpl1Key
        pqxdhAuthHybridKoskImpl1Key
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte, runAuthHybridSendKosk_eq,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      simpa only [map_eq_bind_pure_comp, Function.comp_def]
          using relProbDom_runAuthSend_mu P (.sendNoOPK u i) trivial
        (initSessionSlotIdx_sendNoOPK_lt u i) u bundle m0 m1 hst hst6 keys chal hInv
    · rcases hInv.hProj with rfl
      simp only [↓reduceIte, StateT.run_pure, pure_bind, map_pure, runMu_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv.of_base_eq rfl hInv.hValid rfl rfl rfl rfl⟩
  | recvOPK k j o msg =>
    rcases hInv.hProj with rfl
    rcases validAuthLengths_bounds S P hInv.hValid with ⟨hPrinLen, _, _, hSessLen⟩
    unfold pqxdhAuthForgeAllImpl1Key stepAuthMuPrim1Key
    dsimp only [StateT.run_mk]
    have hTo : (projectMuState P hst).toAuthHybridState =
        projectMuHybrid P hst.toAuthHybridState := rfl
    have hRc : (projectMuState P hst).recvCount = hst.recvCount := rfl
    have hMc : (projectMuState P hst).mkSaltCache = maskMuCache hst.mkSaltCache := rfl
    rw [runMu_embedPrimMu_bind, hTo,
        simulateQ_prepareAuthRecvOPKPrim_mu P k j o msg hst.toAuthHybridState hPrinLen hNoWin,
        pure_bind]
    cases hprep : prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
    | none =>
      simp only [Option.map_none, runMu_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, muInv_of_recv_none_local hInv⟩
    | some prep =>
      rcases prepareAuthHybridRecvOPK_valid_mu true P k j o msg hst.toAuthHybridState hInv.hValid
          hprep with ⟨hDecPrin, hDecUsed, hDecIdeal, hFinValid⟩
      simp only [Option.map_some, map_eq_bind_pure_comp, Function.comp_def, runMu_bind, hRc, hMc]
      refine RelProbDom.bind_rel
        (relProbDom_evalAuthRecvSchedule_mu P prep.hstDec hst.recvCount hst.mkSaltCache
          prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg keys chal
          (hDecPrin ▸ hPrinLen) (hDecIdeal ▸ hSessLen)
          (by rw [hDecIdeal]; exact fun s hs => ⟨(hInv.hSess s hs).2.2.2.1,
            (hInv.hSess s hs).2.2.2.2⟩)
          hInv.hChalLt hInv.hRecv)
        (fun b6 hb6 y6 hy6 => by
          simp only [runMu_pure, support_pure, Set.mem_singleton_iff] at hy6
          subst hy6; exact hb6)
        (fun b5 b6 ⟨hRes, hMc', hf5, hw6, hChal', hKeys', hRecv'⟩ => ?_)
      rcases b5 with ⟨⟨res5?, mkSaltCache5'⟩, forged5⟩
      rcases b6 with ⟨⟨res6?, mkSaltCache6'⟩, keys', chal', w'⟩
      dsimp only at hRes hMc' hf5 hw6 hChal' hKeys' hRecv'
      subst hRes hMc' hf5 hw6 hChal'
      simp only [Bool.false_or, runMu_pure]
      rcases hFinValid res5? with ⟨hVFin, hUsedFin, hIdealFin⟩
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl,
        muInv_of_recv_finish_local hInv _ _ hVFin hUsedFin hIdealFin hKeys' hRecv'⟩
  | recvNoOPK k j l msg =>
    rcases hInv.hProj with rfl
    rcases validAuthLengths_bounds S P hInv.hValid with ⟨hPrinLen, _, _, hSessLen⟩
    unfold pqxdhAuthForgeAllImpl1Key stepAuthMuPrim1Key
    dsimp only [StateT.run_mk]
    have hTo : (projectMuState P hst).toAuthHybridState =
        projectMuHybrid P hst.toAuthHybridState := rfl
    have hRc : (projectMuState P hst).recvCount = hst.recvCount := rfl
    have hMc : (projectMuState P hst).mkSaltCache = maskMuCache hst.mkSaltCache := rfl
    rw [runMu_embedPrimMu_bind, hTo,
        simulateQ_prepareAuthRecvNoOPKPrim_mu P k j l msg hst.toAuthHybridState hPrinLen hNoWin,
        pure_bind]
    cases hprep : prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
    | none =>
      simp only [Option.map_none, runMu_pure]
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl, muInv_of_recv_none_local hInv⟩
    | some prep =>
      rcases prepareAuthHybridRecvNoOPK_valid_mu true P k j l msg hst.toAuthHybridState
          hInv.hValid hprep with ⟨hDecPrin, hDecUsed, hDecIdeal, hFinValid⟩
      simp only [Option.map_some, map_eq_bind_pure_comp, Function.comp_def, runMu_bind, hRc, hMc]
      refine RelProbDom.bind_rel
        (relProbDom_evalAuthRecvSchedule_mu P prep.hstDec hst.recvCount hst.mkSaltCache
          prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg keys chal
          (hDecPrin ▸ hPrinLen) (hDecIdeal ▸ hSessLen)
          (by rw [hDecIdeal]; exact fun s hs => ⟨(hInv.hSess s hs).2.2.2.1,
            (hInv.hSess s hs).2.2.2.2⟩)
          hInv.hChalLt hInv.hRecv)
        (fun b6 hb6 y6 hy6 => by
          simp only [runMu_pure, support_pure, Set.mem_singleton_iff] at hy6
          subst hy6; exact hb6)
        (fun b5 b6 ⟨hRes, hMc', hf5, hw6, hChal', hKeys', hRecv'⟩ => ?_)
      rcases b5 with ⟨⟨res5?, mkSaltCache5'⟩, forged5⟩
      rcases b6 with ⟨⟨res6?, mkSaltCache6'⟩, keys', chal', w'⟩
      dsimp only at hRes hMc' hf5 hw6 hChal' hKeys' hRecv'
      subst hRes hMc' hf5 hw6 hChal'
      simp only [Bool.false_or, runMu_pure]
      rcases hFinValid res5? with ⟨hVFin, hUsedFin, hIdealFin⟩
      exact RelProbDom.of_pure ⟨rfl, rfl, rfl,
        muInv_of_recv_finish_local hInv _ _ hVFin hUsedFin hIdealFin hKeys' hRecv'⟩
  | initPrin _ | corruptIK _ | genSPK _ _ | genOPK _ _ _ | registerKey _ | roQuery _
  | roRootQuery _ _ | revealDhSecrets =>
    rcases hInv.hProj with rfl
    unfold pqxdhAuthForgeAllImpl1Key stepAuthMuPrim1Key
    dsimp only [StateT.run_mk]
    rw [runMu_embedPrimMu,
        simulateQ_stepAuthOtherPrim_projectMuState1Key P _ hst (by intro h; cases h)
            (by intro h; cases h) hNoWin]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, Prod.map]
    refine RelProbDom.bind_same_of_support _ (fun ⟨resp, hst'⟩ hy => ?_)
    rcases validAuthLengths_stepAuthOther_mu1Key P _ hst (by intro h; cases h) (by intro h; cases h)
        hNoWin hInv.hValid hy with
      ⟨hV', hUsed', hIdeal', hRc', hMc'⟩
    exact RelProbDom.of_pure ⟨rfl, rfl, rfl, hInv.of_base_eq rfl hV' hUsed' hIdeal' hRc' hMc'⟩

theorem pqxdhAuthForgeAllImpl_frozen_of_hasWonAuth1Key
    {S : Setup} (P : Primitives) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hWin : hst.toAuthHybridState.base.hasWonAuth = true)
    {p : (authSpec S).Range q × (AuthHybridStateFixed S × Bool)}
    (hp : p ∈ support ((pqxdhAuthForgeAllImpl1Key true .g5 S P q).run (hst, false))) :
    p.2.1.toAuthHybridState.base.hasWonAuth = true ∧ p.2.2 = false := by
  have hStage : (AuthHybridStage.g3_8).idealMsgKeys = true := rfl
  cases q with
  | recvOPK k j o msg =>
    unfold pqxdhAuthForgeAllImpl1Key prepareAuthHybridRecvOPK at hp
    simp only [hWin, Bool.true_and, ↓reduceIte, StateT.run_mk, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hWin, rfl⟩
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthForgeAllImpl1Key prepareAuthHybridRecvNoOPK at hp
    simp only [hWin, Bool.true_and, ↓reduceIte, StateT.run_mk, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hWin, rfl⟩
  | _ =>
    unfold pqxdhAuthForgeAllImpl1Key pqxdhAuthHybridSplitFixedImpl1Key
      pqxdhAuthHybridKoskImpl1Key at hp
    simp only [hStage, hWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      StateT.run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_pure, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hWin, rfl⟩

theorem simulateQ_authForgeAll_forged_false_of_hasWonAuth1Key
    {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthHybridStateFixed S)
    (hWin : hst.toAuthHybridState.base.hasWonAuth = true)
    {p : α × (AuthHybridStateFixed S × Bool)}
    (hp : p ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthHybridStateFixed S × Bool) ProbComp) +
      pqxdhAuthForgeAllImpl1Key true .g5 S P) oa).run (hst, false))) :
    p.2.1.toAuthHybridState.base.hasWonAuth = true ∧ p.2.2 = false := by
  induction oa using OracleComp.inductionOn generalizing hst with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact ⟨hWin, rfl⟩
  | query_bind q mx ih =>
    rcases q with uq | aq
    · rw [FgGapDh.simulateQ_run_query_inl] at hp
      rcases MonadAttach.mem_support_bind.mp hp with ⟨u, _, hp'⟩
      exact ih u hst hWin hp'
    · rw [FgGapDh.simulateQ_run_query_inr] at hp
      rcases MonadAttach.mem_support_bind.mp hp with ⟨⟨r, hst', f'⟩, hq, hp'⟩
      rcases pqxdhAuthForgeAllImpl_frozen_of_hasWonAuth1Key P aq hst hWin hq with ⟨hWin', rfl⟩
      exact ih r hst' hWin' hp'

theorem relProbDomZ_runWithMuStep1Key {S : Setup} {α : Type} (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α)
    (hst hst6 : AuthHybridStateFixed S)
    (keys : List (Nat × MessageKeys)) (chal : List (Nat × (Bytes × Bytes)))
    (hInv : MuInv S P hst hst6 keys chal) :
    let impl :=
        (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
            ProbComp) +
      pqxdhAuthForgeAllImpl1Key true .g5 S P
    RelProbDomZ
      (fun p5 p6 => p5.1 = p6.1.1 ∧ p5.2.2 = false ∧ p6.2.2.2 = false ∧
        MuInv S P p5.2.1 p6.1.2 p6.2.1 p6.2.2.1)
      (fun p5 => p5.2.2)
      (fun p6 => p6.2.2.2)
      ((simulateQ impl oa).run (hst, false))
      (runMu P (runWithMuStep (stepAuthMuPrim1Key S) oa hst6) (keys, chal, false)) := by
  intro impl
  induction oa using OracleComp.inductionOn generalizing hst hst6 keys chal with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, runWithMuStep_pure, runMu_pure]
    exact RelProbDomZ.of_pure ⟨rfl, rfl, rfl, hInv⟩
  | query_bind q mx ih =>
    rcases q with uq | aq
    · dsimp only [impl]
      rw [FgGapDh.simulateQ_run_query_inl, runWithMuStep_query_inl, runMu_bind,
          runMu_query_inl, bind_assoc]
      refine RelProbDomZ.bind_same (QueryImpl.ofLift unifSpec ProbComp uq) (fun u => ?_)
      rw [pure_bind]
      exact ih u hst hst6 keys chal hInv
    · by_cases hWin : hst.toAuthHybridState.base.hasWonAuth = true
      · exact RelProbDomZ.of_bad5_false _ _ (fun y5 hy5 =>
          (simulateQ_authForgeAll_forged_false_of_hasWonAuth1Key P
            (liftM (OracleSpec.query (Sum.inr aq)) >>= mx) hst hWin hy5).2)
      · have hNoWin := Bool.eq_false_iff.mpr hWin
        dsimp only [impl]
        rw [FgGapDh.simulateQ_run_query_inr, runWithMuStep_query_inr, runMu_bind]
        refine RelProbDomZ.bind_rel
          (relProbDom_stepAuthMu1Key P aq hst hst6 keys chal hInv hNoWin)
          (fun b6 hb6 y6 hy6 => by
            rcases b6 with ⟨⟨r6, hst6'⟩, keys', chal', w'⟩
            dsimp only at hb6; subst hb6
            exact runMu_w_mono P _ keys' chal' y6 hy6)
          (fun b5 b6 ⟨h1, h2, h3, hInv'⟩ => ?_)
        rcases b5 with ⟨r5, hst5', forged5⟩
        rcases b6 with ⟨⟨r6, hst6'⟩, keys', chal', w'⟩
        dsimp only at h1 h2 h3 hInv'
        subst h1 h2 h3
        exact ih r5 hst5' hst6' keys' chal' hInv'

/-- Bounds `authIntForgeAllExp1Key` by the multi-key `INT-CTXT` advantage of `aeadMuIntReductionAuth1Key`. -/
theorem authIntForgeAllExp_le_aeadMuIntCtxt1Key (S : Setup) (P : Primitives)
    (hP : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (𝒟[authIntForgeAllExp1Key S P A.1] {true}).toReal ≤
      AeadMuIntCtxt P (aeadMuIntReductionAuth1Key S b A) := by
  unfold AeadMuIntCtxt
  rw [aeadMuIntCtxtExp_eq_runMu_of_disciplined P (aeadMuIntReductionAuth1Key S b A)
    (aeadMuIntReductionAuth_disciplined1Key S P hP hLaw b A)]
  have hRed : (runMu P (aeadMuIntReductionAuth1Key S b A).run ([], [], false) >>=
      fun p => pure p.2.2.2) =
    ($ᵗ Bool >>= fun secb =>
      runMu P (runWithMuStep (stepAuthMuPrim1Key S) A.1.run (AuthHybridStateFixed.empty S secb))
        ([], [], false) >>= fun p6 => pure p6.2.2.2) := by
    unfold aeadMuIntReductionAuth1Key aeadMuIntReductionAuthRun1Key
    dsimp only
    simp only [runMu_bind, runMu_unifMu, runMu_pure, bind_assoc, pure_bind]
  have hForge : authIntForgeAllExp1Key S P A.1 =
    ($ᵗ Bool >>= fun secb =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S ×
          Bool) ProbComp) +
        pqxdhAuthForgeAllImpl1Key true .g5 S P) A.1.run).run
        (AuthHybridStateFixed.empty S secb, false) >>= fun p5 => pure p5.2.2) := by
    unfold authIntForgeAllExp1Key; rfl
  rw [hRed, hForge]
  have hDom : RelProbDomZ
      (fun (p5 : Bool × (AuthHybridStateFixed S × Bool)) p6 =>
        p5.1 = p6.1.1 ∧ p5.2.2 = false ∧ p6.2.2.2 = false ∧
        MuInv S P p5.2.1 p6.1.2 p6.2.1 p6.2.2.1)
      (fun p5 => p5.2.2)
      (fun p6 => p6.2.2.2)
      ($ᵗ Bool >>= fun secb =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S
            × Bool) ProbComp) +
          pqxdhAuthForgeAllImpl1Key true .g5 S P) A.1.run).run
          (AuthHybridStateFixed.empty S secb, false))
      ($ᵗ Bool >>= fun secb =>
        runMu P (runWithMuStep (stepAuthMuPrim1Key S) A.1.run (AuthHybridStateFixed.empty S secb))
          ([], [], false)) :=
    RelProbDomZ.bind_same ($ᵗ Bool) (fun secb =>
      relProbDomZ_runWithMuStep1Key P A.1.run
        (AuthHybridStateFixed.empty S secb) (AuthHybridStateFixed.empty S secb) [] []
        (muInv_empty S P secb))
  have hLe := RelProbDomZ.evalDist_le hDom (fun _ _ ⟨_, hFalse, _, _⟩ => hFalse)
  simp only [bind_assoc] at hLe
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one) hLe

theorem auth_hop_G3_8_split_g5_le_mu1Key (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (hLaw : ∀ p e, P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    |(𝒟[authFixedExpG3_8_1Key S P A.1] {true}).toReal -
     (𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A.1] {true}).toReal| ≤
      AeadMuIntCtxt P (aeadMuIntReductionAuth1Key S b A) :=
  (auth_hop_G3_8_split_g5_le_forgeAll1Key S P hWF A.1).trans
    (authIntForgeAllExp_le_aeadMuIntCtxt1Key S P hWF hLaw b A)

/-- Bounds the `boolBias` gap between `G3.8` and `split(.g3_8, .g5, true)` by multi-key `INT-CTXT`. -/
theorem auth_hop_G3_8_split_g5_boolBias_le_mu1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |authFixedAdvG3_8_1Key S P A.1 -
     (𝒟[authSplitFixedExp1Key .g3_8 .g5 true S P A.1].boolBias).toReal| ≤
      2 * AeadMuIntCtxt P (aeadMuIntReductionAuth1Key S b A) := by
  unfold authFixedAdvG3_8_1Key
  have hBias := abs_sub_boolBias_toReal_le_two_mul_abs_sub
    (authFixedExpG3_8_1Key S P A.1) (authSplitFixedExp1Key .g3_8 .g5 true S P A.1)
  have hHop :=
    auth_hop_G3_8_split_g5_le_mu1Key S P hP.toWellFormedPrimitivesδ hP.pow8_base_len b A
  linarith

end SignalPqxdh.Security
