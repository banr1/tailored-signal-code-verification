/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaShallow
import Computational.Proofs.GameHop.ReductionDsl.PeelSim
import VCVio.EvalDist.Monad.Basic

/-!
# Send Branch of the `Auth` `AeadIndCpa` Reduction

Proves evaluation equivalence between the DSL send handlers (`cpaSendB`, `cpaSendSlotB`) and
their shallow counterparts (`cpaSendShOpk`/`cpaSendShNoOpk`, `cpaSendSlotShOpk`/`cpaSendSlotShNoOpk`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open SignalPqxdh.Security.ReductionDsl.AuthPrf hiding queryPrim_eval
open Computational.Proofs.GameHop.ReductionDsl
open OracleSpec OracleComp

section Send

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}

/-! ## Helpers -/

theorem cpS_any_sid_iff {S : Setup} (l : List (SessionId S)) (P : sessionIdTy.denote → Bool)
    (sid : SessionId S) (hP : ∀ x, P (sessionIdToVal x) = (sid == x)) :
    (l.map sessionIdToVal).any P = l.contains sid := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.any_cons, hP, ih, List.contains_cons]

theorem cpS_hkdf_eq (c : List (Bytes × DRKey)) (sec : Bytes) :
    AuthSubHops1to3.evalHkdfRoPure c sec = evalHkdfRoPure c sec := rfl

@[simp] theorem getDBytes_eval {Γ : List PT} (o : Expr pqxdhOps Γ (.opt (B 32))) (env : Env Γ) :
    (getDBytes o).eval env = (o.eval env).getD [] := by
  simp only [getDBytes, eCaseOpt, v, litB_eval, Expr.eval, Ext.wk, Env.get_zero]
  cases o.eval env <;> rfl

macro "cps_pt" : tactic =>
  `(tactic| first | rfl | (rw [← $(Lean.mkIdent `hi):ident]; rfl))

macro "cps_hs" : tactic =>
  `(tactic| first | (simp only [Ext.step_wk, Env.get_succ, $(Lean.mkIdent `hs):ident]; done) |
    exact $(Lean.mkIdent `hs):ident | erw [$(Lean.mkIdent `hs):ident])

/-! ## Main lemmas -/

theorem spkHonIdealFromPeerC_eval (st : Var Γ₁ authStateTy)
    (pp : Var Γ₂ (.opt (.prod .nat principalEntryTy))) (bu : Var Γ₃ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (s : AuthState S) (peer? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput)
    (hs : Env.get env (h₁.wk st) = authStateToVal s)
    (hp : Env.get env (h₂.wk pp) = peer?.map (Prod.map id principalEntryToVal))
    (hb : Env.get env (h₃.wk bu) = preKeyBundleToVal bundle)
    (hSpk : s.spkBundles.length ≤ K) :
    (spkHonIdealFromPeerC S K st pp bu).eval env =
      checkBundleSpkHonIdealFromPeerPrim S peer? s.spkBundles bundle := by
  unfold spkHonIdealFromPeerC checkBundleSpkHonIdealFromPeerPrim
  rw [caseOptV_eval]
  simp only [v, Expr.eval, hp]
  rcases peer? with _ | ⟨k, pEntry⟩
  · rfl
  simp only [Option.map_some, Prod.map, id_eq, letV, anyMV, bindV, eval_letC,
    anyML_eq_anyMPrim, queryPrim_eval, queryPrim_pow8_eval, boolOr_eval, bytesBeq_eval,
    natEq_eval, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, asSpkBundles, sbSpkPk, pkbSpkB,
    peCorrupted, hs, hb, authStateToVal, preKeyBundleToVal, bundleV, principalEntryToVal,
    spkBundleEntryToVal, take_min_map_of_le _ _ hSpk, ← List.map_take, anyMPrim_map]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finishCpaC_eval (fhst : Var Γ₁ authHybridStateFixedTy) [h₁ : Ext Γ₁ Δ] (env : Env Δ)
    (fresh isIdeal : Expr pqxdhOps Δ .bool) (pE : Expr pqxdhOps Δ cpaPayloadTy) (ctE : Expr pqxdhOps Δ (B 32))
    (hst : AuthHybridStateFixed S) (p : AuthCpaPausePayload S)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hp : pE.eval env = cpaPayloadToVal p) :
    (finishCpaC fhst fresh isIdeal pE ctE).eval env =
      pure (Prod.map authRespToVal authHybridStateFixedToVal
        (finishAuthCpaSendFixedPure (fresh.eval env) (isIdeal.eval env) p (ctE.eval env) hst)) := by
  simp only [finishCpaC, letV, v, ahsfHybrid, ahsBase, hdMk, pmMk, peIkAPk, pkbSpkId, pkbOpkB?,
    pkbPqspkId, optFst,
    seMk, pkbIkB, pkbSpkB, pkbPqspkB, optSnd, eCaseOpt, ikrMk, isSomeE_eval, iasMk, defaultMsgKeysE,
    ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsfUpd,
    ahsfMkSlots, ahsfSlots,
    ahsfRecvCount, ahsfMkSaltCache,
    stUpd, stMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, aSendFresh, aSendUnfresh, eval_letC, bytesBeq_eval, litB_eval, Comp.eval,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hs, hp, cpaPayloadToVal]
  unfold finishAuthCpaSendFixedPure
  cases p.peerPrin? <;>
    rcases hob : p.bundle.opkB? with _ | ⟨oid, opk⟩ <;>
    cases isIdeal.eval env <;>
    simp [hob, authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
      sessionIdToVal, sidV, principalEntryToVal, preKeyBundleToVal, bundleV, drKeyToVal, drKeyV,
      msgKeysToVal, msgKeysV, authSessionEntryToVal, initKemRecordToVal, idealAuthSessionToVal,
      preKeyMsgV, hdrV, bne]

set_option maxHeartbeats 4000000 in
theorem cpaSendB_eval_opk (allowPause : Bool) (idxV : Var Γ₁ .nat)
    (fhst : Var Γ₂ authHybridStateFixedTy) (x : Var Γ₃ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (idx : Nat) (hst : AuthHybridStateFixed S) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hi : Env.get env (h₁.wk idxV) = idx)
    (hs : Env.get env (h₂.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₃.wk x) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AuthListsBounded K hst) :
    (cpaSendB S K true allowPause idxV fhst x).eval env =
      cpaSendResToVal <$> cpaSendShOpk S allowPause idx u i b m0 m1 hst := by
  have hN : S.N_id ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt u.isLt)
  simp only [cpaSendShOpk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp only [cpaSendB, sendGuardE, ↓reduceIte, v, letV, eval_letC, Comp.eval, Expr.eval,
      isSomeE_eval, pkbOpkB?, hx, preKeyBundleToVal, bundleV, hb,
      Option.isNone_none, map_pure, aNone, hs, Ext.step_wk, Env.get_succ]
    rfl
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  simp only [cpaSendB, sendGuardE, ↓reduceIte, v, letV, bindV, caseOptV, eCaseOpt, eFind,
    eAny, eval_letC, bytesLen_eval, bytesBeq_eval, boolOr_eval, isSomeE_eval,
    encEC_eval, encKEM_eval, natEq_eval, natLt_expr_eval, getDBytes_eval, optSnd_eval,
    samplePrim_bytes32_eval, samplePrim_drKey96_eval, samplePrim_msgKeys80_eval,
    queryPrim_eval, queryPrim_sigVerify_eval, queryPrim_kemEncaps_eval,
    queryPrim_x25519Base_eval, queryPrim_x25519_eval, queryPrim_chainKdfSeed_eval,
    queryPrim_chainKdfNext_eval, queryPrim_spqrInitSend_eval, queryPrim_deriveMsgKeys_eval,
    queryPrim_aeadEnc_eval, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hx, hs, hi, hb, preKeyBundleToVal, bundleV,
    authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    ahsfHybrid, ahsBase, asUsedSendSessions, asPrincipals,
    pkbIkB, pkbSpkB, pkbSpkSig, pkbPqspkB, pkbPqspkSig, pkbOpkB?, peCorrupted, peSecIKA0,
    aNone, PeelSim.take_map_of_le _ _ hB.usedSendSessions_le, PeelSim.take_map_of_le _ _ hB.principals_le]
  simp only [tryPauseAuthCpaSendFixedPrim, prepAuthCpaSendFixedPrim, PeelSim.ite_bind, pure_bind,
    bind_assoc]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]
    rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [cpS_any_sid_iff _ _ (SessionId.sendOPK u i)]
  swap
  · intro y
    rw [sidEq_eval _ _ _ y (SessionId.sendOPK u i) rfl rfl]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
  by_cases hsid :
      hst.toAuthHybridState.base.usedSendSessions.contains (SessionId.sendOPK u i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte]
  simp only [List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑u) hst.toAuthHybridState.base.principals = none
  · simp only [hp, Option.map_none, pure_bind, map_pure]; rfl
  obtain ⟨⟨uIdx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq, bind_assoc, pure_bind, PeelSim.ite_bind]
  refine PeelSim.peel_bind (m := OracleComp PrimBaseSpec) _
    (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ _ _ hst.toAuthHybridState.base (by simp) hB.principals_le]
    simp only [Expr.eval, Env.get_succ, Env.get_zero]
  refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine PeelSim.peel_bind_same _ ?_ (fun ok => ?_)
  · rw [koskBundleOkC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
      (by simp [hb, bundleV]) hB.advKeys_le hB.principals_le
        hB.spkBundles_le hB.opkEntries_le]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun ekASk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun kemCoins => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun ephASk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun spqrCoins => ?_)
  refine PeelSim.peel_bind_same _ (by rcases peer with _ | ⟨k, pE⟩ <;> rfl) (fun v1 => ?_)
  refine PeelSim.peel_bind_same _ (by rcases peer with _ | ⟨k, pE⟩ <;> rfl) (fun v2 => ?_)
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact PeelSim.peel_pure _ rfl
  simp only [bind_assoc, PeelSim.ite_bind, hb]
  refine PeelSim.peel_bind_same _ rfl (fun ekAPk => ?_)
  refine PeelSim.peel_bind_same _ ?_ (fun prov => ?_)
  · rw [checkBundleProvenanceExactC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
      (by simp [hb, bundleV]) hB.spkBundles_le
        hB.principals_le hB.opkEntries_le]
  rcases prov with ⟨sh, oh, ph⟩
  refine PeelSim.peel_bind_same _ ?_ (fun shi => ?_)
  · rw [spkHonIdealFromPeerC_eval S K _ _ _ _ hst.toAuthHybridState.base peer b (by simp) (by simp)
      (by simp [hb, bundleV]) hB.spkBundles_le]
  refine PeelSim.peel_bind_same _ rfl (fun dh1 => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dh2 => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dh3 => ?_)
  refine PeelSim.peel_bind_same _ ?_ (fun dh4 => ?_)
  · rw [hb]; rfl
  refine PeelSim.peel_bind_same _ rfl (fun ephAPk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dhR => ?_)
  rcases peer with _ | ⟨k, pE⟩
  · simp only [Option.map_none, Option.isSome_none, Bool.false_or, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_ (fun dro => ?_)
    · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
      simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero, Option.map_some,
        cpS_hkdf_eq]
    refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
    · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
    refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
    rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
    · simp only [pure_bind, map_pure]; rfl
    simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
    refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
    · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ rfl
      simp [firstMsgADE_eval, peIkAPk, Expr.eval, principalEntryToVal]
    refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
    · simp only [Ext.step_wk, Env.get_succ, hs]
    · simp [cpaPayloadToVal, Expr.eval, peIkAPk, principalEntryToVal, preKeyBundleToVal, bundleV,
        sessionIdToVal, sidV, hb]
  · rcases hc : pE.corrupted with _ | _
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_false,
        Bool.true_or, Option.isSome_some, Bool.true_and, ↓reduceIte]
      refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
      simp only [pure_bind, bind_assoc]
      refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
      rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
      · simp only [pure_bind, map_pure]; rfl
      simp only [pure_bind, ↓reduceIte]
      cases allowPause <;>
        simp only [↓reduceIte, Bool.false_eq_true, Bool.true_and, Bool.false_and, id,
          Comp.eval, Expr.eval, v, natEq_eval,
          sessionSlotIndexE, eCaseSum, hN, Nat.mul_comm S.N_send_opk,
          initSessionSlotIdx, Env.get_succ, Env.get_zero, samplePrim_msgKeys80_eval,
          queryPrim_eval, queryPrim_aeadEnc_eval]
      · refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
        refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
        · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
          · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
          · cps_pt
        refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
        · cps_hs
        · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV]
      · refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ ?_) (fun _ => ?_)
        · rw [← hi]; exact Iff.rfl
        · simp [cpaSendResToVal, cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV, hs]
        refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
        refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
        · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
          · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
          · cps_pt
        refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
        · cps_hs
        · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV]
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_true,
        Bool.false_or, Option.isSome_some, Bool.true_and]
      cases shi <;> cases ph <;> simp only [Bool.false_eq_true, Bool.and_false, Bool.and_true,
        ↓reduceIte]
      all_goals first
        | (refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_
              (fun dro => ?_)
           · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
             simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero,
               cpS_hkdf_eq]
           refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
           · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
           refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [pure_bind, map_pure]; rfl
           simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
           refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
           refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
           · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
             · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
             · cps_pt
           refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
           · cps_hs
           · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
               principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc,
               sessionIdToVal, sidV])
        | (refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
           simp only [pure_bind, bind_assoc]
           refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [pure_bind, map_pure]; rfl
           simp only [pure_bind, ↓reduceIte]
           refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
           refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
           · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
             · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
             · cps_pt
           refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
           · cps_hs
           · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
               principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
               sessionIdToVal, sidV])


set_option maxHeartbeats 4000000 in
theorem cpaSendB_eval_noopk (allowPause : Bool) (idxV : Var Γ₁ .nat)
    (fhst : Var Γ₂ authHybridStateFixedTy) (x : Var Γ₃ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] (env : Env Δ)
    (idx : Nat) (hst : AuthHybridStateFixed S) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hi : Env.get env (h₁.wk idxV) = idx)
    (hs : Env.get env (h₂.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₃.wk x) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AuthListsBounded K hst) :
    (cpaSendB S K false allowPause idxV fhst x).eval env =
      cpaSendResToVal <$> cpaSendShNoOpk S allowPause idx u i b m0 m1 hst := by
  have hN : S.N_id ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt u.isLt)
  simp only [cpaSendShNoOpk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  swap
  · simp only [cpaSendB, sendGuardE, Bool.false_eq_true, ↓reduceIte, v, letV, eval_letC,
      Comp.eval, Expr.eval, isSomeE_eval, pkbOpkB?, hx, preKeyBundleToVal, bundleV, hb,
      Option.isSome_some, map_pure, aNone, hs, Ext.step_wk, Env.get_succ]
    rfl
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [cpaSendB, sendGuardE, ↓reduceIte, v, letV, bindV, caseOptV, eCaseOpt, eFind,
    eAny, eval_letC, bytesLen_eval, bytesBeq_eval, boolOr_eval, isSomeE_eval,
    encEC_eval, encKEM_eval, natEq_eval, natLt_expr_eval, getDBytes_eval, optSnd_eval,
    samplePrim_bytes32_eval, samplePrim_drKey96_eval, samplePrim_msgKeys80_eval,
    queryPrim_eval, queryPrim_sigVerify_eval, queryPrim_kemEncaps_eval,
    queryPrim_x25519Base_eval, queryPrim_x25519_eval, queryPrim_chainKdfSeed_eval,
    queryPrim_chainKdfNext_eval, queryPrim_spqrInitSend_eval, queryPrim_deriveMsgKeys_eval,
    queryPrim_aeadEnc_eval, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hx, hs, hi, hb, preKeyBundleToVal, bundleV,
    authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    ahsfHybrid, ahsBase, asUsedSendSessions, asPrincipals,
    pkbIkB, pkbSpkB, pkbSpkSig, pkbPqspkB, pkbPqspkSig, pkbOpkB?, peCorrupted, peSecIKA0,
    aNone, PeelSim.take_map_of_le _ _ hB.usedSendSessions_le, PeelSim.take_map_of_le _ _ hB.principals_le,
    Bool.false_eq_true]
  simp only [tryPauseAuthCpaSendFixedPrim, prepAuthCpaSendFixedPrim, PeelSim.ite_bind, pure_bind,
    bind_assoc]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]
    rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [cpS_any_sid_iff _ _ (SessionId.sendNoOPK u i)]
  swap
  · intro y
    rw [sidEq_eval _ _ _ y (SessionId.sendNoOPK u i) rfl rfl]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
  by_cases hsid :
      hst.toAuthHybridState.base.usedSendSessions.contains (SessionId.sendNoOPK u i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte]
  simp only [List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑u) hst.toAuthHybridState.base.principals = none
  · simp only [hp, Option.map_none, pure_bind, map_pure]; rfl
  obtain ⟨⟨uIdx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq, bind_assoc, pure_bind, PeelSim.ite_bind]
  refine PeelSim.peel_bind (m := OracleComp PrimBaseSpec) _
    (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ _ _ hst.toAuthHybridState.base (by simp) hB.principals_le]
    simp only [Expr.eval, Env.get_succ, Env.get_zero]
  refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine PeelSim.peel_bind_same _ ?_ (fun ok => ?_)
  · rw [koskBundleOkC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
      (by simp [hb, bundleV]) hB.advKeys_le hB.principals_le
        hB.spkBundles_le hB.opkEntries_le]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun ekASk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun kemCoins => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun ephASk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun spqrCoins => ?_)
  refine PeelSim.peel_bind_same _ (by rcases peer with _ | ⟨k, pE⟩ <;> rfl) (fun v1 => ?_)
  refine PeelSim.peel_bind_same _ (by rcases peer with _ | ⟨k, pE⟩ <;> rfl) (fun v2 => ?_)
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact PeelSim.peel_pure _ rfl
  simp only [bind_assoc, PeelSim.ite_bind, hb]
  refine PeelSim.peel_bind_same _ rfl (fun ekAPk => ?_)
  refine PeelSim.peel_bind_same _ ?_ (fun prov => ?_)
  · rw [checkBundleProvenanceExactC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
      (by simp [hb, bundleV]) hB.spkBundles_le
        hB.principals_le hB.opkEntries_le]
  rcases prov with ⟨sh, oh, ph⟩
  refine PeelSim.peel_bind_same _ ?_ (fun shi => ?_)
  · rw [spkHonIdealFromPeerC_eval S K _ _ _ _ hst.toAuthHybridState.base peer b (by simp) (by simp)
      (by simp [hb, bundleV]) hB.spkBundles_le]
  refine PeelSim.peel_bind_same _ rfl (fun dh1 => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dh2 => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dh3 => ?_)
  refine PeelSim.peel_bind_same _ ?_ (fun dh4 => ?_)
  · rw [hb]
  refine PeelSim.peel_bind_same _ rfl (fun ephAPk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dhR => ?_)
  rcases peer with _ | ⟨k, pE⟩
  · simp only [Option.map_none, Option.isSome_none, Bool.false_or, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_ (fun dro => ?_)
    · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
      simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero,
        cpS_hkdf_eq]
    refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
    · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
    refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
    rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
    · simp only [pure_bind, map_pure]; rfl
    simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
    refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
    · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ rfl
      simp [firstMsgADE_eval, peIkAPk, Expr.eval, principalEntryToVal]
    refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
    · simp only [Ext.step_wk, Env.get_succ, hs]
    · simp [cpaPayloadToVal, Expr.eval, peIkAPk, principalEntryToVal, preKeyBundleToVal, bundleV,
        sessionIdToVal, sidV, hb]
  · rcases hc : pE.corrupted with _ | _
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_false,
        Bool.true_or, Option.isSome_some, Bool.true_and, ↓reduceIte]
      refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
      simp only [pure_bind, bind_assoc]
      refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
      rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
      · simp only [pure_bind, map_pure]; rfl
      simp only [pure_bind, ↓reduceIte]
      cases allowPause <;>
        simp only [↓reduceIte, Bool.false_eq_true, Bool.true_and, Bool.false_and, id,
          Comp.eval, Expr.eval, v, natEq_eval,
          sessionSlotIndexE, eCaseSum, hN, Nat.mul_comm S.N_send_no_opk,
          initSessionSlotIdx, Env.get_succ, Env.get_zero, samplePrim_msgKeys80_eval,
          queryPrim_eval, queryPrim_aeadEnc_eval]
      · refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
        refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
        · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
          · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
          · cps_pt
        refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
        · cps_hs
        · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV]
      · refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ ?_) (fun _ => ?_)
        · rw [← hi]; exact Iff.rfl
        · simp [cpaSendResToVal, cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV, hs]
        refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
        refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
        · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
          · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
          · cps_pt
        refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
        · cps_hs
        · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV]
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_true,
        Bool.false_or, Option.isSome_some, Bool.true_and]
      cases shi <;> cases ph <;> simp only [Bool.false_eq_true, Bool.and_false, Bool.and_true,
        ↓reduceIte]
      all_goals first
        | (refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_
              (fun dro => ?_)
           · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
             simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero,
               Option.map_none, cpS_hkdf_eq]
           refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
           · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
           refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [pure_bind, map_pure]; rfl
           simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
           refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
           refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
           · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
             · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
             · cps_pt
           refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
           · cps_hs
           · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
               principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc,
               sessionIdToVal, sidV])
        | (refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
           simp only [pure_bind, bind_assoc]
           refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [pure_bind, map_pure]; rfl
           simp only [pure_bind, ↓reduceIte]
           refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
           refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
           · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
             · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
             · cps_pt
           refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) rfl
           · cps_hs
           · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
               principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
               sessionIdToVal, sidV])

end Send

section SendSlot

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

local macro "cps_slot_pt" : tactic =>
  `(tactic| first | rfl | (simp only [Ext.step_wk, Env.get_succ, $(Lean.mkIdent `hi):ident,
    $(Lean.mkIdent `hns):ident]; rfl))

local macro "cps_slot_ret" : tactic =>
  `(tactic| (simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Env.get_succ, Env.get_zero,
    $(Lean.mkIdent `hns):ident, Prod.map, cpaSlotSendResToVal]; rfl))

set_option maxHeartbeats 4000000 in
theorem cpaSendSlotB_eval_opk (allowPause : Bool) (idxV : Var Γ₁ .nat) (nsV : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (idx ns : Nat) (hst : AuthHybridStateFixed S) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hi : Env.get env (h₁.wk idxV) = idx)
    (hns : Env.get env (h₂.wk nsV) = ns)
    (hs : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₄.wk x) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AuthListsBounded K hst) :
    (cpaSendSlotB S K true allowPause idxV nsV fhst x).eval env =
      cpaSlotSendResToVal <$> cpaSendSlotShOpk S allowPause idx u i b m0 m1 (ns, hst) := by
  simp only [cpaSendSlotShOpk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp only [cpaSendSlotB, sendGuardE, ↓reduceIte, v, letV, eval_letC, Comp.eval, Expr.eval,
      isSomeE_eval, pkbOpkB?, hx, preKeyBundleToVal, bundleV, hb,
      Option.isNone_none, map_pure, aNone, hs, hns, Ext.step_wk, Env.get_succ]
    rfl
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  simp only [cpaSendSlotB, sendGuardE, ↓reduceIte, v, letV, bindV, caseOptV, eCaseOpt, eFind,
    eAny, eval_letC, bytesLen_eval, bytesBeq_eval, boolOr_eval, isSomeE_eval,
    encEC_eval, encKEM_eval, natEq_eval, natLt_expr_eval, getDBytes_eval, optSnd_eval,
    samplePrim_bytes32_eval, samplePrim_drKey96_eval, samplePrim_msgKeys80_eval,
    queryPrim_eval, queryPrim_sigVerify_eval, queryPrim_kemEncaps_eval,
    queryPrim_x25519Base_eval, queryPrim_x25519_eval, queryPrim_chainKdfSeed_eval,
    queryPrim_chainKdfNext_eval, queryPrim_spqrInitSend_eval, queryPrim_deriveMsgKeys_eval,
    queryPrim_aeadEnc_eval, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hx, hs, hi, hns, hb, preKeyBundleToVal, bundleV,
    authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    ahsfHybrid, ahsBase, asUsedSendSessions, asPrincipals,
    pkbIkB, pkbSpkB, pkbSpkSig, pkbPqspkB, pkbPqspkSig, pkbOpkB?, peCorrupted, peSecIKA0,
    aNone, PeelSim.take_map_of_le _ _ hB.usedSendSessions_le, PeelSim.take_map_of_le _ _ hB.principals_le]
  simp only [cpaTryPauseSendSlotPrim, prepAuthCpaSendFixedPrim, PeelSim.ite_bind, pure_bind,
    bind_assoc]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]
    rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [cpS_any_sid_iff _ _ (SessionId.sendOPK u i)]
  swap
  · intro y
    rw [sidEq_eval _ _ _ y (SessionId.sendOPK u i) rfl rfl]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
  by_cases hsid :
      hst.toAuthHybridState.base.usedSendSessions.contains (SessionId.sendOPK u i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte]
  simp only [List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑u) hst.toAuthHybridState.base.principals = none
  · simp only [hp, Option.map_none, pure_bind, map_pure]; rfl
  obtain ⟨⟨uIdx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq, bind_assoc, pure_bind, PeelSim.ite_bind]
  refine PeelSim.peel_bind (m := OracleComp PrimBaseSpec) _
    (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ _ _ hst.toAuthHybridState.base (by simp) hB.principals_le]
    simp only [Expr.eval, Env.get_succ, Env.get_zero]
  refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine PeelSim.peel_bind_same _ ?_ (fun ok => ?_)
  · rw [koskBundleOkC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
      (by simp [hb, bundleV]) hB.advKeys_le hB.principals_le
        hB.spkBundles_le hB.opkEntries_le]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun ekASk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun kemCoins => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun ephASk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun spqrCoins => ?_)
  refine PeelSim.peel_bind_same _ (by rcases peer with _ | ⟨k, pE⟩ <;> rfl) (fun v1 => ?_)
  refine PeelSim.peel_bind_same _ (by rcases peer with _ | ⟨k, pE⟩ <;> rfl) (fun v2 => ?_)
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact PeelSim.peel_pure _ rfl
  simp only [bind_assoc, PeelSim.ite_bind, hb]
  refine PeelSim.peel_bind_same _ rfl (fun ekAPk => ?_)
  refine PeelSim.peel_bind_same _ ?_ (fun prov => ?_)
  · rw [checkBundleProvenanceExactC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
      (by simp [hb, bundleV]) hB.spkBundles_le
        hB.principals_le hB.opkEntries_le]
  rcases prov with ⟨sh, oh, ph⟩
  refine PeelSim.peel_bind_same _ ?_ (fun shi => ?_)
  · rw [spkHonIdealFromPeerC_eval S K _ _ _ _ hst.toAuthHybridState.base peer b (by simp) (by simp)
      (by simp [hb, bundleV]) hB.spkBundles_le]
  refine PeelSim.peel_bind_same _ rfl (fun dh1 => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dh2 => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dh3 => ?_)
  refine PeelSim.peel_bind_same _ ?_ (fun dh4 => ?_)
  · rw [hb]; rfl
  refine PeelSim.peel_bind_same _ rfl (fun ephAPk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dhR => ?_)
  rcases peer with _ | ⟨k, pE⟩
  · simp only [Option.map_none, Option.isSome_none, Bool.false_or, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_ (fun dro => ?_)
    · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
      simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero, Option.map_some,
        cpS_hkdf_eq]
    refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
    · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
    refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
    rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
    · simp only [pure_bind, map_pure]; rfl
    simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
    refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
    · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ rfl
      simp [firstMsgADE_eval, peIkAPk, Expr.eval, principalEntryToVal]
    refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
    · cps_hs
    · simp [cpaPayloadToVal, Expr.eval, peIkAPk, principalEntryToVal, preKeyBundleToVal, bundleV,
        sessionIdToVal, sidV, hb]
  · rcases hc : pE.corrupted with _ | _
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_false,
        Bool.true_or, Option.isSome_some, Bool.true_and, ↓reduceIte]
      refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
      simp only [pure_bind, bind_assoc]
      refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
      rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
      · simp only [pure_bind, map_pure]; rfl
      simp only [pure_bind, ↓reduceIte]
      cases allowPause <;>
        simp only [↓reduceIte, Bool.false_eq_true, Bool.true_and, Bool.false_and, id,
          Comp.eval, Expr.eval, natEq_eval,
          Env.get_succ, Env.get_zero, samplePrim_msgKeys80_eval,
          queryPrim_eval, queryPrim_aeadEnc_eval]
      · refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
        refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
        · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
          · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
          · cps_slot_pt
        refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
        · cps_hs
        · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV]
      · refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ ?_) (fun _ => ?_)
        · simp only [hi, hns]
        · simp [cpaSlotSendResToVal, cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV, hs, hns, Env.get_succ]
        refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
        refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
        · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
          · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
          · cps_slot_pt
        refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
        · cps_hs
        · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV]
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_true,
        Bool.false_or, Option.isSome_some, Bool.true_and]
      cases shi <;> cases ph <;> simp only [Bool.false_eq_true, Bool.and_false, Bool.and_true,
        ↓reduceIte]
      all_goals first
        | (refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_
              (fun dro => ?_)
           · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
             simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero,
               cpS_hkdf_eq]
           refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
           · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
           refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [pure_bind, map_pure]; rfl
           simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
           refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
           refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
           · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
             · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
             · cps_slot_pt
           refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
           · cps_hs
           · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
               principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc,
               sessionIdToVal, sidV])
        | (refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
           simp only [pure_bind, bind_assoc]
           refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [pure_bind, map_pure]; rfl
           simp only [pure_bind, ↓reduceIte]
           refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
           refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
           · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
             · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
             · cps_slot_pt
           refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
           · cps_hs
           · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
               principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
               sessionIdToVal, sidV])

set_option maxHeartbeats 4000000 in
theorem cpaSendSlotB_eval_noopk (allowPause : Bool) (idxV : Var Γ₁ .nat) (nsV : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (idx ns : Nat) (hst : AuthHybridStateFixed S) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hi : Env.get env (h₁.wk idxV) = idx)
    (hns : Env.get env (h₂.wk nsV) = ns)
    (hs : Env.get env (h₃.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₄.wk x) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AuthListsBounded K hst) :
    (cpaSendSlotB S K false allowPause idxV nsV fhst x).eval env =
      cpaSlotSendResToVal <$> cpaSendSlotShNoOpk S allowPause idx u i b m0 m1 (ns, hst) := by
  simp only [cpaSendSlotShNoOpk]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  swap
  · simp only [cpaSendSlotB, sendGuardE, Bool.false_eq_true, ↓reduceIte, v, letV, eval_letC,
      Comp.eval, Expr.eval, isSomeE_eval, pkbOpkB?, hx, preKeyBundleToVal, bundleV, hb,
      Option.isSome_some, map_pure, aNone, hs, hns, Ext.step_wk, Env.get_succ]
    rfl
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [cpaSendSlotB, sendGuardE, ↓reduceIte, v, letV, bindV, caseOptV, eCaseOpt, eFind,
    eAny, eval_letC, bytesLen_eval, bytesBeq_eval, boolOr_eval, isSomeE_eval,
    encEC_eval, encKEM_eval, natEq_eval, natLt_expr_eval, getDBytes_eval, optSnd_eval,
    samplePrim_bytes32_eval, samplePrim_drKey96_eval, samplePrim_msgKeys80_eval,
    queryPrim_eval, queryPrim_sigVerify_eval, queryPrim_kemEncaps_eval,
    queryPrim_x25519Base_eval, queryPrim_x25519_eval, queryPrim_chainKdfSeed_eval,
    queryPrim_chainKdfNext_eval, queryPrim_spqrInitSend_eval, queryPrim_deriveMsgKeys_eval,
    queryPrim_aeadEnc_eval, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hx, hs, hi, hns, hb, preKeyBundleToVal, bundleV,
    authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    ahsfHybrid, ahsBase, asUsedSendSessions, asPrincipals,
    pkbIkB, pkbSpkB, pkbSpkSig, pkbPqspkB, pkbPqspkSig, pkbOpkB?, peCorrupted, peSecIKA0,
    aNone, PeelSim.take_map_of_le _ _ hB.usedSendSessions_le, PeelSim.take_map_of_le _ _ hB.principals_le,
    Bool.false_eq_true]
  simp only [cpaTryPauseSendSlotPrim, prepAuthCpaSendFixedPrim, PeelSim.ite_bind, pure_bind,
    bind_assoc]
  by_cases hlen : m0.length = m1.length
  swap
  · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
      ↓reduceIte, map_pure]
    rfl
  simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [cpS_any_sid_iff _ _ (SessionId.sendNoOPK u i)]
  swap
  · intro y
    rw [sidEq_eval _ _ _ y (SessionId.sendNoOPK u i) rfl rfl]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
  by_cases hsid :
      hst.toAuthHybridState.base.usedSendSessions.contains (SessionId.sendNoOPK u i) = true
  · simp only [hsid, ↓reduceIte, map_pure]; rfl
  simp only [hsid, Bool.false_eq_true, ↓reduceIte]
  simp only [List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
  by_cases hp : List.find? (fun x => x.1 == ↑u) hst.toAuthHybridState.base.principals = none
  · simp only [hp, Option.map_none, pure_bind, map_pure]; rfl
  obtain ⟨⟨uIdx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
  simp only [hp', Option.map_some, Prod.map, id_eq, bind_assoc, pure_bind, PeelSim.ite_bind]
  refine PeelSim.peel_bind (m := OracleComp PrimBaseSpec) _
    (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
  · rw [findHonestC_eval S _ _ _ hst.toAuthHybridState.base (by simp) hB.principals_le]
    simp only [Expr.eval, Env.get_succ, Env.get_zero]
  refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
  refine PeelSim.peel_bind_same _ ?_ (fun ok => ?_)
  · rw [koskBundleOkC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
      (by simp [hb, bundleV]) hB.advKeys_le hB.principals_le
        hB.spkBundles_le hB.opkEntries_le]
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun ekASk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun kemCoins => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun ephASk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun spqrCoins => ?_)
  refine PeelSim.peel_bind_same _ (by rcases peer with _ | ⟨k, pE⟩ <;> rfl) (fun v1 => ?_)
  refine PeelSim.peel_bind_same _ (by rcases peer with _ | ⟨k, pE⟩ <;> rfl) (fun v2 => ?_)
  refine PeelSim.peel_ite _ Iff.rfl (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun kr => ?_)
  rcases kr with _ | ⟨ss, kemCt⟩
  · exact PeelSim.peel_pure _ rfl
  simp only [bind_assoc, PeelSim.ite_bind, hb]
  refine PeelSim.peel_bind_same _ rfl (fun ekAPk => ?_)
  refine PeelSim.peel_bind_same _ ?_ (fun prov => ?_)
  · rw [checkBundleProvenanceExactC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
      (by simp [hb, bundleV]) hB.spkBundles_le
        hB.principals_le hB.opkEntries_le]
  rcases prov with ⟨sh, oh, ph⟩
  refine PeelSim.peel_bind_same _ ?_ (fun shi => ?_)
  · rw [spkHonIdealFromPeerC_eval S K _ _ _ _ hst.toAuthHybridState.base peer b (by simp) (by simp)
      (by simp [hb, bundleV]) hB.spkBundles_le]
  refine PeelSim.peel_bind_same _ rfl (fun dh1 => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dh2 => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dh3 => ?_)
  refine PeelSim.peel_bind_same _ ?_ (fun dh4 => ?_)
  · rw [hb]
  refine PeelSim.peel_bind_same _ rfl (fun ephAPk => ?_)
  refine PeelSim.peel_bind_same _ rfl (fun dhR => ?_)
  rcases peer with _ | ⟨k, pE⟩
  · simp only [Option.map_none, Option.isSome_none, Bool.false_or, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_ (fun dro => ?_)
    · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
      simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero,
        cpS_hkdf_eq]
    refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
    · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
    refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
    rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
    · simp only [pure_bind, map_pure]; rfl
    simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
    refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
    · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ rfl
      simp [firstMsgADE_eval, peIkAPk, Expr.eval, principalEntryToVal]
    refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
    · cps_hs
    · simp [cpaPayloadToVal, Expr.eval, peIkAPk, principalEntryToVal, preKeyBundleToVal, bundleV,
        sessionIdToVal, sidV, hb]
  · rcases hc : pE.corrupted with _ | _
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_false,
        Bool.true_or, Option.isSome_some, Bool.true_and, ↓reduceIte]
      refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
      simp only [pure_bind, bind_assoc]
      refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
      rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
      · simp only [pure_bind, map_pure]; rfl
      simp only [pure_bind, ↓reduceIte]
      cases allowPause <;>
        simp only [↓reduceIte, Bool.false_eq_true, Bool.true_and, Bool.false_and, id,
          Comp.eval, Expr.eval, natEq_eval,
          Env.get_succ, Env.get_zero, samplePrim_msgKeys80_eval,
          queryPrim_eval, queryPrim_aeadEnc_eval]
      · refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
        refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
        · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
          · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
          · cps_slot_pt
        refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
        · cps_hs
        · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV]
      · refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ ?_) (fun _ => ?_)
        · simp only [hi, hns]
        · simp [cpaSlotSendResToVal, cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV, hs, hns, Env.get_succ]
        refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
        refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
        · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
          · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
          · cps_slot_pt
        refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
        · cps_hs
        · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
            principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
            sessionIdToVal, sidV]
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_true,
        Bool.false_or, Option.isSome_some, Bool.true_and]
      cases shi <;> cases ph <;> simp only [Bool.false_eq_true, Bool.and_false, Bool.and_true,
        ↓reduceIte]
      all_goals first
        | (refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_
              (fun dro => ?_)
           · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
             simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero,
               Option.map_none, cpS_hkdf_eq]
           refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
           · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
           refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [pure_bind, map_pure]; rfl
           simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
           refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
           refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
           · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
             · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
             · cps_slot_pt
           refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
           · cps_hs
           · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
               principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc,
               sessionIdToVal, sidV])
        | (refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
           simp only [pure_bind, bind_assoc]
           refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [pure_bind, map_pure]; rfl
           simp only [pure_bind, ↓reduceIte]
           refine PeelSim.peel_bind _ msgKeysToVal rfl (fun mk => ?_)
           refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
           · refine primQ_aeadEnc_args_eq (by simp only [valToMsgKeys_msgKeysToVal]) ?_ ?_
             · simp [firstMsgADE_eval, peIkAPk, Expr.eval]
             · cps_slot_pt
           refine PeelSim.peel_pure_bind _ (finishCpaC_eval S _ _ _ _ _ _ hst _ ?_ ?_) (by cps_slot_ret)
           · cps_hs
           · simp [cpaPayloadToVal, Expr.eval, firstMsgADE_eval, peIkAPk,
               principalEntryToVal, preKeyBundleToVal, bundleV, hb, hc, asRoCache, asRootRoCache,
               sessionIdToVal, sidV])

end SendSlot

end SignalPqxdh.Security.ReductionDsl.AuthAead
