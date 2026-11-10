/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCr
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import VCVio.EvalDist.Monad.Basic

/-!
# Component Evaluation for `shcrReductionAuthProg`

Value encodings for the `Auth` `KemShCr` reduction state and pause payload, together with
evaluation lemmas for shared components of the `KemShCr` handler branches.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp RoKem

def initRecToVal {S : Setup} (r : RoKem.InitKemRecord S) : initRecTy.denote :=
  (r.sendIdx, (sessionIdToVal r.sid, (r.pqspkPk, (r.kemCt, r.kemSs))))

def recvRecToVal (r : RoKem.RecvKemRecord) : recvRecTy.denote :=
  (r.k, (r.j, (r.pqspkPk, (r.pqspkSk, (r.kemCt, r.kemSs)))))

/-- Encoding of `AuthShCrState` extended with pause index `sIdx` and chosen public key `chosen`. -/
def shcrStToVal {S : Setup} (sIdx : Nat) (chosen : Bytes) (h : AuthShCrState S) :
    shcrStTy.denote :=
  (authStateToVal h.base, (h.targetBIdx?.map (fun bIdx => (bIdx / S.N_recv, bIdx % S.N_recv)),
    (h.targetPk, (h.targetSk, (h.sendCount,
    (h.initKemRecs.map initRecToVal, (h.recvKemRecs.map recvRecToVal, (sIdx, chosen))))))))

def encSCS {S : Setup} (sIdx : Nat) (chosen : Bytes) (p : AuthResponse × AuthShCrState S) :
    SCS.denote :=
  (authRespToVal p.1, shcrStToVal sIdx chosen p.2)

abbrev UInfo := PrincipalEntry × Option (Nat × PrincipalEntry) × Bytes

def uInfoToVal (u : UInfo) : uInfoTy.denote :=
  (principalEntryToVal u.1, (u.2.1.map (Prod.map id principalEntryToVal), u.2.2))

abbrev PauseMid (S : Setup) := SessionId S × PreKeyBundleInput × Bytes × Bytes × UInfo

def pauseToVal {S : Setup} (p : PauseMid S) : pauseTy.denote :=
  (sessionIdToVal p.1, (preKeyBundleToVal p.2.1, ((p.2.2.1, p.2.2.2.1), uInfoToVal p.2.2.2.2)))

def encFinA {S : Setup} (p : AuthResponse × Option (AuthState S)) : FinTy.denote :=
  (authRespToVal p.1, p.2.map authStateToVal)

theorem sidEq_eval {S : Setup} {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ sessionIdTy) (env : Env Γ)
    (x y : SessionId S) (ha : a.eval env = sessionIdToVal x) (hb : b.eval env = sessionIdToVal y) :
    (sidEq a b).eval env = (y == x) := by
  simp only [sidEq, eLet2, eLet, eCaseSum, nat2Eq, nat3Eq, eval_natEq, v, Expr.eval,
    Env.get_vs, Env.get_vz, Ext.step_wk, Ext.refl_wk, ha, hb]
  cases x <;> cases y <;> simp only [sessionIdToVal, sidV]
  all_goals
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq, SessionId.sendOPK.injEq, SessionId.sendNoOPK.injEq,
      SessionId.recvOPK.injEq, SessionId.recvNoOPK.injEq, Fin.ext_iff]
    tauto

section Components
variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  (env : Env Δ)

theorem onBase_eval (sV : Var Γ₁ shcrStTy) (h : AuthShCrState S) (sIdx : Nat) (chosen : Bytes)
    (hs : env.get (h₁.wk sV) = shcrStToVal sIdx chosen h)
    (br : (g : Var (authStateTy :: Δ) authStateTy) → Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS)
    (m : StateT (AuthState S) (OracleComp PrimBaseSpec) AuthResponse)
    (hbr : (br .vz).eval (.cons (authStateToVal h.base) env) =
      Prod.map authRespToVal authStateToVal <$> m.run h.base) :
    (onBase sV br).eval env = encSCS sIdx chosen <$> (liftShCrBasePrim (S := S) m).run h := by
  unfold onBase
  simp only [bindV, letV, Comp.eval_letC, Comp.eval, Expr.eval, v, Ext.step_wk, Env.get_vs, hs,
    scBase, scUpd, scMk, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, shcrStToVal]
  rw [hbr]
  simp only [liftShCrBasePrim, StateT.run, map_eq_bind_pure_comp, bind_assoc, Function.comp_def,
    pure_bind]
  rfl

theorem checkSigsC_eval (st : Var Γ₁ authStateTy) (s : AuthState S)
    (hst : env.get (h₁.wk st) = authStateToVal s) (bu : Var Γ₂ preKeyBundleTy)
    (b : PreKeyBundleInput) (hb : env.get (h₂.wk bu) = preKeyBundleToVal b)
    (hPrin : s.principals.length ≤ K) :
    (checkSigsC S K st bu).eval env = checkBundleSigsPrim S s.principals b := by
  unfold checkSigsC checkBundleSigsPrim
  simp only [bindV, eval_queryPrim, Comp.eval, v]
  rw [resolveSigPkC_eval S env s st hst (hPrin := hPrin)]
  simp only [Expr.eval, buSpkB, buSpkSig, buPqspkB, buPqspkSig, encEC_eval, encKEM_eval,
    PTag.dec_sigVerify, SignalPqxdh.LegacyCosted.PTag.enc, id_map, Ext.step_wk, Env.get_vs]
  erw [hb]
  rfl

theorem preCheckC_eval (opk : Bool) (st : Var Γ₁ authStateTy) (s : AuthState S)
    (hst : env.get (h₁.wk st) = authStateToVal s) (hK : AuthBaseListsBounded K s)
    (x : Var Γ₂ sendQTy) (sid : SessionId S) (u : Fin S.N_id) (iv : Nat) (b : PreKeyBundleInput)
    (m0 m1 : Bytes)
    (hx : env.get (h₂.wk x) = (u.val, (iv, (preKeyBundleToVal b, (m0, m1)))))
    (hsid : sessionIdToVal sid =
      if opk then Sum.inl (u.val, iv) else Sum.inr (Sum.inl (u.val, iv))) :
    (preCheckC S K opk st x).eval env =
      Option.map (fun ui => pauseToVal (sid, b, m0, m1, ui)) <$>
        preCheckAuthSimPrim S sid u b m0 m1 s := by
  have hsidE : ∀ (Γ' : List (Ty pqSig)) (e : Expr pqxdhOps Γ' sendQTy) (env' : Env Γ'),
      e.eval env' = (u.val, (iv, (preKeyBundleToVal b, (m0, m1)))) →
      (if opk then Expr.inl (.pair (.fst e) (.fst (.snd e)))
        else (Expr.inr (.inl (.pair (.fst e) (.fst (.snd e)))) :
          Expr pqxdhOps Γ' sessionIdTy)).eval env' =
        sessionIdToVal sid := by
    intro Γ' e env' he
    rw [hsid]; cases opk <;> simp [Expr.eval, he]
  unfold preCheckC
  simp only [letV, bindV, caseOptV, v, Comp.eval_letC, Comp.eval, Expr.eval, Ext.step_wk,
    Ext.refl_wk, Env.get_vs, Env.get_vz, hx, hst, authStateToVal, stUsedS, stPrin, eAny, eFind,
    eval_natEq, Expr.eval_bytesLen, Expr.eval_bytesBeq, preKeyBundleToVal, bundleV]
  rw [hsidE]
  rotate_left
  · simp only [Expr.eval, Env.get_vs, hx]
  rw [take_map_of_le _ _ hK.usedSendSessions_le, any_sid_iff _ _ sid
    (fun y => sidEq_eval _ _ _ y sid rfl rfl)]
  rw [take_map_of_le _ _ hK.principals_le, List.find?_map]
  simp only [preCheckAuthSimPrim]
  have hpred : ((fun x : Nat × principalEntryTy.denote => x.1 == (u : Nat)) ∘
      Prod.map id principalEntryToVal) = (fun x => x.1 == u.val) := rfl
  rw [hpred]
  by_cases hlen : m0.length = m1.length
  swap
  · simp [hlen]
  by_cases hs : sid ∈ s.usedSendSessions
  · simp [hlen, hs]
  rcases hp : List.find? (fun x => x.1 == u.val) s.principals with _ | ⟨idx, uE⟩
  · simp [hlen, hs, hp]
  simp only [hlen, hs, hp, bne_self_eq_false, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
    ite_false, Option.map_some, Prod.map, id, List.contains_iff_mem]
  rw [findHonestC_eval S _ s st (by simp only [Ext.step_wk, Env.get_vs, hst]) (hPrin := hK.principals_le)]
  simp only [Expr.eval, Env.get_vs, Env.get_vz, map_bind, bind_map_left]
  refine bind_congr' rfl fun pp => ?_
  simp only [koskBundleOkC_eval' S K _ s st _ hK.advKeys_le _ hK.principals_le hK.spkBundles_le
    hK.opkEntries_le, Ext.step_wk, Ext.refl_wk, Env.get_vs,
    Env.get_vz, hst, valToPreKeyBundle]
  rcases pp with _ | ⟨k, pE⟩
  · by_cases hm : m0 = m1
    · subst hm
      simp [eCaseOpt, Expr.eval, map_bind, pauseToVal, preKeyBundleToVal, uInfoToVal]
      refine bind_congr' rfl fun a => ?_
      cases a <;> simp []
    · simp [eCaseOpt, Expr.eval, hm]
  · cases hc : pE.corrupted
    · simp [eCaseOpt, Expr.eval, peCorrupted, principalEntryToVal, hc,
        map_bind, pauseToVal, preKeyBundleToVal, uInfoToVal]
      refine bind_congr' rfl fun a => ?_
      cases a <;> simp [principalEntryToVal, hc]
    · by_cases hm : m0 = m1
      · subst hm
        simp [eCaseOpt, Expr.eval, peCorrupted, principalEntryToVal, hc,
          map_bind, pauseToVal, preKeyBundleToVal, uInfoToVal]
        refine bind_congr' rfl fun a => ?_
        cases a <;> simp [principalEntryToVal, hc]
      · simp [eCaseOpt, Expr.eval, peCorrupted, principalEntryToVal, hc, hm]

set_option maxHeartbeats 2000000 in
theorem finishC_eval [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (st : Var Γ₁ authStateTy) (s : AuthState S)
    (hst : env.get (h₁.wk st) = authStateToVal s) (hK : AuthBaseListsBounded K s)
    (d : Var Γ₂ pauseTy) (sid : SessionId S) (b : PreKeyBundleInput) (m0 m1 : Bytes) (ui : UInfo)
    (hd : env.get (h₂.wk d) = pauseToVal (sid, b, m0, m1, ui))
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32)))) (ekSk ephSk spqrCoins : Bytes)
    (hks : env.get (h₃.wk ks) = (ekSk, (ephSk, spqrCoins)))
    (sc : Var Γ₄ (.prod (B 32) (B 1568))) (ss kemCt : Bytes)
    (hsc : env.get (h₄.wk sc) = (ss, kemCt)) :
    (finishC K st d ks sc).eval env =
      encFinA <$> finishAuthSimBasePrim S sid b m0 m1 ui ekSk ephSk spqrCoins ss kemCt s := by
  rcases ui with ⟨uE, pp, pt⟩
  unfold finishC
  send_unfold
  simp only [hd, hks, hsc]
  simp only [hkdfOrRoC_eval S K _ s st (hK := hK.roCache_le),
    rootRoC_eval S K _ s st (hK := hK.rootRoCache_le),
    Ext.step_wk, Env.get_vs, hst]
  simp only [buildSecretsE_eval, Expr.eval, Env.get_vs, Env.get_vz, hsc,
    pauseToVal, uInfoToVal, preKeyBundleToVal, bundleV, authStateToVal]
  simp only [finishAuthSimBasePrim, map_bind]
  rw [hd, hks]
  simp only [pauseToVal, uInfoToVal, preKeyBundleToVal, bundleV,
    take_map_of_le _ _ hK.spkBundles_le]
  simp only [bind_map_left]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩ <;>
  · simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
    peel; peel; peel; peel; peel
    refine bind_congr' rfl (fun _ => ?_)
    peel; peel; peel; peel; peel; peel
    rename_i spq
    rcases spq with _ | ⟨pqst, salt, pqmsg⟩
    · rfl
    simp only [map_bind, map_pure]
    peel
    refine bind_congr' ?_ (fun ct => ?_)
    · exact primQ_aeadEnc_congr (by simp)
        (by simp [firstMsgAD, encodeEC, pbBytesField, principalEntryToVal])
        rfl
    rcases pp with _ | ⟨k, pE⟩ <;>
      simp [encFinA, authRespToVal, authStateToVal, authSessionEntryToVal, principalEntryToVal,
        List.any_map, Function.comp_def, spkBundleEntryToVal, bne]

theorem shcrFinC_eval [h₃ : Ext Γ₃ Δ] (sV : Var Γ₁ shcrStTy) (h : AuthShCrState S) (sIdx : Nat)
    (chosen : Bytes) (hs : env.get (h₁.wk sV) = shcrStToVal sIdx chosen h)
    (sidE : Expr pqxdhOps Δ sessionIdTy) (sid : SessionId S) (hsid : sidE.eval env = sessionIdToVal sid)
    (pkE : Expr pqxdhOps Δ (B 1568)) (pk : Bytes) (hpk : pkE.eval env = pk)
    (sc : Var Γ₂ (.prod (B 32) (B 1568))) (ss kemCt : Bytes)
    (hsc : env.get (h₂.wk sc) = (ss, kemCt))
    (out : Var Γ₃ FinTy) (o : AuthResponse × Option (AuthState S))
    (hout : env.get (h₃.wk out) = encFinA o) :
    (shcrFinC sV sidE pkE sc out).eval env =
      pure (encSCS sIdx chosen (applyShCrFinish sid pk ss kemCt h o)) := by
  rcases o with ⟨r, _ | b'⟩ <;>
  · unfold shcrFinC
    simp only [letV, caseOptV, v, Comp.eval_letC, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_vs, Env.get_vz, hs, hsid, hpk, hsc, hout, scUpd, scBase, scTB, scTPk,
      scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, shcrStToVal, encFinA, Option.map_none,
      Option.map_some]
    rfl

end Components

end SignalPqxdh.Security.ReductionDsl.AuthHs
