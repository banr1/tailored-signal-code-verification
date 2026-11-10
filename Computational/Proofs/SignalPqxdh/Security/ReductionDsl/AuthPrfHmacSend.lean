/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacEnc
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacMu
import Computational.Proofs.GameHop.ReductionDsl.PeelSim
import VCVio.EvalDist.Monad.Basic

/-!
# Send Branch of the `PrfHmac` Evaluation Equivalence

Proves that `finishIntC` and `hmSendC` evaluate to `finishAuthIntSendPure` and the send cases of
`hmPre`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthAead
open SignalPqxdh.Security.ReductionDsl.AuthPrf hiding queryPrim_eval
open Computational.Proofs.GameHop.ReductionDsl
open OracleSpec OracleComp

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

theorem initSlotE_eval {Γ : List PT} (e : Expr pqxdhOps Γ sessionIdTy) (env : Env Γ) (sid : SessionId S)
    (he : e.eval env = sessionIdToVal sid) :
    (initSlotE S e).eval env = initSessionSlotIdx sid := by
  simp only [initSlotE, eCaseSum, v, Expr.eval, Ext.refl_wk, Env.get_zero, he]
  cases sid with
  | sendOPK u i =>
    have hN : S.N_id ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt u.isLt)
    simp [sessionIdToVal, sidV, initSessionSlotIdx, hN, Nat.mul_comm]
  | sendNoOPK u i =>
    have hN : S.N_id ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt u.isLt)
    simp [sessionIdToVal, sidV, initSessionSlotIdx, hN, Nat.mul_comm]
  | recvOPK _ _ _ => rfl
  | recvNoOPK _ _ _ => rfl

theorem initKeyIdE_eval {Γ : List PT} (e : Expr pqxdhOps Γ sessionIdTy) (env : Env Γ) (sid : SessionId S)
    (he : e.eval env = sessionIdToVal sid) :
    (initKeyIdE S e).eval env = natToMuKeyIdVal S (initSessionSlotIdx sid) := by
  simp only [initKeyIdE, eCaseSum, v, Expr.eval, Ext.refl_wk, Env.get_zero, he]
  cases sid with
  | sendOPK u i =>
    have hu : u.val < S.N_id := u.isLt
    have hi : i.val < S.N_send_opk := i.isLt
    have hlt : u.val * S.N_send_opk + i.val < S.N_send_opk_tot := by
      unfold Setup.N_send_opk_tot
      have h1 : (u.val + 1) * S.N_send_opk ≤ S.N_id * S.N_send_opk :=
        Nat.mul_le_mul_right _ hu
      nlinarith
    have hdiv : (u.val * S.N_send_opk + i.val) / S.N_send_opk = u.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.add_zero]
    have hmod : (u.val * S.N_send_opk + i.val) % S.N_send_opk = i.val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    simp [sessionIdToVal, sidV, initSessionSlotIdx, natToMuKeyIdVal, hlt, hdiv, hmod]
  | sendNoOPK u i =>
    have hu : u.val < S.N_id := u.isLt
    have hi : i.val < S.N_send_no_opk := i.isLt
    have hlt0 : ¬ (S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val) < S.N_send_opk_tot) := by
      omega
    have hlt1 : S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val) < S.N_send_tot := by
      unfold Setup.N_send_tot Setup.N_send_no_opk_tot
      have h1 : (u.val + 1) * S.N_send_no_opk ≤ S.N_id * S.N_send_no_opk :=
        Nat.mul_le_mul_right _ hu
      nlinarith
    have hdiv : (u.val * S.N_send_no_opk + i.val) / S.N_send_no_opk = u.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.add_zero]
    have hmod : (u.val * S.N_send_no_opk + i.val) % S.N_send_no_opk = i.val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    simp [sessionIdToVal, sidV, initSessionSlotIdx, natToMuKeyIdVal, hlt0, hlt1, hdiv, hmod]
  | recvOPK _ _ _ =>
    have hLe : S.N_send_opk_tot ≤ S.N_send_tot := Nat.le_add_right _ _
    have h1 : ¬ (S.N_send_tot < S.N_send_opk_tot) := by omega
    simp [sessionIdToVal, sidV, initSessionSlotIdx, natToMuKeyIdVal, h1]
  | recvNoOPK _ _ _ =>
    have hLe : S.N_send_opk_tot ≤ S.N_send_tot := Nat.le_add_right _ _
    have h1 : ¬ (S.N_send_tot < S.N_send_opk_tot) := by omega
    simp [sessionIdToVal, sidV, initSessionSlotIdx, natToMuKeyIdVal, h1]

set_option maxHeartbeats 4000000 in
theorem intSendPrepC_eval (opk : Bool) (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (hst : AuthHybridStateFixed S)
    (sid : SessionId S) (u : Fin S.N_id) (iv : Nat) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal hst)
    (hx : Env.get env (h₂.wk x) = (u.val, (iv, (preKeyBundleToVal b, (m0, m1)))))
    (hsid : sessionIdToVal sid = if opk then .inl (u.val, iv) else .inr (.inl (u.val, iv)))
    (hB : AuthListsBounded K hst) :
    (intSendPrepC S K opk fhst x).eval env =
      Option.map intPrepToVal <$> prepAuthIntSendPrim S sid u b m0 m1 hst := by
  cases opk <;> simp only [Bool.false_eq_true, ↓reduceIte] at hsid <;>
  simp only [intSendPrepC, Bool.false_eq_true, ↓reduceIte, v, letV, bindV, caseOptV, eCaseOpt,
    eFind, eAny, eval_letC, bytesLen_eval, bytesBeq_eval, boolOr_eval, isSomeE_eval,
    encEC_eval, encKEM_eval, natEq_eval, getDBytes_eval, optSnd_eval,
    samplePrim_bytes32_eval, samplePrim_drKey96_eval,
    queryPrim_eval, queryPrim_sigVerify_eval, queryPrim_kemEncaps_eval,
    queryPrim_x25519Base_eval, queryPrim_x25519_eval, queryPrim_chainKdfSeed_eval,
    queryPrim_chainKdfNext_eval, queryPrim_spqrInitSend_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, hx, hs, preKeyBundleToVal, bundleV,
    authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authHybridStateToVal, authStateToVal,
    ahsfHybrid, ahsBase, asUsedSendSessions, asPrincipals,
    pkbIkB, pkbSpkB, pkbSpkSig, pkbPqspkB, pkbPqspkSig, pkbOpkB?, peCorrupted, peSecIKA0,
    PeelSim.take_map_of_le _ _ hB.usedSendSessions_le, PeelSim.take_map_of_le _ _ hB.principals_le] <;>
  simp only [prepAuthIntSendPrim, PeelSim.ite_bind, pure_bind, bind_assoc] <;>
  · by_cases hlen : m0.length = m1.length
    swap
    · simp only [hlen, beq_false_of_ne hlen, bne_iff_ne, ne_eq, not_false_eq_true, Bool.not_false,
        ↓reduceIte, map_pure]
      rfl
    simp only [hlen, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    rw [cpS_any_sid_iff _ _ sid]
    swap
    · intro y
      rw [sidEq_eval _ _ _ y sid rfl (by rw [hsid]; rfl)]
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
    by_cases hsid' : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
    · simp only [hsid', ↓reduceIte, map_pure]; rfl
    simp only [hsid', Bool.false_eq_true, ↓reduceIte]
    simp only [List.find?_map, Function.comp_def, Prod.map_fst, id_eq]
    by_cases hp : List.find? (fun x => x.1 == ↑u) hst.toAuthHybridState.base.principals = none
    · simp only [hp, Option.map_none, map_pure]
    obtain ⟨⟨uIdx, uE⟩, hp'⟩ := Option.ne_none_iff_exists'.mp hp
    simp only [hp', Option.map_some, Prod.map, id_eq]
    refine PeelSim.peel_bind (m := OracleComp PrimBaseSpec) _
      (Option.map (Prod.map id principalEntryToVal)) ?_ (fun peer => ?_)
    · rw [findHonestC_eval S _ _ _ hst.toAuthHybridState.base (by simp) hB.principals_le]
      simp only [Expr.eval, Env.get_succ, Env.get_zero]
    refine PeelSim.peel_ite _ ?_ (fun _ => PeelSim.peel_pure _ rfl) (fun _ => ?_)
    · rcases peer with _ | ⟨k, pE⟩ <;> simp [principalEntryToVal, bne]
    refine PeelSim.peel_bind_same _ ?_ (fun ok => ?_)
    · rw [koskBundleOkC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
        (by simp [bundleV]) hB.advKeys_le hB.principals_le
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
    refine PeelSim.peel_bind_same _ rfl (fun ekAPk => ?_)
    refine PeelSim.peel_bind_same _ ?_ (fun prov => ?_)
    · rw [checkBundleProvenanceExactC_eval S K _ _ _ hst.toAuthHybridState.base b (by simp)
        (by simp [bundleV]) hB.spkBundles_le
        hB.principals_le hB.opkEntries_le]
    rcases prov with ⟨sh, oh, ph⟩
    refine PeelSim.peel_bind_same _ ?_ (fun shi => ?_)
    · rw [spkHonIdealFromPeerC_eval S K _ _ _ _ hst.toAuthHybridState.base peer b (by simp)
        (by simp) (by simp [bundleV]) hB.spkBundles_le]; rfl
    refine PeelSim.peel_bind_same _ rfl (fun dh1 => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun dh2 => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun dh3 => ?_)
    refine PeelSim.peel_bind_same _ ?_ (fun dh4 => ?_)
    · rcases b.opkB? with _ | ⟨_, _⟩ <;> rfl
    refine PeelSim.peel_bind_same _ rfl (fun ephAPk => ?_)
    refine PeelSim.peel_bind_same _ rfl (fun dhR => ?_)
    rcases peer with _ | ⟨k, pE⟩
    · simp only [Option.map_none, Option.isSome_none, Bool.false_or, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_ (fun dro => ?_)
      · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
        simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero, cpS_hkdf_eq]
        rcases b.opkB? with _ | _ <;> rfl
      refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
      · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp) hB.rootRoCache_le]; rfl
      refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
      rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
      · simp only [map_pure]; rfl
      simp only [map_pure, Option.map_some]
      simp [intPrepToVal, firstMsgADE_eval, peIkAPk, Expr.eval, principalEntryToVal]
    rcases hc : pE.corrupted with _ | _
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_false,
        Bool.true_or, Option.isSome_some, Bool.true_and, ↓reduceIte, bind_assoc, pure_bind]
      refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
      refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
      rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
      · simp only [map_pure]; rfl
      simp only [map_pure, Option.map_some]
      simp [intPrepToVal, firstMsgADE_eval, peIkAPk, Expr.eval, principalEntryToVal, hc,
             asSecb, asRoCache, asRootRoCache, peIkSignPk]
    · simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, hc, Bool.not_true,
        Bool.false_or, Option.isSome_some, Bool.true_and]
      cases shi <;> cases ph <;> simp only [Bool.false_eq_true, Bool.and_false, Bool.and_true,
        ↓reduceIte, bind_assoc, pure_bind]
      all_goals first
        | (refine PeelSim.peel_bind _ (Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal))) ?_
              (fun dro => ?_)
           · rw [hkdfRoC_eval S K _ _ _ hst.toAuthHybridState.base (by simp) hB.roCache_le]
             simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero, cpS_hkdf_eq]
             rcases b.opkB? with _ | _ <;> rfl
           refine PeelSim.peel_bind_same _ ?_ (fun rko => ?_)
           · rw [rootRoC_eval S K _ _ _ _ hst.toAuthHybridState.base (by simp)
               hB.rootRoCache_le]; rfl
           refine PeelSim.peel_bind_same _ rfl (fun mkSeed => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ck1_1 => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [map_pure]; rfl
           simp only [map_pure, Option.map_some]
           simp [intPrepToVal, firstMsgADE_eval, peIkAPk, Expr.eval, principalEntryToVal, hc,
             peIkSignPk])
        | (refine PeelSim.peel_bind _ drKeyToVal rfl (fun dk => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun r => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun c => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun ms => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun cn => ?_)
           refine PeelSim.peel_bind_same _ rfl (fun sp => ?_)
           rcases sp with _ | ⟨pqrStA, salt, pqMsg⟩
           · simp only [map_pure]; rfl
           simp only [map_pure, Option.map_some]
           simp [intPrepToVal, firstMsgADE_eval, peIkAPk, Expr.eval, principalEntryToVal, hc,
             asRoCache, asRootRoCache, peIkSignPk])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finishIntC_eval (a : Expr pqxdhOps Δ intFinArgsTy) (env : Env Δ) (hst : AuthHybridStateFixed S)
    (sid : SessionId S) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (p : AuthIntSendPrep S)
    (mk : MessageKeys) (ct : Bytes)
    (ha : a.eval env = (authHybridStateFixedToVal hst, (sessionIdToVal sid,
      (preKeyBundleToVal bundle, ((m0, m1), (intPrepToVal p, (msgKeysToVal mk, ct))))))) :
    (finishIntC a).eval env =
      pure (Prod.map authRespToVal authHybridStateFixedToVal
        (finishAuthIntSendPure sid bundle m0 m1 p mk ct hst)) := by
  simp only [finishIntC, letV, v, ahsfHybrid, ahsBase, hdMk, pmMk, peIkAPk, pkbSpkId, pkbOpkB?,
    pkbPqspkId, optFst,
    seMk, pkbIkB, pkbSpkB, pkbPqspkB, optSnd, eCaseOpt, ikrMk, isSomeE_eval, iasMk,
    ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsfUpd,
    ahsfMkSlots, ahsfSlots, ahsfRecvCount, ahsfMkSaltCache,
    stUpd, stMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, aSendFresh, aSendUnfresh, eval_letC, bytesBeq_eval, Comp.eval,
    ipUEntry, ipPeer, ipFim, ipFresh, ipIdeal, ipMsgPlain, ipT3, ipKeys6, ipDrKey, ipRks4,
    ipSalt, ipPqMsg, ipAd, ipProv, ipRoC, ipRootC,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, ha, intPrepToVal]
  unfold finishAuthIntSendPure
  cases p.peerPrincipal? <;>
    rcases hob : bundle.opkB? with _ | ⟨oid, opk⟩ <;>
    cases p.isIdealSend <;>
    simp [hob, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authHybridStateToVal, authStateToVal, authRespToVal,
      authRenc, sessionIdToVal, sidV, principalEntryToVal, preKeyBundleToVal, bundleV, drKeyToVal,
      drKeyV, msgKeysToVal, msgKeysV, authSessionEntryToVal, initKemRecordToVal,
      idealAuthSessionToVal, preKeyMsgV, hdrV, bne]

set_option maxHeartbeats 4000000 in
theorem hmSendTailC_eval_v2 {Γ₅ : List PT} (opk : Bool) (jt : Var Γ₁ .nat)
    (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    (p : Var Γ₅ intPrepTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] [h₅ : Ext Γ₅ Δ] (env : Env Δ)
    (jtv : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState) (sid : SessionId S)
    (u : Fin S.N_id) (iv : Nat) (b : PreKeyBundleInput) (m0 m1 : Bytes) (pv : AuthIntSendPrep S)
    (hj : Env.get env (h₁.wk jt) = jtv)
    (hs : Env.get env (h₂.wk fhst) = authHybridStateFixedToVal hst)
    (hm : Env.get env (h₃.wk mst) = muStToValS S ms)
    (hx : Env.get env (h₄.wk x) = (u.val, (iv, (preKeyBundleToVal b, (m0, m1)))))
    (hp : Env.get env (h₅.wk p) = intPrepToVal pv)
    (hsid : sessionIdToVal sid = if opk then .inl (u.val, iv) else .inr (.inl (u.val, iv)))
    (hM : MuBounded K ms) :
    (hmSendTailC S K opk jt fhst mst x p).eval env =
      hmPreToVal <$> hmSendTail S jtv sid b m0 m1 hst ms pv := by
  have hsidE : (sendSidE opk (v x)).eval env = sessionIdToVal sid := by
    rw [hsid]; cases opk <;> simp [sendSidE, v, Expr.eval, hx]
  simp only [hmSendTailC, letV_eval]
  rw [hsidE]
  simp only [Comp.eval, Expr.eval, v, Ext.step_wk, Env.get_succ, hp, hx, intPrepToVal,
    ipIdeal, ipFim, ipAd, ipMsgPlain, ipT3, ipRks4, ipSalt]
  unfold hmSendTail
  cases hI : pv.isIdealSend
  · simp only [Bool.false_eq_true, ↓reduceIte, bindV, queryPrim_eval, queryPrim_deriveMsgKeys_eval,
      queryPrim_aeadEnc_eval, Comp.eval, Expr.eval, Env.get_succ]
    refine PeelSim.peel_bind _ msgKeysToVal (by erw [hp]; rfl) (fun mk => ?_)
    refine PeelSim.peel_bind_same _ ?_ (fun ct => ?_)
    · exact primQ_aeadEnc_args_eq (by simp; rfl) rfl rfl
    refine PeelSim.peel_pure_bind _ (finishIntC_eval S _ _ hst sid b m0 m1 pv mk ct ?_) ?_
    · simp [Expr.eval, hs, hp]
    · simp only [Ext.refl_wk, Env.get_zero, hm]
      rfl
  · simp only [↓reduceIte, bindV, caseSumV, Comp.eval]
    refine PeelSim.peel_bind _ (encPreToValS S) ?_ (fun e => ?_)
    · rw [hmEncPreIdC_eval S K _ _ jtv (initSessionSlotIdx sid) pv.ad pv.msgPlain ms ?_ hM]
      simp only [Expr.eval]
      rw [initKeyIdE_eval S _ _ sid (by simp [Expr.eval])]
      simp [hj, hm]
    rcases e with ⟨ct?, mst'⟩ | c
    · simp only [encPreToValS, Expr.eval, Ext.refl_wk, Env.get_succ, Env.get_zero]
      refine PeelSim.peel_pure_bind _ (finishIntC_eval S _ _ hst sid b m0 m1 pv default (ct?.getD []) ?_) ?_
      · simp [Expr.eval, hs, hp, defaultMsgKeysE, msgKeysToVal, msgKeysV, getDBytes_eval]
      · rfl
    · simp [encPreToValS, Expr.eval, hs, hp, hmPreToVal, hmSendContToVal]

theorem hmSendC_eval_opk_v2 (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (jtv : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hj : Env.get env (h₁.wk jt) = jtv)
    (hs : Env.get env (h₂.wk fhst) = authHybridStateFixedToVal hst)
    (hm : Env.get env (h₃.wk mst) = muStToValS S ms)
    (hx : Env.get env (h₄.wk x) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AuthListsBounded K hst) (hM : MuBounded K ms) :
    (hmSendC S K true jt fhst mst x).eval env =
      hmPreToVal <$> hmPre S jtv (.sendOPK u i b m0 m1) hst ms := by
  simp only [hmPre]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp only [hmSendC, sendGuardE, ↓reduceIte, v, Comp.eval, Expr.eval, isSomeE_eval, pkbOpkB?, hx,
      preKeyBundleToVal, bundleV, hb, Option.isNone_none, map_pure]
    erw [hs, hm]; rfl
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  simp only [hmSendC, sendGuardE, ↓reduceIte, v, Comp.eval, Expr.eval, isSomeE_eval, pkbOpkB?, hx,
    preKeyBundleToVal, bundleV, hb, bindV, caseOptV, hmSendPre]
  refine PeelSim.peel_bind _ (Option.map intPrepToVal) ?_ (fun p? => ?_)
  · exact intSendPrepC_eval S K true fhst x env hst (.sendOPK u i) u i.val b m0 m1 hs hx rfl hB
  rcases p? with _ | pv
  · simp only [Ext.step_wk, Env.get_succ, map_pure]
    erw [hs, hm]; rfl
  · exact hmSendTailC_eval_v2 S K true jt fhst mst x Var.zero _ jtv hst ms (.sendOPK u i) u i.val b
      m0 m1 pv (by simp [hj]) (by simp [hs]) (by simp [hm]) (by simp [hx]) rfl rfl hM

theorem hmSendC_eval_noopk_v2 (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ] [h₄ : Ext Γ₄ Δ] (env : Env Δ)
    (jtv : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hj : Env.get env (h₁.wk jt) = jtv)
    (hs : Env.get env (h₂.wk fhst) = authHybridStateFixedToVal hst)
    (hm : Env.get env (h₃.wk mst) = muStToValS S ms)
    (hx : Env.get env (h₄.wk x) = (u.val, (i.val, (preKeyBundleToVal b, (m0, m1)))))
    (hB : AuthListsBounded K hst) (hM : MuBounded K ms) :
    (hmSendC S K false jt fhst mst x).eval env =
      hmPreToVal <$> hmPre S jtv (.sendNoOPK u i b m0 m1) hst ms := by
  simp only [hmPre]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  swap
  · simp only [hmSendC, sendGuardE, Bool.false_eq_true, ↓reduceIte, v, Comp.eval, Expr.eval,
      isSomeE_eval, pkbOpkB?, hx, preKeyBundleToVal, bundleV, hb, Option.isSome_some, map_pure]
    erw [hs, hm]; rfl
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [hmSendC, sendGuardE, Bool.false_eq_true, ↓reduceIte, v, Comp.eval, Expr.eval,
    isSomeE_eval, pkbOpkB?, hx, preKeyBundleToVal, bundleV, hb, bindV, caseOptV, hmSendPre]
  refine PeelSim.peel_bind _ (Option.map intPrepToVal) ?_ (fun p? => ?_)
  · exact intSendPrepC_eval S K false fhst x env hst (.sendNoOPK u i) u i.val b m0 m1 hs hx rfl hB
  rcases p? with _ | pv
  · simp only [Ext.step_wk, Env.get_succ, map_pure]
    erw [hs, hm]; rfl
  · exact hmSendTailC_eval_v2 S K false jt fhst mst x Var.zero _ jtv hst ms (.sendNoOPK u i) u i.val b
      m0 m1 pv (by simp [hj]) (by simp [hs]) (by simp [hm]) (by simp [hx]) rfl rfl hM

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
