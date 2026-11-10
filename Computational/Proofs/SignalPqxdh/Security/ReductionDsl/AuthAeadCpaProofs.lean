/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpa
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost

/-!
# Cost and Primitive-Query Bounds for `aeadCpaRedProg`

Proves linear component bounds and overall `totalCost` and `totalQueries` bounds for
`aeadCpaRedProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp

/-- Concrete polynomial step-cost budget granted to every black-box reduction in the DSL. -/
def stepCostBudget (S : Setup) (b : QueryBudget) : Nat :=
  2 ^ 16 * (b.q_total + 1) * (b.q_total + S.N_dh + S.N_sess_tot + 1) +
    2 ^ 11 * S.N_dh ^ 2 + 2 ^ 8 * S.N_dh * S.N_sess_tot

theorem defaultMsgKeys_cipherKey_length : (default : MessageKeys).cipherKey.length = 0 := rfl
theorem defaultMsgKeys_macKey_length : (default : MessageKeys).macKey.length = 0 := rfl
theorem defaultMsgKeys_iv_length : (default : MessageKeys).iv.length = 0 := rfl

section
attribute [local simp] Expr.cost Comp.cost

@[simp] theorem finishCpaC_cost {Γ₁ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (fresh isIdeal : Expr pqxdhOps Δ .bool)
    (p : Expr pqxdhOps Δ cpaPayloadTy) (aeadCt : Expr pqxdhOps Δ (B 32)) [Ext Γ₁ Δ] :
    (finishCpaC fhst fresh isIdeal p aeadCt).cost =
      fresh.cost + isIdeal.cost + p.cost + aeadCt.cost + 814 := by
  simp only [finishCpaC, letV, eCaseOpt, cost_letC, hdMk, pmMk, seMk, ikrMk, iasMk,
    ahsUpd, ahsMk, stUpd, stMk, ahsfUpd, ahsfMkSlots,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys,
    peIkAPk, pkbSpkId, pkbOpkB?, pkbPqspkId, pkbIkB, pkbSpkB, pkbPqspkB,
    optFst, optSnd, isSomeE, aSendFresh, aSendUnfresh, defaultMsgKeysE,
    cost_bytesBeq, cost_litB, defaultMsgKeys_cipherKey_length,
    defaultMsgKeys_macKey_length, defaultMsgKeys_iv_length,
    v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  omega

@[simp] theorem finishCpaC_queries {Γ₁ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (fresh isIdeal : Expr pqxdhOps Δ .bool)
    (p : Expr pqxdhOps Δ cpaPayloadTy) (aeadCt : Expr pqxdhOps Δ (B 32)) [Ext Γ₁ Δ] :
    (finishCpaC fhst fresh isIdeal p aeadCt).queries primW primWS = 0 := by
  simp [finishCpaC, letV, queries_letC, Comp.queries]

@[simp] theorem spkHonIdealFromPeerC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (st : Var Γ₁ authStateTy) (pp : Var Γ₂ (.opt (.prod .nat principalEntryTy)))
    (bu : Var Γ₃ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (spkHonIdealFromPeerC S K st pp bu : Comp pqxdhOps pqPrimIface Δ .bool).cost =
      16 + min K S.N_dh * 295 := by
  simp only [spkHonIdealFromPeerC, caseOptV, letV, anyMV, bindV, natEq,
    asSpkBundles, sbSpkPk, pkbSpkB, peCorrupted, cost_letC, cost_queryPrim,
    cost_bytesBeq, cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem spkHonIdealFromPeerC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (st : Var Γ₁ authStateTy) (pp : Var Γ₂ (.opt (.prod .nat principalEntryTy)))
    (bu : Var Γ₃ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (spkHonIdealFromPeerC S K st pp bu : Comp pqxdhOps pqPrimIface Δ .bool).queries primW primWS =
      min K S.N_dh * 2 := by
  simp only [spkHonIdealFromPeerC, caseOptV, letV, anyMV, bindV,
    queries_letC, queryPrim, primW, Comp.queries]
  omega

theorem cpa_init_cost (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).init.cost = 66 + bits (min K S.N_send_tot) := by
  simp only [aeadCpaRedProg, authCodec, cpaInitC, bindV,
    emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE, emptyAuthSlotStE,
    ahsfMk, ahsfMkSlots, assMk, ahsMk, stMk,
    cost_samplePrim, PSamp.cost, v, Comp.cost, Expr.cost, bits_0]
  omega

theorem cpa_init_queries (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).init.queries primW primWS = 0 := by
  simp [aeadCpaRedProg, authCodec, cpaInitC, bindV, samplePrim, primWS, Comp.queries]

theorem cpa_chDone_cost (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).chDone.cost = 230 := by
  simp only [aeadCpaRedProg, authCodec, cpaDefaultChC, cost_litB,
    Comp.cost, Expr.cost, PNat.val_ofNat, List.length_cons, List.length_nil]

theorem cpa_chDone_queries (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).chDone.queries primW primWS = 0 := by
  simp [aeadCpaRedProg, authCodec, cpaDefaultChC, Comp.queries]

theorem cpa_resume_cost (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).resume.cost = 874 := by
  simp only [aeadCpaRedProg, authCodec, cpaResumeC, finishCpaC_cost,
    letV, bindV, cost_letC, getDBytes, eCaseOpt, cost_litB,
    v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil, bits_1]
  omega

theorem cpa_resume_queries (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).resume.queries primW primWS = 0 := by
  simp [aeadCpaRedProg, authCodec, cpaResumeC, letV, bindV, queries_letC, Comp.queries]

theorem cpa_finish_cost (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).finish.cost =
      112 + min K S.N_dh * 413 + (min K S.N_dh) ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 := by
  simp only [aeadCpaRedProg, authCodec, cpaFinishC, finalizeAuthFixedDsl,
    allHonestEcPksAuthDslK, finalizeAuthFixedBodyDsl,
    hasDuplicateBytesDsl_cost, hasBadSigAuthDsl_cost, hasKemPkCollisionAuthDsl_cost,
    hasBadKemShCrRecordsDsl_cost, notAllChallengedCleanDsl_cost,
    letV, cost_letC, cost_samplePrim, cost_queryPrim, cost_boolOr, cost_boolBeq,
    ahsfHybrid, ahsBase, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asHasWonAuth,
    peIkAPk, sbSpkPk, oeOpkPk, aseEkASk,
    PSamp.cost, Ty.wd, Comp.cost, Expr.cost, PNat.val_ofNat]
  generalize min K S.N_dh = d
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  ring_nf

theorem cpa_finish_queries (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).finish.queries primW primWS = min K S.N_dh * 5 := by
  simp only [aeadCpaRedProg, authCodec, cpaFinishC, finalizeAuthFixedDsl,
    allHonestEcPksAuthDslK, finalizeAuthFixedBodyDsl,
    letV, queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
  omega

private theorem cpaSendSlotB_cost_le (S : Setup) (K : Nat) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (cpaSendSlotB S K opk allowPause idx ns fhst x :
      Comp pqxdhOps pqPrimIface Δ cpaSlotSendResTy).cost ≤
      11700 + K * 4500 + min K S.N_dh * 1540 := by
  cases opk <;> cases allowPause <;>
  · simp only [cpaSendSlotB,
      koskBundleOkC_cost, finishCpaC_cost, spkHonIdealFromPeerC_cost,
      checkBundleProvenanceExactC_cost,
      hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost, buildSecretsE_cost,
      sidEq_cost, findHonestC, sendGuardE, getDBytes, optSnd,
      bindV, letV, caseOptV, findMV, eFind, eAny, eCaseOpt,
      natEq, natLt, isSomeE,
      ahsfHybrid, ahsBase, asPrincipals, asUsedSendSessions, asRoCache, asRootRoCache,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig, aNone,
      cost_encEC, cost_encKEM, cost_letC, cost_samplePrim, cost_queryPrim,
      cost_bytesLen, cost_bytesBeq, cost_boolOr, cost_litB,
      PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, bits_1, bits_32, ite_true, ite_false, Bool.false_eq_true, id_eq]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem cpaRecvC_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (cpaRecvC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      11600 + K * 4500 + min K S.N_dh * 1540 + min K S.N_sess_tot * 7450 := by
  cases opk <;>
  · simp only [cpaRecvC,
      koskSenderOkC_cost, matchIdealAuthHandshakeC_cost,
      hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost, buildSecretsE_cost,
      sidEq_cost, optU32Eq_cost, sameSaltKeyE_cost, kyberCheckE_cost,
      findHonestC, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
      bindV, letV, caseOptV, caseSumV, findMV, eFind, eAny, eMap, eCaseOpt,
      natEq, nat2Eq, nat3Eq,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMk, ahsfMkSlots, ahsfUpd, emptyAuthSlotStE, assMk,
      ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
      asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd,
      peSecIKA0, peIkAPk, peCorrupted,
      sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd, rkrMk,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
      pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasSid, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys, iasEphAPk,
      aNone, aRecvHonest, aRecvUnfresh,
      cost_u32OfNat, cost_u32Beq, cost_letC, cost_samplePrim,
      cost_queryPrim, cost_bytesLen, cost_bytesBeq, cost_boolOr,
      PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, bits_0, bits_1, bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem cpaInlWrapSlot_cost_le {Γ₁ Γ₂ Δ : List PT}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (m : Comp pqxdhOps pqPrimIface Δ RSF) {M : Nat} (hm : m.cost ≤ M) :
    (bindV (wrapCpaSlot idx ns m) fun r => .ret (.inl (v r)) :
      Comp pqxdhOps pqPrimIface Δ cpaPreTy).cost ≤ M + 25 := by
  simp only [wrapCpaSlot, bindV, v, Comp.cost, Expr.cost]
  omega

private theorem cpaSendSlotWrap_cost_le (S : Setup) (K : Nat) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat) (fhst : Var Γ₃ authHybridStateFixedTy)
    (x : Var Δ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    ((bindV (cpaSendSlotB S K opk allowPause idx ns fhst x) fun r =>
      caseSumV (v r)
        (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
        (fun p => if allowPause then
            .ret (.inr (.pair (.fst (v p)) (.pair (.fst (.snd (v p)))
              (.pair (v idx) (.snd (.snd (v p)))))))
          else .ret (.inl (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst))))))) :
      Comp pqxdhOps pqPrimIface Δ cpaPreTy).cost ≤
      11740 + K * 4500 + min K S.N_dh * 1540 := by
  have h := cpaSendSlotB_cost_le S K opk allowPause idx ns fhst x (Δ := Δ)
  cases allowPause <;>
  · simp only [bindV, caseSumV, aNone, v, Comp.cost, Expr.cost, ite_true, ite_false, Bool.false_eq_true]
    omega

private theorem cpaStepC_cost_le_clamped (S : Setup) (K : Nat) (allowPause : Bool) :
    (cpaStepC S K allowPause).cost ≤
      11800 + K * 5000 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7500 := by
  unfold cpaStepC cpaNonSendSlotC
  refine le_trans (letV_cost_le _ _ (N := 11790 + K * 5000 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7500) ?_) (by simp [Expr.cost]; omega)
  refine le_trans (letV_cost_le _ _ (N := 11784 + K * 5000 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7500) ?_) (by simp [Expr.cost]; omega)
  refine le_trans (letV_cost_le _ _ (N := 11776 + K * 5000 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7500) ?_) (by simp [Expr.cost]; omega)
  refine le_trans
    (caseSumV_cost_le _ _ _ (cpaInlWrapSlot_cost_le _ _ _ (initPrinFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (cpaInlWrapSlot_cost_le _ _ _ (corruptFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (cpaInlWrapSlot_cost_le _ _ _ (genSpkFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (cpaInlWrapSlot_cost_le _ _ _ (genOpkFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (cpaSendSlotWrap_cost_le S K true allowPause _ _ _ _) <|
     caseSumV_cost_le _ _ _ (cpaSendSlotWrap_cost_le S K false allowPause _ _ _ _) <|
     caseSumV_cost_le _ _ _ (cpaInlWrapSlot_cost_le _ _ _ (cpaRecvC_cost_le S K true _ _)) <|
     caseSumV_cost_le _ _ _ (cpaInlWrapSlot_cost_le _ _ _ (cpaRecvC_cost_le S K false _ _)) <|
     caseSumV_cost_le _ _ _ (cpaInlWrapSlot_cost_le _ _ _ (roFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (cpaInlWrapSlot_cost_le _ _ _ (roRootFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (by simp only [bindV, aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
     cpaInlWrapSlot_cost_le _ _ _ (registerFixedB_cost_le _ _))
    (by omega)

private theorem cpaStepC_cost_le (S : Setup) (K : Nat) (allowPause : Bool) :
    (cpaStepC S K allowPause).cost ≤
      11800 + slotIdxCost S + K * 5000 + S.N_dh * 1550 + S.N_sess_tot * 7500 := by
  have h := cpaStepC_cost_le_clamped S K allowPause
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hd' := Nat.mul_le_mul_right 1550 hd
  have hs' := Nat.mul_le_mul_right 7500 hs
  omega

private theorem cpa_handlePre_cost_le_clamped (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).handlePre.cost ≤
      12000 + K * 5000 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7500 := by
  have h := cpaStepC_cost_le_clamped S K true
  simp only [aeadCpaRedProg, authCodec, cpaPreC]
  omega

private theorem cpa_handlePost_cost_le_clamped (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).handlePost.cost ≤
      12000 + K * 5000 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7500 := by
  have h := cpaStepC_cost_le_clamped S K false
  simp only [aeadCpaRedProg, authCodec, cpaPostC, bindV, caseSumV, aNone, v, Comp.cost, Expr.cost]
  omega

theorem cpa_handlePre_cost_le (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).handlePre.cost ≤
      12000 + slotIdxCost S + K * 5000 + S.N_dh * 1550 + S.N_sess_tot * 7500 := by
  have h := cpaStepC_cost_le S K true
  simp only [aeadCpaRedProg, authCodec, cpaPreC]
  omega

theorem cpa_handlePost_cost_le (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).handlePost.cost ≤
      12000 + slotIdxCost S + K * 5000 + S.N_dh * 1550 + S.N_sess_tot * 7500 := by
  have h := cpaStepC_cost_le S K false
  simp only [aeadCpaRedProg, authCodec, cpaPostC, bindV, caseSumV, aNone, v, Comp.cost, Expr.cost]
  omega

@[simp] private theorem cpaSendSlotB_queries (S : Setup) (K : Nat) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (cpaSendSlotB S K opk allowPause idx ns fhst x :
      Comp pqxdhOps pqPrimIface Δ cpaSlotSendResTy).queries primW primWS =
      18 + min K S.N_dh * 14 := by
  cases opk <;> cases allowPause <;>
  · simp only [cpaSendSlotB, koskBundleOkC_queries, finishCpaC_queries,
      spkHonIdealFromPeerC_queries, checkBundleProvenanceExactC_queries,
      hkdfRoC, rootRoC, findHonestC,
      bindV, letV, caseOptV, findMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true, id_eq]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

@[simp] private theorem cpaRecvC_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (cpaRecvC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS =
      16 + min K S.N_dh * 6 + min K S.N_sess_tot * 10 := by
  cases opk <;>
  · simp only [cpaRecvC, koskSenderOkC_queries, matchIdealAuthHandshakeC_queries,
      hkdfRoC, rootRoC, findHonestC,
      bindV, letV, caseOptV, caseSumV, findMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

@[simp] private theorem cpaStepC_queries (S : Setup) (K : Nat) (allowPause : Bool) :
    (cpaStepC S K allowPause).queries primW primWS =
      max (18 + min K S.N_dh * 14) (16 + min K S.N_dh * 6 + min K S.N_sess_tot * 10) := by
  cases allowPause <;>
  · simp only [cpaStepC, cpaNonSendSlotC, wrapCpaSlot,
      initPrinFixedB_queries, corruptFixedB_queries, genSpkFixedB_queries, genOpkFixedB_queries,
      cpaSendSlotB_queries, cpaRecvC_queries, roFixedB_queries, roRootFixedB_queries,
      registerFixedB_queries,
      letV, bindV, caseSumV, queries_letC, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    omega

theorem cpa_handlePre_queries (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).handlePre.queries primW primWS =
      max (18 + min K S.N_dh * 14) (16 + min K S.N_dh * 6 + min K S.N_sess_tot * 10) := by
  simp [aeadCpaRedProg, authCodec, cpaPreC, cpaStepC_queries]

theorem cpa_handlePre_queries_le (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).handlePre.queries primW primWS ≤
      18 + S.N_dh * 14 + S.N_sess_tot * 10 := by
  rw [cpa_handlePre_queries]
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hd1 := Nat.mul_le_mul_right 14 hd
  have hd2 := Nat.mul_le_mul_right 6 hd
  have hs1 := Nat.mul_le_mul_right 10 hs
  omega

theorem cpa_handlePost_queries (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).handlePost.queries primW primWS =
      max (18 + min K S.N_dh * 14) (16 + min K S.N_dh * 6 + min K S.N_sess_tot * 10) := by
  simp [aeadCpaRedProg, authCodec, cpaPostC, bindV, caseSumV, Comp.queries, cpaStepC_queries]

theorem cpa_handlePost_queries_le (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).handlePost.queries primW primWS ≤
      18 + S.N_dh * 14 + S.N_sess_tot * 10 := by
  rw [cpa_handlePost_queries]
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hd1 := Nat.mul_le_mul_right 14 hd
  have hd2 := Nat.mul_le_mul_right 6 hd
  have hs1 := Nat.mul_le_mul_right 10 hs
  omega

end

theorem aeadCpaRedProg_totalCost_poly_le_clamped (S : Setup) (K q : Nat) :
    (aeadCpaRedProg S K).totalCost q ≤
      80 + bits (min K S.N_send_tot) +
      q * (12032 + K * 5000 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7500) +
      900 + (150 + min K S.N_dh * 413 + (min K S.N_dh) ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  unfold TwoStageCostedReduction.totalCost
  have hU : pqPrimIface.uCost = 1 := rfl
  have hC : (authCodec S).codecCost = 32 := rfl
  rw [hU, hC, cpa_init_cost, cpa_chDone_cost, cpa_resume_cost, cpa_finish_cost]
  have hPre := cpa_handlePre_cost_le_clamped S K
  have hPost := cpa_handlePost_cost_le_clamped S K
  have hMax : max 1 (max (aeadCpaRedProg S K).handlePre.cost (aeadCpaRedProg S K).handlePost.cost + 32) ≤
      12032 + K * 5000 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7500 := by omega
  have hMul := Nat.mul_le_mul_left q hMax
  omega

theorem aeadCpaRedProg_totalCost_poly_le (S : Setup) (K q : Nat) :
    (aeadCpaRedProg S K).totalCost q ≤
      66 + bits S.N_send_tot +
      q * (12032 + slotIdxCost S + K * 5000 + S.N_dh * 1550 + S.N_sess_tot * 7500) +
      874 + (112 + S.N_dh * 413 + S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  unfold TwoStageCostedReduction.totalCost
  have hU : pqPrimIface.uCost = 1 := rfl
  have hC : (authCodec S).codecCost = 32 := rfl
  rw [hU, hC, cpa_init_cost, cpa_chDone_cost, cpa_resume_cost, cpa_finish_cost]
  have hb : bits (min K S.N_send_tot) ≤ bits S.N_send_tot := by
    simp only [bits]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.min_le_right _ _)) 1
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hd2 : (min K S.N_dh) ^ 2 ≤ S.N_dh ^ 2 := Nat.pow_le_pow_left hd 2
  have hPre := cpa_handlePre_cost_le S K
  have hPost := cpa_handlePost_cost_le S K
  have hMax : max 1 (max (aeadCpaRedProg S K).handlePre.cost (aeadCpaRedProg S K).handlePost.cost + 32) ≤
      12032 + slotIdxCost S + K * 5000 + S.N_dh * 1550 + S.N_sess_tot * 7500 := by omega
  have hMul := Nat.mul_le_mul_left q hMax
  have := Nat.mul_le_mul_right 413 hd
  have := Nat.mul_le_mul_right 1088 hd2
  omega

theorem aeadCpaRedProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (aeadCpaRedProg S b.q_total).totalCost b.q_total ≤ stepCostBudget S b := by
  refine le_trans (aeadCpaRedProg_totalCost_poly_le S b.q_total b.q_total) ?_
  have hSlot := slotIdxCost_le S
  have hbSend : bits S.N_send_tot ≤ S.N_sess_tot + 1 := by
    have := bits_le_succ S.N_send_tot
    unfold Setup.N_sess_tot; omega
  unfold stepCostBudget
  generalize b.q_total = q at *
  have h1 : q * (12032 + slotIdxCost S + q * 5000 + S.N_dh * 1550 + S.N_sess_tot * 7500) ≤
      q * (12042 + q * 5000 + S.N_dh * 1550 + S.N_sess_tot * 7501) :=
    Nat.mul_le_mul_left q (by omega)
  nlinarith [Nat.zero_le (q * S.N_dh), Nat.zero_le (q * S.N_sess_tot),
    Nat.zero_le (S.N_dh * S.N_sess_tot)]

theorem aeadCpaRedProg_totalCost_le_security (S : Setup) (b : QueryBudget) :
    (aeadCpaRedProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine le_trans (aeadCpaRedProg_totalCost_poly_le_clamped S b.q_total b.q_total) ?_
  have hSendLe : min b.q_total S.N_send_tot ≤ min b.q_total S.N_sess_tot := by
    unfold Setup.N_sess_tot; omega
  have hbSend : bits (min b.q_total S.N_send_tot) ≤ min b.q_total S.N_sess_tot + 1 := by
    have h1 : bits (min b.q_total S.N_send_tot) ≤ min b.q_total S.N_send_tot + 1 :=
      bits_le_succ _
    omega
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize b.q_total = q at *
  set md := min q S.N_dh
  set ms := min q S.N_sess_tot
  set lg := Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot
  nlinarith [Nat.zero_le (q * md), Nat.zero_le (q * ms), Nat.zero_le (md * ms),
    Nat.zero_le lg, Nat.zero_le (q * lg)]

theorem aeadCpaRedProg_totalQueries_poly_le (S : Setup) (K q : Nat) :
    (aeadCpaRedProg S K).totalQueries primW primWS q ≤
      q * (18 + S.N_dh * 14 + S.N_sess_tot * 10) + S.N_dh * 5 := by
  simp only [TwoStageCostedReduction.totalQueries, cpa_init_queries, cpa_chDone_queries,
    cpa_resume_queries, cpa_finish_queries]
  have hPre := cpa_handlePre_queries_le S K
  have hPost := cpa_handlePost_queries_le S K
  have hMax : max ((aeadCpaRedProg S K).handlePre.queries primW primWS)
      ((aeadCpaRedProg S K).handlePost.queries primW primWS) ≤
      18 + S.N_dh * 14 + S.N_sess_tot * 10 := max_le hPre hPost
  have hMul := Nat.mul_le_mul_left q hMax
  omega

theorem aeadCpaRedProg_totalQueries_le (S : Setup) (b : QueryBudget) :
    (aeadCpaRedProg S b.q_total).totalQueries primW primWS b.q_total ≤ primQueryBudget S b := by
  refine le_trans (aeadCpaRedProg_totalQueries_poly_le S b.q_total b.q_total) ?_
  unfold primQueryBudget
  nlinarith

end SignalPqxdh.Security.ReductionDsl.AuthAead
