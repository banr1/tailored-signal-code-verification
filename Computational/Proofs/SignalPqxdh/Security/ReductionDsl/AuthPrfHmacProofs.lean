/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacDsl
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaProofs

/-!
# Cost and Query Bounds for `prfHmacRedProg`

Proves syntactic `.cost`, primitive-query, and challenge-query bounds for `prfHmacRedProg` against
`stepCostBudget` and `primQueryBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf SignalPqxdh.Security.ReductionDsl.AuthAead
open OracleSpec OracleComp

section
attribute [local simp] Expr.cost Comp.cost

@[simp] theorem bits_8 : bits 8 = 4 := by decide
@[simp] theorem bits_24 : bits 24 = 5 := by decide
@[simp] theorem bits_firstMsgHdrLen : bits firstMsgHdrLen = 7 := by decide

@[simp] theorem cost_bytesTake {Γ : List PT} (w : ℕ+) (n : Expr pqxdhOps Γ .nat)
    (x : Expr pqxdhOps Γ (B w)) :
    (bytesTake w n x).cost = n.cost + x.cost + w.val + 2 := by
  simp [bytesTake, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem cost_bytesDrop {Γ : List PT} (w : ℕ+) (n : Expr pqxdhOps Γ .nat)
    (x : Expr pqxdhOps Γ (B w)) :
    (bytesDrop w n x).cost = n.cost + x.cost + w.val + 2 := by
  simp [bytesDrop, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem cost_widenB_32 {Γ : List PT} (x : Expr pqxdhOps Γ (B 24)) :
    @Expr.cost pqSig pqxdhOps Γ (B 32) (widenB 24 8 x) = x.cost + 32 := by
  dsimp only [widenB, Expr.cost]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.val_ofNat]

@[simp] theorem cost_queryHmacEval {Γ : List PT} (x : Expr pqxdhOps Γ (B 359)) :
    (queryHmacEval x).cost = x.cost + 392 := rfl

@[simp] theorem cost_natLe {Γ : List PT} (a b : Expr pqxdhOps Γ .nat) :
    (natLe a b).cost = a.cost + b.cost + 2 := by
  simp [natLe]; omega

@[simp] theorem etmBodyE_cost {Γ : List PT} (ct : Expr pqxdhOps Γ (B 32)) :
    (etmBodyE ct).cost = 2 * ct.cost + 45 := by
  simp only [etmBodyE, cost_bytesTake, cost_bytesLen, Expr.cost, PNat.val_ofNat, bits_8, bits_32]
  omega

@[simp] theorem etmBodyE_widenB_cost {Γ : List PT} (x : Expr pqxdhOps Γ (B 24)) :
    (etmBodyE (widenB 24 8 x)).cost = 2 * x.cost + 109 := by
  dsimp only [etmBodyE, bytesTake, bytesLen, widenB, Expr.cost]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.val_ofNat, bits_8, bits_32]
  omega

@[simp] theorem etmBody24E_cost {Γ : List PT} (ct : Expr pqxdhOps Γ (B 24)) :
    (etmBody24E ct).cost = 2 * ct.cost + 36 := by
  simp only [etmBody24E, cost_bytesTake, cost_bytesLen, Expr.cost, PNat.val_ofNat, bits_8, bits_24]
  omega

@[simp] theorem etmTagE_cost {Γ : List PT} (ct : Expr pqxdhOps Γ (B 32)) :
    (etmTagE ct).cost = 2 * ct.cost + 45 := by
  simp only [etmTagE, cost_bytesDrop, cost_bytesLen, Expr.cost, PNat.val_ofNat, bits_8, bits_32]
  omega

@[simp] theorem macInputE_cost {Γ : List PT} (ad : Expr pqxdhOps Γ (B 158)) (ct : Expr pqxdhOps Γ (B 32)) :
    (macInputE ad ct).cost = 2 * ad.cost + 2 * ct.cost + 998 := by
  dsimp only [macInputE, catB, bytesTake, bytesDrop, bytesCons, bytesVarint, bytesLen, Expr.cost]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.val_ofNat, bits_32, bits_firstMsgHdrLen]
  omega

def initSlotCost (S : Setup) : Nat :=
  max (5 + bits (if S.N_id = 0 then 0 else S.N_send_opk))
    (2 + max (6 + bits S.N_send_opk_tot + bits (if S.N_id = 0 then 0 else S.N_send_no_opk))
      (bits S.N_send_tot))

@[simp] theorem initSlotE_cost (S : Setup) {Γ : List PT} (sid : Expr pqxdhOps Γ sessionIdTy) :
    (initSlotE S sid).cost = sid.cost + initSlotCost S + 1 := by
  simp only [initSlotE, initSlotCost, eCaseSum, v, Expr.cost]
  omega

theorem initSlotCost_le (S : Setup) : initSlotCost S ≤ 10 + S.N_sess_tot := by
  unfold initSlotCost Setup.N_sess_tot Setup.N_send_tot
    Setup.N_send_opk_tot Setup.N_send_no_opk_tot
  by_cases h : S.N_id = 0
  · simp [h, bits_0]
  · have hpos : 1 ≤ S.N_id := by omega
    have h1 : S.N_send_opk ≤ S.N_id * S.N_send_opk := by
      simpa using Nat.mul_le_mul_right S.N_send_opk hpos
    have h2 : S.N_send_no_opk ≤ S.N_id * S.N_send_no_opk := by
      simpa using Nat.mul_le_mul_right S.N_send_no_opk hpos
    have hb1 := AuthAead.bits_le_succ S.N_send_opk
    have hb2 := AuthAead.bits_le_succ (S.N_id * S.N_send_opk)
    have hb3 := AuthAead.bits_le_succ S.N_send_no_opk
    have hb4 := AuthAead.bits_le_succ (S.N_id * S.N_send_opk + S.N_id * S.N_send_no_opk)
    simp only [h, ite_false]
    omega

theorem bits_le_log_succ (n : Nat) : bits n ≤ Nat.log 2 n + 1 := le_rfl

theorem initSlotCost_le_log (S : Setup) : initSlotCost S ≤ 10 + 2 * Nat.log 2 S.N_sess_tot := by
  unfold initSlotCost
  have hsess : S.N_send_tot ≤ S.N_sess_tot := by unfold Setup.N_sess_tot; omega
  have hopk_tot : S.N_send_opk_tot ≤ S.N_sess_tot := by
    unfold Setup.N_sess_tot Setup.N_send_tot; omega
  have hb_tot := (bits_le_log_succ S.N_send_tot).trans (Nat.add_le_add_right (Nat.log_mono_right hsess) 1)
  have hb_opk_tot := (bits_le_log_succ S.N_send_opk_tot).trans (Nat.add_le_add_right (Nat.log_mono_right hopk_tot) 1)
  by_cases h : S.N_id = 0
  · simp only [h, ite_true, bits_0]
    omega
  · have hpos : 1 ≤ S.N_id := by omega
    have hopk : S.N_send_opk ≤ S.N_sess_tot := by
      have h1 : S.N_send_opk ≤ S.N_id * S.N_send_opk := by
        simpa using Nat.mul_le_mul_right S.N_send_opk hpos
      unfold Setup.N_sess_tot Setup.N_send_tot Setup.N_send_opk_tot; omega
    have hnoopk : S.N_send_no_opk ≤ S.N_sess_tot := by
      have h2 : S.N_send_no_opk ≤ S.N_id * S.N_send_no_opk := by
        simpa using Nat.mul_le_mul_right S.N_send_no_opk hpos
      unfold Setup.N_sess_tot Setup.N_send_tot Setup.N_send_no_opk_tot; omega
    have hb_opk := (bits_le_log_succ S.N_send_opk).trans (Nat.add_le_add_right (Nat.log_mono_right hopk) 1)
    have hb_noopk := (bits_le_log_succ S.N_send_no_opk).trans (Nat.add_le_add_right (Nat.log_mono_right hnoopk) 1)
    simp only [h, ite_false]
    omega

@[simp] theorem pendFilterE_cost (K : Nat) {Γ₁ Γ : List PT}
    (a : Var Γ₁ (.prod muPendTy (.prod .nat (B 359)))) [Ext Γ₁ Γ] :
    (pendFilterE K (Γ := Γ) a).cost = 4 + K * 737 := by
  simp only [pendFilterE, natEq, cost_bytesBeq, v, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem pendHitE_cost (K : Nat) {Γ₁ Γ : List PT}
    (a : Var Γ₁ (.prod muPendTy (.prod .nat (.prod (B 359) (B 32))))) [Ext Γ₁ Γ] :
    (pendHitE K (Γ := Γ) a).cost = 3 + K * 845 := by
  simp only [pendHitE, eAny, natEq, cost_bytesBeq, cost_bytesTake, v, Expr.cost,
    PNat.val_ofNat, bits_8]
  omega

@[simp] theorem dedupE_cost (K : Nat) {Γ₁ Γ : List PT}
    (xs : Var Γ₁ (.list (.prod .nat (B 359)))) [Ext Γ₁ Γ] :
    (dedupE K (Γ := Γ) xs).cost = 3 + K * 7 + K ^ 2 * 730 := by
  simp only [dedupE, natEq, cost_bytesBeq, v, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring

@[simp] theorem hmContX0E_cost {Γ : List PT} (c : Expr pqxdhOps Γ hmSendContTy) :
    (hmContX0E c).cost = 6 * c.cost + 1268 := by
  simp only [hmContX0E, macInputE_cost, etmBodyE_widenB_cost, Expr.cost]
  omega

@[simp] private theorem muKeyIdEq_cost {Γ : List PT} (a b : Expr pqxdhOps Γ muKeyIdTy) :
    (muKeyIdEq a b).cost = a.cost + b.cost + 55 := by
  simp only [muKeyIdEq, eLet2, eLet, eCaseSum, sidEq_cost, natEq, v, Expr.cost]
  omega

@[simp] private theorem initKeyIdE_cost (S : Setup) {Γ : List PT}
    (sid : Expr pqxdhOps Γ sessionIdTy) :
    (initKeyIdE S sid).cost = sid.cost + 7 := by
  simp only [initKeyIdE, eCaseSum, v, Expr.cost, bits_0]
  omega

@[simp] private theorem hmKeyIdC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) :
    (hmKeyIdC K a).cost = a.cost + 127 + K * 59 := by
  simp only [hmKeyIdC, letV, caseOptV, bindV, eFind, muKeyIdEq_cost, muKeys, muChal, muPend, muBad,
    muMk, cost_letC, cost_samplePrim, PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost,
    PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

@[simp] theorem hmKeyC_cost (K : Nat) {Δ : List PT} (a : Expr pqxdhOps Δ (.prod .nat muStTy)) :
    (hmKeyC K a).cost = a.cost + 135 + K * 59 := by
  simp only [hmKeyC, letV, hmKeyIdC_cost, cost_letC, v, Expr.cost]
  omega

@[simp] theorem encPostC_cost (K : Nat) {Δ : List PT} (a : Expr pqxdhOps Δ (.prod encContTy (B 32))) :
    (encPostC K a).cost = a.cost + 1429 + K * 1582 := by
  simp only [encPostC, letV, macInputE_cost, etmBodyE_widenB_cost, etmBody24E_cost,
    pendFilterE_cost, pendHitE_cost, muKeys, muChal, muPend, muBad, muMk,
    cost_letC, cost_catB, cost_takeKB, cost_boolOr, v, Comp.cost, Expr.cost,
    PNat.val_ofNat]
  omega

@[simp] private theorem hmEncPreIdC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmEncPreIdC K a).cost = a.cost + 1968 + K * 1700 := by
  simp only [hmEncPreIdC, letV, caseOptV, bindV, eFind, muKeyIdEq_cost, natEq, natLt,
    hmKeyIdC_cost, encPostC_cost, muKeys, muChal, muPend, muBad, muMk,
    cost_letC, cost_samplePrim, cost_queryPrim, cost_widenB_32,
    PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

@[simp] theorem hmEncPreC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod .nat (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmEncPreC K a).cost = a.cost + 1981 + K * 1700 := by
  simp only [hmEncPreC, letV, hmEncPreIdC_cost, cost_letC, v, Expr.cost]
  omega

@[simp] private theorem hmForgeIdC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmForgeIdC K a).cost = a.cost + 3855 + K * 177 := by
  simp only [hmForgeIdC, letV, bindV, eCaseOpt, eFind, muKeyIdEq_cost, cost_natLe, isSomeE,
    hmKeyIdC_cost, macInputE_cost, etmBodyE_cost, etmTagE_cost,
    muKeys, muChal, muPend, muBad, muMk,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_bytesLen, cost_boolOr,
    Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_24, bits_32]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

@[simp] theorem hmForgeC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod .nat (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmForgeC K a).cost = a.cost + 3868 + K * 177 := by
  simp only [hmForgeC, letV, hmForgeIdC_cost, cost_letC, v, Expr.cost]
  omega

@[simp] theorem finishIntC_cost {Δ : List PT} (a : Expr pqxdhOps Δ intFinArgsTy) :
    (finishIntC a).cost = a.cost + 706 := by
  simp only [finishIntC, letV, isSomeE, optFst, optSnd, eCaseOpt,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, stMk, stUpd,
    ipUEntry, ipPeer, ipFim, ipFresh, ipIdeal, ipMsgPlain, ipT3, ipKeys6, ipDrKey,
    ipRks4, ipSalt, ipPqMsg, ipAd, ipProv, ipRoC, ipRootC,
    hdMk, pmMk, seMk, ikrMk, iasMk, aSendFresh, aSendUnfresh,
    peIkAPk, pkbIkB, pkbSpkId, pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB,
    cost_letC, cost_bytesBeq, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]

@[simp] theorem hmPostC_cost (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod hmSendContTy (B 32))) :
    (hmPostC K a).cost = a.cost + 2325 + K * 1582 := by
  simp only [hmPostC, letV, bindV, getDBytes, eCaseOpt,
    encPostC_cost, finishIntC_cost, defaultMsgKeysE,
    defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length, defaultMsgKeys_iv_length,
    cost_letC, cost_litB, v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem hm_init_cost (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).init.cost = 75 + bits (S.N_send_tot + S.N_recv_tot) := by
  simp only [prfHmacRedProg, hmInitC, bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE,
    emptyAuthStE, emptyAuthSlotStE, emptyMuE, ahsfMk, ahsfMkSlots, assMk, ahsMk, stMk, muMk,
    cost_sampleChal, PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost, bits_0]
  omega

theorem hm_finish_cost (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).finish.cost = 35 + K * 432 + K ^ 2 * 1575 := by
  simp only [prfHmacRedProg, hmFinishC, letV, bindV, mapMV, eMap, eAny,
    dedupE_cost, pendHitE_cost, natLt, muPend, muBad,
    cost_letC, cost_sampleChal, cost_queryHmacEval, cost_boolOr,
    PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring

private theorem intSendPrepC_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (intSendPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt intPrepTy)).cost ≤
      10500 + K * 4100 + min K S.N_dh * 1540 := by
  cases opk <;>
  · simp only [intSendPrepC,
      koskBundleOkC_cost, spkHonIdealFromPeerC_cost, checkBundleProvenanceExactC_cost,
      hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost, buildSecretsE_cost, sidEq_cost,
      findHonestC, getDBytes, optSnd,
      bindV, letV, caseOptV, findMV, eFind, eAny, eCaseOpt,
      natEq, isSomeE,
      ahsfHybrid, ahsBase, asSecb, asPrincipals, asUsedSendSessions, asRoCache, asRootRoCache,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      cost_encEC, cost_encKEM, cost_letC, cost_samplePrim, cost_queryPrim,
      cost_bytesLen, cost_bytesBeq, cost_boolOr, cost_litB,
      PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem hmSendTailC_cost_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmSendTailC S K opk jt fhst mst x p : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      3500 + K * 1750 := by
  cases opk <;>
  · simp only [hmSendTailC, sendSidE,
      hmEncPreIdC_cost, finishIntC_cost, initKeyIdE_cost,
      getDBytes, defaultMsgKeysE,
      defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length, defaultMsgKeys_iv_length,
      ipAd, ipMsgPlain, ipIdeal, ipRks4, ipSalt, ipT3, ipFim,
      bindV, letV, caseSumV, eCaseOpt,
      cost_letC, cost_queryPrim, cost_litB,
      Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem hmSendC_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmSendC S K opk jt fhst mst x : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      14100 + K * 5850 + min K S.N_dh * 1540 := by
  unfold hmSendC
  have hPrep := intSendPrepC_cost_le S K opk (Δ := Δ) fhst x
  have hTail := hmSendTailC_cost_le S K opk (Δ := intPrepTy :: .opt intPrepTy :: Δ)
    jt fhst mst x (.zero : Var (intPrepTy :: .opt intPrepTy :: Δ) intPrepTy)
  cases opk <;>
  · simp only [sendGuardE, isSomeE, pkbOpkB?, aNone, bindV, caseOptV,
      v, Comp.cost, Expr.cost, ite_true, ite_false, Bool.false_eq_true]
    omega

private theorem hmRecvPrepC_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (hmRecvPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy)).cost ≤
      7000 + K * 300 + min K S.N_dh * 420 := by
  cases opk <;>
  · simp only [hmRecvPrepC,
      koskSenderOkC_cost, optU32Eq_cost, kyberCheckE_cost, buildSecretsE_cost,
      findHonestC, bindV, letV, caseOptV, caseSumV, findMV, eFind, eAny, eCaseOpt,
      natEq, nat2Eq, nat3Eq, isSomeE,
      ahsfHybrid, ahsBase, ahsRecvKemRecs, ahsMk, ahsUpd, ahsInitKemRecs, ahsIdealSessions,
      asPrincipals, asSpkBundles, asOpkEntries, asUsedRecvOPK, asUsedRecvNoOPK,
      asUsedKyberTriples, peSecIKA0, peIkAPk, sbSpkSk, sbPqspkSk, sbPqspkPk,
      oeOpkSk, oeOpkPk, oeConsumed, rkrMk,
      hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
      cost_u32OfNat, cost_u32Beq, cost_letC, cost_queryPrim,
      cost_bytesLen, cost_bytesBeq, cost_boolOr,
      Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem hmSchedPrepC_cost_le (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (hmSchedPrepC S K a).cost ≤
      a.cost + 1500 + K * 600 + min K S.N_dh * 210 + min K S.N_sess_tot * 7350 := by
  simp only [hmSchedPrepC,
    matchIdealAuthHandshakeC_cost, hkdfRoC_cost, rootRoC_cost, findHonestC, iasCk1_0E,
    bindV, letV, caseOptV, findMV, eCaseOpt, isSomeE,
    ahsBase, ahsIdealSessions, asPrincipals, asRoCache, asRootRoCache,
    peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkPk,
    hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg,
    iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasEphAPk,
    cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesBeq, cost_boolOr,
    PSamp.cost, PSamp.ty, Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem hmSchedFinC_cost_le (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) :
    (hmSchedFinC S K a).cost ≤
      a.cost + 6500 + K * 900 := by
  simp only [hmSchedFinC, forgeRetIdC,
    hmForgeIdC_cost, initKeyIdE_cost, firstMsgADE_cost, sidEq_cost, sameSaltKeyE_cost,
    iasAdE, iasAeadCtE, iasMsgPlainE,
    defaultMsgKeysE, defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length,
    defaultMsgKeys_iv_length,
    bindV, letV, caseOptV, eFind, eCaseOpt,
    peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    iasSid, iasSpqrSalt?,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_litB,
    Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem hmSchedC_cost_le (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (hmSchedC S K a).cost ≤
      a.cost + 8100 + K * 1500 + min K S.N_dh * 210 + min K S.N_sess_tot * 7350 := by
  unfold hmSchedC
  refine le_trans
    (letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     bindV_cost_le _ _ (hmSchedPrepC_cost_le S K _) <|
     caseOptV_cost_le _ _ _
       (by simp only [v, Comp.cost, Expr.cost]; exact le_rfl)
       (hmSchedFinC_cost_le S K _))
    ?_
  simp only [v, Expr.cost]
  omega

private theorem hmRecvTailC_cost_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    (hmRecvTailC S K opk jt fhst mst x d : Comp pqxdhOps pqPrimIface Δ hmResTy).cost ≤
      9000 + K * 1650 + min K S.N_dh * 210 + min K S.N_sess_tot * 7350 := by
  unfold hmRecvTailC
  refine le_trans
    (letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     bindV_cost_le (N := 500 + K * 40) _ _ (hmSchedC_cost_le S K _) ?_)
    ?_
  · cases opk <;>
    · simp only [finErasedE, letV, eMap, eCaseOpt, natEq, nat2Eq, nat3Eq,
        ahsfRecvCount, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
        ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
        asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
        asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
        asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
        asAdvKeys, stMk, stUpd, oeOpkSk, oeOpkPk, oeMk, oeUpd,
        aNone, aRecvHonest, aRecvUnfresh,
        cost_letC, v, Comp.cost, Expr.cost, bits_0, bits_1, ite_true, ite_false, Bool.false_eq_true]
      repeat' first
        | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
        | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
      omega
  · simp only [ahsfRecvCount, ahsfMkSaltCache, v, Expr.cost]
    omega

private theorem hmRecvC_cost_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmRecvC S K opk jt fhst mst x : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      16200 + K * 2000 + min K S.N_dh * 630 + min K S.N_sess_tot * 7350 := by
  unfold hmRecvC
  refine le_trans
    (bindV_cost_le _ _ (hmRecvPrepC_cost_le S K opk fhst x) <|
     caseOptV_cost_le _ _ _
       (by simp only [aNone, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache,
         v, Comp.cost, Expr.cost, bits_1]; exact le_rfl)
       (bindV_cost_le _ _ (hmRecvTailC_cost_le S K opk jt fhst mst x .zero)
         (by simp only [v, Comp.cost, Expr.cost]; exact le_rfl)))
    (by simp only [v, Expr.cost]; omega)

private theorem hmOther_cost_le {Γ₁ Δ : List PT} (mst : Var Γ₁ muStTy) [Ext Γ₁ Δ]
    (m : Comp pqxdhOps pqPrimIface Δ RSF) {M : Nat} (hm : m.cost ≤ M) :
    (hmOther mst m).cost ≤ M + 10 := by
  simp only [hmOther, bindV, v, Comp.cost, Expr.cost]
  omega

private theorem hmDispatchC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (q : Var Γ₄ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmDispatchC S K jt fhst mst q : Comp pqxdhOps pqPrimIface Δ hmPreTy).cost ≤
      16250 + K * 5900 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7350 := by
  unfold hmDispatchC
  refine le_trans
    (caseSumV_cost_le _ _ _ (hmOther_cost_le _ _ (initPrinFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (hmOther_cost_le _ _ (corruptFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (hmOther_cost_le _ _ (genSpkFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (hmOther_cost_le _ _ (genOpkFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (hmSendC_cost_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (hmSendC_cost_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (hmRecvC_cost_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (hmRecvC_cost_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (hmOther_cost_le _ _ (roFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (hmOther_cost_le _ _ (roRootFixedB_cost_le K _ _)) <|
     caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
     hmOther_cost_le _ _ (registerFixedB_cost_le _ _))
    (by omega)

private theorem hmPreC_cost_le (S : Setup) (K : Nat) :
    (hmPreC S K).cost ≤
      16300 + K * 5900 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7350 := by
  unfold hmPreC
  refine le_trans
    (letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <| letV_cost_le _ _ <|
     hmDispatchC_cost_le S K _ _ _ _)
    (by simp only [v, Expr.cost]; omega)

private theorem hm_handle_cost_clamped_le (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).handle.cost ≤
      24000 + K * 7500 + min K S.N_dh * 1550 + min K S.N_sess_tot * 7350 := by
  dsimp only [prfHmacRedProg, authCodec]
  unfold hmHandleC
  have hPre := hmPreC_cost_le S K
  simp only [bindV, letV, caseSumV, hmContX0E_cost, hmPostC_cost,
    cost_liftPrimComp, cost_queryHmacEval, cost_letC, v, Comp.cost, Expr.cost]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem hm_handle_cost_tight_le (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).handle.cost ≤
      24000 + initSlotCost S + K * 7500 + min K S.N_dh * 1550 +
        S.N_sess_tot * 7350 + Nat.log 2 S.N_sess_tot * 10 := by
  refine le_trans (hm_handle_cost_clamped_le S K) ?_
  have := Nat.min_le_right K S.N_sess_tot
  omega

theorem hm_handle_cost_le (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).handle.cost ≤
      24000 + initSlotCost S + K * 7500 + S.N_dh * 1550 + S.N_sess_tot * 7500 := by
  refine le_trans (hm_handle_cost_tight_le S K) ?_
  have := Nat.min_le_right K S.N_dh
  have := Nat.log_le_self 2 S.N_sess_tot
  omega

theorem hm_init_queries_prim (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).init.queries chalPrimW chalWS = 0 := by
  simp [prfHmacRedProg, hmInitC, bindV, sampleChal, chalWS, Comp.queries]

theorem hm_finish_queries_prim (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).finish.queries chalPrimW chalWS = 0 := by
  simp [prfHmacRedProg, hmFinishC, letV, bindV, mapMV, sampleChal, queryHmacEval,
    queries_letC, chalPrimW, chalWS, Comp.queries]

@[simp] private theorem hmPostC_queries (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod hmSendContTy (B 32))) :
    (hmPostC K a).queries primW primWS = 0 := by
  simp [hmPostC, encPostC, finishIntC, bindV, letV, queries_letC, Comp.queries]

@[simp] private theorem hmSendC_queries (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmSendC S K opk jt fhst mst x : Comp pqxdhOps pqPrimIface Δ hmPreTy).queries primW primWS =
      18 + min K S.N_dh * 14 := by
  cases opk <;>
  · simp only [hmSendC, intSendPrepC, hmSendTailC, hmEncPreIdC, hmKeyIdC, encPostC, finishIntC,
      koskBundleOkC_queries, spkHonIdealFromPeerC_queries, checkBundleProvenanceExactC_queries,
      hkdfRoC, rootRoC, findHonestC,
      bindV, letV, caseOptV, caseSumV, findMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

@[simp] private theorem hmRecvC_queries (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (x : Var Γ₄ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (hmRecvC S K opk jt fhst mst x : Comp pqxdhOps pqPrimIface Δ hmPreTy).queries primW primWS =
      16 + min K S.N_dh * 6 + min K S.N_sess_tot * 10 := by
  cases opk <;>
  · simp only [hmRecvC, hmRecvPrepC, hmRecvTailC, hmSchedC, hmSchedPrepC, hmSchedFinC,
      forgeRetIdC, hmForgeIdC, hmKeyIdC,
      koskSenderOkC_queries, matchIdealAuthHandshakeC_queries, hkdfRoC, rootRoC, findHonestC,
      bindV, letV, caseOptV, caseSumV, findMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

theorem hm_handle_queries_prim (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).handle.queries chalPrimW chalWS =
      max (18 + min K S.N_dh * 14) (16 + min K S.N_dh * 6 + min K S.N_sess_tot * 10) := by
  simp only [prfHmacRedProg, authCodec, hmHandleC, hmPreC, hmDispatchC, hmOther,
    hmPostC_queries, hmSendC_queries, hmRecvC_queries,
    initPrinFixedB_queries, corruptFixedB_queries, genSpkFixedB_queries, genOpkFixedB_queries,
    roFixedB_queries, roRootFixedB_queries, registerFixedB_queries,
    bindV, letV, caseSumV,
    queries_letC, queries_liftPrimComp_prim, queryHmacEval, chalPrimW, Comp.queries]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem hm_handle_queries_prim_le (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).handle.queries chalPrimW chalWS ≤
      18 + S.N_dh * 14 + S.N_sess_tot * 10 := by
  rw [hm_handle_queries_prim]
  have := Nat.min_le_right K S.N_dh
  have := Nat.min_le_right K S.N_sess_tot
  omega

end

theorem prfHmacRedProg_totalCost_poly_le (S : Setup) (K q : Nat) :
    (prfHmacRedProg S K).totalCost q ≤
      75 + bits (S.N_send_tot + S.N_recv_tot) +
      q * (24032 + initSlotCost S + K * 7500 + S.N_dh * 1550 + S.N_sess_tot * 7500) +
      (35 + K * 432 + K ^ 2 * 1575) := by
  unfold CostedReduction.totalCost
  have hU : pqPrfHmacIface.uCost = 1 := rfl
  have hC : (authCodec S).codecCost = 32 := rfl
  rw [hU, hC, hm_init_cost, hm_finish_cost]
  have hH := hm_handle_cost_le S K
  have hMax : max 1 ((prfHmacRedProg S K).handle.cost + 32) ≤
      24032 + initSlotCost S + K * 7500 + S.N_dh * 1550 + S.N_sess_tot * 7500 := by omega
  have hMul := Nat.mul_le_mul_left q hMax
  omega

/-- Step-cost bound for `prfHmacRedProg` against `AuthAead.stepCostBudget`. -/
theorem prfHmacRedProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (prfHmacRedProg S b.q_total).totalCost b.q_total ≤ AuthAead.stepCostBudget S b := by
  refine le_trans (prfHmacRedProg_totalCost_poly_le S b.q_total b.q_total) ?_
  have hSlot := initSlotCost_le S
  have hbSess : bits (S.N_send_tot + S.N_recv_tot) ≤ S.N_sess_tot + 1 := by
    have := AuthAead.bits_le_succ (S.N_send_tot + S.N_recv_tot)
    unfold Setup.N_sess_tot; omega
  unfold AuthAead.stepCostBudget
  generalize b.q_total = q at *
  have h1 : q * (24032 + initSlotCost S + q * 7500 + S.N_dh * 1550 + S.N_sess_tot * 7500) ≤
      q * (24042 + q * 7500 + S.N_dh * 1550 + S.N_sess_tot * 7501) :=
    Nat.mul_le_mul_left q (by omega)
  nlinarith [Nat.zero_le (q * S.N_dh), Nat.zero_le (q * S.N_sess_tot),
    Nat.zero_le (S.N_dh * S.N_sess_tot)]

/-- Twice-`totalCost` bound for `prfHmacRedProg` against `SignalPqxdh.Security.stepCostBudget`. -/
theorem prfHmacRedProg_totalCost_two_mul_security_le (S : Setup) (b : QueryBudget) :
    2 * (prfHmacRedProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  unfold CostedReduction.totalCost _root_.SignalPqxdh.Security.stepCostBudget
  have hU : pqPrfHmacIface.uCost = 1 := rfl
  have hC : (authCodec S).codecCost = 32 := rfl
  rw [hU, hC, hm_init_cost, hm_finish_cost]
  have hH := hm_handle_cost_clamped_le S b.q_total
  have hbSess : bits (S.N_send_tot + S.N_recv_tot) ≤ Nat.log 2 S.N_sess_tot + 1 := by
    have hs : S.N_send_tot + S.N_recv_tot = S.N_sess_tot := rfl
    rw [hs]; exact le_rfl
  set q := b.q_total
  set M_dh := min q S.N_dh
  set M_sess := min q S.N_sess_tot
  set L_dh := Nat.log 2 S.N_dh
  set L_sess := Nat.log 2 S.N_sess_tot
  have hMax : max 1 ((prfHmacRedProg S q).handle.cost + 32) ≤
      24032 + q * 7500 + M_dh * 1550 + M_sess * 7350 := by omega
  have hMul := Nat.mul_le_mul_left q hMax
  nlinarith [Nat.zero_le (q * M_dh), Nat.zero_le (q * M_sess),
    Nat.zero_le (q * L_dh), Nat.zero_le (q * L_sess),
    Nat.zero_le (M_dh ^ 2), Nat.zero_le (M_dh * M_sess)]

/-- Step-cost bound for `prfHmacRedProg` against `SignalPqxdh.Security.stepCostBudget`. -/
theorem prfHmacRedProg_totalCost_security_le (S : Setup) (b : QueryBudget) :
    (prfHmacRedProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b :=
  le_trans (by omega) (prfHmacRedProg_totalCost_two_mul_security_le S b)

theorem prfHmacRedProg_totalQueries_prim_poly_le (S : Setup) (K q : Nat) :
    (prfHmacRedProg S K).totalQueries chalPrimW chalWS q ≤
      q * (18 + S.N_dh * 14 + S.N_sess_tot * 10) := by
  simp only [CostedReduction.totalQueries, hm_init_queries_prim, hm_finish_queries_prim]
  have hMul := Nat.mul_le_mul_left q (hm_handle_queries_prim_le S K)
  omega

/-- Primitive-query bound for `prfHmacRedProg` against `primQueryBudget`. -/
theorem prfHmacRedProg_totalQueries_prim_le (S : Setup) (b : QueryBudget) :
    (prfHmacRedProg S b.q_total).totalQueries chalPrimW chalWS b.q_total ≤
      primQueryBudget S b := by
  refine le_trans (prfHmacRedProg_totalQueries_prim_poly_le S b.q_total b.q_total) ?_
  unfold primQueryBudget
  nlinarith

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
