/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaProofs

/-!
# Two-Fuel `AuthPrf` and `AuthAead` Branch Bounds

Step-cost, `.random64`-coin, primitive-query, AST-size, and byte-literal-size bounds over
`pqxdhOps` for the two-fuel `(K_on, K_ro)` handshake arms `authCkSendKB`, `authCkRecvKB`,
`authMkSendPreKB`, `authMkRecvPreKB`, `cpaSendSlotKB`, and `cpaRecvKC`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostPrf

open _root_.ReductionDsl (Ty Var Expr Comp bits)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (sampR64W compLitSize)
open _root_.SignalPqxdh (Setup)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps B primIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (shcrStTy pauseTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (authHybridStateFixedTy prfMkCoreTy prfMkStepPreTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead (cpaSlotSendResTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
  (muStTy intPrepTy schedPrepArgsTy schedPrepTy schedArgsTy schedResTy hmRecvDataTy hmResTy hmPreTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (sendKC recvKB shcrFinishSendKC shcrSendKC shcrAcceptKB shcrResumeKC
   authCkSendKB authCkRecvKB authMkSendPreKB authMkRecvPreKB cpaSendSlotKB cpaRecvKC
   intSendPrepKC hmSendKC hmSchedPrepKC hmSchedKC hmRecvTailKC hmRecvKC)

section PrfBranchBounds

open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (exprLitSize pqOpLitSize r64W)
open _root_.SignalPqxdh (F_X25519)
open _root_.SignalPqxdh.LegacyCosted
  (pqPrimIface PTag PSamp U32 drKeyT msgKeysT pqBytesOps pqU32Ops)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext sendQTy recvQTy PT RSF v bindV letV caseOptV caseSumV findMV anyMV consumeFirstMV
   eLet eLet2 eCaseOpt eCaseSum eFind eAny eMap
   litB catB bytesCons widenB takeKB bytesLen bytesBeq bytesVarint u32OfNat u32Beq
   samplePrim queryPrim encEC encKEM boolOr boolBeq
   bits_0 bits_1 bits_32 bits_33 F_X25519_length
   cost_boolOr cost_boolBeq cost_litB cost_encEC cost_encKEM cost_bytesLen cost_bytesBeq
   cost_u32OfNat cost_u32Beq cost_samplePrim cost_queryPrim cost_letC
   firstMsgADE firstMsgADE_cost buildSecretsE buildSecretsE_cost sidEq sidEq_cost
   optU32Eq optU32Eq_cost saltBytesE sameSaltKeyE sameSaltKeyE_cost kyberEq kyberCheckE kyberCheckE_cost
   koskBundleOkC koskBundleOkC_cost koskBundleOkC_queries
   koskSenderOkC koskSenderOkC_cost koskSenderOkC_queries
   checkBundleProvenanceExactC checkBundleProvenanceExactC_cost checkBundleProvenanceExactC_queries
   matchIdealAuthHandshakeC matchIdealAuthHandshakeC_cost matchIdealAuthHandshakeC_queries
   recvFinishTagRunC recvFinishTagRunC_cost recvFinishTagRunC_queries
   prepareAuthHybridRecvC prepareAuthHybridRecvC_true_cost prepareAuthHybridRecvC_false_cost
   prepareAuthHybridRecvC_true_queries prepareAuthHybridRecvC_false_queries
   finishAuthHybridSendC finishAuthHybridSendC_cost finishAuthHybridSendC_queries
   hkdfRoC hkdfRoC_cost rootRoC rootRoC_cost
   findHonestC isAdvRegC isGameSpkC isGameOpkC resolveSigPkC checkBundleSpkHonIdealC
   matchSentOPKC matchSentNoOPKC sendGuardE
   sampCkPairC sampAtCkC finishAuthRecvCkC finishAuthSendMkC finishAuthRecvMkC
   finishRecvUnmatchedMkPreC
   primW primWS queries_letC
   authHybridStateTy authSlotStateTy sessionIdTy preKeyMsgTy preparedAuthRecvTy drKeyTy
   principalEntryTy preKeyBundleTy keys6Ty msgKeysTy authMkSaltCacheTy recvFinishTagTy
   recvFinishResTy finishSendArgsTy
   mkcSecb mkcIdx mkcSentChal mkcFhst mkcMk
   parKEntry parSecrets parDhRatchet parIsUncorrSender parMatchedSess? parSameEph parHstDec
   parFinishTag fhstSetBase
   peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peCorrupted
   sbSpkSk sbSpkPk sbPqspkSk sbPqspkPk oeOpkSk oeOpkPk oeConsumed
   pkbIkB pkbSpkId pkbSpkB pkbSpkSig pkbOpkB? pkbPqspkId pkbPqspkB pkbPqspkSig
   hdrIkAPk hdrEkAPk hdrSpkId hdrOpkId? hdrPqspkId hdrKemCt
   pkmHdr pkmEphAPk pkmPqRatchetMsg pkmAeadCt
   soA0 soB0 soSb soOb soA1 soPk1 soCt soM soMatched soMarkMatched
   snoA0 snoB0 snoSb snoA1 snoPk1 snoCt snoM snoMatched snoMarkMatched
   roBCorr roA0 roB0 roSb roOb roA1 roPk1 roCt roM
   rnoBCorr rnoA0 rnoB0 rnoSb rnoA1 rnoPk1 rnoCt rnoM
   aseSpkHonest asePqspkHonest aseEkASk aseFresh aseChallenged
   ikrPqspkPk ikrKemCt ikrKemSs rkrPqspkPk rkrKemCt rkrKemSs
   iasSid iasIkAPk iasPeerIkPk iasPeerSpkPk iasPeerOpkPk? iasEkAPk iasPeerPqspkPk
   iasKemCt iasEphAPk iasSpqrSalt? iasDrKey iasRk1 iasMkSeed iasCk1_1 iasMsgKeys
   asSecb asHasWonAuth asPrincipals asSpkBundles asOpkEntries asSessions
   asUsedSendSessions asUsedRecvOPK asUsedRecvNoOPK asUsedKyberTriples
   asSentOPKEvents asSentNoOPKEvents asRecvdOPKEvents asRecvdNoOPKEvents
   asAdvKeys asRoCache asRootRoCache
   ahsBase ahsInitKemRecs ahsRecvKemRecs ahsIdealSessions
   ahsfHybrid ahsfRecvCount ahsfMkSaltCache ahsfSlots
   assNext assSendOpk assSendNoOpk assRecv assMk emptyAuthSlotStE
   lookupSendSlotE lookupSendSlotOrZeroE allocSendSlotE
   lookupRecvSlotE lookupRecvSlotOrZeroE allocRecvSlotE ahsfMkSlots ahsfUpdSlots
   natEq natLt nat2Eq nat3Eq bytes2Eq isSomeE optFst optSnd sessionSlotIndexE
   peMk peUpd sbMk oeMk oeUpd buMk hdMk pmMk seMk iasMk soMk snoMk roMk rnoMk
   ikrMk rkrMk stMk stUpd ahsMk ahsUpd ahsfMk ahsfUpd
   aNone aInitPrin aPk aCorr aBundle aSendFresh aSendUnfresh aRecvHonest aRecvUnfresh
   aDrKey aRootKdf)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
  (cpaSendB finishCpaC finishCpaC_cost finishCpaC_queries
   spkHonIdealFromPeerC spkHonIdealFromPeerC_cost spkHonIdealFromPeerC_queries
   getDBytes defaultMsgKeysE iasAdE iasAeadCtE iasMsgPlainE iasCk1_0E
   defaultMsgKeys_cipherKey_length defaultMsgKeys_macKey_length defaultMsgKeys_iv_length)

attribute [local simp] Expr.cost Comp.cost

@[local simp] private theorem lookupSendSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy) :
    (lookupSendSlotE ss sid).cost = ss.cost + sid.cost + 148 := by
  simp only [lookupSendSlotE, eLet2, eLet, eCaseSum, assSendOpk, assSendNoOpk, v, Expr.cost]
  omega

@[local simp] private theorem lookupSendSlotOrZeroE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy) :
    (lookupSendSlotOrZeroE ss sid).cost = ss.cost + sid.cost + 150 := by
  simp only [lookupSendSlotOrZeroE, lookupSendSlotE_cost, eCaseOpt, v, Expr.cost, bits_0]
  omega

@[local simp] private theorem allocSendSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy) :
    (allocSendSlotE ss sid).cost = ss.cost + sid.cost + 436 := by
  simp only [allocSendSlotE, eLet2, eLet, eCaseSum, eCaseOpt, assMk, assNext, assSendOpk,
    assSendNoOpk, assRecv, v, Expr.cost, bits_0, bits_1]
  omega

@[local simp] private theorem allocRecvSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (rc : Expr pqxdhOps Γ .nat) :
    (allocRecvSlotE ss rc).cost = ss.cost + rc.cost + 231 := by
  simp only [allocRecvSlotE, eLet2, eLet, eCaseOpt, assMk, assNext, assSendOpk,
    assSendNoOpk, assRecv, v, Expr.cost, bits_1]
  omega

@[local simp] private theorem finishAuthRecvCkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rc' : Expr pqxdhOps Δ .nat)
    (p : Expr pqxdhOps Δ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvCkC S K msg prep drKey rk1 spqrSalt? rc' p).cost =
      drKey.cost + rk1.cost + spqrSalt?.cost + rc'.cost + p.cost +
      1827 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishAuthRecvCkC, bindV, letV, eCaseOpt, firstMsgADE_cost,
    recvFinishTagRunC_cost, ahsBase, parHstDec, parFinishTag, parKEntry,
    hdrIkAPk, pkmHdr, peIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    asRoCache, asRootRoCache, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
    cost_letC, cost_queryPrim, v, Comp.cost, Expr.cost,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, bits_0]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[local simp] private theorem finishAuthSendMkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (sid : Expr pqxdhOps Δ sessionIdTy) (uE : Expr pqxdhOps Δ principalEntryTy)
    (pp : Expr pqxdhOps Δ (.opt (.prod .nat principalEntryTy))) (isFresh : Expr pqxdhOps Δ .bool)
    (bu : Expr pqxdhOps Δ preKeyBundleTy) (m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (keys6 : Expr pqxdhOps Δ keys6Ty) (drKey : Expr pqxdhOps Δ drKeyTy)
    (rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (pqMsg msgPlain : Expr pqxdhOps Δ (B 32)) (mks : Expr pqxdhOps Δ msgKeysTy) [Ext Γ₁ Δ] :
    (finishAuthSendMkC S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
      spqrSalt? pqMsg msgPlain mks).cost =
      sid.cost + uE.cost + pp.cost + isFresh.cost + bu.cost + m01.cost + keys6.cost +
      drKey.cost + rk1.cost + mkSeed.cost + ck1_1.cost + spqrSalt?.cost + pqMsg.cost +
      msgPlain.cost + mks.cost + 2354 + min K S.N_dh * 920 + K * 3239 := by
  simp only [finishAuthSendMkC, bindV, letV, firstMsgADE_cost, finishAuthHybridSendC_cost,
    ahsfHybrid, ahsBase, peIkAPk, pkbIkB, asRoCache, asRootRoCache, ahsfUpd, ahsfMkSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    cost_letC, cost_queryPrim, cost_litB, v, Comp.cost, Expr.cost,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, List.length_nil]
  omega

@[local simp] private theorem finishAuthRecvMkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 ck1_1 : Expr pqxdhOps Δ (B 32)) (rc' : Expr pqxdhOps Δ .nat)
    (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) (mks : Expr pqxdhOps Δ msgKeysTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvMkC S K msg prep drKey rk1 ck1_1 rc' cache' mks).cost =
      drKey.cost + rk1.cost + ck1_1.cost + rc'.cost + cache'.cost + mks.cost +
      1679 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishAuthRecvMkC, bindV, letV, eCaseOpt, firstMsgADE_cost,
    recvFinishTagRunC_cost, ahsBase, parHstDec, parFinishTag, parKEntry,
    hdrIkAPk, pkmHdr, peIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    asRoCache, asRootRoCache, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
    cost_letC, cost_queryPrim, v, Comp.cost, Expr.cost,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, bits_0]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[local simp] private theorem finishRecvUnmatchedMkPreC_cost_tight (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (msg : Var Γ₂ preKeyMsgTy)
    (prep : Var Γ₃ preparedAuthRecvTy) (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rSlot rc' : Expr pqxdhOps Δ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (finishRecvUnmatchedMkPreC S K core msg prep drKey rk1 spqrSalt? rSlot rc').cost =
      drKey.cost + rk1.cost + spqrSalt?.cost + rSlot.cost + rc'.cost +
      2008 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishRecvUnmatchedMkPreC, bindV, letV, natEq, natLt, finishAuthRecvMkC_cost_tight,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsfUpdSlots, ahsfMkSlots, mkcMk,
    cost_letC, cost_samplePrim, cost_queryPrim, PSamp.cost,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, v,
    Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[local simp] private theorem samplePrim_r64_eq {Γ : List PT} (s : PSamp) :
    (samplePrim (Γ := Γ) s).queries (fun _ => 0) (sampR64W rfl) = r64W s := rfl

@[local simp] private theorem queryPrim_r64_eq {Γ : List PT} (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (queryPrim g e).queries (fun _ => 0) (sampR64W rfl) = 0 := rfl

@[local simp] private theorem v_litSize {Γ Δ : List PT} {τ : PT} [Ext Γ Δ] (x : Var Γ τ) :
    exprLitSize (v (Δ := Δ) x) = 0 := rfl

private theorem bits_mono_le {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b :=
  _root_.ReductionDsl.bits_mono h

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[local simp] private theorem recvFinishTagRunC_size (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).size =
      res?.size + bits K + 4 * bits (min K S.N_dh) + 1864 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC,
    natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk, rnoMk, stMk, stUpd, ahsMk, ahsUpd,
    aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt,
    pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched, snoA0, snoB0,
    snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb,
    roA1, roPk1, roCt, roM, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
    asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    boolOr, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, caseSumV, findMV, consumeFirstMV, eMap,
    bytesBeq, queryPrim, Comp.size, Expr.size]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[local simp] private theorem prepareAuthHybridRecvC_true_size (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K true hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).size =
      6 * bits K + 3 * bits (min K S.N_dh) + 875 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk,
    iasPeerPqspkPk, iasKemCt, iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asUsedRecvOPK, asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, findMV, eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[local simp] private theorem prepareAuthHybridRecvC_false_size (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K false hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).size =
      5 * bits K + 3 * bits (min K S.N_dh) + 813 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asUsedRecvNoOPK,
    asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, findMV, eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
@[local simp] private theorem finishAuthHybridSendC_size (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    (finishAuthHybridSendC S K hst args).size =
      args.size + 4 * bits (min K S.N_dh) + 2 * bits K + 1040 := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, natEq, isSomeE, boolOr,
    optFst, optSnd, hdMk, pmMk, seMk, iasMk, soMk, snoMk, ikrMk, stMk, stUpd, ahsMk, ahsUpd,
    aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkId,
    pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
    asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    bindV, letV, caseOptV, findMV, anyMV, eCaseOpt, eAny, bytesBeq, queryPrim, Comp.size, Expr.size]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
@[local simp] private theorem recvFinishTagRunC_r64 (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC,
    bindV, letV, caseOptV, caseSumV, findMV, consumeFirstMV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM,
    samplePrim_r64_eq, queryPrim_r64_eq, r64W, Comp.queries, Nat.max_self, Nat.add_zero, Nat.mul_zero]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
@[local simp] private theorem prepareAuthHybridRecvC_r64 (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K opk hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).queries
      (fun _ => 0) (sampR64W rfl) = 0 := by
  cases opk <;> simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, bindV, letV, caseOptV, findMV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    Comp.iteC, Comp.caseOptC, Comp.findBoundedM,
    samplePrim_r64_eq, queryPrim_r64_eq, r64W, Comp.queries, ↓reduceIte, Bool.false_eq_true,
    Nat.max_self, Nat.add_zero, Nat.mul_zero]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
@[local simp] private theorem finishAuthHybridSendC_r64 (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    (finishAuthHybridSendC S K hst args).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, bindV, letV, caseOptV, findMV, anyMV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    Comp.iteC, Comp.caseOptC, Comp.findBoundedM, Comp.anyBoundedM,
    samplePrim_r64_eq, queryPrim_r64_eq, r64W, Comp.queries, Nat.max_self, Nat.add_zero, Nat.mul_zero]

set_option maxRecDepth 200000 in
local macro "prove_r64" : tactic => `(tactic| {
  simp only [authCkSendKB, authCkRecvKB, authMkSendPreKB, authMkRecvPreKB, cpaSendSlotKB, cpaRecvKC,
    AuthCoreKArmsBase.authCkSendKB, AuthCoreKArmsBase.authCkRecvKB,
    AuthCoreKArmsBase.authMkSendPreKB, AuthCoreKArmsBase.authMkRecvPreKB,
    AuthCoreKArmsBase.cpaSendSlotKB, AuthCoreKArmsBase.cpaRecvKC,
    finishAuthRecvCkC, finishAuthSendMkC, finishAuthRecvMkC, finishRecvUnmatchedMkPreC,
    recvFinishTagRunC_r64, prepareAuthHybridRecvC_r64, finishAuthHybridSendC_r64,
    sampCkPairC, sampAtCkC, cpaSendB, finishCpaC, spkHonIdealFromPeerC,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    bindV, letV, caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM,
    samplePrim_r64_eq, queryPrim_r64_eq, r64W, Comp.queries,
    ↓reduceIte, Bool.false_eq_true, id_eq, Nat.max_self, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega })

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
@[local simp] private theorem recvFinishTagRunC_litSize (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    compLitSize (recvFinishTagRunC S K tag res?) = exprLitSize res? := by
  simp (config := { maxSteps := 1000000 }) only [
    recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC,
    natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk, rnoMk, stMk, stUpd, ahsMk, ahsUpd,
    aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt, pkmHdr,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, boolOr,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v_litSize, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, consumeFirstMV, eMap,
    bytesBeq, Expr.bytesBeq, queryPrim, compLitSize, exprLitSize, pqOpLitSize,
    Nat.add_zero, Nat.zero_add]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
@[local simp] private theorem finishAuthHybridSendC_litSize (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    compLitSize (finishAuthHybridSendC S K hst args) = exprLitSize args := by
  simp (config := { maxSteps := 1000000 }) only [
    finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, natEq, isSomeE, boolOr, optFst, optSnd,
    hdMk, pmMk, seMk, iasMk, soMk, snoMk, ikrMk, stMk, stUpd, ahsMk, ahsUpd,
    aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkPk,
    pkbIkB, pkbSpkId, pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v_litSize, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV, anyMV, eCaseOpt, eAny,
    bytesBeq, Expr.bytesBeq, queryPrim, compLitSize, exprLitSize, pqOpLitSize,
    Nat.add_zero, Nat.zero_add]

set_option maxRecDepth 200000 in
local macro "prove_size" s:ident k:ident : tactic => `(tactic| {
  simp only [authCkSendKB, authCkRecvKB, authMkSendPreKB, authMkRecvPreKB, cpaSendSlotKB, cpaRecvKC,
    AuthCoreKArmsBase.authCkSendKB, AuthCoreKArmsBase.authCkRecvKB,
    AuthCoreKArmsBase.authMkSendPreKB, AuthCoreKArmsBase.authMkRecvPreKB,
    AuthCoreKArmsBase.cpaSendSlotKB, AuthCoreKArmsBase.cpaRecvKC,
    finishAuthRecvCkC, finishAuthSendMkC, finishAuthRecvMkC, finishRecvUnmatchedMkPreC,
    sampCkPairC, sampAtCkC, mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
    cpaSendB, finishCpaC, spkHonIdealFromPeerC,
    getDBytes, defaultMsgKeysE, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
    recvFinishTagRunC_size, prepareAuthHybridRecvC_true_size, prepareAuthHybridRecvC_false_size,
    finishAuthHybridSendC_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, asRoCache, asRootRoCache,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE, ahsfMkSlots, ahsfUpdSlots,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, id_eq]
  dsimp only [pqxdhOps, _root_.ReductionDsl.Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hmdh : bits (min $k ($s).N_dh) ≤ bits $k := bits_mono_le (Nat.min_le_left _ _)
  have hmsess : bits (min $k ($s).N_sess_tot) ≤ bits $k := bits_mono_le (Nat.min_le_left _ _)
  omega })

set_option maxRecDepth 200000 in
local macro "prove_litSize" : tactic => `(tactic| {
  simp (config := { maxSteps := 1000000 }) only [
    authCkSendKB, authCkRecvKB, authMkSendPreKB, authMkRecvPreKB, cpaSendSlotKB, cpaRecvKC,
    AuthCoreKArmsBase.authCkSendKB, AuthCoreKArmsBase.authCkRecvKB,
    AuthCoreKArmsBase.authMkSendPreKB, AuthCoreKArmsBase.authMkRecvPreKB,
    AuthCoreKArmsBase.cpaSendSlotKB, AuthCoreKArmsBase.cpaRecvKC,
    finishAuthRecvCkC, finishAuthSendMkC, finishAuthRecvMkC, finishRecvUnmatchedMkPreC,
    recvFinishTagRunC_litSize, finishAuthHybridSendC_litSize, prepareAuthHybridRecvC,
    sampCkPairC, sampAtCkC, mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
    cpaSendB, finishCpaC, spkHonIdealFromPeerC,
    getDBytes, defaultMsgKeysE, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, asRoCache, asRootRoCache,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE, ahsfMkSlots, ahsfUpdSlots,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v_litSize, v, _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Comp.letC,
    _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden, Expr.bytesTakeK,
    Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint, Expr.u32OfNat, Expr.u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, F_X25519_length,
    defaultMsgKeys_cipherKey_length, defaultMsgKeys_macKey_length, defaultMsgKeys_iv_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
  omega })

theorem authCkSendKB_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).cost ≤
      19000 + 13469 * K_on + 16000 * min K_on S.N_dh + 531 * K_ro := by
  cases opk <;>
  · simp only [authCkSendKB, AuthCoreKArmsBase.authCkSendKB, sampAtCkC, sampCkPairC,
      koskBundleOkC_cost, finishAuthHybridSendC_cost, hkdfRoC_cost, rootRoC_cost,
      allocSendSlotE_cost, sidEq_cost, firstMsgADE_cost, buildSecretsE_cost,
      resolveSigPkC, checkBundleSpkHonIdealC, findHonestC, sendGuardE,
      cost_encEC, cost_encKEM, bindV, letV, caseOptV, findMV, anyMV, eFind, eAny, eCaseOpt,
      natEq, natLt, isSomeE, ahsfHybrid, ahsfRecvCount, ahsfSlots, ahsfMkSlots,
      ahsBase, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asUsedSendSessions,
      asRoCache, asRootRoCache, peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      sbSpkPk, sbPqspkPk, pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      aNone, cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesLen, cost_bytesBeq,
      cost_boolOr, cost_litB, PSamp.cost, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v,
      Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil, bits_32,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
theorem authCkSendKB_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).queries (fun _ => 0) (sampR64W rfl) ≤
      2 := by
  cases opk <;> prove_r64

theorem authCkSendKB_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 20 + 26 * min K_on S.N_dh := by
  change (authCkSendKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).queries primW primWS ≤ _
  cases opk <;>
  · simp only [authCkSendKB, AuthCoreKArmsBase.authCkSendKB, sampAtCkC, sampCkPairC,
      koskBundleOkC_queries, finishAuthHybridSendC_queries, hkdfRoC, rootRoC,
      resolveSigPkC, checkBundleSpkHonIdealC, findHonestC, bindV, letV, caseOptV, findMV, anyMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
theorem authCkSendKB_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).size ≤
      12000 + 30 * bits K_on + 10 * bits K_ro := by
  cases opk <;> prove_size S K_on

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem authCkSendKB_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    compLitSize (authCkSendKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x) ≤ 4000 := by
  cases opk <;> prove_litSize

theorem authCkRecvKB_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).cost ≤
      19000 + 13469 * K_on + 16000 * min K_on S.N_dh + 531 * K_ro := by
  cases opk <;>
  · simp only [authCkRecvKB, AuthCoreKArmsBase.authCkRecvKB, sampAtCkC, sampCkPairC,
      recvFinishTagRunC_cost, prepareAuthHybridRecvC_true_cost, prepareAuthHybridRecvC_false_cost,
      finishAuthRecvCkC_cost_tight, allocRecvSlotE_cost, hkdfRoC_cost, rootRoC_cost,
      firstMsgADE_cost, bindV, letV, caseOptV, eCaseOpt, natEq, natLt, isSomeE,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots,
      ahsfUpd, ahsfUpdSlots, ahsBase,
      peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasDrKey, iasRk1, iasMkSeed, iasCk1_1,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, aNone,
      cost_letC, cost_samplePrim, cost_queryPrim, cost_boolOr,
      PSamp.cost, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, bits_1]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
theorem authCkRecvKB_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).queries (fun _ => 0) (sampR64W rfl) ≤
      2 := by
  cases opk <;> prove_r64

theorem authCkRecvKB_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 20 + 26 * min K_on S.N_dh := by
  change (authCkRecvKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).queries primW primWS ≤ _
  cases opk <;>
  · simp only [authCkRecvKB, AuthCoreKArmsBase.authCkRecvKB, sampAtCkC, sampCkPairC,
      finishAuthRecvCkC, prepareAuthHybridRecvC_true_queries, prepareAuthHybridRecvC_false_queries,
      recvFinishTagRunC_queries, hkdfRoC, rootRoC, bindV, letV, caseOptV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
theorem authCkRecvKB_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x).size ≤
      20000 + 64 * bits K_on + 10 * bits K_ro := by
  cases opk <;> prove_size S K_on

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem authCkRecvKB_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    compLitSize (authCkRecvKB S K_on K_ro opk (Δ := Δ) idx chalP fhst x) ≤ 4000 := by
  cases opk <;> prove_litSize

theorem authMkSendPreKB_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreKB S K_on K_ro opk (Δ := Δ) core x).cost ≤
      15000 + 9469 * K_on + 16000 * min K_on S.N_dh + 531 * K_ro := by
  cases opk <;>
  · simp only [authMkSendPreKB, AuthCoreKArmsBase.authMkSendPreKB, koskBundleOkC_cost,
      finishAuthHybridSendC_cost, finishAuthSendMkC_cost_tight, hkdfRoC_cost, rootRoC_cost,
      allocSendSlotE_cost, sidEq_cost, firstMsgADE_cost, buildSecretsE_cost,
      resolveSigPkC, checkBundleSpkHonIdealC, findHonestC, sendGuardE,
      cost_encEC, cost_encKEM, bindV, letV, caseOptV, findMV, anyMV, eFind, eAny, eCaseOpt,
      natEq, natLt, isSomeE, mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsfUpdSlots, ahsBase,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asUsedSendSessions,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      sbSpkPk, sbPqspkPk, pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      aNone, cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesLen, cost_bytesBeq,
      cost_boolOr, cost_litB, PSamp.cost, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v,
      Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil, bits_32,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
theorem authMkSendPreKB_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreKB S K_on K_ro opk (Δ := Δ) core x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  cases opk <;> prove_r64

theorem authMkSendPreKB_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreKB S K_on K_ro opk (Δ := Δ) core x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 20 + 26 * min K_on S.N_dh := by
  change (authMkSendPreKB S K_on K_ro opk (Δ := Δ) core x).queries primW primWS ≤ _
  cases opk <;>
  · simp only [authMkSendPreKB, AuthCoreKArmsBase.authMkSendPreKB, finishAuthSendMkC,
      koskBundleOkC_queries, finishAuthHybridSendC_queries, hkdfRoC, rootRoC,
      resolveSigPkC, checkBundleSpkHonIdealC, findHonestC, bindV, letV, caseOptV, findMV, anyMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
theorem authMkSendPreKB_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreKB S K_on K_ro opk (Δ := Δ) core x).size ≤
      12000 + 50 * bits K_on + 10 * bits K_ro := by
  cases opk <;> prove_size S K_on

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem authMkSendPreKB_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (authMkSendPreKB S K_on K_ro opk (Δ := Δ) core x) ≤ 4000 := by
  cases opk <;> prove_litSize

theorem authMkRecvPreKB_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreKB S K_on K_ro opk (Δ := Δ) core x).cost ≤
      15000 + 9469 * K_on + 16000 * min K_on S.N_dh + 531 * K_ro := by
  cases opk <;>
  · simp only [authMkRecvPreKB, AuthCoreKArmsBase.authMkRecvPreKB, recvFinishTagRunC_cost,
      prepareAuthHybridRecvC_true_cost, prepareAuthHybridRecvC_false_cost,
      finishAuthRecvMkC_cost_tight, finishRecvUnmatchedMkPreC_cost_tight,
      hkdfRoC_cost, rootRoC_cost, allocRecvSlotE_cost,
      lookupSendSlotE_cost, sidEq_cost, sameSaltKeyE_cost, firstMsgADE_cost,
      bindV, letV, caseOptV, eFind, eCaseOpt, natEq, natLt, isSomeE,
      mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsfUpdSlots, ahsBase,
      peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasSid, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, aNone,
      cost_letC, cost_samplePrim, cost_queryPrim, cost_boolOr,
      PSamp.cost, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, bits_0, bits_1]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
theorem authMkRecvPreKB_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreKB S K_on K_ro opk (Δ := Δ) core x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  cases opk <;> prove_r64

theorem authMkRecvPreKB_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreKB S K_on K_ro opk (Δ := Δ) core x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 20 + 26 * min K_on S.N_dh := by
  change (authMkRecvPreKB S K_on K_ro opk (Δ := Δ) core x).queries primW primWS ≤ _
  cases opk <;>
  · simp only [authMkRecvPreKB, AuthCoreKArmsBase.authMkRecvPreKB,
      finishAuthRecvMkC, finishRecvUnmatchedMkPreC,
      prepareAuthHybridRecvC_true_queries, prepareAuthHybridRecvC_false_queries,
      recvFinishTagRunC_queries, hkdfRoC, rootRoC, bindV, letV, caseOptV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
theorem authMkRecvPreKB_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreKB S K_on K_ro opk (Δ := Δ) core x).size ≤
      40000 + 100 * bits K_on + 10 * bits K_ro := by
  cases opk <;> prove_size S K_on

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem authMkRecvPreKB_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (authMkRecvPreKB S K_on K_ro opk (Δ := Δ) core x) ≤ 4000 := by
  cases opk <;> prove_litSize

theorem cpaSendSlotKB_cost_le (S : Setup) (K_on K_ro : ℕ) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (cpaSendSlotKB S K_on K_ro opk allowPause (Δ := Δ) idx ns fhst x).cost ≤
      11700 + 3969 * K_on + 1540 * min K_on S.N_dh + 531 * K_ro := by
  cases opk <;> cases allowPause <;>
  · simp only [cpaSendSlotKB, AuthCoreKArmsBase.cpaSendSlotKB,
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
      PSamp.cost, PSamp.ty, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, bits_1, bits_32, ite_true, ite_false,
      Bool.false_eq_true, id_eq]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
theorem cpaSendSlotKB_r64_le (S : Setup) (K_on K_ro : ℕ) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (cpaSendSlotKB S K_on K_ro opk allowPause (Δ := Δ) idx ns fhst x).queries
        (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  cases opk <;> cases allowPause <;> prove_r64

theorem cpaSendSlotKB_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (cpaSendSlotKB S K_on K_ro opk allowPause (Δ := Δ) idx ns fhst x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 25 + 20 * min K_on S.N_dh := by
  change (cpaSendSlotKB S K_on K_ro opk allowPause (Δ := Δ) idx ns fhst x).queries primW primWS ≤ _
  cases opk <;> cases allowPause <;>
  · simp only [cpaSendSlotKB, AuthCoreKArmsBase.cpaSendSlotKB,
      koskBundleOkC_queries, finishCpaC_queries, spkHonIdealFromPeerC_queries,
      checkBundleProvenanceExactC_queries, hkdfRoC, rootRoC, findHonestC,
      bindV, letV, caseOptV, findMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true, id_eq]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
theorem cpaSendSlotKB_size_le (S : Setup) (K_on K_ro : ℕ) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (cpaSendSlotKB S K_on K_ro opk allowPause (Δ := Δ) idx ns fhst x).size ≤
      12000 + 30 * bits K_on + 10 * bits K_ro := by
  cases opk <;> cases allowPause <;> prove_size S K_on

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem cpaSendSlotKB_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    compLitSize (cpaSendSlotKB S K_on K_ro opk allowPause (Δ := Δ) idx ns fhst x) ≤ 4000 := by
  cases opk <;> cases allowPause <;> prove_litSize

theorem cpaRecvKC_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (cpaRecvKC S K_on K_ro opk (Δ := Δ) fhst x).cost ≤
      11600 + 3969 * K_on + 1540 * min K_on S.N_dh + 7450 * min K_on S.N_sess_tot + 531 * K_ro := by
  cases opk <;>
  · simp only [cpaRecvKC, AuthCoreKArmsBase.cpaRecvKC,
      koskSenderOkC_cost, matchIdealAuthHandshakeC_cost,
      hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost, buildSecretsE_cost,
      sidEq_cost, optU32Eq_cost, sameSaltKeyE_cost, kyberCheckE_cost,
      findHonestC, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
      bindV, letV, caseOptV, caseSumV, findMV, eFind, eAny, eMap, eCaseOpt,
      natEq, nat2Eq, nat3Eq,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMk, ahsfMkSlots, ahsfUpd,
      emptyAuthSlotStE, assMk,
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
      PSamp.cost, PSamp.ty, _root_.SignalPqxdh.LegacyCosted.Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, bits_0, bits_1, bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
theorem cpaRecvKC_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (cpaRecvKC S K_on K_ro opk (Δ := Δ) fhst x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  cases opk <;> prove_r64

theorem cpaRecvKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (cpaRecvKC S K_on K_ro opk (Δ := Δ) fhst x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      25 + 20 * min K_on S.N_dh + 10 * min K_on S.N_sess_tot := by
  change (cpaRecvKC S K_on K_ro opk (Δ := Δ) fhst x).queries primW primWS ≤ _
  cases opk <;>
  · simp only [cpaRecvKC, AuthCoreKArmsBase.cpaRecvKC,
      koskSenderOkC_queries, matchIdealAuthHandshakeC_queries,
      hkdfRoC, rootRoC, findHonestC,
      bindV, letV, caseOptV, caseSumV, findMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 200000 in
theorem cpaRecvKC_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (cpaRecvKC S K_on K_ro opk (Δ := Δ) fhst x).size ≤
      12000 + 30 * bits K_on + 10 * bits K_ro := by
  cases opk <;> prove_size S K_on

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1600000 in
theorem cpaRecvKC_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (cpaRecvKC S K_on K_ro opk (Δ := Δ) fhst x) ≤ 4000 := by
  cases opk <;> prove_litSize

end PrfBranchBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCostPrf
