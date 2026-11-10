/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs

/-!
# Two-Fuel `AuthHs` Handshake Branch Bounds

Step-cost, `.random64`-coin, primitive-query, AST-size, and byte-literal-size bounds over
`pqxdhOps` for the two-fuel `(K_on, K_ro)` handshake arms `sendKC`, `recvKB`, `shcrFinishSendKC`,
`shcrSendKC`, `shcrAcceptKB`, and `shcrResumeKC`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCost

open _root_.ReductionDsl (Ty Var Expr Comp bits)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (sampR64W compLitSize exprLitSize pqOpLitSize)
open _root_.SignalPqxdh (Setup)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B primIfacePrimQueryWeight samplerZeroQueryWeight)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy principalEntryTy spkBundleEntryTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (shcrStTy pauseTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
  (sendKC recvKB shcrFinishSendKC shcrSendKC shcrAcceptKB shcrResumeKC)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs (recvTailKC)

section HsBranchBounds

open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (
  Ext sendQTy recvQTy
  shcrFinC onBase preCheckC checkSigsC sendGuardE
  findHonestC isAdvRegC isGameSpkC isGameOpkC koskBundleOkC koskSenderOkC
  resolveSigPkC honestPeerC hkdfOrRoC rootRoC
  scBase scTB scTPk scTSk scCnt scIR scRR scSIdx scChosen scMk scUpd
  pdSid pdBu pdM0 pdM1 pdUI
  stSecb stHasWon stPrin stSpks stOpks stSess stUsedS stUsedO stUsedN stKyb
  stSOE stSNE stROE stRNE stRo stRoot stAdv stMk stUpd
  seSid sePeerIk sePeerSpk sePeerOpk sePeerPqspk seSpkHon seOpkHon sePqspkHon
  seEkASk seEphASk seFresh seChal seMk
  pmHdr pmEphAPk pmPqMsg pmAeadCt pmMk pmUpd
  peSecIKA0 peIkAPk peSecIKAsign peIkSignPk peCorrupted peMk peUpd
  sbSpkSk sbSpkPk sbSpkSig sbPqspkSk sbPqspkPk sbPqspkSig sbRevealed sbMk
  oeOpkSk oeOpkPk oeConsumed oeMk oeUpd
  buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig buMk buUpd
  hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt hdMk hdUpd
  aNone aInitPrin aPk aCorr aBundle aSendFresh aSendUnfresh aRecvHonest aRecvUnfresh
  aDrKey aRootKdf rs firstMsgADE bytes2Eq emptyAuthStE
  isSomeE getDBytes optFst optSnd dhOptNZ guardE kyberCheckE
  natEq nat2Eq nat3Eq optBytesEq optU32Eq sidEq kyberEq nonZero32 buildSecretsE eLet2
  v bindV letV caseOptV caseSumV findMV anyMV mapMV foldMV
  eLet eCaseOpt eCaseSum eFind eAny eMap
  encEC encKEM F_X25519_length
  bits_0 bits_1 bits_2 bits_3 bits_32 bits_33
  koskBundleOkC_costUB resolveSigPkC_costUB findHonestC_costUB
  hkdfOrRoC_true_costUB rootRoC_costUB firstMsgADE_costUB buildSecretsE_costUB
  sidEq_costUB kyberCheckE_costUB koskSenderOkC_costUB optU32Eq_costUB
  preCheckC_costUB checkSigsC_costUB shcrFinC_costUB onBase_costUB
  costUB_encEC costUB_encKEM costUB_bytesLen costUB_bytesBeq costUB_litBytes
  costUB_sampleBytes32 costUB_queryPrim costUB_u32OfNat costUB_u32Beq costUB_v
  primW primWS
  koskBundleOkC_queries resolveSigPkC_queries findHonestC_queries
  hkdfOrRoC_true_queries rootRoC_queries koskSenderOkC_queries
  preCheckC_queries checkSigsC_queries shcrFinC_queries onBase_queries
)

private theorem hs_bits_mono {x y : ℕ} (h : x ≤ y) : bits x ≤ bits y := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

local macro "hs_size_simp" : tactic => `(tactic| (
  simp (config := { maxSteps := 1000000 }) only [
    sendKC, recvKB, shcrFinishSendKC, shcrSendKC, shcrAcceptKB, shcrResumeKC,
    AuthCoreKArmsHs.sendKC, AuthCoreKArmsHs.recvTailKC, AuthCoreKArmsHs.recvKB,
    AuthCoreKArmsHs.shcrFinishSendKC, AuthCoreKArmsHs.shcrSendKC,
    AuthCoreKArmsHs.shcrAcceptKB, AuthCoreKArmsHs.shcrResumeKC,
    shcrFinC, onBase, preCheckC, checkSigsC, sendGuardE,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    pdSid, pdBu, pdM0, pdM1, pdUI,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim, encEC, encKEM, Comp.size, Expr.size,
    bits_0, bits_1, bits_2, bits_3, bits_32, bits_33,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
))

local macro "hs_lit_simp" : tactic => `(tactic| (
  simp (config := { maxSteps := 1000000 }) only [
    sendKC, recvKB, shcrFinishSendKC, shcrSendKC, shcrAcceptKB, shcrResumeKC,
    AuthCoreKArmsHs.sendKC, AuthCoreKArmsHs.recvTailKC, AuthCoreKArmsHs.recvKB,
    AuthCoreKArmsHs.shcrFinishSendKC, AuthCoreKArmsHs.shcrSendKC,
    AuthCoreKArmsHs.shcrAcceptKB, AuthCoreKArmsHs.shcrResumeKC,
    shcrFinC, onBase, preCheckC, checkSigsC, sendGuardE,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    pdSid, pdBu, pdM0, pdM1, pdUI,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, Comp.letC, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
))

@[local simp] private theorem sampR64W_drKey96 :
    sampR64W (I := pqPrimIface) rfl .drKey96 = 0 := rfl

@[local simp] private theorem sampR64W_bytes32 :
    sampR64W (I := pqPrimIface) rfl .bytes32 = 0 := rfl

private theorem hkdfOrRoC_true_r64 (K : ℕ) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K true st sec).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [hkdfOrRoC, letV, caseOptV, bindV, Comp.sampleDrKey96, Comp.queries]

private theorem rootRoC_r64 (K : ℕ) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) :
    (rootRoC K st rk dh).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [rootRoC, letV, caseOptV, bindV, Comp.sampleBytes32, Comp.queries]

private theorem findHonestC_r64 (S : Setup) (K : ℕ) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [findHonestC, letV, findMV, bindV, Comp.queryPrim, Comp.queries]

private theorem koskBundleOkC_r64 (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [koskBundleOkC, isAdvRegC, isGameSpkC, isGameOpkC, findHonestC_r64,
    letV, anyMV, bindV, caseOptV, Comp.queryPrim, Comp.queries]

private theorem koskSenderOkC_r64 (S : Setup) (K : ℕ) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [koskSenderOkC, isAdvRegC, findHonestC_r64, letV, bindV, Comp.queries_letC,
    Comp.queryPrim, Comp.queries]

private theorem resolveSigPkC_r64 (S : Setup) (K : ℕ) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [resolveSigPkC, findHonestC_r64, letV, bindV, Comp.queries_letC, Comp.queries]

theorem sendKC_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sendKC S K_on K_ro opk (Δ := Δ) st x).cost ≤
      12000 + 3570 * K_on + 1030 * min K_on S.N_dh + 531 * K_ro := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  cases opk <;>
  · simp only [sendKC, AuthCoreKArmsHs.sendKC,
      koskBundleOkC_costUB, resolveSigPkC_costUB, findHonestC_costUB,
      hkdfOrRoC_true_costUB, rootRoC_costUB, firstMsgADE_costUB, buildSecretsE_costUB, sidEq_costUB,
      bindV, letV, caseOptV, eFind, eAny, eCaseOpt, Comp.costUB_letC,
      natEq, getDBytes, optFst, optSnd,
      stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
      stSOE, stSNE, stROE, stRNE, stAdv, stMk, stUpd,
      seMk, peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig,
      hdMk, aNone, aSendFresh, aSendUnfresh, rs,
      costUB_encEC, costUB_encKEM, costUB_bytesLen, costUB_bytesBeq, costUB_litBytes,
      costUB_sampleBytes32, costUB_queryPrim,
      _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, List.length_nil, bits_32,
      Bool.false_eq_true, ite_true, ite_false, costUB_v, Comp.costUB, Expr.costUB]
    omega

theorem sendKC_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sendKC S K_on K_ro opk (Δ := Δ) st x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  suffices (sendKC S K_on K_ro opk (Δ := Δ) st x).queries (fun _ => 0) (sampR64W rfl) = 0 by omega
  simp [sendKC, AuthCoreKArmsHs.sendKC, koskBundleOkC_r64, resolveSigPkC_r64, findHonestC_r64,
    hkdfOrRoC_true_r64, rootRoC_r64, bindV, letV, caseOptV, Comp.queries_letC,
    Comp.sampleBytes32, Comp.queryPrim, Comp.queries]

theorem sendKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sendKC S K_on K_ro opk (Δ := Δ) st x).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      20 + 10 * min K_on S.N_dh := by
  change (sendKC S K_on K_ro opk (Δ := Δ) st x).queries primW primWS ≤ 20 + 10 * min K_on S.N_dh
  simp only [sendKC, AuthCoreKArmsHs.sendKC,
    koskBundleOkC_queries, resolveSigPkC_queries, findHonestC_queries,
    hkdfOrRoC_true_queries, rootRoC_queries, bindV, letV, caseOptV, Comp.queries_letC,
    Comp.sampleBytes32, Comp.queryPrim, primW, primWS, Comp.queries]
  omega

set_option linter.unusedSimpArgs false in
theorem sendKC_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sendKC S K_on K_ro opk (Δ := Δ) st x).size ≤
      8000 + 20 * bits K_on + 10 * bits K_ro := by
  have hmin : bits (min K_on S.N_dh) ≤ bits K_on := hs_bits_mono (Nat.min_le_left _ _)
  cases opk <;> · hs_size_simp; omega

set_option linter.unusedSimpArgs false in
theorem sendKC_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (sendKC S K_on K_ro opk (Δ := Δ) st x) ≤ 3000 := by
  cases opk <;> · hs_lit_simp; omega

@[local simp] private theorem recvTailKC_true_costUB (S : Setup) (K_on K_ro : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsHs.recvTailKC S K_on K_ro true st x kE bE oSk?).costUB =
      oSk?.costUB + 9147 + 140 * K_on + 206 * min K_on S.N_dh + 531 * K_ro := by
  simp only [AuthCoreKArmsHs.recvTailKC, findHonestC_costUB, hkdfOrRoC_true_costUB, rootRoC_costUB,
    firstMsgADE_costUB, buildSecretsE_costUB, kyberCheckE_costUB,
    bindV, letV, caseOptV, eMap, eCaseOpt, Comp.costUB_letC,
    nat3Eq, nat2Eq, natEq, getDBytes,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stAdv, stMk, stUpd,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbPqspkSk,
    oeOpkSk, oeOpkPk, oeMk, oeUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdPqspkId, hdKemCt,
    aNone, aRecvHonest, aRecvUnfresh, rs,
    costUB_litBytes, costUB_queryPrim,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, List.length_nil,
    ite_true, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[local simp] private theorem recvTailKC_false_costUB (S : Setup) (K_on K_ro : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsHs.recvTailKC S K_on K_ro false st x kE bE oSk?).costUB =
      oSk?.costUB + 9007 + 100 * K_on + 206 * min K_on S.N_dh + 531 * K_ro := by
  simp only [AuthCoreKArmsHs.recvTailKC, findHonestC_costUB, hkdfOrRoC_true_costUB, rootRoC_costUB,
    firstMsgADE_costUB, buildSecretsE_costUB, kyberCheckE_costUB,
    bindV, letV, caseOptV, eCaseOpt, Comp.costUB_letC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stAdv, stMk, stUpd,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbPqspkSk,
    hdIkAPk, hdEkAPk, hdSpkId, hdPqspkId, hdKemCt,
    aNone, aRecvHonest, aRecvUnfresh, rs,
    costUB_queryPrim, _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat,
    Bool.false_eq_true, ite_false, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[local simp] private theorem recvTailKC_r64 (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsHs.recvTailKC S K_on K_ro opk st x kE bE oSk?).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  cases opk <;> simp [AuthCoreKArmsHs.recvTailKC, findHonestC_r64, hkdfOrRoC_true_r64, rootRoC_r64,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, Comp.queries]

@[local simp] private theorem recvTailKC_true_queries (S : Setup) (K_on K_ro : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsHs.recvTailKC S K_on K_ro true st x kE bE oSk?).queries primW primWS =
      13 + 2 * min K_on S.N_dh := by
  simp only [AuthCoreKArmsHs.recvTailKC, findHonestC_queries, hkdfOrRoC_true_queries, rootRoC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries, ite_true]
  omega

@[local simp] private theorem recvTailKC_false_queries (S : Setup) (K_on K_ro : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsHs.recvTailKC S K_on K_ro false st x kE bE oSk?).queries primW primWS =
      12 + 2 * min K_on S.N_dh := by
  simp only [AuthCoreKArmsHs.recvTailKC, findHonestC_queries, hkdfOrRoC_true_queries, rootRoC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries,
    Bool.false_eq_true, ite_false]
  omega

@[local simp] private theorem recvKB_true_costUB (S : Setup) (K_on K_ro : ℕ)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (AuthCoreKArmsHs.recvKB S K_on K_ro true (Δ := Δ) st x).costUB =
      9474 + 286 * K_on + 412 * min K_on S.N_dh + 531 * K_ro := by
  simp only [AuthCoreKArmsHs.recvKB, recvTailKC_true_costUB, koskSenderOkC_costUB, optU32Eq_costUB,
    bindV, letV, caseOptV, eFind, eAny, Comp.costUB_letC, nat3Eq, nat2Eq, natEq,
    stPrin, stSpks, stOpks, stUsedO, pmHdr, pmEphAPk, oeOpkSk, oeConsumed,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, aNone, rs,
    costUB_bytesLen, costUB_u32OfNat, costUB_u32Beq,
    PNat.val_ofNat, bits_32, ite_true, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[local simp] private theorem recvKB_false_costUB (S : Setup) (K_on K_ro : ℕ)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (AuthCoreKArmsHs.recvKB S K_on K_ro false (Δ := Δ) st x).costUB =
      9304 + 221 * K_on + 412 * min K_on S.N_dh + 531 * K_ro := by
  simp only [AuthCoreKArmsHs.recvKB, recvTailKC_false_costUB, koskSenderOkC_costUB, optU32Eq_costUB,
    bindV, letV, caseOptV, eFind, eAny, Comp.costUB_letC, nat3Eq, nat2Eq, natEq,
    stPrin, stSpks, stUsedN, pmHdr, pmEphAPk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, aNone, rs,
    costUB_bytesLen, costUB_u32OfNat, costUB_u32Beq,
    PNat.val_ofNat, bits_32, Bool.false_eq_true, ite_false, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[local simp] private theorem recvKB_r64 (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (AuthCoreKArmsHs.recvKB S K_on K_ro opk (Δ := Δ) st x).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  cases opk <;> simp [AuthCoreKArmsHs.recvKB, koskSenderOkC_r64, recvTailKC_r64,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queries]

@[local simp] private theorem recvKB_true_queries (S : Setup) (K_on K_ro : ℕ)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (AuthCoreKArmsHs.recvKB S K_on K_ro true (Δ := Δ) st x).queries primW primWS = 14 + 4 * min K_on S.N_dh := by
  simp only [AuthCoreKArmsHs.recvKB, recvTailKC_true_queries, koskSenderOkC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queries, ite_true]
  omega

@[local simp] private theorem recvKB_false_queries (S : Setup) (K_on K_ro : ℕ)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (AuthCoreKArmsHs.recvKB S K_on K_ro false (Δ := Δ) st x).queries primW primWS = 13 + 4 * min K_on S.N_dh := by
  simp only [AuthCoreKArmsHs.recvKB, recvTailKC_false_queries, koskSenderOkC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queries, Bool.false_eq_true, ite_false]
  omega

set_option linter.unusedSimpArgs false in
theorem recvKB_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (recvKB S K_on K_ro opk (Δ := Δ) st x).cost ≤
      9500 + 300 * K_on + 412 * min K_on S.N_dh + 531 * K_ro := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  cases opk <;> · simp only [recvKB, recvKB_true_costUB, recvKB_false_costUB]; omega

theorem recvKB_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (recvKB S K_on K_ro opk (Δ := Δ) st x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  rw [recvKB, recvKB_r64]; omega

set_option linter.unusedSimpArgs false in
theorem recvKB_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (recvKB S K_on K_ro opk (Δ := Δ) st x).queries primIfacePrimQueryWeight samplerZeroQueryWeight ≤
      20 + 4 * min K_on S.N_dh := by
  change (recvKB S K_on K_ro opk (Δ := Δ) st x).queries primW primWS ≤ 20 + 4 * min K_on S.N_dh
  cases opk <;> · simp only [recvKB, recvKB_true_queries, recvKB_false_queries]; omega

set_option linter.unusedSimpArgs false in
theorem recvKB_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (recvKB S K_on K_ro opk (Δ := Δ) st x).size ≤
      8000 + 20 * bits K_on + 10 * bits K_ro := by
  have hmin : bits (min K_on S.N_dh) ≤ bits K_on := hs_bits_mono (Nat.min_le_left _ _)
  cases opk <;> · hs_size_simp; omega

set_option linter.unusedSimpArgs false in
theorem recvKB_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (recvKB S K_on K_ro opk (Δ := Δ) st x) ≤ 3000 := by
  cases opk <;> · hs_lit_simp; omega

@[local simp] private theorem shcrFinishSendKC_costUB (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsHs.shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc).costUB =
      4603 + 3241 * K_on + 531 * K_ro := by
  simp only [AuthCoreKArmsHs.shcrFinishSendKC,
    hkdfOrRoC_true_costUB, rootRoC_costUB, firstMsgADE_costUB, buildSecretsE_costUB,
    bindV, letV, caseOptV, eAny, eCaseOpt, Comp.costUB_letC,
    natEq, getDBytes, optFst, optSnd,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stAdv, stMk, stUpd,
    seMk, peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
    buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
    hdMk, pdSid, pdBu, pdM0, pdM1, pdUI,
    aNone, aSendFresh, aSendUnfresh,
    costUB_bytesBeq, costUB_litBytes, costUB_queryPrim,
    _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, List.length_nil,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

@[local simp] private theorem shcrFinishSendKC_r64 (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsHs.shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc).queries (fun _ => 0) (sampR64W rfl) = 0 := by
  simp [AuthCoreKArmsHs.shcrFinishSendKC,
    hkdfOrRoC_true_r64, rootRoC_r64, bindV, letV, caseOptV, Comp.queries_letC,
    Comp.queryPrim, Comp.queries]

@[local simp] private theorem shcrFinishSendKC_queries (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthCoreKArmsHs.shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc).queries primW primWS = 12 := by
  simp only [AuthCoreKArmsHs.shcrFinishSendKC,
    hkdfOrRoC_true_queries, rootRoC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries]
  omega

theorem shcrFinishSendKC_cost_le (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc).cost ≤
      5000 + 3250 * K_on + 531 * K_ro := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [shcrFinishSendKC, shcrFinishSendKC_costUB]; omega

theorem shcrFinishSendKC_r64_le (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  rw [shcrFinishSendKC, shcrFinishSendKC_r64]; omega

theorem shcrFinishSendKC_queries_prim_le (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 12 := by
  change (shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc).queries primW primWS ≤ 12
  rw [shcrFinishSendKC, shcrFinishSendKC_queries]

set_option linter.unusedSimpArgs false in
theorem shcrFinishSendKC_size_le (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc).size ≤
      5000 + 20 * bits K_on + 10 * bits K_ro := by
  hs_size_simp; omega

set_option linter.unusedSimpArgs false in
theorem shcrFinishSendKC_litSize_le (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    compLitSize (shcrFinishSendKC K_on K_ro (Δ := Δ) st d ks sc) ≤ 2500 := by
  hs_lit_simp; omega

set_option linter.unusedSimpArgs false in
theorem shcrSendKC_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrSendKC S K_on K_ro opk (Δ := Δ) s x).cost ≤
      12300 + 3570 * K_on + 1030 * min K_on S.N_dh + 531 * K_ro := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  cases opk <;>
  · simp only [shcrSendKC, AuthCoreKArmsHs.shcrSendKC, sendGuardE,
      preCheckC_costUB, checkSigsC_costUB, shcrFinishSendKC_costUB, shcrFinC_costUB,
      bindV, letV, caseOptV, Comp.costUB_letC, isSomeE, buOpkB, buPqspkB, pdSid, pdBu,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scMk, scUpd,
      aNone, costUB_sampleBytes32, costUB_queryPrim,
      _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat, bits_1,
      Bool.false_eq_true, ite_true, ite_false, costUB_v, Comp.costUB, Expr.costUB]
    omega

theorem shcrSendKC_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrSendKC S K_on K_ro opk (Δ := Δ) s x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  suffices (shcrSendKC S K_on K_ro opk (Δ := Δ) s x).queries (fun _ => 0) (sampR64W rfl) = 0 by omega
  simp [shcrSendKC, AuthCoreKArmsHs.shcrSendKC, preCheckC, checkSigsC, shcrFinC,
    koskBundleOkC_r64, resolveSigPkC_r64, findHonestC_r64, shcrFinishSendKC_r64,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.sampleBytes32, Comp.queryPrim, Comp.queries]

theorem shcrSendKC_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrSendKC S K_on K_ro opk (Δ := Δ) s x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 20 + 10 * min K_on S.N_dh := by
  change (shcrSendKC S K_on K_ro opk (Δ := Δ) s x).queries primW primWS ≤ 20 + 10 * min K_on S.N_dh
  simp only [shcrSendKC, AuthCoreKArmsHs.shcrSendKC,
    preCheckC_queries, checkSigsC_queries, shcrFinishSendKC_queries, shcrFinC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.sampleBytes32, Comp.queryPrim,
    primW, primWS, Comp.queries]
  omega

set_option linter.unusedSimpArgs false in
theorem shcrSendKC_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrSendKC S K_on K_ro opk (Δ := Δ) s x).size ≤
      9000 + 20 * bits K_on + 10 * bits K_ro := by
  have hmin : bits (min K_on S.N_dh) ≤ bits K_on := hs_bits_mono (Nat.min_le_left _ _)
  cases opk <;> · hs_size_simp; omega

set_option linter.unusedSimpArgs false in
theorem shcrSendKC_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (shcrSendKC S K_on K_ro opk (Δ := Δ) s x) ≤ 3000 := by
  cases opk <;> · hs_lit_simp; omega

set_option linter.unusedSimpArgs false in
theorem shcrAcceptKB_cost_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptKB S K_on K_ro opk (Δ := Δ) s x).cost ≤
      16000 + 370 * K_on + 412 * min K_on S.N_dh + 531 * K_ro := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  cases opk <;>
  · simp only [shcrAcceptKB, AuthCoreKArmsHs.shcrAcceptKB,
      onBase_costUB, recvKB_true_costUB, recvKB_false_costUB,
      bindV, letV, caseOptV, eFind, Comp.costUB_letC, nat2Eq, natEq,
      stSpks, pmHdr, sbPqspkSk, sbPqspkPk, hdKemCt,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scMk, scUpd,
      costUB_queryPrim, _root_.SignalPqxdh.LegacyCosted.Ty.wd, PNat.val_ofNat,
      costUB_v, Comp.costUB, Expr.costUB]
    omega

theorem shcrAcceptKB_r64_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptKB S K_on K_ro opk (Δ := Δ) s x).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  suffices (shcrAcceptKB S K_on K_ro opk (Δ := Δ) s x).queries (fun _ => 0) (sampR64W rfl) = 0 by
    omega
  simp [shcrAcceptKB, AuthCoreKArmsHs.shcrAcceptKB, onBase, recvKB_r64,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, Comp.queries]

set_option linter.unusedSimpArgs false in
theorem shcrAcceptKB_queries_prim_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptKB S K_on K_ro opk (Δ := Δ) s x).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 22 + 4 * min K_on S.N_dh := by
  change (shcrAcceptKB S K_on K_ro opk (Δ := Δ) s x).queries primW primWS ≤ 22 + 4 * min K_on S.N_dh
  cases opk <;>
  · simp only [shcrAcceptKB, AuthCoreKArmsHs.shcrAcceptKB,
      onBase_queries, recvKB_true_queries, recvKB_false_queries,
      bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries]
    omega

set_option linter.unusedSimpArgs false in
theorem shcrAcceptKB_size_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptKB S K_on K_ro opk (Δ := Δ) s x).size ≤
      9000 + 20 * bits K_on + 10 * bits K_ro := by
  have hmin : bits (min K_on S.N_dh) ≤ bits K_on := hs_bits_mono (Nat.min_le_left _ _)
  cases opk <;> · hs_size_simp; omega

set_option linter.unusedSimpArgs false in
theorem shcrAcceptKB_litSize_le (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (shcrAcceptKB S K_on K_ro opk (Δ := Δ) s x) ≤ 3000 := by
  cases opk <;> · hs_lit_simp; omega

theorem shcrResumeKC_cost_le (K_on1 K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (shcrResumeKC K_on1 K_ro (Δ := Δ) sc d s).cost ≤
      10000 + 3970 * K_on1 + 531 * K_ro := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [shcrResumeKC, AuthCoreKArmsHs.shcrResumeKC, shcrFinishSendKC_costUB, shcrFinC_costUB,
    bindV, letV, Comp.costUB_letC, buPqspkB, pdSid, pdBu,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scMk, scUpd,
    costUB_sampleBytes32, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem shcrResumeKC_r64_le (K_on1 K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (shcrResumeKC K_on1 K_ro (Δ := Δ) sc d s).queries (fun _ => 0) (sampR64W rfl) ≤ 2 := by
  suffices (shcrResumeKC K_on1 K_ro (Δ := Δ) sc d s).queries (fun _ => 0) (sampR64W rfl) = 0 by
    omega
  simp [shcrResumeKC, AuthCoreKArmsHs.shcrResumeKC, shcrFinishSendKC_r64, shcrFinC,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.sampleBytes32, Comp.queries]

theorem shcrResumeKC_queries_prim_le (K_on1 K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (shcrResumeKC K_on1 K_ro (Δ := Δ) sc d s).queries
        primIfacePrimQueryWeight samplerZeroQueryWeight ≤ 14 := by
  change (shcrResumeKC K_on1 K_ro (Δ := Δ) sc d s).queries primW primWS ≤ 14
  simp only [shcrResumeKC, AuthCoreKArmsHs.shcrResumeKC, shcrFinishSendKC_queries, shcrFinC_queries,
    bindV, letV, Comp.queries_letC, Comp.sampleBytes32, primWS, Comp.queries]
  omega

set_option linter.unusedSimpArgs false in
theorem shcrResumeKC_size_le (K_on1 K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (shcrResumeKC K_on1 K_ro (Δ := Δ) sc d s).size ≤
      6000 + 20 * bits K_on1 + 10 * bits K_ro := by
  hs_size_simp; omega

set_option linter.unusedSimpArgs false in
theorem shcrResumeKC_litSize_le (K_on1 K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    compLitSize (shcrResumeKC K_on1 K_ro (Δ := Δ) sc d s) ≤ 3000 := by
  hs_lit_simp; omega

end HsBranchBounds

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKBranchCost
