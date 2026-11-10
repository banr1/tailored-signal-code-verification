/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK -- proof-setup: allow-public-import
public import Computational.Specifications.Pqxdh.Security.Headline -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.KindedDispatch
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget

/-!
# Per-Query-Kind Cost Bounds for `KeyIndCoreK`

Proves syntactic `cost`, `costAt`, and `queries` bounds for the shadow-indexed `KeyIndCoreK` and
`KemShCr` handlers, establishing logarithmic `.roQuery` step cost (`O(bits roCap)`) and clamped
online arm bounds (`shcrOnlineArmBudget`) for `KindedDispatch`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost

open OracleSpec OracleComp
open _root_.SignalPqxdh (Setup QueryBudget keyIndSpec KeyIndQuery)
open _root_.SignalPqxdh.Security (keyIndQueryKind)
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface
  pqAtomicSig pqAtomicOps pqPrimIface pqKeyIndCodec
  B PB drKeyT bits
)
open _root_.Computational.Proofs.ReductionDsl.KindedDispatch (
  DispatchesTo costAt_le_arm_cost_of_dispatchesTo
)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  TagLift tlPrimKeyInd embedTy finSidToNatExpr
  exprRename compRename mapExpr mapComp
  exprRename_cost compRename_cost mapComp_cost_eleven_mul_le
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  aop avlSearchB192C avlInsertAtPathC avlSearchResTy
  sampleDrKey96AtomicC samplePbytes32C
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost (
  avlSearchB192C_queries avlInsertAtPathC_queries samplePbytes32C_queries_zero
  sampleDrKey96AtomicC_cost_eq avlSearchB192C_cost_le avlInsertAtPathC_cost_le
)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT accQTy eAny eFind eMap eCaseOpt eCaseSum isSomeE litB
  letV bindV caseOptV v natEq nat2Eq nat3Eq
  keyIndStateTy shcrStTy
  stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb stRo stAdv stSecb
  stUpd stMk peMk peUpd peSecIKA0 peIkAPk peSecIKAsign peIkSignPk
  sbMk sbUpd sbSpkSk sbSpkPk sbSpkSig sbPqspkSk sbPqspkPk sbPqspkSig
  oeMk oeUpd oeOpkSk oeOpkPk oeConsumed
  hdMk hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt
  seMk seUpd seSid seHonestPeer sePeerIk sePeerSpk sePeerOpk sePeerPqspk
  seSpkHon seOpkHon sePqspkHon seEkASk seFresh seDrReal seDrRand seHdr seTested seRevealed
  reMk reUpd reSid reRespIk reSpk reOpk rePqspk reHdr reSenderHonest reDrReal reDrRand
  reTested reRevealed buMk buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig
  rs rNone rInitPrin rPk rCorr rBundle rHdr rInitUnfresh rAccFresh rDrKey rSpkSk
  findMV scBase scTB scTPk scTSk scCnt scIR scRR scSIdx scChosen scUpd scMk
  initGuardE initSidE shcrFinE isNoneRespE qK qJ qO qHdr qKJO optFst optSnd getDBytes
  buildSecretsE_cost optU32Eq_cost kyberCheckE_cost findHonestC_cost
  koskSenderOkC_cost honestPeerC_cost checkProvC_cost partnerC_cost recordRespC_cost
  acceptKeysC_cost preCheckC_cost checkSigsC_cost
  initPrinB_cost corruptB_cost genSpkB_cost genOpkB_cost
  testB_cost revealB_cost revealDhB_true_cost registerB_cost revealSpkB_cost
  onBase_cost shcrGenSpkB_cost tryPauseC_true_cost tryPauseC_false_cost shcrExtractC_cost
  initPrin1KeyB_cost_le
  cost_v cost_litB cost_eqU32 cost_u32OfNat cost_lenB cost_encEC cost_encKEM
  cost_sBytes32 cost_sRandom64 cost_sDrKey96
  cost_qX25519 cost_qX25519Base cost_qSigSign cost_qKemEncaps cost_qKemDecaps
  bits_0 bits_1 bits_32
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  KeyIndCoreFuels keyIndCoreFuels roAvlTy roListAtomicTy shcrKindStTy
  coreGetRoE coreSetRoRespC shcrGetRoE shcrSetRoRespC
  initFinishPreRoC initFinishPostRoC shcrInitMidTy shcrAccMidTy
  roShadowQueryC shcrInitiatePreRoC shcrInitiatePostRoC
  coreAcceptPreRoC shcrAcceptPreRoC shcrAcceptPostRoC
  shcrResumePreRoC shcrResumePostRoC
  shcrInitPrin1KeyLeg shcrInitPrin2KeyLeg shcrCorruptLeg
  shcrGenSpkLeg shcrActiveGenSpkLeg shcrGenOpkLeg
  shcrTestLeg shcrRevDhLeg shcrRevSessLeg shcrRegKeyLeg shcrRevSpkLeg
  shcrChDoneLeg shcrExtractLeg
  atomicRNoneE finPairToNatE finTripleToNatE initPayToNatE accPayToNatE
  wkRen1 dispatchKeyIndQ ren1 ren2 ren3 ren4 ren5 ren6 wkTop3
  runAt2 runAt3 runAt4 runAt5 runAt6
  shcrRoListAtomicE shcrLiftLegArmK shcrRoArmK
  shcrInitArmPostK shcrInitArmPreK shcrAccArmPostK
  shcrKindHandlePreC shcrKindHandlePostC
  shcrKindChDoneC shcrKindResumeC shcrKindFinishC
)

theorem roShadowQueryC_queries_zero {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T}
    {A : _root_.Computational.Proofs.SignalPqxdh.AtomicLift.AtomicIface T}
    (tl : TagLift I₁ A) (w : A.toIface.Tag → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowQueryC tl cap roListE tblE secE).queries w (fun _ => 0) = 0 := by
  simp [roShadowQueryC, sampleDrKey96AtomicC,
    samplePbytes32C_queries_zero (I := A.toIface) rfl w (fun _ => 0) (fun _ => rfl),
    avlSearchB192C_queries, avlInsertAtPathC_queries, Comp.queries]

theorem roShadowQueryC_cost_le {ι : Type} {T : OracleSpec ι}
    {I₁ : _root_.ReductionDsl.Iface pqSig T}
    {A : _root_.Computational.Proofs.SignalPqxdh.AtomicLift.AtomicIface T}
    (tl : TagLift I₁ A) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowQueryC tl cap roListE tblE secE).cost ≤
      4420 * bits cap + 1290 + roListE.cost + tblE.cost + 2 * secE.cost := by
  have hSmpCost := sampleDrKey96AtomicC_cost_eq (I := A.toIface) rfl
    (Γ := avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
          .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ)
  have hSrch := avlSearchB192C_cost_le (I := A.toIface) cap
    (Γ := .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ)
    (V := drKeyT (ℓ := 0) (Pt := Empty)) (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))
  have hIns := avlInsertAtPathC_cost_le (I := A.toIface) cap
    (Γ := drKeyT (ℓ := 0) (Pt := Empty) ::
          avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)) ::
          .prod roListAtomicTy (.prod roAvlTy (.prod (PB 192) (B 192))) :: Γ)
    (.fst (.snd .v2)) (.snd .v1) (.snd (.snd (.snd .v2))) .v0
  simp only [roShadowQueryC, aop, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost,
    PNat.val_ofNat] at hSrch hIns ⊢
  norm_num [Nat.max_def]
  split <;> omega

theorem shcrInitiatePreRoC_cost_le (S : Setup) (K : ℕ) (opk : Bool) :
    (shcrInitiatePreRoC S K opk).cost ≤ 8600 + 860 * min K S.N_dh + 260 * K := by
  cases opk <;>
    simp only [shcrInitiatePreRoC, initFinishPreRoC, initGuardE, initSidE,
      letV, bindV, caseOptV, eCaseOpt, optSnd, getDBytes,
      preCheckC_cost, checkSigsC_cost, buildSecretsE_cost,
      isSomeE, buOpkB, buPqspkB, buSpkB, buIkB, peSecIKA0, rNone,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
      cost_sBytes32, cost_qKemEncaps, cost_qX25519Base, cost_qX25519,
      cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil,
      cost_litB, bits_1, Bool.false_eq_true, ↓reduceIte] <;>
    omega

theorem shcrInitiatePostRoC_cost_le (S : Setup) (K : ℕ) :
    (shcrInitiatePostRoC S K).cost ≤
      5600 + 1050 * min K S.N_dh + 7362 * min K S.N_sess_tot + 3200 * K := by
  simp only [shcrInitiatePostRoC, initFinishPostRoC, letV, bindV, caseOptV, findMV,
    honestPeerC_cost, checkProvC_cost, partnerC_cost, findHonestC_cost,
    peIkAPk, buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
    optFst, optSnd, eCaseOpt, isSomeE, hdMk, seMk, seUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
    seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seHdr, seTested, seRevealed,
    reDrRand, rs, rInitUnfresh, rHdr, stUpd, stMk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    shcrFinE, scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
    cost_sDrKey96, cost_v, Comp.cost, Expr.cost, bits_1]
  omega

theorem coreAcceptPreRoC_cost_le (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy)
    (x : Var Γ₂ accQTy) :
    (coreAcceptPreRoC (Δ := Δ) S K opk st x).cost ≤ 13500 + 206 * min K S.N_dh + 400 * K := by
  have hMax1 : ∀ n : ℕ, max (n + 1) 1 = n + 1 := fun _ => Nat.max_eq_left (Nat.le_add_left 1 _)
  cases opk <;>
    simp only [coreAcceptPreRoC, letV, bindV, caseOptV, eAny, eFind, eMap,
      natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost,
      koskSenderOkC_cost, acceptKeysC_cost, buildSecretsE_cost,
      qK, qJ, qO, qHdr, qKJO, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
      peSecIKA0, sbSpkSk, sbPqspkSk, oeOpkSk, oeOpkPk, oeConsumed, oeUpd, oeMk,
      stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps,
      stUsedO, stUsedN, stKyb, stRo, stAdv,
      cost_eqU32, cost_u32OfNat, cost_lenB, cost_qKemDecaps, cost_qX25519,
      cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_32, hMax1,
      Bool.false_eq_true, ↓reduceIte] <;>
    omega

theorem shcrAcceptPreRoC_cost_le (S : Setup) (K : ℕ) (opk : Bool) :
    (shcrAcceptPreRoC S K opk).cost ≤ 13600 + 206 * min K S.N_dh + 400 * K := by
  have hCore := coreAcceptPreRoC_cost_le S K opk
    (Γ₁ := [keyIndStateTy, shcrStTy, accQTy])
    (Γ₂ := [shcrStTy, accQTy])
    (Δ := [keyIndStateTy, shcrStTy, accQTy])
    .zero (.succ .zero)
  simp only [shcrAcceptPreRoC, letV, scBase, cost_v, Comp.cost, Expr.cost] at hCore ⊢
  omega

theorem shcrAcceptPostRoC_cost_le (S : Setup) (K : ℕ) (opk : Bool) :
    (shcrAcceptPostRoC S K opk).cost ≤ 5800 + 7774 * min K S.N_dh + 50 * K := by
  cases opk <;>
    simp only [shcrAcceptPostRoC, letV, bindV, caseOptV, eFind, eCaseOpt,
      nat2Eq, natEq, findHonestC_cost, recordRespC_cost, isSomeE, isNoneRespE, eCaseSum,
      qK, qJ, qO, qKJO, qHdr, hdIkAPk, hdKemCt, peIkAPk, sbSpkPk, sbPqspkPk, sbPqspkSk, reMk,
      rDrKey, rAccFresh, stUpd, stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
      cost_qKemDecaps, cost_v, Comp.cost, Expr.cost, bits_0,
      Bool.false_eq_true, ↓reduceIte] <;>
    omega

theorem shcrResumePreRoC_cost_le :
    shcrResumePreRoC.cost ≤ 2200 := by
  simp only [shcrResumePreRoC, initFinishPreRoC, letV, bindV, eCaseOpt, optSnd, getDBytes,
    buildSecretsE_cost, buOpkB, buSpkB, buIkB, peSecIKA0,
    cost_sBytes32, cost_qX25519Base, cost_qX25519,
    cost_litB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  omega

theorem shcrResumePostRoC_cost_le (S : Setup) (K : ℕ) :
    (shcrResumePostRoC S K).cost ≤
      5800 + 1050 * min K S.N_dh + 7362 * min K S.N_sess_tot + 3200 * K := by
  simp only [shcrResumePostRoC, initFinishPostRoC, letV, bindV, caseOptV, findMV,
    honestPeerC_cost, checkProvC_cost, partnerC_cost, findHonestC_cost,
    peIkAPk, buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
    optFst, optSnd, eCaseOpt, isSomeE, hdMk, seMk, seUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
    seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seHdr, seTested, seRevealed,
    reDrRand, rs, rInitUnfresh, rHdr, stUpd, stMk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    shcrFinE, scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
    cost_sDrKey96, cost_v, Comp.cost, Expr.cost, bits_1]
  omega

theorem shcrActiveGenSpkLeg_cost_le (S : Setup) (K : ℕ) :
    (shcrActiveGenSpkLeg S K).cost ≤ 8900 + 50 * K := by
  simp only [shcrActiveGenSpkLeg, caseOptV, bindV, onBase_cost, genSpkB_cost,
    eAny, eFind, nat2Eq, natEq,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
    stKyb, stRo, stAdv, sbMk, buMk, peIkAPk, peSecIKAsign, rNone, rBundle,
    cost_sBytes32, cost_qX25519Base, cost_sRandom64, cost_qSigSign,
    cost_encEC, cost_encKEM, cost_u32OfNat,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  omega

section AtomicArmHelpers

private theorem runAt2_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (c : Comp pqAtomicOps I [A, B] R) :
    (runAt2 aE bE c).cost = c.cost + aE.cost + bE.cost + 4 := by
  simp only [runAt2, Comp.cost, exprRename_cost, compRename_cost]
  omega

private theorem runAt3_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (m : Comp pqAtomicOps I [A, B, C] R) :
    (runAt3 aE bE cE m).cost = m.cost + aE.cost + bE.cost + cE.cost + 6 := by
  simp only [runAt3, Comp.cost, exprRename_cost, compRename_cost]
  omega

private theorem runAt4_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (cE : Expr pqAtomicOps Γ C) (dE : Expr pqAtomicOps Γ D)
    (m : Comp pqAtomicOps I [A, B, C, D] R) :
    (runAt4 aE bE cE dE m).cost = m.cost + aE.cost + bE.cost + cE.cost + dE.cost + 8 := by
  simp only [runAt4, Comp.cost, exprRename_cost, compRename_cost]
  omega

private theorem runAt5_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B)
    (cE : Expr pqAtomicOps Γ C) (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E)
    (m : Comp pqAtomicOps I [A, B, C, D, E] R) :
    (runAt5 aE bE cE dE eE m).cost =
      m.cost + aE.cost + bE.cost + cE.cost + dE.cost + eE.cost + 10 := by
  simp only [runAt5, Comp.cost, exprRename_cost, compRename_cost]
  omega

private theorem runAt6_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B C D E F R : Ty pqAtomicSig}
    (aE : Expr pqAtomicOps Γ A) (bE : Expr pqAtomicOps Γ B) (cE : Expr pqAtomicOps Γ C)
    (dE : Expr pqAtomicOps Γ D) (eE : Expr pqAtomicOps Γ E) (fE : Expr pqAtomicOps Γ F)
    (m : Comp pqAtomicOps I [A, B, C, D, E, F] R) :
    (runAt6 aE bE cE dE eE fE m).cost =
      m.cost + aE.cost + bE.cost + cE.cost + dE.cost + eE.cost + fE.cost + 12 := by
  simp only [runAt6, Comp.cost, exprRename_cost, compRename_cost]
  omega

private theorem wrapInl_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {A B : Ty pqAtomicSig}
    (c : Comp pqAtomicOps I Γ A) :
    (Comp.bind c (.ret (.inl .v0 : Expr pqAtomicOps (A :: Γ) (.sum A B)))).cost = c.cost + 4 := by
  simp only [Comp.cost, Expr.cost, Expr.v0]

private theorem shcrRoListAtomicE_cost_le {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ (embedTy shcrStTy)) :
    (shcrRoListAtomicE sE).cost ≤ sE.cost + 20 := by
  simp only [shcrRoListAtomicE, shcrGetRoE, stRo, scBase, exprRename_cost, mapExpr, Expr.cost]
  omega

private theorem shcrSetRoRespC_cost_le :
    shcrSetRoRespC.cost ≤ 200 := by
  decide

private theorem shcrLiftLegArmK_cost_le_of (S : Setup) (K_on : ℕ)
    {A : Ty pqAtomicSig} {P : Ty pqSig}
    (payE : Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy P))
    (leg : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [shcrStTy, P]
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.SCS)
    (hPay : payE.cost ≤ 40)
    (hLeg : leg.cost ≤ 8900 + 350 * K_on) :
    (shcrLiftLegArmK S payE leg).cost ≤ 19000 + 750 * K_on := by
  have hMap := mapComp_cost_eleven_mul_le tlPrimKeyInd leg
  simp only [shcrLiftLegArmK, runAt2_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2]
  omega

private theorem finSidToNatExpr_v0_cost_le (S : Setup) {Γ : List (Ty pqAtomicSig)} :
    (finSidToNatExpr S (.v0 : Expr pqAtomicOps (_root_.ReductionDsl.sidT S :: Γ) _)).cost ≤ 40 := by
  simp only [finSidToNatExpr, Expr.cost, Expr.v0,
    pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost]
  norm_num [Nat.max_def]

private theorem shcrInitArmPostK_cost_le (S : Setup) (K_on capRo N_s : ℕ) (opk : Bool) :
    (shcrInitArmPostK S K_on capRo N_s opk).cost ≤
      29800 + 4000 * min K_on S.N_dh + 15400 * min K_on S.N_sess_tot + 7250 * K_on +
        (4420 * bits capRo + 1400) := by
  have hPre := shcrInitiatePreRoC_cost_le S K_on opk
  have hPreMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrInitiatePreRoC S K_on opk)
  have hPost := shcrInitiatePostRoC_cost_le S K_on
  have hPostMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrInitiatePostRoC S K_on)
  have hRo := roShadowQueryC_cost_le tlPrimKeyInd capRo
    (Γ := embedTy shcrInitMidTy ::
          embedTy (.sum _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.SCS shcrInitMidTy) ::
          .prod (.base (.fin S.N_id))
            (.prod (.base (.fin N_s)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
          shcrKindStTy :: (pqKeyIndCodec S).Q :: [])
    (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)
  have hRoList := shcrRoListAtomicE_cost_le
    (Γ := embedTy shcrInitMidTy ::
          embedTy (.sum _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.SCS shcrInitMidTy) ::
          .prod (.base (.fin S.N_id))
            (.prod (.base (.fin N_s)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
          shcrKindStTy :: (pqKeyIndCodec S).Q :: [])
    (.fst .v3)
  simp only [shcrInitArmPostK, initPayToNatE, aop, runAt2_cost, runAt4_cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v3, Expr.v4,
    pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost] at hRo hRoList ⊢
  omega

private theorem shcrInitArmPreK_cost_le (S : Setup) (K_on capRo N_s : ℕ) (opk : Bool) :
    (shcrInitArmPreK S K_on capRo N_s opk).cost ≤
      37900 + 5750 * min K_on S.N_dh + 15400 * min K_on S.N_sess_tot + 7800 * K_on +
        (4420 * bits capRo + 1400) := by
  let tp := _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.tryPauseC S K_on opk
    (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initQTy])
    (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initQTy])
    (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initQTy]) .zero .zero
  have hTp : tp.cost = 3843 + min K_on S.N_dh * 824 + K_on * 257 := by
    cases opk
    · exact tryPauseC_false_cost S K_on .zero .zero
    · exact tryPauseC_true_cost S K_on .zero .zero
  have hTpMap := mapComp_cost_eleven_mul_le tlPrimKeyInd tp
  have hPost := shcrInitArmPostK_cost_le S K_on capRo N_s opk
  dsimp only [tp] at hTp hTpMap
  simp only [shcrInitArmPreK, initPayToNatE, aop, runAt2_cost, compRename_cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v3,
    pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost]
  omega

private theorem shcrAccArmPostK_cost_le (S : Setup) (K_on capRo N_o : ℕ) (opk : Bool) :
    (shcrAccArmPostK S K_on capRo N_o opk).cost ≤
      40700 + 16700 * min K_on S.N_dh + 960 * K_on +
        (4420 * bits capRo + 1400) := by
  have hPre := shcrAcceptPreRoC_cost_le S K_on opk
  have hPreMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrAcceptPreRoC S K_on opk)
  have hPost := shcrAcceptPostRoC_cost_le S K_on opk
  have hPostMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrAcceptPostRoC S K_on opk)
  have hRo := roShadowQueryC_cost_le tlPrimKeyInd capRo
    (Γ := embedTy shcrAccMidTy ::
          embedTy (.opt shcrAccMidTy) ::
          .prod (.base (.fin S.N_id))
            (.prod (.base (.fin S.N_recv))
              (.prod (.base (.fin N_o)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
          shcrKindStTy :: (pqKeyIndCodec S).Q :: [])
    (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)
  have hRoList := shcrRoListAtomicE_cost_le
    (Γ := embedTy shcrAccMidTy ::
          embedTy (.opt shcrAccMidTy) ::
          .prod (.base (.fin S.N_id))
            (.prod (.base (.fin S.N_recv))
              (.prod (.base (.fin N_o)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
          shcrKindStTy :: (pqKeyIndCodec S).Q :: [])
    (.fst .v3)
  simp only [shcrAccArmPostK, accPayToNatE, atomicRNoneE, aop, runAt2_cost, runAt5_cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    pqAtomicOps, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.AtomicPureOp.cost] at hRo hRoList ⊢
  omega

theorem dispatchKeyIndQ_ro_costAt_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (S : Setup) {A R : Ty pqAtomicSig}
    (st : A.denote) (sec : List UInt8)
    (onInitPrin  : Comp pqAtomicOps I (.base (.fin S.N_id) :: [A, (pqKeyIndCodec S).Q]) R)
    (onCorrupt   : Comp pqAtomicOps I (.base (.fin S.N_id) :: [A, (pqKeyIndCodec S).Q]) R)
    (onGenSpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: [A, (pqKeyIndCodec S).Q]) R)
    (onGenOpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))) :: [A, (pqKeyIndCodec S).Q]) R)
    (onInitOpk   : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
          [A, (pqKeyIndCodec S).Q]) R)
    (onInitNoOpk : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_no_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
          [A, (pqKeyIndCodec S).Q]) R)
    (onAccOpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
          [A, (pqKeyIndCodec S).Q]) R)
    (onAccNoOpk  : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_no_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
          [A, (pqKeyIndCodec S).Q]) R)
    (onTest      : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S ::
      [A, (pqKeyIndCodec S).Q]) R)
    (onRo        : Comp pqAtomicOps I (PB 192 :: [A, (pqKeyIndCodec S).Q]) R)
    (onRevDh     : Comp pqAtomicOps I (.unit :: [A, (pqKeyIndCodec S).Q]) R)
    (onRevSess   : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S ::
      [A, (pqKeyIndCodec S).Q]) R)
    (onRegKey    : Comp pqAtomicOps I (PB 32 :: [A, (pqKeyIndCodec S).Q]) R)
    (onRevSpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: [A, (pqKeyIndCodec S).Q]) R) :
    (dispatchKeyIndQ S .v1 onInitPrin onCorrupt onGenSpk onGenOpk onInitOpk onInitNoOpk
      onAccOpk onAccNoOpk onTest onRo onRevDh onRevSess onRegKey onRevSpk).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc (.roQuery sec)) .nil)) ≤
      onRo.cost + 20 := by
  have hDisp : DispatchesTo
      (dispatchKeyIndQ S .v1 onInitPrin onCorrupt onGenSpk onGenOpk onInitOpk onInitNoOpk
        onAccOpk onAccNoOpk onTest onRo onRevDh onRevSess onRegKey onRevSpk)
      (.cons st (.cons ((pqKeyIndCodec S).qenc (.roQuery sec)) .nil))
      20 _ _ :=
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inr rfl <|
    DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
  have hLe := costAt_le_arm_cost_of_dispatchesTo hDisp (Nat.le_refl 20)
  simpa only [compRename_cost] using hLe

theorem dispatchKeyIndQ_online_costAt_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (S : Setup) {A R : Ty pqAtomicSig} (B : ℕ)
    (st : A.denote) (q : KeyIndQuery S)
    (hq : keyIndQueryKind q = ⟨0, by decide⟩)
    (onInitPrin  : Comp pqAtomicOps I (.base (.fin S.N_id) :: [A, (pqKeyIndCodec S).Q]) R)
    (onCorrupt   : Comp pqAtomicOps I (.base (.fin S.N_id) :: [A, (pqKeyIndCodec S).Q]) R)
    (onGenSpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: [A, (pqKeyIndCodec S).Q]) R)
    (onGenOpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))) :: [A, (pqKeyIndCodec S).Q]) R)
    (onInitOpk   : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
          [A, (pqKeyIndCodec S).Q]) R)
    (onInitNoOpk : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_send_no_opk)) (_root_.ReductionDsl.bundleT (ℓ := 0) (Pt := Empty))) ::
          [A, (pqKeyIndCodec S).Q]) R)
    (onAccOpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
          [A, (pqKeyIndCodec S).Q]) R)
    (onAccNoOpk  : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin S.N_no_opk)) (_root_.ReductionDsl.hdrT (ℓ := 0) (Pt := Empty)))) ::
          [A, (pqKeyIndCodec S).Q]) R)
    (onTest      : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S ::
      [A, (pqKeyIndCodec S).Q]) R)
    (onRo        : Comp pqAtomicOps I (PB 192 :: [A, (pqKeyIndCodec S).Q]) R)
    (onRevDh     : Comp pqAtomicOps I (.unit :: [A, (pqKeyIndCodec S).Q]) R)
    (onRevSess   : Comp pqAtomicOps I (_root_.ReductionDsl.sidT (ℓ := 0) (Pt := Empty) S ::
      [A, (pqKeyIndCodec S).Q]) R)
    (onRegKey    : Comp pqAtomicOps I (PB 32 :: [A, (pqKeyIndCodec S).Q]) R)
    (onRevSpk    : Comp pqAtomicOps I
      (.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)) :: [A, (pqKeyIndCodec S).Q]) R)
    (h1  : onInitPrin.cost ≤ B)
    (h2  : onCorrupt.cost ≤ B)
    (h3  : onGenSpk.cost ≤ B)
    (h4  : onGenOpk.cost ≤ B)
    (h5  : onInitOpk.cost ≤ B)
    (h6  : onInitNoOpk.cost ≤ B)
    (h7  : onAccOpk.cost ≤ B)
    (h8  : onAccNoOpk.cost ≤ B)
    (h9  : onTest.cost ≤ B)
    (h11 : onRevDh.cost ≤ B)
    (h12 : onRevSess.cost ≤ B)
    (h13 : onRegKey.cost ≤ B)
    (h14 : onRevSpk.cost ≤ B) :
    (dispatchKeyIndQ S .v1 onInitPrin onCorrupt onGenSpk onGenOpk onInitOpk onInitNoOpk
      onAccOpk onAccNoOpk onTest onRo onRevDh onRevSess onRegKey onRevSpk).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc q) .nil)) ≤
      B + 26 := by
  let prog := dispatchKeyIndQ S .v1 onInitPrin onCorrupt onGenSpk onGenOpk onInitOpk onInitNoOpk
    onAccOpk onAccNoOpk onTest onRo onRevDh onRevSess onRegKey onRevSpk
  cases q with
  | initPrin u =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.initPrin u)) .nil)) 2 _ _ :=
      DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 2 ≤ 26)
    exact Nat.le_trans hL (Nat.add_le_add_right h1 26)
  | corruptIK u =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.corruptIK u)) .nil)) 4 _ _ :=
      DispatchesTo.caseSum_inr rfl (DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _))
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 4 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h2 26)
  | genSPK u j =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.genSPK u j)) .nil)) 6 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 6 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h3 26)
  | genOPK u j o =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.genOPK u j o)) .nil)) 8 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 8 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h4 26)
  | initiateOPK u i b =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.initiateOPK u i b)) .nil)) 10 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 10 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h5 26)
  | initiateNoOPK u i b =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.initiateNoOPK u i b)) .nil)) 12 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 12 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h6 26)
  | acceptOPK k j o h =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.acceptOPK k j o h)) .nil)) 14 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 14 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h7 26)
  | acceptNoOPK k j l h =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.acceptNoOPK k j l h)) .nil)) 16 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 16 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h8 26)
  | testSession sid =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.testSession sid)) .nil)) 18 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 18 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h9 26)
  | roQuery sec =>
    simp [keyIndQueryKind] at hq
  | revealDhSecrets =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc .revealDhSecrets) .nil)) 22 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 22 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h11 26)
  | revealSessionKey sid =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.revealSessionKey sid)) .nil)) 24 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 24 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h12 26)
  | registerKey sk =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.registerKey sk)) .nil)) 26 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inl rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 26 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h13 26)
  | revealSpkSk u j =>
    have hD : DispatchesTo prog (.cons st (.cons ((pqKeyIndCodec S).qenc (.revealSpkSk u j)) .nil)) 26 _ _ :=
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl <| DispatchesTo.caseSum_inr rfl <|
      DispatchesTo.caseSum_inr rfl (DispatchesTo.refl _ _)
    have hL := costAt_le_arm_cost_of_dispatchesTo hD (by omega : 26 ≤ 26)
    simp only [compRename_cost] at hL
    exact Nat.le_trans hL (Nat.add_le_add_right h14 26)

end AtomicArmHelpers

theorem shcrRoArmK_cost_le (S : Setup) (capRo : ℕ) :
    (shcrRoArmK S capRo).cost ≤ 4420 * bits capRo + 1760 := by
  have hRo := roShadowQueryC_cost_le tlPrimKeyInd capRo
    (Γ := [PB 192, shcrKindStTy, (pqKeyIndCodec S).Q])
    (shcrRoListAtomicE (.fst .v1)) (.snd .v1) .v0
  have hRoList := shcrRoListAtomicE_cost_le
    (Γ := [PB 192, shcrKindStTy, (pqKeyIndCodec S).Q]) (.fst .v1)
  have hSet := shcrSetRoRespC_cost_le
  have hSetMap := mapComp_cost_eleven_mul_le tlPrimKeyInd shcrSetRoRespC
  simp only [shcrRoArmK, runAt3_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hRo hRoList ⊢
  omega

/-- Pointwise `costAt` bound for `shcrKindHandlePreC` on offline `.roQuery` inputs. -/
theorem shcrKindHandlePreC_costAt_ro_le
    (oneKey : Bool) (S : Setup) (K_on capRo : ℕ)
    (st : shcrKindStTy.denote) (sec : List UInt8) :
    (shcrKindHandlePreC oneKey S K_on capRo).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc (.roQuery sec)) .nil)) +
      (pqKeyIndCodec S).codecCost ≤
      4420 * bits capRo + 1850 := by
  have hD := dispatchKeyIndQ_ro_costAt_le S st sec
    (.bind (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0)
      (if oneKey then shcrInitPrin1KeyLeg K_on else shcrInitPrin2KeyLeg K_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg K_on))
      (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0)
      (if oneKey then shcrActiveGenSpkLeg S K_on else shcrGenSpkLeg S K_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat))
      (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg K_on)) (.ret (.inl .v0)))
    (shcrInitArmPreK S K_on capRo S.N_send_opk true)
    (shcrInitArmPreK S K_on capRo S.N_send_no_opk false)
    (.bind (shcrAccArmPostK S K_on capRo S.N_opk true) (.ret (.inl .v0)))
    (.bind (shcrAccArmPostK S K_on capRo S.N_no_opk false) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrTestLeg K_on)) (.ret (.inl .v0)))
    (.bind (shcrRoArmK S capRo) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg K_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrRevSessLeg K_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg)
      (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg K_on)) (.ret (.inl .v0)))
  have hRo := shcrRoArmK_cost_le S capRo
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  refine Nat.le_trans (Nat.add_le_add_right hD _) ?_
  simp only [wrapInl_cost]
  omega

/-- Pointwise `costAt` bound for `shcrKindHandlePostC` on offline `.roQuery` inputs. -/
theorem shcrKindHandlePostC_costAt_ro_le
    (oneKey : Bool) (S : Setup) (K_on capRo : ℕ)
    (st : shcrKindStTy.denote) (sec : List UInt8) :
    (shcrKindHandlePostC oneKey S K_on capRo).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc (.roQuery sec)) .nil)) +
      (pqKeyIndCodec S).codecCost ≤
      4420 * bits capRo + 1850 := by
  have hD := dispatchKeyIndQ_ro_costAt_le S st sec
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0)
      (if oneKey then shcrInitPrin1KeyLeg K_on else shcrInitPrin2KeyLeg K_on))
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg K_on))
    (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0)
      (if oneKey then shcrActiveGenSpkLeg S K_on else shcrGenSpkLeg S K_on))
    (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat))
      (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg K_on))
    (shcrInitArmPostK S K_on capRo S.N_send_opk true)
    (shcrInitArmPostK S K_on capRo S.N_send_no_opk false)
    (shcrAccArmPostK S K_on capRo S.N_opk true)
    (shcrAccArmPostK S K_on capRo S.N_no_opk false)
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrTestLeg K_on))
    (shcrRoArmK S capRo)
    (shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg K_on))
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrRevSessLeg K_on))
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg)
    (shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg K_on))
  have hRo := shcrRoArmK_cost_le S capRo
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  refine Nat.le_trans (Nat.add_le_add_right hD _) ?_
  omega

/-- Per-step `costAt` budget for online (`kind 0`) arms at clamped fuels `f`. -/
@[expose] def shcrOnlineArmBudget (f : KeyIndCoreFuels) : ℕ :=
  42000 + 8000 * f.M_on + 16700 * f.M_dh + 15400 * f.M_sess + (4420 * bits f.roCap + 1850)

private theorem nonSessionLegs_cost_le (oneKey : Bool) (S : Setup) (K : ℕ) :
    (if oneKey then shcrInitPrin1KeyLeg K else shcrInitPrin2KeyLeg K).cost ≤ 8900 + 350 * K ∧
    (shcrCorruptLeg K).cost ≤ 8900 + 350 * K ∧
    (if oneKey then shcrActiveGenSpkLeg S K else shcrGenSpkLeg S K).cost ≤ 8900 + 350 * K ∧
    (shcrGenOpkLeg K).cost ≤ 8900 + 350 * K ∧
    (shcrTestLeg K).cost ≤ 8900 + 350 * K ∧
    (shcrRevDhLeg K).cost ≤ 8900 + 350 * K ∧
    (shcrRevSessLeg K).cost ≤ 8900 + 350 * K ∧
    shcrRegKeyLeg.cost ≤ 8900 + 350 * K ∧
    (shcrRevSpkLeg K).cost ≤ 8900 + 350 * K := by
  have h1k := initPrin1KeyB_cost_le K
    (Γ₁ := [keyIndStateTy, shcrStTy, .nat])
    (Γ₂ := [keyIndStateTy, shcrStTy, .nat])
    (Δ := [keyIndStateTy, shcrStTy, .nat])
    .zero (.succ (.succ .zero))
  have hGenAct := shcrActiveGenSpkLeg_cost_le S K
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases oneKey <;> simp only [shcrInitPrin1KeyLeg, shcrInitPrin2KeyLeg,
      onBase_cost, initPrinB_cost, ↓reduceIte, Bool.false_eq_true] at h1k ⊢ <;> omega
  · simp only [shcrCorruptLeg, onBase_cost, corruptB_cost]; omega
  · cases oneKey <;> simp only [shcrGenSpkLeg, shcrGenSpkB_cost, ↓reduceIte, Bool.false_eq_true] <;> omega
  · simp only [shcrGenOpkLeg, onBase_cost, genOpkB_cost]; omega
  · simp only [shcrTestLeg, onBase_cost, testB_cost]; omega
  · simp only [shcrRevDhLeg, onBase_cost, revealDhB_true_cost]; omega
  · simp only [shcrRevSessLeg, onBase_cost, revealB_cost]; omega
  · simp only [shcrRegKeyLeg, onBase_cost, registerB_cost]; omega
  · simp only [shcrRevSpkLeg, onBase_cost, revealSpkB_cost]; omega

/-- Pointwise `costAt` bound for `shcrKindHandlePreC` on online (`kind 0`) queries. -/
theorem shcrKindHandlePreC_costAt_online_le
    (oneKey : Bool) (S : Setup) (b : QueryBudget)
    (st : shcrKindStTy.denote) (q : KeyIndQuery S)
    (hq : keyIndQueryKind q = ⟨0, by decide⟩) :
    let f := keyIndCoreFuels S b
    (shcrKindHandlePreC oneKey S f.M_on f.roCap).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc q) .nil)) +
      (pqKeyIndCodec S).codecCost ≤
      shcrOnlineArmBudget f := by
  intro f
  have hMdh : min f.M_on S.N_dh = f.M_dh := rfl
  have hMsess : min f.M_on S.N_sess_tot = f.M_sess := rfl
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  rcases nonSessionLegs_cost_le oneKey S f.M_on with
    ⟨hL1, hL2, hL3, hL4, hL9, hL11, hL12, hL13, hL14⟩
  have hSid := finSidToNatExpr_v0_cost_le S (Γ := [shcrKindStTy, (pqKeyIndCodec S).Q])
  have hPayFin1 : (aop (.finVal S.N_id)
      (.v0 : Expr pqAtomicOps [.base (.fin S.N_id), shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
      _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayPair : (finPairToNatE S.N_id S.N_recv
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)),
        shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [finPairToNatE, aop, Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
      _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayTriple : (finTripleToNatE S.N_id S.N_recv S.N_opk
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))),
        shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [finTripleToNatE, aop, Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
      _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayUnit : (.unit : Expr pqAtomicOps [.unit, shcrKindStTy, (pqKeyIndCodec S).Q] .unit).cost ≤ 40 := by
    simp [Expr.cost]
  have hPayV0 : (.v0 : Expr pqAtomicOps [PB 32, shcrKindStTy, (pqKeyIndCodec S).Q] (PB 32)).cost ≤ 40 := by
    simp [Expr.cost, Expr.v0]
  have hA1  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayFin1 hL1
  have hA2  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayFin1 hL2
  have hA3  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayPair hL3
  have hA4  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayTriple hL4
  have hA5  := shcrInitArmPreK_cost_le S f.M_on f.roCap S.N_send_opk true
  have hA6  := shcrInitArmPreK_cost_le S f.M_on f.roCap S.N_send_no_opk false
  have hA7  := shcrAccArmPostK_cost_le S f.M_on f.roCap S.N_opk true
  have hA8  := shcrAccArmPostK_cost_le S f.M_on f.roCap S.N_no_opk false
  have hA9  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hSid hL9
  have hA11 := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayUnit hL11
  have hA12 := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hSid hL12
  have hA13 := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayV0 hL13
  have hA14 := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayPair hL14
  rw [hMdh] at hA5 hA6 hA7 hA8
  rw [hMsess] at hA5 hA6
  let B := shcrOnlineArmBudget f - 90
  have hD := dispatchKeyIndQ_online_costAt_le S B st q hq
    (.bind (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0)
      (if oneKey then shcrInitPrin1KeyLeg f.M_on else shcrInitPrin2KeyLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg f.M_on))
      (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0)
      (if oneKey then shcrActiveGenSpkLeg S f.M_on else shcrGenSpkLeg S f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat))
      (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg f.M_on)) (.ret (.inl .v0)))
    (shcrInitArmPreK S f.M_on f.roCap S.N_send_opk true)
    (shcrInitArmPreK S f.M_on f.roCap S.N_send_no_opk false)
    (.bind (shcrAccArmPostK S f.M_on f.roCap S.N_opk true) (.ret (.inl .v0)))
    (.bind (shcrAccArmPostK S f.M_on f.roCap S.N_no_opk false) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrTestLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrRoArmK S f.roCap) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrRevSessLeg f.M_on)) (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg)
      (.ret (.inl .v0)))
    (.bind (shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg f.M_on)) (.ret (.inl .v0)))
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
    (by simp only [wrapInl_cost, B, shcrOnlineArmBudget]; omega)
  refine Nat.le_trans (Nat.add_le_add_right hD _) ?_
  simp only [B, shcrOnlineArmBudget]
  omega

/-- Pointwise `costAt` bound for `shcrKindHandlePostC` on online (`kind 0`) queries. -/
theorem shcrKindHandlePostC_costAt_online_le
    (oneKey : Bool) (S : Setup) (b : QueryBudget)
    (st : shcrKindStTy.denote) (q : KeyIndQuery S)
    (hq : keyIndQueryKind q = ⟨0, by decide⟩) :
    let f := keyIndCoreFuels S b
    (shcrKindHandlePostC oneKey S f.M_on f.roCap).costAt
        (.cons st (.cons ((pqKeyIndCodec S).qenc q) .nil)) +
      (pqKeyIndCodec S).codecCost ≤
      shcrOnlineArmBudget f := by
  intro f
  have hMdh : min f.M_on S.N_dh = f.M_dh := rfl
  have hMsess : min f.M_on S.N_sess_tot = f.M_sess := rfl
  have hCodec : (pqKeyIndCodec S).codecCost = 64 := rfl
  rcases nonSessionLegs_cost_le oneKey S f.M_on with
    ⟨hL1, hL2, hL3, hL4, hL9, hL11, hL12, hL13, hL14⟩
  have hSid := finSidToNatExpr_v0_cost_le S (Γ := [shcrKindStTy, (pqKeyIndCodec S).Q])
  have hPayFin1 : (aop (.finVal S.N_id)
      (.v0 : Expr pqAtomicOps [.base (.fin S.N_id), shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
      _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayPair : (finPairToNatE S.N_id S.N_recv
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id)) (.base (.fin S.N_recv)),
        shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [finPairToNatE, aop, Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
      _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayTriple : (finTripleToNatE S.N_id S.N_recv S.N_opk
      (.v0 : Expr pqAtomicOps [.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv)) (.base (.fin S.N_opk))),
        shcrKindStTy, (pqKeyIndCodec S).Q] _)).cost ≤ 40 := by
    simp [finTripleToNatE, aop, Expr.cost, Expr.v0, pqAtomicOps, _root_.ReductionDsl.atomicPureOps,
      _root_.ReductionDsl.AtomicPureOp.cost]
  have hPayUnit : (.unit : Expr pqAtomicOps [.unit, shcrKindStTy, (pqKeyIndCodec S).Q] .unit).cost ≤ 40 := by
    simp [Expr.cost]
  have hPayV0 : (.v0 : Expr pqAtomicOps [PB 32, shcrKindStTy, (pqKeyIndCodec S).Q] (PB 32)).cost ≤ 40 := by
    simp [Expr.cost, Expr.v0]
  have hA1  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayFin1 hL1
  have hA2  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayFin1 hL2
  have hA3  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayPair hL3
  have hA4  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayTriple hL4
  have hA5  := shcrInitArmPostK_cost_le S f.M_on f.roCap S.N_send_opk true
  have hA6  := shcrInitArmPostK_cost_le S f.M_on f.roCap S.N_send_no_opk false
  have hA7  := shcrAccArmPostK_cost_le S f.M_on f.roCap S.N_opk true
  have hA8  := shcrAccArmPostK_cost_le S f.M_on f.roCap S.N_no_opk false
  have hA9  := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hSid hL9
  have hA11 := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayUnit hL11
  have hA12 := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hSid hL12
  have hA13 := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayV0 hL13
  have hA14 := shcrLiftLegArmK_cost_le_of S f.M_on _ _ hPayPair hL14
  rw [hMdh] at hA5 hA6 hA7 hA8
  rw [hMsess] at hA5 hA6
  let B := shcrOnlineArmBudget f - 90
  have hD := dispatchKeyIndQ_online_costAt_le S B st q hq
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0)
      (if oneKey then shcrInitPrin1KeyLeg f.M_on else shcrInitPrin2KeyLeg f.M_on))
    (shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg f.M_on))
    (shcrLiftLegArmK S (P := .prod .nat .nat) (finPairToNatE S.N_id S.N_recv .v0)
      (if oneKey then shcrActiveGenSpkLeg S f.M_on else shcrGenSpkLeg S f.M_on))
    (shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat))
      (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg f.M_on))
    (shcrInitArmPostK S f.M_on f.roCap S.N_send_opk true)
    (shcrInitArmPostK S f.M_on f.roCap S.N_send_no_opk false)
    (shcrAccArmPostK S f.M_on f.roCap S.N_opk true)
    (shcrAccArmPostK S f.M_on f.roCap S.N_no_opk false)
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrTestLeg f.M_on))
    (shcrRoArmK S f.roCap)
    (shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg f.M_on))
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrRevSessLeg f.M_on))
    (shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg)
    (shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg f.M_on))
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
    (by simp only [B, shcrOnlineArmBudget]; omega)
  dsimp only [shcrKindHandlePostC]
  simp only [B, shcrOnlineArmBudget] at hD ⊢
  omega

theorem shcrKindResumeC_cost_le_of (S : Setup) (K_on capRo : ℕ) :
    (shcrKindResumeC S K_on capRo).cost ≤
      17000 + 2200 * min K_on S.N_dh + 15400 * min K_on S.N_sess_tot + 6700 * K_on +
        (4420 * bits capRo + 1400) := by
  have hPre := shcrResumePreRoC_cost_le
  have hPreMap := mapComp_cost_eleven_mul_le tlPrimKeyInd shcrResumePreRoC
  have hPost := shcrResumePostRoC_cost_le S K_on
  have hPostMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrResumePostRoC S K_on)
  have hRo := roShadowQueryC_cost_le tlPrimKeyInd capRo
    (Γ := [embedTy (.prod (_root_.SignalPqxdh.LegacyCosted.B 192)
             (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
                    (_root_.SignalPqxdh.LegacyCosted.B 32))),
           shcrKindStTy,
           embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pauseTy,
           .prod (PB 32) (PB 1568)])
    (shcrRoListAtomicE (.fst .v1)) (.snd .v1) (.fst .v0)
  have hRoList := shcrRoListAtomicE_cost_le
    (Γ := [embedTy (.prod (_root_.SignalPqxdh.LegacyCosted.B 192)
             (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
                    (_root_.SignalPqxdh.LegacyCosted.B 32))),
           shcrKindStTy,
           embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pauseTy,
           .prod (PB 32) (PB 1568)])
    (.fst .v1)
  simp only [shcrKindResumeC, runAt3_cost, runAt6_cost,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hRo hRoList ⊢
  omega

theorem shcrKindResumeC_cost_le (S : Setup) (b : QueryBudget) :
    let f := keyIndCoreFuels S b
    (shcrKindResumeC S f.M_on f.roCap).cost ≤ shcrOnlineArmBudget f := by
  intro f
  have hMdh : min f.M_on S.N_dh = f.M_dh := rfl
  have hMsess : min f.M_on S.N_sess_tot = f.M_sess := rfl
  refine Nat.le_trans (shcrKindResumeC_cost_le_of S f.M_on f.roCap) ?_
  rw [hMdh, hMsess]
  clear_value f
  clear hMdh hMsess
  simp only [shcrOnlineArmBudget]
  omega

theorem shcrKindChDoneC_cost_le :
    shcrKindChDoneC.cost ≤ 50 := by
  have hLeg : shcrChDoneLeg.cost ≤ 15 := by
    simp only [shcrChDoneLeg, scTPk, Comp.cost, Expr.cost]; omega
  have hMap := mapComp_cost_eleven_mul_le tlPrimKeyInd shcrChDoneLeg
  simp only [shcrKindChDoneC, runAt2_cost, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem shcrKindFinishC_cost_le (K_on : ℕ) :
    (shcrKindFinishC K_on).cost ≤ 100 + 23400 * K_on := by
  have hLeg : (shcrExtractLeg K_on).cost = 20 + K_on * 11168 := by
    simp only [shcrExtractLeg, shcrExtractC_cost]
  have hMap := mapComp_cost_eleven_mul_le tlPrimKeyInd (shcrExtractLeg K_on)
  simp only [shcrKindFinishC, runAt3_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKCost
