/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDhProofs
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs
import Computational.Proofs.ReductionDsl.Size

/-!
# Cost, Query, and Block-Size Bounds for `fgAuth1KeyGapDhProg`

**Checked by Lean.** Syntactic step-cost, query-count, program-size, and output block-size bounds
for `fgAuth1KeyGapDhProg`, together with `CostedReduction.queryBound_eval` soundness bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle gapDhDdhOracle
end

theorem a1g_wDdhGdh_eq : KeyIndGapDh.wDdhGdh = gdhChalW := by
  funext g; rcases g with g | ⟨⟩ <;> rfl

theorem a1g_wPrimGdh_eq : KeyIndGapDh.wPrimGdh = gdhPrimW := by
  funext g; rcases g with g | ⟨⟩ <;> rfl

theorem a1g_wsZero_eq : KeyIndGapDh.wsZero = gdhWS := rfl

@[simp] theorem a1g_wSig_inl (g : PTag) : KeyInd1KeyGapDh.wSig1Key (.inl g) = 0 := rfl
@[simp] theorem a1g_wSig_inrl (m : ℕ+) : KeyInd1KeyGapDh.wSig1Key (.inr (.inl m)) = 1 := rfl
@[simp] theorem a1g_wSig_inrr (u : Unit) : KeyInd1KeyGapDh.wSig1Key (.inr (.inr u)) = 0 := rfl
@[simp] theorem a1g_wDdh_inl (g : PTag) : KeyInd1KeyGapDh.wDdh1Key (.inl g) = 0 := rfl
@[simp] theorem a1g_wDdh_inrl (m : ℕ+) : KeyInd1KeyGapDh.wDdh1Key (.inr (.inl m)) = 0 := rfl
@[simp] theorem a1g_wDdh_inrr (u : Unit) : KeyInd1KeyGapDh.wDdh1Key (.inr (.inr u)) = 1 := by
  rcases u with ⟨⟩; rfl
@[simp] theorem a1g_wPrim_inl (g : PTag) : KeyInd1KeyGapDh.wPrim1Key (.inl g) = 1 := rfl
@[simp] theorem a1g_wPrim_inr (t : ℕ+ ⊕ Unit) : KeyInd1KeyGapDh.wPrim1Key (.inr t) = 0 := rfl
@[simp] theorem a1g_wsZero1Key (s : PSamp) : KeyInd1KeyGapDh.wsZero1Key s = 0 := rfl

@[simp] theorem a1g_liftGdhComp_queries_ddh {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (KeyInd1KeyGapDh.liftGdhComp c).queries KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key =
      c.queries gdhChalW gdhWS := by
  rw [KeyInd1KeyGapDh.liftGdhComp_queries_ddh, a1g_wDdhGdh_eq, a1g_wsZero_eq]

@[simp] theorem a1g_liftGdhComp_queries_prim {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (KeyInd1KeyGapDh.liftGdhComp c).queries KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key =
      c.queries gdhPrimW gdhWS := by
  rw [KeyInd1KeyGapDh.liftGdhComp_queries_prim, a1g_wPrimGdh_eq, a1g_wsZero_eq]

/-! ## Step cost -/

section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

local macro "a1g_step_cost_simp" : tactic => `(tactic|
  simp only [a1gStepC, a1gPreC, a1gInitPrinC, a1gGenSpkC,
    a1gStep2C, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C,
    KeyInd1KeyGapDh.liftGdhComp_costUB, KeyInd1KeyGapDh.sigChalQ_dsl_costUB,
    findHonestC_costUB, isGameSpkC_costUB, isGameOpkC_costUB, resolveSigPkC_costUB,
    firstMsgADE_costUB, sidEq_costUB, optU32Eq_costUB, kyberCheckE_costUB,
    fgStepC, fgInitPrinC, fgGenSpkC, fgSendC, fgStep2C, fgInitPrin2C, fgGenSpk2C, fgSend2C,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF, corruptB, genOpkB, sendGuardE,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC, patchC,
    rootPatchC, isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    bindV, letV, caseOptV, caseSumV, findMV, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    natEq, nat2Eq, nat3Eq, isSomeE, optFst, optSnd, bytesEmpty, slice32, q4,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    peMk, peUpd, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, sbMk, oeOpkSk, oeOpkPk, oeConsumed,
    oeMk, oeUpd, buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paV, paDh1, paTI, paTS, pa2U, pa2V, pa2Role, pa2TS, pa2Dh1,
    feP1, feP2, feP3, feP4, feSs, feDk, pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, Comp.costUB_liftChal, Comp.letC,
    costUB_encEC, costUB_encKEM, costUB_bytesTakeK, costUB_bytesDrop, costUB_bytesLen,
    costUB_bytesBeq, costUB_litBytes, costUB_u32OfNat, costUB_u32Beq, costUB_sampleBytes32,
    costUB_sampleBytes32C, costUB_sampleRandom64C, costUB_sampleDrKey96C, costUB_queryPrim,
    costUB_queryPrimC, costUB_queryDdh, Ty.wd, v, Comp.costUB, Expr.costUB,
    PNat.val_ofNat, F_X25519_length, List.length_nil,
    bits_0, bits_1, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ite_true, ite_false, Bool.false_eq_true])

theorem a1gStepC_costUB_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy) :
    (a1gStepC S K (Δ := Δ) st q).costUB ≤ 80000 + 30000 * K + 10000 * S.N_dh := by
  have hb1 : bits (nRecvEff S) ≤ S.N_dh + 1 := by
    have := bits_le_succ (nRecvEff S); have := nRecvEff_le_N_dh S; omega
  have hb2 : bits (nSendOpkEff S) ≤ S.N_dh + 1 := by
    have := bits_le_succ (nSendOpkEff S); have := nSendOpkEff_le_N_dh S; omega
  have hb3 : bits (nSendNoOpkEff S) ≤ S.N_dh + 1 := by
    have := bits_le_succ (nSendNoOpkEff S); have := nSendNoOpkEff_le_N_dh S; omega
  have hb4 : bits S.N_send_opk_tot ≤ S.N_dh + 1 := by
    have := bits_le_succ S.N_send_opk_tot; unfold Setup.N_dh Setup.N_send_tot; omega
  a1g_step_cost_simp
  omega

theorem a1gStep2C_costUB_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ a1g2StTy) (q : Var Γ₂ authQueryTy) :
    (a1gStep2C S K (Δ := Δ) st q).costUB ≤ 80000 + 30000 * K + 10000 * min K S.N_dh := by
  a1g_step_cost_simp
  generalize min K S.N_dh = md
  omega

theorem a1g_handle_cost_le_v2 (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).handle.cost ≤ 80000 + 30000 * K + 10000 * min K S.N_dh := by
  dsimp only [fgAuth1KeyGapDhProg, a1g2HandleDsl, authCodec]
  exact Nat.le_trans (Comp.cost_le_costUB _) (a1gStep2C_costUB_le S K .vz (.vs .vz))

theorem a1g_handle_cost_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).handle.cost ≤ 80000 + 30000 * K + 10000 * S.N_dh := by
  have h := a1g_handle_cost_le_v2 S K
  have hm : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  omega

theorem a1g_finish_cost_le_v2 (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).finish.cost ≤
      1100 + 1100 * K + 1000 * min K S.N_dh + 1000 * min K S.N_sess_tot +
        200 * (K * min K S.N_dh) + 200 * (min K S.N_dh * min K S.N_dh) +
        50 * (min K S.N_dh * min K S.N_sess_tot) := by
  dsimp only [fgAuth1KeyGapDhProg, a1g2FinishDsl, letV, Comp.letC, Comp.cost, Expr.cost]
  rw [KeyInd1KeyGapDh.renameComp_cost]
  have hUB : (KeyInd1KeyGapDh.liftGdhComp (fgFinish2Dsl S K)).cost ≤
      1080 + 1100 * K + 1000 * min K S.N_dh + 1000 * min K S.N_sess_tot +
        200 * (K * min K S.N_dh) + 200 * (min K S.N_dh * min K S.N_dh) +
        50 * (min K S.N_dh * min K S.N_sess_tot) := by
    refine Nat.le_trans (Comp.cost_le_costUB _) ?_
    rw [KeyInd1KeyGapDh.liftGdhComp_costUB]
    simp only [fgFinish2Dsl, fgExtract2C, findMap2C, logScan2C, respCand2C, initDh1Cand2C,
      bindV, letV, caseOptV, findMV, mapMV, foldMV, eCaseOpt, eCaseSum, eFind, eMap,
      natEq, nat2Eq, bytesEmpty, slice32, zero32, stPrin, stSpks, stSess, seSid, sePeerSpk, seEkASk,
      peIkAPk, sbSpkSk, sbSpkPk, fsBase, fsLog, fsResp, fsPows, pa2U, pa2V, pa2Dh1, Comp.letC,
      costUB_bytesTakeK, costUB_bytesDrop, costUB_bytesBeq, costUB_litBytes,
      costUB_queryPrimC, costUB_queryDdh, Ty.wd, v, Comp.costUB, Expr.costUB,
      PNat.val_ofNat, List.length_nil, List.length_replicate, bits_32, bits_96]
    generalize min K S.N_dh = md; generalize min K S.N_sess_tot = ms; ring_nf; omega
  omega

theorem a1g_finish_cost_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).finish.cost ≤
      1100 + 1100 * K + 1000 * S.N_dh + 1000 * S.N_sess_tot +
        200 * (K * S.N_dh) + 200 * (S.N_dh * S.N_dh) + 200 * (S.N_dh * S.N_sess_tot) := by
  have h := a1g_finish_cost_le_v2 S K
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right K S.N_sess_tot
  have h1 : K * min K S.N_dh ≤ K * S.N_dh := Nat.mul_le_mul_left K hd
  have h2 : min K S.N_dh * min K S.N_dh ≤ S.N_dh * S.N_dh := Nat.mul_le_mul hd hd
  have h3 : min K S.N_dh * min K S.N_sess_tot ≤ S.N_dh * S.N_sess_tot := Nat.mul_le_mul hd hs
  omega

private theorem pow_two_ge_two_mul (k : ℕ) (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · decide
    · have ih' := ih (by omega)
      have hEq : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      omega

private theorem two_mul_log2_le (n : ℕ) : 2 * Nat.log 2 n ≤ n := by
  by_cases hn : n < 2
  · interval_cases n <;> simp
  · have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) (by omega)
    have h1 := pow_two_ge_two_mul (Nat.log 2 n) hlog
    have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    omega

private theorem bits_le_log2_N_dh_add_one {n D : ℕ} (h : n ≤ D) :
    bits n ≤ Nat.log 2 D + 1 := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem sampleSpkPair2C_costUB_le (S : Setup) {Δ : List (Ty pqSig)} :
    (sampleSpkPair2C S (Δ := Δ)).costUB ≤ 20 + 2 * Nat.log 2 S.N_dh := by
  unfold sampleSpkPair2C
  split_ifs with h0
  · simp [Comp.costUB, Expr.costUB]; omega
  · have hSpkPos : 0 < S.N_id * S.N_recv := by unfold Setup.N_spk_tot at h0; omega
    have hIdPos : 1 ≤ S.N_id := by
      rcases Nat.eq_zero_or_pos S.N_id with hZ | hP
      · simp [hZ] at hSpkPos
      · omega
    have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by unfold Setup.N_dh; omega)
    have hbRecv : bits S.N_recv ≤ Nat.log 2 S.N_dh + 1 := by
      apply bits_le_log2_N_dh_add_one
      have hm : 1 * S.N_recv ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv hIdPos
      unfold Setup.N_dh Setup.N_spk_tot; omega
    simp only [bindV, v, Comp.sampleIndexC, pqGapDhIface, pqChalIface, pqSamplers, PSamp.cost,
      Comp.costUB, Expr.costUB, bits] at hbId hbRecv ⊢
    omega

private theorem bernoulliRatioC_costUB_le {Δ : List (Ty pqSig)} (A B D : Nat) (hAB : A + B ≤ D) :
    (bernoulliRatioC (Δ := Δ) A B).costUB ≤ 45 + 3 * Nat.log 2 D := by
  unfold bernoulliRatioC; split_ifs with hA hB hle
  · simp [Comp.costUB, Expr.costUB]; omega
  · simp [Comp.costUB, Expr.costUB]; omega
  · have hb1 := bits_le_log2_N_dh_add_one hAB
    have hb2 := bits_le_log2_N_dh_add_one (n := A) (D := D) (by omega)
    simp only [bindV, v, Comp.sampleIndexC, pqGapDhIface, pqChalIface, pqSamplers, PSamp.cost, Comp.costUB, Expr.costUB, bits_1]
    simp only [bits] at hb1 hb2 ⊢; omega
  · have hb1 := bits_le_log2_N_dh_add_one hAB
    have hb2 := bits_le_log2_N_dh_add_one (n := B) (D := D) (by omega)
    simp only [bindV, v, Comp.sampleIndexC, pqGapDhIface, pqChalIface, pqSamplers, PSamp.cost, Comp.costUB, Expr.costUB, bits_1]
    simp only [bits] at hb1 hb2 ⊢; omega

private theorem sampleRole2C_costUB_le (S : Setup) {Δ : List (Ty pqSig)} :
    (sampleRole2C S (Δ := Δ)).costUB ≤ 120 + 7 * Nat.log 2 S.N_dh := by
  unfold sampleRole2C; by_cases h0 : S.N_id = 0
  · simp [h0, Comp.costUB, Expr.costUB]; omega
  · simp only [h0, ↓reduceIte]; have hIdPos : 1 ≤ S.N_id := by omega
    have hbId := bits_le_log2_N_dh_add_one (n := S.N_id) (D := S.N_dh) (by unfold Setup.N_dh; omega)
    have hTot : 1 + S.N_send_opk + S.N_send_no_opk ≤ S.N_dh := by
      unfold Setup.N_dh Setup.N_send_tot Setup.N_send_opk_tot Setup.N_send_no_opk_tot; nlinarith
    have hbTot := bits_le_log2_N_dh_add_one hTot
    have hbO : bits S.N_send_opk ≤ Nat.log 2 S.N_dh + 1 := bits_le_log2_N_dh_add_one (by omega)
    have hbN : bits S.N_send_no_opk ≤ Nat.log 2 S.N_dh + 1 := bits_le_log2_N_dh_add_one (by omega)
    have hBern := bernoulliRatioC_costUB_le (Δ := .nat :: .nat :: Δ)
      S.N_send_opk S.N_send_no_opk S.N_dh (by omega)
    simp only [pqGapDhIface, pqChalIface, pqSamplers] at hBern
    split_ifs with h1 h2 h3 <;>
      simp only [bindV, natEq, v, Comp.iteC, Comp.sampleIndexC, pqGapDhIface, pqChalIface, pqSamplers,
        PSamp.cost, Comp.costUB, Expr.costUB, bits_0] <;>
      (simp only [bits] at hbId hbTot hbO hbN ⊢; omega)

theorem a1g_init_cost_le_v2 (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).init.cost ≤ 280 + 10 * Nat.log 2 S.N_dh := by
  dsimp only [fgAuth1KeyGapDhProg]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  have hR := sampleRole2C_costUB_le S (Δ := [.prod (B 32) (B 32)])
  have hS := sampleSpkPair2C_costUB_le S (Δ := [a1gRole2Ty, .prod (B 32) (B 32)])
  have hbB : bits (min K (min S.N_spk_tot S.N_recv)) ≤ Nat.log 2 S.N_dh + 1 := by
    apply bits_le_log2_N_dh_add_one
    have h1 : min K (min S.N_spk_tot S.N_recv) ≤ S.N_spk_tot :=
      le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    unfold Setup.N_dh; omega
  simp only [a1g2InitDsl, KeyInd1KeyGapDh.liftGdhComp_costUB, fgInit2Dsl,
    emptySimE, emptyAuthStE, fsMk, stMk,
    bindV, v, costUB_sampleBoolC,
    Comp.costUB, Expr.costUB]
  omega

theorem a1g_init_cost_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).init.cost ≤ 300 + 5 * S.N_dh := by
  have h := a1g_init_cost_le_v2 S K
  have hlog := two_mul_log2_le S.N_dh
  omega

end

theorem fgAuth1KeyGapDhProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (fgAuth1KeyGapDhProg S b.q_total).totalCost b.q_total ≤
      SignalPqxdh.LegacyCosted.stepCostBudget S b := by
  have hH := a1g_handle_cost_le S b.q_total
  have hF := a1g_finish_cost_le S b.q_total
  have hI := a1g_init_cost_le S b.q_total
  change (fgAuth1KeyGapDhProg S b.q_total).init.cost +
      b.q_total * max 1 ((fgAuth1KeyGapDhProg S b.q_total).handle.cost + 32) +
      (fgAuth1KeyGapDhProg S b.q_total).finish.cost ≤
      SignalPqxdh.LegacyCosted.stepCostBudget S b
  generalize (fgAuth1KeyGapDhProg S b.q_total).init.cost = cI at hI ⊢
  generalize (fgAuth1KeyGapDhProg S b.q_total).handle.cost = cH at hH ⊢
  generalize (fgAuth1KeyGapDhProg S b.q_total).finish.cost = cF at hF ⊢
  have hMax : max 1 (cH + 32) = cH + 32 := by omega
  rw [hMax]
  unfold SignalPqxdh.LegacyCosted.stepCostBudget
  generalize b.q_total = q at *
  have hqH : q * (cH + 32) ≤ q * (80032 + 30000 * q + 10000 * S.N_dh) :=
    Nat.mul_le_mul_left q (by omega)
  nlinarith [Nat.zero_le (q * S.N_dh), Nat.zero_le (q * S.N_sess_tot),
    Nat.zero_le (S.N_dh * S.N_sess_tot)]

theorem fgAuth1KeyGapDhProg_totalCost_le_security (S : Setup) (b : QueryBudget) :
    (fgAuth1KeyGapDhProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have hH := a1g_handle_cost_le_v2 S b.q_total
  have hF := a1g_finish_cost_le_v2 S b.q_total
  have hI := a1g_init_cost_le_v2 S b.q_total
  change (fgAuth1KeyGapDhProg S b.q_total).init.cost +
      b.q_total * max 1 ((fgAuth1KeyGapDhProg S b.q_total).handle.cost + 32) +
      (fgAuth1KeyGapDhProg S b.q_total).finish.cost ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b
  generalize (fgAuth1KeyGapDhProg S b.q_total).init.cost = cI at hI ⊢
  generalize (fgAuth1KeyGapDhProg S b.q_total).handle.cost = cH at hH ⊢
  generalize (fgAuth1KeyGapDhProg S b.q_total).finish.cost = cF at hF ⊢
  have hMax : max 1 (cH + 32) = cH + 32 := by omega
  rw [hMax]
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize min b.q_total S.N_dh = md at hH hF ⊢
  generalize min b.q_total S.N_sess_tot = ms at hF ⊢
  generalize Nat.log 2 S.N_dh = ld at hI ⊢
  generalize Nat.log 2 S.N_sess_tot = ls at ⊢
  generalize b.q_total = q at *
  have hqH : q * (cH + 32) ≤ q * (80032 + 30000 * q + 10000 * md) :=
    Nat.mul_le_mul_left q (by omega)
  nlinarith [Nat.zero_le (q * md), Nat.zero_le (q * ms), Nat.zero_le (md * ms),
    Nat.zero_le (q * ld), Nat.zero_le (q * ls)]

/-! ## Query counts -/

section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

theorem a1gStepC_queries_sig_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy) :
    (a1gStepC S K (Δ := Δ) st q).queries
      KeyInd1KeyGapDh.wSig1Key KeyInd1KeyGapDh.wsZero1Key ≤ 2 := by
  simp only [
    a1gStepC, Comp.letC, a1gPreC, a1gInitPrinC, a1gGenSpkC,
    KeyInd1KeyGapDh.liftGdhComp_queries_sig, KeyInd1KeyGapDh.sigChalQ_dsl_queries_sig,
    bindV, letV, caseOptV, caseSumV,
    Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.queryPrimC,
    a1g_wSig_inl, a1g_wsZero1Key, Comp.queries,
    Nat.zero_max, Nat.max_zero, max_self, Nat.add_zero, Nat.zero_add]
  omega

theorem a1g_handle_sig_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).handle.queries
      KeyInd1KeyGapDh.wSig1Key KeyInd1KeyGapDh.wsZero1Key ≤ 2 := by
  dsimp only [fgAuth1KeyGapDhProg, a1g2HandleDsl, authCodec]
  simp only [
    a1gStep2C, Comp.letC, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C,
    KeyInd1KeyGapDh.liftGdhComp_queries_sig, KeyInd1KeyGapDh.sigChalQ_dsl_queries_sig,
    bindV, letV, caseOptV, caseSumV, Comp.iteC,
    Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.queryPrimC,
    a1g_wSig_inl, a1g_wsZero1Key, Comp.queries,
    Nat.zero_max, Nat.max_zero, max_self, Nat.add_zero, Nat.zero_add]
  omega

local macro "a1g_ddh_q_simp" : tactic => `(tactic|
  simp only [a1gStepC, a1gPreC, a1gInitPrinC, a1gGenSpkC,
    a1gStep2C, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C, Comp.letC, Comp.iteC,
    a1g_liftGdhComp_queries_ddh, KeyInd1KeyGapDh.sigChalQ_dsl_queries_ddh,
    queries_liftChal_gdhChalW, queries_queryDdh_chal,
    fgStepC, fgInitPrinC, fgGenSpkC, fgSendC, fgStep2C, fgInitPrin2C, fgGenSpk2C, fgSend2C,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF, corruptB, genOpkB,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC, patchC,
    rootPatchC, findMV, Comp.sampleDrKey96C, gdhChalW, gdhWS, bindV, letV, caseOptV, caseSumV,
    Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.queryPrimC, a1g_wDdh_inl, a1g_wsZero1Key,
    Comp.queries, ite_true, ite_false, Bool.false_eq_true,
    Nat.zero_max, Nat.max_zero, max_self, Nat.add_zero, Nat.zero_add, Nat.mul_one])

local macro "a1g_prim_q_simp" : tactic => `(tactic|
  simp only [a1gStepC, a1gPreC, a1gInitPrinC, a1gGenSpkC,
    a1gStep2C, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C, Comp.letC, Comp.iteC,
    a1g_liftGdhComp_queries_prim, KeyInd1KeyGapDh.sigChalQ_dsl_queries_prim,
    findHonestC_queries, isGameSpkC_queries, isGameOpkC_queries, resolveSigPkC_queries,
    queries_liftChal_gdhPrimW, queries_queryDdh_prim,
    fgStepC, fgInitPrinC, fgGenSpkC, fgSendC, fgStep2C, fgInitPrin2C, fgGenSpk2C, fgSend2C,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF, corruptB, genOpkB,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC, patchC,
    rootPatchC, isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    findMV, Comp.sampleBytes32, Comp.sampleDrKey96C, Comp.queryPrim, primW, primWS, gdhPrimW, gdhWS,
    bindV, letV, caseOptV, caseSumV, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.queryPrimC,
    a1g_wPrim_inl, a1g_wsZero1Key, Comp.queries, ite_true, ite_false, Bool.false_eq_true,
    Nat.zero_max, Nat.max_zero, max_self, Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.mul_one])

theorem a1gStepC_queries_ddh_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy) :
    (a1gStepC S K (Δ := Δ) st q).queries
      KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key ≤ 5 * K := by
  a1g_ddh_q_simp; omega

theorem a1g_handle_ddh_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).handle.queries
      KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key ≤ 5 * K := by
  dsimp only [fgAuth1KeyGapDhProg, a1g2HandleDsl, authCodec]; a1g_ddh_q_simp; omega

theorem a1gStepC_queries_prim_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy) :
    (a1gStepC S K (Δ := Δ) st q).queries
      KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key ≤ 174 + S.N_dh * 30 := by
  a1g_prim_q_simp; omega

theorem a1g_handle_prim_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).handle.queries
      KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key ≤ 174 + S.N_dh * 30 := by
  dsimp only [fgAuth1KeyGapDhProg, a1g2HandleDsl, authCodec]; a1g_prim_q_simp
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh; omega

end

theorem a1g_finish_sig (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).finish.queries
      KeyInd1KeyGapDh.wSig1Key KeyInd1KeyGapDh.wsZero1Key = 0 := by
  simp [fgAuth1KeyGapDhProg, a1g2FinishDsl, letV, Comp.letC, Comp.queries,
    KeyInd1KeyGapDh.renameComp_queries, KeyInd1KeyGapDh.liftGdhComp_queries_sig]

theorem a1g_finish_ddh_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).finish.queries
      KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key ≤ K + S.N_dh + S.N_sess_tot := by
  dsimp only [fgAuth1KeyGapDhProg, a1g2FinishDsl, letV, Comp.letC, Comp.queries]
  rw [KeyInd1KeyGapDh.renameComp_queries, a1g_liftGdhComp_queries_ddh]
  simp only [
    queries_queryDdh_chal,
    fgFinish2Dsl, fgExtract2C, findMap2C, logScan2C, respCand2C, initDh1Cand2C,
    bindV, letV, caseOptV, findMV, mapMV, foldMV,
    Comp.iteC, Comp.letC, Comp.queryPrimC,
    gdhChalW, Comp.queries]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right K S.N_sess_tot
  omega

theorem a1g_finish_prim_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).finish.queries
      KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key ≤ S.N_dh * 4 + S.N_sess_tot * 2 := by
  dsimp only [fgAuth1KeyGapDhProg, a1g2FinishDsl, letV, Comp.letC, Comp.queries]
  rw [KeyInd1KeyGapDh.renameComp_queries, a1g_liftGdhComp_queries_prim]
  simp only [
    queries_queryDdh_prim,
    fgFinish2Dsl, fgExtract2C, findMap2C, logScan2C, respCand2C, initDh1Cand2C,
    bindV, letV, caseOptV, findMV, mapMV, foldMV,
    Comp.iteC, Comp.letC, Comp.queryPrimC,
    gdhPrimW, Comp.queries]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right K S.N_sess_tot
  omega

private theorem bernoulliRatioC_queries_zero {Δ : List (Ty pqSig)} (A B : Nat)
    (w : pqGapDhIface.Tag → Nat) :
    (bernoulliRatioC (Δ := Δ) A B).queries w gdhWS = 0 := by
  unfold bernoulliRatioC
  split_ifs <;> simp [bindV, Comp.sampleIndexC, gdhWS, Comp.queries]

private theorem sampleRole2C_queries_zero (S : Setup) {Δ : List (Ty pqSig)}
    (w : pqGapDhIface.Tag → Nat) :
    (sampleRole2C S (Δ := Δ)).queries w gdhWS = 0 := by
  unfold sampleRole2C
  split_ifs <;>
    simp [bindV, Comp.iteC, Comp.sampleIndexC, bernoulliRatioC_queries_zero, gdhWS, Comp.queries]

private theorem sampleSpkPair2C_queries_zero (S : Setup) {Δ : List (Ty pqSig)}
    (w : pqGapDhIface.Tag → Nat) :
    (sampleSpkPair2C S (Δ := Δ)).queries w gdhWS = 0 := by
  unfold sampleSpkPair2C
  split_ifs <;> simp [bindV, Comp.sampleIndexC, gdhWS, Comp.queries]

theorem a1g_init_sig (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).init.queries
      KeyInd1KeyGapDh.wSig1Key KeyInd1KeyGapDh.wsZero1Key = 0 := by
  simp [fgAuth1KeyGapDhProg, a1g2InitDsl, bindV, Comp.queries,
    KeyInd1KeyGapDh.liftGdhComp_queries_sig]

theorem a1g_init_ddh (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).init.queries
      KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key = 0 := by
  simp only [fgAuth1KeyGapDhProg, a1g2InitDsl, fgInit2Dsl, bindV, Comp.sampleBoolC,
    a1g_liftGdhComp_queries_ddh, sampleRole2C_queries_zero, sampleSpkPair2C_queries_zero,
    gdhWS, Comp.queries, Nat.add_zero]

theorem a1g_init_prim (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).init.queries
      KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key = 0 := by
  simp only [fgAuth1KeyGapDhProg, a1g2InitDsl, fgInit2Dsl, bindV, Comp.sampleBoolC,
    a1g_liftGdhComp_queries_prim, sampleRole2C_queries_zero, sampleSpkPair2C_queries_zero,
    gdhWS, Comp.queries, Nat.add_zero]

theorem fgAuth1KeyGapDhProg_totalSigQueries_le (S : Setup) (b : QueryBudget) :
    (fgAuth1KeyGapDhProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total := by
  change (fgAuth1KeyGapDhProg S b.q_total).totalQueries
    KeyInd1KeyGapDh.wSig1Key KeyInd1KeyGapDh.wsZero1Key b.q_total ≤ _
  dsimp only [CostedReduction.totalQueries]
  rw [a1g_init_sig, a1g_finish_sig]
  have hH := Nat.mul_le_mul_left b.q_total (a1g_handle_sig_le S b.q_total)
  omega

theorem fgAuth1KeyGapDhProg_totalDdhQueries_le (S : Setup) (b : QueryBudget) :
    (fgAuth1KeyGapDhProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤
        5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  change (fgAuth1KeyGapDhProg S b.q_total).totalQueries
    KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key b.q_total ≤ _
  dsimp only [CostedReduction.totalQueries]
  rw [a1g_init_ddh, Nat.zero_add]
  have hH := a1g_handle_ddh_le S b.q_total
  have hF := a1g_finish_ddh_le S b.q_total
  generalize (fgAuth1KeyGapDhProg S b.q_total).handle.queries
    KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key = qH at hH ⊢
  generalize (fgAuth1KeyGapDhProg S b.q_total).finish.queries
    KeyInd1KeyGapDh.wDdh1Key KeyInd1KeyGapDh.wsZero1Key = qF at hF ⊢
  generalize b.q_total = q at *
  have h1 : q * qH ≤ 5 * (q * q) := by
    rw [← Nat.mul_left_comm]
    exact Nat.mul_le_mul_left q hH
  rw [pow_two]
  omega

theorem fgAuth1KeyGapDhProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (fgAuth1KeyGapDhProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  change (fgAuth1KeyGapDhProg S b.q_total).totalQueries
    KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key b.q_total ≤ _
  dsimp only [CostedReduction.totalQueries]
  rw [a1g_init_prim, Nat.zero_add]
  have hH := a1g_handle_prim_le S b.q_total
  have hF := a1g_finish_prim_le S b.q_total
  generalize (fgAuth1KeyGapDhProg S b.q_total).handle.queries
    KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key = qH at hH ⊢
  generalize (fgAuth1KeyGapDhProg S b.q_total).finish.queries
    KeyInd1KeyGapDh.wPrim1Key KeyInd1KeyGapDh.wsZero1Key = qF at hF ⊢
  unfold primQueryBudget
  generalize b.q_total = q at *
  have h1 : q * qH ≤ q * (174 + S.N_dh * 30) := Nat.mul_le_mul_left q hH
  nlinarith

/-! ## Output block-size bound -/

private theorem a1g_valFits_iff_fits {S : Sig} (B : ℕ) :
    ∀ (t : Ty S) (x : t.denote), ValFits B t x ↔ t.Fits B x
  | .base _, _ => Iff.rfl
  | .unit, _ => Iff.rfl
  | .bool, _ => Iff.rfl
  | .nat, _ => Iff.rfl
  | .opt _, none => Iff.rfl
  | .opt t, some a => a1g_valFits_iff_fits B t a
  | .prod t u, x => and_congr (a1g_valFits_iff_fits B t x.1) (a1g_valFits_iff_fits B u x.2)
  | .sum t _, .inl a => a1g_valFits_iff_fits B t a
  | .sum _ u, .inr b => a1g_valFits_iff_fits B u b
  | .list t, _ => and_congr Iff.rfl
      (forall_congr' fun x => imp_congr_right fun _ => a1g_valFits_iff_fits B t x)
  | .tbl t, m => forall_congr' fun i => a1g_valFits_iff_fits B t (m i)

private theorem a1g_one_le_pqSamplers_sCost (s : PSamp) : 1 ≤ pqSamplers.sCost s := by
  cases s <;> simp [pqSamplers, PSamp.cost]

private theorem a1g_one_le_pqChalIface_qCost {C : ChallengerOracle} (g : (pqChalIface C).Tag) :
    1 ≤ (pqChalIface C).qCost g := by
  cases g <;> simp only [pqChalIface, ChallengerOracle.qCost] <;> omega

private theorem a1g_comp_nq_le_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    (hq : ∀ g, 1 ≤ I.qCost g) (hs : ∀ s, 1 ≤ I.smp.sCost s)
    {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps I Γ t) : c.nq ≤ c.cost := by
  induction c with
  | ret _ => simp [Comp.nq, Comp.queries, Comp.cost]
  | bind c k ihc ihk => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | ite _ c d ihc ihd => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | caseOpt _ n s ihn ihs => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | caseSum _ l r ihl ihr => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | sample s _ => have := hs s; dsimp only [Comp.nq, Comp.queries, Comp.cost]; omega
  | query g _ => have := hq g; dsimp only [Comp.nq, Comp.queries, Comp.cost]; omega
  | iter n _ body ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) body ≤ body.cost + 1 := by omega
    have := Nat.mul_le_mul_left n h1
    omega
  | findM K _ p ih | anyM K _ p ih | mapM K _ p ih | foldM K _ _ p ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) p ≤ p.cost + 1 := by omega
    have := Nat.mul_le_mul_left K h1
    omega
  | consumeFirstM K _ p mk ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) p ≤ p.cost + mk.cost + 1 := by omega
    have := Nat.mul_le_mul_left K h1
    omega

private theorem a1g_gred_nq_le_totalCost {ι κ : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {G : OracleSpec κ} {C : GameCodec pqSig G} {rIn aIn aOut out : Ty pqSig}
    (hq : ∀ g, 1 ≤ I.qCost g) (hs : ∀ s, 1 ≤ I.smp.sCost s)
    (R : CostedReduction pqxdhOps I G C rIn aIn aOut out) (q : ℕ) :
    R.nq q ≤ R.totalCost q := by
  have hI := a1g_comp_nq_le_cost hq hs R.init
  have hH := a1g_comp_nq_le_cost hq hs R.handle
  have hF := a1g_comp_nq_le_cost hq hs R.finish
  have hMax : R.handle.nq ≤ max I.uCost (R.handle.cost + C.codecCost) :=
    le_trans hH (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left q hMax
  dsimp only [CostedReduction.nq, CostedReduction.totalQueries, CostedReduction.totalCost,
    Comp.nq] at *
  omega

theorem fgAuth1KeyGapDhProg_blockBounded (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    SignalPqxdh.LegacyCosted.GRedBlockBounded S b ℓ (fgAuth1KeyGapDhProg S b.q_total) := by
  intro hq henc A hA x hx y hy
  rw [a1g_valFits_iff_fits]
  have hq' : ∀ g x u, (pqSigAndDdhIface.cod g).Fits ℓ (pqSigAndDdhIface.dec g x u) := fun g x u =>
    (a1g_valFits_iff_fits ℓ _ _).1 (hq g x u)
  have henc' : ∀ t, (authCodec S).Q.Fits ℓ ((authCodec S).qenc t) := fun t =>
    (a1g_valFits_iff_fits ℓ _ _).1 (henc t)
  have hx' : (Ty.prod (B 32) (B 32)).Fits ℓ x := (a1g_valFits_iff_fits ℓ _ _).1 hx
  have hA' : ∀ u, (A u).IsQueryBoundP
      (ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  have hEval := (fgAuth1KeyGapDhProg S b.q_total).fits_eval
    pqO_sizeHonest SignalPqxdh.LegacyCosted.pqSamplers_sizeHonest ℓ hq' ℓ henc' 0 (fun _ => trivial)
    A b.q_total ℓ hA' x hx' y hy
  have hCost := fgAuth1KeyGapDhProg_totalCost_le S b
  have hNq := le_trans
    (a1g_gred_nq_le_totalCost a1g_one_le_pqChalIface_qCost a1g_one_le_pqSamplers_sCost
      (fgAuth1KeyGapDhProg S b.q_total) b.q_total)
    hCost
  refine Ty.fits_mono ?_ (B 32) y hEval
  unfold SignalPqxdh.LegacyCosted.outputSizeBudget SignalPqxdh.LegacyCosted.stepCostBudget at *
  have hM := Nat.mul_le_mul_right ℓ hNq
  nlinarith

/-! ## Query-bound soundness bridges -/

theorem fgAuth1KeyGapDhProg_ddhBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := authSpec S)) q)
    (U V : Bytes) :
    ((fgAuth1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true)
      ((fgAuth1KeyGapDhProg S K).totalQueries
        SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q) := by
  refine CostedReduction.queryBound_eval (fgAuth1KeyGapDhProg S K)
    (fun q => isDdhChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
    | inr t =>
      cases t with
      | inl m => simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
      | inr u => rcases u with ⟨⟩; simp [SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isDdhChalQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isDdhChalQuery]

theorem fgAuth1KeyGapDhProg_sigBounded_syntactic (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := authSpec S)) q)
    (U V : Bytes) :
    ((fgAuth1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isSigChalQuery q = true)
      ((fgAuth1KeyGapDhProg S K).totalQueries
        SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q) := by
  refine CostedReduction.queryBound_eval (fgAuth1KeyGapDhProg S K)
    (fun q => isSigChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [pqSigAndDdhIface, pqChalIface, isSigChalQuery] at hx
    | inr t =>
      cases t with
      | inl m => simp [SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]
      | inr u =>
        rcases u with ⟨⟩
        simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isSigChalQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isSigChalQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isSigChalQuery]

theorem fgAuth1KeyGapDhProg_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := authSpec S)) q)
    (U V : Bytes) :
    ((fgAuth1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      ((fgAuth1KeyGapDhProg S K).totalQueries
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
        SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q) := by
  refine CostedReduction.queryBound_eval (fgAuth1KeyGapDhProg S K)
    (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    | inr t => simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]

/-! ## Program-size and run-local block-size bounds -/

section Auth1KeySizeAndWhen

@[simp] private theorem a1g_pqxdhOps_opSize (o : pqxdhOps.Op) : pqxdhOps.opSize o = 0 := by
  cases o <;> rfl
@[simp] private theorem a1g_ops_sum_opSize_inl {S : Sig} (O₁ O₂ : Ops S) (o : O₁.Op) :
    (Ops.sum O₁ O₂).opSize (Sum.inl o) = O₁.opSize o := rfl
@[simp] private theorem a1g_ops_sum_opSize_inr {S : Sig} (O₁ O₂ : Ops S) (o : O₂.Op) :
    (Ops.sum O₁ O₂).opSize (Sum.inr o) = O₂.opSize o := rfl
@[simp] private theorem a1g_pqBytesOps_opSize (o : pqBytesOps.Op) : pqBytesOps.opSize o = 0 := rfl
@[simp] private theorem a1g_pqU32Ops_opSize (o : pqU32Ops.Op) : pqU32Ops.opSize o = 0 := rfl

@[simp] private theorem a1g_liftChal_size {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    c.liftChal.size (I := pqChalIface C) = c.size := by
  induction c <;> simp_all [Comp.liftChal, Comp.size, pqChalIface, pqPrimIface]

private theorem a1g_renameExpr_size_aux {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (e : Expr pqxdhOps Γ t) :
    ∀ {Δ : List (Ty pqSig)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ),
      (KeyInd1KeyGapDh.renameExpr ρ e).size = e.size := by
  induction e <;> intro Δ ρ <;> simp [KeyInd1KeyGapDh.renameExpr, Expr.size, *]

@[simp] private theorem a1g_renameExpr_size {Γ Δ : List (Ty pqSig)} {t : Ty pqSig}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (e : Expr pqxdhOps Γ t) :
    (KeyInd1KeyGapDh.renameExpr ρ e).size = e.size :=
  a1g_renameExpr_size_aux e ρ

private theorem a1g_renameComp_size_aux {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps I Γ t) :
    ∀ {Δ : List (Ty pqSig)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ),
      (KeyInd1KeyGapDh.renameComp ρ c).size = c.size := by
  induction c <;> intro Δ ρ <;> simp [KeyInd1KeyGapDh.renameComp, Comp.size, *]

@[simp] private theorem a1g_renameComp_size {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List (Ty pqSig)} {t : Ty pqSig}
    (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (c : Comp pqxdhOps I Γ t) :
    (KeyInd1KeyGapDh.renameComp ρ c).size = c.size :=
  a1g_renameComp_size_aux c ρ

@[simp] private theorem a1g_liftGdhComp_size {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (KeyInd1KeyGapDh.liftGdhComp c).size = c.size := by
  induction c with
  | query g e =>
    cases g with
    | inl g => rfl
    | inr u => cases u; rfl
  | _ => simp [KeyInd1KeyGapDh.liftGdhComp, Comp.size, *]

@[simp] private theorem a1g_sigChalQ_dsl_size (m : ℕ+) {Γ : List (Ty pqSig)}
    (msg : Expr pqxdhOps Γ (B m)) :
    (KeyInd1KeyGapDh.sigChalQ_dsl m msg).size = msg.size + 1 := rfl

section A1gAtomicSizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {C : ChallengerOracle} {Γ Δ : List (Ty pqSig)} {τ τ₁ τ₂ : Ty pqSig}

@[simp] private theorem a1g_v_size [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).size = 1 := rfl
@[simp] private theorem a1g_letC_size (e : Expr pqxdhOps Γ τ₁) (k : Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (Comp.letC e k).size = e.size + 1 + k.size + 1 := rfl
@[simp] private theorem a1g_bindV_size (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).size = m.size + (k .vz).size + 1 := rfl
@[simp] private theorem a1g_letV_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).size = e.size + 1 + (k .vz).size + 1 := rfl
@[simp] private theorem a1g_caseOptV_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).size = o.size + kn.size + (ks .vz).size + 1 := rfl
@[simp] private theorem a1g_caseSumV_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).size = s.size + (kl .vz).size + (kr .vz).size + 1 := rfl
@[simp] private theorem a1g_findMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem a1g_anyMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem a1g_mapMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV K xs f).size = xs.size + (f .vz).size + bits K + 1 := rfl
@[simp] private theorem a1g_foldMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV K xs init f).size = xs.size + init.size + (f .vz (.vs .vz)).size + bits K + 1 := rfl
@[simp] private theorem a1g_eLet_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).size = e.size + (k .vz).size + 1 := rfl
@[simp] private theorem a1g_eCaseOpt_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt o kn ks).size = o.size + kn.size + (ks .vz).size + 1 := rfl
@[simp] private theorem a1g_eCaseSum_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) :
    (eCaseSum s kl kr).size = s.size + (kl .vz).size + (kr .vz).size + 1 := rfl
@[simp] private theorem a1g_eFind_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem a1g_eAny_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem a1g_eMap_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eMap K xs f).size = xs.size + (f .vz).size + bits K + 1 := rfl
@[simp] private theorem a1g_litBytes_size (w : ℕ+) (bs : Bytes) : (Expr.litBytes w bs (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_bytesAppend_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (Expr.bytesAppend a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem a1g_bytesCons_size {w : ℕ+} (b : UInt8) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesCons b a).size = a.size + 1 := rfl
@[simp] private theorem a1g_bytesWiden_size (w d : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesWiden w d a).size = a.size + 1 := rfl
@[simp] private theorem a1g_bytesTakeK_size {w : ℕ+} (k : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesTakeK k a).size = a.size + 1 := rfl
@[simp] private theorem a1g_bytesDrop_size {w : ℕ+} (n : Expr pqxdhOps Γ .nat) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesDrop n a).size = n.size + a.size + 2 := rfl
@[simp] private theorem a1g_bytesLen_size {w : ℕ+} (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesLen a).size = a.size + 1 := rfl
@[simp] private theorem a1g_bytesBeq_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (Expr.bytesBeq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem a1g_bytesVarint_size (n : Expr pqxdhOps Γ .nat) : (Expr.bytesVarint n).size = n.size + 1 := rfl
@[simp] private theorem a1g_u32OfNat_size (n : Expr pqxdhOps Γ .nat) : (Expr.u32OfNat n).size = n.size + 1 := rfl
@[simp] private theorem a1g_u32Beq_size (a b : Expr pqxdhOps Γ U32) : (Expr.u32Beq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem a1g_sampleBool_size : (Comp.sampleBool (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_sampleBytes32_size : (Comp.sampleBytes32 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_sampleRandom64_size : (Comp.sampleRandom64 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_sampleDrKey96_size : (Comp.sampleDrKey96 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_sampleIndex_size (N : ℕ) : (Comp.sampleIndex N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_queryPrim_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrim g e).size = e.size + 1 := rfl
@[simp] private theorem a1g_sampleBoolC_size : (Comp.sampleBoolC (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_sampleBytes32C_size : (Comp.sampleBytes32C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_sampleRandom64C_size : (Comp.sampleRandom64C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_sampleDrKey96C_size : (Comp.sampleDrKey96C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_sampleIndexC_size (N : ℕ) : (Comp.sampleIndexC (C := C) N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem a1g_queryPrimC_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrimC (C := C) g e).size = e.size + 1 := rfl
@[simp] private theorem a1g_queryChal_size (g : C.Tag) (e : Expr pqxdhOps Γ (C.dom g)) :
    (Comp.queryChal (C := C) g e).size = e.size + 1 := rfl
@[simp] private theorem a1g_queryDdh_size (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) :
    (Comp.queryDdh e).size = e.size + 1 := rfl
@[simp] private theorem a1g_encEC_size (e : Expr pqxdhOps Γ (B 32)) : (encEC e).size = e.size + 1 := rfl
@[simp] private theorem a1g_encKEM_size (e : Expr pqxdhOps Γ (B 1568)) : (encKEM e).size = e.size + 1 := rfl

end A1gAtomicSizeSimp

private theorem a1g_eff_le_dh (S : Setup) :
    nRecvEff S ≤ S.N_dh ∧ nSendOpkEff S ≤ S.N_dh ∧ nSendNoOpkEff S ≤ S.N_dh :=
  ⟨nRecvEff_le_N_dh S, nSendOpkEff_le_N_dh S, nSendNoOpkEff_le_N_dh S⟩

set_option linter.unusedSimpArgs false in
private theorem fg2InitDsl_size_le (S : Setup) : (fg2InitDsl S).size ≤ 200 := by
  have hT : ∀ {Γ : List (Ty pqSig)}, (fgSampleTargetC S (Γ := Γ)).size ≤ 90 := by
    intro Γ; unfold fgSampleTargetC; dsimp only; have hb2 : bits 2 = 2 := by decide
    split_ifs <;> simp only [natEq, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE,
      Expr.someE, Expr.boolNot, Expr.boolAnd, Comp.iteC, a1g_v_size, a1g_bindV_size,
      a1g_sampleIndexC_size, Comp.size, Expr.size, a1g_pqxdhOps_opSize, bits_0, bits_1, hb2] <;> omega
  have hS : ∀ {Γ : List (Ty pqSig)}, (fgSampleSpkC S (Γ := Γ)).size ≤ 20 := by
    intro Γ; unfold fgSampleSpkC
    split_ifs <;> simp only [Expr.noneE, Expr.someE, a1g_v_size, a1g_bindV_size,
      a1g_sampleIndexC_size, Comp.size, Expr.size, a1g_pqxdhOps_opSize] <;> omega
  have h1 := hT (Γ := [.prod (B 32) (B 32)]); have h2 := hS (Γ := [targetChoiceTy, .prod (B 32) (B 32)])
  simp only [fg2InitDsl, emptySimE, emptyAuthStE, fsMk, stMk, Expr.litUnit, Expr.litBool, Expr.litNat,
    Expr.noneE, Expr.listNil, a1g_v_size, a1g_bindV_size, a1g_sampleBoolC_size, Comp.size, Expr.size,
    a1g_pqxdhOps_opSize, bits_0]; omega

set_option linter.unusedSimpArgs false in
private theorem fgInit2Dsl_size_le (S : Setup) : (fgInit2Dsl S).size ≤ 200 := by
  have hB : ∀ {Δ : List (Ty pqSig)} (A B : Nat), (bernoulliRatioC (Δ := Δ) A B).size ≤ 30 := by
    intro Δ A B; unfold bernoulliRatioC
    split_ifs <;> simp only [Expr.litBool, Expr.litNat, Expr.boolNot, a1g_v_size, a1g_bindV_size,
      a1g_sampleIndexC_size, Comp.size, Expr.size, a1g_pqxdhOps_opSize, bits_1] <;> omega
  have hR : ∀ {Δ : List (Ty pqSig)}, (sampleRole2C S (Δ := Δ)).size ≤ 90 := by
    intro Δ; unfold sampleRole2C
    by_cases h0 : S.N_id = 0
    · simp [h0, Expr.litNat, Comp.size, Expr.size, a1g_pqxdhOps_opSize, bits_0]
    · simp only [h0, ↓reduceIte]; have hBern := hB (Δ := [.nat, .nat] ++ Δ) S.N_send_opk S.N_send_no_opk
      split_ifs <;> simp only [natEq, Expr.litBool, Expr.litNat, Comp.iteC, a1g_v_size, a1g_bindV_size,
        a1g_sampleIndexC_size, Comp.size, Expr.size, a1g_pqxdhOps_opSize, bits_0] <;> omega
  have hS : ∀ {Δ : List (Ty pqSig)}, (sampleSpkPair2C S (Δ := Δ)).size ≤ 20 := by
    intro Δ; unfold sampleSpkPair2C
    split_ifs <;> simp only [Expr.noneE, Expr.someE, a1g_v_size, a1g_bindV_size,
      a1g_sampleIndexC_size, Comp.size, Expr.size, a1g_pqxdhOps_opSize] <;> omega
  have h1 := hR (Δ := [.prod (B 32) (B 32)]); have h2 := hS (Δ := [a1gRole2Ty, .prod (B 32) (B 32)])
  simp only [fgInit2Dsl, emptySimE, emptyAuthStE, fsMk, stMk, Expr.litUnit, Expr.litBool, Expr.litNat,
    Expr.noneE, Expr.listNil, a1g_v_size, a1g_bindV_size, a1g_sampleBoolC_size, Comp.size, Expr.size,
    a1g_pqxdhOps_opSize, bits_0]; omega

local macro "a1g_fin_size_simp" : tactic => `(tactic|
  simp only [fg2FinishDsl, fg2ExtractC, fg2InitDh1CandC, fg2RespCandC, fg2LogScanC, fg2FindMapC,
    fgFinish2Dsl, fgExtract2C, initDh1Cand2C, respCand2C, logScan2C, findMap2C,
    fg2PaDh1, fg2PaU, fg2PaV, pa2Dh1, pa2U, pa2V, fsLog, fsBase, fsPows, fsResp,
    stSpks, stSess, stPrin, sbSpkPk, sbSpkSk, sePeerSpk, seSid, seEkASk, peIkAPk,
    slice32, bytesEmpty, zero32, natEq, nat2Eq, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Comp.iteC, a1g_v_size, a1g_bindV_size, a1g_letV_size, a1g_caseOptV_size, a1g_findMV_size,
    a1g_mapMV_size, a1g_foldMV_size, a1g_eCaseOpt_size, a1g_eCaseSum_size, a1g_eFind_size,
    a1g_eMap_size, a1g_litBytes_size, a1g_bytesTakeK_size, a1g_bytesDrop_size, a1g_bytesLen_size,
    a1g_bytesBeq_size, a1g_queryPrimC_size, a1g_queryDdh_size, Comp.size, Expr.size,
    a1g_pqxdhOps_opSize, bits_0])

set_option linter.unusedSimpArgs false in
private theorem fg2FinishDsl_size_le (S : Setup) (K : Nat) :
    (fg2FinishDsl S K).size ≤ 10 * bits K + 10 * bits (min K S.N_dh) + 4 * bits (min K S.N_sess_tot) + 800 := by
  have hb : bits 32 = 6 ∧ bits 96 = 7 := by decide
  a1g_fin_size_simp; omega

set_option linter.unusedSimpArgs false in
private theorem fgFinish2Dsl_size_le (S : Setup) (K : Nat) :
    (fgFinish2Dsl S K).size ≤ 10 * bits K + 10 * bits (min K S.N_dh) + 4 * bits (min K S.N_sess_tot) + 800 := by
  have hb : bits 32 = 6 ∧ bits 96 = 7 := by decide
  a1g_fin_size_simp; omega

set_option linter.unusedSimpArgs false in
private theorem a1g_firstMsgADE_size {Γ : List (Ty pqSig)} (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) :
    (firstMsgADE ikA ikB eph pq).size = ikA.size + ikB.size + eph.size + 3 * pq.size + 36 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [firstMsgADE, pbBytesField, encEC, Expr.bytesAppend, Expr.bytesCons, Expr.litBytes,
    Expr.bytesVarint, Expr.bytesLen, Expr.litNat, Expr.size, a1g_ops_sum_opSize_inl,
    a1g_ops_sum_opSize_inr, a1g_pqBytesOps_opSize, a1g_pqU32Ops_opSize, a1g_pqxdhOps_opSize, hb0]
  dsimp only [pqxdhOps, Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]; omega

set_option maxRecDepth 100000 in
local macro "a1g_fgstep_size_simp" : tactic => `(tactic|
  simp (config := { maxSteps := 4000000 }) only [
    fgStepC, fgInitPrinC, fgGenSpkC, fgSendC, fg2StepC, fg2InitPrinC, fg2GenSpkC, fg2SendC,
    fgStep2C, fgInitPrin2C, fgGenSpk2C, fgSend2C, fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC,
    onBaseF, sendGuardE, isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC,
    patchC, rootPatchC, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paV, paDh1, paTI, paTS, fg2PaU, fg2PaV, fg2PaDh1, fg2PaTI, fg2PaSendOpk, fg2PaSendIdx,
    fg2PaTS, pa2U, pa2V, pa2Role, pa2TS, pa2Dh1, feP1, feP2, feP3, feP4, feSs, feDk,
    pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk, q4, bytesEmpty, slice32, zero32,
    emptySimE, initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB,
    roB, roRootB, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk, pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, a1g_firstMsgADE_size, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM, a1g_liftChal_size, a1g_v_size, a1g_letC_size, a1g_bindV_size, a1g_letV_size,
    a1g_caseOptV_size, a1g_caseSumV_size, a1g_findMV_size, a1g_anyMV_size, a1g_mapMV_size,
    a1g_foldMV_size, a1g_eLet_size, a1g_eCaseOpt_size, a1g_eCaseSum_size,
    a1g_eFind_size, a1g_eAny_size, a1g_eMap_size, a1g_litBytes_size, a1g_bytesAppend_size,
    a1g_bytesCons_size, a1g_bytesWiden_size, a1g_bytesTakeK_size, a1g_bytesDrop_size,
    a1g_bytesLen_size, a1g_bytesBeq_size, a1g_bytesVarint_size, a1g_u32OfNat_size, a1g_u32Beq_size,
    a1g_sampleBool_size, a1g_sampleBytes32_size, a1g_sampleRandom64_size, a1g_sampleDrKey96_size,
    a1g_sampleIndex_size, a1g_queryPrim_size, a1g_sampleBoolC_size, a1g_sampleBytes32C_size,
    a1g_sampleRandom64C_size, a1g_sampleDrKey96C_size, a1g_sampleIndexC_size, a1g_queryPrimC_size,
    a1g_queryChal_size, a1g_queryDdh_size, a1g_encEC_size, a1g_encKEM_size, Comp.size, Expr.size,
    a1g_pqxdhOps_opSize, bits_0, bits_1, ↓reduceIte, Bool.false_eq_true])

private theorem a1g_hb_consts :
    bits 32 = 6 ∧ bits 64 = 7 ∧ bits 96 = 7 ∧ bits 128 = 8 ∧ bits 160 = 8 ∧ bits 192 = 8 := by decide

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3200000 in
private theorem fgStepC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgStepC (Δ := Δ) S K pa sim q).size ≤
      105 * bits K + 45 * bits S.N_dh + 15 * bits S.N_sess_tot + 18500 := by
  a1g_fgstep_size_simp
  have hb_consts := a1g_hb_consts; obtain ⟨hNR, hSO, hSN⟩ := a1g_eff_le_dh S
  have := bits_mono hNR; have := bits_mono hSO; have := bits_mono hSN
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have : bits S.N_send_opk_tot ≤ bits S.N_dh := bits_mono (by omega)
  have : bits (min K S.N_dh) ≤ bits S.N_dh := bits_mono (Nat.min_le_right _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3200000 in
private theorem fg2StepC_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fg2StepC (Δ := Δ) S K pa sim q).size ≤ 105 * bits K + 45 * bits (min K S.N_dh) + 18500 := by
  a1g_fgstep_size_simp; have hb_consts := a1g_hb_consts; omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3200000 in
private theorem fgStep2C_size_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgStep2C (Δ := Δ) S K pa sim q).size ≤ 105 * bits K + 45 * bits (min K S.N_dh) + 18500 := by
  a1g_fgstep_size_simp; have hb_consts := a1g_hb_consts; omega

local macro "a1g_step_size_simp" : tactic => `(tactic|
  simp only [a1gStepC, a1gPreC, a1gInitPrinC, a1gGenSpkC,
    a1gStep2C, a1gPre2C, a1gInitPrin2C, a1gGenSpk2C, a1g_liftGdhComp_size, a1g_sigChalQ_dsl_size,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paV, paDh1, paTI, paTS, pa2U, pa2V, pa2Role, pa2TS, pa2Dh1,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    aNone, aInitPrin, aBundle, natEq, nat2Eq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Comp.iteC, a1g_v_size, a1g_letC_size, a1g_bindV_size,
    a1g_letV_size, a1g_caseOptV_size, a1g_caseSumV_size, a1g_eCaseOpt_size, a1g_eCaseSum_size,
    a1g_eFind_size, a1g_eAny_size, a1g_litBytes_size, a1g_u32OfNat_size,
    a1g_sampleBytes32C_size, a1g_sampleRandom64C_size, a1g_queryPrimC_size,
    a1g_encEC_size, a1g_encKEM_size, Comp.size, Expr.size, a1g_pqxdhOps_opSize, bits_0, bits_1])

set_option linter.unusedSimpArgs false in
theorem a1gStepC_size_le (S : Setup) (K : Nat) {Γs Γq Δ : List (Ty pqSig)} [Ext Γs Δ] [Ext Γq Δ]
    (st : Var Γs a1gStTy) (q : Var Γq authQueryTy) :
    (a1gStepC S K (Δ := Δ) st q).size ≤
      115 * bits K + 50 * bits S.N_dh + 15 * bits S.N_sess_tot + 20000 := by
  have hb1 : bits (nRecvEff S) ≤ bits S.N_dh := bits_mono (nRecvEff_le_N_dh S)
  have hFg := fgStepC_size_le S K (Γ₁ := paramsTy :: Δ) (Γ₂ := fgSimTy :: paramsTy :: Δ)
    (Γ₃ := Γq) (Δ := .unit :: (.sum RSB .unit) :: .nat :: fgSimTy :: paramsTy :: Δ) .vz .vz q
  a1g_step_size_simp; omega

set_option linter.unusedSimpArgs false in
private theorem a1gStep2C_size_le (S : Setup) (K : Nat) {Γs Γq Δ : List (Ty pqSig)}
    [Ext Γs Δ] [Ext Γq Δ] (st : Var Γs a1g2StTy) (q : Var Γq authQueryTy) :
    (a1gStep2C S K (Δ := Δ) st q).size ≤ 115 * bits K + 45 * bits (min K S.N_dh) + 20000 := by
  have hFg := fgStep2C_size_le S K (Γ₁ := a1gParams2Ty :: Δ) (Γ₂ := fgSimTy :: a1gParams2Ty :: Δ)
    (Γ₃ := Γq) (Δ := .unit :: (.sum RSB .unit) :: .nat :: fgSimTy :: a1gParams2Ty :: Δ) .vz .vz q
  a1g_step_size_simp; omega

set_option linter.unusedSimpArgs false in
private theorem a1g_fgAuthGapDhProg_size_le_clamped (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).size ≤
      120 * bits K + 60 * bits (min K S.N_dh) + 20 * bits (min K S.N_sess_tot) + 20000 := by
  have hI := fg2InitDsl_size_le S
  have hF := fg2FinishDsl_size_le S K
  have hSt := fg2StepC_size_le S K
    (Γ₁ := fg2ParamsTy :: [fg2GsTy, authQueryTy])
    (Γ₂ := fgSimTy :: fg2ParamsTy :: [fg2GsTy, authQueryTy])
    (Γ₃ := [fg2GsTy, authQueryTy])
    (Δ := fgSimTy :: fg2ParamsTy :: [fg2GsTy, authQueryTy])
    .vz .vz (.vs .vz)
  simp only [CostedReduction.size, fgAuthGapDhProg, fg2HandleDsl, authCodec,
    fg2PaDh1, fg2PaTI, fsBase, stPrin, peCorrupted, aNone, natEq,
    Expr.litBool, Expr.boolAnd, Comp.iteC,
    a1g_v_size, a1g_bindV_size, a1g_letV_size, a1g_eCaseOpt_size, a1g_eFind_size,
    Comp.size, Expr.size, a1g_pqxdhOps_opSize]
  omega

theorem fgAuthGapDhProg_size_le_v2 (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).size ≤ 200 * bits K + 20000 := by
  have h := a1g_fgAuthGapDhProg_size_le_clamped S K
  have hd : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have hs : bits (min K S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  omega

theorem fgAuthGapDhProg_size_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).size ≤
      120 * bits K + 60 * bits S.N_dh + 20 * bits S.N_sess_tot + 20000 := by
  have h := a1g_fgAuthGapDhProg_size_le_clamped S K
  have hd : bits (min K S.N_dh) ≤ bits S.N_dh := bits_mono (Nat.min_le_right _ _)
  have hs : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := bits_mono (Nat.min_le_right _ _)
  omega

set_option linter.unusedSimpArgs false in
private theorem fgAuth1KeyGapDhProg_size_le_clamped (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).size ≤
      125 * bits K + 55 * bits (min K S.N_dh) + 4 * bits (min K S.N_sess_tot) +
        bits (min K (min S.N_spk_tot S.N_recv)) + 21500 := by
  have hI := fgInit2Dsl_size_le S
  have hF := fgFinish2Dsl_size_le S K
  have hH := a1gStep2C_size_le S K (Γs := [a1g2StTy, authQueryTy])
    (Γq := [a1g2StTy, authQueryTy]) (Δ := [a1g2StTy, authQueryTy]) .vz (.vs .vz)
  simp only [CostedReduction.size, fgAuth1KeyGapDhProg, a1g2InitDsl, a1g2HandleDsl, a1g2FinishDsl,
    authCodec, a1g_liftGdhComp_size, a1g_renameComp_size,
    Expr.litNat, a1g_v_size, a1g_bindV_size, a1g_letV_size,
    Comp.size, Expr.size, a1g_pqxdhOps_opSize]
  omega

theorem fgAuth1KeyGapDhProg_size_le_v2 (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).size ≤ 209 * bits K + 21500 := by
  have h := fgAuth1KeyGapDhProg_size_le_clamped S K
  have hd : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have hs : bits (min K S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have hb : bits (min K (min S.N_spk_tot S.N_recv)) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  omega

theorem fgAuth1KeyGapDhProg_size_le (S : Setup) (K : Nat) :
    (fgAuth1KeyGapDhProg S K).size ≤
      125 * bits K + 65 * bits S.N_dh + 19 * bits S.N_sess_tot + 21500 := by
  have h := fgAuth1KeyGapDhProg_size_le_clamped S K
  have hd : bits (min K S.N_dh) ≤ bits S.N_dh := bits_mono (Nat.min_le_right _ _)
  have hs : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := bits_mono (Nat.min_le_right _ _)
  have hb : bits (min K (min S.N_spk_tot S.N_recv)) ≤ bits S.N_dh := by
    apply bits_mono
    have h1 : min K (min S.N_spk_tot S.N_recv) ≤ S.N_spk_tot :=
      le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    unfold Setup.N_dh; omega
  omega

private theorem bits_q_total_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    bits b.q_total ≤ bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  apply bits_mono
  unfold _root_.SignalPqxdh.Security.stepCostBudget; dsimp only
  have hmul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

theorem fgAuthGapDhProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgAuthGapDhProg S b.q_total).size ≤
      20000 + 200 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hP := fgAuthGapDhProg_size_le_v2 S b.q_total
  have hq := bits_q_total_le_stepCostBudget S b
  omega

theorem fgAuth1KeyGapDhProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgAuth1KeyGapDhProg S b.q_total).size ≤
      21500 + 209 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hP := fgAuth1KeyGapDhProg_size_le_v2 S b.q_total
  have hq := bits_q_total_le_stepCostBudget S b
  omega

/-- Run-local output block-size bound for `fgAuth1KeyGapDhProg`. -/
theorem fgAuth1KeyGapDhProg_blockBounded_when (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (fun q => SignalPqxdh.isGameQuery q = true) b.q_total)
    (hfit : ∀ u, AllGameQueriesFit ℓ (authCodec S) (A u))
    (x : (Ty.prod (B 32) (B 32)).denote)
    (hx : ValFits ℓ (Ty.prod (B 32) (B 32)) x)
    (y : Bytes)
    (hy : y ∈ supportWhen (pqSigAndDdhIface.AnswerFits ℓ)
      ((fgAuth1KeyGapDhProg S b.q_total).eval A x)) :
    ValFits (SignalPqxdh.LegacyCosted.outputSizeBudget S b ℓ) (B 32) y := by
  rw [a1g_valFits_iff_fits]
  have hx' : (Ty.prod (B 32) (B 32)).Fits ℓ x := (a1g_valFits_iff_fits ℓ _ _).1 hx
  have hA' : ∀ u, (A u).IsQueryBoundP
      (ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  have hEval := (fgAuth1KeyGapDhProg S b.q_total).fits_eval_when
    pqO_sizeHonest SignalPqxdh.LegacyCosted.pqSamplers_sizeHonest ℓ ℓ 0 (fun _ => trivial)
    A b.q_total ℓ hA' hfit x hx' y hy
  have hCost := fgAuth1KeyGapDhProg_totalCost_le S b
  have hNq := le_trans
    (a1g_gred_nq_le_totalCost a1g_one_le_pqChalIface_qCost a1g_one_le_pqSamplers_sCost
      (fgAuth1KeyGapDhProg S b.q_total) b.q_total)
    hCost
  refine Ty.fits_mono ?_ (B 32) y hEval
  unfold SignalPqxdh.LegacyCosted.outputSizeBudget SignalPqxdh.LegacyCosted.stepCostBudget at *
  have hM := Nat.mul_le_mul_right ℓ hNq
  nlinarith

end Auth1KeySizeAndWhen

end SignalPqxdh.Security.ReductionDsl.AuthHs
