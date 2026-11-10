/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCr
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs

/-!
# Cost and Query Bounds for `shcrReductionAuthProg`

Syntactic step-cost and primitive-query bounds for the two-stage `KemShCr` reduction
`shcrReductionAuthProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl

theorem bits_le_succ (n : Nat) : bits n ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have := bits_le_self hpos; omega

theorem nRecvEff_le_N_dh (S : Setup) : nRecvEff S ≤ S.N_dh := by
  unfold nRecvEff Setup.N_dh Setup.N_spk_tot
  split_ifs with h0
  · omega
  · have h1 : 1 ≤ S.N_id := by omega
    have h2 : 1 * S.N_recv ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv h1
    omega

@[simp] theorem preCheckC_costUB (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (preCheckC (Δ := Δ) S K opk st x).costUB =
      (if opk then 534 else 535) + 321 * K + 824 * min K S.N_dh := by
  cases opk <;>
  · simp only [preCheckC, koskBundleOkC_costUB, findHonestC_costUB, sidEq_costUB,
      bindV, letV, caseOptV, eFind, eAny, eCaseOpt, Comp.costUB_letC,
      natEq, stSecb, stPrin, stUsedS, peCorrupted, buIkB,
      costUB_bytesLen, costUB_bytesBeq, PNat.val_ofNat, bits_32,
      Bool.false_eq_true, ite_true, ite_false, costUB_v, Comp.costUB, Expr.costUB]
    omega

@[simp] theorem checkSigsC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).costUB = 3459 + 206 * min K S.N_dh := by
  simp only [checkSigsC, resolveSigPkC_costUB, bindV,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    costUB_encEC, costUB_encKEM, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem finishC_costUB (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (finishC (Δ := Δ) K st d ks sc).costUB = 4603 + 3772 * K := by
  simp only [finishC, hkdfOrRoC_true_costUB, rootRoC_costUB, firstMsgADE_costUB, buildSecretsE_costUB,
    bindV, letV, caseOptV, eAny, eCaseOpt, Comp.costUB_letC,
    natEq, getDBytes, optFst, optSnd,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stAdv, stMk, stUpd,
    seMk, peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
    buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
    hdMk, pdSid, pdBu, pdM0, pdM1, pdUI,
    aNone, aSendFresh, aSendUnfresh,
    costUB_bytesBeq, costUB_litBytes, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, List.length_nil, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem shcrFinC_costUB {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (sid : Expr pqxdhOps Δ sessionIdTy)
    (pqspkPk : Expr pqxdhOps Δ (B 1568)) (sc : Var Γ₂ (.prod (B 32) (B 1568)))
    (out : Var Γ₃ FinTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (shcrFinC s sid pqspkPk sc out).costUB = sid.costUB + pqspkPk.costUB + 158 := by
  simp only [shcrFinC, letV, caseOptV, Comp.costUB_letC,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    bits_1, costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem onBase_costUB {Γ₁ Δ : List (Ty pqSig)} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (authStateTy :: Δ) authStateTy) → Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS) :
    (onBase s br).costUB = (br .vz).costUB + 70 := by
  simp only [onBase, bindV, letV, Comp.costUB_letC,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem shcrGenSpkB_costUB_le_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrGenSpkB (Δ := Δ) S K s x).costUB ≤ 25000 + 100 * K := by
  simp only [shcrGenSpkB, onBase_costUB, genSpkB_costUB,
    bindV, caseOptV, eAny, eFind, nat2Eq, natEq,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    peIkAPk, peSecIKAsign, buMk, sbMk, aNone, aBundle,
    costUB_encEC, costUB_encKEM, costUB_u32OfNat,
    costUB_sampleBytes32, costUB_sampleRandom64, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem shcrGenSpkB_costUB_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrGenSpkB (Δ := Δ) S K s x).costUB ≤ 25000 + 100 * K + bits (nRecvEff S) :=
  Nat.le_trans (shcrGenSpkB_costUB_le_tight S K s x) (Nat.le_add_right _ _)

@[simp] theorem shcrSendC_costUB (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrSendC (Δ := Δ) S K opk s x).costUB = 12238 + 4093 * K + 1030 * min K S.N_dh := by
  cases opk <;>
  · simp only [shcrSendC, sendGuardE, preCheckC_costUB, checkSigsC_costUB, finishC_costUB,
      shcrFinC_costUB, bindV, letV, caseOptV, Comp.costUB_letC,
      isSomeE, buOpkB, buPqspkB, pdSid, pdBu,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
      aNone, costUB_sampleBytes32, costUB_queryPrim,
      Ty.wd, PNat.val_ofNat, bits_1, Bool.false_eq_true, ite_true, ite_false,
      costUB_v, Comp.costUB, Expr.costUB]
    omega

theorem shcrAcceptB_true_costUB_le_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K true s x).costUB ≤
      16000 + 900 * K + 412 * min K S.N_dh := by
  simp only [shcrAcceptB, onBase_costUB, recvB_true_costUB,
    bindV, letV, caseOptV, eFind, Comp.costUB_letC, nat2Eq, natEq,
    stSpks, pmHdr, sbPqspkSk, sbPqspkPk, hdKemCt,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    costUB_queryPrim, Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem shcrAcceptB_true_costUB_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K true s x).costUB ≤
      16000 + 900 * K + 412 * S.N_dh + bits (nRecvEff S) := by
  have h1 := shcrAcceptB_true_costUB_le_tight S K (Δ := Δ) s x
  have h2 := Nat.min_le_right K S.N_dh
  omega

theorem shcrAcceptB_false_costUB_le_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K false s x).costUB ≤
      16000 + 900 * K + 412 * min K S.N_dh := by
  simp only [shcrAcceptB, onBase_costUB, recvB_false_costUB,
    bindV, letV, caseOptV, eFind, Comp.costUB_letC, nat2Eq, natEq,
    stSpks, pmHdr, sbPqspkSk, sbPqspkPk, hdKemCt,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    costUB_queryPrim, Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem shcrAcceptB_false_costUB_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K false s x).costUB ≤
      16000 + 900 * K + 412 * S.N_dh + bits (nRecvEff S) := by
  have h1 := shcrAcceptB_false_costUB_le_tight S K (Δ := Δ) s x
  have h2 := Nat.min_le_right K S.N_dh
  omega

@[simp] theorem tryPauseC_costUB (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (tryPauseC (Δ := Δ) S K opk s x).costUB = 4049 + 321 * K + 1030 * min K S.N_dh := by
  cases opk <;>
  · simp only [tryPauseC, sendGuardE, preCheckC_costUB, checkSigsC_costUB,
      bindV, letV, caseOptV, Comp.costUB_letC, natEq, isSomeE, buOpkB, pdBu,
      scBase, scCnt, scSIdx, Bool.false_eq_true, ite_true, ite_false,
      costUB_v, Comp.costUB, Expr.costUB]
    omega

private theorem caseSumV_costUB_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List (Ty pqSig)} {a b c : Ty pqSig} (q : Var Γ (.sum a b)) [Ext Γ Δ]
    (l : Var (a :: Δ) a → Comp pqxdhOps I (a :: Δ) c)
    (r : Var (b :: Δ) b → Comp pqxdhOps I (b :: Δ) c)
    {M N : Nat} (hl : (l .vz).costUB ≤ M) (hr : (r .vz).costUB ≤ N) :
    (caseSumV (v q) l r).costUB ≤ M + N + 2 := by
  simp only [caseSumV, costUB_v, Comp.costUB]
  omega

theorem shcrPostC_costUB_le_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).costUB ≤
      95000 + 18000 * K + 3000 * min K S.N_dh := by
  unfold shcrPostC
  refine le_trans
    (caseSumV_costUB_le _ _ _ (by simp only [onBase_costUB, initPrinB_costUB]; exact le_rfl) <|
     caseSumV_costUB_le _ _ _ (by simp only [onBase_costUB, corruptB_costUB]; exact le_rfl) <|
     caseSumV_costUB_le _ _ _ (shcrGenSpkB_costUB_le_tight S K _ _) <|
     caseSumV_costUB_le _ _ _ (by simp only [onBase_costUB, genOpkB_costUB]; exact le_rfl) <|
     caseSumV_costUB_le _ _ _ (by simp only [shcrSendC_costUB]; exact le_rfl) <|
     caseSumV_costUB_le _ _ _ (by simp only [shcrSendC_costUB]; exact le_rfl) <|
     caseSumV_costUB_le _ _ _ (shcrAcceptB_true_costUB_le_tight S K _ _) <|
     caseSumV_costUB_le _ _ _ (shcrAcceptB_false_costUB_le_tight S K _ _) <|
     caseSumV_costUB_le _ _ _ (by simp only [onBase_costUB, roB_costUB]; exact le_rfl) <|
     caseSumV_costUB_le _ _ _ (by simp only [onBase_costUB, roRootB_costUB]; exact le_rfl) <|
     caseSumV_costUB_le _ _ _ (by simp only [aNone, costUB_v, Comp.costUB, Expr.costUB]; exact le_rfl) <|
     by simp only [onBase_costUB, registerB_costUB]; exact le_rfl)
    (by omega)

theorem shcrPostC_costUB_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).costUB ≤
      95000 + 18000 * K + 3000 * S.N_dh + 3 * bits (nRecvEff S) := by
  have h1 := shcrPostC_costUB_le_tight S K (Δ := Δ) s q
  have h2 := Nat.min_le_right K S.N_dh
  omega

theorem pauseCheckC_costUB_le_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (pauseCheckC (Δ := Δ) S K s q).costUB ≤ 9000 + 700 * K + 2100 * min K S.N_dh := by
  simp only [pauseCheckC, tryPauseC_costUB, caseSumV, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem pauseCheckC_costUB_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (pauseCheckC (Δ := Δ) S K s q).costUB ≤ 9000 + 700 * K + 2100 * S.N_dh := by
  have h1 := pauseCheckC_costUB_le_tight S K (Δ := Δ) s q
  have h2 := Nat.min_le_right K S.N_dh
  omega

theorem shcr_handlePre_cost_le_tight (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).handlePre.cost ≤
      120000 + 22000 * K + 6000 * min K S.N_dh := by
  dsimp only [shcrReductionAuthProg, authCodec]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  have h1 := pauseCheckC_costUB_le_tight (Δ := [shcrStTy, authQueryTy]) S K
    (.vz : Var [shcrStTy, authQueryTy] shcrStTy)
    (.vz : Var [authQueryTy] authQueryTy)
  have h2 := shcrPostC_costUB_le_tight (Δ := .opt pauseTy :: [shcrStTy, authQueryTy]) S K
    (.vz : Var [shcrStTy, authQueryTy] shcrStTy)
    (.vz : Var [authQueryTy] authQueryTy)
  simp only [shcrPreC, bindV, caseOptV, buPqspkB, pdBu, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem shcr_handlePre_cost_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).handlePre.cost ≤
      120000 + 22000 * K + 6000 * S.N_dh + 3 * bits (nRecvEff S) := by
  have h1 := shcr_handlePre_cost_le_tight S Q K
  have h2 := Nat.min_le_right K S.N_dh
  omega

theorem shcr_handlePost_cost_le_tight (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).handlePost.cost ≤
      100000 + 20000 * K + 4500 * min K S.N_dh := by
  dsimp only [shcrReductionAuthProg, authCodec]
  exact Nat.le_trans (Comp.cost_le_costUB _)
    (Nat.le_trans
      (shcrPostC_costUB_le_tight S K
        (.vz : Var [shcrStTy, authQueryTy] shcrStTy)
        (.vz : Var [authQueryTy] authQueryTy))
      (by omega))

theorem shcr_handlePost_cost_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).handlePost.cost ≤
      100000 + 20000 * K + 4500 * S.N_dh + 3 * bits (nRecvEff S) := by
  have h1 := shcr_handlePost_cost_le_tight S Q K
  have h2 := Nat.min_le_right K S.N_dh
  omega

theorem shcr_resume_cost_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).resume.cost ≤ 10000 + 4500 * K := by
  dsimp only [shcrReductionAuthProg, authCodec]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [
    shcrResumeC, finishC_costUB, shcrFinC_costUB,
    bindV, letV, Comp.costUB_letC,
    buPqspkB, pdSid, pdBu,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scMk, scUpd,
    costUB_sampleBytes32, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem shcr_finish_cost_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).finish.cost ≤ 100 + 12000 * Q := by
  dsimp only [shcrReductionAuthProg, authCodec]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [
    optBytesEq_costUB, shcrExtractC,
    bindV, findMV, eCaseOpt,
    scTSk, scTPk, scRR, scChosen, rrCt,
    costUB_bytesBeq, costUB_queryPrim,
    Ty.wd, costUB_v, Comp.costUB, Expr.costUB, PNat.val_ofNat]
  omega

private theorem log2_mul_ge {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.log 2 a + Nat.log 2 b ≤ Nat.log 2 (a * b) := by
  apply Nat.le_log_of_pow_le (by decide)
  rw [Nat.pow_add]
  exact Nat.mul_le_mul (Nat.pow_log_le_self 2 (by omega)) (Nat.pow_log_le_self 2 (by omega))

theorem shcr_init_cost_le_tight (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).init.cost ≤
      200 + 4 * Nat.log 2 S.N_dh + 4 * Nat.log 2 S.N_sess_tot := by
  dsimp only [shcrReductionAuthProg, authCodec]
  split_ifs with h0
  · refine Nat.le_trans (Comp.cost_le_costUB _) ?_
    simp only [emptyAuthStE, stMk, scMk, bindV, costUB_sampleBool,
      costUB_v, Comp.costUB, Expr.costUB, bits_0]
    omega
  · refine Nat.le_trans (Comp.cost_le_costUB _) ?_
    have hspk : 1 ≤ S.N_spk_tot := by
      rcases Nat.eq_zero_or_pos S.N_spk_tot with h | h
      · exact absurd (by simp [h]) h0
      · omega
    have hsend : 1 ≤ S.N_send_tot := by
      rcases Nat.eq_zero_or_pos S.N_send_tot with h | h
      · exact absurd (by simp [h]) h0
      · omega
    have hid : 1 ≤ S.N_id := by
      unfold Setup.N_spk_tot at hspk
      rcases Nat.eq_zero_or_pos S.N_id with h | h
      · simp [h] at hspk
      · omega
    have hrecv : 1 ≤ S.N_recv := by
      unfold Setup.N_spk_tot at hspk
      rcases Nat.eq_zero_or_pos S.N_recv with h | h
      · simp [h] at hspk
      · omega
    have hid_le : S.N_id ≤ S.N_dh := by
      have := Nat.le_mul_of_pos_right S.N_id hrecv
      unfold Setup.N_dh Setup.N_spk_tot; omega
    have hrecv_le : S.N_recv ≤ S.N_dh := by
      have := Nat.le_mul_of_pos_left S.N_recv hid
      unfold Setup.N_dh Setup.N_spk_tot; omega
    have hsend_le : S.N_send_tot ≤ S.N_sess_tot := by
      unfold Setup.N_sess_tot; omega
    have hl1 : Nat.log 2 S.N_id ≤ Nat.log 2 S.N_dh := Nat.log_mono_right hid_le
    have hl2 : Nat.log 2 S.N_recv ≤ Nat.log 2 S.N_dh := Nat.log_mono_right hrecv_le
    have hl3 : Nat.log 2 S.N_send_tot ≤ Nat.log 2 S.N_sess_tot := Nat.log_mono_right hsend_le
    have hl0 : Nat.log 2 0 = 0 := rfl
    simp only [emptyAuthStE, stMk, scMk, bindV,
      costUB_sampleIndex, costUB_sampleBool,
      costUB_v, Comp.costUB, Expr.costUB, bits]
    omega

theorem shcr_init_cost_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).init.cost ≤
      100 + bits (S.N_spk_tot * S.N_send_tot) + 2 * bits S.N_send_tot := by
  dsimp only [shcrReductionAuthProg, authCodec]
  split_ifs with h0
  · refine Nat.le_trans (Comp.cost_le_costUB _) ?_
    simp only [emptyAuthStE, stMk, scMk, bindV, costUB_sampleBool,
      costUB_v, Comp.costUB, Expr.costUB, bits_0]
    omega
  · refine Nat.le_trans (Comp.cost_le_costUB _) ?_
    have hspk : 1 ≤ S.N_spk_tot := by
      rcases Nat.eq_zero_or_pos S.N_spk_tot with h | h
      · exact absurd (by simp [h]) h0
      · omega
    have hsend : 1 ≤ S.N_send_tot := by
      rcases Nat.eq_zero_or_pos S.N_send_tot with h | h
      · exact absurd (by simp [h]) h0
      · omega
    have hid : 1 ≤ S.N_id := by
      unfold Setup.N_spk_tot at hspk
      rcases Nat.eq_zero_or_pos S.N_id with h | h
      · simp [h] at hspk
      · omega
    have hrecv : 1 ≤ S.N_recv := by
      unfold Setup.N_spk_tot at hspk
      rcases Nat.eq_zero_or_pos S.N_recv with h | h
      · simp [h] at hspk
      · omega
    have h1 : Nat.log 2 S.N_id + Nat.log 2 S.N_recv ≤ Nat.log 2 S.N_spk_tot := by
      simpa [Setup.N_spk_tot] using log2_mul_ge hid hrecv
    have h2 : Nat.log 2 S.N_spk_tot + Nat.log 2 S.N_send_tot ≤
        Nat.log 2 (S.N_spk_tot * S.N_send_tot) := log2_mul_ge hspk hsend
    have hl0 : Nat.log 2 0 = 0 := rfl
    simp only [emptyAuthStE, stMk, scMk, bindV,
      costUB_sampleIndex, costUB_sampleBool,
      costUB_v, Comp.costUB, Expr.costUB, bits]
    omega

theorem shcr_chDone_cost_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).chDone.cost ≤ 20 := by
  dsimp only [shcrReductionAuthProg, authCodec]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [Comp.costUB, Expr.costUB]
  omega

@[simp] theorem preCheckC_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (preCheckC (Δ := Δ) S K opk st x).queries primW primWS = 3 + 8 * min K S.N_dh := by
  simp only [preCheckC, koskBundleOkC_queries, findHonestC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queries]
  omega

@[simp] theorem checkSigsC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).queries primW primWS = 2 + 2 * min K S.N_dh := by
  simp only [checkSigsC, resolveSigPkC_queries, bindV, Comp.queryPrim, primW, Comp.queries]
  omega

@[simp] theorem finishC_queries (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (finishC (Δ := Δ) K st d ks sc).queries primW primWS = 12 := by
  simp only [finishC, hkdfOrRoC_true_queries, rootRoC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries]
  omega

@[simp] theorem shcrFinC_queries {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (sid : Expr pqxdhOps Δ sessionIdTy)
    (pqspkPk : Expr pqxdhOps Δ (B 1568)) (sc : Var Γ₂ (.prod (B 32) (B 1568)))
    (out : Var Γ₃ FinTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (shcrFinC s sid pqspkPk sc out).queries primW primWS = 0 := by
  simp [shcrFinC, letV, caseOptV, Comp.queries]

@[simp] theorem onBase_queries {Γ₁ Δ : List (Ty pqSig)} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (authStateTy :: Δ) authStateTy) → Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS) :
    (onBase s br).queries primW primWS = (br .vz).queries primW primWS := by
  simp [onBase, bindV, letV, Comp.queries]

@[simp] theorem shcrGenSpkB_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrGenSpkB (Δ := Δ) S K s x).queries primW primWS = 4 := by
  simp [shcrGenSpkB, bindV, caseOptV, Comp.sampleBytes32, Comp.sampleRandom64, Comp.queryPrim,
    primW, primWS, Comp.queries]

@[simp] theorem shcrSendC_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrSendC (Δ := Δ) S K opk s x).queries primW primWS = 18 + 10 * min K S.N_dh := by
  simp only [shcrSendC, preCheckC_queries, checkSigsC_queries, finishC_queries, shcrFinC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.sampleBytes32, Comp.queryPrim,
    primW, primWS, Comp.queries]
  omega

@[simp] theorem shcrAcceptB_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K true s x).queries primW primWS = 15 + 4 * min K S.N_dh := by
  simp only [shcrAcceptB, onBase_queries, recvB_true_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries]
  omega

@[simp] theorem shcrAcceptB_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K false s x).queries primW primWS = 14 + 4 * min K S.N_dh := by
  simp only [shcrAcceptB, onBase_queries, recvB_false_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries]
  omega

@[simp] theorem tryPauseC_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (tryPauseC (Δ := Δ) S K opk s x).queries primW primWS = 5 + 10 * min K S.N_dh := by
  simp only [tryPauseC, preCheckC_queries, checkSigsC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queries]
  omega

theorem shcr_handlePre_queries_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).handlePre.queries primW primWS ≤ 91 + 48 * S.N_dh := by
  dsimp only [shcrReductionAuthProg, authCodec]
  simp only [
    shcrPreC, pauseCheckC, shcrPostC,
    tryPauseC_queries, shcrGenSpkB_queries, shcrSendC_queries,
    shcrAcceptB_true_queries, shcrAcceptB_false_queries, onBase_queries,
    initPrinB_queries, corruptB_queries, genOpkB_queries, registerB_queries,
    roB_queries, roRootB_queries,
    bindV, caseOptV, caseSumV, Comp.queries]
  have := Nat.min_le_right K S.N_dh
  omega

theorem shcr_handlePost_queries_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).handlePost.queries primW primWS ≤ 81 + 28 * S.N_dh := by
  dsimp only [shcrReductionAuthProg, authCodec]
  simp only [
    shcrPostC,
    shcrGenSpkB_queries, shcrSendC_queries,
    shcrAcceptB_true_queries, shcrAcceptB_false_queries, onBase_queries,
    initPrinB_queries, corruptB_queries, genOpkB_queries, registerB_queries,
    roB_queries, roRootB_queries,
    caseSumV, Comp.queries]
  have := Nat.min_le_right K S.N_dh
  omega

theorem shcr_resume_queries (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).resume.queries primW primWS = 12 := by
  dsimp only [shcrReductionAuthProg, authCodec]
  simp only [
    shcrResumeC, finishC_queries, shcrFinC_queries,
    bindV, letV, Comp.queries_letC, Comp.sampleBytes32,
    primWS, Comp.queries]

theorem shcr_finish_queries (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).finish.queries primW primWS = Q := by
  simp [shcrReductionAuthProg, authCodec, shcrExtractC, bindV, findMV,
    Comp.queryPrim, primW, Comp.queries]

theorem shcr_init_queries (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).init.queries primW primWS = 0 := by
  dsimp only [shcrReductionAuthProg, authCodec]
  split_ifs <;> simp [bindV, Comp.sampleIndex, Comp.sampleBool, primWS, Comp.queries]

theorem shcr_chDone_queries (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).chDone.queries primW primWS = 0 := by
  simp [shcrReductionAuthProg, authCodec, Comp.queries]

theorem shcrReductionAuthProg_totalCost_le_sec (S : Setup) (b : QueryBudget) :
    (shcrReductionAuthProg S b.q_total b.q_total).totalCost b.q_total ≤
      SignalPqxdh.Security.stepCostBudget S b := by
  have hPre := shcr_handlePre_cost_le_tight S b.q_total b.q_total
  have hPost := shcr_handlePost_cost_le_tight S b.q_total b.q_total
  have hRes := shcr_resume_cost_le S b.q_total b.q_total
  have hFin := shcr_finish_cost_le S b.q_total b.q_total
  have hIni := shcr_init_cost_le_tight S b.q_total b.q_total
  have hDef := shcr_chDone_cost_le S b.q_total b.q_total
  change (shcrReductionAuthProg S b.q_total b.q_total).init.cost +
      b.q_total * max 1 (max (shcrReductionAuthProg S b.q_total b.q_total).handlePre.cost
        (shcrReductionAuthProg S b.q_total b.q_total).handlePost.cost + 32) +
      max (shcrReductionAuthProg S b.q_total b.q_total).chDone.cost
        (shcrReductionAuthProg S b.q_total b.q_total).resume.cost +
      (shcrReductionAuthProg S b.q_total b.q_total).finish.cost ≤
        SignalPqxdh.Security.stepCostBudget S b
  generalize (shcrReductionAuthProg S b.q_total b.q_total).init.cost = cInit at hIni ⊢
  generalize (shcrReductionAuthProg S b.q_total b.q_total).handlePre.cost = cPre at hPre ⊢
  generalize (shcrReductionAuthProg S b.q_total b.q_total).handlePost.cost = cPost at hPost ⊢
  generalize (shcrReductionAuthProg S b.q_total b.q_total).chDone.cost = cDone at hDef ⊢
  generalize (shcrReductionAuthProg S b.q_total b.q_total).resume.cost = cRes at hRes ⊢
  generalize (shcrReductionAuthProg S b.q_total b.q_total).finish.cost = cFin at hFin ⊢
  unfold SignalPqxdh.Security.stepCostBudget
  dsimp only
  set M_dh := min b.q_total S.N_dh
  set M_sess := min b.q_total S.N_sess_tot
  set L_dh := Nat.log 2 S.N_dh
  set L_sess := Nat.log 2 S.N_sess_tot
  generalize b.q_total = q at *
  have hcH : max 1 (max cPre cPost + 32) ≤ 120035 + 22000 * q + 6000 * M_dh := by omega
  have hqH : q * max 1 (max cPre cPost + 32) ≤ q * (120035 + 22000 * q + 6000 * M_dh) :=
    Nat.mul_le_mul_left q hcH
  have hMid : max cDone cRes ≤ 10000 + 4500 * q := by omega
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · nlinarith [Nat.zero_le (M_dh ^ 2), Nat.zero_le (M_dh * M_sess)]
  · have hqq : q ≤ q * q := Nat.le_mul_of_pos_left q hq
    nlinarith [Nat.zero_le (q * M_dh), Nat.zero_le (q * M_sess),
      Nat.zero_le (q * L_dh), Nat.zero_le (q * L_sess),
      Nat.zero_le (M_dh ^ 2), Nat.zero_le (M_dh * M_sess)]

theorem shcrReductionAuthProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (shcrReductionAuthProg S b.q_total b.q_total).totalCost b.q_total ≤ stepCostBudget S b := by
  refine Nat.le_trans (shcrReductionAuthProg_totalCost_le_sec S b) ?_
  unfold SignalPqxdh.Security.stepCostBudget stepCostBudget
  dsimp only
  have hMdh : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hMsess : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hLdh : Nat.log 2 S.N_dh ≤ S.N_dh := Nat.log_le_self 2 S.N_dh
  have hLsess : Nat.log 2 S.N_sess_tot ≤ S.N_sess_tot := Nat.log_le_self 2 S.N_sess_tot
  set M_dh := min b.q_total S.N_dh
  set M_sess := min b.q_total S.N_sess_tot
  set L_dh := Nat.log 2 S.N_dh
  set L_sess := Nat.log 2 S.N_sess_tot
  generalize b.q_total = q at *
  have hSq : M_dh ^ 2 ≤ S.N_dh ^ 2 := Nat.pow_le_pow_left hMdh 2
  have hMul : M_dh * M_sess ≤ S.N_dh * S.N_sess_tot := Nat.mul_le_mul hMdh hMsess
  nlinarith [Nat.mul_le_mul_left (q + 1) (Nat.add_le_add hMdh hMsess),
    Nat.mul_le_mul_left (q + 1) (Nat.add_le_add hLdh hLsess)]

theorem shcrReductionAuthProg_totalQueries_le (S : Setup) (b : QueryBudget) :
    (shcrReductionAuthProg S b.q_total b.q_total).totalQueries primW primWS b.q_total ≤
      primQueryBudget S b := by
  dsimp only [TwoStageCostedReduction.totalQueries]
  have hPre := shcr_handlePre_queries_le S b.q_total b.q_total
  have hPost := shcr_handlePost_queries_le S b.q_total b.q_total
  have hRes := shcr_resume_queries S b.q_total b.q_total
  have hFin := shcr_finish_queries S b.q_total b.q_total
  have hIni := shcr_init_queries S b.q_total b.q_total
  have hDef := shcr_chDone_queries S b.q_total b.q_total
  rw [hIni, hDef, hRes, hFin]
  generalize (shcrReductionAuthProg S b.q_total b.q_total).handlePre.queries primW primWS =
    qPre at hPre ⊢
  generalize (shcrReductionAuthProg S b.q_total b.q_total).handlePost.queries primW primWS =
    qPost at hPost ⊢
  unfold primQueryBudget
  generalize b.q_total = q at *
  have hqH : max qPre qPost ≤ 91 + 48 * S.N_dh := max_le hPre (by omega)
  have hqqH : q * max qPre qPost ≤ q * (91 + 48 * S.N_dh) := Nat.mul_le_mul_left q hqH
  have hMid : max 0 12 = 12 := rfl
  rw [hMid]
  nlinarith

end SignalPqxdh.Security.ReductionDsl.AuthHs
