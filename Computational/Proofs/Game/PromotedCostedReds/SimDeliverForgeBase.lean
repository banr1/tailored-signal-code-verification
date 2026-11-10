/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim
public import Computational.Proofs.HeadlineV1.SendShortC
public import Computational.Proofs.ReductionDsl.Fig8Atomic
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Outer Loop, Cost, and Program-Size Bounds for `SimDeliverForge`

Assembles single-session `simDeliverForge` costed reduction programs from a single-query step
computation, bounds their execution cost and syntactic description bit-length (`atomicDFRedDescBits`),
and defines the `SimDeliverForgeAtomicStepBundle` contract.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeBase

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Expr Comp GameCodec CostedReduction bits reductionSizeBudget
  isGameQuery atomicSig atomicSamplers atomicSessionOps fig8SmIfaceDF e2eSessionCodec
  B PB BV128 BV256 U64 PK PlainT PtT GhostStT smQT smRT fig8CtT
  fig8HdrT fsRecvStT lctT wireSaltCtT)
open _root_.CryptoGames (Party)
open CryptoGames.SM (posTy)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM.Construction.DeliverForge
  (specDF MakesAtMostQueriesDF forgeGuessedAdvantageCellPaper sameHdrScheme challSimDF'Paper)
open CryptoGames.Ratchet.LibsignalInst (lFig8 LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalSession (ratchetCostBudget ratchetCostBudget_pos GRedBounded)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds gRedBounded_of_bounds_const)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge
  (bits_mono bits_mul_le size_le_budget_of_log_cost)
open CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF GuardedSMDFShort)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes idsOf paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSamplers_sizeHonest atomicSessionOps_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (sessPureOp sessSpqrKemOp atomicDraw256 atomicDraw256_cost atomicDraw256_queries_zero)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (session_cost_le_ratchetCostBudget dummyBoolSessionRed
   dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits
   atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits
   descBitBudget ratchetDescBudget ratchetDescBudget_le_reductionSizeBudget
   red_size_le_of_atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simRecT ghostChainT initSimMirE keptUnknownE initSimCE cost_initSimCE)
open Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (dfFullT atomicTyDescBits_dfFullT simDeliverForgeInitC simDeliverForgeFinishC
   simDeliverForgeProgOfStep)

export Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (dfFullT dfFullEnc dfFullDec dfFullDec_dfFullEnc atomicTyDescBits_dfFullT)
export Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (simDeliverForgeInitImpl simDeliverForgeInitC simDeliverForgeInitC_eval
   simDeliverForgeFinishC simDeliverForgeFinishC_eval)
export Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
  (simDeliverForgeProgOfStep simDeliverForgeProgOfStep_eval_san
   simDeliverForgeProgOfStep_eval_sanQ)

abbrev SimDeliverForgeRedProg (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (ℓ : ℕ)
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) : Type :=
  CostedReduction
    (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (fig8SmIfaceDF ℓ Pt)
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (e2eSessionCodec ℓ Pt)
    .unit .unit .bool .bool

section LoopAndCost

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem simDeliverForgeInitC_queries_zero (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (w : (fig8SmIfaceDF ℓ Pt).Tag → ℕ) :
    (simDeliverForgeInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).queries w (fun _ => 0) = 0 := by
  simp [simDeliverForgeInitC, Comp.queries, atomicDraw256_queries_zero]

theorem simDeliverForgeInitC_cost_le (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simDeliverForgeInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 610 := by
  let pqA : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) [BV256, .unit] (B 32) :=
    sessSpqrKemOp .spqrV1InitOp (.pair (.bool true) (.var .zero))
  let pqB : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) [BV256, .unit] (B 32) :=
    sessSpqrKemOp .spqrV1InitOp (.pair (.bool false) (.var .zero))
  have hc := cost_initSimCE pqA pqB
  have hcA : pqA.cost = 213 := rfl
  have hcB : pqB.cost = 213 := rfl
  have hdraw := atomicDraw256_cost (ℓ := ℓ) (Pt := Pt)
    (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (I := fig8SmIfaceDF ℓ Pt) (Γ := [.unit]) rfl
  dsimp only [simDeliverForgeInitC, Comp.cost, Expr.cost]
  dsimp only [pqA, pqB] at hc hcA hcB
  rw [hdraw]
  omega

theorem simDeliverForgeFinishC_queries_zero (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (w : (fig8SmIfaceDF ℓ Pt).Tag → ℕ) :
    (simDeliverForgeFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).queries w (fun _ => 0) = 0 :=
  rfl

theorem simDeliverForgeFinishC_cost_le (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simDeliverForgeFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 4 := by
  simp [simDeliverForgeFinishC, Comp.cost, Expr.cost]

theorem simDeliverForgeProgOfStep_totalQueries_le (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q := by
  unfold simDeliverForgeProgOfStep
  split_ifs with hℓ
  · simp only [CostedReduction.totalQueries, simDeliverForgeInitC_queries_zero,
      simDeliverForgeFinishC_queries_zero, zero_add, add_zero]
    exact le_trans (Nat.mul_le_mul_left q hstep_q) (by omega)
  · rw [dummyBoolSessionRed_totalQueries]
    exact Nat.zero_le q

theorem simDeliverForgeProgOfStep_totalCost_le (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1)) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).totalCost q ≤
      ratchetCostBudget q (qep + 1) := by
  unfold simDeliverForgeProgOfStep
  split_ifs with hℓ
  · have hi := simDeliverForgeInitC_cost_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hf := simDeliverForgeFinishC_cost_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hs := hstep_c hℓ
    have hmax : max 1 (step.cost + 16) ≤
        199000020 + 100000000 * q + 4096 * bits (qep + 1) := by
      omega
    have htot :
        ({ σ := dfFullT ℓ Pt
           init := simDeliverForgeInitC C K Dh encPt encT decT lam
           handle := step
           finish := simDeliverForgeFinishC C K Dh encPt encT decT lam } :
          CostedReduction _ _ _ (e2eSessionCodec ℓ Pt) _ _ _ _).totalCost q ≤
        610 + q * (199000020 + 100000000 * q + 4096 * bits (qep + 1)) + 4 := by
      dsimp only [CostedReduction.totalCost]
      have hmul := Nat.mul_le_mul_left q hmax
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q (qep + 1)
      610 4 199000020 100000000 4096
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le (fig8SmIfaceDF ℓ Pt) rfl .unit q (qep + 1)

theorem simDeliverForgeProgOfStep_makesAtMostQueriesDF
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    MakesAtMostQueriesDF
      ((simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) ()) q := by
  rw [CryptoGames.Ratchet.LibsignalSim.makesAtMostQueriesDF_iff_isGameQuery]
  have hA' := SessionProgCommon.isQueryBoundP_of_makesAtMostQueries hq
  have h := CostedReduction.queryBound_eval
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step)
    (isGameQuery (G := specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [isGameQuery, OracleComp.isQueryBoundP_query_iff])
    (fun _ => A) q (fun _ => hA') ()
  exact h.mono (simDeliverForgeProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)

end LoopAndCost

section DescBits

/-- Total syntactic description bit-length of a session-level `CostedReduction` over
`atomicSessionOps` and `fig8SmIfaceDF` (charging `8` bits per sampler and oracle tag). -/
def atomicDFRedDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt) G GC rIn aIn aOut out) : ℕ :=
  atomicTyDescBits R.σ + atomicTyDescBits rIn + atomicTyDescBits aIn +
    atomicTyDescBits aOut + atomicTyDescBits out +
    (atomicTyDescBits GC.Q + atomicTyDescBits GC.R) +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.init +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.handle +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.finish

theorem dfFullT_descBits_le (ℓ : ℕ) (Pt : Type) :
    atomicTyDescBits (dfFullT ℓ Pt) ≤ 2000 :=
  atomicTyDescBits_dfFullT ℓ Pt

theorem simDeliverForgeInitC_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (simDeliverForgeInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam) ≤ 2500 := by
  have hb0 : bits 0 = 1 := by decide
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  dsimp only [simDeliverForgeInitC, atomicDraw256, initSimCE, initSimMirE, keptUnknownE,
    sessPureOp, sessSpqrKemOp, simRecT, ghostChainT, posTy, PlainT, PK,
    B, PB, fig8CtT, fig8HdrT, fsRecvStT, lctT, wireSaltCtT, BV128, U64,
    BV256, PtT, varIdx, atomicCompDescBits, atomicExprDescBits, atomicSessionOpDescBits,
    atomicPureOpDescBits, atomicTyDescBits, atomicSortDescBits]
  rw [hb0, hb32]
  omega

theorem simDeliverForgeFinishC_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (simDeliverForgeFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam) ≤ 50 := by
  have hb1 : bits 1 = 1 := by decide
  dsimp only [simDeliverForgeFinishC, varIdx, atomicCompDescBits, atomicExprDescBits]
  rw [hb1]
  omega

theorem dummyBoolSessionRed_df_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {rIn : Ty (atomicSig ℓ Pt)} (hrIn : atomicTyDescBits rIn ≤ 64) (q qep : ℕ) :
    atomicDFRedDescBits
      (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (fig8SmIfaceDF ℓ Pt) rIn) ≤
      ratchetDescBudget q qep := by
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  have hcodecQ : atomicTyDescBits (e2eSessionCodec ℓ Pt).Q ≤ 200 := by
    dsimp only [e2eSessionCodec, smQT, B, atomicTyDescBits, atomicSortDescBits]
    rw [hb32]
    omega
  have hcodecR : atomicTyDescBits (e2eSessionCodec ℓ Pt).R ≤ 200 := by
    dsimp only [e2eSessionCodec, smRT, atomicTyDescBits, atomicSortDescBits]
    omega
  have hhandle :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (fig8SmIfaceDF ℓ Pt) rIn).handle ≤ 300 := by
    dsimp only [dummyBoolSessionRed, e2eSessionCodec, smRT,
      atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits]
    omega
  have hfin :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (fig8SmIfaceDF ℓ Pt) rIn).finish ≤ 50 := by
    dsimp only [dummyBoolSessionRed, atomicCompDescBits, atomicExprDescBits]
    omega
  have hinit :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (fig8SmIfaceDF ℓ Pt) rIn).init ≤ 50 := by
    dsimp only [dummyBoolSessionRed, atomicCompDescBits, atomicExprDescBits]
    omega
  have hbase : 2 ^ 23 ≤ ratchetDescBudget q qep := by
    unfold ratchetDescBudget descBitBudget
    omega
  unfold atomicDFRedDescBits
  have hsig : atomicTyDescBits
      (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (fig8SmIfaceDF ℓ Pt) rIn).σ = 4 := rfl
  have hu : atomicTyDescBits (.unit : Ty (atomicSig ℓ Pt)) = 4 := rfl
  have hb : atomicTyDescBits (.bool : Ty (atomicSig ℓ Pt)) = 4 := rfl
  omega

theorem simDeliverForgeRed_descBits_le_of_parts {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (R : SimDeliverForgeRedProg Pt ℓ C K Dh encPt encT decT lam) (q qep : ℕ)
    (hparts :
      atomicTyDescBits R.σ +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.init +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.handle +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.finish ≤
      2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q qep + qep)) :
    atomicDFRedDescBits R ≤ ratchetDescBudget q qep := by
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  have hcodecQ : atomicTyDescBits (e2eSessionCodec ℓ Pt).Q ≤ 200 := by
    dsimp only [e2eSessionCodec, smQT, B, atomicTyDescBits, atomicSortDescBits]
    rw [hb32]
    omega
  have hcodecR : atomicTyDescBits (e2eSessionCodec ℓ Pt).R ≤ 200 := by
    dsimp only [e2eSessionCodec, smRT, atomicTyDescBits, atomicSortDescBits]
    omega
  have hu : atomicTyDescBits (.unit : Ty (atomicSig ℓ Pt)) = 4 := rfl
  have hb : atomicTyDescBits (.bool : Ty (atomicSig ℓ Pt)) = 4 := rfl
  unfold atomicDFRedDescBits ratchetDescBudget descBitBudget
  omega

theorem simDeliverForgeProgOfStep_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    atomicDFRedDescBits (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step) ≤
      ratchetDescBudget q (qep + 1) := by
  unfold simDeliverForgeProgOfStep
  split_ifs with hℓ
  · apply simDeliverForgeRed_descBits_le_of_parts
    change atomicTyDescBits (dfFullT ℓ Pt) +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (simDeliverForgeInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam) +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (simDeliverForgeFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam) ≤ _
    have hσ := dfFullT_descBits_le ℓ Pt
    have hi := simDeliverForgeInitC_descBits_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hf := simDeliverForgeFinishC_descBits_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    have hs := hstep_d hℓ
    omega
  · exact dummyBoolSessionRed_df_descBits_le (by change 4 ≤ 64; omega) q (qep + 1)

private theorem two_mul_atomicSessionOps_opSize_le_local {ℓ : ℕ} {Pt : Type} [DecidableEq Pt]
    [Zero Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (o : (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).Op) :
    2 * (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).opSize o ≤
      atomicSessionOpDescBits o := by
  rcases o with (((o | (_ | _)) | _) | (_ | _)) | _
  · cases o <;>
      dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
        _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
        _root_.ReductionDsl.Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize,
        atomicSessionOpDescBits, KemFailRedLoopAndCost.atomicPureOpDescBits] <;> omega
  · change 2 * 0 ≤ 8 + 5; omega
  · change 2 * 0 ≤ KemFailRedLoopAndCost.atomicSymOpDescBits _ + 5; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 1; omega

theorem two_mul_expr_size_le_atomicExprDescBits {ℓ : ℕ} {Pt : Type}
    {O : _root_.ReductionDsl.Ops (atomicSig ℓ Pt)} (opBits : O.Op → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (e : _root_.ReductionDsl.Expr O Γ t)
    (hop : ∀ o, 2 * O.opSize o ≤ opBits o :=
      by intro o; exact two_mul_atomicSessionOps_opSize_le_local o) :
    2 * e.size ≤ KemFailRedLoopAndCost.atomicExprDescBits opBits e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [_root_.ReductionDsl.Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | tget _ _ ha hb
  | appendL _ _ _ ha hb | findB _ _ _ ha hb | anyB _ _ _ ha hb | mapB _ _ _ ha hb
  | letE _ _ ha hb =>
    simp only [_root_.ReductionDsl.Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha =>
    simp only [_root_.ReductionDsl.Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega
  | ite _ _ _ hc ha hb | tset _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb
  | caseSum _ _ _ hc ha hb | foldrB _ _ _ _ hc ha hb =>
    simp only [_root_.ReductionDsl.Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega
  | op o _ ha =>
    have ho := hop o
    simp only [_root_.ReductionDsl.Expr.size, KemFailRedLoopAndCost.atomicExprDescBits]; omega

theorem two_mul_comp_size_le_atomicCompDescBits {ℓ : ℕ} {Pt : Type}
    {O : _root_.ReductionDsl.Ops (atomicSig ℓ Pt)} {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface (atomicSig ℓ Pt) T}
    (opBits : O.Op → ℕ) (sBits : I.smp.Samp → ℕ) (qBits : I.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (c : Comp O I Γ t)
    (hop : ∀ o, 2 * O.opSize o ≤ opBits o :=
      by intro o; exact two_mul_atomicSessionOps_opSize_le_local o) :
    2 * c.size ≤ atomicCompDescBits opBits sBits qBits c := by
  induction c with
  | ret e =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | bind c k ihc ihk =>
    simp only [Comp.size, atomicCompDescBits]; omega
  | ite b c d ihc ihd =>
    have hb := two_mul_expr_size_le_atomicExprDescBits opBits b hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | caseOpt e n s ihn ihs =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | caseSum e l r ihl ihr =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | sample s e =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | query g e =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | iter n e body ih =>
    have he := two_mul_expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | findM k l p ih | anyM k l p ih | mapM k l p ih =>
    have hl := two_mul_expr_size_le_atomicExprDescBits opBits l hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | consumeFirstM k l p mk ih =>
    have hl := two_mul_expr_size_le_atomicExprDescBits opBits l hop
    have hmk := two_mul_expr_size_le_atomicExprDescBits opBits mk hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | foldM k l z f ih =>
    have hl := two_mul_expr_size_le_atomicExprDescBits opBits l hop
    have hz := two_mul_expr_size_le_atomicExprDescBits opBits z hop
    simp only [Comp.size, atomicCompDescBits]; omega

theorem two_mul_red_size_le_atomicDFRedDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt) G GC rIn aIn aOut out) :
    2 * R.size ≤ atomicDFRedDescBits R := by
  unfold CostedReduction.size atomicDFRedDescBits
  have hi := two_mul_comp_size_le_atomicCompDescBits (I := fig8SmIfaceDF ℓ Pt)
    atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.init
  have hh := two_mul_comp_size_le_atomicCompDescBits (I := fig8SmIfaceDF ℓ Pt)
    atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.handle
  have hf := two_mul_comp_size_le_atomicCompDescBits (I := fig8SmIfaceDF ℓ Pt)
    atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) R.finish
  omega

theorem red_size_le_atomicDFRedDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt) G GC rIn aIn aOut out) :
    R.size ≤ atomicDFRedDescBits R := by
  have h := two_mul_red_size_le_atomicDFRedDescBits R
  omega

theorem simDeliverForgeProgOfStep_size_le_ratchetDescBudget {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).size ≤
      ratchetDescBudget q (qep + 1) :=
  (red_size_le_atomicDFRedDescBits _).trans
    (simDeliverForgeProgOfStep_descBits_le C K Dh encPt encT decT lam qep q step hstep_d)

theorem simDeliverForgeProgOfStep_size_le_of_budget {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hB : ratchetCostBudget q (qep + 1) + (qep + 1) < 2 ^ 126) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).size ≤ reductionSizeBudget :=
  (simDeliverForgeProgOfStep_size_le_ratchetDescBudget C K Dh encPt encT decT lam qep q step hstep_d).trans
    (ratchetDescBudget_le_reductionSizeBudget hB)

theorem simDeliverForgeProgOfStep_gRedBounded_of_budget {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hB : ratchetCostBudget q (qep + 1) + (qep + 1) < 2 ^ 126) :
    GRedBounded (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  gRedBounded_of_bounds_const _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    (simDeliverForgeProgOfStep_totalCost_le C K Dh encPt encT decT lam qep q step hstep_c)
    (simDeliverForgeProgOfStep_size_le_of_budget C K Dh encPt encT decT lam qep q step hstep_d hB)
    (simDeliverForgeProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

private theorem ratchetCostBudget_mono_qep_df {q qep₁ qep₂ : ℕ} (h : qep₁ ≤ qep₂) :
    ratchetCostBudget q qep₁ ≤ ratchetCostBudget q qep₂ := by
  unfold ratchetCostBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (bits_mono h) _)

theorem simDeliverForgeProgOfStep_size_le_of_clamp {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep₀ qep q : ℕ)
    (hqep₀ : qep₀ ≤ qep)
    (hClamp : qep₀ ≤ ratchetCostBudget q (qep + 1))
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1))) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q (qep + 1)) := by
  have h2 := (two_mul_red_size_le_atomicDFRedDescBits _).trans
    (simDeliverForgeProgOfStep_descBits_le C K Dh encPt encT decT lam qep₀ q step hstep_d)
  dsimp only [ratchetDescBudget, descBitBudget] at h2
  set B := ratchetCostBudget q (qep + 1)
  have hBpos : 16777216 * (q + 1) ≤ B := ratchetCostBudget_pos q (qep + 1)
  have hBmono : ratchetCostBudget q (qep₀ + 1) ≤ B :=
    ratchetCostBudget_mono_qep_df (Nat.add_le_add_right hqep₀ 1)
  have hsum : ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1) ≤ 4 * B := by omega
  have hbits : bits (ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1)) ≤ 3 + bits B := by
    have hm1 := bits_mono hsum
    have hm2 := bits_mul_le 4 B
    have hb4 : bits 4 = 3 := by decide
    omega
  have hred : 2 ^ 22 + 3 * 2 ^ 12 ≤ reductionSizeBudget := by decide
  omega

theorem simDeliverForgeProgOfStep_gRedBounded_of_clamp {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep₀ qep q : ℕ)
    (hqep₀ : qep₀ ≤ qep)
    (hClamp : qep₀ ≤ ratchetCostBudget q (qep + 1))
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep₀ + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep₀ + 1) + (qep₀ + 1))) :
    GRedBounded (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    ((simDeliverForgeProgOfStep_totalCost_le C K Dh encPt encT decT lam qep₀ q step hstep_c).trans
      (ratchetCostBudget_mono_qep_df (Nat.add_le_add_right hqep₀ 1)))
    (simDeliverForgeProgOfStep_size_le_of_clamp C K Dh encPt encT decT lam qep₀ qep q
      hqep₀ hClamp step hstep_d)
    (simDeliverForgeProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem simDeliverForgeProgOfStep_size_le_of_qep_le {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (hqep : qep ≤ q + 10)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q (qep + 1)) := by
  have hBpos := ratchetCostBudget_pos q (qep + 1)
  exact simDeliverForgeProgOfStep_size_le_of_clamp C K Dh encPt encT decT lam qep qep q
    (Nat.le_refl qep) (by omega) step hstep_d

theorem simDeliverForgeProgOfStep_gRedBounded_of_qep_le {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (hqep : qep ≤ q + 10)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    GRedBounded (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  have hBpos := ratchetCostBudget_pos q (qep + 1)
  exact simDeliverForgeProgOfStep_gRedBounded_of_clamp C K Dh encPt encT decT lam qep qep q
    (Nat.le_refl qep) (by omega) step hstep_q hstep_c hstep_d

theorem simDeliverForgeProgOfStep_gRedBounded {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_d : ℓ < 10 ^ 6 →
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) step ≤
        2 ^ 21 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hqep : qep ≤ q + 10) :
    GRedBounded (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  simDeliverForgeProgOfStep_gRedBounded_of_qep_le C K Dh encPt encT decT lam qep q hqep
    step hstep_q hstep_c hstep_d

theorem simDeliverForgeProgOfStep_gRedBounded_of_size {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep_q : step.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hstep_c : ℓ < 10 ^ 6 →
      step.cost ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1))
    (hstep_size : ℓ < 10 ^ 6 →
      step.size ≤ 2 ^ 21 + 2 ^ 11 * bits (ratchetCostBudget q (qep + 1))) :
    GRedBounded (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  refine gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
    (simDeliverForgeProgOfStep_totalCost_le C K Dh encPt encT decT lam qep q step hstep_c) ?_
    (simDeliverForgeProgOfStep_totalQueries_le C K Dh encPt encT decT lam q step hstep_q)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)
  unfold simDeliverForgeProgOfStep
  split_ifs with hℓ
  · apply size_le_budget_of_log_cost (C₀ := 2 ^ 22) (C₁ := 2 ^ 11) (by decide) (by decide)
    have hi : (simDeliverForgeInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 100000 := by
      have h1 := two_mul_comp_size_le_atomicCompDescBits
        atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (simDeliverForgeInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam)
      have h2 := simDeliverForgeInitC_descBits_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
      omega
    have hf : (simDeliverForgeFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 1000 := by
      have h1 := two_mul_comp_size_le_atomicCompDescBits
        atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
        (simDeliverForgeFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam)
      have h2 := simDeliverForgeFinishC_descBits_le (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
      omega
    have hs := hstep_size hℓ
    dsimp only [CostedReduction.size]
    omega
  · have hd := SessionProgCommon.dummyBoolSessionRed_size_le
      (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt) .unit
    omega

end DescBits

section AtomicStepBundle

/-- Semantic contract for a costed `simDeliverForge` reduction program at `(idA, idB, qep, q)`. -/
structure SimDeliverForgeEvalOk (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (prog : SimDeliverForgeRedProg Pt ℓ C K Dh encPt encT decT lam) : Prop where
  makesAtMostQueriesDF :
    ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      MakesAtMostQueriesDF (prog.eval (fun _ => A) ()) q
  sendAtomicShortDF : ℓ < 10 ^ 6 →
    ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
        (prog.eval (fun _ => A) ())
  guardedSMDFShort : ℓ < 10 ^ 6 →
    ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      GuardedSMDFShort (prog.eval (fun _ => A) ())
  forgeGuessedAdvantageCellPaper_eq : ℓ < 10 ^ 6 →
    2 * (q + 1) + 25002 < 2 ^ 32 →
    ∀ (tL : Option ℕ) (t : ℕ)
      (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes),
      CryptoGames.SM.MakesAtMostQueries A q →
      let P := paramsV1 C K idA idB
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT (idsOf idA idB) 25000 lam
      forgeGuessedAdvantageCellPaper fig (qep + 1)
          sameHdrScheme tL t
          (challSimDF'Paper (2 + 1) (qep + 1)
            (prog.eval (fun _ => A) ())) =
        forgeGuessedAdvantageCellPaper fig (qep + 1)
          sameHdrScheme tL t
          (challSimDF'Paper (2 + 1) (qep + 1)
            (CryptoGames.LibsignalSM.Proofs.Refinement.simDeliverForge
              P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A))

/-- Complete bundle packaging a `simDeliverForge` costed reduction program together with its
`GRedBounded` proof, syntactic `descBits` bound, and `SimDeliverForgeEvalOk` contract at
`(idA, idB)`. -/
structure SimDeliverForgeAtomicStepBundle (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) where
  prog : SimDeliverForgeRedProg Pt ℓ C K Dh encPt encT decT lam
  gRedBounded : GRedBounded prog (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1))
  descBits_le : atomicDFRedDescBits prog ≤ ratchetDescBudget q (qep + 1)
  evalOk : SimDeliverForgeEvalOk Pt ℓ C K idA idB Dh encPt encT decT lam qep q prog

end AtomicStepBundle

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeBase
