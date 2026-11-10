/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF

/-!
# Receive Pipeline Programs and Cost Bounds for `SimDeliverForge`

Defines the atomic `ReductionDsl` expressions and computations for the `SimDeliverForge` receive
pipeline over `fig8SmIfaceDF`, together with query, step-cost, and description-bit bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost

open _root_.ReductionDsl (Ty Expr Comp SMTagDF bits atomicSig atomicSessionOps fig8SmIfaceDF
  B PK PlainT PtT lpubT lctT fig8CtT fig8CtV fig8CtOfV smRrT smRrDec partyToBool)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalSim (Fig8C)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState)
open CryptoGames.SM (RecvResult orE boolEq pGet pSet)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simMirT ghostChainT simBaseT keptT sentEntryT simFullT simFullEnc simFullDec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet sOpPure srecPos mWin mEpoch mSafeInjE mInTransitE mAcceptE mChallContainsE mTrivialE
   mInWinE ssMir ssPq ssPn ssUnackA ssHonest ssChains ssAmb ssStopped ssMk ssSetAmb ssSetMirWin
   scBase scKept scSent scSnaps scMk scSetBase
   ghostAcceptC ghostRejectsE pushChainE findChainIdxE getChainDE modifyChainAcceptC
   anyChainKeyNoneE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (kDecOutT parseOutT knownSeedDecryptAtomicFastC lctSaltEqOfLctAtomicE injOKAtomicE
   isZeroPtOptAtomicE parseRecvAtomicC toWireAtomicE toWireAtomicE_cost toWireAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
  (sameWireFig8AtomicE eqFig8CAtomicE defaultMcAtomicE fsReceiveAtomicE fig8ReceiveAtomicE
   keptRecvAtomicE keptEvalAtomicE sentEvalAtomicE)

noncomputable section

/-- Combined `(sC, sent)` state type in `atomicSig ℓ Pt` for `SimDeliverForge`. -/
@[reducible] def dfStepT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))

@[reducible] def dfStepDec {ℓ : ℕ} {Pt : Type} (v : (dfStepT ℓ Pt).denote) :
    LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt) :=
  (simFullDec v.1, v.2.map fig8CtOfV)

def dfStepEnc {ℓ : ℕ} {Pt : Type}
    (st : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) :
    (dfStepT ℓ Pt).denote :=
  (simFullEnc st.1, st.2.map fig8CtV)

/-- Output type `(rr?, (sC', sent'))` of a `SimDeliverForge` receive sub-branch. -/
@[reducible] def dfRecvOutT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt)))) (dfStepT ℓ Pt)

@[reducible] def dfRecvOutDec {ℓ : ℕ} {Pt : Type} (v : (dfRecvOutT ℓ Pt).denote) :
    Option (RecvResult (Plain ℓ)) ×
      (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) :=
  (v.1.map (smRrDec id), dfStepDec v.2)

@[reducible] def dfFwdEvictInT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfStepT ℓ Pt)
    (.prod .bool (.prod (B 32) (.prod .bool
      (.prod PK (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))))

@[reducible] def dfFwdInT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfStepT ℓ Pt)
    (.prod .bool (.prod (B 32) (.prod .bool (.prod (.opt .nat)
      (.prod PK (.prod (B 32)
        (.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))))))

@[reducible] def dfRecvNewInT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfStepT ℓ Pt)
    (.prod .bool (.prod (B 32) (.prod .bool
      (.prod (parseOutT ℓ Pt) (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))))))

@[reducible] def dfRecvSameInT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfStepT ℓ Pt)
    (.prod .bool (.prod (B 32) (.prod .bool
      (.prod (parseOutT ℓ Pt) (.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) .nat)))))

@[reducible] def dfRecvInT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32) .bool))

section Builders

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
  (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "IDF" => fig8SmIfaceDF ℓ Pt

/-! ## Cost lemmas for `SimFig8Kept` operations -/

private theorem bits_le_succ_nat_local (n : ℕ) : bits n ≤ n + 1 := by
  have hpow : ∀ m : ℕ, m < 2 ^ (m + 1) := by
    intro m; induction m with
    | zero => omega
    | succ m ih => rw [Nat.pow_succ]; omega
  exact Computational.Proofs.Game.PromotedCostedReds.SimFig8State.bits_le_of_lt_pow
    (by omega) (hpow n)

omit [SampleableType Pt] in
private theorem fsReceiveAtomicE_cost_tight20 (T B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T B stE cE).cost ≤
      stE.cost + cE.cost + 20 * T + 3 * bits B + 16 * (ℓ / 32) + 2200300 := by
  have hr := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB
    (Computational.Proofs.ReductionDsl.Fig8Atomic.fsRecvExpr ℓ Pt C Dh encPt encT lam T B)
    (.pair stE cE)
  have hf := Computational.Proofs.ReductionDsl.Fig8Atomic.fsRecvExpr_cost
    ℓ Pt C Dh encPt encT lam T B
  simp only [fsReceiveAtomicE, Expr.cost] at hr ⊢
  omega

omit [SampleableType Pt] in
private theorem fig8ReceiveAtomicE_cost_tight20 (T B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T B stE cE).cost ≤
      stE.cost + cE.cost + 20 * T + 5 * bits B + 16 * (ℓ / 32) + 2350000 := by
  let t0 := Ty.prod (ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let Γ1 := t0 :: Γ
  let Γ2 := PtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := Ty.prod (ReductionDsl.ckaStT (ℓ := ℓ) (Pt := Pt)) PtT :: Γ2
  let Γ4 := ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt) ::
    ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hcka := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ2)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.ckaRecvExpr ℓ Pt C Dh encPt encT lam)
    (.pair (SimFig8Kept.f8Gamma (.fst .v1)) .v0)
  have hup := Computational.Proofs.Game.PromotedCostedReds.SimFig8State.cost_runFig8WithIds
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB (Γ := Γ3)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr ℓ Pt C Dh encPt encT lam)
    (.pair (SimFig8Kept.f8Root (.fst .v2)) (.snd .v0))
  have hfs := fsReceiveAtomicE_cost_tight20 C K idA idB Dh encPt encT decT lam T B
    (Γ := Γ4) .v0 (.snd .v2)
  have hc_cka := Computational.Proofs.ReductionDsl.Fig8Atomic.ckaRecvExpr_cost
    ℓ Pt C Dh encPt encT lam
  have hc_up := Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr_cost
    ℓ Pt C Dh encPt encT lam
  have hb0 : bits 0 = 1 := SimFig8State.bits_zero
  have hb1 : bits 1 = 1 := SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 ≤ 2 := SimFig8State.bits_le_of_lt_pow (by omega) (by omega)
  unfold fig8ReceiveAtomicE
  dsimp only [SimFig8Kept.f8Mk, SimFig8Kept.f8Id, SimFig8Kept.f8Root, SimFig8Kept.f8VS,
    SimFig8Kept.f8VR, SimFig8Kept.f8Gamma, SimFig8Kept.f8Cur, SimFig8Kept.f8Tcur, orE,
    CryptoGames.SM.sendsInE, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hcka hup hfs ⊢
  generalize SimFig8State.runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.ckaRecvExpr ℓ Pt C Dh encPt encT lam) _ = e_rcka
    at hcka ⊢
  generalize SimFig8State.runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr ℓ Pt C Dh encPt encT lam) _ = e_rup
    at hup ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB T B (Γ := Γ4) _ _ = e_rfs at hfs ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hcka hup hfs ⊢
  simp only [hb0, hb1] at hcka hup hfs ⊢
  omega

theorem fsReceiveAtomicE_cost_tight (T B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T B stE cE).cost ≤
      stE.cost + cE.cost + 20 * T + 3 * bits B + 16 * (ℓ / 32) + 2250000 := by
  let _ := (inferInstance : SampleableType Pt)
  have h := fsReceiveAtomicE_cost_tight20 C K idA idB Dh encPt encT decT lam T B stE cE
  omega

theorem fig8ReceiveAtomicE_cost_tight (T B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T B stE cE).cost ≤
      stE.cost + cE.cost + 20 * T + 5 * bits B + 16 * (ℓ / 32) + 2400000 := by
  let _ := (inferInstance : SampleableType Pt)
  have h := fig8ReceiveAtomicE_cost_tight20 C K idA idB Dh encPt encT decT lam T B stE cE
  omega

theorem keptRecvAtomicE_cost_tight (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T kE cE).cost ≤
      kE.cost + cE.cost + 21 * T + 16 * (ℓ / 32) + 2600000 := by
  let _ := (inferInstance : SampleableType Pt)
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  let ΓS := ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := SimFig8Kept.sanRSAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_cost_tight20 C K idA idB Dh encPt encT decT lam T 0 (Γ := ΓN)
    (SimFig8Kept.sanRSAtomicE T .v0) (.snd .v1)
  have hat := SimFig8Kept.sanAtAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_cost_tight20 C K idA idB Dh encPt encT decT lam T 0 (Γ := ΓS)
    (SimFig8Kept.sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have hb0 : bits 0 = 1 := SimFig8State.bits_zero
  have hbT : bits T ≤ T + 1 := bits_le_succ_nat_local T
  dsimp only [keptRecvAtomicE, SimFig8Kept.f8VR, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize SimFig8Kept.sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs
    at hrs hfs ⊢
  generalize SimFig8Kept.sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hrs hfs hat hf8 ⊢
  simp only [hb0] at hrs hfs hat hf8 ⊢
  omega

theorem keptEvalAtomicE_cost_tight (T B_cap : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T B_cap kE cE).cost ≤
      kE.cost + cE.cost + 21 * T + 5 * bits B_cap + 16 * (ℓ / 32) + 2600000 := by
  let _ := (inferInstance : SampleableType Pt)
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  let ΓS := ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := SimFig8Kept.sanRSAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_cost_tight20 C K idA idB Dh encPt encT decT lam T B_cap (Γ := ΓN)
    (SimFig8Kept.sanRSAtomicE T .v0) (.snd .v1)
  have hat := SimFig8Kept.sanAtAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_cost_tight20 C K idA idB Dh encPt encT decT lam T B_cap (Γ := ΓS)
    (SimFig8Kept.sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have hbT : bits T ≤ T + 1 := bits_le_succ_nat_local T
  dsimp only [keptEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize SimFig8Kept.sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs
    at hrs hfs ⊢
  generalize SimFig8Kept.sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hrs hfs hat hf8 ⊢
  omega

theorem sentEvalAtomicE_cost_tight (L B_cap : ℕ) {Γ : List (Ty ASig)}
    (sentE : Expr AOps Γ (.list (sentEntryT ℓ Pt)))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L B_cap sentE cE c'E).cost ≤
      sentE.cost + cE.cost + c'E.cost + L * (ℓ / 16 + 230) +
        3 * bits B_cap + 16 * (ℓ / 32) + 2400000 := by
  let _ := (inferInstance : SampleableType Pt)
  let t0 := Ty.prod (.list (sentEntryT ℓ Pt))
    (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let Γ1 := sentEntryT ℓ Pt :: t0 :: Γ
  have heq := SimFig8Kept.eqFig8CAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.fst (.snd .v1))
  have hvr := SimFig8Kept.senderToFreshVrAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    (Γ := Γ1) (.snd .v0)
  have hfs := fsReceiveAtomicE_cost_tight20 C K idA idB Dh encPt encT decT lam 0 B_cap (Γ := Γ1)
    (SimFig8Kept.senderToFreshVrAtomicE (.snd .v0)) (.snd (.snd .v1))
  dsimp only [Expr.cost, Expr.v0, Expr.v1] at heq hvr
  have hmul : L * ((eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.fst (.snd .v1))).cost + 1) ≤
      L * (ℓ / 16 + 230) :=
    Nat.mul_le_mul_left L (by dsimp only [Expr.v0, Expr.v1]; omega)
  dsimp only [sentEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at heq hvr hfs hmul ⊢
  generalize eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) _ _ = e_eq at heq hmul ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 B_cap (Γ := Γ1) _ _ = e_fs at hfs ⊢
  generalize SimFig8Kept.senderToFreshVrAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ = e_vr
    at hvr hfs ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hfs ⊢
  omega

/-! ## Pure receive helpers -/

def fwdOrElseOptE {Γ : List (Ty ASig)} {a : Ty ASig}
    (e1 e2 : Expr AOps Γ (.opt a)) : Expr AOps Γ (.opt a) :=
  eLet (.pair e1 e2) (.caseOpt (.fst .v0) (.snd .v0) (.some .v0))

def fwdNoneOutE {Γ : List (Ty ASig)} (stE : Expr AOps Γ (dfStepT ℓ Pt)) :
    Expr AOps Γ (dfRecvOutT ℓ Pt) :=
  .pair .none stE

def fwdRejOutE {Γ : List (Ty ASig)} (stE : Expr AOps Γ (dfStepT ℓ Pt)) :
    Expr AOps Γ (dfRecvOutT ℓ Pt) :=
  .pair (.some (.inl .unit)) stE

def fwdAccRrE {Γ : List (Ty ASig)} (tE iE : Expr AOps Γ .nat)
    (mOptE : Expr AOps Γ (.opt (PlainT (ℓ := ℓ) (Pt := Pt)))) :
    Expr AOps Γ (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt)))) :=
  .some (.inr (.pair tE (.pair iE mOptE)))

def fwdOnAcceptFinishE (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32)) :
    Expr AOps Γ
      (.prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt)))) (simBaseT ℓ Pt)) :=
  let tupT := Ty.prod (simBaseT ℓ Pt) (.prod (.list (ghostChainT ℓ Pt))
    (.prod .bool (.prod (B 32) (.prod .bool (.prod .nat (.prod .nat
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B 32))))))))
  eLet (a := tupT)
    (.pair sE (.pair csE (.pair qBE (.pair wE (.pair isDelE (.pair tE (.pair iE (.pair mE pq'E))))))))
    (let s0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst x
     let cs0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd x)
     let q0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd x))
     let w0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd x)))
     let isDel0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd x))))
     let t0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd x)))))
     let i0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
     let m0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))
     let pq0 {Δ} (x : Expr AOps Δ tupT) := Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))
     let mkS' {Δ} (x : Expr AOps Δ tupT) (mirE : Expr AOps Δ (simMirT ℓ Pt)) :=
       ssMk mirE (pSet (ssPq (s0 x)) (q0 x) (pq0 x)) (ssPn (s0 x))
         (.and (ssUnackA (s0 x)) (q0 x)) (ssHonest (s0 x))
         (pSet (ssChains (s0 x)) (q0 x) (cs0 x)) (ssAmb (s0 x)) (ssStopped (s0 x))
     .ite (isDel0 .v0)
       (.caseOpt (mInTransitE Lq (ssMir (s0 .v0)) (.not (q0 .v0)) (w0 .v0))
         (.pair .none (s0 .v0))
         (let rPos := srecPos .v0
          let mOpt := Expr.ite (mChallContainsE Lq (ssMir (s0 .v1)) rPos) .none (.some (m0 .v1))
          let mir' := mAcceptE Lq (ssMir (s0 .v1)) (q0 .v1) rPos
          .pair (fwdAccRrE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (t0 .v1) (i0 .v1) mOpt) (mkS' .v1 mir')))
       (.ite (.lt (.nat (qep + 1)) (t0 .v0))
         (.pair (.some (.inl .unit)) (s0 .v0))
         (let posE := Expr.pair (.not (q0 .v0)) (.pair (t0 .v0) (i0 .v0))
          .ite (mTrivialE Lq (ssMir (s0 .v0)) posE)
            (.pair (fwdAccRrE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
                (decT := decT) (lam := lam) (t0 .v0) (i0 .v0) (.some (m0 .v0)))
              (mkS' .v0 (mAcceptE Lq (ssMir (s0 .v0)) (q0 .v0) posE)))
            (.pair (.some (.inl .unit)) (ssSetMirWin (s0 .v0))))))

def fwdInTE (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ .bool :=
  eLet (.pair sE (.pair qBE c'E))
    (.and
      (.anyB Lq (ssHonest (.fst .v0))
        (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.snd .v0) (.snd (.snd .v1))))
      (.caseOpt
        (mInTransitE Lq (ssMir (.fst .v0)) (.not (.fst (.snd .v0)))
          (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) (.snd (.snd .v0))))
        (.bool false) (.bool true)))

def fwdScAcceptUpdateE (T : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (base'E : Expr AOps Γ (simBaseT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (simFullT ℓ Pt) :=
  eLet (.pair sCE (.pair base'E (.pair qBE cE)))
    (let sC0 := Expr.fst .v0
     let b0 := Expr.fst (.snd .v0)
     let q0 := Expr.fst (.snd (.snd .v0))
     let c0 := Expr.snd (.snd (.snd .v0))
     let kept' := pSet (scKept sC0) q0
       (keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) idA idB T (pGet (scKept sC0) q0) c0)
     scMk b0 kept' (scSent sC0) (scSnaps sC0))

def fwdMkCE {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat) (T?E : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)) :=
  eLet (.pair honestCE (.pair tE (.pair T?E lctE)))
    (.caseOpt (.fst .v0)
      (.pair (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0))))
      (.ite
        (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v0 (.snd (.snd (.snd .v1))))
        .v0
        (.pair (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))) (.snd (.snd (.snd .v1))))))

def fwdEvictedE {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) : Expr AOps Γ .bool :=
  eLet (.pair honestCE (.pair sE qBE))
    (.caseOpt (.fst .v0)
      (.bool false)
      (.not (.eqN (.fst (.fst .v0))
        (.add (pGet (mEpoch (ssMir (.fst (.snd .v1)))) (.snd (.snd .v1))) (.nat 1)))))

def fwdSaltEqE {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ .bool :=
  eLet (.pair honestCE lctE)
    (.caseOpt (.fst .v0)
      (.bool false)
      (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .v0 (.snd .v1)))

def fwdAmbCondE {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) : Expr AOps Γ .bool :=
  eLet (.pair sE qBE)
    (orE (mInWinE (ssMir (.fst .v0)) (.snd .v0))
      (.and (.not (.snd .v0))
        (anyChainKeyNoneE (pGet (ssChains (.fst .v0)) (.snd .v0)))))

def fwdScAmbE {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    Expr AOps Γ (simFullT ℓ Pt) :=
  eLet (.pair sCE qBE)
    (let sC0 := Expr.fst .v0
     let b0 := scBase sC0
     let q0 := Expr.snd .v0
     .ite (fwdAmbCondE C K Dh encPt encT decT lam b0 q0)
       (scSetBase sC0 (ssSetAmb b0 (.add (ssAmb b0) (.nat 1))))
       sC0)

def fwdNewGuardRejectE {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (iE : Expr AOps Γ .nat) : Expr AOps Γ .bool :=
  eLet (.pair sE (.pair qBE iE))
    (orE
      (orE (mInWinE (ssMir (.fst .v0)) (.fst (.snd .v0)))
        (.lt (.nat 25000) (.sub (.snd (.snd .v0)) (.nat 1))))
      (.not (.lt (.snd (.snd .v0)) (.nat (2 ^ 32)))))

def fwdRefuseE (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool) : Expr AOps Γ .bool :=
  eLet (.pair sE (.pair qBE (.pair wE isDelE)))
    (let s0 := Expr.fst .v0
     let q0 := Expr.fst (.snd .v0)
     let w0 := Expr.fst (.snd (.snd .v0))
     let d0 := Expr.snd (.snd (.snd .v0))
     let mir0 := ssMir s0
     let inTrOpt := mInTransitE Lq mir0 (.not q0) w0
     let inTrNone := Expr.caseOpt inTrOpt (.bool true) (.bool false)
     let inTrSome := Expr.caseOpt inTrOpt (.bool false) (.bool true)
     orE (orE (ssStopped s0) (mWin mir0))
       (orE (.and d0 inTrNone)
         (.and (.not d0)
           (orE (orE inTrSome (.not (mSafeInjE mir0)))
             (.not (injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) w0))))))

def fwdHonestCE (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
  eLet (.pair sE (.pair qBE wE))
    (.caseOpt
      (.findB Lq (ssHonest (.fst .v0))
        (.and
          (sOpPure (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v1))))
          (boolEq (.eqN (.modK 2 (.fst (.fst (.snd .v0)))) (.nat 0))
            (.not (.fst (.snd .v1))))))
      .none
      (.some (.snd .v0)))

/-! ## Atomic receive computations -/

def fwdOnAcceptC (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK)
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32)) :
    Comp AOps IDF Γ
      (.prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt)))) (simBaseT ℓ Pt)) :=
  let tupT := Ty.prod (simBaseT ℓ Pt) (.prod (.opt .nat) (.prod PK
    (.prod .bool (.prod (B 32) (.prod .bool (.prod .nat (.prod .nat
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B 32)))))))))
  let s0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst x
  let ci0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd x)
  let pk0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd x))
  let q0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd x)))
  let w0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd x))))
  let isDel0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd x)))))
  let t0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
  let i0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))
  let m0 {Δ} (x : Expr AOps Δ tupT) :=
    Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))))
  let pq0 {Δ} (x : Expr AOps Δ tupT) :=
    Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))))
  .bind (.ret (t := tupT)
      (.pair sE (.pair ci?E (.pair pkE (.pair qBE (.pair wE (.pair isDelE
        (.pair tE (.pair iE (.pair mE pq'E))))))))))
    (.bind
      (.caseOpt (ci0 .v0)
        (.bind
          (ghostAcceptC IDF
            (.pair (.some (pk0 .v0)) (.pair (t0 .v0) (.pair (.nat 0) .nil)))
            (i0 .v0))
          (.ret (pushChainE (pGet (ssChains (s0 .v1)) (q0 .v1)) .v0)))
        (modifyChainAcceptC IDF (pGet (ssChains (s0 .v1)) (q0 .v1)) .v0 (i0 .v1)))
      (.ret
        (fwdOnAcceptFinishE C K Dh encPt encT decT lam qep Lq
          (s0 .v1) .v0 (q0 .v1) (w0 .v1) (isDel0 .v1) (t0 .v1) (i0 .v1) (m0 .v1) (pq0 .v1))))

def fwdProbeC (Lq : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool)
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (exE : Expr AOps Γ (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))) :
    Comp AOps IDF Γ (.list (fig8CtT (ℓ := ℓ) (Pt := Pt))) :=
  .bind (.ret (.pair qBE (.pair c'E exE)))
    (.caseOpt
      (.findB Lq (.snd (.snd .v0))
        (sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .v0 (.fst (.snd .v1))))
      (.ret (.snd (.snd .v0)))
      (.bind (Comp.query (I := IDF) SMTagDF.df (.pair (.fst .v1) (.pair .v0 (.fst (.snd .v1)))))
        (.ret (.snd (.snd .v2)))))

def fwdEvalCKSC (Lq T Kc B_cap : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Comp AOps IDF Γ (.opt (.opt (kDecOutT ℓ Pt))) :=
  .bind (.ret (.pair sCE (.pair qBE (.pair wE (.pair cE c'E)))))
    (let sC0 := Expr.fst .v0
     let q0 := Expr.fst (.snd .v0)
     let w0 := Expr.fst (.snd (.snd .v0))
     let c0 := Expr.fst (.snd (.snd (.snd .v0)))
     let c'0 := Expr.snd (.snd (.snd (.snd .v0)))
     let predE :=
       fwdOrElseOptE C K Dh encPt encT decT lam
         (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
           (decT := decT) (lam := lam) idA idB T B_cap (pGet (scKept sC0) q0) c'0)
         (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
           (decT := decT) (lam := lam) idA idB Lq B_cap (scSent sC0) c0 c'0)
     .caseOpt predE
       (knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) idA idB Lq Kc B_cap IDF
         (scSnaps sC0) q0 (.fst (.fst c0)) w0 c'0)
       (.ret (.some .v0)))

def fwdResyncC (qep Lq T : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (rE : Expr AOps Γ (.opt (kDecOutT ℓ Pt))) :
    Comp AOps IDF Γ (dfRecvOutT ℓ Pt) :=
  let tupT := Ty.prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod (.opt .nat) (.prod PK (.prod (B 32)
      (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (.opt (kDecOutT ℓ Pt))))))))
  let st0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst x
  let q0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd x)
  let w0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd x))
  let ci0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd x)))
  let pk0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd x))))
  let pq0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd x)))))
  let c0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
  let r0 {Δ} (x : Expr AOps Δ tupT) := Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))
  .bind (.ret (t := tupT)
      (.pair stE (.pair qBE (.pair wE (.pair ci?E (.pair pkE (.pair pq'E (.pair cE rE))))))))
    (.caseOpt (r0 .v0)
      (.ret (fwdRejOutE C K Dh encPt encT decT lam (st0 .v0)))
      (.bind (Comp.query (I := IDF) SMTagDF.dl (.pair (q0 .v1) (c0 .v1)))
        (.caseOpt .v0
          (.ret (fwdRejOutE C K Dh encPt encT decT lam (st0 .v2)))
          (.caseSum .v0
            (.ret (fwdRejOutE C K Dh encPt encT decT lam (st0 .v4)))
            (.bind
              (fwdOnAcceptC C K Dh encPt encT decT lam qep Lq
                (scBase (.fst (st0 .v4))) (ci0 .v4) (pk0 .v4) (q0 .v4) (w0 .v4) (.bool true)
                (.fst .v3) (.fst (.snd .v3)) (.snd (.snd (.snd .v3))) (pq0 .v4))
              (.ret
                (.pair (.fst .v0)
                  (.pair
                    (fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam T
                      (.fst (st0 .v5)) (.snd .v0) (q0 .v5) (c0 .v5))
                    (.snd (st0 .v5))))))))))

def fwdAnswerC (qep Lq T : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Comp AOps IDF Γ (dfRecvOutT ℓ Pt) :=
  let tupT := Ty.prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod .bool (.prod (.opt .nat) (.prod PK (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))
  let st0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst x
  let q0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd x)
  let w0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd x))
  let isDel0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd x)))
  let ci0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd x))))
  let pk0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd x)))))
  let pq0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
  let c'0 {Δ} (x : Expr AOps Δ tupT) := Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd x))))))
  .bind (.ret (t := tupT)
      (.pair stE (.pair qBE (.pair wE (.pair isDelE (.pair ci?E (.pair pkE (.pair pq'E c'E))))))))
    (.bind
      (.ite (fwdInTE C K Dh encPt encT decT lam Lq (scBase (.fst (st0 .v0))) (q0 .v0) (c'0 .v0))
        (Comp.query (I := IDF) SMTagDF.dl (.pair (q0 .v0) (c'0 .v0)))
        (Comp.query (I := IDF) SMTagDF.ij (.pair (q0 .v0) (c'0 .v0))))
      (.caseOpt .v0
        (.ret (fwdRejOutE C K Dh encPt encT decT lam (st0 .v1)))
        (.caseSum .v0
          (.ret (fwdRejOutE C K Dh encPt encT decT lam (st0 .v3)))
          (.bind
            (fwdOnAcceptC C K Dh encPt encT decT lam qep Lq
              (scBase (.fst (st0 .v3))) (ci0 .v3) (pk0 .v3) (q0 .v3) (w0 .v3) (isDel0 .v3)
              (.fst .v0) (.fst (.snd .v0))
              (.caseOpt (.snd (.snd .v0))
                (.snd (.fst (defaultMcAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam))))
                (.snd .v0))
              (pq0 .v3))
            (.ret
              (.pair (.fst .v0)
                (.pair
                  (fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam T
                    (.fst (st0 .v4)) (.snd .v0) (q0 .v4) (c'0 .v4))
                  (.snd (st0 .v4)))))))))

def fwdEvictC (qep q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Comp AOps IDF Γ (dfRecvOutT ℓ Pt) :=
  let Lq := q
  let T := 50000 * q
  let tupT := dfFwdEvictInT ℓ Pt
  let st0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst x
  let q0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd x)
  let w0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd x))
  let isDel0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd x)))
  let pk0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd x))))
  let pq0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd x)))))
  let c'0 {Δ} (x : Expr AOps Δ tupT) := Expr.snd (.snd (.snd (.snd (.snd (.snd x)))))
  .bind (.ret (t := tupT)
      (.pair stE (.pair qBE (.pair wE (.pair isDelE (.pair pkE (.pair pq'E c'E)))))))
    (.ite (.and (isDel0 .v0) (.not (mSafeInjE (ssMir (scBase (.fst (st0 .v0)))))))
      (.bind (fwdProbeC C K Dh encPt encT decT lam Lq (q0 .v0) (c'0 .v0) (.snd (st0 .v0)))
        (.ret (fwdRejOutE C K Dh encPt encT decT lam (.pair (.fst (st0 .v1)) .v0))))
      (fwdAnswerC C K idA idB Dh encPt encT decT lam qep Lq T
        (st0 .v0) (q0 .v0) (w0 .v0) (isDel0 .v0) .none (pk0 .v0) (pq0 .v0) (c'0 .v0)))

def fwdHookC (qep q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Comp AOps IDF Γ (dfRecvOutT ℓ Pt) :=
  let Lq := q
  let T := 50000 * q
  let Kc := 25001 * q + 25000
  let B_cap := 2 ^ 32
  let tupT := dfFwdInT ℓ Pt
  let st0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst x
  let q0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd x)
  let w0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd x))
  let isDel0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd x)))
  let ci0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd x))))
  let pk0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd (.snd x)))))
  let pq0 {Δ} (x : Expr AOps Δ tupT) :=
    Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd x))))))
  let hc0 {Δ} (x : Expr AOps Δ tupT) :=
    Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))
  let c'0 {Δ} (x : Expr AOps Δ tupT) :=
    Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd x)))))))
  .bind (.ret (t := tupT)
      (.pair stE (.pair qBE (.pair wE (.pair isDelE (.pair ci?E
        (.pair pkE (.pair pq'E (.pair honestCE c'E)))))))))
    (.caseOpt (hc0 .v0)
      (fwdAnswerC C K idA idB Dh encPt encT decT lam qep Lq T
        (st0 .v0) (q0 .v0) (w0 .v0) (isDel0 .v0) (ci0 .v0) (pk0 .v0) (pq0 .v0) (c'0 .v0))
      (.ite
        (.and
          (.not (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
            (decT := decT) (lam := lam) .v0 (c'0 .v1)))
          (.and (isDel0 .v1) (.not (mSafeInjE (ssMir (scBase (.fst (st0 .v1))))))))
        (.bind
          (fwdEvalCKSC C K idA idB Dh encPt encT decT lam Lq T Kc B_cap
            (.fst (st0 .v1)) (q0 .v1) (w0 .v1) .v0 (c'0 .v1))
          (.caseOpt .v0
            (.bind
              (fwdProbeC C K Dh encPt encT decT lam Lq (q0 .v2) (c'0 .v2) (.snd (st0 .v2)))
              (.ret (fwdRejOutE C K Dh encPt encT decT lam (.pair (.fst (st0 .v3)) .v0))))
            (fwdResyncC C K idA idB Dh encPt encT decT lam qep Lq T
              (st0 .v3) (q0 .v3) (w0 .v3) (ci0 .v3) (pk0 .v3) (pq0 .v3) .v2 .v0)))
        (fwdAnswerC C K idA idB Dh encPt encT decT lam qep Lq T
          (st0 .v1) (q0 .v1) (w0 .v1) (isDel0 .v1) (ci0 .v1) (pk0 .v1) (pq0 .v1) (c'0 .v1))))

/-- Atomic computation for the new-epoch (`findIdx? = none`) receive branch of `semRecvHookS`. -/
def fwdRecvNewC (qep q : ℕ) :
    Comp AOps IDF [dfRecvNewInT ℓ Pt] (dfRecvOutT ℓ Pt) :=
  let tupT := dfRecvNewInT ℓ Pt
  let st0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst x
  let q0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd x)
  let w0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd x))
  let isDel0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd x)))
  let parsed0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (.snd x))))
  let pq0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (parsed0 x)
  let i0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (parsed0 x))
  let pk0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (parsed0 x)))
  let T?0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd (.snd (parsed0 x))))
  let lct0 {Δ} (x : Expr AOps Δ tupT) := Expr.snd (.snd (.snd (.snd (parsed0 x))))
  let hc0 {Δ} (x : Expr AOps Δ tupT) := Expr.snd (.snd (.snd (.snd (.snd x))))
  let base0 {Δ} (x : Expr AOps Δ tupT) := scBase (.fst (st0 x))
  let evicted0 {Δ} (x : Expr AOps Δ tupT) :=
    fwdEvictedE C K Dh encPt encT decT lam (hc0 x) (base0 x) (q0 x)
  let saltEq0 {Δ} (x : Expr AOps Δ tupT) :=
    fwdSaltEqE C K Dh encPt encT decT lam (hc0 x) (lct0 x)
  let stAmb0 {Δ} (x : Expr AOps Δ tupT) : Expr AOps Δ (dfStepT ℓ Pt) :=
    .pair (fwdScAmbE C K Dh encPt encT decT lam (.fst (st0 x)) (q0 x)) (.snd (st0 x))
  .ite (.and (evicted0 .v0) (saltEq0 .v0))
    (.ret (fwdRejOutE C K Dh encPt encT decT lam (st0 .v0)))
    (.ite
      (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (T?0 .v0))
      (.ret (fwdRejOutE C K Dh encPt encT decT lam (st0 .v0)))
      (.ite (fwdNewGuardRejectE C K Dh encPt encT decT lam (base0 .v0) (q0 .v0) (i0 .v0))
        (.ret (fwdRejOutE C K Dh encPt encT decT lam (stAmb0 .v0)))
        (.caseOpt (T?0 .v0)
          (.ret (fwdRejOutE C K Dh encPt encT decT lam (stAmb0 .v0)))
          (let nextEp := Expr.add (pGet (mEpoch (ssMir (base0 .v1))) (q0 .v1)) (.nat 1)
           let evC := Expr.pair (.pair nextEp (.some .v0)) (lct0 .v1)
           let mkC := fwdMkCE C K Dh encPt encT decT lam (hc0 .v1) nextEp (.some .v0) (lct0 .v1)
           .ite (evicted0 .v1)
             (fwdEvictC C K idA idB Dh encPt encT decT lam qep q
               (stAmb0 .v1) (q0 .v1) (w0 .v1) (isDel0 .v1) (pk0 .v1) (pq0 .v1) evC)
             (fwdHookC C K idA idB Dh encPt encT decT lam qep q
               (stAmb0 .v1) (q0 .v1) (w0 .v1) (isDel0 .v1) .none (pk0 .v1) (pq0 .v1)
               (hc0 .v1) mkC)))))

/-- Atomic computation for the existing-epoch (`findIdx? = some ci`) receive branch of `semRecvHookS`. -/
def fwdRecvSameC (qep q : ℕ) :
    Comp AOps IDF [dfRecvSameInT ℓ Pt] (dfRecvOutT ℓ Pt) :=
  let st0 := Expr.fst (O := AOps) (Γ := [dfRecvSameInT ℓ Pt]) .v0
  let q0 := Expr.fst (.snd .v0)
  let w0 := Expr.fst (.snd (.snd .v0))
  let isDel0 := Expr.fst (.snd (.snd (.snd .v0)))
  let parsed0 := Expr.fst (.snd (.snd (.snd (.snd .v0))))
  let pq0 := Expr.fst parsed0
  let i0 := Expr.fst (.snd parsed0)
  let pk0 := Expr.fst (.snd (.snd parsed0))
  let T?0 := Expr.fst (.snd (.snd (.snd parsed0)))
  let lct0 := Expr.snd (.snd (.snd (.snd parsed0)))
  let hc0 := Expr.fst (.snd (.snd (.snd (.snd (.snd .v0)))))
  let ci0 := Expr.snd (.snd (.snd (.snd (.snd (.snd .v0)))))
  let g0 := getChainDE (pGet (ssChains (scBase (.fst st0))) q0) ci0
  let c'0 := fwdMkCE C K Dh encPt encT decT lam hc0 (.fst (.snd g0)) T?0 lct0
  .ite (ghostRejectsE g0 i0)
    (.ret (fwdRejOutE C K Dh encPt encT decT lam st0))
    (fwdHookC C K idA idB Dh encPt encT decT lam qep q
      st0 q0 w0 isDel0 (.some ci0) pk0 pq0 hc0 c'0)

def singletonWk {A : Ty ASig} {Δ : List (Ty ASig)} :
    ∀ {u : Ty ASig}, _root_.ReductionDsl.Var [A] u → _root_.ReductionDsl.Var (A :: Δ) u
  | _, .zero => .zero

/-- Full `semRecvHookS` dispatcher combining wire refusal, parsing, and chain-index dispatch. -/
def fwdRecvDispatchC (q : ℕ)
    (newBranchC : Comp AOps IDF [dfRecvNewInT ℓ Pt] (dfRecvOutT ℓ Pt))
    (sameBranchC : Comp AOps IDF [dfRecvSameInT ℓ Pt] (dfRecvOutT ℓ Pt)) :
    Comp AOps IDF [dfRecvInT ℓ Pt] (dfRecvOutT ℓ Pt) :=
  let tupT := dfRecvInT ℓ Pt
  let st0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst x
  let q0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd x)
  let w0 {Δ} (x : Expr AOps Δ tupT) := Expr.fst (.snd (.snd x))
  let isDel0 {Δ} (x : Expr AOps Δ tupT) := Expr.snd (.snd (.snd x))
  let base0 {Δ} (x : Expr AOps Δ tupT) := scBase (.fst (st0 x))
  .ite (fwdRefuseE C K Dh encPt encT decT lam q (base0 .v0) (q0 .v0) (w0 .v0) (isDel0 .v0))
    (.ret (fwdNoneOutE C K Dh encPt encT decT lam (st0 .v0)))
    (.bind
      (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) IDF idA idB (2 ^ 32)
        (q0 .v0) (pGet (ssPq (base0 .v0)) (q0 .v0)) (w0 .v0))
      (.caseOpt .v0
        (.ret (fwdRejOutE C K Dh encPt encT decT lam (st0 .v1)))
        (let pkE := Expr.fst (.snd (.snd .v0))
         let hcE := fwdHonestCE C K Dh encPt encT decT lam q (base0 .v2) (q0 .v2) (w0 .v2)
         .caseOpt
           (findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
             (decT := decT) (lam := lam) (pGet (ssChains (base0 .v2)) (q0 .v2)) pkE)
           (.bind
             (.ret (t := dfRecvNewInT ℓ Pt)
               (.pair (st0 .v2) (.pair (q0 .v2) (.pair (w0 .v2) (.pair (isDel0 .v2)
                 (.pair .v0 hcE))))))
             (AtomicSessionBridge.renComp singletonWk newBranchC))
           (.bind
             (.ret (t := dfRecvSameInT ℓ Pt)
               (.pair (st0 .v3) (.pair (q0 .v3) (.pair (w0 .v3) (.pair (isDel0 .v3)
                 (.pair .v1 (.pair
                   (fwdHonestCE C K Dh encPt encT decT lam q (base0 .v3) (q0 .v3) (w0 .v3))
                   .v0)))))))
             (AtomicSessionBridge.renComp singletonWk sameBranchC)))))

/-! ## Query, cost, and description-bit bounds -/

private theorem fwdOnAcceptC_queries (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK)
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32))
    (wt : (IDF).Tag → ℕ) (ws : (IDF).smp.Samp → ℕ) :
    (fwdOnAcceptC C K Dh encPt encT decT lam qep Lq sE ci?E pkE qBE wE isDelE tE iE mE pq'E).queries
      wt ws = 0 := by
  simp [fwdOnAcceptC, Comp.queries, SimFig8State.ghostAcceptC_queries,
    SimFig8State.modifyChainAcceptC_queries]

private theorem fwdProbeC_queries (Lq : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (exE : Expr AOps Γ (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))) :
    (fwdProbeC C K Dh encPt encT decT lam Lq qBE c'E exE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  simp [fwdProbeC, Comp.queries]

private theorem fwdEvalCKSC_queries (Lq T Kc B_cap : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (wt : (IDF).Tag → ℕ) (ws : (IDF).smp.Samp → ℕ) :
    (fwdEvalCKSC C K idA idB Dh encPt encT decT lam Lq T Kc B_cap sCE qBE wE cE c'E).queries
      wt ws = 0 := by
  simp [fwdEvalCKSC, Comp.queries, SimFig8Crypto.knownSeedDecryptAtomicFastC_queries]

private theorem fwdResyncC_queries (qep Lq T : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (rE : Expr AOps Γ (.opt (kDecOutT ℓ Pt))) :
    (fwdResyncC C K idA idB Dh encPt encT decT lam qep Lq T stE qBE wE ci?E pkE pq'E cE rE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  simp [fwdResyncC, Comp.queries, fwdOnAcceptC_queries]

private theorem fwdAnswerC_queries (qep Lq T : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdAnswerC C K idA idB Dh encPt encT decT lam qep Lq T stE qBE wE isDelE ci?E pkE pq'E c'E).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  simp [fwdAnswerC, Comp.queries, fwdOnAcceptC_queries]

private theorem fwdEvictC_queries (qep q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdEvictC C K idA idB Dh encPt encT decT lam qep q stE qBE wE isDelE pkE pq'E c'E).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  have hp := fwdProbeC_queries C K Dh encPt encT decT lam q
    (Γ := dfFwdEvictInT ℓ Pt :: Γ) (.fst (.snd .v0))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))) (.snd (.fst .v0))
  have ha := fwdAnswerC_queries C K idA idB Dh encPt encT decT lam qep q (50000 * q)
    (Γ := dfFwdEvictInT ℓ Pt :: Γ) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) .none (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  dsimp only [fwdEvictC]
  simp only [Comp.queries] at hp ha ⊢
  omega

private theorem fwdHookC_queries (qep q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdHookC C K idA idB Dh encPt encT decT lam qep q stE qBE wE isDelE ci?E pkE pq'E honestCE c'E).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  let Γ1 := dfFwdInT ℓ Pt :: Γ
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := Ty.opt (Ty.opt (kDecOutT ℓ Pt)) :: Γ2
  let Γ4 := Ty.opt (kDecOutT ℓ Pt) :: Γ3
  have ha1 := fwdAnswerC_queries C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ1)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.fst (.snd (.snd (.snd (.snd .v0))))) (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
  have ha2 := fwdAnswerC_queries C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ2)
    (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  have hp := fwdProbeC_queries C K Dh encPt encT decT lam q (Γ := Γ3)
    (.fst (.snd .v2)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))) (.snd (.fst .v2))
  have hr := fwdResyncC_queries C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ4)
    (.fst .v3) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))) .v2 .v0
  dsimp only [fwdHookC]
  simp only [Comp.queries, fwdEvalCKSC_queries] at ha1 ha2 hp hr ⊢
  omega

private theorem hb0_c : bits 0 = 1 := SimFig8State.bits_zero
private theorem hb1_c : bits 1 = 1 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb2_c : bits 2 ≤ 2 := SimFig8State.bits_le_of_lt_pow (by omega) (by omega)
private theorem hb25k_c : bits 25000 ≤ 16 := SimFig8State.bits_le_of_lt_pow (by omega) (by omega)
private theorem hb2p32_c : bits (2 ^ 32) ≤ 34 :=
  SimFig8State.bits_le_of_lt_pow (by omega) (by omega)

omit [SampleableType Pt] in
private theorem fwdOrElseOptE_cost {Γ : List (Ty ASig)} {a : Ty ASig}
    (e1 e2 : Expr AOps Γ (.opt a)) :
    (fwdOrElseOptE C K Dh encPt encT decT lam e1 e2).cost ≤ e1.cost + e2.cost + 10 := by
  simp only [fwdOrElseOptE, SimFig8State.cost_eLet, Expr.cost, Expr.v0]; omega

omit [SampleableType Pt] in
private theorem fwdOnAcceptFinishE_cost (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32)) :
    (fwdOnAcceptFinishE C K Dh encPt encT decT lam qep Lq sE csE qBE wE isDelE tE iE mE pq'E).cost ≤
      sE.cost + csE.cost + qBE.cost + wE.cost + isDelE.cost + tE.cost + iE.cost +
        mE.cost + pq'E.cost + 700 * Lq + bits (qep + 1) + 2500 := by
  let tupT := Ty.prod (simBaseT ℓ Pt) (.prod (.list (ghostChainT ℓ Pt))
    (.prod .bool (.prod (B 32) (.prod .bool (.prod .nat (.prod .nat
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B 32))))))))
  let Γ1 := tupT :: Γ
  let Γ2 := SimFig8LoopAndCost.simRecT ℓ Pt :: Γ1
  have htr := SimFig8State.cost_mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq (Γ := Γ1)
    (ssMir (.fst .v0)) (.not (.fst (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd .v0))))
  have hch := SimFig8State.cost_mChallContainsE (O' := AOps) Lq (Γ := Γ2)
    (ssMir (.fst .v1)) (srecPos .v0)
  have hac1 := SimFig8State.cost_mAcceptE (O' := AOps) Lq (Γ := Γ2)
    (ssMir (.fst .v1)) (.fst (.snd (.snd .v1))) (srecPos .v0)
  let posE : Expr AOps Γ1 CryptoGames.SM.posTy :=
    .pair (.not (.fst (.snd (.snd .v0))))
      (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
  have htv := SimFig8State.cost_mTrivialE (O' := AOps) Lq (Γ := Γ1) (ssMir (.fst .v0)) posE
  have hac2 := SimFig8State.cost_mAcceptE (O' := AOps) Lq (Γ := Γ1)
    (ssMir (.fst .v0)) (.fst (.snd (.snd .v0))) posE
  have hmw := SimFig8State.cost_ssSetMirWin (O' := AOps) (Γ := Γ1) (.fst .v0)
  unfold fwdOnAcceptFinishE
  dsimp only [posE, fwdAccRrE, ssMk, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb,
    ssStopped, srecPos, pSet, Expr.v0, Expr.v1] at htr hch hac1 htv hac2 hmw ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Lq (Γ := Γ1) _ _ _ = etr at htr ⊢
  generalize mChallContainsE (O' := AOps) Lq (Γ := Γ2) _ _ = ech at hch ⊢
  generalize mAcceptE (O' := AOps) Lq (Γ := Γ2) _ _ _ = eac1 at hac1 ⊢
  generalize mTrivialE (O' := AOps) Lq (Γ := Γ1) _ _ = etv at htv ⊢
  generalize mAcceptE (O' := AOps) Lq (Γ := Γ1) _ _ _ = eac2 at hac2 ⊢
  generalize ssSetMirWin (O' := AOps) (Γ := Γ1) _ = emw at hmw ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at htr hch hac1 htv hac2 hmw ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdInTE_cost (Lq : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdInTE C K Dh encPt encT decT lam Lq sE qBE c'E).cost ≤
      sE.cost + qBE.cost + c'E.cost + 63100 * Lq + 200 := by
  let tupT := Ty.prod (simBaseT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let Γ1 := tupT :: Γ
  let Γ2 := Ty.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ1
  have heq := SimFig8Kept.eqFig8CAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd .v0) (.snd (.snd .v1))
  have htw := toWireAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.snd (.snd .v0))
  have htr := SimFig8State.cost_mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq (Γ := Γ1)
    (ssMir (.fst .v0)) (.not (.fst (.snd .v0)))
    (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.snd (.snd .v0)))
  let predE : Expr AOps Γ2 .bool :=
    eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.snd .v0) (.snd (.snd .v1))
  have hp : predE.cost + 1 ≤ 62800 := by
    dsimp only [predE, Expr.v0, Expr.v1] at heq ⊢
    generalize eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ2) _ _ = eeq at heq ⊢
    dsimp only [Expr.cost] at heq ⊢; omega
  have hmul : Lq * (predE.cost + 1) ≤ 62800 * Lq := by
    calc Lq * (predE.cost + 1) ≤ Lq * 62800 := Nat.mul_le_mul_left Lq hp
      _ = 62800 * Lq := Nat.mul_comm Lq 62800
  unfold fwdInTE
  dsimp only [ssHonest, ssMir, Expr.v0, Expr.v1] at htw htr ⊢
  change (eLet (.pair sE (.pair qBE c'E)) (.and (.anyB Lq _ predE) _)).cost ≤ _
  generalize predE = ep at hmul ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Lq (Γ := Γ1) _ _ _ = etr at htr ⊢
  generalize toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) _ = etw at htw htr
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at htw htr ⊢
  omega

private theorem fwdScAcceptUpdateE_cost (T : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (base'E : Expr AOps Γ (simBaseT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam T sCE base'E qBE cE).cost ≤
      sCE.cost + base'E.cost + qBE.cost + cE.cost + 21 * T + 16 * (ℓ / 32) + 2600100 := by
  let tupT := Ty.prod (simFullT ℓ Pt)
    (.prod (simBaseT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt))))
  let Γ1 := tupT :: Γ
  have hkr := keptRecvAtomicE_cost_tight C K idA idB Dh encPt encT decT lam T (Γ := Γ1)
    (pGet (scKept (.fst .v0)) (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  unfold fwdScAcceptUpdateE
  dsimp only [scMk, scKept, scSent, scSnaps, pGet, pSet, Expr.v0] at hkr ⊢
  generalize keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB T (Γ := Γ1) _ _ = ekr at hkr ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hkr ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdMkCE_cost {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat) (T?E : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    (fwdMkCE C K Dh encPt encT decT lam honestCE tE T?E lctE).cost ≤
      honestCE.cost + tE.cost + T?E.cost + lctE.cost + 60 := by
  let tupT := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (.prod .nat (.prod (.opt PtT) (lctT (ℓ := ℓ) (Pt := Pt))))
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: tupT :: Γ
  have hse := SimFig8Crypto.lctSaltEqOfLctAtomicE_cost (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2)
    .v0 (.snd (.snd (.snd .v1)))
  unfold fwdMkCE
  dsimp only [Expr.v0, Expr.v1] at hse ⊢
  generalize lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = ese at hse ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hse ⊢; omega

omit [SampleableType Pt] in
private theorem fwdEvictedE_cost {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    (fwdEvictedE C K Dh encPt encT decT lam honestCE sE qBE).cost ≤
      honestCE.cost + sE.cost + qBE.cost + 60 := by
  unfold fwdEvictedE
  dsimp only [pGet, mEpoch, ssMir, Expr.v0, Expr.v1, SimFig8State.cost_eLet, Expr.cost]
  simp only [hb1_c]; omega

omit [SampleableType Pt] in
private theorem fwdSaltEqE_cost {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    (fwdSaltEqE C K Dh encPt encT decT lam honestCE lctE).cost ≤
      honestCE.cost + lctE.cost + 35 := by
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) ::
    Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (lctT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hse := SimFig8Crypto.lctSaltEqOfLctAtomicE_cost (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) .v0 (.snd .v1)
  unfold fwdSaltEqE
  dsimp only [Expr.v0, Expr.v1] at hse ⊢
  generalize lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = ese at hse ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hse ⊢; omega

omit [SampleableType Pt] in
private theorem fwdScAmbE_cost {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    (fwdScAmbE C K Dh encPt encT decT lam sCE qBE).cost ≤ sCE.cost + qBE.cost + 260 := by
  let Γ1 := Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let Γ2 := Ty.prod (simBaseT ℓ Pt) .bool :: Γ1
  have hmw := SimFig8State.cost_mInWinE (O' := AOps) (Γ := Γ2) (ssMir (.fst .v0)) (.snd .v0)
  have hkn := SimFig8State.cost_anyChainKeyNoneE (O' := AOps) (Γ := Γ2)
    (pGet (ssChains (.fst .v0)) (.snd .v0))
  have hsa := SimFig8State.cost_ssSetAmb (O' := AOps) (Γ := Γ1)
    (scBase (.fst .v0)) (.add (ssAmb (scBase (.fst .v0))) (.nat 1))
  have hsb := SimFig8State.cost_scSetBase (O' := AOps) (Γ := Γ1)
    (.fst .v0) (ssSetAmb (scBase (.fst .v0)) (.add (ssAmb (scBase (.fst .v0))) (.nat 1)))
  unfold fwdScAmbE fwdAmbCondE
  dsimp only [orE, pGet, scBase, ssMir, ssChains, ssAmb, Expr.v0] at hmw hkn hsa hsb ⊢
  generalize scSetBase (O' := AOps) (Γ := Γ1) _ _ = esb at hsb ⊢
  generalize ssSetAmb (O' := AOps) (Γ := Γ1) _ _ = esa at hsa hsb
  generalize mInWinE (O' := AOps) (Γ := Γ2) _ _ = emw at hmw ⊢
  generalize anyChainKeyNoneE (O' := AOps) (Γ := Γ2) _ = ekn at hkn ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hmw hkn hsa hsb ⊢
  simp only [hb1_c] at hsa ⊢; omega

omit [SampleableType Pt] in
private theorem fwdNewGuardRejectE_cost {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) (iE : Expr AOps Γ .nat) :
    (fwdNewGuardRejectE C K Dh encPt encT decT lam sE qBE iE).cost ≤
      sE.cost + qBE.cost + iE.cost + 140 := by
  let Γ1 := Ty.prod (simBaseT ℓ Pt) (.prod .bool .nat) :: Γ
  have hmw := SimFig8State.cost_mInWinE (O' := AOps) (Γ := Γ1)
    (ssMir (.fst .v0)) (.fst (.snd .v0))
  have _ := hb25k_c; have _ := hb2p32_c
  unfold fwdNewGuardRejectE
  dsimp only [orE, ssMir, Expr.v0] at hmw ⊢
  generalize mInWinE (O' := AOps) (Γ := Γ1) _ _ = emw at hmw ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at hmw ⊢
  simp only [hb1_c]; omega

omit [SampleableType Pt] in
private theorem fwdRefuseE_cost (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool) :
    (fwdRefuseE C K Dh encPt encT decT lam Lq sE qBE wE isDelE).cost ≤
      sE.cost + qBE.cost + wE.cost + isDelE.cost + 400 * Lq + ℓ / 32 + 400 := by
  let Γ1 := Ty.prod (simBaseT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ
  have htr := SimFig8State.cost_mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq (Γ := Γ1)
    (ssMir (.fst .v0)) (.not (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hsi := SimFig8State.cost_mSafeInjE (O' := AOps) (Γ := Γ1) (ssMir (.fst .v0))
  have hij := SimFig8Crypto.injOKAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.fst (.snd (.snd .v0)))
  unfold fwdRefuseE
  dsimp only [orE, ssStopped, mWin, ssMir, Expr.v0] at htr hsi hij ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Lq (Γ := Γ1) _ _ _ = etr at htr ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γ1) _ = esi at hsi ⊢
  generalize injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) _ = eij at hij ⊢
  dsimp only [SimFig8State.cost_eLet, Expr.cost] at htr hsi hij ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdHonestCE_cost (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (fwdHonestCE C K Dh encPt encT decT lam Lq sE qBE wE).cost ≤
      sE.cost + qBE.cost + wE.cost + 120 * Lq + 40 := by
  have hb0 := hb0_c; have hb2 := hb2_c
  let Γ1 := Ty.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)) ::
    Ty.prod (simBaseT ℓ Pt) (.prod .bool (B 32)) :: Γ
  let predE : Expr AOps Γ1 .bool :=
    .and (sOpPure (.bytesEq 32 32) (.pair (.fst .v0) (.snd (.snd .v1))))
      (boolEq (.eqN (.modK 2 (.fst (.fst (.snd .v0)))) (.nat 0)) (.not (.fst (.snd .v1))))
  have hp : predE.cost + 1 ≤ 120 := by
    have h32 : ((32 : PNat) : ℕ) = 32 := rfl
    dsimp only [predE, boolEq, Expr.v0, Expr.v1, SimFig8State.cost_sOpPure,
      _root_.ReductionDsl.AtomicPureOp.cost, Expr.cost]
    rw [h32]; omega
  have hmul : Lq * (predE.cost + 1) ≤ 120 * Lq := by
    have := Nat.mul_le_mul_left Lq hp; omega
  unfold fwdHonestCE
  change (eLet (.pair sE (.pair qBE wE))
    (.caseOpt (.findB Lq (ssHonest (.fst .v0)) predE) .none (.some (.snd .v0)))).cost ≤ _
  generalize predE = ep at hmul ⊢
  dsimp only [ssHonest, Expr.v0, SimFig8State.cost_eLet, Expr.cost]
  omega

private theorem fwdOnAcceptC_cost (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK)
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32)) :
    (fwdOnAcceptC C K Dh encPt encT decT lam qep Lq sE ci?E pkE qBE wE isDelE tE iE mE pq'E).cost ≤
      sE.cost + ci?E.cost + pkE.cost + qBE.cost + wE.cost + isDelE.cost + tE.cost +
        iE.cost + mE.cost + pq'E.cost + 700 * Lq + bits (qep + 1) + 256000 := by
  let tupT := Ty.prod (simBaseT ℓ Pt) (.prod (.opt .nat) (.prod PK
    (.prod .bool (.prod (B 32) (.prod .bool (.prod .nat (.prod .nat
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B 32)))))))))
  let Γ1 := tupT :: Γ
  let Γ2 := ghostChainT ℓ Pt :: Γ1
  let Γ3 := Ty.nat :: Γ1
  let Γ4 := Ty.list (ghostChainT ℓ Pt) :: Γ1
  have hga := SimFig8State.ghostAcceptC_cost (O' := AOps) IDF (Γ := Γ1)
    (.pair (.some (.fst (.snd (.snd .v0))))
      (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))) (.pair (.nat 0) .nil)))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
  have hpc := SimFig8State.cost_pushChainE (O' := AOps) (Γ := Γ2)
    (pGet (ssChains (.fst .v1)) (.fst (.snd (.snd (.snd .v1))))) .v0
  have hmc := SimFig8State.modifyChainAcceptC_cost (O' := AOps) IDF (Γ := Γ3)
    (pGet (ssChains (.fst .v1)) (.fst (.snd (.snd (.snd .v1))))) .v0
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  have hfn := fwdOnAcceptFinishE_cost C K Dh encPt encT decT lam qep Lq (Γ := Γ4)
    (.fst .v1) .v0 (.fst (.snd (.snd (.snd .v1)))) (.fst (.snd (.snd (.snd (.snd .v1)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
  unfold fwdOnAcceptC
  dsimp only [pGet, ssChains, Expr.v0, Expr.v1] at hga hpc hmc hfn ⊢
  generalize ghostAcceptC (O' := AOps) IDF (Γ := Γ1) _ _ = ega at hga ⊢
  generalize pushChainE (O' := AOps) (Γ := Γ2) _ _ = epc at hpc ⊢
  generalize modifyChainAcceptC (O' := AOps) IDF (Γ := Γ3) _ _ _ = emc at hmc ⊢
  generalize fwdOnAcceptFinishE C K Dh encPt encT decT lam qep Lq (Γ := Γ4) _ _ _ _ _ _ _ _ _ = efn
    at hfn ⊢
  dsimp only [SimFig8State.cost_eLet, Comp.cost, Expr.cost] at hga hpc hmc hfn ⊢
  simp only [hb0_c] at hga ⊢; omega

private theorem fwdProbeC_cost (Lq : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (exE : Expr AOps Γ (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))) :
    (fwdProbeC C K Dh encPt encT decT lam Lq qBE c'E exE).cost ≤
      qBE.cost + c'E.cost + exE.cost + 63000 * Lq + 100100 := by
  let Γ1 := Ty.prod .bool (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))) :: Γ
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hsw := SimFig8Kept.sameWireFig8AtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) .v0 (.fst (.snd .v1))
  have hp : (sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ2) .v0 (.fst (.snd .v1))).cost + 1 ≤ 63000 := by
    dsimp only [Expr.v0, Expr.v1, Expr.cost] at hsw ⊢; omega
  have hmul : Lq * ((sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) .v0 (.fst (.snd .v1))).cost + 1) ≤
      63000 * Lq := by have := Nat.mul_le_mul_left Lq hp; omega
  unfold fwdProbeC
  dsimp only [Expr.v0, Expr.v1, Expr.v2] at hmul ⊢
  generalize sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = esw at hmul ⊢
  simp only [Comp.cost, Expr.cost]; omega

private theorem fwdEvalCKSC_cost (q : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdEvalCKSC C K idA idB Dh encPt encT decT lam q (50000 * q) (25001 * q + 25000) (2 ^ 32)
      sCE qBE wE cE c'E).cost ≤
      sCE.cost + qBE.cost + wE.cost + cE.cost + c'E.cost +
        2000000 * q + 7200000 := by
  let Γ1 := Ty.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt))))) :: Γ
  have hke := keptEvalAtomicE_cost_tight C K idA idB Dh encPt encT decT lam (50000 * q) (2 ^ 32)
    (Γ := Γ1) (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))
  have hse := sentEvalAtomicE_cost_tight C K idA idB Dh encPt encT decT lam q (2 ^ 32)
    (Γ := Γ1) (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
  have hse_mul : q * (ℓ / 16 + 230) ≤ 63000 * q := by
    have := Nat.mul_le_mul_left q (show ℓ / 16 + 230 ≤ 63000 by omega); omega
  have hor := fwdOrElseOptE_cost C K Dh encPt encT decT lam (Γ := Γ1)
    (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB (50000 * q) (2 ^ 32)
      (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))
    (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB q (2 ^ 32)
      (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0)))))
  have hks := SimFig8Crypto.knownSeedDecryptAtomicFastC_cost (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    idA idB q (25001 * q + 25000) (2 ^ 32) IDF (Γ := Γ1)
    (scSnaps (.fst .v0)) (.fst (.snd .v0)) (.fst (.fst (.fst (.snd (.snd (.snd .v0))))))
    (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))
  have hbKc := bits_le_succ_nat_local (25001 * q + 25000)
  have _ := hb2p32_c
  unfold fwdEvalCKSC
  dsimp only [pGet, scKept, scSent, scSnaps, Expr.v0] at hke hse hor hks ⊢
  generalize fwdOrElseOptE C K Dh encPt encT decT lam (Γ := Γ1) _ _ = eor at hor ⊢
  generalize keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (50000 * q) (2 ^ 32) (Γ := Γ1) _ _ = eke at hke hor
  generalize sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB q (2 ^ 32) (Γ := Γ1) _ _ _ = ese at hse hor
  generalize knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB q (25001 * q + 25000) (2 ^ 32) IDF (Γ := Γ1) _ _ _ _ _ = eks
    at hks ⊢
  dsimp only [SimFig8State.cost_eLet, Comp.cost, Expr.cost] at hke hse hor hks ⊢
  omega

private theorem fwdResyncC_cost (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (rE : Expr AOps Γ (.opt (kDecOutT ℓ Pt))) :
    (fwdResyncC C K idA idB Dh encPt encT decT lam qep q (50000 * q)
      stE qBE wE ci?E pkE pq'E cE rE).cost ≤
      stE.cost + qBE.cost + wE.cost + ci?E.cost + pkE.cost + pq'E.cost + cE.cost + rE.cost +
        1100000 * q + bits (qep + 1) + 3500000 := by
  let tupT := Ty.prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod (.opt .nat) (.prod PK (.prod (B 32)
      (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (.opt (kDecOutT ℓ Pt))))))))
  let rrPT := Ty.prod .nat (.prod .nat
    (.opt (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))))
  let rrT := smRrT (ℓ := ℓ) (Pt := Pt) (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))
  let Γ4 := rrPT :: rrT :: Ty.opt rrT :: kDecOutT ℓ Pt :: tupT :: Γ
  let accOutT := Ty.prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt)))) (simBaseT ℓ Pt)
  let Γ5 := accOutT :: Γ4
  have hoa := fwdOnAcceptC_cost C K Dh encPt encT decT lam qep q (Γ := Γ4)
    (scBase (.fst (.fst .v4))) (.fst (.snd (.snd (.snd .v4))))
    (.fst (.snd (.snd (.snd (.snd .v4))))) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.bool true) (.fst .v3) (.fst (.snd .v3)) (.snd (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
  have hup := fwdScAcceptUpdateE_cost C K idA idB Dh encPt encT decT lam (50000 * q) (Γ := Γ5)
    (.fst (.fst .v5)) (.snd .v0) (.fst (.snd .v5))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v5)))))))
  unfold fwdResyncC
  dsimp only [fwdRejOutE, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hoa hup ⊢
  generalize fwdOnAcceptC C K Dh encPt encT decT lam qep q (Γ := Γ4) _ _ _ _ _ _ _ _ _ _ = eoa at hoa ⊢
  generalize fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam (50000 * q) (Γ := Γ5) _ _ _ _ = eup
    at hup ⊢
  simp only [fig8SmIfaceDF, Comp.cost, Expr.cost] at hoa hup ⊢; omega

private theorem fwdAnswerC_cost (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdAnswerC C K idA idB Dh encPt encT decT lam qep q (50000 * q)
      stE qBE wE isDelE ci?E pkE pq'E c'E).cost ≤
      stE.cost + qBE.cost + wE.cost + isDelE.cost + ci?E.cost + pkE.cost + pq'E.cost + c'E.cost +
        1200000 * q + bits (qep + 1) + 3600000 := by
  let tupT := Ty.prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod .bool (.prod (.opt .nat) (.prod PK (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))
  let Γ1 := tupT :: Γ
  let rrPT := Ty.prod .nat (.prod .nat
    (.opt (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))))
  let rrT := smRrT (ℓ := ℓ) (Pt := Pt) (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))
  let Γ3 := rrPT :: rrT :: Ty.opt rrT :: Γ1
  let accOutT := Ty.prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt)))) (simBaseT ℓ Pt)
  let Γ4 := accOutT :: Γ3
  have hin := fwdInTE_cost C K Dh encPt encT decT lam q hℓ (Γ := Γ1)
    (scBase (.fst (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  have hdm := SimFig8Kept.defaultMcAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3)
  have hoa := fwdOnAcceptC_cost C K Dh encPt encT decT lam qep q (Γ := Γ3)
    (scBase (.fst (.fst .v3))) (.fst (.snd (.snd (.snd (.snd .v3)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v3)))))) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd .v3)))) (.fst .v0) (.fst (.snd .v0))
    (.caseOpt (.snd (.snd .v0))
      (.snd (.fst (defaultMcAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)))) (.snd .v0))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
  have hup := fwdScAcceptUpdateE_cost C K idA idB Dh encPt encT decT lam (50000 * q) (Γ := Γ4)
    (.fst (.fst .v4)) (.snd .v0) (.fst (.snd .v4))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
  unfold fwdAnswerC
  dsimp only [fwdRejOutE, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4] at hin hdm hoa hup ⊢
  generalize fwdInTE C K Dh encPt encT decT lam q (Γ := Γ1) _ _ _ = ein at hin ⊢
  generalize fwdOnAcceptC C K Dh encPt encT decT lam qep q (Γ := Γ3) _ _ _ _ _ _ _ _ _ _ = eoa at hoa ⊢
  generalize defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) = edm at hdm hoa
  generalize fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam (50000 * q) (Γ := Γ4) _ _ _ _ = eup
    at hup ⊢
  simp only [fig8SmIfaceDF, Comp.cost, Expr.cost] at hin hdm hoa hup ⊢; omega

private theorem fwdEvictC_cost (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdEvictC C K idA idB Dh encPt encT decT lam qep q stE qBE wE isDelE pkE pq'E c'E).cost ≤
      stE.cost + qBE.cost + wE.cost + isDelE.cost + pkE.cost + pq'E.cost + c'E.cost +
        1200000 * q + bits (qep + 1) + 3700000 := by
  let Γ1 := dfFwdEvictInT ℓ Pt :: Γ
  have hsi := SimFig8State.cost_mSafeInjE (O' := AOps) (Γ := Γ1) (ssMir (scBase (.fst (.fst .v0))))
  have hpr := fwdProbeC_cost C K Dh encPt encT decT lam q hℓ (Γ := Γ1)
    (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))) (.snd (.fst .v0))
  have han := fwdAnswerC_cost C K idA idB Dh encPt encT decT lam qep q hℓ (Γ := Γ1)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    .none (.fst (.snd (.snd (.snd (.snd .v0))))) (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  unfold fwdEvictC
  dsimp only [fwdRejOutE, ssMir, scBase, Expr.v0, Expr.v1] at hsi hpr han ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γ1) _ = esi at hsi ⊢
  generalize fwdProbeC C K Dh encPt encT decT lam q (Γ := Γ1) _ _ _ = epr at hpr ⊢
  generalize fwdAnswerC C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ1)
    _ _ _ _ _ _ _ _ = ean at han ⊢
  dsimp only [Comp.cost, Expr.cost] at hsi hpr han ⊢; omega

private theorem fwdHookC_cost (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fwdHookC C K idA idB Dh encPt encT decT lam qep q
      stE qBE wE isDelE ci?E pkE pq'E honestCE c'E).cost ≤
      stE.cost + qBE.cost + wE.cost + isDelE.cost + ci?E.cost + pkE.cost + pq'E.cost +
        honestCE.cost + c'E.cost + 3200000 * q + bits (qep + 1) + 11000000 := by
  let Γ1 := dfFwdInT ℓ Pt :: Γ
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := Ty.opt (Ty.opt (kDecOutT ℓ Pt)) :: Γ2
  let Γ4 := Ty.opt (kDecOutT ℓ Pt) :: Γ3
  have han1 := fwdAnswerC_cost C K idA idB Dh encPt encT decT lam qep q hℓ (Γ := Γ1)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.fst (.snd (.snd (.snd (.snd .v0))))) (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
  have heq := SimFig8Kept.eqFig8CAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2)
    .v0 (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  have hsi := SimFig8State.cost_mSafeInjE (O' := AOps) (Γ := Γ2) (ssMir (scBase (.fst (.fst .v1))))
  have hek := fwdEvalCKSC_cost C K idA idB Dh encPt encT decT lam q hℓ (Γ := Γ2)
    (.fst (.fst .v1)) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    .v0 (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  have hpr := fwdProbeC_cost C K Dh encPt encT decT lam q hℓ (Γ := Γ3)
    (.fst (.snd .v2)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))) (.snd (.fst .v2))
  have hrs := fwdResyncC_cost C K idA idB Dh encPt encT decT lam qep q hℓ (Γ := Γ4)
    (.fst .v3) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))) .v2 .v0
  have han2 := fwdAnswerC_cost C K idA idB Dh encPt encT decT lam qep q hℓ (Γ := Γ2)
    (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  unfold fwdHookC
  dsimp only [fwdRejOutE, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    at han1 heq hsi hek hpr hrs han2 ⊢
  generalize fwdAnswerC C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ1)
    _ _ _ _ _ _ _ _ = ea1 at han1 ⊢
  generalize eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = eeq at heq ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γ2) _ = esi at hsi ⊢
  generalize fwdEvalCKSC C K idA idB Dh encPt encT decT lam q (50000 * q) (25001 * q + 25000)
    (2 ^ 32) (Γ := Γ2) _ _ _ _ _ = eek at hek ⊢
  generalize fwdProbeC C K Dh encPt encT decT lam q (Γ := Γ3) _ _ _ = epr at hpr ⊢
  generalize fwdResyncC C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ4)
    _ _ _ _ _ _ _ _ = ers at hrs ⊢
  generalize fwdAnswerC C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ2)
    _ _ _ _ _ _ _ _ = ea2 at han2 ⊢
  dsimp only [Comp.cost, Expr.cost] at han1 heq hsi hek hpr hrs han2 ⊢; omega

theorem fwdRecvNewC_queries (qep q : ℕ) :
    (fwdRecvNewC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  dsimp only [fwdRecvNewC]
  simp only [Comp.queries]
  have he := fwdEvictC_queries C K idA idB Dh encPt encT decT lam qep q
    (Γ := [PtT (ℓ := ℓ) (Pt := Pt), dfRecvNewInT ℓ Pt])
  have hh := fwdHookC_queries C K idA idB Dh encPt encT decT lam qep q
    (Γ := [PtT (ℓ := ℓ) (Pt := Pt), dfRecvNewInT ℓ Pt])
  refine Nat.max_le.mpr ⟨by omega, Nat.max_le.mpr ⟨by omega, Nat.max_le.mpr ⟨by omega,
    Nat.max_le.mpr ⟨by omega, Nat.max_le.mpr ⟨he _ _ _ _ _ _ _, hh _ _ _ _ _ _ _ _ _⟩⟩⟩⟩⟩

theorem fwdRecvNewC_cost (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    (fwdRecvNewC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q).cost ≤
      25000000 + 15000000 * q + 512 * bits (qep + 1) := by
  let Γ0 : List (Ty ASig) := [dfRecvNewInT ℓ Pt]
  let Γ1 : List (Ty ASig) := [PtT (ℓ := ℓ) (Pt := Pt), dfRecvNewInT ℓ Pt]
  have hev0 := fwdEvictedE_cost C K Dh encPt encT decT lam (Γ := Γ0)
    (.snd (.snd (.snd (.snd (.snd .v0))))) (scBase (.fst (.fst .v0))) (.fst (.snd .v0))
  have hse0 := fwdSaltEqE_cost C K Dh encPt encT decT lam (Γ := Γ0)
    (.snd (.snd (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
  have hzr := SimFig8Crypto.isZeroPtOptAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0)
    (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
  have hgr := fwdNewGuardRejectE_cost C K Dh encPt encT decT lam (Γ := Γ0)
    (scBase (.fst (.fst .v0))) (.fst (.snd .v0))
    (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))
  have ham0 := fwdScAmbE_cost C K Dh encPt encT decT lam (Γ := Γ0) (.fst (.fst .v0)) (.fst (.snd .v0))
  have hev1 := fwdEvictedE_cost C K Dh encPt encT decT lam (Γ := Γ1)
    (.snd (.snd (.snd (.snd (.snd .v1))))) (scBase (.fst (.fst .v1))) (.fst (.snd .v1))
  have ham1 := fwdScAmbE_cost C K Dh encPt encT decT lam (Γ := Γ1) (.fst (.fst .v1)) (.fst (.snd .v1))
  let nextEp : Expr AOps Γ1 .nat :=
    .add (pGet (mEpoch (ssMir (scBase (.fst (.fst .v1))))) (.fst (.snd .v1))) (.nat 1)
  let lct1 : Expr AOps Γ1 (lctT (ℓ := ℓ) (Pt := Pt)) :=
    .snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v1))))))))
  let stAmb1 : Expr AOps Γ1 (dfStepT ℓ Pt) :=
    .pair (fwdScAmbE C K Dh encPt encT decT lam (.fst (.fst .v1)) (.fst (.snd .v1))) (.snd (.fst .v1))
  have hmk := fwdMkCE_cost C K Dh encPt encT decT lam (Γ := Γ1)
    (.snd (.snd (.snd (.snd (.snd .v1))))) nextEp (.some .v0) lct1
  have hevc := fwdEvictC_cost C K idA idB Dh encPt encT decT lam qep q hℓ (Γ := Γ1)
    stAmb1 (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v1))))))))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1)))))) (.pair (.pair nextEp (.some .v0)) lct1)
  have hhkc := fwdHookC_cost C K idA idB Dh encPt encT decT lam qep q hℓ (Γ := Γ1)
    stAmb1 (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))) .none
    (.fst (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v1))))))))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1)))))) (.snd (.snd (.snd (.snd (.snd .v1)))))
    (fwdMkCE C K Dh encPt encT decT lam (.snd (.snd (.snd (.snd (.snd .v1))))) nextEp (.some .v0) lct1)
  unfold fwdRecvNewC
  dsimp only [nextEp, lct1, stAmb1, fwdRejOutE, pGet, mEpoch, ssMir, scBase, Expr.v0, Expr.v1]
    at hev0 hse0 hzr hgr ham0 hev1 ham1 hmk hevc hhkc ⊢
  generalize fwdEvictC C K idA idB Dh encPt encT decT lam qep q (Γ := Γ1) _ _ _ _ _ _ _ = eevc
    at hevc ⊢
  generalize fwdHookC C K idA idB Dh encPt encT decT lam qep q (Γ := Γ1) _ _ _ _ _ _ _ _ _ = ehkc
    at hhkc ⊢
  generalize fwdMkCE C K Dh encPt encT decT lam (Γ := Γ1) _ _ _ _ = emk at hmk hhkc
  generalize fwdScAmbE C K Dh encPt encT decT lam (Γ := Γ1) _ _ = eam1 at ham1 hevc hhkc
  generalize fwdScAmbE C K Dh encPt encT decT lam (Γ := Γ0) _ _ = eam0 at ham0 ⊢
  generalize fwdEvictedE C K Dh encPt encT decT lam (Γ := Γ0) _ _ _ = eev0 at hev0 ⊢
  generalize fwdEvictedE C K Dh encPt encT decT lam (Γ := Γ1) _ _ _ = eev1 at hev1 ⊢
  generalize fwdSaltEqE C K Dh encPt encT decT lam (Γ := Γ0) _ _ = ese0 at hse0 ⊢
  generalize isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ0) _ = ezr at hzr ⊢
  generalize fwdNewGuardRejectE C K Dh encPt encT decT lam (Γ := Γ0) _ _ _ = egr at hgr ⊢
  dsimp only [SimFig8State.cost_eLet, Comp.cost, Expr.cost]
    at hev0 hse0 hzr hgr ham0 hev1 ham1 hmk hevc hhkc ⊢
  simp only [hb1_c] at hmk hevc hhkc ⊢; omega

private theorem hb2_eq : bits 2 = 2 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb3_c : bits 3 = 2 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb4_c : bits 4 = 3 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb5_c : bits 5 = 3 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb32_c : bits 32 = 6 :=
  SimFig8State.bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem hb32p_c : bits ((32 : ℕ+) : ℕ) = 6 := hb32_c
private theorem hb_ell (hℓ : ℓ < 10 ^ 6) : bits ℓ ≤ 20 :=
  SimFig8State.bits_le_of_lt_pow (by omega) (by omega)

omit [SampleableType Pt] in
private theorem fwdNoneOutE_descBits_le (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdNoneOutE C K Dh encPt encT decT lam stE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits stE + 100 := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  dsimp only [fwdNoneOutE, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits]
  omega

omit [SampleableType Pt] in
private theorem fwdRejOutE_descBits_le (hℓ : ℓ < 10 ^ 6) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdRejOutE C K Dh encPt encT decT lam stE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits stE + 100 := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  dsimp only [fwdRejOutE, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits]
  omega

private theorem bits_50k_le_budget (q qep : ℕ) :
    bits (50000 * q) ≤ 16 + bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have hq := SimFig8SpqrDesc.bits_L_le_budget q qep
  calc bits (50000 * q)
      ≤ 16 + bits q := SimFig8SpqrDesc.bits_mul_le_add (by omega) (show 50000 ≤ 2 ^ 16 by omega)
    _ ≤ 16 + bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by omega

private theorem bits_25k1_le_budget (q qep : ℕ) :
    bits (25001 * q + 25000) ≤ 16 + bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have hbud := SessionProgCommon.session_cost_le_ratchetCostBudget q (qep + 1) 1 0 1 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hle : 25001 * q + 25000 ≤ 2 ^ 15 * (ratchetCostBudget q (qep + 1) + (qep + 1)) := by omega
  calc bits (25001 * q + 25000)
      ≤ bits (2 ^ 15 * (ratchetCostBudget q (qep + 1) + (qep + 1))) :=
        _root_.ReductionDsl.bits_mono hle
    _ ≤ 15 + bits (ratchetCostBudget q (qep + 1) + (qep + 1)) :=
        SimFig8SpqrDesc.bits_mul_le_add (by omega) (le_refl _)
    _ ≤ 16 + bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by omega

omit [SampleableType Pt] in
private theorem fsReceiveAtomicE_descBits_tight (B0 B_cap : ℕ) {Γ : List (Ty ASig)}
    (vE : Expr AOps Γ (ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B0 B_cap vE cE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits vE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits cE +
      6 * bits B0 + 4 * bits B_cap + 18000 := by
  have hr := SimFig8State.descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B_cap)
    (.pair vE cE)
  have hf := SimFig8SpqrDesc.fsRecvExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam) B0 B_cap
  dsimp only [fsReceiveAtomicE, KemFailRedLoopAndCost.atomicExprDescBits] at hr ⊢
  omega

omit [SampleableType Pt] in
private theorem fig8ReceiveAtomicE_descBits_tight (B0 B_cap : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B0 B_cap stE cE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits stE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits cE +
      6 * bits B0 + 8 * bits B_cap + 23000 := by
  let t0 := Ty.prod (ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let Γ1 := t0 :: Γ
  let Γ2 := PtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := Ty.prod (ReductionDsl.ckaStT (ℓ := ℓ) (Pt := Pt)) PtT :: Γ2
  let Γ4 := ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt) ::
    ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hcka := SimFig8State.descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.ckaRecvExpr ℓ Pt C Dh encPt encT lam)
    (.pair (SimFig8Kept.f8Gamma (.fst .v1)) .v0)
  have hup := SimFig8State.descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr ℓ Pt C Dh encPt encT lam)
    (.pair (SimFig8Kept.f8Root (.fst .v2)) (.snd .v0))
  have hfs := fsReceiveAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam B0 B_cap
    (Γ := Γ4) .v0 (.snd .v2)
  have hd_cka := SimFig8SpqrDesc.ckaRecvExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_up := SimFig8SpqrDesc.prngUpExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have ht_f8 := SimFig8State.atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt)
  unfold fig8ReceiveAtomicE
  dsimp only [SimFig8Kept.f8Mk, SimFig8Kept.f8Id, SimFig8Kept.f8Root, SimFig8Kept.f8VS,
    SimFig8Kept.f8VR, SimFig8Kept.f8Gamma, SimFig8Kept.f8Cur, SimFig8Kept.f8Tcur, orE,
    CryptoGames.SM.sendsInE, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hcka hup hfs ⊢
  generalize SimFig8State.runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.ckaRecvExpr ℓ Pt C Dh encPt encT lam) _ = e_rcka
    at hcka ⊢
  generalize SimFig8State.runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3)
    (Computational.Proofs.ReductionDsl.Fig8Atomic.prngUpExpr ℓ Pt C Dh encPt encT lam) _ = e_rup
    at hup ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B0 B_cap (Γ := Γ4) _ _ = e_rfs at hfs ⊢
  dsimp only [eLet, lpubT, PlainT, B, _root_.ReductionDsl.U32, _root_.ReductionDsl.BV256,
    KemFailRedLoopAndCost.atomicExprDescBits, KemFailRedLoopAndCost.atomicTyDescBits,
    KemFailRedLoopAndCost.atomicSortDescBits] at hcka hup hfs ⊢
  simp only [KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_c, hb1_c, hb2_eq, hb3_c, hb32p_c] at hcka hup hfs ⊢
  omega

omit [SampleableType Pt] in
private theorem sanAtAtomicE_descBits_tight (T : ℕ) {Γ : List (Ty ASig)}
    (tE : Expr AOps Γ .nat) (stE : Expr AOps Γ (ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (SimFig8Kept.sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) T tE stE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits tE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits stE +
      2 * bits T + 2000 := by
  let tP := Ty.prod .nat (ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt))
  have hrs := SimFig8Kept.sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps) T
    atomicSessionOpDescBits (Γ := ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tP :: Γ) .v0
  have hγ := SimFig8Kept.sanGammaAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := tP :: Γ) (.snd .v0)
  have ht_fsR := SimFig8State.atomicTyDescBits_fsRecvStT (ℓ := ℓ) (Pt := Pt)
  dsimp only [SimFig8Kept.sanAtAtomicE, SimFig8Kept.f8Mk, SimFig8Kept.f8Id, SimFig8Kept.f8Root,
    SimFig8Kept.f8VS, SimFig8Kept.f8VR, SimFig8Kept.f8Cur, SimFig8Kept.f8Tcur, Expr.v0]
    at hrs hγ ⊢
  generalize SimFig8Kept.sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T _ = e_rs at hrs ⊢
  generalize SimFig8Kept.sanGammaAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = e_g at hγ ⊢
  simp only [SimFig8State.descBits_eLet, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.varIdx, hb0_c] at hrs hγ ⊢
  omega

omit [SampleableType Pt] in
private theorem keptRecvAtomicE_descBits_tight (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB T kE cE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits kE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits cE +
      16 * bits T + 45000 := by
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  let ΓS := ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := SimFig8Kept.sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps) T
    atomicSessionOpDescBits (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam T 0 (Γ := ΓN)
    (SimFig8Kept.sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_descBits_tight C K Dh encPt encT decT lam T (Γ := ΓS)
    (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam T 0 (Γ := ΓS)
    (SimFig8Kept.sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have ht_f8 := SimFig8State.atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt)
  have ht_fsR := SimFig8State.atomicTyDescBits_fsRecvStT (ℓ := ℓ) (Pt := Pt)
  dsimp only [keptRecvAtomicE, SimFig8Kept.f8VR, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize SimFig8Kept.sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs
    at hrs hfs ⊢
  generalize SimFig8Kept.sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  simp only [SimFig8State.descBits_eLet, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c, hb2_eq] at hrs hfs hat hf8 ⊢
  omega

omit [SampleableType Pt] in
private theorem keptEvalAtomicE_descBits_tight (hℓ : ℓ < 10 ^ 6) (T B_cap : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB T B_cap kE cE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits kE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits cE +
      16 * bits T + 12 * bits B_cap + 45000 := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := ReductionDsl.fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  let ΓS := ReductionDsl.fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := SimFig8Kept.sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps) T
    atomicSessionOpDescBits (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam T B_cap (Γ := ΓN)
    (SimFig8Kept.sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_descBits_tight C K Dh encPt encT decT lam T (Γ := ΓS)
    (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam T B_cap (Γ := ΓS)
    (SimFig8Kept.sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  dsimp only [keptEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B_cap (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize SimFig8Kept.sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs
    at hrs hfs ⊢
  generalize SimFig8Kept.sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  dsimp only [eLet, lpubT, PlainT, B, _root_.ReductionDsl.U32, _root_.ReductionDsl.BV256,
    KemFailRedLoopAndCost.atomicExprDescBits, KemFailRedLoopAndCost.atomicTyDescBits,
    KemFailRedLoopAndCost.atomicSortDescBits] at hrs hfs hat hf8 ⊢
  simp only [KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_c, hb1_c, hb2_eq, hb32p_c] at hrs hfs hat hf8 ⊢
  omega

omit [SampleableType Pt] in
private theorem sentEvalAtomicE_descBits_tight (hℓ : ℓ < 10 ^ 6) (L B_cap : ℕ) {Γ : List (Ty ASig)}
    (sentE : Expr AOps Γ (.list (sentEntryT ℓ Pt)))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB L B_cap sentE cE c'E) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sentE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits cE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits c'E +
      2 * bits L + 4 * bits B_cap + 20000 := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  let t0 := Ty.prod (.list (sentEntryT ℓ Pt))
    (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let Γ1 := sentEntryT ℓ Pt :: t0 :: Γ
  have heq := SimFig8Kept.eqFig8CAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.fst (.snd .v1))
  have hvr := SimFig8Kept.senderToFreshVrAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (O' := AOps)
    atomicSessionOpDescBits (Γ := Γ1) (.snd .v0)
  have hfs := fsReceiveAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam 0 B_cap (Γ := Γ1)
    (SimFig8Kept.senderToFreshVrAtomicE (.snd .v0)) (.snd (.snd .v1))
  dsimp only [sentEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at heq hvr hfs ⊢
  generalize eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) _ _ = e_eq at heq ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 B_cap (Γ := Γ1) _ _ = e_fs at hfs ⊢
  generalize SimFig8Kept.senderToFreshVrAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ = e_vr
    at hvr hfs ⊢
  dsimp only [eLet, lpubT, PlainT, B, _root_.ReductionDsl.U32, _root_.ReductionDsl.BV256,
    KemFailRedLoopAndCost.atomicExprDescBits, KemFailRedLoopAndCost.atomicTyDescBits,
    KemFailRedLoopAndCost.atomicSortDescBits] at heq hvr hfs ⊢
  simp only [KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_c, hb1_c, hb2_eq, hb32p_c] at heq hvr hfs ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdOrElseOptE_descBits_le {Γ : List (Ty ASig)} {a : Ty ASig}
    (e1 e2 : Expr AOps Γ (.opt a)) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdOrElseOptE C K Dh encPt encT decT lam e1 e2) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits e1 +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits e2 + 60 := by
  dsimp only [fwdOrElseOptE, eLet, Expr.v0, KemFailRedLoopAndCost.atomicExprDescBits]
  simp only [KemFailRedLoopAndCost.varIdx, hb0_c]; omega

omit [SampleableType Pt] in
private theorem fwdOnAcceptFinishE_descBits_le (hℓ : ℓ < 10 ^ 6) (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (csE : Expr AOps Γ (.list (ghostChainT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32)) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdOnAcceptFinishE C K Dh encPt encT decT lam qep Lq sE csE qBE wE isDelE tE iE mE pq'E) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits csE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits isDelE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits tE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits iE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits mE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pq'E +
      24 * bits Lq + 2 * bits (qep + 1) + 16000 := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  let tupT := Ty.prod (simBaseT ℓ Pt) (.prod (.list (ghostChainT ℓ Pt))
    (.prod .bool (.prod (B 32) (.prod .bool (.prod .nat (.prod .nat
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B 32))))))))
  let Γ1 := tupT :: Γ
  let Γ2 := SimFig8LoopAndCost.simRecT ℓ Pt :: Γ1
  have htr := SimFig8State.mInTransitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq (Γ := Γ1)
    (ssMir (.fst .v0)) (.not (.fst (.snd (.snd .v0)))) (.fst (.snd (.snd (.snd .v0))))
  have hcc := SimFig8State.mChallContainsE_descBits_le (O' := AOps) atomicSessionOpDescBits Lq
    (Γ := Γ2) (ssMir (.fst .v1)) (srecPos .v0)
  have hac1 := SimFig8State.mAcceptE_descBits_le (O' := AOps) atomicSessionOpDescBits Lq
    (Γ := Γ2) (ssMir (.fst .v1)) (.fst (.snd (.snd .v1))) (srecPos .v0)
  have htv := SimFig8State.mTrivialE_descBits_le (O' := AOps) atomicSessionOpDescBits Lq
    (Γ := Γ1) (ssMir (.fst .v0)) (.pair (.not (.fst (.snd (.snd .v0))))
      (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))))
  have hac0 := SimFig8State.mAcceptE_descBits_le (O' := AOps) atomicSessionOpDescBits Lq
    (Γ := Γ1) (ssMir (.fst .v0)) (.fst (.snd (.snd .v0))) (.pair (.not (.fst (.snd (.snd .v0))))
      (.pair (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
        (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))))
  have hmw := SimFig8State.ssSetMirWin_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ1)
    (.fst .v0)
  unfold fwdOnAcceptFinishE
  dsimp only [fwdAccRrE, ssMir, ssPq, ssPn, ssUnackA, ssHonest, ssChains, ssAmb, ssStopped,
    ssMk, pSet, srecPos, Expr.v0, Expr.v1] at htr hcc hac1 htv hac0 hmw ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Lq (Γ := Γ1) _ _ _ = etr at htr ⊢
  generalize mChallContainsE (ℓ := ℓ) (Pt := Pt) (O' := AOps) Lq (Γ := Γ2) _ _ = ecc at hcc ⊢
  generalize mAcceptE (ℓ := ℓ) (Pt := Pt) (O' := AOps) Lq (Γ := Γ2) _ _ _ = eac1 at hac1 ⊢
  generalize mTrivialE (ℓ := ℓ) (Pt := Pt) (O' := AOps) Lq (Γ := Γ1) _ _ = etv at htv ⊢
  generalize mAcceptE (ℓ := ℓ) (Pt := Pt) (O' := AOps) Lq (Γ := Γ1) _ _ _ = eac0 at hac0 ⊢
  generalize ssSetMirWin (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ = emw at hmw ⊢
  dsimp only [eLet, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits]
    at htr hcc hac1 htv hac0 hmw ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c]
    at htr hcc hac1 htv hac0 hmw ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdInTE_descBits_le (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdInTE C K Dh encPt encT decT lam Lq sE qBE c'E) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits c'E +
      4 * bits Lq + 2200 := by
  let Γ1 := Ty.prod (simBaseT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt))) :: Γ
  let Γ2 := Ty.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ1
  have heq := SimFig8Kept.eqFig8CAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd .v0) (.snd (.snd .v1))
  have htw := toWireAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.snd (.snd .v0))
  have htr := SimFig8State.mInTransitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq (Γ := Γ1)
    (ssMir (.fst .v0)) (.not (.fst (.snd .v0)))
    (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.snd (.snd .v0)))
  unfold fwdInTE
  dsimp only [ssHonest, ssMir, Expr.v0, Expr.v1] at heq htw htr ⊢
  generalize eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = eeq at heq ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Lq (Γ := Γ1) _ _ _ = etr at htr ⊢
  generalize toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) _ = etw at htw htr
  dsimp only [eLet, KemFailRedLoopAndCost.atomicExprDescBits] at heq htw htr ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c] at heq htw htr ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdScAcceptUpdateE_descBits_le (T : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (base'E : Expr AOps Γ (simBaseT ℓ Pt))
    (qBE : Expr AOps Γ .bool) (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam T sCE base'E qBE cE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sCE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits base'E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits cE +
      16 * bits T + 46000 := by
  let Γ1 := Ty.prod (simFullT ℓ Pt)
    (.prod (simBaseT ℓ Pt) (.prod .bool (fig8CtT (ℓ := ℓ) (Pt := Pt)))) :: Γ
  have hkr := keptRecvAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam T (Γ := Γ1)
    (pGet (scKept (.fst .v0)) (.fst (.snd (.snd .v0)))) (.snd (.snd (.snd .v0)))
  unfold fwdScAcceptUpdateE
  dsimp only [scKept, scSent, scSnaps, scMk, pGet, pSet, Expr.v0] at hkr ⊢
  generalize keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB T (Γ := Γ1) _ _ = ekr at hkr ⊢
  dsimp only [eLet, KemFailRedLoopAndCost.atomicExprDescBits] at hkr ⊢
  simp only [KemFailRedLoopAndCost.varIdx, hb0_c] at hkr ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdMkCE_descBits_le {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (tE : Expr AOps Γ .nat) (T?E : Expr AOps Γ (.opt PtT))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdMkCE C K Dh encPt encT decT lam honestCE tE T?E lctE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits honestCE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits tE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits T?E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits lctE + 500 := by
  let Γ1 := Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (.prod .nat (.prod (.opt PtT) (lctT (ℓ := ℓ) (Pt := Pt)))) :: Γ
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hl := SimFig8Crypto.lctSaltEqOfLctAtomicE_descBits_le (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2)
    .v0 (.snd (.snd (.snd .v1)))
  unfold fwdMkCE
  dsimp only [Expr.v0, Expr.v1] at hl ⊢
  generalize lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = el at hl ⊢
  dsimp only [eLet, KemFailRedLoopAndCost.atomicExprDescBits] at hl ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c] at hl ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdEvictedE_descBits_le {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdEvictedE C K Dh encPt encT decT lam honestCE sE qBE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits honestCE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE + 250 := by
  dsimp only [fwdEvictedE, eLet, pGet, mEpoch, ssMir, Expr.v0, Expr.v1,
    KemFailRedLoopAndCost.atomicExprDescBits]
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c]; omega

omit [SampleableType Pt] in
private theorem fwdSaltEqE_descBits_le {Γ : List (Ty ASig)}
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdSaltEqE C K Dh encPt encT decT lam honestCE lctE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits honestCE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits lctE + 200 := by
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) ::
    Ty.prod (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))) (lctT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hl := SimFig8Crypto.lctSaltEqOfLctAtomicE_descBits_le (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) .v0 (.snd .v1)
  unfold fwdSaltEqE
  dsimp only [Expr.v0, Expr.v1] at hl ⊢
  generalize lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = el at hl ⊢
  dsimp only [eLet, KemFailRedLoopAndCost.atomicExprDescBits] at hl ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c] at hl ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdScAmbE_descBits_le {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdScAmbE C K Dh encPt encT decT lam sCE qBE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sCE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE + 1800 := by
  let Γ1 := Ty.prod (simFullT ℓ Pt) .bool :: Γ
  let Γ2 := Ty.prod (simBaseT ℓ Pt) .bool :: Γ1
  have hmw := SimFig8State.mInWinE_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ2)
    (ssMir (.fst .v0)) (.snd .v0)
  have hck := SimFig8State.anyChainKeyNoneE_descBits_le (O' := AOps) atomicSessionOpDescBits
    (Γ := Γ2) (pGet (ssChains (.fst .v0)) (.snd .v0))
  have hsa := SimFig8State.ssSetAmb_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ1)
    (scBase (.fst .v0)) (.add (ssAmb (scBase (.fst .v0))) (.nat 1))
  have hsb := SimFig8State.scSetBase_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ1)
    (.fst .v0) (ssSetAmb (scBase (.fst .v0)) (.add (ssAmb (scBase (.fst .v0))) (.nat 1)))
  unfold fwdScAmbE fwdAmbCondE
  dsimp only [scBase, ssMir, ssChains, ssAmb, pGet, orE, Expr.v0] at hmw hck hsa hsb ⊢
  generalize mInWinE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ2) _ _ = emw at hmw ⊢
  generalize anyChainKeyNoneE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ2) _ = eck at hck ⊢
  generalize scSetBase (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ _ = esb at hsb ⊢
  generalize ssSetAmb (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ _ = esa at hsa hsb
  dsimp only [eLet, KemFailRedLoopAndCost.atomicExprDescBits] at hmw hck hsa hsb ⊢
  simp only [KemFailRedLoopAndCost.varIdx, hb0_c, hb1_c] at hmw hck hsa hsb ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdNewGuardRejectE_descBits_le {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) (iE : Expr AOps Γ .nat) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdNewGuardRejectE C K Dh encPt encT decT lam sE qBE iE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits iE + 800 := by
  let Γ1 := Ty.prod (simBaseT ℓ Pt) (.prod .bool .nat) :: Γ
  have hmw := SimFig8State.mInWinE_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ1)
    (ssMir (.fst .v0)) (.fst (.snd .v0))
  have _ := hb25k_c; have _ := hb2p32_c
  unfold fwdNewGuardRejectE
  dsimp only [ssMir, orE, Expr.v0] at hmw ⊢
  generalize mInWinE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ _ = emw at hmw ⊢
  dsimp only [eLet, KemFailRedLoopAndCost.atomicExprDescBits] at hmw ⊢
  simp only [KemFailRedLoopAndCost.varIdx, hb0_c, hb1_c] at hmw ⊢
  omega

private theorem fwdOnAcceptC_descBits_le (hℓ : ℓ < 10 ^ 6) (qep Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK)
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool)
    (tE iE : Expr AOps Γ .nat) (mE : Expr AOps Γ (PlainT (ℓ := ℓ) (Pt := Pt)))
    (pq'E : Expr AOps Γ (B 32)) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdOnAcceptC C K Dh encPt encT decT lam qep Lq sE ci?E pkE qBE wE isDelE tE iE mE pq'E) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits ci?E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pkE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits isDelE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits tE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits iE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits mE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pq'E +
      24 * bits Lq + 2 * bits (qep + 1) + 31000 := by
  let tupT := Ty.prod (simBaseT ℓ Pt) (.prod (.opt .nat) (.prod PK
    (.prod .bool (.prod (B 32) (.prod .bool (.prod .nat (.prod .nat
      (.prod (PlainT (ℓ := ℓ) (Pt := Pt)) (B 32)))))))))
  let Γ1 := tupT :: Γ
  let Γ2 := ghostChainT ℓ Pt :: Γ1
  let Γ3 := Ty.nat :: Γ1
  let Γ4 := Ty.list (ghostChainT ℓ Pt) :: Γ1
  have hga := SimFig8State.ghostAcceptC_descBits_le (O' := AOps) atomicSessionOpDescBits IDF
    (fun _ => 8) (fun _ => 8) (Γ := Γ1)
    (.pair (.some (.fst (.snd (.snd .v0))))
      (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))) (.pair (.nat 0) .nil)))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
  have hpc := SimFig8State.pushChainE_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ2)
    (pGet (ssChains (.fst .v1)) (.fst (.snd (.snd (.snd .v1))))) .v0
  have hmc := SimFig8State.modifyChainAcceptC_descBits_le (O' := AOps) atomicSessionOpDescBits IDF
    (fun _ => 8) (fun _ => 8) (Γ := Γ3)
    (pGet (ssChains (.fst .v1)) (.fst (.snd (.snd (.snd .v1))))) .v0
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  have hfn := fwdOnAcceptFinishE_descBits_le C K Dh encPt encT decT lam hℓ qep Lq (Γ := Γ4)
    (.fst .v1) .v0 (.fst (.snd (.snd (.snd .v1)))) (.fst (.snd (.snd (.snd (.snd .v1)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))))
  unfold fwdOnAcceptC
  dsimp only [pGet, ssChains, Expr.v0, Expr.v1] at hga hpc hmc hfn ⊢
  generalize ghostAcceptC (O' := AOps) IDF (Γ := Γ1) _ _ = ega at hga ⊢
  generalize pushChainE (O' := AOps) (Γ := Γ2) _ _ = epc at hpc ⊢
  generalize modifyChainAcceptC (O' := AOps) IDF (Γ := Γ3) _ _ _ = emc at hmc ⊢
  generalize fwdOnAcceptFinishE C K Dh encPt encT decT lam qep Lq (Γ := Γ4) _ _ _ _ _ _ _ _ _ = efn
    at hfn ⊢
  dsimp only [atomicCompDescBits, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits] at hga hpc hmc hfn ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c] at hga hpc hmc hfn ⊢
  omega

private theorem fwdProbeC_descBits_le (Lq : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (exE : Expr AOps Γ (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdProbeC C K Dh encPt encT decT lam Lq qBE c'E exE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits c'E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits exE +
      2 * bits Lq + 1100 := by
  let t0 := Ty.prod .bool (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt))
    (.list (fig8CtT (ℓ := ℓ) (Pt := Pt))))
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: t0 :: Γ
  have hsw := SimFig8Kept.sameWireFig8AtomicE_descBits_le (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) .v0 (.fst (.snd .v1))
  unfold fwdProbeC
  dsimp only [Expr.v0, Expr.v1, Expr.v2] at hsw ⊢
  generalize sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = esw at hsw ⊢
  dsimp only [atomicCompDescBits, KemFailRedLoopAndCost.atomicExprDescBits] at hsw ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c, hb2_eq] at hsw ⊢
  omega

private theorem fwdEvalCKSC_descBits_le (hℓ : ℓ < 10 ^ 6) (Lq T Kc B_cap : ℕ) {Γ : List (Ty ASig)}
    (sCE : Expr AOps Γ (simFullT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdEvalCKSC C K idA idB Dh encPt encT decT lam Lq T Kc B_cap sCE qBE wE cE c'E) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sCE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits cE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits c'E +
      12 * bits Lq + 16 * bits T + 4 * bits Kc + 20 * bits B_cap + 83000 := by
  let t0 := Ty.prod (simFullT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
  let Γ1 := t0 :: Γ
  have hke := keptEvalAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam hℓ T B_cap
    (Γ := Γ1) (pGet (scKept (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd (.snd (.snd .v0))))
  have hse := sentEvalAtomicE_descBits_tight C K idA idB Dh encPt encT decT lam hℓ Lq B_cap
    (Γ := Γ1) (scSent (.fst .v0)) (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
  have hor := fwdOrElseOptE_descBits_le C K Dh encPt encT decT lam (Γ := Γ1)
    (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T B_cap (pGet (scKept (.fst .v0)) (.fst (.snd .v0)))
      (.snd (.snd (.snd (.snd .v0)))))
    (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB Lq B_cap (scSent (.fst .v0))
      (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0)))))
  have hks := SimFig8Crypto.knownSeedDecryptAtomicFastC_descBits_le idA idB Lq Kc B_cap IDF
    (fun _ => 8) (fun _ => 8) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) (scSnaps (.fst .v0)) (.fst (.snd .v0))
    (.fst (.fst (.fst (.snd (.snd (.snd .v0)))))) (.fst (.snd (.snd .v0)))
    (.snd (.snd (.snd (.snd .v0))))
  unfold fwdEvalCKSC
  dsimp only [scKept, scSent, scSnaps, pGet, Expr.v0] at hke hse hor hks ⊢
  generalize fwdOrElseOptE C K Dh encPt encT decT lam (Γ := Γ1) _ _ = eor at hor ⊢
  generalize keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB T B_cap (Γ := Γ1) _ _ = eke at hke hor
  generalize sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB Lq B_cap (Γ := Γ1) _ _ _ = ese at hse hor
  generalize knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB Lq Kc B_cap IDF (Γ := Γ1) _ _ _ _ _ = eks at hks ⊢
  dsimp only [atomicCompDescBits, KemFailRedLoopAndCost.atomicExprDescBits] at hke hse hor hks ⊢
  simp only [KemFailRedLoopAndCost.varIdx, hb0_c] at hke hse hor hks ⊢
  omega

private theorem fwdResyncC_descBits_le (hℓ : ℓ < 10 ^ 6) (qep Lq T : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (ci?E : Expr AOps Γ (.opt .nat)) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (rE : Expr AOps Γ (.opt (kDecOutT ℓ Pt))) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdResyncC C K idA idB Dh encPt encT decT lam qep Lq T
        stE qBE wE ci?E pkE pq'E cE rE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits stE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits ci?E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pkE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pq'E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits cE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits rE +
      24 * bits Lq + 16 * bits T + 2 * bits (qep + 1) + 80000 := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  let tupT := Ty.prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod (.opt .nat) (.prod PK (.prod (B 32)
      (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (.opt (kDecOutT ℓ Pt))))))))
  let rrPT := Ty.prod .nat (.prod .nat
    (.opt (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))))
  let rrT := smRrT (ℓ := ℓ) (Pt := Pt)
    (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))
  let Γ4 := rrPT :: rrT :: Ty.opt rrT :: kDecOutT ℓ Pt :: tupT :: Γ
  let accOutT := Ty.prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt))))
    (simBaseT ℓ Pt)
  let Γ5 := accOutT :: Γ4
  have hoa := fwdOnAcceptC_descBits_le C K Dh encPt encT decT lam hℓ qep Lq (Γ := Γ4)
    (scBase (.fst (.fst .v4))) (.fst (.snd (.snd (.snd .v4))))
    (.fst (.snd (.snd (.snd (.snd .v4))))) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.bool true) (.fst .v3) (.fst (.snd .v3)) (.snd (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
  have hup := fwdScAcceptUpdateE_descBits_le C K idA idB Dh encPt encT decT lam T (Γ := Γ5)
    (.fst (.fst .v5)) (.snd .v0) (.fst (.snd .v5))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v5)))))))
  unfold fwdResyncC
  dsimp only [fwdRejOutE, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
    at hoa hup ⊢
  generalize fwdOnAcceptC C K Dh encPt encT decT lam qep Lq (Γ := Γ4) _ _ _ _ _ _ _ _ _ _ = eoa
    at hoa ⊢
  generalize fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam T (Γ := Γ5) _ _ _ _ = eup
    at hup ⊢
  dsimp only [atomicCompDescBits, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits] at hoa hup ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c, hb2_eq, hb3_c,
    hb4_c, hb5_c] at hoa hup ⊢
  omega

private theorem fwdAnswerC_descBits_le (hℓ : ℓ < 10 ^ 6) (qep Lq T : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdAnswerC C K idA idB Dh encPt encT decT lam qep Lq T
        stE qBE wE isDelE ci?E pkE pq'E c'E) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits stE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits isDelE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits ci?E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pkE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pq'E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits c'E +
      28 * bits Lq + 16 * bits T + 2 * bits (qep + 1) + 83000 := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  let tupT := Ty.prod (dfStepT ℓ Pt) (.prod .bool (.prod (B 32)
    (.prod .bool (.prod (.opt .nat) (.prod PK (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))))))))
  let Γ1 := tupT :: Γ
  let rrPT := Ty.prod .nat (.prod .nat
    (.opt (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))))
  let rrT := smRrT (ℓ := ℓ) (Pt := Pt)
    (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt)))
  let Γ3 := rrPT :: rrT :: Ty.opt rrT :: Γ1
  let accOutT := Ty.prod (.opt (smRrT (ℓ := ℓ) (Pt := Pt) (PlainT (ℓ := ℓ) (Pt := Pt))))
    (simBaseT ℓ Pt)
  let Γ4 := accOutT :: Γ3
  have hin := fwdInTE_descBits_le C K Dh encPt encT decT lam Lq (Γ := Γ1)
    (scBase (.fst (.fst .v0))) (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
  have hdm := SimFig8Kept.defaultMcAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
    (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3)
  have hoa := fwdOnAcceptC_descBits_le C K Dh encPt encT decT lam hℓ qep Lq (Γ := Γ3)
    (scBase (.fst (.fst .v3))) (.fst (.snd (.snd (.snd (.snd .v3)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v3)))))) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd .v3)))) (.fst .v0) (.fst (.snd .v0))
    (.caseOpt (.snd (.snd .v0))
      (.snd (.fst (defaultMcAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)))) (.snd .v0))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
  have hup := fwdScAcceptUpdateE_descBits_le C K idA idB Dh encPt encT decT lam T (Γ := Γ4)
    (.fst (.fst .v4)) (.snd .v0) (.fst (.snd .v4))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))
  unfold fwdAnswerC
  dsimp only [fwdRejOutE, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
    at hin hdm hoa hup ⊢
  generalize fwdInTE C K Dh encPt encT decT lam Lq (Γ := Γ1) _ _ _ = ein at hin ⊢
  generalize fwdOnAcceptC C K Dh encPt encT decT lam qep Lq (Γ := Γ3) _ _ _ _ _ _ _ _ _ _ = eoa
    at hoa ⊢
  generalize defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ3) = edm at hdm hoa
  generalize fwdScAcceptUpdateE C K idA idB Dh encPt encT decT lam T (Γ := Γ4) _ _ _ _ = eup
    at hup ⊢
  dsimp only [atomicCompDescBits, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits]
    at hin hdm hoa hup ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c, hb3_c, hb4_c]
    at hin hdm hoa hup ⊢
  omega

private theorem fwdEvictC_descBits_le (hℓ : ℓ < 10 ^ 6) (qep q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdEvictC C K idA idB Dh encPt encT decT lam qep q stE qBE wE isDelE pkE pq'E c'E) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits stE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits isDelE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pkE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pq'E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits c'E +
      48 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) + 87000 := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  have hbq := SimFig8SpqrDesc.bits_L_le_budget q qep
  have hbT := bits_50k_le_budget q qep
  have hbe := SimFig8SpqrDesc.bits_qep1_le_budget q qep
  let Γ1 := dfFwdEvictInT ℓ Pt :: Γ
  have hsi := SimFig8State.mSafeInjE_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ1)
    (ssMir (scBase (.fst (.fst .v0))))
  have hpr := fwdProbeC_descBits_le C K Dh encPt encT decT lam q (Γ := Γ1)
    (.fst (.snd .v0)) (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))) (.snd (.fst .v0))
  have han := fwdAnswerC_descBits_le C K idA idB Dh encPt encT decT lam hℓ qep q (50000 * q)
    (Γ := Γ1) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) .none (.fst (.snd (.snd (.snd (.snd .v0)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v0)))))) (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  unfold fwdEvictC
  dsimp only [fwdRejOutE, ssMir, scBase, Expr.v0, Expr.v1] at hsi hpr han ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γ1) _ = esi at hsi ⊢
  generalize fwdProbeC C K Dh encPt encT decT lam q (Γ := Γ1) _ _ _ = epr at hpr ⊢
  generalize fwdAnswerC C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ1)
    _ _ _ _ _ _ _ _ = ean at han ⊢
  dsimp only [atomicCompDescBits, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits]
    at hsi hpr han ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c] at hsi hpr han ⊢
  omega

private theorem fwdHookC_descBits_le (hℓ : ℓ < 10 ^ 6) (qep q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (dfStepT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (isDelE : Expr AOps Γ .bool) (ci?E : Expr AOps Γ (.opt .nat))
    (pkE : Expr AOps Γ PK) (pq'E : Expr AOps Γ (B 32))
    (honestCE : Expr AOps Γ (.opt (fig8CtT (ℓ := ℓ) (Pt := Pt))))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdHookC C K idA idB Dh encPt encT decT lam qep q
        stE qBE wE isDelE ci?E pkE pq'E honestCE c'E) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits stE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits isDelE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits ci?E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pkE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits pq'E +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits honestCE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits c'E +
      200 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) + 340000 := by
  have _ := hb_ell (ℓ := ℓ) hℓ; have _ := hb2p32_c
  have hbq := SimFig8SpqrDesc.bits_L_le_budget q qep
  have hbT := bits_50k_le_budget q qep
  have hbK := bits_25k1_le_budget q qep
  have hbe := SimFig8SpqrDesc.bits_qep1_le_budget q qep
  let Γ1 := dfFwdInT ℓ Pt :: Γ
  let Γ2 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := Ty.opt (Ty.opt (kDecOutT ℓ Pt)) :: Γ2
  let Γ4 := Ty.opt (kDecOutT ℓ Pt) :: Γ3
  have han1 := fwdAnswerC_descBits_le C K idA idB Dh encPt encT decT lam hℓ qep q (50000 * q)
    (Γ := Γ1) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.fst (.snd (.snd (.snd (.snd .v0))))) (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))))
  have heq := SimFig8Kept.eqFig8CAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2)
    .v0 (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  have hsi := SimFig8State.mSafeInjE_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ2)
    (ssMir (scBase (.fst (.fst .v1))))
  have hek := fwdEvalCKSC_descBits_le C K idA idB Dh encPt encT decT lam hℓ q (50000 * q)
    (25001 * q + 25000) (2 ^ 32) (Γ := Γ2)
    (.fst (.fst .v1)) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    .v0 (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  have hpr := fwdProbeC_descBits_le C K Dh encPt encT decT lam q (Γ := Γ3)
    (.fst (.snd .v2)) (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v2)))))))) (.snd (.fst .v2))
  have hrs := fwdResyncC_descBits_le C K idA idB Dh encPt encT decT lam hℓ qep q (50000 * q)
    (Γ := Γ4) (.fst .v3) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3))))))) .v2 .v0
  have han2 := fwdAnswerC_descBits_le C K idA idB Dh encPt encT decT lam hℓ qep q (50000 * q)
    (Γ := Γ2) (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v1)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v1))))))))
  unfold fwdHookC
  dsimp only [fwdRejOutE, ssMir, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    at han1 heq hsi hek hpr hrs han2 ⊢
  generalize fwdAnswerC C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ1)
    _ _ _ _ _ _ _ _ = ea1 at han1 ⊢
  generalize eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = eeq at heq ⊢
  generalize mSafeInjE (O' := AOps) (Γ := Γ2) _ = esi at hsi ⊢
  generalize fwdEvalCKSC C K idA idB Dh encPt encT decT lam q (50000 * q) (25001 * q + 25000)
    (2 ^ 32) (Γ := Γ2) _ _ _ _ _ = eek at hek ⊢
  generalize fwdProbeC C K Dh encPt encT decT lam q (Γ := Γ3) _ _ _ = epr at hpr ⊢
  generalize fwdResyncC C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ4)
    _ _ _ _ _ _ _ _ = ers at hrs ⊢
  generalize fwdAnswerC C K idA idB Dh encPt encT decT lam qep q (50000 * q) (Γ := Γ2)
    _ _ _ _ _ _ _ _ = ea2 at han2 ⊢
  dsimp only [atomicCompDescBits, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits]
    at han1 heq hsi hek hpr hrs han2 ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c, hb2_eq, hb3_c]
    at han1 heq hsi hek hpr hrs han2 ⊢
  omega

theorem fwdRecvNewC_descBits_le (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdRecvNewC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q) ≤
      2 ^ 19 + 2 ^ 11 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  let Γ0 : List (Ty ASig) := [dfRecvNewInT ℓ Pt]
  let Γ1 : List (Ty ASig) := [PtT (ℓ := ℓ) (Pt := Pt), dfRecvNewInT ℓ Pt]
  have hev0 := fwdEvictedE_descBits_le C K Dh encPt encT decT lam (Γ := Γ0)
    (.snd (.snd (.snd (.snd (.snd .v0))))) (scBase (.fst (.fst .v0))) (.fst (.snd .v0))
  have hse0 := fwdSaltEqE_descBits_le C K Dh encPt encT decT lam (Γ := Γ0)
    (.snd (.snd (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
  have hzr := SimFig8Crypto.isZeroPtOptAtomicE_descBits_le (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0)
    (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
  have hgr := fwdNewGuardRejectE_descBits_le C K Dh encPt encT decT lam (Γ := Γ0)
    (scBase (.fst (.fst .v0))) (.fst (.snd .v0))
    (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))
  have ham0 := fwdScAmbE_descBits_le C K Dh encPt encT decT lam (Γ := Γ0)
    (.fst (.fst .v0)) (.fst (.snd .v0))
  have hev1 := fwdEvictedE_descBits_le C K Dh encPt encT decT lam (Γ := Γ1)
    (.snd (.snd (.snd (.snd (.snd .v1))))) (scBase (.fst (.fst .v1))) (.fst (.snd .v1))
  have ham1 := fwdScAmbE_descBits_le C K Dh encPt encT decT lam (Γ := Γ1)
    (.fst (.fst .v1)) (.fst (.snd .v1))
  let nextEp : Expr AOps Γ1 .nat :=
    .add (pGet (mEpoch (ssMir (scBase (.fst (.fst .v1))))) (.fst (.snd .v1))) (.nat 1)
  let lct1 : Expr AOps Γ1 (lctT (ℓ := ℓ) (Pt := Pt)) :=
    .snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v1))))))))
  let stAmb1 : Expr AOps Γ1 (dfStepT ℓ Pt) :=
    .pair (fwdScAmbE C K Dh encPt encT decT lam (.fst (.fst .v1)) (.fst (.snd .v1)))
      (.snd (.fst .v1))
  have hmk := fwdMkCE_descBits_le C K Dh encPt encT decT lam (Γ := Γ1)
    (.snd (.snd (.snd (.snd (.snd .v1))))) nextEp (.some .v0) lct1
  have hevc := fwdEvictC_descBits_le C K idA idB Dh encPt encT decT lam hℓ qep q (Γ := Γ1)
    stAmb1 (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v1))))))))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1)))))) (.pair (.pair nextEp (.some .v0)) lct1)
  have hhkc := fwdHookC_descBits_le C K idA idB Dh encPt encT decT lam hℓ qep q (Γ := Γ1)
    stAmb1 (.fst (.snd .v1)) (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))) .none
    (.fst (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v1))))))))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1)))))) (.snd (.snd (.snd (.snd (.snd .v1)))))
    (fwdMkCE C K Dh encPt encT decT lam (.snd (.snd (.snd (.snd (.snd .v1))))) nextEp
      (.some .v0) lct1)
  unfold fwdRecvNewC
  dsimp only [nextEp, lct1, stAmb1, fwdRejOutE, pGet, mEpoch, ssMir, scBase, Expr.v0, Expr.v1]
    at hev0 hse0 hzr hgr ham0 hev1 ham1 hmk hevc hhkc ⊢
  generalize fwdEvictC C K idA idB Dh encPt encT decT lam qep q (Γ := Γ1) _ _ _ _ _ _ _ = eevc
    at hevc ⊢
  generalize fwdHookC C K idA idB Dh encPt encT decT lam qep q (Γ := Γ1) _ _ _ _ _ _ _ _ _ = ehkc
    at hhkc ⊢
  generalize fwdMkCE C K Dh encPt encT decT lam (Γ := Γ1) _ _ _ _ = emk at hmk hhkc
  generalize fwdScAmbE C K Dh encPt encT decT lam (Γ := Γ1) _ _ = eam1 at ham1 hevc hhkc
  generalize fwdScAmbE C K Dh encPt encT decT lam (Γ := Γ0) _ _ = eam0 at ham0 ⊢
  generalize fwdEvictedE C K Dh encPt encT decT lam (Γ := Γ0) _ _ _ = eev0 at hev0 ⊢
  generalize fwdEvictedE C K Dh encPt encT decT lam (Γ := Γ1) _ _ _ = eev1 at hev1 ⊢
  generalize fwdSaltEqE C K Dh encPt encT decT lam (Γ := Γ0) _ _ = ese0 at hse0 ⊢
  generalize isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ0) _ = ezr at hzr ⊢
  generalize fwdNewGuardRejectE C K Dh encPt encT decT lam (Γ := Γ0) _ _ _ = egr at hgr ⊢
  dsimp only [atomicCompDescBits, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits]
    at hev0 hse0 hzr hgr ham0 hev1 ham1 hmk hevc hhkc ⊢
  simp only [KemFailRedLoopAndCost.varIdx, Nat.reduceAdd, hb0_c, hb1_c]
    at hev0 hse0 hzr hgr ham0 hev1 ham1 hmk hevc hhkc ⊢
  omega

theorem fwdRecvSameC_queries (qep q : ℕ) :
    (fwdRecvSameC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  dsimp only [fwdRecvSameC]
  simp only [Comp.queries]
  have hh := fwdHookC_queries C K idA idB Dh encPt encT decT lam qep q
    (Γ := [dfRecvSameInT ℓ Pt])
  exact Nat.max_le.mpr ⟨by omega, hh _ _ _ _ _ _ _ _ _⟩

theorem fwdRecvSameC_cost (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    (fwdRecvSameC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q).cost ≤
      26000000 + 15000000 * q + 512 * bits (qep + 1) := by
  let Γ0 : List (Ty ASig) := [dfRecvSameInT ℓ Pt]
  let g0 : Expr AOps Γ0 (ghostChainT ℓ Pt) :=
    getChainDE (pGet (ssChains (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
      (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  have hgd := SimFig8State.cost_getChainDE (O' := AOps) (Γ := Γ0)
    (pGet (ssChains (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  have hgr := SimFig8State.cost_ghostRejectsE (O' := AOps) (Γ := Γ0)
    g0 (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))
  have hmk := fwdMkCE_cost C K Dh encPt encT decT lam (Γ := Γ0)
    (.fst (.snd (.snd (.snd (.snd (.snd .v0)))))) (.fst (.snd g0))
    (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
    (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
  have hhk := fwdHookC_cost C K idA idB Dh encPt encT decT lam qep q hℓ (Γ := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.some (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
    (.fst (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))))
    (.fst (.fst (.snd (.snd (.snd (.snd .v0)))))) (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
    (fwdMkCE C K Dh encPt encT decT lam (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
      (.fst (.snd g0))
      (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
      (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))))))
  unfold fwdRecvSameC
  dsimp only [g0, fwdRejOutE, pGet, ssChains, scBase, Expr.v0] at hgd hgr hmk hhk ⊢
  generalize fwdHookC C K idA idB Dh encPt encT decT lam qep q (Γ := Γ0) _ _ _ _ _ _ _ _ _ = ehk
    at hhk ⊢
  generalize fwdMkCE C K Dh encPt encT decT lam (Γ := Γ0) _ _ _ _ = emk at hmk hhk
  generalize ghostRejectsE (O' := AOps) (Γ := Γ0) _ _ = egr at hgr ⊢
  generalize getChainDE (O' := AOps) (Γ := Γ0) _ _ = egd at hgd egr hgr hmk
  dsimp only [SimFig8State.cost_eLet, Comp.cost, Expr.cost] at hgd hgr hmk hhk ⊢; omega

theorem fwdRecvSameC_descBits_le (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdRecvSameC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam qep q) ≤
      2 ^ 19 + 2 ^ 11 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have _ := hb_ell (ℓ := ℓ) hℓ
  let Γ0 : List (Ty ASig) := [dfRecvSameInT ℓ Pt]
  let g0 : Expr AOps Γ0 (ghostChainT ℓ Pt) :=
    getChainDE (pGet (ssChains (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
      (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  have hgd := SimFig8State.getChainDE_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ0)
    (pGet (ssChains (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
    (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
  have hgr := SimFig8State.ghostRejectsE_descBits_le (O' := AOps) atomicSessionOpDescBits
    (Γ := Γ0) g0 (.fst (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))
  have hmk := fwdMkCE_descBits_le C K Dh encPt encT decT lam (Γ := Γ0)
    (.fst (.snd (.snd (.snd (.snd (.snd .v0)))))) (.fst (.snd g0))
    (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
    (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
  have hhk := fwdHookC_descBits_le C K idA idB Dh encPt encT decT lam hℓ qep q (Γ := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.some (.snd (.snd (.snd (.snd (.snd (.snd .v0)))))))
    (.fst (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))))
    (.fst (.fst (.snd (.snd (.snd (.snd .v0)))))) (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
    (fwdMkCE C K Dh encPt encT decT lam (.fst (.snd (.snd (.snd (.snd (.snd .v0))))))
      (.fst (.snd g0))
      (.fst (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0)))))))))
      (.snd (.snd (.snd (.snd (.fst (.snd (.snd (.snd (.snd .v0))))))))))
  unfold fwdRecvSameC
  dsimp only [g0, fwdRejOutE, pGet, ssChains, scBase, Expr.v0] at hgd hgr hmk hhk ⊢
  generalize fwdHookC C K idA idB Dh encPt encT decT lam qep q (Γ := Γ0) _ _ _ _ _ _ _ _ _ = ehk
    at hhk ⊢
  generalize fwdMkCE C K Dh encPt encT decT lam (Γ := Γ0) _ _ _ _ = emk at hmk hhk
  generalize ghostRejectsE (O' := AOps) (Γ := Γ0) _ _ = egr at hgr ⊢
  generalize getChainDE (O' := AOps) (Γ := Γ0) _ _ = egd at hgd egr hgr hmk
  dsimp only [atomicCompDescBits, smRrT, PlainT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits]
    at hgd hgr hmk hhk ⊢
  simp only [KemFailRedLoopAndCost.varIdx, hb0_c] at hgd hgr hmk hhk ⊢
  omega

theorem fwdRecvDispatchC_queries (q : ℕ)
    (newBranchC : Comp AOps IDF [dfRecvNewInT ℓ Pt] (dfRecvOutT ℓ Pt))
    (sameBranchC : Comp AOps IDF [dfRecvSameInT ℓ Pt] (dfRecvOutT ℓ Pt))
    (hnew : newBranchC.queries (fun _ => 1) (fun _ => 0) ≤ 1)
    (hsame : sameBranchC.queries (fun _ => 1) (fun _ => 0) ≤ 1) :
    (fwdRecvDispatchC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam q
      newBranchC sameBranchC).queries (fun _ => 1) (fun _ => 0) ≤ 1 := by
  dsimp only [fwdRecvDispatchC]
  simp only [Comp.queries, SimFig8Crypto.parseRecvAtomicC_queries]
  rw [AtomicSessionBridge.renComp_queries, AtomicSessionBridge.renComp_queries]
  refine Nat.max_le.mpr ⟨by omega, ?_⟩
  rw [Nat.zero_add]
  refine Nat.max_le.mpr ⟨by omega, Nat.max_le.mpr ⟨?_, ?_⟩⟩ <;> simpa using ‹_›

theorem fwdRecvDispatchC_cost (q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (newBranchC : Comp AOps IDF [dfRecvNewInT ℓ Pt] (dfRecvOutT ℓ Pt))
    (sameBranchC : Comp AOps IDF [dfRecvSameInT ℓ Pt] (dfRecvOutT ℓ Pt)) :
    (fwdRecvDispatchC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam q
      newBranchC sameBranchC).cost ≤
      135000000 + 1000000 * q + max newBranchC.cost sameBranchC.cost := by
  let Γ0 : List (Ty ASig) := [dfRecvInT ℓ Pt]
  let Γ2 : List (Ty ASig) := [parseOutT ℓ Pt, Ty.opt (parseOutT ℓ Pt), dfRecvInT ℓ Pt]
  let Γ3 : List (Ty ASig) := [Ty.nat, parseOutT ℓ Pt, Ty.opt (parseOutT ℓ Pt), dfRecvInT ℓ Pt]
  have hrf := fwdRefuseE_cost C K Dh encPt encT decT lam q (Γ := Γ0)
    (scBase (.fst (.fst .v0))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  have hpr := SimFig8Crypto.parseRecvAtomicC_cost IDF idA idB (2 ^ 32) (Γ := Γ0)
    (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
    (.fst (.snd .v0)) (pGet (ssPq (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
    (.fst (.snd (.snd .v0)))
  have hfi := SimFig8State.cost_findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2)
    (pGet (ssChains (scBase (.fst (.fst .v2)))) (.fst (.snd .v2))) (.fst (.snd (.snd .v0)))
  have hhc2 := fwdHonestCE_cost C K Dh encPt encT decT lam q (Γ := Γ2)
    (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
  have hhc3 := fwdHonestCE_cost C K Dh encPt encT decT lam q (Γ := Γ3)
    (scBase (.fst (.fst .v3))) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
  have _ := hb2p32_c
  unfold fwdRecvDispatchC
  dsimp only [fwdNoneOutE, fwdRejOutE, pGet, ssPq, ssChains, scBase,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hrf hpr hfi hhc2 hhc3 ⊢
  generalize fwdRefuseE C K Dh encPt encT decT lam q (Γ := Γ0) _ _ _ _ = erf at hrf ⊢
  generalize parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) IDF idA idB (2 ^ 32) (Γ := Γ0) _ _ _ = epr at hpr ⊢
  generalize findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = efi at hfi ⊢
  generalize fwdHonestCE C K Dh encPt encT decT lam q (Γ := Γ2) _ _ _ = ehc2 at hhc2 ⊢
  generalize fwdHonestCE C K Dh encPt encT decT lam q (Γ := Γ3) _ _ _ = ehc3 at hhc3 ⊢
  simp only [Comp.cost, Expr.cost, AtomicSessionBridge.renComp_cost]
    at hrf hpr hfi hhc2 hhc3 ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem singletonWk_varIdx {A : Ty ASig} {Δ : List (Ty ASig)} {u : Ty ASig}
    (v : _root_.ReductionDsl.Var [A] u) :
    KemFailRedLoopAndCost.varIdx (singletonWk (Δ := Δ) v) = KemFailRedLoopAndCost.varIdx v := by
  match v with
  | .zero => rfl

omit [SampleableType Pt] in
private theorem fwdRefuseE_descBits_le (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (wE : Expr AOps Γ (B 32)) (isDelE : Expr AOps Γ .bool) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdRefuseE C K Dh encPt encT decT lam Lq sE qBE wE isDelE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits isDelE +
      4 * bits Lq + 2000 := by
  let Γ1 := Ty.prod (simBaseT ℓ Pt) (.prod .bool (.prod (B 32) .bool)) :: Γ
  have htr := SimFig8State.mInTransitE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) Lq (Γ := Γ1)
    (ssMir (.fst .v0)) (.not (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hsi := SimFig8State.mSafeInjE_descBits_le (O' := AOps) atomicSessionOpDescBits (Γ := Γ1)
    (ssMir (.fst .v0))
  have hij := SimFig8Crypto.injOKAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.fst (.snd (.snd .v0)))
  unfold fwdRefuseE
  dsimp only [ssMir, ssStopped, mWin, orE, Expr.v0] at htr hsi hij ⊢
  generalize mInTransitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Lq (Γ := Γ1) _ _ _ = etr at htr ⊢
  generalize mSafeInjE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ = esi at hsi ⊢
  generalize injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) _ = eij at hij ⊢
  simp only [SimFig8State.descBits_eLet, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.varIdx, hb0_c] at htr hsi hij ⊢
  omega

omit [SampleableType Pt] in
private theorem fwdHonestCE_descBits_le (Lq : ℕ) {Γ : List (Ty ASig)}
    (sE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits
      (fwdHonestCE C K Dh encPt encT decT lam Lq sE qBE wE) ≤
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits sE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits qBE +
      KemFailRedLoopAndCost.atomicExprDescBits atomicSessionOpDescBits wE +
      2 * bits Lq + 600 := by
  unfold fwdHonestCE
  dsimp only [eLet, ssHonest, boolEq, Expr.v0, Expr.v1, fig8CtT, _root_.ReductionDsl.fig8HdrT,
    lctT, _root_.ReductionDsl.wireSaltCtT, B, _root_.ReductionDsl.PB, _root_.ReductionDsl.U64,
    _root_.ReductionDsl.BV256, PtT, KemFailRedLoopAndCost.atomicExprDescBits,
    KemFailRedLoopAndCost.atomicTyDescBits, KemFailRedLoopAndCost.atomicSortDescBits,
    KemFailRedLoopAndCost.varIdx]
  simp only [SimFig8State.descBits_sOpPure, KemFailRedLoopAndCost.atomicPureOpDescBits,
    KemFailRedLoopAndCost.atomicExprDescBits, KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_c, hb1_c, hb2_eq, hb32p_c]
  omega

theorem fwdRecvDispatchC_descBits_le (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (newBranchC : Comp AOps IDF [dfRecvNewInT ℓ Pt] (dfRecvOutT ℓ Pt))
    (sameBranchC : Comp AOps IDF [dfRecvSameInT ℓ Pt] (dfRecvOutT ℓ Pt)) :
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8)
      (fwdRecvDispatchC (Pt := Pt) (ℓ := ℓ) C K idA idB Dh encPt encT decT lam q
        newBranchC sameBranchC) ≤
      2 ^ 18 + 2 ^ 10 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) newBranchC +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) (fun _ => 8) sameBranchC := by
  let Γ0 : List (Ty ASig) := [dfRecvInT ℓ Pt]
  let Γ1 : List (Ty ASig) := [Ty.opt (parseOutT ℓ Pt), dfRecvInT ℓ Pt]
  let Γ2 : List (Ty ASig) := [parseOutT ℓ Pt, Ty.opt (parseOutT ℓ Pt), dfRecvInT ℓ Pt]
  let Γ3 : List (Ty ASig) := [Ty.nat, parseOutT ℓ Pt, Ty.opt (parseOutT ℓ Pt), dfRecvInT ℓ Pt]
  have hbq := SimFig8SpqrDesc.bits_L_le_budget q qep
  have hrf := fwdRefuseE_descBits_le C K Dh encPt encT decT lam q (Γ := Γ0)
    (scBase (.fst (.fst .v0))) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  have hno := fwdNoneOutE_descBits_le C K Dh encPt encT decT lam hℓ (Γ := Γ0) (.fst .v0)
  have hpr := SimFig8Crypto.parseRecvAtomicC_descBits_le IDF idA idB (2 ^ 32)
    (fun _ => 8) (fun _ => 8) (Γ := Γ0) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (.fst (.snd .v0)) (pGet (ssPq (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
    (.fst (.snd (.snd .v0)))
  have hrj := fwdRejOutE_descBits_le C K Dh encPt encT decT lam hℓ (Γ := Γ1) (.fst .v1)
  have hfi := SimFig8State.findChainIdxE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2)
    (pGet (ssChains (scBase (.fst (.fst .v2)))) (.fst (.snd .v2))) (.fst (.snd (.snd .v0)))
  have hhc2 := fwdHonestCE_descBits_le C K Dh encPt encT decT lam q (Γ := Γ2)
    (scBase (.fst (.fst .v2))) (.fst (.snd .v2)) (.fst (.snd (.snd .v2)))
  have hhc3 := fwdHonestCE_descBits_le C K Dh encPt encT decT lam q (Γ := Γ3)
    (scBase (.fst (.fst .v3))) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
  have hrn1 := SimFig8SpqrDesc.renComp_descBits_eq atomicSessionOpDescBits
    (fun _ => 8) (fun _ => 8) (singletonWk (A := dfRecvNewInT ℓ Pt) (Δ := Γ2)) newBranchC
    singletonWk_varIdx
  have hrn2 := SimFig8SpqrDesc.renComp_descBits_eq atomicSessionOpDescBits
    (fun _ => 8) (fun _ => 8) (singletonWk (A := dfRecvSameInT ℓ Pt) (Δ := Γ3)) sameBranchC
    singletonWk_varIdx
  have _ := hb2p32_c
  let _ := (inferInstance : SampleableType Pt)
  unfold fwdRecvDispatchC
  dsimp only [pGet, ssPq, ssChains, scBase, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
    at hrf hno hpr hrj hfi hhc2 hhc3 ⊢
  generalize fwdRefuseE C K Dh encPt encT decT lam q (Γ := Γ0) _ _ _ _ = erf at hrf ⊢
  generalize fwdNoneOutE C K Dh encPt encT decT lam (Γ := Γ0) _ = eno at hno ⊢
  generalize parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) IDF idA idB (2 ^ 32) (Γ := Γ0) _ _ _ = epr at hpr ⊢
  generalize fwdRejOutE C K Dh encPt encT decT lam (Γ := Γ1) _ = erj at hrj ⊢
  generalize findChainIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ2) _ _ = efi at hfi ⊢
  generalize fwdHonestCE C K Dh encPt encT decT lam q (Γ := Γ2) _ _ _ = ehc2 at hhc2 ⊢
  generalize fwdHonestCE C K Dh encPt encT decT lam q (Γ := Γ3) _ _ _ = ehc3 at hhc3 ⊢
  rw [atomicCompDescBits, atomicCompDescBits, atomicCompDescBits, atomicCompDescBits,
    atomicCompDescBits, atomicCompDescBits, atomicCompDescBits, atomicCompDescBits,
    atomicCompDescBits, atomicCompDescBits, hrn1, hrn2]
  simp only [KemFailRedLoopAndCost.atomicExprDescBits, KemFailRedLoopAndCost.varIdx,
    Nat.reduceAdd, hb0_c, hb1_c, hb2_eq, hb3_c] at hrf hno hpr hrj hfi hhc2 hhc3 ⊢
  omega

end Builders

end

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeStepRecvFwdCost
