/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Step
public import Computational.Proofs.HeadlineV1.SendShortC
import Computational.Proofs.Game.PromotedCostedReds.SimFig8QepCap
import Computational.Proofs.Game.PromotedCostedReds.SimFig8QepCapQueries

/-!
# Top-Level `simFig8` Costed Reduction Program

Assembles `simFig8RedProg` from `SimFig8Step.simFig8RawStepSpec` and proves its `GRedBounded`,
description-bit, and `GuardedSMShort` query invariants.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog

open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst
  (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32 lFig8 ratchetKeyAdmissible)
open CryptoGames.LibsignalSession
  (Crypto IdentityKey PublicKey GhostState signalWireCodec)
open CryptoGames.LibsignalSM.Refine (libsignalToModularSchemeSim)
open CryptoGames.LibsignalSM.Proofs.Refinement (simCNoneWinEvent)
open CryptoGames.LibsignalSM.Proofs.SessionShort (SendMsgsOk GuardedSMShort)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (ratchetCostBudget ratchetCostBudget_pos GRedBounded)
open CryptoVerification.E2E (Bytes idsOf paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (ratchetDescBudget ratchetDescBudget_mono)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
  (simFig8ClampSan simFig8ProgOfStep_eval_san)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanSem
  (simFig8ClampSan_queries simFig8ClampSan_equalPub simFig8ClampSan_sendShort)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanCoupling
  (SanSnapExtra sanSnapExtra_init sanSnapExtra_step sm_run_simFig8ClampSan_eq)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (lengthsOk_paramsIdsWithSpqr_v1 SimFig8RedProg SimFig8EvalOk atomicFig8RedDescBits
   simFig8ProgOfStep simFig8ProgOfStep_gRedBounded_of_clamp_linear simFig8ProgOfStep_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Step (simFig8RawStepSpec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8QepCap
  (sm_run_lFig8_qep_eq sm_run_libsignalToModularSchemeSim_qep_eq)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8QepCapQueries
  (libsignalToModularSchemeSim_queries)

noncomputable section

/-- Clamped epoch cap `min qep (q + 4)` keeping AST literal sizes bounded by `ratchetCostBudget`
while preserving `q`-query game semantics. -/
abbrev simFig8QepClamp (qep q : ℕ) : ℕ := min qep (q + 4)

abbrev simFig8RedProg {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimFig8RedProg Pt ℓ C K Dh encPt encT decT lam :=
  simFig8ProgOfStep C K Dh encPt encT decT lam
    (simFig8RawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam
      (simFig8QepClamp qep q) q).step

theorem simFig8RedProg_gRedBounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    GRedBounded (simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) := by
  let qep₀ := simFig8QepClamp qep q
  let S := simFig8RawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep₀ q
  have hqep₀ : qep₀ ≤ qep := Nat.min_le_left qep (q + 4)
  have hClamp : qep₀ ≤ ratchetCostBudget q (qep + 1) := by
    have hle : qep₀ ≤ q + 4 := Nat.min_le_right qep (q + 4)
    have hpos : 16777216 * (q + 1) ≤ ratchetCostBudget q (qep + 1) :=
      ratchetCostBudget_pos q (qep + 1)
    omega
  exact simFig8ProgOfStep_gRedBounded_of_clamp_linear C K Dh encPt encT decT lam qep₀ qep q
    hqep₀ hClamp S.step S.hstep_q S.hstep_c S.hstep_d

theorem simFig8RedProg_descBits_le {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    atomicFig8RedDescBits (simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q) ≤
      ratchetDescBudget q (qep + 1) := by
  let qep₀ := simFig8QepClamp qep q
  let S := simFig8RawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep₀ q
  have hqep₀ : qep₀ + 1 ≤ qep + 1 := Nat.add_le_add_right (Nat.min_le_left qep (q + 4)) 1
  exact (simFig8ProgOfStep_descBits_le C K Dh encPt encT decT lam qep₀ q S.step S.hstep_d).trans
    (ratchetDescBudget_mono le_rfl hqep₀)

theorem simFig8RedProg_eval_san {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) () =
      simFig8ClampSan (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam (simFig8QepClamp qep q)
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A := by
  let qep₀ := simFig8QepClamp qep q
  let S := simFig8RawStepSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep₀ q
  dsimp only [simFig8RedProg]
  exact simFig8ProgOfStep_eval_san C K idA idB Dh encPt encT decT lam
    q qep₀ (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) hℓ
    (SanSnapExtra C K) (sanSnapExtra_init C K idA idB)
    (sanSnapExtra_step C K idA idB Dh encPt encT decT lam qep₀
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q))
    S.step (S.hstep hℓ) A q hq le_rfl

private theorem paramsV1_idsOf_eq (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (R : Party) :
    (if R == Party.A then (paramsV1 C K idA idB).idA else (paramsV1 C K idA idB).idB) =
      idsOf idA idB R := by
  cases R <;> rfl

private theorem sm_run_simFig8ClampSan_qepClamp_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)) (b : Bool)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    let P := paramsV1 C K idA idB
    let fig := lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (simFig8ClampSan P ℓ Dh encPt encT decT lam (simFig8QepClamp qep q)
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A) =
    CryptoGames.SM.run fig 3 (qep + 1) cfg b
      (libsignalToModularSchemeSim P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A) := by
  intro P fig
  by_cases hle : qep ≤ q + 4
  · have hmin : simFig8QepClamp qep q = qep := Nat.min_eq_left hle
    rw [hmin]
    exact sm_run_simFig8ClampSan_eq P Dh encPt encT decT (idsOf idA idB)
      (paramsV1_idsOf_eq C K idA idB) lam qep
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
      cfg b hq (by omega) (by omega) le_rfl le_rfl le_rfl
  · let qep₀ := simFig8QepClamp qep q
    have hmin : qep₀ = q + 4 := Nat.min_eq_right (by omega)
    have hQ₁ : q + 1 ≤ qep + 1 := by omega
    have hQ₀ : q + 1 ≤ qep₀ + 1 := by omega
    have hq₁ : q + 1 ≤ qep := by omega
    have hq₀ : q + 1 ≤ qep₀ := by omega
    have hStep1 :
        CryptoGames.SM.run fig 3 (qep + 1) cfg b
          (simFig8ClampSan P ℓ Dh encPt encT decT lam qep₀
            (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A) =
        CryptoGames.SM.run fig 3 (qep₀ + 1) cfg b
          (simFig8ClampSan P ℓ Dh encPt encT decT lam qep₀
            (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A) :=
      sm_run_lFig8_qep_eq C protoSignalCodec Dh encPt encT (idsOf idA idB) lam
        q (qep + 1) (qep₀ + 1) hQ₁ hQ₀ cfg b _
        (simFig8ClampSan_queries P Dh encPt encT decT lam qep₀
          (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) hq)
    have hStep2 :
        CryptoGames.SM.run fig 3 (qep₀ + 1) cfg b
          (simFig8ClampSan P ℓ Dh encPt encT decT lam qep₀
            (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A) =
        CryptoGames.SM.run fig 3 (qep₀ + 1) cfg b
          (libsignalToModularSchemeSim P ℓ Dh encPt encT decT (idsOf idA idB) lam qep₀ A) :=
      sm_run_simFig8ClampSan_eq P Dh encPt encT decT (idsOf idA idB)
        (paramsV1_idsOf_eq C K idA idB) lam qep₀
        (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q)
        cfg b hq (by omega) (by omega) le_rfl le_rfl le_rfl
    have hStep3 :
        CryptoGames.SM.run fig 3 (qep₀ + 1) cfg b
          (libsignalToModularSchemeSim P ℓ Dh encPt encT decT (idsOf idA idB) lam qep₀ A) =
        CryptoGames.SM.run fig 3 (qep₀ + 1) cfg b
          (libsignalToModularSchemeSim P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A) :=
      sm_run_libsignalToModularSchemeSim_qep_eq P Dh encPt encT decT (idsOf idA idB) lam
        q (qep₀ + 1) qep₀ qep hQ₀ hq₀ hq₁ cfg b A hq
    have hStep4 :
        CryptoGames.SM.run fig 3 (qep₀ + 1) cfg b
          (libsignalToModularSchemeSim P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A) =
        CryptoGames.SM.run fig 3 (qep + 1) cfg b
          (libsignalToModularSchemeSim P ℓ Dh encPt encT decT (idsOf idA idB) lam qep A) :=
      sm_run_lFig8_qep_eq C protoSignalCodec Dh encPt encT (idsOf idA idB) lam
        q (qep₀ + 1) (qep + 1) hQ₀ hQ₁ cfg b _
        (libsignalToModularSchemeSim_queries P Dh encPt encT decT (idsOf idA idB) lam qep q A hq)
    exact hStep1.trans (hStep2.trans (hStep3.trans hStep4))

theorem simFig8RedProg_evalOk {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimFig8EvalOk Pt ℓ C K idA idB Dh encPt encT decT lam qep q
      (simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q) where
  queries hℓ A hq := by
    rw [simFig8RedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
    exact simFig8ClampSan_queries (paramsV1 C K idA idB) Dh encPt encT decT lam
      (simFig8QepClamp qep q) (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) hq
  equalPub hℓ A hq := by
    rw [simFig8RedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
    exact simFig8ClampSan_equalPub (paramsV1 C K idA idB) Dh encPt encT decT lam
      (simFig8QepClamp qep q) (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A
  sendShort hℓ A hq := by
    rw [simFig8RedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
    exact simFig8ClampSan_sendShort (paramsV1 C K idA idB)
      (lengthsOk_paramsIdsWithSpqr_v1 C K idA idB (by omega))
      Dh encPt encT decT lam (simFig8QepClamp qep q)
      (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A
  sm_game_eq hℓ cfg A hq := by
    rw [simFig8RedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
    unfold CryptoGames.SM.game
    refine congrArg (_ >>= ·) (funext fun b => ?_)
    dsimp only
    rw [sm_run_simFig8ClampSan_qepClamp_eq C K idA idB Dh encPt encT decT lam qep q cfg b A hq]
  simCNoneWinEvent_eq hℓ A hq := by
    rw [simFig8RedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
    unfold simCNoneWinEvent
    refine congrArg (_ >>= ·) (funext fun b => ?_)
    dsimp only
    rw [sm_run_simFig8ClampSan_qepClamp_eq C K idA idB Dh encPt encT decT lam qep q
      CryptoGames.SM.Config.h1 b A hq]
    rfl

theorem simFig8RedProg_queries {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.MakesAtMostQueries
      ((simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) q :=
  (simFig8RedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).queries hℓ A hq

theorem simFig8RedProg_equalPub {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.EqualPubChalls (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)
      ((simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) :=
  (simFig8RedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).equalPub hℓ A hq

theorem simFig8RedProg_sendShort {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      ((simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) :=
  (simFig8RedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).sendShort hℓ A hq

theorem simFig8RedProg_sm_game_eq {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (cfg : CryptoGames.SM.Config _)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    CryptoGames.SM.game (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        3 (qep + 1) cfg
        ((simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) =
      CryptoGames.SM.game (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
        3 (qep + 1) cfg
        (libsignalToModularSchemeSim (paramsV1 C K idA idB) ℓ
          Dh encPt encT decT (idsOf idA idB) lam qep A) :=
  (simFig8RedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).sm_game_eq hℓ cfg A hq

theorem simFig8RedProg_simCNoneWinEvent_eq {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    simCNoneWinEvent (paramsV1 C K idA idB) ℓ
        Dh encPt encT decT (idsOf idA idB) lam qep A =
      (do
        let b ← $ᵗ Bool
        let (_, s) ← CryptoGames.SM.run
          (lFig8 Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) 25000 lam)
          3 (qep + 1) CryptoGames.SM.Config.h1 b
          ((simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ())
        return s.win) :=
  (simFig8RedProg_evalOk ℓ C K idA idB Dh encPt encT decT lam qep q).simCNoneWinEvent_eq hℓ A hq

section SendAtomicShort

open OracleSpec OracleComp
open CryptoGames.SM
  (partyEnc noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10)
open CryptoGames.LibsignalSession (Params)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8Comp inReceiveOnlyEpoch semDrawSendCoins semSendHook mkPub simParseRecvC)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.LibsignalSM.Proofs.QueryBounds (FSpec isQueryBoundP_simulateQ_run_zero)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM (badSendMsg)
open CryptoVerification.LibsignalSession.HeadlineV1
  (AtomicLengthsOk atomicLengthsOk_paramsIdsWithSpqr_v1 QAtomicShort hQu_QAtomicShort
   atomicShortPubB_mkPub)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (evalCKS semFwdAnswerHookS semResyncHookS semFwdEvictHookS semFwdHookS semRecvHookS
   semCorrHookTGB semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (fig8IdSemHook)

private theorem liftProb_qAtomicShort {Pt α : Type} {ℓ : ℕ} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : Fig8Comp Pt ℓ α) (QAtomicShort Pt ℓ) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure (QAtomicShort Pt ℓ) x 0
  | query_bind t mx ih =>
    change IsQueryBoundP (query (spec := FSpec Pt ℓ) (.inl t) >>= fun u => liftM (mx u))
      (QAtomicShort Pt ℓ) 0
    rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ)
      ((isQueryBoundP_query_iff (QAtomicShort Pt ℓ) (.inl t) 0).2 fun h =>
        absurd h (hQu_QAtomicShort t))
      fun u _ => ih u

private theorem simDrawSendCoins_qAtomicShort {PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (r : Option PQC) :
    IsQueryBoundP (semDrawSendCoins (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) r)
      (QAtomicShort Pt ℓ) 0 := by
  cases r with
  | none =>
    dsimp only [semDrawSendCoins, fig8IdSemHook]
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ) (liftProb_qAtomicShort ($ᵗ PQC))
      fun rq _ => isQueryBoundP_pure (QAtomicShort Pt ℓ) (rq, none) 0
  | some rq =>
    dsimp only [semDrawSendCoins, fig8IdSemHook]
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ) (liftProb_qAtomicShort ($ᵗ (BitVec 256)))
      fun rc _ => isQueryBoundP_pure (QAtomicShort Pt ℓ) (rq, some rc) 0

private theorem semSendHook_qAtomicShort {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (lam : Pt) (qep : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party)
    (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    IsQueryBoundP
      (semSendHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q m₀ chal r)
      (QAtomicShort Pt ℓ) 0 := by
  unfold semSendHook
  by_cases hc1 : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp only [hc1, ↓reduceIte]; exact isQueryBoundP_pure _ _ 0
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    rcases sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · exact isQueryBoundP_pure _ _ 0
    · dsimp only []
      by_cases hc2 : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hc2, ↓reduceIte]; exact isQueryBoundP_pure _ _ 0
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        rw [← Nat.zero_add 0]
        refine isQueryBoundP_bind (p := QAtomicShort Pt ℓ) (simDrawSendCoins_qAtomicShort r)
          fun ⟨rq, rc⟩ _ => ?_
        dsimp only [fig8IdSemHook]; rw [pure_bind]
        set pn : BitVec 32 := if s₁.epoch Q ≠ sC.base.mir.epoch Q
          then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
        rcases hmk : mkPub (P := P) sC.base Q rq pn with _ | ⟨pq', pub⟩
        · exact isQueryBoundP_pure _ _ 0
        · have hpub := atomicShortPubB_mkPub hL sC.base Q rq pn hmk
          dsimp only []; rw [← Nat.add_zero 0]
          cases chal with
          | none =>
            refine isQueryBoundP_bind (p := QAtomicShort Pt ℓ) ?_ fun x _ => ?_
            · dsimp only [CryptoGames.SM.transmitQuery]; rw [← Nat.add_zero 0]
              exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ)
                ((isQueryBoundP_query_iff (QAtomicShort Pt ℓ) _ 0).2 fun h => by
                  simp [QAtomicShort, badSendMsg, hpub] at h)
                fun r₀ _ => isQueryBoundP_pure _ (r₀, ()) 0
            · rcases x with ⟨_ | c, _⟩ <;> exact isQueryBoundP_pure _ _ 0
          | some m₁ =>
            refine isQueryBoundP_bind (p := QAtomicShort Pt ℓ) ?_ fun x _ => ?_
            · dsimp only [CryptoGames.SM.challQuery]; rw [← Nat.add_zero 0]
              exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ)
                ((isQueryBoundP_query_iff (QAtomicShort Pt ℓ) _ 0).2 fun h => by
                  simp [QAtomicShort, badSendMsg, hpub] at h)
                fun r₀ _ => isQueryBoundP_pure _ (r₀, ()) 0
            · rcases x with ⟨_ | c, _⟩ <;> exact isQueryBoundP_pure _ _ 0

private theorem semRecvHookS_qAtomicShort {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (T K qep B : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (Q : Party) (w : Bytes) (isDel : Bool) :
    IsQueryBoundP
      (semRecvHookS P Dh encPt encT decT lam T K
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel)
      (QAtomicShort Pt ℓ) 0 := by
  have hDlQ : ∀ c, IsQueryBoundP
      ((fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).onDl Q c ())
      (QAtomicShort Pt ℓ) 0 := fun c => by
    dsimp only [fig8IdSemHook, CryptoGames.SM.deliverQuery]; rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ)
      ((isQueryBoundP_query_iff (QAtomicShort Pt ℓ) _ 0).2 fun h => nomatch h)
      fun res _ => isQueryBoundP_pure _ (res, ()) 0
  have hIjQ : ∀ c, IsQueryBoundP
      ((fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none).onIj Q c ())
      (QAtomicShort Pt ℓ) 0 := fun c => by
    dsimp only [fig8IdSemHook, CryptoGames.SM.injectQuery]; rw [← Nat.add_zero 0]
    exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ)
      ((isQueryBoundP_query_iff (QAtomicShort Pt ℓ) _ 0).2 fun h => nomatch h)
      fun res _ => isQueryBoundP_pure _ (res, ()) 0
  have hAns : ∀ sC' ci? Tpk pq' c', IsQueryBoundP
      (semFwdAnswerHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w isDel ci? Tpk pq' c')
      (QAtomicShort Pt ℓ) 0 := fun sC' ci? Tpk pq' c' => by
    unfold semFwdAnswerHookS; dsimp only []; rw [← Nat.add_zero 0]
    refine isQueryBoundP_bind (p := QAtomicShort Pt ℓ) ?_ fun ⟨res, _⟩ _ => isQueryBoundP_pure _ _ 0
    split_ifs
    · exact hDlQ c'
    · exact hIjQ c'
  have hResync : ∀ sC' ci? Tpk pq' c r, IsQueryBoundP
      (semResyncHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w ci? Tpk pq' c r)
      (QAtomicShort Pt ℓ) 0 := fun sC' ci? Tpk pq' c r => by
    unfold semResyncHookS
    rcases r with _ | ⟨t, i, ⟨pub, m'⟩⟩
    · exact isQueryBoundP_pure _ _ 0
    · rw [← Nat.add_zero 0]
      refine isQueryBoundP_bind (p := QAtomicShort Pt ℓ) (hDlQ c) fun ⟨res, _⟩ _ => ?_
      rcases res with _ | (_ | _) <;> exact isQueryBoundP_pure _ _ 0
  have hEvict : ∀ sC' Tpk pq' c', IsQueryBoundP
      (semFwdEvictHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC' () Q w isDel Tpk pq' c')
      (QAtomicShort Pt ℓ) 0 := fun sC' Tpk pq' c' => by
    unfold semFwdEvictHookS
    split_ifs
    · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure _ _ 0
    · exact hAns sC' none Tpk pq' c'
  have hFwd : ∀ sC' ci? Tpk pq' hc c', IsQueryBoundP
      (semFwdHookS P Dh encPt encT lam T K
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC' () Q w isDel ci? Tpk pq'
          hc c')
      (QAtomicShort Pt ℓ) 0 := fun sC' ci? Tpk pq' hc c' => by
    unfold semFwdHookS
    rcases hc with _ | c
    · exact hAns sC' ci? Tpk pq' c'
    · dsimp only []; split_ifs
      · rcases evalCKS P Dh encPt encT lam T K B sC' Q w c c' with _ | r
        · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact isQueryBoundP_pure _ _ 0
        · exact hResync sC' ci? Tpk pq' c r
      · exact hAns sC' ci? Tpk pq' c'
  unfold semRecvHookS; dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩
    · exact isQueryBoundP_pure _ _ 0
    · rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) ||
                decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T₀
              · exact isQueryBoundP_pure _ _ 0
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                        sC.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hFwd _ none pk pq' _ _
                · simp only [↓reduceIte]
                  exact hEvict _ pk pq' _
            · exact isQueryBoundP_pure _ _ 0
          · exact isQueryBoundP_pure _ _ 0
        · exact isQueryBoundP_pure _ _ 0
      · cases h5 :
          ((sC.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact hFwd sC (some ci) pk pq' _ _
        · exact isQueryBoundP_pure _ _ 0
  · simp only [↓reduceIte]; exact isQueryBoundP_pure _ _ 0

private theorem semCorrHookTGB_qAtomicShort {PQ PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Bsk : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) :
    IsQueryBoundP
      (semCorrHookTGB P Dh encT
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) Bsk sC () Q)
      (QAtomicShort Pt ℓ) 0 := by
  unfold semCorrHookTGB
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp only [hc, ↓reduceIte]; exact isQueryBoundP_pure _ _ 0
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; rw [← Nat.add_zero 0]
    refine isQueryBoundP_bind (p := QAtomicShort Pt ℓ) ?_ fun x _ => ?_
    · dsimp only [fig8IdSemHook, CryptoGames.SM.corrQuery]; rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ)
        ((isQueryBoundP_query_iff (QAtomicShort Pt ℓ) _ 0).2 fun h => nomatch h)
        fun _ _ => isQueryBoundP_pure _ _ 0
    · rcases x with ⟨_ | _, _⟩ <;> exact isQueryBoundP_pure _ _ 0

theorem simFig8ClampSan_sendAtomicShort {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) := by
  unfold SendMsgsOk simFig8ClampSan
  change IsQueryBoundP _ (QAtomicShort Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (p := QAtomicShort Pt ℓ) (liftProb_qAtomicShort ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QAtomicShort Pt ℓ) 0 := by
    refine isQueryBoundP_simulateQ_run_zero A (fun t sC => ?_) _
    rcases t with (n | o)
    · dsimp only [simFig8OracleSan, StateT.lift, StateT.run, StateT.mk]
      rw [← Nat.add_zero 0]
      exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ)
        ((isQueryBoundP_query_iff (QAtomicShort Pt ℓ) (.inl n) 0).2 fun h =>
          absurd h (hQu_QAtomicShort n))
        fun u _ => isQueryBoundP_pure (QAtomicShort Pt ℓ) (u, sC) 0
    · dsimp only [simFig8OracleSan, StateT.run, StateT.mk]
      refine (isQueryBoundP_map_iff _ _ _).mpr ?_
      rcases o with ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · exact semSendHook_qAtomicShort P hL Dh encPt encT lam qep sC Q m none r
      · exact semSendHook_qAtomicShort P hL Dh encPt encT lam qep sC Q m₀ (some m₁) r
      · dsimp only [semHandleHookDedupS, fig8IdSemHook]; rw [← Nat.add_zero 0]
        exact isQueryBoundP_bind (p := QAtomicShort Pt ℓ)
          (semRecvHookS_qAtomicShort P Dh encPt encT decT lam T Kc qep B sC Q w true)
          fun ⟨rr, sC₁, _⟩ _ => by rw [pure_bind]; exact isQueryBoundP_pure _ _ 0
      · exact semRecvHookS_qAtomicShort P Dh encPt encT decT lam T Kc qep B sC Q w false
      · exact semCorrHookTGB_qAtomicShort P Dh encT Bsk sC Q
  rw [StateT.run'_eq]
  exact (isQueryBoundP_map_iff _ _ _).mpr hsim

end SendAtomicShort

theorem simFig8RedProg_sendAtomicShort {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      ((simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) := by
  rw [simFig8RedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  exact simFig8ClampSan_sendAtomicShort (paramsV1 C K idA idB)
    (CryptoVerification.LibsignalSession.HeadlineV1.atomicLengthsOk_paramsIdsWithSpqr_v1
      C K idA idB ℓ hℓ)
    Dh encPt encT decT lam (simFig8QepClamp qep q)
    (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A

section GuardedSMShortSan

open OracleSpec OracleComp
open CryptoGames.GuardedSafe (GuardedSafePost)
open CryptoGames.SM
  (RecvResult partyEnc noBobSendInEpoch0 noAliceCorrWhileAliceBelowEpoch10)
open CryptoGames.LibsignalSession (Params)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C Fig8Comp SimState inReceiveOnlyEpoch onAcceptPure onAnswerPure
   semDrawSendCoins semSendHook mkPub simParseRecvC)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.LibsignalSM.Proofs.QueryBounds (FSpec)
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (smRespShort smRecvLong SimShortInv simShortInv_initSim simShortInv_record
   hQu_smRecvLong epMgmt_trans_eq mem_accept_trans inTransit_mem_and_ct)
open Computational.Proofs.GameHop.CompDedup (afterCorrDedup)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (evalCKS semFwdAnswerHookS semResyncHookS semFwdEvictHookS semFwdHookS semRecvHookS
   semCorrHookTGB semHandleHookDedupS)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost (fig8IdSemHook)

private abbrev Fig8SafePost (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (x : Fig8Comp Pt ℓ (α × (LibsignalToModularSchemeSimState PQ Pt ℓ × Unit))) : Prop :=
  GuardedSafePost
    (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (T := Pt))
    (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
      (Coins := BitVec 256) (T := Pt))
    (fun r => SimShortInv r.2.1.base) x

private theorem simShortInv_onAcceptPure {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (s : SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (onAcceptPure qep Q w isDel t i m ci? T pq' s).2 := by
  unfold onAcceptPure; dsimp only []; split_ifs
  · rcases s.mir.inTransit Q.other w with _ | r
    · exact hs
    · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact hs
  · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact ⟨hs.1, hs.2⟩

private theorem simShortInv_onAnswerPure {PQ Pt : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (onAnswerPure qep Q w isDel ci? T pq' res s).2 := by
  unfold onAnswerPure
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact simShortInv_onAcceptPure qep Q w isDel t i _ ci? T pq' s hs

private theorem simParseRecvC_ser_eq {PQ PQC Pt : Type} (P : Params PQ PQC)
    (decT : PublicKey → Option Pt) (B : ℕ) (qB : Bool) (pq : PQ) (w : Bytes)
    {pq' : PQ} {i : ℕ} {pk : PublicKey} {T? : Option Pt} {lct : ℕ × LibsignalCiphertextWithSalt32}
    (hp : simParseRecvC P decT B qB pq w = some (pq', (i, (pk, (T?, lct))))) :
    lct.2.1.1 = w.take (w.length - 8) := by
  unfold simParseRecvC at hp; split_ifs at hp; dsimp only [] at hp
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
  · rw [hparse] at hp; cases hp
  · rw [hparse] at hp; dsimp only [] at hp; split_ifs at hp
    rcases hspqr : P.spqr.recv pq h.pqRatchet with _ | ⟨pq1, salt⟩
    · rw [hspqr] at hp; cases hp
    · rw [hspqr] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      exact congrArg (fun x : ℕ × LibsignalCiphertextWithSalt32 => x.2.1.1) hp.2.2.2.2.symm

private theorem simDrawSendCoins_safePost {PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (r : Option PQC) :
    GuardedSafePost
      (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (T := Pt))
      (fun _ => True)
      (semDrawSendCoins (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) r) := by
  cases r with
  | none =>
    dsimp only [semDrawSendCoins, fig8IdSemHook]
    exact (GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ PQC)).bind fun _ _ =>
      GuardedSafePost.pure trivial
  | some _ =>
    dsimp only [semDrawSendCoins, fig8IdSemHook]
    exact (GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ (BitVec 256))).bind fun _ _ =>
      GuardedSafePost.pure trivial

private theorem semSendHook_safePost {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    Fig8SafePost PQ Pt ℓ
      (semSendHook P Dh encPt encT lam
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q m₀ chal r) := by
  unfold semSendHook
  by_cases hc1 : (sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q)) = true
  · simp only [hc1, ↓reduceIte]; exact GuardedSafePost.pure hs
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
    rcases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with _ | s₁
    · exact GuardedSafePost.pure hs
    · have htr₁ : s₁.trans = sC.base.mir.trans := epMgmt_trans_eq hep
      dsimp only []
      by_cases hc2 : (chal.isSome && !(s₁.safeCh 3 Q)) = true
      · simp only [hc2, ↓reduceIte]; exact GuardedSafePost.pure hs
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte]
        refine (simDrawSendCoins_safePost r).bind fun ⟨rq, rc⟩ _ => ?_
        dsimp only [fig8IdSemHook]; rw [pure_bind]
        set pn : BitVec 32 := if s₁.epoch Q ≠ sC.base.mir.epoch Q
          then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
        rcases mkPub (P := P) sC.base Q rq pn with _ | ⟨pq', pub⟩
        · exact GuardedSafePost.pure hs
        · dsimp only []
          cases chal with
          | none =>
            dsimp only [CryptoGames.SM.transmitQuery]; rw [bind_assoc]
            refine GuardedSafePost.query_bind not_false fun res hres => ?_
            rw [pure_bind]
            cases res with
            | none => exact GuardedSafePost.pure hs
            | some c =>
              exact GuardedSafePost.pure (simShortInv_record hs htr₁ Q m₀ false pq' pn c (hres c rfl))
          | some m₁ =>
            dsimp only [CryptoGames.SM.challQuery]; rw [bind_assoc]
            refine GuardedSafePost.query_bind not_false fun res hres => ?_
            rw [pure_bind]
            cases res with
            | none => exact GuardedSafePost.pure hs
            | some c =>
              exact GuardedSafePost.pure (simShortInv_record hs htr₁ Q m₀ true pq' pn c (hres c rfl))

private theorem semFwdAnswerHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    Fig8SafePost PQ Pt ℓ
      (semFwdAnswerHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q w isDel ci? Tpk pq' c') := by
  unfold semFwdAnswerHookS; dsimp only []
  refine GuardedSafePost.bind (P := fun _ => True) ?_ fun ⟨res, _⟩ _ =>
    GuardedSafePost.pure (simShortInv_onAnswerPure qep Q w isDel ci? Tpk pq' res sC.base hs)
  split_ifs
  · dsimp only [fig8IdSemHook, CryptoGames.SM.deliverQuery]
    exact GuardedSafePost.query_bind (fun h => h hc') fun _ _ => GuardedSafePost.pure trivial
  · dsimp only [fig8IdSemHook, CryptoGames.SM.injectQuery]
    exact GuardedSafePost.query_bind (fun h => h hc') fun _ _ => GuardedSafePost.pure trivial

private theorem semResyncHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    Fig8SafePost PQ Pt ℓ
      (semResyncHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q w ci? Tpk pq' c r) := by
  unfold semResyncHookS
  rcases r with _ | ⟨t, i, ⟨_, m'⟩⟩
  · exact GuardedSafePost.pure hs
  · dsimp only [fig8IdSemHook, CryptoGames.SM.deliverQuery]; rw [bind_assoc]
    refine GuardedSafePost.query_bind (fun h => h hc) fun res _ => ?_
    rw [pure_bind]
    rcases res with _ | (_ | _)
    · exact GuardedSafePost.pure hs
    · exact GuardedSafePost.pure hs
    · exact GuardedSafePost.pure (simShortInv_onAcceptPure qep Q w true t i m' ci? Tpk pq' sC.base hs)

private theorem semFwdEvictHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ)
    (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    Fig8SafePost PQ Pt ℓ
      (semFwdEvictHookS P Dh encPt encT lam T
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep sC () Q w isDel Tpk pq' c') := by
  unfold semFwdEvictHookS; split_ifs
  · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact GuardedSafePost.pure hs
  · exact semFwdAnswerHookS_safePost P Dh encPt encT lam T qep sC hs Q w isDel none Tpk pq' c' hc'

private theorem semFwdHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T K qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt))
    (hhon : ∀ c, honestC = some c → c.2.2.1.1.length < 2 ^ 32)
    (c' : Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    Fig8SafePost PQ Pt ℓ
      (semFwdHookS P Dh encPt encT lam T K
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel ci? Tpk pq'
          honestC c') := by
  unfold semFwdHookS
  rcases honestC with _ | c
  · exact semFwdAnswerHookS_safePost P Dh encPt encT lam T qep sC hs Q w isDel ci? Tpk pq' c' hc'
  · dsimp only []; split_ifs
    · rcases evalCKS P Dh encPt encT lam T K B sC Q w c c' with _ | r
      · dsimp only [fig8IdSemHook]; rw [pure_bind]; exact GuardedSafePost.pure hs
      · exact semResyncHookS_safePost P Dh encPt encT lam T qep sC hs Q w ci? Tpk pq' c
          (hhon c rfl) r
    · exact semFwdAnswerHookS_safePost P Dh encPt encT lam T qep sC hs Q w isDel ci? Tpk pq' c' hc'

private theorem semRecvHookS_safePost {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (T K qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) :
    Fig8SafePost PQ Pt ℓ
      (semRecvHookS P Dh encPt encT decT lam T K
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) qep B sC () Q w isDel) := by
  unfold semRecvHookS; dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hp : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w
      with _ | ⟨pq', i, pk, T?, lct⟩
    · exact GuardedSafePost.pure hs
    · have hwlen : w.length < 2 ^ 32 := by
        cases isDel with
        | true =>
          rcases htr : sC.base.mir.inTransit Q.other w with _ | rec'
          · simp [htr] at href
          · obtain ⟨hmem, rfl⟩ := inTransit_mem_and_ct htr
            exact hs.1 rec' hmem
        | false =>
          by_cases hw9 : w.length < 9
          · omega
          · have hadm : ratchetKeyAdmissible P.codec decT encT w = true := by
              revert href; cases ratchetKeyAdmissible P.codec decT encT w <;> simp
            unfold ratchetKeyAdmissible at hadm; simp only [hw9, ↓reduceIte] at hadm
            have hp0 := hp; unfold simParseRecvC at hp0; split_ifs at hp0; dsimp only [] at hp0
            rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
            · rw [hparse] at hp0; cases hp0
            · simp only [hparse, Bool.and_eq_true, decide_eq_true_eq] at hadm
              exact hadm.1
      have hlct : lct.2.1.1.length < 2 ^ 32 := by
        rw [simParseRecvC_ser_eq P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w hp,
          List.length_take]
        omega
      have hhon : ∀ c : Fig8C Pt,
          (sC.base.honest.find? fun (wc : Bytes × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
              (fun (wc : Bytes × Fig8C Pt) => wc.2) = some c →
          c.2.2.1.1.length < 2 ^ 32 := by
        intro c hc_eq
        rcases Option.mem_map.mp hc_eq with ⟨wc, hfind, rfl⟩
        exact hs.2 wc (List.mem_of_find?_eq_some hfind)
      have hmkC : ∀ (t : ℕ) (To : Option Pt),
          (match (sC.base.honest.find? fun (wc : Bytes × Fig8C Pt) =>
               wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
                 (fun (wc : Bytes × Fig8C Pt) => wc.2) with
           | some (c : Fig8C Pt) => if c.2.2.2 = lct.2.2 then c else ((t, To), lct)
           | none => ((t, To), lct)).2.2.1.1.length < 2 ^ 32 := by
        intro t To
        rcases hfind : sC.base.honest.find? (fun (wc : Bytes × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with _ | wc
        · exact hlct
        · simp only [Option.map]; split
          · exact hs.2 wc (List.mem_of_find?_eq_some hfind)
          · exact hlct
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · have hsAmb : SimShortInv
            ({ sC with base :=
                if inReceiveOnlyEpoch sC.base.mir Q ||
                    (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
                  { sC.base with amb := sC.base.amb + 1 }
                else sC.base }).base := by
          dsimp only []; split_ifs <;> exact ⟨hs.1, hs.2⟩
        cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) ||
                decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T₀
              · exact GuardedSafePost.pure hsAmb
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                        sC.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact semFwdHookS_safePost P Dh encPt encT lam T K qep B _ hsAmb Q w isDel none
                    pk pq' _ hhon _ (hmkC _ _)
                · simp only [↓reduceIte]
                  exact semFwdEvictHookS_safePost P Dh encPt encT lam T qep _ hsAmb Q w isDel
                    pk pq' _ hlct
            · simp only [↓reduceIte]; exact GuardedSafePost.pure hsAmb
          · simp only [↓reduceIte]; exact GuardedSafePost.pure hs
        · simp only [↓reduceIte]; exact GuardedSafePost.pure hs
      · cases h5 :
          ((sC.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact semFwdHookS_safePost P Dh encPt encT lam T K qep B sC hs Q w isDel (some ci)
            pk pq' _ hhon _ (hmkC _ _)
        · simp only [↓reduceIte]; exact GuardedSafePost.pure hs
  · simp only [↓reduceIte]; exact GuardedSafePost.pure hs

private theorem semCorrHookTGB_safePost {PQ PQC Pt : Type} [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Bsk : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (hs : SimShortInv sC.base) (Q : Party) :
    Fig8SafePost PQ Pt ℓ
      (semCorrHookTGB P Dh encT
        (fig8IdSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ) none) Bsk sC () Q) := by
  unfold semCorrHookTGB
  by_cases hc :
      (sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q)) = true
  · simp only [hc, ↓reduceIte]; exact GuardedSafePost.pure hs
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    dsimp only [fig8IdSemHook, CryptoGames.SM.corrQuery]; rw [bind_assoc]
    refine GuardedSafePost.query_bind not_false fun res _ => ?_
    rw [pure_bind]
    rcases res with _ | _
    · exact GuardedSafePost.pure hs
    · exact GuardedSafePost.pure ⟨hs.1, hs.2⟩

theorem simFig8ClampSan_guardedSMShort {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    GuardedSMShort (simFig8ClampSan P ℓ Dh encPt encT decT lam qep B T Kc Bsk A) := by
  unfold GuardedSMShort simFig8ClampSan
  refine (GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ BitVec 256)).bind fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost
      (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (T := Pt))
      (fun r => SimShortInv r.2.base)
      ((simulateQ (simFig8OracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A).run
        (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) := by
    refine GuardedSafePost.simulateQ_run
      (I := fun sC : LibsignalToModularSchemeSimState PQ Pt ℓ => SimShortInv sC.base)
      (GuardedSafePost.true_of_false A) ?_ (simShortInv_initSim _ _)
    rintro (n | o) _ sC hs
    · dsimp only [simFig8OracleSan, StateT.lift, StateT.run, StateT.mk]
      exact (GuardedSafePost.query (hQu_smRecvLong n)).bind fun _ _ =>
        GuardedSafePost.pure ⟨trivial, hs⟩
    · dsimp only [simFig8OracleSan, StateT.run, StateT.mk]
      refine GuardedSafePost.map (Prod.map id Prod.fst) ?_ (fun _ hp => ⟨trivial, hp⟩)
      rcases o with ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
      · exact semSendHook_safePost P Dh encPt encT lam qep sC hs Q m none r
      · exact semSendHook_safePost P Dh encPt encT lam qep sC hs Q m₀ (some m₁) r
      · dsimp only [semHandleHookDedupS, fig8IdSemHook]
        exact (semRecvHookS_safePost P Dh encPt encT decT lam T Kc qep B sC hs Q w true).bind
          fun ⟨rr, sC₁, _⟩ hs₁ => by rw [pure_bind]; exact GuardedSafePost.pure hs₁
      · exact semRecvHookS_safePost P Dh encPt encT decT lam T Kc qep B sC hs Q w false
      · exact semCorrHookTGB_safePost P Dh encT Bsk sC hs Q
  exact hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial

end GuardedSMShortSan

theorem simFig8RedProg_guardedSMShort {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    GuardedSMShort
      ((simFig8RedProg ℓ C K idA idB Dh encPt encT decT lam qep q).eval (fun _ => A) ()) := by
  rw [simFig8RedProg_eval_san hℓ C K idA idB Dh encPt encT decT lam qep q A hq]
  exact simFig8ClampSan_guardedSMShort (paramsV1 C K idA idB) Dh encPt encT decT lam
    (simFig8QepClamp qep q)
    (2 ^ 32 + q + 2) (50000 * q) (25001 * q + 25000) (25000 * q) A

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8Prog
