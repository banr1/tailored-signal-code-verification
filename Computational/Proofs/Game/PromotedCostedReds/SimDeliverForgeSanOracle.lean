/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEClamp2

/-!
# Sanitized Oracle Wrapper for `SimDeliverForge`

Defines the raw `(sC, sent)` state encoding (`dfFullT`), the sanitized `DeliverForge` oracle
`simDeliverForgeOracleSan`, step-wise preservation of `DFStateInv`, and the game-loop `.eval`
bridge `simDeliverForgeProgOfStep_eval_san`.
-/

@[expose] public section

set_option autoImplicit false

open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore (evalCKS semCorrHookTGB semFwdAnswerHookS semFwdEvictHookS semFwdHookS semHandleHookDedupS semHandleHookDedupS_preserves_sC_inv semRecvHookS semResyncHookS)
open ReductionDsl (BV256 Comp CostedReduction GhostStT Ty atomicSessionOps atomicSig e2eSessionCodec fig8CtOfV fig8CtT fig8CtV fig8SmIfaceDF handlerImpl smQT smRT)

namespace Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Expr Comp CostedReduction handlerImpl atomicSig atomicSessionOps
  e2eSessionCodec GhostStT BV256 fig8SmIfaceDF smQT smRT fig8CtT fig8CtV fig8CtOfV)
open _root_.CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimCStateBounded SimCStateInv
  deliverForgeSemHook)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState Params)
open CryptoGames.SM.Construction.DeliverForge (AdversaryDF AdversaryCompDF specDF)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init)
open CryptoVerification.E2E (Bytes paramsV1)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (sessSpqrKemOp atomicDraw256 eval_sessSpqrKemOp atomicDraw256_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (comp_eval_bind comp_eval_ret dummyBoolSessionRed)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost (atomicTyDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (atomicTyDescBits_simFullT atomicTyDescBits_fig8CtT)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simFullT simFullEnc simFullDec simFullDec_simFullEnc fig8CtOfV_fig8CtV
   initSimCE eval_initSimCE atomicSpqrV1InitOp_lossless simCStateInv_initSimC)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (SanExtra)

export CryptoGames.Ratchet.LibsignalSim (deliverForgeSemHook)
export Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (SanExtra)

@[reducible] def dfFullT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  ReductionDsl.Ty.prod (simFullT ℓ Pt) (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))

@[reducible] def dfFullEnc {ℓ : ℕ} {Pt : Type}
    (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) :
    (dfFullT ℓ Pt).denote :=
  (simFullEnc s.1, s.2.map fig8CtV)

@[reducible] def dfFullDec {ℓ : ℕ} {Pt : Type}
    (v : (dfFullT ℓ Pt).denote) :
    LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt) :=
  (simFullDec v.1, v.2.map fig8CtOfV)

@[simp] theorem dfFullDec_dfFullEnc {ℓ : ℕ} {Pt : Type}
    (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)) :
    dfFullDec (dfFullEnc s) = s := by
  rcases s with ⟨sC, sent⟩
  simp only [dfFullDec, simFullDec_simFullEnc, List.map_map, Prod.mk.injEq, true_and]
  have hfn : (fig8CtOfV (ℓ := ℓ) (Pt := Pt) ∘ fig8CtV) = id := by
    funext c; exact fig8CtOfV_fig8CtV c
  simp [hfn]

theorem atomicTyDescBits_dfFullT (ℓ : ℕ) (Pt : Type) :
    atomicTyDescBits (dfFullT ℓ Pt) ≤ 2000 := by
  have h1 := atomicTyDescBits_simFullT (ℓ := ℓ) (Pt := Pt)
  have h2 := atomicTyDescBits_fig8CtT (ℓ := ℓ) (Pt := Pt)
  change atomicTyDescBits (ReductionDsl.Ty.prod (simFullT ℓ Pt) (.list (fig8CtT (ℓ := ℓ) (Pt := Pt)))) ≤ 2000
  generalize hA : simFullT ℓ Pt = A at h1 ⊢
  generalize hC : fig8CtT (ℓ := ℓ) (Pt := Pt) = C at h2 ⊢
  dsimp only [atomicTyDescBits]
  omega

/-- Sanitized `DeliverForge` semantic query implementation (`semHandleHookDedupS` with
`deliverForgeSemHook`). -/
def simDeliverForgeOracleSan {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt))
        (AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)))
  | .inl n => StateT.lift
    (query (spec := unifSpec + specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) (.inl n))
  | .inr t => StateT.mk fun s =>
    semHandleHookDedupS P Dh encPt encT decT lam T Kc Bsk
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B t s.1 s.2

abbrev simDeliverForgeOracleSanQ {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :=
  simDeliverForgeOracleSan (ℓ := ℓ) P Dh encPt encT decT lam
    qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q)

def simDeliverForgeClampSan {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :
    AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) :=
  show AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt) Bool
  from do
    let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
      AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
        (BitVec 256))
    let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    (simulateQ (simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk) A).run' (sC₀, [])

abbrev simDeliverForgeClampSanQ {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC Bytes) :=
  simDeliverForgeClampSan P ℓ Dh encPt encT decT lam
    qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q) A

@[simp] theorem simDeliverForgeOracleSan_inr_run {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) :
    ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk (.inr t)).run s) =
      semHandleHookDedupS P Dh encPt encT decT lam T Kc Bsk
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B t s.1 s.2 :=
  rfl

theorem simDeliverForgeOracleSan_send_run {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (Q : Party) (m : Plain ℓ) (r : Option PQC)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) :
    ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk
        (.inr (.inl (.inl (.inl (.inl (Q, m, r))))))).run (sC, ex)) =
      CryptoGames.Ratchet.LibsignalSim.semSendHook P Dh encPt encT lam
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC ex Q m none r :=
  rfl

theorem simDeliverForgeOracleSan_chall_run {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) :
    ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run (sC, ex)) =
      CryptoGames.Ratchet.LibsignalSim.semSendHook P Dh encPt encT lam
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep sC ex Q m₀ (some m₁) r :=
  rfl

theorem simDeliverForgeOracleSan_deliver_run {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (Q : Party) (w : Bytes)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) :
    ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk
        (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, ex)) =
      semRecvHookS P Dh encPt encT decT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w true := by
  dsimp only [simDeliverForgeOracleSan, StateT.run, StateT.mk, semHandleHookDedupS]
  have hpost : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDeliverPost =
      fun _ _ _ ex' => pure ex' := rfl
  rw [hpost]
  simp only [pure_bind, Prod.mk.eta, bind_pure]

theorem simDeliverForgeOracleSan_inject_run {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (Q : Party) (w : Bytes)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) :
    ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk
        (.inr (.inl (.inr (Q, w))))).run (sC, ex)) =
      semRecvHookS P Dh encPt encT decT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B sC ex Q w false :=
  rfl

theorem simDeliverForgeOracleSan_corrupt_run {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (Q : Party)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : List (Fig8C Pt)) :
    ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk
        (.inr (.inr Q))).run (sC, ex)) =
      semCorrHookTGB P Dh encT
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) Bsk sC ex Q :=
  rfl

def DFStateBounded {PQ Pt : Type} {ℓ : ℕ} (L : ℕ)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) : Prop :=
  SimCStateBounded L s.1 ∧ s.2.length ≤ L

/-- Step-indexed invariant on `(sC, sent)` with `m` remaining game queries. -/
def DFStateInv {PQ Pt : Type} {ℓ : ℕ} (L m : ℕ)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)) : Prop :=
  SimCStateInv L m s.1 ∧ s.2.length + m ≤ L

theorem DFStateInv.mono {PQ Pt : Type} {ℓ L m m' : ℕ}
    {s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)}
    (hle : m' ≤ m) (h : DFStateInv L m s) : DFStateInv L m' s :=
  ⟨h.1.mono hle, by have := h.2; omega⟩

theorem DFStateInv.toBounded {PQ Pt : Type} {ℓ L m : ℕ}
    {s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt)}
    (h : DFStateInv L m s) : DFStateBounded L s :=
  ⟨h.1.toBounded, by have := h.2; omega⟩

theorem dfStateInv_initSimC {PQ Pt : Type} [Zero Pt] {ℓ L q : ℕ} (hqL : q ≤ L) (pqA pqB : PQ) :
    DFStateInv (ℓ := ℓ) (Pt := Pt) L q (initSimC pqA pqB, []) :=
  ⟨simCStateInv_initSimC hqL pqA pqB, by simp [hqL]⟩

private theorem deliverForgeSemHook_onProbe_eq {PQC Pt : Type}
    [DecidableEq Pt] [SampleableType PQC] {ℓ : ℕ}
    (Q : Party) (c' : Fig8C Pt) (ex₀ : List (Fig8C Pt)) :
    ∀ ex₁ ∈ support ((deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex₀),
      ex₁ = ex₀ := by
  intro ex₁ hx
  unfold deliverForgeSemHook at hx
  rcases hfind : ex₀.find?
      (fun c => CryptoGames.LibsignalSM.Proofs.Refinement.sameWireFig8 c c') with _ | c <;>
    simp only [hfind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
  · exact hx
  · obtain ⟨_, -, rfl⟩ := hx; rfl

private theorem semFwdAnswerHookS_deliverForge_ex_eq {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    ∀ x ∈ support (semFwdAnswerHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      x.2.2 = ex₀ := by
  rintro ⟨_, _, ex₁⟩ hx
  unfold semFwdAnswerHookS at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, hq, -, -, rfl⟩ := hx
  split_ifs at hq <;>
    simp only [deliverForgeSemHook, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hq <;>
    obtain ⟨_, -, -, rfl⟩ := hq <;> rfl

private theorem semResyncHookS_deliverForge_ex_eq {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : Fig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    ∀ x ∈ support (semResyncHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC₀ ex₀ Q w ci? Tpk pq' c r),
      x.2.2 = ex₀ := by
  rintro ⟨_, _, ex₁⟩ hx
  unfold semResyncHookS at hx
  rcases r with _ | ⟨t, i, _, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    exact hx.2.2
  · simp only [deliverForgeSemHook, bind_assoc, pure_bind, mem_support_bind_iff] at hx
    obtain ⟨res, -, hx⟩ := hx
    rcases res with _ | (_ | ⟨_, _, _⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx <;>
      exact hx.2.2

private theorem semFwdEvictHookS_deliverForge_ex_eq {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (Tpk : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    ∀ x ∈ support (semFwdEvictHookS P Dh encPt encT lam T
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      x.2.2 = ex₀ := by
  rintro ⟨rr, sC₁, ex₁⟩ hx
  unfold semFwdEvictHookS at hx
  split at hx
  · rw [mem_support_bind_iff] at hx
    obtain ⟨ex', hp, hx⟩ := hx
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, _, rfl⟩
    exact deliverForgeSemHook_onProbe_eq Q c' ex₀ ex₁ hp
  · exact semFwdAnswerHookS_deliverForge_ex_eq P Dh encPt encT lam T qep
      sC₀ ex₀ Q w isDel none Tpk pq' c' (rr, sC₁, ex₁) hx

private theorem semFwdHookS_deliverForge_ex_eq {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (T Kc qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    ∀ x ∈ support (semFwdHookS P Dh encPt encT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c'),
      x.2.2 = ex₀ := by
  rintro ⟨rr, sC₁, ex₁⟩ hx
  unfold semFwdHookS at hx
  rcases honestC with _ | c <;> dsimp only [] at hx
  · exact semFwdAnswerHookS_deliverForge_ex_eq P Dh encPt encT lam T qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' (rr, sC₁, ex₁) hx
  · split at hx
    · rcases hev : evalCKS P Dh encPt encT lam T Kc B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · rw [mem_support_bind_iff] at hx
        obtain ⟨ex', hp, hx⟩ := hx
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        rcases hx with ⟨_, _, rfl⟩
        exact deliverForgeSemHook_onProbe_eq Q c' ex₀ ex₁ hp
      · exact semResyncHookS_deliverForge_ex_eq P Dh encPt encT lam T qep
          sC₀ ex₀ Q w ci? Tpk pq' c r (rr, sC₁, ex₁) hx
    · exact semFwdAnswerHookS_deliverForge_ex_eq P Dh encPt encT lam T qep
        sC₀ ex₀ Q w isDel ci? Tpk pq' c' (rr, sC₁, ex₁) hx

theorem semRecvHookS_deliverForge_ex_eq {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (T Kc qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (Fig8C Pt))
    (Q : Party) (w : Bytes) (isDel : Bool) :
    ∀ x ∈ support (semRecvHookS P Dh encPt encT decT lam T Kc
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ))
        qep B sC₀ ex₀ Q w isDel),
      x.2.2 = ex₀ := by
  rintro ⟨rr, sC₁, ex₁⟩ hx
  unfold semRecvHookS at hx
  dsimp only [] at hx
  split at hx
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; exact hx.2.2
  · rcases hp : CryptoGames.Ratchet.LibsignalSim.simParseRecvC P decT (2 ^ 32)
        (CryptoGames.SM.partyEnc Q) (sC₀.base.pq Q) w with _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hp] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; exact hx.2.2
    · rcases hci : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hci] at hx
      · split at hx
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; exact hx.2.2
        · split at hx
          · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; exact hx.2.2
          · split at hx
            · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; exact hx.2.2
            · rcases hT : T? with _ | T₀ <;> simp only [hT] at hx
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; exact hx.2.2
              · split at hx
                · exact semFwdEvictHookS_deliverForge_ex_eq P Dh encPt encT lam T qep
                    _ ex₀ Q w isDel pk pq' _ (rr, sC₁, ex₁) hx
                · exact semFwdHookS_deliverForge_ex_eq P Dh encPt encT lam T Kc qep B
                    _ ex₀ Q w isDel none pk pq' _ _ (rr, sC₁, ex₁) hx
      · split at hx
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; exact hx.2.2
        · exact semFwdHookS_deliverForge_ex_eq P Dh encPt encT lam T Kc qep B
            sC₀ ex₀ Q w isDel (some ci) pk pq' _ _ (rr, sC₁, ex₁) hx

theorem semCorrHookTGB_deliverForge_ex_eq {PQ PQC Pt : Type}
    [DecidableEq Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (Bsk : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (Fig8C Pt)) (Q : Party) :
    ∀ x ∈ support (semCorrHookTGB P Dh encT
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) Bsk sC₀ ex₀ Q),
      x.2.2 = ex₀ := by
  rintro ⟨_, _, ex₁⟩ hx
  unfold semCorrHookTGB at hx
  split at hx
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx; exact hx.2.2
  · rw [mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, hcr, hx⟩ := hx
    have hex' : ex' = ex₀ := by
      dsimp only [deliverForgeSemHook] at hcr
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcr
      obtain ⟨_, -, -, rfl⟩ := hcr
      rfl
    subst hex'
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx <;>
      exact hx.2.2

theorem semHandleHookDedupS_deliverForge_preserves_sent_len {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (T Kc Bsk L m qep B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : List (Fig8C Pt))
    (hlen : ex₀.length + (m + 1) ≤ L) :
    ∀ x ∈ support (semHandleHookDedupS P Dh encPt encT decT lam T Kc Bsk
        (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) qep B t sC₀ ex₀),
      x.2.2.length + m ≤ L := by
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact CryptoGames.Ratchet.LibsignalSim.semSendHook_preserves_ex_inv P Dh encPt encT lam
      (CryptoGames.Ratchet.LibsignalSim.deliverForgeSemHookInv L) m qep sC₀ ex₀ Q m₀ none r hlen
  · exact CryptoGames.Ratchet.LibsignalSim.semSendHook_preserves_ex_inv P Dh encPt encT lam
      (CryptoGames.Ratchet.LibsignalSim.deliverForgeSemHookInv L) m qep sC₀ ex₀ Q m₀ (some m₁) r hlen
  · rintro ⟨rr, sC₁, ex₁⟩ hx
    unfold semHandleHookDedupS at hx
    have hpost : (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onDeliverPost =
        fun _ _ _ ex' => pure ex' := rfl
    rw [hpost] at hx
    simp only [pure_bind, Prod.mk.eta, bind_pure] at hx
    have hex := semRecvHookS_deliverForge_ex_eq P Dh encPt encT decT lam T Kc qep B
      sC₀ ex₀ Q w true (rr, sC₁, ex₁) hx
    dsimp only [] at hex ⊢; rw [hex]; omega
  · rintro ⟨rr, sC₁, ex₁⟩ hx
    have hex := semRecvHookS_deliverForge_ex_eq P Dh encPt encT decT lam T Kc qep B
      sC₀ ex₀ Q w false (rr, sC₁, ex₁) hx
    dsimp only [] at hex ⊢; rw [hex]; omega
  · rintro ⟨rr, sC₁, ex₁⟩ hx
    have hex := semCorrHookTGB_deliverForge_ex_eq P Dh encT Bsk sC₀ ex₀ Q (rr, sC₁, ex₁) hx
    dsimp only [] at hex ⊢; rw [hex]; omega

theorem simDeliverForgeOracleSan_preserves_dfStateInv {PQ PQC Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (L m qep B T Kc Bsk : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC Bytes).Domain)
    (s : LibsignalToModularSchemeSimState PQ Pt ℓ × List (Fig8C Pt))
    (hInv : DFStateInv L (m + 1) s) :
    ∀ x ∈ support ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk (.inr t)).run s),
      DFStateInv L m x.2 := by
  rintro ⟨rr, sC', ex'⟩ hx
  exact ⟨semHandleHookDedupS_preserves_sC_inv P Dh encPt encT decT lam T Kc Bsk
      (deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)) L m qep B t s.1 s.2 hInv.1
      (rr, sC', ex') hx,
    semHandleHookDedupS_deliverForge_preserves_sent_len P Dh encPt encT decT lam T Kc Bsk
      L m qep B t s.1 s.2 hInv.2 (rr, sC', ex') hx⟩

def simDeliverForgeInitImpl {ℓ : ℕ} {Pt : Type} [Zero Pt] (C : Crypto) (K : MlKem) :
    AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
      (Unit × (LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt))) := do
  let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
    AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
      (BitVec 256))
  return ((), (initSimC (spqrV1Init C.F K .a2b pqrKey) (spqrV1Init C.F K .b2a pqrKey), []))

def simDeliverForgeInitC {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [.unit] (.prod .unit (dfFullT ℓ Pt)) :=
  .bind (atomicDraw256 (I := fig8SmIfaceDF ℓ Pt) rfl)
    (.ret (.pair .unit
      (.pair
        (initSimCE
          (sessSpqrKemOp .spqrV1InitOp (.pair (.bool true) (.var .zero)))
          (sessSpqrKemOp .spqrV1InitOp (.pair (.bool false) (.var .zero))))
        .nil)))

theorem simDeliverForgeInitC_eval {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    (simDeliverForgeInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval (.cons () .nil) =
      Prod.map id (dfFullEnc (ℓ := ℓ) (Pt := Pt)) <$>
        simDeliverForgeInitImpl (ℓ := ℓ) (Pt := Pt) C K := by
  unfold simDeliverForgeInitC simDeliverForgeInitImpl
  rw [comp_eval_bind, atomicDraw256_eval]
  have hlift : (fig8SmIfaceDF ℓ Pt).liftP ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) =
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
          (BitVec 256)) := by
    induction ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind n mx ih =>
      dsimp only [_root_.ReductionDsl.Iface.liftP] at ih ⊢
      rw [simulateQ_bind, simulateQ_query]
      exact bind_congr ih
  rw [hlift]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  rw [comp_eval_ret]
  have hinit :
      (initSimCE (ℓ := ℓ) (Pt := Pt)
        (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .spqrV1InitOp (.pair (.bool true) (.var .zero)))
        (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .spqrV1InitOp (.pair (.bool false) (.var .zero)))).eval
        (.cons pqrKey (.cons () .nil) : _root_.ReductionDsl.Env [BV256, .unit]) =
      simFullEnc (ℓ := ℓ) (Pt := Pt)
        (initSimC (spqrV1Init C.F K .a2b pqrKey) (spqrV1Init C.F K .b2a pqrKey)) := by
    rw [eval_initSimCE, eval_sessSpqrKemOp, eval_sessSpqrKemOp]
    dsimp only [_root_.ReductionDsl.AtomicSpqrKemOp.eval, ReductionDsl.Expr.eval]
    rw [atomicSpqrV1InitOp_lossless, atomicSpqrV1InitOp_lossless]
    rfl
  have hpair :
      (ReductionDsl.Expr.pair .unit
        (.pair
          (initSimCE
            (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .spqrV1InitOp (.pair (.bool true) (.var .zero)))
            (sessSpqrKemOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .spqrV1InitOp (.pair (.bool false) (.var .zero))))
          .nil)).eval
        (.cons pqrKey (.cons () .nil) : _root_.ReductionDsl.Env [BV256, .unit]) =
      ((), dfFullEnc (initSimC (spqrV1Init C.F K .a2b pqrKey) (spqrV1Init C.F K .b2a pqrKey), [])) := by
    change ((), (_, [])) = _
    rw [hinit]
    rfl
  rw [hpair]
  rfl

def simDeliverForgeFinishC {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, .bool] .bool :=
  .ret (.var (.succ .zero))

@[simp] theorem simDeliverForgeFinishC_eval {ℓ : ℕ} {Pt : Type}
    [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (s : (dfFullT ℓ Pt).denote) (b : Bool) :
    (simDeliverForgeFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).eval
      (.cons s (.cons b .nil)) = pure b :=
  rfl

/-- Assembles `simDeliverForge` as a `CostedReduction` from a step handler on `dfFullT ℓ Pt`,
falling back to `dummyBoolSessionRed` when `¬ (ℓ < 10 ^ 6)`. -/
def simDeliverForgeProgOfStep {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt))) :
    CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
  if _hℓ : ℓ < 10 ^ 6 then
    { σ := dfFullT ℓ Pt
      init := simDeliverForgeInitC C K Dh encPt encT decT lam
      handle := step
      finish := simDeliverForgeFinishC C K Dh encPt encT decT lam }
  else
    dummyBoolSessionRed (fig8SmIfaceDF ℓ Pt) .unit

/-- Game-loop `.eval` bridge from `simDeliverForgeProgOfStep` to `simDeliverForgeClampSan`. -/
theorem simDeliverForgeProgOfStep_eval_san {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep B T Kc Bsk : ℕ) (hℓ : ℓ < 10 ^ 6)
    (Extra : LibsignalToModularSchemeSimState Bytes Pt ℓ → Prop)
    (hExtra_init : ∀ pqrKey : BitVec 256,
      Extra (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
        ((paramsV1 C K idA idB).spqr.init .b2a pqrKey)))
    (hExtra_step : ∀ t (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)),
      Extra s.1 →
      ∀ x ∈ support ((simDeliverForgeOracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep B T Kc Bsk (.inr t)).run s), Extra x.2.1)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (dfFullT ℓ Pt).denote),
      SimCStateBounded L (dfFullDec s_raw).1 →
      (dfFullDec s_raw).2.length ≤ L →
      Extra (dfFullDec s_raw).1 →
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSan (paramsV1 C K idA idB) Dh encPt encT decT lam qep B T Kc Bsk
        (.inr t)).run (dfFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (q : ℕ) (hq : CryptoGames.SM.MakesAtMostQueries A q) (hqL : q ≤ L) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) () =
      simDeliverForgeClampSan (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep B T Kc Bsk A := by
  have hq' := (CryptoGames.Ratchet.LibsignalSim.makesAtMostQueries_iff_isGameQuery A q).mp hq
  let P := paramsV1 C K idA idB
  unfold simDeliverForgeProgOfStep
  simp only [hℓ, ↓reduceDIte]
  set prog : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool .bool :=
    { σ := dfFullT ℓ Pt
      init := simDeliverForgeInitC C K Dh encPt encT decT lam
      handle := step
      finish := simDeliverForgeFinishC C K Dh encPt encT decT lam }
  have hinit_eval :
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        prog.init.eval (.cons () .nil)) =
      (do
        let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
            (BitVec 256))
        return ((), (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), []))) := by
    dsimp only [prog]
    rw [simDeliverForgeInitC_eval, Functor.map_map]
    unfold simDeliverForgeInitImpl
    rw [map_bind]
    refine bind_congr fun pqrKey => ?_
    rw [map_pure]
    dsimp only [Function.comp_def, Prod.map, id_eq]
    rw [dfFullDec_dfFullEnc]
    rfl
  have hinit_inv :
      ∀ r ∈ support (prog.init.eval (.cons () .nil)),
        DFStateInv L q (dfFullDec (ℓ := ℓ) (Pt := Pt) r.2) ∧
          Extra (dfFullDec (ℓ := ℓ) (Pt := Pt) r.2).1 := by
    rintro ⟨u₀, s_raw⟩ hr
    dsimp only [prog] at hr
    rw [simDeliverForgeInitC_eval, support_map, Set.mem_image] at hr
    obtain ⟨⟨_, s₀⟩, hs, hEq₀⟩ := hr
    dsimp only [Prod.map, id_eq] at hEq₀
    injection hEq₀ with _ hs_raw
    rw [← hs_raw, dfFullDec_dfFullEnc]
    unfold simDeliverForgeInitImpl at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨pqrKey, -, hs⟩ := hs
    rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hs
    rcases hs with ⟨_, rfl⟩
    exact ⟨dfStateInv_initSimC hqL _ _, hExtra_init pqrKey⟩
  have habs := prog.eval_eq_simulateQ_of_abs
    (dfFullDec (ℓ := ℓ) (Pt := Pt))
    (fun m s_raw => DFStateInv L m (dfFullDec (ℓ := ℓ) (Pt := Pt) s_raw) ∧
      Extra (dfFullDec (ℓ := ℓ) (Pt := Pt) s_raw).1)
    (fun _ => do
      let pqrKey ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        AdversaryCompDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)
          (BitVec 256))
      return ((), (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), [])))
    (simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk)
    (fun _ b => pure b)
    q ()
    hinit_eval
    hinit_inv
    (fun _ _ => rfl)
    (fun m t s_raw hInv => by
      have hbnd := hInv.1.toBounded
      have heq := hstep t s_raw hbnd.1 hbnd.2 hInv.2
      refine ⟨heq, ?_⟩
      rintro ⟨rr, s_raw'⟩ hmem
      have hmem' : (rr, dfFullDec s_raw') ∈
          support ((simDeliverForgeOracleSan P Dh encPt encT decT lam qep B T Kc Bsk (.inr t)).run
            (dfFullDec s_raw)) := by
        rw [← heq, support_map, Set.mem_image]
        exact ⟨(rr, s_raw'), hmem, rfl⟩
      exact ⟨simDeliverForgeOracleSan_preserves_dfStateInv P Dh encPt encT decT lam
          L m qep B T Kc Bsk t (dfFullDec s_raw) hInv.1 (rr, dfFullDec s_raw') hmem',
        hExtra_step t (dfFullDec s_raw) hInv.2 (rr, dfFullDec s_raw') hmem'⟩)
    (fun _ _ _ => rfl)
    (fun _ hle hInv => ⟨hInv.1.mono hle, hInv.2⟩)
    (fun _ => A)
    (fun _ => hq')
  rw [habs]
  dsimp only [simDeliverForgeClampSan, P]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pqrKey => ?_
  rw [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]

theorem simDeliverForgeProgOfStep_eval_sanQ {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt]
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (hℓ : ℓ < 10 ^ 6)
    (Extra : LibsignalToModularSchemeSimState Bytes Pt ℓ → Prop)
    (hExtra_init : ∀ pqrKey : BitVec 256,
      Extra (initSimC ((paramsV1 C K idA idB).spqr.init .a2b pqrKey)
        ((paramsV1 C K idA idB).spqr.init .b2a pqrKey)))
    (hExtra_step : ∀ t (s : LibsignalToModularSchemeSimState Bytes Pt ℓ × List (Fig8C Pt)),
      Extra s.1 →
      ∀ x ∈ support ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam
          qep q (.inr t)).run s), Extra x.2.1)
    (step : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIfaceDF ℓ Pt)
      [dfFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (dfFullT ℓ Pt)))
    (hstep : ∀ t (s_raw : (dfFullT ℓ Pt).denote),
      SimCStateBounded q (dfFullDec s_raw).1 →
      (dfFullDec s_raw).2.length ≤ q →
      Extra (dfFullDec s_raw).1 →
      (Prod.map id (dfFullDec (ℓ := ℓ) (Pt := Pt)) <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) step (.inr t)).run s_raw)) =
      ((simDeliverForgeOracleSanQ (paramsV1 C K idA idB) Dh encPt encT decT lam qep q
        (.inr t)).run (dfFullDec s_raw)))
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : CryptoGames.SM.MakesAtMostQueries A q) :
    (simDeliverForgeProgOfStep C K Dh encPt encT decT lam step).eval (fun _ => A) () =
      simDeliverForgeClampSanQ (paramsV1 C K idA idB) ℓ Dh encPt encT decT lam qep q A :=
  simDeliverForgeProgOfStep_eval_san C K idA idB Dh encPt encT decT lam
    q qep (2 ^ 32) (50000 * q) (25001 * q + 25000) (25000 * q) hℓ
    Extra hExtra_init hExtra_step step hstep A q hq le_rfl

end Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeSanOracle
