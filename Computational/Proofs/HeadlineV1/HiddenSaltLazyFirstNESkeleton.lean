/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECell
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafDeliverProbe
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafTransmit
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeaves1
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Sticky-Dead-Ghost `firstNESimImpl'` Coupling and Cell-Sum Bound

Proves per-query preservation of `FirstNECoupledInvD` across `firstNESimImpl'`, lifts it over
`simulateQ`, and bounds the probe probability by the `admissibleLastLeakGuesses 2` cell sum.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

/-! ## Initialization and per-oracle steps -/

theorem firstNECoupledInvD_init
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (b : Bool) (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
      initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let g₀ := SM.initState fig k b
    let m'₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := { st := fun _ => (), b }
    FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ [] m'₀ g₀ (fun _ _ => g₀) := by
  intro fig sC₀ g₀ m'₀
  refine Or.inr (Or.inr ⟨rfl, rfl, ⟨fun _ _ _ _ => rfl, fun t _ =>
    ⟨pprimePaperRel_init_b fig k b, SM.Thm1L17.wfState_init fig (2 + 1) k b,
      fun tL _ => Or.inr ⟨(pprimePaperRel_init_b fig k b).toShifted,
        SM.Thm1L17.wfState_init fig (cellDelta tL t) k b,
        shiftedLeakRel_init fig (cellShift tL t) k b,
        cellCompRel_init fig tL t k b⟩⟩⟩,
    firstNEInTransOriginInv_init_b fig qep sC₀.snaps k b, ?_⟩)
  have hvR₀ : ∀ Q t, ((g₀.st Q).vR t).isSome ↔ (t ≤ (g₀.st Q).tcur ∧ Q.sendsIn t = false) := by
    intro Q t; cases Q <;> by_cases ht : t = 0 <;>
      simp [g₀, fig, SM.initState, lFig8, scheme, initParty, ht, Party.sendsIn]
  refine ⟨fun _ => ⟨SM.initState (libsignalSessionScheme P ℓ encPt lam).sendPart (k.1, k.2, 0, pqrKey) b,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩⟩,
    mirrorSync_init fig k b,
    SM.Thm1L17.wfState_init fig 3 k b,
    corrsLeEpoch_init_b fig k b,
    fun _ => Nat.zero_le _,
    corrsSnapIdxInv_init_b fig sC₀.snaps k b,
    corrsSnapsInv_init_b fig sC₀.snaps k b,
    ⟨fun Q => by cases Q <;> rfl,
     fun Q hQ => by cases Q with | A => cases hQ | B => exact ⟨k.2, _, rfl, rfl, rfl⟩,
     hvR₀⟩,
    corrsKeptRecvInv_init_b fig sC₀ k b,
    ⟨fun Q st hst => by simp [sC₀, initSimC, Kept.unknown] at hst,
     fun Q t v _ hrs => by simp [sC₀, initSimC, Kept.unknown] at hrs,
     hvR₀⟩,
    fun Q => by cases Q <;> rfl,
    honestSentSync_nil Pt⟩

theorem firstNECoupledInvD_corr_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inr Q)) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inr Q)))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} :=
  firstNECoupledInvD_corr_query_step_aux P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q u sC g tr
    sent m' s_cell hbody horig hsync hih

theorem firstNECoupledInvD_inject_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inr (Q, w)))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inr (Q, w)))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} :=
  firstNECoupledInvD_inject_query_step_aux P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u sC g
    tr sent m' s_cell hbody horig hsync hih

theorem firstNECoupledInvD_transmit_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} :=
  firstNECoupledInvD_transmit_query_step_aux P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q m₀ r u
    sC g tr sent m' s_cell hbody horig hsync hih

theorem firstNECoupledInvD_chall_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>=
          u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>=
            u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  rcases hbody with ⟨hcol, hrel_all⟩
  have hcoupled₀ :
      FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig, hsync⟩)
  rcases hsync with ⟨hmeta_opt, hmsync, hwf_g, hcorrs_le, hep_le_qep, hsnap_idx, hcorrs_snaps,
    hsender_sync, hkept_corr, hkept, hid_st, hhon_sent⟩
  have hsim_chall :
      (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8)))
          (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>= u)).run
        (sC, (g, false, false), tr) =
      ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r).run
        (sC, (g, false), tr) >>=
        fun x =>
          (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
            (u x.1)).run (x.2.1, (x.2.2.1.1, x.2.2.1.2, false), x.2.2.2)) := by
    have hlift : ∀ {β : Type} (m : ProbComp β),
        (StateT.lift m : KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ β).run
          (sC, (g, false, false), tr) =
          (m >>= fun a => pure (a, (sC, (g, false, false), tr))) := fun _ => rfl
    rw [simulateQ_query_bind, StateT.run_bind]
    change ((firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run
        (sC, (g, false, false), tr) >>=
      fun p => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (u p.1)).run p.2) = _
    simp only [firstNESimImpl', kemFailSimImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
    rfl
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [hsim_chall,
      kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
        sC (g, false) tr (Or.inl hg1), pure_bind]
    refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
    refine sum_cellSimRun_le_of_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
      _ (u none) sC sC g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
    rw [cellSimRun_chall_query_bind,
      runCellStep_simSendC_of_guard_fail P qep fig t tL Q m₀ (some m₁) r sC sent m' (s_cell t tL)
        (Or.inl hg1), pure_bind]
  · have hg1_f : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
      Bool.eq_false_iff.mpr hg1
    cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      rw [hsim_chall,
        kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
          sC (g, false) tr (Or.inr (Or.inl hep)), pure_bind]
      refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
      refine sum_cellSimRun_le_of_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
        _ (u none) sC sC g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
      rw [cellSimRun_chall_query_bind,
        runCellStep_simSendC_of_guard_fail P qep fig t tL Q m₀ (some m₁) r sC sent m' (s_cell t tL)
          (Or.inr (Or.inl hep)), pure_bind]
    | some s₁ =>
      by_cases hg3 : ((some m₁).isSome && !s₁.safeCh 3 Q) = true
      · rw [hsim_chall,
          kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
            sC (g, false) tr (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)), pure_bind]
        refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
        refine sum_cellSimRun_le_of_doomed_or_eq P ℓ Dh encPt encT decT idOf lam qep
          _ (u none) sC sC g sent sent m' m' s_cell s_cell fun t _ tL _ => Or.inr ?_
        rw [cellSimRun_chall_query_bind,
          runCellStep_simSendC_of_guard_fail P qep fig t tL Q m₀ (some m₁) r sC sent m'
            (s_cell t tL) (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)), pure_bind]
      · have hg3_f : ((some m₁).isSome && !s₁.safeCh 3 Q) = false := Bool.eq_false_iff.mpr hg3
        have hstop : sC.base.stopped = false := by
          cases h : sC.base.stopped
          · rfl
          · simp [h] at hg1_f
        have hsafe_s₁ : s₁.safeCh 3 Q = true := by
          simpa using hg3_f
        rcases hmeta_opt hstop with ⟨s_R, hmeta⟩
        have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
        rcases hmsync.chall_sync (hrel_all 0 ht0).1 hmeta.hepoch_fig8.symm hmeta.htL_fig8.symm
            hep hsafe_s₁ with
          ⟨g₁, m₁', hep_g, hsafe_g, hep_m, hsafe_m, hb_eq⟩
        have hwin_g : g.win = false := (hrel_all 0 ht0).1.win_mir_false
        rw [hsim_chall,
          kemFailSendStep_run_of_guards_pass P K Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
            s₁ sC g false tr hg1_f hep hg3_f, bind_assoc, bind_assoc]
        simp only [cellSimRun_chall_query_bind,
          runCellStep_simSendC_of_guards_pass P qep
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) _ _ Q m₀ (some m₁) r s₁ sC sent m' _
            hg1_f hep hg3_f, bind_assoc]
        refine evalDist_bind_le_double_sum _ _ _ _ _ fun rq => ?_
        cases hmk : LibsignalSim.mkPub (P := P) sC.base Q rq
            (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
             else sC.base.pn Q) with
        | none =>
          simp only [evalDist_drawRc_bind_const, pure_bind]
          exact hih none sC g false false { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }
            sent m' s_cell hcoupled₀
        | some p_pub =>
          rcases p_pub with ⟨pq', pub⟩
          dsimp only [Option.isSome]
          let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
            else sC.base.pn Q
          rw [kemFailSendStep_chall_mkPub_some P qep fig Q m₀ m₁ r s₁ pq' pub pn sC g tr
            (stepKemFailSend P.C.F K tr Q rq) hwin_g]
          simp only [evalDist_cell_chall_mkPub_some qep _ _
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀ m₁ r s₁ pq' pub _
            sC sent m' m₁' _ hep_m hsafe_m]
          refine evalDist_bind_le_double_sum _ _ _ _ _ fun coins => ?_
          let m_ch := if m'.b then (pub, m₁) else (pub, m₀)
          let c := (fig.send (g₁.st Q) m_ch coins).2
          let st' := (fig.send (g₁.st Q) m_ch coins).1
          let rec_r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
            ⟨⟨Q, g₁.epoch Q, g₁.idx Q + 1⟩, m_ch, c⟩
          let m₂' := m₁'.record (2 + 1) Q () ⟨⟨Q, m₁'.epoch Q, m₁'.idx Q + 1⟩, m_ch, c⟩ true
          let s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
            fun t tL =>
              if (s_cell t tL).win then s_cell t tL
              else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false with
                | some s₂ => s₂.record (cellDelta tL t) Q st' rec_r false
                | none => s_cell t tL
          have hch_g := (challPure_eq_of_pprimePaperRelShifted fig (2 + 1) qep Q (pub, m₀) (pub, m₁)
            coins r.isSome (hrel_all 0 ht0).1.toShifted hep_g hsafe_g hb_eq).1
          rw [hch_g]
          dsimp only
          let sC' := updSimStateCSend fig Q m₀ true s₁ pq' pn c sC
          let g' := g₁.record (2 + 1) Q st' rec_r true
          have hinv₁ : FirstNECellFamilyInvT qep false g' m₂' s_cell₁ := by
            refine Eq.ndrec (motive := fun f => FirstNECellFamilyInvT qep false g' m₂' f)
              (firstNECellFamilyInvT_chall_step (m₁' := m₂') fig qep Q m_ch coins r.isSome
                (Or.inr ⟨rfl, hcol, hrel_all⟩) hep_g hsafe_g) ?_
            funext t tL
            dsimp only [s_cell₁, st', rec_r, c]
            cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;> rfl
          have hcoupled₁ :
              FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC' (c :: sent) m₂' g'
                s_cell₁ := by
            rcases hinv₁ with hwin | ⟨_, hcol₁, hrel_all₁⟩
            · exact Or.inl hwin
            · have horig₁ : FirstNEInTransOriginInv qep sC'.snaps g' s_cell₁ :=
                firstNEInTransOriginInv_send_step_of_cellFamily qep sC.snaps Q r.isSome true st'
                  m_ch c horig hrel_all hep_g hcorrs_le hsnap_idx
              have hst_corrs_g₁ : g₁.st = g.st ∧ g₁.corrs = g.corrs := by
                unfold SM.GameState.epMgmt at hep_g
                split_ifs at hep_g <;> { injection hep_g with h; subst h; exact ⟨rfl, rfl⟩ }
              have hst_g₁ : g₁.st = g.st := hst_corrs_g₁.1
              have hcorrs_g₁ : g₁.corrs = g.corrs := hst_corrs_g₁.2
              obtain ⟨s_R₁, g₁', _, hep_g', _, _, hmeta₁⟩ := hmeta.epMgmt_some Q qep r.isSome hep
              have hg₁_eq : g₁' = g₁ := Option.some.inj (hep_g'.symm.trans hep_g)
              subst g₁'
              have hmeta' : SameMeta
                  (s_R₁.record 3 Q (s_R₁.st Q)
                    ⟨⟨Q, s_R₁.epoch Q, s_R₁.idx Q + 1⟩, m₀, LibsignalSim.toWire c⟩ true)
                  sC'.base g' := by
                simpa [sC', g', updSimStateCSend, hstop] using
                  hmeta₁.record_preserves Q (s_R₁.st Q) st' m₀ m₀ m_ch c true
                    (Function.update sC.base.pq Q pq') (Function.update sC.base.pn Q pn)
                    sC.base.unackA ((LibsignalSim.toWire c, c) :: sC.base.honest)
                    sC.base.chains sC.base.amb
              obtain ⟨s_unsh₁, hep_u, _⟩ :=
                (hrel_all 0 ht0).1.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
              obtain ⟨m₁'', hep_m', hmsync₁⟩ :=
                hmsync.epMgmt_step (hrel_all 0 ht0).1.epoch_eq hep_g hep_u
              have hm₁_eq : m₁'' = m₁' := Option.some.inj (hep_m'.symm.trans hep_m)
              subst m₁''
              have hs_cell₁_0 : s_cell₁ 0 none = s_unsh₁.record (2 + 1) Q st' rec_r false := by
                have hdelta0 : cellDelta none 0 = 2 + 1 := by simp [cellDelta]
                dsimp only [s_cell₁]
                simp only [(hrel_all 0 ht0).1.win_df_false, Bool.false_eq_true, ↓reduceIte,
                  hdelta0, hep_u]
              have hm₂'_eq : m₂' = m₁'.record (2 + 1) Q () rec_r true := by
                dsimp only [m₂', rec_r]
                rw [hmsync₁.epoch_eq, hmsync₁.idx_eq]
              have hmsync' : MirrorSync m₂' g' (s_cell₁ 0 none) := by
                rw [hm₂'_eq, hs_cell₁_0]
                exact hmsync₁.record_step Q st' rec_r true
              obtain ⟨hwf₁, hsends₁⟩ := SM.Thm1L17.epMgmt_wf hwf_g hep_g
              have hwf_g' : SM.Thm1L17.WFState 3 g' :=
                SM.Thm1L17.record_wf (by omega) hwf₁ rfl rfl rfl hsends₁ (fun _ => hsafe_g)
              have hep_le_qep' : ∀ P₀, g'.epoch P₀ ≤ qep + 1 := by
                intro P₀
                change g₁.epoch P₀ ≤ qep + 1
                unfold SM.GameState.epMgmt at hep_g
                by_cases hs : Q.sendsIn (g.epoch Q + 1) = true
                · simp only [hs, ↓reduceIte] at hep_g
                  by_cases hq : qep + 1 < g.epoch Q + 1
                  · simp [hq] at hep_g
                  · simp only [hq, ↓reduceIte] at hep_g
                    split_ifs at hep_g <;>
                      { injection hep_g with h; subst h
                        by_cases hPQ : P₀ = Q
                        · subst hPQ; simp [SM.GameState.leak]; omega
                        · simp [SM.GameState.leak, hPQ, hep_le_qep P₀] }
                · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep_g
                  by_cases hq : qep + 1 < g.epoch Q
                  · simp [hq] at hep_g
                  · simp only [hq, ↓reduceIte, Option.some.injEq] at hep_g
                    subst hep_g; exact hep_le_qep P₀
              have hkept' : KeptInv P Dh encPt encT idOf lam sC' g' :=
                keptInv_send hkept Q (hid_st Q) m_ch coins
                  (by simp [g', SM.GameState.record, st', hst_g₁, fig]) rfl
              have hid_st' : ∀ P₀, (g'.st P₀).id = P₀ := by
                intro P₀
                change (Function.update g₁.st Q st' P₀).id = P₀
                by_cases hPQ : P₀ = Q
                · subst hPQ
                  rw [Function.update_self]
                  dsimp only [st', fig, lFig8, scheme]
                  unfold SM.Construction.send
                  dsimp only
                  rw [hst_g₁]
                  by_cases hs : (g.st P₀).id.sendsIn ((g.st P₀).tcur + 1) = true
                  · simp only [hs, ↓reduceIte]
                    exact hid_st P₀
                  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
                    cases (g.st P₀).vS <;> exact hid_st P₀
                · rw [Function.update_of_ne hPQ, hst_g₁]
                  exact hid_st P₀
              have hsender_sync' : Fig8SenderSync g' := by
                refine ⟨?_, ?_, hkept'.hvR⟩
                · intro P₀
                  change (Function.update g₁.st Q st' P₀).tcur = g₁.epoch P₀
                  by_cases hPQ : P₀ = Q
                  · subst hPQ
                    rw [Function.update_self]
                    dsimp only [st', fig, lFig8, scheme]
                    unfold SM.Construction.send
                    dsimp only
                    rw [hst_g₁, hid_st P₀, hsender_sync.htcur P₀]
                    unfold SM.GameState.epMgmt at hep_g
                    by_cases hs : P₀.sendsIn (g.epoch P₀ + 1) = true
                    · simp only [hs, ↓reduceIte] at hep_g ⊢
                      by_cases hq : qep + 1 < g.epoch P₀ + 1
                      · simp [hq] at hep_g
                      · simp only [hq, ↓reduceIte] at hep_g
                        split_ifs at hep_g <;>
                          { injection hep_g with h; subst h; simp [SM.GameState.leak] }
                    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep_g ⊢
                      by_cases hq : qep + 1 < g.epoch P₀
                      · simp [hq] at hep_g
                      · simp only [hq, ↓reduceIte, Option.some.injEq] at hep_g
                        subst hep_g
                        cases (g.st P₀).vS <;> simp [hsender_sync.htcur P₀]
                  · rw [Function.update_of_ne hPQ, hst_g₁]
                    have hep_eq : g₁.epoch P₀ = g.epoch P₀ := by
                      unfold SM.GameState.epMgmt at hep_g
                      split_ifs at hep_g <;>
                        { injection hep_g with h; subst h
                          simp [SM.GameState.leak, hPQ] }
                    rw [hep_eq]
                    exact hsender_sync.htcur P₀
                · intro P₀ hsend_P₀
                  dsimp only [g', rec_r, SM.GameState.record]
                  by_cases hPQ : P₀ = Q
                  · subst hPQ
                    rw [Function.update_self, Function.update_self]
                    dsimp only [st', fig, lFig8, scheme, lFS]
                    unfold SM.Construction.send
                    dsimp only
                    rw [hst_g₁, hid_st P₀, hsender_sync.htcur P₀]
                    unfold SM.GameState.epMgmt at hep_g
                    by_cases hs : P₀.sendsIn (g.epoch P₀ + 1) = true
                    · simp only [hs, ↓reduceIte] at hep_g ⊢
                      by_cases hq : qep + 1 < g.epoch P₀ + 1
                      · simp [hq] at hep_g
                      · simp only [hq, ↓reduceIte] at hep_g
                        have hidx_z : g₁.idx P₀ = 0 := by
                          split_ifs at hep_g <;>
                            { injection hep_g with h; subst h; simp [SM.GameState.leak] }
                        have hγ_exp : ((dhScheme Dh).send (g.st P₀).γ coins).1 =
                            DDH.State.exp coins := by
                          cases (g.st P₀).γ <;> rfl
                        exact ⟨coins, _, hγ_exp, rfl, by simp [FSAEAD.fromAEADPRG, hidx_z]⟩
                    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep_g ⊢
                      by_cases hq : qep + 1 < g.epoch P₀
                      · simp [hq] at hep_g
                      · simp only [hq, ↓reduceIte, Option.some.injEq] at hep_g
                        subst hep_g
                        rcases hsender_sync.hvS P₀ hsends₁ with ⟨x₀, v₀, hγ₀, hvS₀, hlast₀⟩
                        simp only [hvS₀]
                        exact ⟨x₀, _, hγ₀, rfl, by simp [FSAEAD.fromAEADPRG, hlast₀]⟩
                  · rw [Function.update_of_ne hPQ, Function.update_of_ne hPQ, hst_g₁]
                    have hep_idx_eq : g₁.epoch P₀ = g.epoch P₀ ∧ g₁.idx P₀ = g.idx P₀ := by
                      unfold SM.GameState.epMgmt at hep_g
                      split_ifs at hep_g <;>
                        { injection hep_g with h; subst h
                          simp [SM.GameState.leak, hPQ] }
                    rw [hep_idx_eq.2]
                    exact hsender_sync.hvS P₀ (hep_idx_eq.1 ▸ hsend_P₀)
              have hkept_corr' : CorrsKeptRecvInv sC' g' := by
                intro R e hmem t hle hrecv
                have hmem' : (R, e) ∈ g.corrs := hcorrs_g₁ ▸ hmem
                by_cases hRQ : R = Q
                · subst hRQ
                  simp only [sC', updSimStateCSend, Function.update_self, Kept.send]
                  cases hk : (sC.kept R).full with
                  | none => exact hkept_corr R e hmem' t hle hrecv
                  | some st₀ =>
                    dsimp only
                    split_ifs with hs_next
                    · right
                      have hst₀ : st₀ = g.st R := hkept.hfull R st₀ hk
                      subst hst₀
                      have he_le : e ≤ (g.st R).tcur := by
                        rw [hsender_sync.htcur R]; exact hcorrs_le R e hmem'
                      exact (hsender_sync.hvR R t).mpr ⟨le_trans hle he_le, hrecv⟩
                    · left; rfl
                · simp only [sC', updSimStateCSend, Function.update_of_ne hRQ]
                  exact hkept_corr R e hmem' t hle hrecv
              exact Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol₁, hrel_all₁⟩, horig₁,
                fun _ => ⟨_, hmeta'⟩,
                hmsync',
                hwf_g',
                corrsLeEpoch_record_of_epMgmt st' rec_r true hcorrs_le hep_g hcorrs_g₁,
                hep_le_qep',
                corrsSnapIdxInv_record_of_epMgmt st' rec_r true hsnap_idx hcorrs_le hep_g
                  hcorrs_g₁ (Nat.le_succ (g₁.idx Q)),
                corrsSnapsInv_of_corrs_eq hcorrs_snaps hcorrs_g₁,
                hsender_sync',
                hkept_corr',
                hkept',
                hid_st',
                honestSentSync_cons Pt hhon_sent c⟩)
          refine le_trans
            (hih (some (LibsignalSim.toWire c)) sC' g' false false
              (stepKemFailSend P.C.F K tr Q rq) (c :: sent) m₂' s_cell₁ hcoupled₁) ?_
          refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun tL htL => ?_
          rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
          · dsimp only [s_cell₁]
            simp only [hdoomed.2.2.2, ↓reduceIte]
            have hcorrs_sub : ∀ x ∈ g.corrs, x ∈ g'.corrs := by
              unfold SM.GameState.epMgmt at hep_g
              split_ifs at hep_g <;>
                { injection hep_g with h; subst h; intro x hx; exact hx }
            rw [evalDist_cellSimRun_cellWinPred_eq_zero_of_doomed P ℓ Dh encPt encT decT idOf lam
              qep t tL (u (some (LibsignalSim.toWire c))) sC' (c :: sent) m₂'
              (hdoomed.of_corrs_sub hcorrs_sub)]
            exact zero_le
          · have htr_df := (challPure_eq_of_pprimePaperRelShifted fig (cellDelta tL t) qep Q
              (pub, m₀) (pub, m₁) coins r.isSome hrel_sh hep_g hsafe_g hb_eq).2
            dsimp only [cellChallPost, s_cell₁, sC', m₂', rec_r, c, st', m_ch, pn, fig]
            simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
            rw [htr_df]
            simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
            cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;>
              { dsimp only; exact le_rfl }

theorem firstNECoupledInvD_deliver_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  exact firstNECoupledInvD_deliver_query_step_aux P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT
    decT idOf hid hX hinj hdec lam qep q Q w u sC g tr sent m' s_cell hbody horig hsync hih

/-! ## `simulateQ` induction and cell-sum bound -/

theorem firstNECoupledInvD_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range q_sm →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hinv : FirstNECoupledInvD P Dh encPt encT idOf lam qep fl dead sC sent m' g s_cell)
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range q_sm)
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u u₁) sC₁ sent₁ m₁'
            (s_cell₁ t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true}) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) q_sm >>= u)).run
        (sC, (g, fl, dead), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
          (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
            (BitVec 512) (List (BitVec 8))) q_sm >>= u)
          sC sent m' (s_cell t tL) >>=
        fun z => pure (cellWinPred tL t z.2)] {true} := by
  rcases hinv with hwin | hdead | ⟨hfl, hdead, hbody, horig, hsync⟩
  · exact le_trans MeasureTheory.prob_le_one
      (firstNECellFamilyInv_inl_one_le_sum_cell
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep DeliverForge.sameHdrScheme
        (fun _ _ => (simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
          (((simulateQ (LibsignalSimC.simImplC P encT decT qep
              (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
              (lFS P.C P.codec ℓ encT idOf 25000)
              (deliverForgeHook Pt ℓ) Dh)
            (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
              (BitVec 512) (List (BitVec 8))) q_sm >>= u)).run sC).run sent)).run m')
        s_cell hwin)
  · rw [fl_false_of_dead_support P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) q_sm >>= u)
      sC g fl dead tr hdead]
    exact zero_le
  · subst hfl; subst hdead
    rcases q_sm with n | q_game
    · rw [simulateQ_firstNESimImpl'_inl_query_bind, bind_assoc]
      simp only [cellSimRun_inl_query_bind, bind_assoc]
      refine evalDist_bind_le_double_sum _ _ _ _ _ fun u₁ => ?_
      exact hih u₁ sC g false false tr sent m' s_cell
        (firstNECoupledInvD_unif_step (Or.inr (Or.inr ⟨rfl, rfl, hbody, horig, hsync⟩)))
    · rcases q_game with (((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
      · exact firstNECoupledInvD_transmit_query_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          Q m₀ r u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_chall_query_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          Q m₀ m₁ r u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_deliver_query_step P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt
          encT decT idOf hid hX hinj hdec lam qep q Q w u sC g tr sent m' s_cell hbody horig hsync
          hih
      · exact firstNECoupledInvD_inject_query_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          Q w u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_corr_query_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          Q u sC g tr sent m' s_cell hbody horig hsync hih

theorem firstNECoupledInvD_simulateQ_le_sum {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α) :
    ∀ (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl dead : Bool) (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
      (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl dead sC sent m' g s_cell →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, fl, dead), tr) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
        𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL oa sC sent m' (s_cell t tL) >>=
          fun z => pure (cellWinPred tL t z.2)] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC g fl dead tr sent m' s_cell hinv
    rcases hinv with hwin | ⟨_, hfl⟩ | ⟨hfl, _, _, _, _⟩
    · exact le_trans MeasureTheory.prob_le_one
        (firstNECellFamilyInv_inl_one_le_sum_cell
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep DeliverForge.sameHdrScheme
          (fun _ _ => (simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
            (((simulateQ (LibsignalSimC.simImplC P encT decT qep
                (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
                (lFS P.C P.codec ℓ encT idOf 25000)
                (deliverForgeHook Pt ℓ) Dh) (pure a)).run sC).run sent)).run m')
          s_cell hwin)
    · subst hfl
      simp [simulateQ_pure, StateT.run_pure]
    · subst hfl
      simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    intro sC g fl dead tr sent m' s_cell hinv
    exact firstNECoupledInvD_query_step P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT idOf
      hid hX hinj hdec lam qep q q_sm u sC g fl dead tr sent m' s_cell hinv ih

theorem deliverForge_forgeGuessedAdvantageCellPaper_eq
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) :
    DeliverForge.forgeGuessedAdvantageCellPaper sm qep sameHdr tL t B =
      forgeGuessedAdvantageCellPaper sm qep sameHdr tL t B := by
  unfold DeliverForge.forgeGuessedAdvantageCellPaper forgeGuessedAdvantageCellPaper
  split_ifs with h1 h2
  · unfold DeliverForge.forgeGuessedAdvantageShiftedDir2Paper
      DeliverForge.forgeGameGuessedShiftedDir2Paper
      forgeGuessedAdvantageShiftedDir2Paper forgeGameGuessedShiftedDir2Paper
    simp only [authOKDir2_eq_refinement_authOKDir2]
  · rfl
  · rfl

/-- Bounds the `fl && !cand.isSome = true` probability of `firstNESimImpl'` from initial state by
the double sum of `DeliverForge.forgeGuessedAdvantageCellPaper` over `admissibleLastLeakGuesses 2`. -/
theorem evalDist_simulateQ_firstNESimImpl'_le_sum_cells
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (A : LibsignalSM.LibAdv (List (BitVec 8)) (BitVec 512) ℓ) :
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
      let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let ghd₀ := (SM.initState fig k b, false, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
          (sC₀, ghd₀, tr₀)
      return (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ SM.admissibleLastLeakGuesses 2 t,
      DeliverForge.forgeGuessedAdvantageCellPaper
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (qep + 1) DeliverForge.sameHdrScheme tL t
        (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
          (simDeliverForge P ℓ Dh encPt encT decT idOf lam qep A)) := by
  simp_rw [deliverForge_forgeGuessedAdvantageCellPaper_eq,
    forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForge_eq]
  refine evalDist_bind_le_double_sum _ _ _ _ _ fun b => ?_
  refine evalDist_bind_le_double_sum _ _ _ _ _ fun k => ?_
  refine evalDist_bind_le_double_sum _ _ _ _ _ fun pqrKey => ?_
  exact firstNECoupledInvD_simulateQ_le_sum P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT
    idOf hid hX hinj hdec lam qep q A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b) false false
    (initKemFailTrack P.C.F pqrKey) []
    { st := fun _ => (), b }
    (fun _ _ => SM.initState (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) k b)
    (firstNECoupledInvD_init P ℓ Dh encPt encT idOf lam qep b k pqrKey)

end CryptoVerification.LibsignalSession.HeadlineV1

end
