/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepCorr -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSame -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNew -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Online Tracker-Halted Figure 8 Reduction

Defines the `KemFailTrackState`-halted Figure 8 simulator `libsignalToModularSchemeSimHalted`, its
sanitized clamped intermediate `simFig8ClampSanHalted`, and the promoted `CostedReduction`
`simFig8RedProgHalted` over `atomicSessionOps`, together with `GRedBounded` bounds.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Ops Iface Expr Comp CostedReduction
  bits reductionSizeBudget atomicSig atomicSessionOps fig8SmIface
  coinOnlyIface GhostStT smQT smRT B U32 BV256 BV512 PlainT lpubT
  UniformSamplerTag AtomicPureOp fig8CtT)
open CryptoGames (Party SMScheme FSAEADScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM.Construction (Header)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open CryptoGames.SM (Record RecvResult noBobSendInEpoch0 orE isSomeE pGet)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lFig8 lFS)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C Fig8Comp SimState mkPub toWire)
open CryptoGames.Ratchet.LibsignalSimC (Kept LibsignalToModularSchemeSimState Hook
  idHook guardC initSimC simRecvC simCorrC)
open CryptoGames.LibsignalSession (Params Crypto IdentityKey PublicKey GhostState)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack stepKemFailSend stepKemFailDeliver)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (GRedBounded ratchetCostBudget ratchetCostBudget_pos)
open CryptoVerification.E2E (Bytes)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
  (atomicSamplers_sizeHonest atomicSessionOps_sizeHonest)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_mul_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInit
  (kemTrackT initSimCAtomicE initKemTrackAtomicE)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedInitCost
  (initSimCAtomicE_cost initKemTrackAtomicE_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrSub
  (trE_cand stepKemFailSendAtomicC)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedSendCorrCost
  (stepKemFailSendAtomicC_cost)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness
  (findRevHonestIdxE findRevHonestIdxE_cost findRevHonestIdxE_descBits_le
   kemOnDeliverPostAtomicE kemOnDeliverPostAtomicE_cost kemOnDeliverPostAtomicE_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SanOracle (simFig8OracleSan)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (SimFig8RedProg simMirT simFullT)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSessionOpDescBits atomicCompDescBits atomicExprDescBits
   bits_two_mul_add_two_le_ratchetCostBudget)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet sOpPure sOpSpqr cost_eLet cost_sOpPure mWin mEpoch mIdx mSafeChE mEpMgmtE mNoBobEpoch0E
   cost_mNoBobEpoch0E cost_mEpMgmtE cost_mSafeChE
   mNoBobEpoch0E_descBits_le mEpMgmtE_descBits_le mSafeChE_descBits_le
   ssMir ssPn ssStopped ssHonest scBase)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
  (mkPubAtomicC mkPubAtomicC_queries mkPubAtomicC_cost mkPubAtomicC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepSend
  (simSendQueryC simSendQueryC_queries simSendQueryC_cost simSendQueryC_descBits_le
   scPostSendAtomicE scPostSendAtomicE_cost scPostSendAtomicE_descBits_le unpackSendQE)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepCorr
  (simFig8StepCorrC simFig8StepCorrC_queries simFig8StepCorrC_cost simFig8StepCorrC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvSame
  (simFig8FwdHookSpec simFig8RecvSameSpec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNewCost
  (recvOutT recvHookInpT wkTop1Comp callSub1C recvHookOfBranchesC
   recvHookOfBranchesC_queries recvHookOfBranchesC_cost recvHookOfBranchesC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8StepRecvNew (simFig8RecvNewSpec_of_fwd)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
  (session_cost_le_ratchetCostBudget
   dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le)

noncomputable section

/-! ## Tracker-halted Figure 8 simulator -/

@[expose] def simSendCTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {M : Type → Type} [Monad M] (P : Params PQ (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (qep : ℕ) (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (H : Hook Pt ℓ M) (Q : Party) (m₀ : Plain ℓ)
    (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) M
      (Option (List (BitVec 8))) := do
  let (sC, tr) ← get
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then return none
  match sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => return none
  | some s₁ =>
    if chal.isSome && !(s₁.safeCh 3 Q) then return none
    let rq ← StateT.lift (H.lift (match r with
      | some rq => pure rq | none => liftM ($ᵗ BitVec 512 : ProbComp (BitVec 512))))
    let tr' := stepKemFailSend P.C.F K tr Q rq
    if tr'.cand.isSome then set (sC, { tr with cand := tr'.cand }); return none
    else
      let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1) else sC.base.pn Q
      let rc : Option (BitVec 256) ← StateT.lift (H.lift (match r with
        | some _ => some <$> liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) | none => pure none))
      match mkPub (P := P) sC.base Q rq pn with
      | none => set (sC, { tr with cand := tr'.cand }); return none
      | some (pq', pub) =>
        let res ← StateT.lift (H.lift (match chal with
          | none => CryptoGames.SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc
          | some m₁ => CryptoGames.SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc))
        match res with
        | none => set (sC, { tr with cand := tr'.cand }); return none
        | some c =>
          let w := toWire c
          let rec' : Record (Plain ℓ) (List (BitVec 8)) := ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
          let base' : SimState PQ Pt ℓ := { sC.base with
            mir := s₁.record 3 Q () rec' chal.isSome, pq := Function.update sC.base.pq Q pq',
            pn := Function.update sC.base.pn Q pn, honest := (w, c) :: sC.base.honest }
          let sent' := match (sC.kept Q).full, base'.honest.head? with
            | some st, some (_, c₀) => if st.id.sendsIn (st.tcur + 1) then sC.sent
              else match st.vS with | some v => (c₀, v) :: sC.sent | none => sC.sent
            | _, _ => sC.sent
          set ({ sC with base := base', kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)),
                         sent := sent' }, tr')
          return some w

@[expose] def simImplCTrackHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {M : Type → Type} [Monad M] (P : Params PQ (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8)))
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) M) :=
  let TrM := StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F) M
  let liftS {α : Type} (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M α) : TrM α := do
    let (sC, tr) ← get; let (a, sC') ← StateT.lift (m.run sC); set (sC', tr); return a
  let c : QueryImpl unifSpec TrM := fun n =>
    StateT.lift (H.lift (liftM (query (spec := unifSpec) n : ProbComp _) : Fig8Comp Pt ℓ _))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option (BitVec 512)) →ₒ Option (List (BitVec 8))) TrM :=
    fun ⟨Q, m, r⟩ => simSendCTrackHalted P K qep fig H Q m none r
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) →ₒ Option (List (BitVec 8))) TrM :=
    fun ⟨Q, m₀, m₁, r⟩ => simSendCTrackHalted P K qep fig H Q m₀ (some m₁) r
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) TrM := fun ⟨Q, w⟩ => do
    let (sC, _) ← get
    let j? := sC.base.honest.reverse.findIdx? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
    let res ← liftS (guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep)
      (fig := fig) (fs := fs) (H := H) Q w true))
    match res, j? with
    | some (.accepted _ _ _), some j => modify fun (sC', tr) => (sC', stepKemFailDeliver P.C.F K tr Q j)
    | _, _ => pure ()
    return res
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ))) TrM := fun ⟨Q, w⟩ =>
    liftS (guardC (simRecvC (P := P) (encT := encT) (decT := decT) (qep := qep) (fig := fig) (fs := fs) (H := H) Q w false))
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) TrM := fun Q =>
    liftS (guardC (simCorrC (P := P) (encT := encT) (H := H) Dh Q))
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

@[expose] def simRunCTrackHaltedWith {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {M : Type → Type} [Monad M] (P : Params PQ (BitVec 512)) (K : MlKem) {ℓ : ℕ}
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) :
    M Bool := do
  let pqrKey ← H.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  (simulateQ (simImplCTrackHalted P K encT decT qep fig fs H Dh) A).run'
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), initKemFailTrack P.C.F pqrKey)

/-- Tracker-halted Figure 8 simulator adversary matching `runLibsignalToModularSchemeSimTrackHalted`. -/
@[expose] def libsignalToModularSchemeSimHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    Fig8Comp Pt ℓ Bool :=
  simRunCTrackHaltedWith P K encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
    (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh A

/-- Win event of `libsignalToModularSchemeSimHalted`. -/
@[expose] def simCNoneWinEventHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, s) ← CryptoGames.SM.run sm 3 (qep + 1) CryptoGames.SM.Config.h1 b
    (libsignalToModularSchemeSimHalted P K ℓ Dh encPt encT decT idOf lam qep A)
  return s.win

/-! ## Sanitized clamped simulator -/

@[expose] def semSendHookHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (st : LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option (BitVec 512)) :
    Fig8Comp Pt ℓ
      (Option Bytes × (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)) :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT
    (fun R => if R == Party.A then P.idA else P.idB) 25000 lam
  (simSendCTrackHalted P K qep fig idHook Q m₀ chal r).run st

@[expose] def simFig8OracleSanHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ : ℕ} (P : Params PQ (BitVec 512)) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
        (Fig8Comp Pt ℓ)) :=
  let TrM := StateT (LibsignalToModularSchemeSimState PQ Pt ℓ × KemFailTrackState P.C.F)
    (Fig8Comp Pt ℓ)
  let baseSan := simFig8OracleSan (PQC := BitVec 512) P Dh encPt encT decT lam qep B T Kc Bsk
  let liftSan {α : Type}
      (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) : TrM α :=
    StateT.mk fun (sC, tr) => (fun (a, sC') => (a, (sC', tr))) <$> m.run sC
  let c : QueryImpl unifSpec TrM := fun n => liftSan (baseSan (.inl n))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option (BitVec 512)) →ₒ Option Bytes) TrM :=
    fun ⟨Q, m, r⟩ => StateT.mk fun st =>
      semSendHookHalted P K Dh encPt encT lam qep st Q m none r
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option (BitVec 512)) →ₒ Option Bytes) TrM :=
    fun ⟨Q, m₀, m₁, r⟩ => StateT.mk fun st =>
      semSendHookHalted P K Dh encPt encT lam qep st Q m₀ (some m₁) r
  let i₃ : QueryImpl ((Party × Bytes) →ₒ Option (RecvResult (Plain ℓ))) TrM :=
    fun ⟨Q, w⟩ => StateT.mk fun (sC, tr) => do
      let j? := sC.base.honest.reverse.findIdx?
        (fun wc => wc.1 == (w : List (BitVec 8)) && Party.senderOf wc.2.1.1 == Q.other)
      let (res, sC') ← (baseSan (.inr (.inl (.inl (.inr (Q, w)))))).run sC
      let tr' := match res, j? with
        | some (.accepted _ _ _), some j => stepKemFailDeliver P.C.F K tr Q j
        | _, _ => tr
      return (res, (sC', tr'))
  let i₄ : QueryImpl ((Party × Bytes) →ₒ Option (RecvResult (Plain ℓ))) TrM :=
    fun q => liftSan (baseSan (.inr (.inl (.inr q))))
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ)) TrM :=
    fun q => liftSan (baseSan (.inr (.inr q)))
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

/-- Sanitized clamped tracker-halted Figure 8 simulator adversary. -/
@[expose] def simFig8ClampSanHalted {PQ Pt : Type} [DecidableEq Pt] [Zero Pt]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B T Kc Bsk : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) Bytes) :
    Fig8Comp Pt ℓ Bool := do
  let pqrKey ← (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  (simulateQ (simFig8OracleSanHalted P K Dh encPt encT decT lam qep B T Kc Bsk) A).run'
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), initKemFailTrack P.C.F pqrKey)

/-! ## Promoted costed reduction -/

section DslProg

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local notation "ASig" => atomicSig ℓ Pt

abbrev simHaltedT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simFullT ℓ Pt) (kemTrackT ℓ Pt)

@[expose] def simFig8HaltedInitC (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [.unit] (.prod .unit (simHaltedT ℓ Pt)) :=
  .bind (Comp.sample (I := fig8SmIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
    (.ret (.pair .unit
      (.pair
        (initSimCAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) .v0)
        (initKemTrackAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) .v0))))

@[expose] def simFig8HaltedFinishC (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simHaltedT ℓ Pt, .bool] .bool :=
  .ret (.var (.succ .zero))

@[expose] def callSub2C {S : Sig} {O' : Ops S} {ι : Type} {T : OracleSpec ι} {I' : Iface S T}
    {Γ : List (Ty S)} {A B_ty R : Ty S}
    (c : Comp O' I' [A, B_ty] R) (aE : Expr O' Γ A) (bE : Expr O' Γ B_ty) : Comp O' I' Γ R :=
  .bind (.ret bE)
    (.bind (.ret (Expr.renameM (fun ⦃_⦄ v => .succ v) aE))
      (Comp.wkTop2 c))

@[expose] def liftCoinToFig8C {O' : Ops ASig} {Γ : List (Ty ASig)} {τ : Ty ASig} :
    Comp O' (coinOnlyIface ℓ Pt) Γ τ → Comp O' (fig8SmIface ℓ Pt) Γ τ
  | .ret e => .ret e
  | .bind c k => .bind (liftCoinToFig8C c) (liftCoinToFig8C k)
  | .ite b ct cf => .ite b (liftCoinToFig8C ct) (liftCoinToFig8C cf)
  | .caseOpt b cn cs => .caseOpt b (liftCoinToFig8C cn) (liftCoinToFig8C cs)
  | .caseSum b cl cr => .caseSum b (liftCoinToFig8C cl) (liftCoinToFig8C cr)
  | .sample s a =>
      Comp.sample (I := fig8SmIface ℓ Pt)
        (show UniformSamplerTag _ from s) a
  | .query g _ => nomatch g
  | .iter n e body => .iter n e (liftCoinToFig8C body)
  | .findM n e body => .findM n e (liftCoinToFig8C body)
  | .anyM n e body => .anyM n e (liftCoinToFig8C body)
  | .mapM n e body => .mapM n e (liftCoinToFig8C body)
  | .consumeFirstM n l body mk => .consumeFirstM n l (liftCoinToFig8C body) mk
  | .foldM n l z body => .foldM n l z (liftCoinToFig8C body)

@[expose] def stepKemFailSendFig8C {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (kemTrackT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (rqE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ BV512) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt) Γ
      (.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)) :=
  liftCoinToFig8C
    (stepKemFailSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q trE qBE rqE)

abbrev haltedSendInpT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (simHaltedT ℓ Pt) (.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))))

@[expose] def simFig8HaltedSendHookC {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (idA idB : IdentityKey) (qep q : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (simHaltedT ℓ Pt))
    (qBE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ .bool)
    (m0E : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ PlainT)
    (chalE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt PlainT))
    (rE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt BV512)) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt) Γ
      (.prod (.opt (B 32)) (simHaltedT ℓ Pt)) :=
  let AOps := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
  .bind (.ret (.pair stE (.pair qBE (.pair m0E (.pair chalE rE)))))
    (let st0  : Expr AOps _ (simHaltedT ℓ Pt) := .fst .v0
     let s0   : Expr AOps _ (simFullT ℓ Pt) := .fst st0
     let b0   := scBase s0
     let mir0 := ssMir b0
     let q0   : Expr AOps _ .bool := .fst (.snd .v0)
     let r0   : Expr AOps _ (.opt BV512) := .snd (.snd (.snd (.snd .v0)))
     .ite (orE (orE (ssStopped b0) (mWin mir0)) (.not (mNoBobEpoch0E mir0 q0)))
       (.ret (.pair .none st0))
       (.caseOpt (mEpMgmtE qep mir0 q0 (isSomeE r0))
         (.ret (.pair .none st0))
         (.ite (.and (isSomeE (.fst (.snd (.snd (.snd .v1)))))
             (.not (mSafeChE .v0 (.fst (.snd .v1)))))
           (.ret (.pair .none (.fst .v1)))
           (.bind
             (.caseOpt (.snd (.snd (.snd (.snd .v1))))
               (Comp.sample (I := fig8SmIface ℓ Pt) (UniformSamplerTag.base .bv512) .unit)
               (.ret .v0))
             (.bind
               (stepKemFailSendFig8C (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                 (encT := encT) (decT := decT) (lam := lam)
                 q (.snd (.fst .v2)) (.fst (.snd .v2)) .v0)
               (.ite (isSomeE (trE_cand (.fst .v0)))
                 (.ret (.pair .none (.pair (.fst (.fst .v3)) (.snd .v0))))
                 (.bind
                   (.caseOpt (.snd (.snd (.snd (.snd .v3))))
                     (.ret .none)
                     (.bind (Comp.sample (I := fig8SmIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
                       (.ret (.some .v0))))
                   (let v4 : Expr AOps _ (haltedSendInpT ℓ Pt) :=
                      .var (.succ (.succ (.succ (.succ .zero))))
                    .bind (.ret
                        (let b4   := scBase (.fst (.fst v4))
                         let mir4 := ssMir b4
                         let q4   : Expr AOps _ .bool := .fst (.snd v4)
                         Expr.ite (.not (.eqN (pGet (mEpoch .v3) q4) (pGet (mEpoch mir4) q4)))
                           (sOpPure .u32OfNat (.sub (pGet (mIdx mir4) q4) (.nat 1)))
                           (pGet (ssPn b4) q4)))
                      (let v5 : Expr AOps _ (haltedSendInpT ℓ Pt) :=
                         .var (.succ (.succ (.succ (.succ (.succ .zero)))))
                       .bind
                         (mkPubAtomicC (fig8SmIface ℓ Pt) idA idB
                           (scBase (.fst (.fst v5))) (.fst (.snd v5)) .v3 .v0)
                         (let v6 : Expr AOps _ (haltedSendInpT ℓ Pt) :=
                            .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
                          .caseOpt .v0
                            (.ret (.pair .none (.pair (.fst (.fst v6)) (.snd .v3))))
                            (let v7 : Expr AOps _ (haltedSendInpT ℓ Pt) :=
                               .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
                             .bind
                               (simSendQueryC (.fst (.snd v7)) (.snd .v0)
                                 (.fst (.snd (.snd v7))) (.fst (.snd (.snd (.snd v7)))) .v3)
                               (let v5_tr : Expr AOps _ (.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)) :=
                                  .var (.succ (.succ (.succ (.succ (.succ .zero)))))
                                let v8 : Expr AOps _ (haltedSendInpT ℓ Pt) :=
                                  .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
                                .caseOpt .v0
                                  (.ret (.pair .none (.pair (.fst (.fst v8)) (.snd v5_tr))))
                                  (let v4_pn : Expr AOps _ U32 :=
                                     .var (.succ (.succ (.succ (.succ .zero))))
                                   let v8_s1 : Expr AOps _ (simMirT ℓ Pt) :=
                                     .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
                                   let v9 : Expr AOps _ (haltedSendInpT ℓ Pt) :=
                                     .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                                   .ret (eLet
                                     (scPostSendAtomicE idA idB (.fst (.fst v9)) v8_s1
                                       (.fst (.snd v9)) (.fst (.snd (.snd v9)))
                                       (isSomeE (.fst (.snd (.snd (.snd v9)))))
                                       (.fst .v2) v4_pn .v0)
                                     (.pair (.some (.fst .v0))
                                       (.pair (.snd .v0)
                                         (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))))))))))))

@[expose] def simFig8HaltedStepSendC {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (idA idB : IdentityKey) (qep q : ℕ) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simHaltedT ℓ Pt)) :=
  .caseOpt (unpackSendQE .v1)
    (.ret (.pair (.pair .none (.pair .none .none)) .v0))
    (.bind (simFig8HaltedSendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB qep q
        .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))))
      (.ret (.pair (.pair (.fst .v0) (.pair .none .none)) (.snd .v0))))

@[expose] def extractHaltedRecvOptE {O' : Ops ASig} :
    Expr O' [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.opt (.prod .bool (.prod (B 32) .bool))) :=
  .caseSum (.var (.succ .zero))
    .none
    (.caseSum .v0
      .none
      (.caseSum .v0
        (.some (.pair (.fst .v0) (.pair (.snd .v0) (.bool true))))
        (.caseSum .v0
          (.some (.pair (.fst .v0) (.pair (.snd .v0) (.bool false))))
          .none)))

@[expose] def isHaltedSendOrChallE {O' : Ops ASig} :
    Expr O' [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)] .bool :=
  .caseSum (.var (.succ .zero))
    (.bool true)
    (.caseSum .v0 (.bool true) (.bool false))

@[expose] def simHaltedStepDispatchC {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (q : ℕ)
    (cSend : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) I'
      [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simHaltedT ℓ Pt)))
    (cCorr : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) I'
      [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) I'
      [recvHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) I'
      [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simHaltedT ℓ Pt)) :=
  .caseOpt (extractHaltedRecvOptE (ℓ := ℓ) (Pt := Pt))
    (.ite (isHaltedSendOrChallE (ℓ := ℓ) (Pt := Pt))
      cSend
      (.bind (callSub2C cCorr (.fst .v0) .v1)
        (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v1))))))
    (.bind
      (.ret
        (.ite (.snd (.snd .v0))
          (findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            q (ssHonest (scBase (.fst .v1))) (.fst .v0) (.fst (.snd .v0)))
          .none))
      (.bind (callSub1C cRecv (.pair (.fst .v2) .v1))
        (.ret
          (.pair
            (.pair .none (.pair (.fst .v0) .none))
            (.pair (.snd .v0)
              (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam)
                q (.fst .v2) .v1 (.fst .v0) (.snd .v3)))))))

@[expose] def simFig8HaltedRawStepC (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (fig8SmIface ℓ Pt)
      [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simHaltedT ℓ Pt)) :=
  let cSend := simFig8HaltedStepSendC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q
  let corrC := simFig8StepCorrC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB q
  let fwdSpec := simFig8FwdHookSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let sameSpec := simFig8RecvSameSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let newSpec := simFig8RecvNewSpec_of_fwd C K Dh encPt encT decT lam
    idA idB qep q fwdSpec.comp fwdSpec.hq fwdSpec.hcost fwdSpec.hdesc fwdSpec.heval
  let recvHookC := recvHookOfBranchesC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB q sameSpec.comp newSpec.comp
  simHaltedStepDispatchC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q cSend corrC recvHookC

@[expose] def simFig8RedProgHaltedReal (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimFig8RedProg Pt ℓ C K Dh encPt encT decT lam where
  σ := simHaltedT ℓ Pt
  init := simFig8HaltedInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
  handle := simFig8HaltedRawStepC (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  finish := simFig8HaltedFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam

/-- Promoted `CostedReduction` for `libsignalToModularSchemeSimHalted`, guarded by `ℓ < 10 ^ 6`. -/
@[expose] def simFig8RedProgHalted (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) :
    SimFig8RedProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 then
    simFig8RedProgHaltedReal (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  else
    dummyBoolSessionRed (fig8SmIface ℓ Pt) .unit

end DslProg

/-! ## `GRedBounded` bounds -/

section CostAndSize

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
variable {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ADesc" => atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
  (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)

@[local simp] private theorem expr_renameM_size {S : Sig} {O' : Ops S} {Γ₁ Γ₂ : List (Ty S)}
    {t : Ty S} (f : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u) (e : Expr O' Γ₁ t) :
    (Expr.renameM f e).size = e.size := by
  induction e generalizing Γ₂ <;> simp [Expr.renameM, Expr.size, *]

private theorem comp_renameM_size {S : Sig} {O' : Ops S} {ι : Type} {T : OracleSpec ι}
    {I' : Iface S T} {Γ₁ Γ₂ : List (Ty S)} {t : Ty S}
    (f : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u) (c : Comp O' I' Γ₁ t) :
    (Comp.renameM f c).size = c.size := by
  induction c generalizing Γ₂ <;> simp [Comp.renameM, Comp.size, *]

private theorem callSub1C_size {S : Sig} {O' : Ops S} {ι : Type} {T : OracleSpec ι}
    {I' : Iface S T} {Γ : List (Ty S)} {a t : Ty S}
    (c : Comp O' I' [a] t) (argE : Expr O' Γ a) :
    (callSub1C c argE).size = argE.size + c.size + 2 := by
  simp only [callSub1C, wkTop1Comp, Comp.size, comp_renameM_size]; omega

private theorem callSub2C_queries {S : Sig} {O' : Ops S} {ι : Type} {T : OracleSpec ι}
    {I' : Iface S T} {Γ : List (Ty S)} {A B_ty R : Ty S}
    (c : Comp O' I' [A, B_ty] R) (aE : Expr O' Γ A) (bE : Expr O' Γ B_ty)
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (callSub2C c aE bE).queries w ws = c.queries w ws := by
  simp [callSub2C, Comp.wkTop2, Comp.queries, Comp.renameM_queries]

private theorem callSub2C_cost {S : Sig} {O' : Ops S} {ι : Type} {T : OracleSpec ι}
    {I' : Iface S T} {Γ : List (Ty S)} {A B_ty R : Ty S}
    (c : Comp O' I' [A, B_ty] R) (aE : Expr O' Γ A) (bE : Expr O' Γ B_ty) :
    (callSub2C c aE bE).cost = bE.cost + aE.cost + c.cost + 4 := by
  simp only [callSub2C, Comp.wkTop2, Comp.cost, Comp.renameM_cost, Expr.renameM_cost]; omega

private theorem callSub2C_size {S : Sig} {O' : Ops S} {ι : Type} {T : OracleSpec ι}
    {I' : Iface S T} {Γ : List (Ty S)} {A B_ty R : Ty S}
    (c : Comp O' I' [A, B_ty] R) (aE : Expr O' Γ A) (bE : Expr O' Γ B_ty) :
    (callSub2C c aE bE).size = bE.size + aE.size + c.size + 4 := by
  simp only [callSub2C, Comp.wkTop2, Comp.size, comp_renameM_size, expr_renameM_size]; omega

omit [DecidableEq Pt] [Zero Pt] in
private theorem liftCoinToFig8C_queries {O' : Ops ASig} {Γ : List (Ty ASig)} {τ : Ty ASig}
    (c : Comp O' (coinOnlyIface ℓ Pt) Γ τ) (w : (fig8SmIface ℓ Pt).Tag → ℕ) :
    (liftCoinToFig8C c).queries w (fun _ => 0) = 0 := by
  induction c with | query g _ => nomatch g | _ => simp [liftCoinToFig8C, Comp.queries, *]

omit [DecidableEq Pt] [Zero Pt] in
private theorem liftCoinToFig8C_cost {O' : Ops ASig} {Γ : List (Ty ASig)} {τ : Ty ASig}
    (c : Comp O' (coinOnlyIface ℓ Pt) Γ τ) : (liftCoinToFig8C c).cost = c.cost := by
  induction c with
  | query g _ => nomatch g | sample _ _ => rfl | _ => simp [liftCoinToFig8C, Comp.cost, *]

omit [DecidableEq Pt] [Zero Pt] in
private theorem liftCoinToFig8C_size {O' : Ops ASig} {Γ : List (Ty ASig)} {τ : Ty ASig}
    (c : Comp O' (coinOnlyIface ℓ Pt) Γ τ) : (liftCoinToFig8C c).size = c.size := by
  induction c with | query g _ => nomatch g | _ => simp [liftCoinToFig8C, Comp.size, *]

omit [SampleableType Pt] in
private theorem atomicSessionOps_opSize_le_local (o : (AOps).Op) :
    (AOps).opSize o ≤ ADesc o := by
  rcases o with (((o | (_ | _)) | _) | (_ | _)) | _
  · cases o <;>
      dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
        _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
        Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize,
        atomicSessionOpDescBits,
        Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicPureOpDescBits] <;>
      omega
  · change 0 ≤ 8 + 5; omega
  · change 0 ≤ Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.atomicSymOpDescBits _ + 5; omega
  · change 0 ≤ 8 + 3; omega
  · change 0 ≤ 8 + 3; omega
  · change 0 ≤ 8 + 3; omega
  · change 0 ≤ 8 + 1; omega

omit [SampleableType Pt] in
private theorem expr_size_le_descBits (opB : (AOps).Op → ℕ)
    {Γ : List (Ty ASig)} {t : Ty ASig} (e : Expr AOps Γ t)
    (hop : ∀ o, (AOps).opSize o ≤ opB o := by intro o; exact atomicSessionOps_opSize_le_local o) :
    e.size ≤ atomicExprDescBits opB e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [Expr.size, atomicExprDescBits]; omega
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | tget _ _ ha hb
  | appendL _ _ _ ha hb | findB _ _ _ ha hb | anyB _ _ _ ha hb | mapB _ _ _ ha hb
  | letE _ _ ha hb =>
    simp only [Expr.size, atomicExprDescBits]; omega
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha =>
    simp only [Expr.size, atomicExprDescBits]; omega
  | ite _ _ _ hc ha hb | tset _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb
  | caseSum _ _ _ hc ha hb | foldrB _ _ _ _ hc ha hb =>
    simp only [Expr.size, atomicExprDescBits]; omega
  | op o _ ha =>
    have ho := hop o
    simp only [Expr.size, atomicExprDescBits]; omega

omit [SampleableType Pt] in
private theorem comp_size_le_descBits {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (opB : (AOps).Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty ASig)} {t : Ty ASig} (c : Comp AOps I' Γ t)
    (hop : ∀ o, (AOps).opSize o ≤ opB o := by intro o; exact atomicSessionOps_opSize_le_local o) :
    c.size ≤ atomicCompDescBits opB sB qB c := by
  induction c with
  | ret e =>
    have he := expr_size_le_descBits opB e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | bind _ _ _ _ =>
    simp only [Comp.size, atomicCompDescBits]; omega
  | ite b _ _ _ _ =>
    have hb := expr_size_le_descBits opB b hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | caseOpt e _ _ _ _ | caseSum e _ _ _ _ | sample _ e | query _ e | iter _ e _ _ =>
    have he := expr_size_le_descBits opB e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | findM _ l _ _ | anyM _ l _ _ | mapM _ l _ _ =>
    have hl := expr_size_le_descBits opB l hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | consumeFirstM _ l _ mk _ =>
    have hl := expr_size_le_descBits opB l hop
    have hmk := expr_size_le_descBits opB mk hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | foldM _ l z _ _ =>
    have hl := expr_size_le_descBits opB l hop
    have hz := expr_size_le_descBits opB z hop
    simp only [Comp.size, atomicCompDescBits]; omega

private theorem simFig8HaltedInitC_queries :
    (simFig8HaltedInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).queries
      (fun _ => 1) (fun _ => 0) = 0 := rfl

private theorem simFig8HaltedInitC_cost_le :
    (simFig8HaltedInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 4100 := by
  let Γ0 : List (Ty ASig) := [BV256, .unit]
  have h1 := initSimCAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) .v0
  have h2 := initKemTrackAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ0) .v0
  dsimp only [simFig8HaltedInitC, _root_.ReductionDsl.AtomicUnifBase.sort, Γ0] at h1 h2 ⊢
  generalize initSimCAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = e1 at h1 ⊢
  generalize initKemTrackAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) _ = e2 at h2 ⊢
  dsimp only [Comp.sample, fig8SmIface, _root_.ReductionDsl.atomicSamplers,
    _root_.ReductionDsl.unifSamplers, _root_.ReductionDsl.AtomicUnifBase.cost,
    Expr.v0, Comp.cost, Expr.cost] at h1 h2 ⊢
  omega

private theorem simFig8HaltedInitC_size_le :
    (simFig8HaltedInitC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 500 := by
  have hb0 : bits 0 = 1 := rfl
  dsimp only [simFig8HaltedInitC, Comp.sample, initSimCAtomicE, initKemTrackAtomicE,
    KemFailRedInit.initV1BraidStAtomicE, SimFig8LoopAndCost.initSimCE,
    SimFig8LoopAndCost.initSimMirE, SimFig8LoopAndCost.keptUnknownE,
    AtomicSessionBridge.sessPureOp, AtomicSessionBridge.sessSpqrKemOp,
    eLet, Expr.v0, Comp.size, Expr.size,
    atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize, List.length_cons, List.length_nil]
  omega

private theorem simFig8HaltedFinishC_queries :
    (simFig8HaltedFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).queries
      (fun _ => 1) (fun _ => 0) = 0 := rfl

private theorem simFig8HaltedFinishC_cost_le :
    (simFig8HaltedFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).cost ≤ 4 := by
  dsimp only [simFig8HaltedFinishC, Comp.cost, Expr.cost]; omega

private theorem simFig8HaltedFinishC_size_le :
    (simFig8HaltedFinishC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam).size ≤ 10 := by
  dsimp only [simFig8HaltedFinishC, Comp.size, Expr.size]; omega

private theorem stepKemFailSendFig8C_queries (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendFig8C q trE qBE rqE).queries (fun _ => 1) (fun _ => 0) = 0 :=
  liftCoinToFig8C_queries _ _

private theorem stepKemFailSendFig8C_cost (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendFig8C q trE qBE rqE).cost ≤
      trE.cost + qBE.cost + rqE.cost + 4 * q + 15100000 := by
  unfold stepKemFailSendFig8C; rw [liftCoinToFig8C_cost]
  exact stepKemFailSendAtomicC_cost q trE qBE rqE

private theorem stepKemFailSendFig8C_size_le (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendFig8C q trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + bits (q + 1) + 1000 := by
  unfold stepKemFailSendFig8C; rw [liftCoinToFig8C_size]
  have hb1 : bits 1 = 1 := rfl; have hb2 : bits 2 = 2 := rfl
  have hb256 : bits 256 = 9 := rfl; have hb1024 : bits 1024 = 11 := rfl
  have hb1536 : bits 1536 = 11 := rfl; have hb2048 : bits 2048 = 12 := rfl
  dsimp only [stepKemFailSendAtomicC, KemFailRedSendCorrSub.nextKemCandAtomicC,
    KemFailRedSendCorrSub.stepPostKemSendE, KemFailRedSendCorrSub.nextKemCoinsAtomicE,
    KemFailRedSendCorrSub.honestExchangeFailsAtomicC, KemFailRedSendCorrSub.issue1275FixEsC,
    KemFailRedSendCorrSub.issue1275ScanStepE, KemFailRedSendCorrSub.swapPairsStepE,
    KemFailRedSendCorrSub.bytes2EqLitE, KemFailRedSendCorrSub.encRandBvAtomicE,
    KemFailRedSendCorrSub.isKeysUnsampledV1E, KemFailRedSendCorrSub.isHeaderReceivedV1E,
    KemFailRedSendCorrSub.ekSideIsAE, KemFailRedSendCorrSub.boolOrE, KemFailRedSendCorrSub.boolEqE,
    KemFailRedSendCorrSub.trE_e, KemFailRedSendCorrSub.trE_c, KemFailRedSendCorrSub.trE_st,
    KemFailRedSendCorrSub.trE_sentB, KemFailRedSendCorrSub.trE_sendCtr, trE_cand,
    KemFailRedSendCorrSub.trMk, CryptoGames.SM.pGet, CryptoGames.SM.pSet,
    sOpPure, sOpSpqr, AtomicSessionBridge.sessPureOp, AtomicSessionBridge.sessSpqrKemOp,
    eLet, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Comp.size, Expr.size,
    atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize,
    List.length_cons, List.length_nil] at trE qBE rqE ⊢
  omega

private theorem simFig8HaltedSendHookC_queries (idA idB : IdentityKey) (qep q : ℕ)
    {Γ : List (Ty ASig)} (stE : Expr AOps Γ (simHaltedT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (simFig8HaltedSendHookC idA idB qep q stE qBE m0E chalE rE).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  dsimp only [simFig8HaltedSendHookC, _root_.ReductionDsl.AtomicUnifBase.sort]
  simp only [Comp.queries, stepKemFailSendFig8C_queries, mkPubAtomicC_queries,
    simSendQueryC_queries]
  omega

private theorem simFig8HaltedSendHookC_cost (idA idB : IdentityKey) (qep q : ℕ)
    {Γ : List (Ty ASig)} (stE : Expr AOps Γ (simHaltedT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (simFig8HaltedSendHookC idA idB qep q stE qBE m0E chalE rE).cost ≤
      stE.cost + qBE.cost + m0E.cost + chalE.cost + rE.cost +
        16 * (ℓ / 32) + 4 * q + 2 * bits qep + 18000000 := by
  let Γ1 := haltedSendInpT ℓ Pt :: Γ; let Γ2 := simMirT ℓ Pt :: Γ1
  let Γ3 := BV512 :: Γ2; let Γ4 := Ty.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt) :: Γ3
  let Γ5 := Ty.opt BV256 :: Γ4
  let Γ6 := U32 :: Γ5; let Γ7 := Ty.opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))) :: Γ6
  let Γ8 := Ty.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)) :: Γ7
  let Γ9 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ8
  let Γ10 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ9
  have hnb := cost_mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1)
    (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0))
  have hep := cost_mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) qep
    (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hsf := cost_mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ2) .v0 (.fst (.snd .v1))
  have hkf := stepKemFailSendFig8C_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ3)
    (.snd (.fst .v2)) (.fst (.snd .v2)) .v0
  let v5 : Expr AOps Γ6 (haltedSendInpT ℓ Pt) := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
  have hmk := mkPubAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB (Γ := Γ6)
    (scBase (.fst (.fst v5))) (.fst (.snd v5)) .v3 .v0
  let v7 : Expr AOps Γ8 (haltedSendInpT ℓ Pt) :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  have hsq := simSendQueryC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ8)
    (.fst (.snd v7)) (.snd .v0) (.fst (.snd (.snd v7))) (.fst (.snd (.snd (.snd v7)))) .v3
  let v4_pn : Expr AOps Γ10 U32 := .var (.succ (.succ (.succ (.succ .zero))))
  let v8_s1 : Expr AOps Γ10 (simMirT ℓ Pt) :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
  let v9 : Expr AOps Γ10 (haltedSendInpT ℓ Pt) :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
  have hps := scPostSendAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ10) (.fst (.fst v9)) v8_s1 (.fst (.snd v9))
    (.fst (.snd (.snd v9))) (isSomeE (.fst (.snd (.snd (.snd v9))))) (.fst .v2) v4_pn .v0
  have hb1 : bits 1 = 1 := rfl
  dsimp only [simFig8HaltedSendHookC, _root_.ReductionDsl.AtomicUnifBase.sort]
  dsimp only [Γ1, Γ2, Γ3, Γ4, Γ5, Γ6, Γ7, Γ8, Γ9, Γ10, haltedSendInpT,
    v5, v7, v4_pn, v8_s1, v9] at hnb hep hsf hkf hmk hsq hps ⊢
  generalize mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ _ = enb at hnb ⊢
  generalize mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) qep _ _ _ = eep at hep ⊢
  generalize mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ _ = esf at hsf ⊢
  generalize stepKemFailSendFig8C (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ = ckf at hkf ⊢
  generalize mkPubAtomicC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB _ _ _ _ = cmk at hmk ⊢
  generalize simSendQueryC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ _ _ _ _ = csq at hsq ⊢
  generalize scPostSendAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB _ _ _ _ _ _ _ _ = eps at hps ⊢
  dsimp only [Comp.sample, fig8SmIface, _root_.ReductionDsl.atomicSamplers,
    _root_.ReductionDsl.unifSamplers, _root_.ReductionDsl.AtomicUnifBase.cost,
    Comp.cost, Expr.cost, cost_eLet, cost_sOpPure, AtomicPureOp.cost, trE_cand,
    orE, isSomeE, pGet, scBase, ssMir, ssStopped, ssPn, mWin, mEpoch, mIdx,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hnb hep hsf hkf hmk hsq hps ⊢
  omega

private theorem simFig8HaltedSendHookC_size_le (idA idB : IdentityKey) (qep q : ℕ)
    {Γ : List (Ty ASig)} (stE : Expr AOps Γ (simHaltedT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (m0E : Expr AOps Γ PlainT) (chalE : Expr AOps Γ (.opt PlainT))
    (rE : Expr AOps Γ (.opt BV512)) :
    (simFig8HaltedSendHookC idA idB qep q stE qBE m0E chalE rE).size ≤
      stE.size + qBE.size + m0E.size + chalE.size + rE.size +
        4 * bits qep + bits (q + 1) + 90000 := by
  let Γ1 := haltedSendInpT ℓ Pt :: Γ; let Γ2 := simMirT ℓ Pt :: Γ1
  let Γ3 := BV512 :: Γ2; let Γ4 := Ty.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt) :: Γ3
  let Γ5 := Ty.opt BV256 :: Γ4
  let Γ6 := U32 :: Γ5; let Γ7 := Ty.opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt))) :: Γ6
  let Γ8 := Ty.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)) :: Γ7
  let Γ9 := Ty.opt (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ8
  let Γ10 := fig8CtT (ℓ := ℓ) (Pt := Pt) :: Γ9
  have hnb := (expr_size_le_descBits ADesc _).trans
    (mNoBobEpoch0E_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc (Γ := Γ1)
      (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)))
  have hep := (expr_size_le_descBits ADesc _).trans
    (mEpMgmtE_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc qep (Γ := Γ1)
      (ssMir (scBase (.fst (.fst .v0)))) (.fst (.snd .v0)) (isSomeE (.snd (.snd (.snd (.snd .v0))))))
  have hsf := (expr_size_le_descBits ADesc _).trans
    (mSafeChE_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc (Γ := Γ2) .v0 (.fst (.snd .v1)))
  have hkf := stepKemFailSendFig8C_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γ3)
    (.snd (.fst .v2)) (.fst (.snd .v2)) .v0
  let v5 : Expr AOps Γ6 (haltedSendInpT ℓ Pt) := .var (.succ (.succ (.succ (.succ (.succ .zero)))))
  have hmk := (comp_size_le_descBits ADesc (fun _ => 8) (fun _ => 8) _).trans
    (mkPubAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB (fun _ => 8) (fun _ => 8) (Γ := Γ6)
      (scBase (.fst (.fst v5))) (.fst (.snd v5)) .v3 .v0)
  let v7 : Expr AOps Γ8 (haltedSendInpT ℓ Pt) :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
  have hsq := (comp_size_le_descBits ADesc (fun _ => 8) (fun _ => 8) _).trans
    (simSendQueryC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ8)
      (.fst (.snd v7)) (.snd .v0) (.fst (.snd (.snd v7))) (.fst (.snd (.snd (.snd v7)))) .v3)
  let v4_pn : Expr AOps Γ10 U32 := .var (.succ (.succ (.succ (.succ .zero))))
  let v8_s1 : Expr AOps Γ10 (simMirT ℓ Pt) :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
  let v9 : Expr AOps Γ10 (haltedSendInpT ℓ Pt) :=
    .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
  have hps := (expr_size_le_descBits ADesc _).trans
    (scPostSendAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB (Γ := Γ10) (.fst (.fst v9)) v8_s1 (.fst (.snd v9))
      (.fst (.snd (.snd v9))) (isSomeE (.fst (.snd (.snd (.snd v9))))) (.fst .v2) v4_pn .v0)
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl; have hb3 : bits 3 = 2 := rfl
  have hb4 : bits 4 = 3 := rfl; have hb5 : bits 5 = 3 := rfl; have hb6 : bits 6 = 3 := rfl
  have hb7 : bits 7 = 3 := rfl; have hb8 : bits 8 = 4 := rfl; have hb9 : bits 9 = 4 := rfl
  have hb10 : bits 10 = 4 := rfl
  dsimp only [simFig8HaltedSendHookC, _root_.ReductionDsl.AtomicUnifBase.sort]
  dsimp only [Γ1, Γ2, Γ3, Γ4, Γ5, Γ6, Γ7, Γ8, Γ9, Γ10, haltedSendInpT,
    v5, v7, v4_pn, v8_s1, v9] at hnb hep hsf hkf hmk hsq hps ⊢
  generalize mNoBobEpoch0E (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ _ = enb at hnb ⊢
  generalize mEpMgmtE (ℓ := ℓ) (Pt := Pt) (O' := AOps) qep _ _ _ = eep at hep ⊢
  generalize mSafeChE (ℓ := ℓ) (Pt := Pt) (O' := AOps) _ _ = esf at hsf ⊢
  generalize stepKemFailSendFig8C (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q _ _ _ = ckf at hkf ⊢
  generalize mkPubAtomicC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (fig8SmIface ℓ Pt) idA idB _ _ _ _ = cmk at hmk ⊢
  generalize simSendQueryC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ _ _ _ _ = csq at hsq ⊢
  generalize scPostSendAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB _ _ _ _ _ _ _ _ = eps at hps ⊢
  dsimp only [Comp.sample, Comp.size, Expr.size, eLet, sOpPure,
    AtomicSessionBridge.sessPureOp, trE_cand, orE, isSomeE, pGet, scBase, ssMir, ssStopped, ssPn,
    mWin, mEpoch, mIdx, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    atomicExprDescBits, Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx,
    atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicSpqrKemOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.AtomicPureOp.opSize]
    at stE qBE m0E chalE rE enb eep esf ckf cmk csq eps hnb hep hsf hkf hmk hsq hps ⊢
  simp only [Nat.reduceAdd]
    at hnb hep hsf hkf hmk hsq hps ⊢
  omega

omit [SampleableType Pt] in
private theorem simHaltedStepDispatchC_queries {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (q : ℕ)
    (cSend : Comp AOps I' [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simHaltedT ℓ Pt)))
    (cCorr : Comp AOps I' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp AOps I' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (simHaltedStepDispatchC q cSend cCorr cRecv).queries w ws ≤
      max (max (cSend.queries w ws) (cCorr.queries w ws)) (cRecv.queries w ws) := by
  simp only [simHaltedStepDispatchC, callSub1C, wkTop1Comp, callSub2C_queries,
    Comp.queries, Comp.renameM_queries]; omega

private theorem simHaltedStepDispatchC_cost {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (q : ℕ)
    (cSend : Comp AOps I' [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simHaltedT ℓ Pt)))
    (cCorr : Comp AOps I' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp AOps I' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    (simHaltedStepDispatchC q cSend cCorr cRecv).cost ≤
      max (max cSend.cost cCorr.cost) cRecv.cost + 152 * q + 8400 := by
  let Γr := Ty.prod .bool (.prod (B 32) .bool) :: [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γj := Ty.opt .nat :: Γr; let Γo := recvOutT ℓ Pt :: Γj
  have hf := findRevHonestIdxE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr)
    (ssHonest (scBase (.fst .v1))) (.fst .v0) (.fst (.snd .v0))
  have hk := kemOnDeliverPostAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γo) (.fst .v2) .v1 (.fst .v0) (.snd .v3)
  dsimp only [simHaltedStepDispatchC]
  generalize findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr) _ _ _ = ef at hf ⊢
  generalize kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γo) _ _ _ _ = ek at hk ⊢
  simp only [extractHaltedRecvOptE, isHaltedSendOrChallE, callSub1C, wkTop1Comp,
    callSub2C_cost, Comp.cost, Comp.renameM_cost, Expr.cost, scBase, ssHonest,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hf hk ⊢; omega

private theorem simHaltedStepDispatchC_size_le {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    (q : ℕ)
    (cSend : Comp AOps I' [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simHaltedT ℓ Pt)))
    (cCorr : Comp AOps I' [simFullT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (simFullT ℓ Pt)))
    (cRecv : Comp AOps I' [recvHookInpT ℓ Pt] (recvOutT ℓ Pt)) :
    (simHaltedStepDispatchC q cSend cCorr cRecv).size ≤
      cSend.size + cCorr.size + cRecv.size + 16 * bits q + 15000 := by
  let Γr := Ty.prod .bool (.prod (B 32) .bool) :: [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let Γj := Ty.opt .nat :: Γr; let Γo := recvOutT ℓ Pt :: Γj
  have hf := (expr_size_le_descBits ADesc _).trans
    (findRevHonestIdxE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr)
      (ssHonest (scBase (.fst .v1))) (.fst .v0) (.fst (.snd .v0)))
  have hk := (expr_size_le_descBits ADesc _).trans
    (kemOnDeliverPostAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q (Γ := Γo) (.fst .v2) .v1 (.fst .v0) (.snd .v3))
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl; have hb3 : bits 3 = 2 := rfl; have hb4 : bits 4 = 3 := rfl
  dsimp only [simHaltedStepDispatchC]
  generalize findRevHonestIdxE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γr) _ _ _ = ef at hf ⊢
  generalize kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) q (Γ := Γo) _ _ _ _ = ek at hk ⊢
  simp only [extractHaltedRecvOptE, isHaltedSendOrChallE, callSub1C_size, callSub2C_size,
    Comp.size, Expr.size, scBase, ssHonest, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    atomicExprDescBits, Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost.varIdx]
    at hf hk ⊢
  simp only [Nat.reduceAdd] at hf hk ⊢
  omega

private theorem simFig8HaltedStepSendC_queries (idA idB : IdentityKey) (qep q : ℕ) :
    (simFig8HaltedStepSendC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  let Γu := Ty.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))) ::
    [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hh := simFig8HaltedSendHookC_queries (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q (Γ := Γu)
    .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  dsimp only [simFig8HaltedStepSendC]
  generalize simFig8HaltedSendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q (Γ := Γu) _ _ _ _ _ = ch at hh ⊢
  dsimp only [Comp.queries] at hh ⊢; omega

private theorem simFig8HaltedStepSendC_cost (idA idB : IdentityKey) (qep q : ℕ) :
    (simFig8HaltedStepSendC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q).cost ≤
      16 * (ℓ / 32) + 4 * q + 2 * bits qep + 18000100 := by
  let Γu := Ty.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))) ::
    [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hh := simFig8HaltedSendHookC_cost (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q (Γ := Γu)
    .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  dsimp only [simFig8HaltedStepSendC]
  generalize simFig8HaltedSendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q (Γ := Γu) _ _ _ _ _ = ch at hh ⊢
  dsimp only [unpackSendQE, Comp.cost, Expr.cost, Expr.v0, Expr.v1] at hh ⊢; omega

private theorem simFig8HaltedStepSendC_size_le (idA idB : IdentityKey) (qep q : ℕ) :
    (simFig8HaltedStepSendC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q).size ≤
      4 * bits qep + bits (q + 1) + 90100 := by
  let Γu := Ty.prod .bool (.prod PlainT (.prod (.opt PlainT) (.opt BV512))) ::
    [simHaltedT ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have hh := simFig8HaltedSendHookC_size_le (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q (Γ := Γu)
    .v1 (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
  dsimp only [simFig8HaltedStepSendC]
  generalize simFig8HaltedSendHookC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB qep q (Γ := Γu) _ _ _ _ _ = ch at hh ⊢
  dsimp only [unpackSendQE, Comp.size, Expr.size, Expr.v0, Expr.v1] at hh ⊢; omega

private theorem halted_step_queries_arith {qTot qS qC qR qN qSm : ℕ}
    (h0 : qTot ≤ max (max qS qC) qR) (hS : qS ≤ 1) (hC : qC ≤ 1)
    (hR : qR = max qN qSm) (hN : qN ≤ 1) (hSm : qSm ≤ 1) : qTot ≤ 1 := by omega

private theorem halted_step_cost_arith {ℓ q qep cTot cS cC cR cN cSm : ℕ} (hℓ : ℓ < 10 ^ 6)
    (h0 : cTot ≤ max (max cS cC) cR + 152 * q + 8400)
    (hS : cS ≤ 16 * (ℓ / 32) + 4 * q + 2 * bits qep + 18000100)
    (hC : cC ≤ 2000100 + 25100000 * q)
    (hR : cR ≤ max cN cSm + 2 * (ℓ / 32) + 500 * q + 131220000)
    (hN : cN ≤ 24010005 + 20000000 * q + 128 * bits (qep + 1))
    (hSm : cSm ≤ 25000005 + 20000000 * q + 128 * bits (qep + 1)) :
    cTot ≤ 199000000 + 100000000 * q + 4096 * bits (qep + 1) := by
  have hbqep : bits qep ≤ bits (qep + 1) := bits_mono (by omega); omega

private theorem halted_step_size_arith {q qep sTot sS sC sR dN dSm : ℕ}
    (h0 : sTot ≤ sS + sC + sR + 16 * bits q + 15000)
    (hS : sS ≤ 4 * bits qep + bits (q + 1) + 90100)
    (hC : sC ≤ 132000 + 128 * bits (q + 1))
    (hR : sR ≤ dN + dSm + 8 * bits q + 130000)
    (hN : dN ≤ 275010 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (hSm : dSm ≤ 260010 + 256 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))) :
    sTot ≤ 2 ^ 20 + 2 ^ 10 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  have hb2 := bits_two_mul_add_two_le_ratchetCostBudget q (qep + 1)
  have hbq : bits q ≤ bits (2 * q + 2) := bits_mono (by omega)
  have hbq1 : bits (q + 1) ≤ bits (2 * q + 2) := bits_mono (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := bits_mono (by omega)
  omega

private theorem simFig8HaltedRawStepC_queries (idA idB : IdentityKey) (qep q : ℕ) :
    (simFig8HaltedRawStepC (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).queries
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  unfold simFig8HaltedRawStepC
  let fwdSpec := simFig8FwdHookSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let sameSpec := simFig8RecvSameSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let newSpec := simFig8RecvNewSpec_of_fwd C K Dh encPt encT decT lam
    idA idB qep q fwdSpec.comp fwdSpec.hq fwdSpec.hcost fwdSpec.hdesc fwdSpec.heval
  exact halted_step_queries_arith
    (simHaltedStepDispatchC_queries q _ _ _ (fun _ => 1) (fun _ => 0))
    (simFig8HaltedStepSendC_queries idA idB qep q)
    (simFig8StepCorrC_queries idA idB q)
    (recvHookOfBranchesC_queries C K Dh encPt encT decT lam idA idB q
      sameSpec.comp newSpec.comp (fun _ => 1) (fun _ => 0))
    newSpec.hq sameSpec.hq

private theorem simFig8HaltedRawStepC_cost (idA idB : IdentityKey) (qep q : ℕ) (hℓ : ℓ < 10 ^ 6) :
    (simFig8HaltedRawStepC (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).cost ≤
      199000000 + 100000000 * q + 4096 * bits (qep + 1) := by
  unfold simFig8HaltedRawStepC
  let fwdSpec := simFig8FwdHookSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let sameSpec := simFig8RecvSameSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let newSpec := simFig8RecvNewSpec_of_fwd C K Dh encPt encT decT lam
    idA idB qep q fwdSpec.comp fwdSpec.hq fwdSpec.hcost fwdSpec.hdesc fwdSpec.heval
  exact halted_step_cost_arith hℓ
    (simHaltedStepDispatchC_cost q _ _ _)
    (simFig8HaltedStepSendC_cost idA idB qep q)
    (simFig8StepCorrC_cost idA idB q hℓ)
    (recvHookOfBranchesC_cost C K Dh encPt encT decT lam idA idB q sameSpec.comp newSpec.comp)
    (newSpec.hcost hℓ) (sameSpec.hcost hℓ)

private theorem simFig8HaltedRawStepC_size_le (idA idB : IdentityKey) (qep q : ℕ)
    (hℓ : ℓ < 10 ^ 6) :
    (simFig8HaltedRawStepC (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q).size ≤
      2 ^ 20 + 2 ^ 10 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)) := by
  unfold simFig8HaltedRawStepC
  let fwdSpec := simFig8FwdHookSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let sameSpec := simFig8RecvSameSpec (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q
  let newSpec := simFig8RecvNewSpec_of_fwd C K Dh encPt encT decT lam
    idA idB qep q fwdSpec.comp fwdSpec.hq fwdSpec.hcost fwdSpec.hdesc fwdSpec.heval
  exact halted_step_size_arith
    (simHaltedStepDispatchC_size_le q _ _ _)
    (simFig8HaltedStepSendC_size_le idA idB qep q)
    ((comp_size_le_descBits ADesc (fun _ => 8) (fun _ => 8) _).trans
      (simFig8StepCorrC_descBits_le idA idB q hℓ))
    ((comp_size_le_descBits ADesc (fun _ => 8) (fun _ => 8) _).trans
      (recvHookOfBranchesC_descBits_le C K Dh encPt encT decT lam idA idB q
        sameSpec.comp newSpec.comp (fun _ => 8) (fun _ => 8)))
    (newSpec.hdesc hℓ) (sameSpec.hdesc hℓ)

private theorem ratchetCostBudget_mono_qep {q qep₁ qep₂ : ℕ} (h : qep₁ ≤ qep₂) :
    ratchetCostBudget q qep₁ ≤ ratchetCostBudget q qep₂ := by
  unfold ratchetCostBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (bits_mono h) _)

end CostAndSize

section Theorems

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem simFig8RedProgHalted_gRedBounded_of_le (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q qep' : ℕ)
    (hqep : qep ≤ q + 10) (hbud : qep + 1 ≤ qep') :
    GRedBounded (simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep') := by
  apply gRedBounded_of_bounds _ (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q qep')
  · unfold simFig8RedProgHalted
    split_ifs with hℓ
    · have hi := simFig8HaltedInitC_cost_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      have hf := simFig8HaltedFinishC_cost_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      have hs := simFig8HaltedRawStepC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q hℓ
      have hmax : max 1 ((simFig8HaltedRawStepC (Pt := Pt) ℓ C K idA idB Dh encPt encT decT
          lam qep q).cost + 16) ≤
          199000020 + 100000000 * q + 4096 * bits (qep + 1) := by omega
      have htot : (simFig8RedProgHaltedReal (Pt := Pt) ℓ C K idA idB Dh encPt encT decT
          lam qep q).totalCost q ≤
          4100 + q * (199000020 + 100000000 * q + 4096 * bits (qep + 1)) + 4 := by
        dsimp only [simFig8RedProgHaltedReal, CostedReduction.totalCost]
        have hmul := Nat.mul_le_mul_left q hmax
        omega
      exact (htot.trans (session_cost_le_ratchetCostBudget q (qep + 1)
        4100 4 199000020 100000000 4096
        (by omega) (by omega) (by omega) (by omega) (by omega))).trans
        (ratchetCostBudget_mono_qep hbud)
    · exact dummyBoolSessionRed_totalCost_le (fig8SmIface ℓ Pt) rfl .unit q qep'
  · unfold simFig8RedProgHalted
    split_ifs with hℓ
    · have hi := simFig8HaltedInitC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      have hf := simFig8HaltedFinishC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
      have hs := simFig8HaltedRawStepC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q hℓ
      set B := ratchetCostBudget q qep'
      have hBpos : 16777216 * (q + 1) ≤ B := ratchetCostBudget_pos q qep'
      have hBmono : ratchetCostBudget q (qep + 1) ≤ B := ratchetCostBudget_mono_qep hbud
      have hsum : ratchetCostBudget q (qep + 1) + (qep + 1) ≤ 4 * B := by omega
      have hbits : bits (ratchetCostBudget q (qep + 1) + (qep + 1)) ≤ 3 + bits B := by
        have hm1 := bits_mono hsum; have hm2 := bits_mul_le 4 B; have hb4 : bits 4 = 3 := rfl; omega
      have hred : reductionSizeBudget = 2 ^ 24 := rfl
      dsimp only [simFig8RedProgHaltedReal, CostedReduction.size]; omega
    · have hd : (dummyBoolSessionRed (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
          (fig8SmIface ℓ Pt) .unit).size = 14 := rfl
      have hred : reductionSizeBudget = 2 ^ 24 := rfl; omega
  · unfold simFig8RedProgHalted; split_ifs with hℓ
    · simp only [simFig8RedProgHaltedReal, CostedReduction.totalQueries,
        simFig8HaltedInitC_queries, simFig8HaltedFinishC_queries, zero_add, add_zero]
      have hs := simFig8HaltedRawStepC_queries (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB qep q
      exact (Nat.mul_le_mul_left q hs).trans (Nat.mul_one q).le
    · rw [dummyBoolSessionRed_totalQueries]; exact Nat.zero_le q
  · exact atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam
  · exact atomicSamplers_sizeHonest ℓ Pt

/-- `GRedBounded` bound for `simFig8RedProgHalted` at `ratchetCostBudget q (qep + 1)`. -/
theorem simFig8RedProgHalted_gRedBounded (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ) (hqep : qep ≤ q + 10) :
    GRedBounded (simFig8RedProgHalted (Pt := Pt) ℓ C K idA idB Dh encPt encT decT lam qep q)
      (fun _ => 1) (fun _ => 0) q q (ratchetCostBudget q (qep + 1)) :=
  simFig8RedProgHalted_gRedBounded_of_le ℓ C K idA idB Dh encPt encT decT lam qep q (qep + 1)
    hqep (Nat.le_refl _)

end Theorems

end

end Computational.Proofs.Game.PromotedCostedReds.SimFig8Halted
