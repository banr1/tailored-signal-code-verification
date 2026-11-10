/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8
public import Computational.Proofs.SessionCostedFig8.BundlesEval
public import Computational.Proofs.SessionCostedFig8.FsAtomicBSwap
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2

/-!
# Atomic Compiler, `FsAtomicBSwap`, and `FsOk` Bridges for Shifted Paper `DeliverForge` Reductions

Proves evaluation, `CoinSimEquiv`, `QuerySubsumes`, `FsAtomicBSwap`, and `FsOk` bridges for
`compile{Cka,Prng,Fs}DFAtomic` applied to `red{CKA,PRNG,FS}AuthDFShiftedPaperGenProg`.
-/
open scoped ENNReal
open CryptoGames (AEADScheme CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lPubOf)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open CryptoGames.SM.Construction (CKAState FSState FSVROkStep Header PRNGState PartyState fst_mem_support_of_mem_support_simulateQ_run hooksFS hooksFS_vrInv_fromAEADPRG initFS initFSRaw initFSRaw_inv initFSRaw_vrInv_fromAEADPRG initPRNG isQueryBoundP_initFSRaw_dec liftC mkParties receiverState_reach_of_isDecQuery_bound sampleT vSend_ext_snd)
open CryptoGames.SM.Engine (Ctx EState HM Hooks HooksVRInv Policy RSReach SMEngineInv SMVRInv VP abortE challE coinsE commitE deliverE injectE run_liftH_bind transmitE vRecv vSend)
open CryptoVerification.LibsignalSession (FsOk ckaAdvantage_dhSchemeFb_eq encMsgsOk_shortB_of_atomicShortPubB fsClamp_fsAtomicB_fsSendShort)
open CryptoVerification.LibsignalSession.HeadlineV1 (EqualPubChallsDF GuardedSMDFShort SendMsgsOkDF badSendMsgDF guardedFSInjectShort_redFSAuthDFShiftedPaperGen safePost_redFSAuthDFShiftedPaperGen_restricted safePost_redFSAuthDFShiftedPaperGen_short)
open ReductionDsl (CostedReduction ckaTargetIface fsaeadHeaderIface prngTargetIface)

@[expose] public section

namespace Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapShifted

set_option autoImplicit false
set_option linter.dupNamespace false


open OracleSpec OracleComp
open _root_.ReductionDsl (CostedReduction atomicFig8Ops fig8SmIfaceDF fig8SmCodecDF
  ckaTargetIface prngTargetIface fsaeadHeaderIface)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic fsAtomicB atomicShortPubB)
open Computational.Proofs.SessionCostedFig8.Bundles (fig8CkaOpsShallow
  compileCkaDFAtomic compilePrngDFAtomic compileFsDFAtomic)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

section ShiftedPaperAtomicBridges

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance instInhabitedPtBSwapShifted : Inhabited Pt := ⟨0⟩

/-- Shifted paper CKA reduction wrapper unifying `ShiftedPaper` (`Δcka = 1`, `tStarH = tStar`)
and `ShiftedDir2Paper` (`Δcka = 0`, `tStarH = 0`). -/
abbrev redCKAAuthDFShiftedPaperGen
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (Δcka qep l tStarH tStar : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    CryptoGames.CKA.Adversary Γ CCoins T I :=
  show CryptoGames.CKA.AdversaryComp Γ CCoins T I Bool from
  CryptoGames.SM.Construction.DeliverForge.authSimDFShiftedPaperGen (decide (Δcka = 0)) l fs Δcka qep
    (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted cka prng fs l tStarH)
    (CryptoGames.SM.Construction.DeliverForge.initCKAShifted cka prng fs lam l) {} (some (l - 1)) tStar A

omit [Zero Pt] [SampleableType Pt] in
theorem redCKAAuthDFShiftedPaperGen_one {ℓ : ℕ}
    (cka : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (lam : Pt) (qep l tStar : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) :
    redCKAAuthDFShiftedPaperGen cka prng fs lam 1 qep l tStar tStar A =
      CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedPaper cka prng fs lam 1 qep l tStar A :=
  CryptoGames.SM.Construction.DeliverForge.authSimDFShiftedPaperGen_false l fs 1 qep _ _ _ _ tStar A

omit [Zero Pt] [SampleableType Pt] in
theorem redCKAAuthDFShiftedPaperGen_zero {ℓ : ℕ}
    (cka : CKAScheme (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt)
    (prng : PRFPRNG (BitVec 256) (BitVec 256) Pt (BitVec 256))
    (fs : FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (lam : Pt) (qep l tStar : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) :
    redCKAAuthDFShiftedPaperGen cka prng fs lam 0 qep l 0 tStar A =
      CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedDir2Paper cka prng fs lam qep l tStar A :=
  CryptoGames.SM.Construction.DeliverForge.authSimDFShiftedPaperGen_true l fs qep _ _ _ _ tStar A

/-! ## Shallow evaluation bridges -/

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem hooksCKAShifted_commit_vR {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (l tStar : ℕ)
    (ctx : CryptoGames.SM.Engine.Ctx (Option Γ) T RSt SS RS M E) (P : Party)
    (old new : CryptoGames.SM.Engine.VP (Option Γ) T RSt SS RS) (h : CryptoGames.SM.Construction.DeliverForge.CKAStateShifted Γ T I) :
    ∀ res ∈ support (((CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted cka prng fs l tStar).commit
        ctx P old new).run h),
      ∀ new', res.1 = some new' → new'.vR = new.vR := by
  intro ⟨ans, h'⟩ hmem new' hEq
  dsimp only at hEq
  subst hEq
  dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted] at hmem
  by_cases h1 : (decide (old.tcur < new.tcur) && old.γ.isNone) = true
  · simp only [h1, ↓reduceIte, CryptoGames.SM.Construction.DeliverForge.liftCShifted, StateT.run_bind, StateT.run_lift,
      mem_support_bind_iff] at hmem
    obtain ⟨rcvRes, _, hmem⟩ := hmem
    rcases rcvRes with _ | ⟨⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h, _⟩; cases h
    · dsimp only at hmem
      by_cases h2 : l + 2 ≤ new.tcur
      · simp only [h2, ↓reduceIte, StateT.run_bind, StateT.run_lift,
          mem_support_bind_iff] at hmem
        obtain ⟨γ?, _, hmem⟩ := hmem
        rcases γ? with _ | γ'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h, _⟩; cases h
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩; rfl
      · simp only [h2, ↓reduceIte] at hmem
        by_cases h3 : new.tcur + 1 ≤ l
        · simp only [h3, ↓reduceIte, StateT.run_bind, StateT.run_lift,
            mem_support_bind_iff] at hmem
          obtain ⟨γ?, _, hmem⟩ := hmem
          rcases γ? with _ | γ'
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨h, _⟩; cases h
          · simp only [CryptoGames.SM.Construction.DeliverForge.setγPreShifted, StateT.run_bind, StateT.run_modify,
              pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq, Option.some.injEq] at hmem
            rcases hmem with ⟨rfl, rfl⟩; rfl
        · simp only [h3, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩; rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩; rfl

omit [Zero Pt] [SampleableType Pt] in
theorem hooksCKAShifted_vrInv_fsAtomicB
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 l tStarH : ℕ) :
    HooksVRInv (RSReach maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) l tStarH) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    CryptoGames.SM.Construction.hooksCKAShifted_startRecv_rs (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) l tStarH
      (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps)
      ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨hrec, _⟩
    exact (BundlesEval.fsAtomicB_receive_rsReach C ℓ encT idOf B0 _ hVR hrec.symm).2
  commit_vR :=
    hooksCKAShifted_commit_vR (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
      l tStarH

omit [Zero Pt] in
theorem redCKAAuthDFShiftedPaperGenProg_eval_atomic
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q l tStarH tStar : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
        l tStarH tStar :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    redCKAAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l tStarH tStar A := by
  intro B0
  exact CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperProg_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q Δcka qep l tStarH tStar
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksCKAShifted_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 l tStarH)
    (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (BundlesEval.fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redPRNGAuthDFShiftedPaperGenProg_advantage_atomic
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      ((CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
          l t useSafeCh :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l t useSafeCh A) := by
  intro B0
  exact CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperProg_advantage_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q Δcka qep l t useSafeCh
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (BundlesEval.hooksPRNG_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 ⟨useSafeCh, some (l - 1), t⟩)
    (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (BundlesEval.fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redFSAuthDFShiftedPaperGenProg_eval_atomic_clamp
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
        j l t useSafeCh :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
      lam Δcka qep j l t useSafeCh A := by
  intro B0
  exact CryptoGames.SM.Construction.redFSAuthDFShiftedPaperProg_eval_clamp
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q Δcka qep j l t useSafeCh
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

/-! ## Compiled `CoinSimEquiv` and `QuerySubsumes` bridges -/

theorem compileCkaDFAtomic_shiftedPaperGen_coinSimEquiv
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q l tStarH tStar : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      ((compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
            l tStarH tStar)).eval (fun _ => A) ())
      (redCKAAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l tStarH tStar A) := by
  intro B0
  rw [← redCKAAuthDFShiftedPaperGenProg_eval_atomic Dh encPt C ℓ encT idOf lam Δcka qep q l tStarH tStar A hqA]
  exact BundlesEval.compileCkaDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem compilePrngDFAtomic_shiftedPaperGen_coinSimEquiv
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      ((compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
            l t useSafeCh)).eval (fun _ => A) ())
      ((CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
          l t useSafeCh :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) := by
  intro B0
  exact BundlesEval.compilePrngDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem compileFsDFAtomic_shiftedPaperGen_coinSimEquiv
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
            j l t useSafeCh)).eval (fun _ => A) ())
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep j l t useSafeCh A) := by
  intro B0
  rw [← redFSAuthDFShiftedPaperGenProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam Δcka qep q j l t useSafeCh A hqA]
  exact BundlesEval.compileFsDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem compileFsDFAtomic_shiftedPaperGen_querySubsumes
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    QuerySubsumes
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
            j l t useSafeCh)).eval (fun _ => A) ())
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep j l t useSafeCh A) := by
  intro B0
  rw [← redFSAuthDFShiftedPaperGenProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam Δcka qep q j l t useSafeCh A hqA]
  exact BundlesEval.compileFsDFAtomic_querySubsumes ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

/-! ## `FsAtomicBSwap` bridges -/

local notation "DDHSt" => CryptoGames.CKA.DDH.State (BitVec 256) Pt
local notation "SS256" => CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)
local notation "RS256" => CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)
local notation "MsgPt" => fun (ℓ : ℕ) => LibsignalMsgPublicPart × Plain ℓ
local notation "Ct32" => ℕ × LibsignalCiphertextWithSalt32

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma badSendMsgDF_query_bind_step {St Msg Coins C α : Type} (ok : Msg → Bool)
    (qy : (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Domain)
    (mx : (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C).Range qy →
      CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF St Msg Coins C α)
    (h : IsQueryBoundP
      ((liftM (OracleSpec.query qy) : OracleComp (unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF St Msg Coins C) _) >>= mx)
      (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) ok t = true) 0) :
    badSendMsgDF (St := St) (Coins := Coins) (C := C) ok qy = false ∧
      ∀ u, IsQueryBoundP (mx u)
        (fun t => badSendMsgDF (St := St) (Coins := Coins) (C := C) ok t = true) 0 := by
  rw [isQueryBoundP_query_bind_iff] at h
  rcases h with ⟨hq0, hmx⟩
  have hbf : badSendMsgDF (St := St) (Coins := Coins) (C := C) ok qy = false :=
    Bool.eq_false_iff.mpr (hq0.resolve_right (by omega))
  refine ⟨hbf, fun u => ?_⟩
  have hu := hmx u; simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hu; exact hu

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma badSendMsgDF_to_badSendMsg {St Msg Coins C : Type} (ok : Msg → Bool)
    (t3 : (((Party × Msg × Option Coins →ₒ Option C) +
        (Party × Msg × Msg × Option Coins →ₒ Option C)) +
        (Party × C →ₒ Option (CryptoGames.SM.RecvResult Msg))).Domain)
    (h : badSendMsgDF (St := St) (Coins := Coins) (C := C) ok (.inr (.inl (.inl (.inl t3)))) = false) :
    CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
      (St := St) (Coins := Coins) (C := C) ok (.inr (.inl (.inl t3))) = false := by
  rcases t3 with (⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩ <;> exact h

omit [Zero Pt] [SampleableType Pt] in
private lemma hooksCKAShifted_vrInv_lFS
    {KC Γ CCoins I KR RSt : Type} [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (l tStarH : ℕ) :
    HooksVRInv (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) l tStarH) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    CryptoGames.SM.Construction.hooksCKAShifted_startRecv_rs cka prng
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) l tStarH
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps) ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩; dsimp only at hEq; subst hEq
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR hmem.1.symm).2
  commit_vR :=
    hooksCKAShifted_commit_vR cka prng
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) l tStarH

omit [Zero Pt] [SampleableType Pt] in
private lemma hooksCKAShifted_localFsAgree
    {KC Γ CCoins I KR RSt : Type} [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 l tStarH : ℕ) :
    FsAtomicBSwap.HooksLocalFsAgree ℓ B0
      (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted cka prng (fsAtomicB C ℓ encT idOf B0) l tStarH)
      (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) l tStarH) where
  startSend_eq := by unfold CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  startRecv_eq := by unfold CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted]
    rw [Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted]
    rw [Computational.Proofs.ReductionDsl.Fig8Atomic.fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq := by unfold CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted; rfl
  reveal_eq := by unfold CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted; rfl

omit [Zero Pt] [SampleableType Pt] in
private lemma implEDFShiftedPaper_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV : Type}
    {ℓ B0 B_q q' l Δ qep tStar : ℕ} {b1 : Bool} {mo' : CryptoGames.SM.Construction.Mode}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt SS256 RS256 (MsgPt ℓ) Ct32 CCoins γV σV SS256 RS256}
    (hAg : FsAtomicBSwap.HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (hVRHk : HooksVRInv (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP γV Pt σV SS256 RS256) (MsgPt ℓ) (Header Pt × Ct32) HS)
    (t : (CryptoGames.SM.specDF (PartyState Γ Pt RSt SS256 RS256) (MsgPt ℓ) CCoins (Header Pt × Ct32)).Domain)
    (hBad : badSendMsgDF (St := PartyState Γ Pt RSt SS256 RS256) (Coins := CCoins)
      (C := Header Pt × Ct32) (fun m => atomicShortPubB m.1) (.inr t) = false)
    (hVR : SMVRInv (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB maxForwardJumps)
      B_q (q' + 1) es.g) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₁ Δ qep maxForwardJumps tStar
      mo'.cfg mo'.policy (.inr t)).run es =
    (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₂ Δ qep maxForwardJumps tStar
      mo'.cfg mo'.policy (.inr t)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
  rcases t with ((t3 | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · exact FsAtomicBSwap.implE_localFs_eq hAg hVRHk hB0 es (.inl (.inl t3))
      (badSendMsgDF_to_badSendMsg (fun m => atomicShortPubB m.1) t3 hBad) hVR
  · cases b1
    · exact FsAtomicBSwap.implE_localFs_eq hAg hVRHk hB0 es (.inl (.inr (P, c))) rfl hVR
    · change (CryptoGames.SM.Construction.DeliverForge.injectEB1 hk₁ qep tStar mo'.cfg (P, c)).run es =
        (CryptoGames.SM.Construction.DeliverForge.injectEB1 hk₂ qep tStar mo'.cfg (P, c)).run es
      unfold CryptoGames.SM.Construction.DeliverForge.injectEB1; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · rfl
      · simp only [run_liftH_bind,
          FsAtomicBSwap.vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c none es.h (hVR P),
          hCommit]
  · change (CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l hk₁ mo'.policy P).run es =
      (CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l hk₂ mo'.policy P).run es
    unfold CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper; rw [hAg.reveal_eq]
  · cases b1
    · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ Δ qep mo'.cfg (P, c, c')).run es =
        (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep mo'.cfg (P, c, c')).run es
      unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · rfl
      · rcases es.g.inTransit P.other c with _ | r
        · rfl
        · dsimp only
          split_ifs
          · rfl
          · simp only [run_liftH_bind,
              FsAtomicBSwap.vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c' none es.h (hVR P),
              hCommit]
    · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 hk₁ qep tStar mo'.cfg (P, c, c')).run es =
        (CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 hk₂ qep tStar mo'.cfg (P, c, c')).run es
      unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · rfl
      · rcases es.g.inTransit P.other c with _ | r
        · rfl
        · dsimp only
          split_ifs
          · rfl
          · simp only [run_liftH_bind,
              FsAtomicBSwap.vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c' none es.h (hVR P),
              hCommit]

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_implEDFShiftedPaper_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV α : Type}
    {ℓ L B0 B_q q l Δ qep tStar : ℕ} {b1 : Bool} {mo' : CryptoGames.SM.Construction.Mode}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt SS256 RS256 (MsgPt ℓ) Ct32 CCoins γV σV SS256 RS256}
    (hAg : FsAtomicBSwap.HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (hVRHk : HooksVRInv (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : OracleComp (unifSpec + CryptoGames.SM.specDF (PartyState Γ Pt RSt SS256 RS256)
      (MsgPt ℓ) CCoins (Header Pt × Ct32)) α}
    (hoa : oa.IsQueryBoundP (ReductionDsl.isGameQuery
      (G := CryptoGames.SM.specDF (PartyState Γ Pt RSt SS256 RS256) (MsgPt ℓ) CCoins (Header Pt × Ct32))) q)
    (hSendOk : oa.IsQueryBoundP (fun t => badSendMsgDF (St := PartyState Γ Pt RSt SS256 RS256)
      (Coins := CCoins) (C := Header Pt × Ct32) (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP γV Pt σV SS256 RS256) (MsgPt ℓ) (Header Pt × Ct32) HS)
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB maxForwardJumps)
      B_q q es.g) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₁ Δ qep maxForwardJumps tStar
      mo'.cfg mo'.policy) oa).run es =
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₂ Δ qep maxForwardJumps tStar
      mo'.cfg mo'.policy) oa).run es := by
  induction oa using OracleComp.inductionOn generalizing q es with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa; rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ := badSendMsgDF_query_bind_step (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      have hInl1 : (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₁ Δ qep maxForwardJumps tStar
          mo'.cfg mo'.policy (.inl n)).run es = (coinsE n).run es := rfl
      have hInl2 : (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₂ Δ qep maxForwardJumps tStar
          mo'.cfg mo'.policy (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, _, rfl⟩ := hmem
      exact ih u (hmx u) (hSendMx u) _ hInv hVR
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq0.resolve_left (by decide); omega⟩
      rw [implEDFShiftedPaper_localFs_eq hAg hVRHk hB0 es t_sm hBad hVR]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      exact ih u (by simpa using hmx u) (hSendMx u) es'
        (CryptoGames.SM.Engine.implEDFShiftedPaper_inv b1 hk₂ l mo'.cfg mo'.policy es t_sm hInv (u, es') hmem)
        (CryptoGames.SM.Engine.implEDFShiftedPaper_vrInv b1 hk₂ hVRHk l mo'.cfg mo'.policy es t_sm hInv hVR
          (u, es') hmem)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private lemma afterCorrShifted_st_eq {St Msg C : Type} (l : ℕ) (s : CryptoGames.SM.GameState St Msg C)
    (P : Party) :
    (CryptoGames.SM.Construction.DeliverForge.afterCorrShifted l s P).st = s.st := by
  unfold CryptoGames.SM.Construction.DeliverForge.afterCorrShifted CryptoGames.SM.GameState.leak; split_ifs <;> rfl

omit [Zero Pt] [SampleableType Pt] in
private lemma deliverForgeEGen_localCKA_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS RSt SS RS M E σV ssV rsV : Type} [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS DDHSt Pt RSt SS RS M E (BitVec 256) DDHSt σV ssV rsV}
    (hAg : CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree (fun P γ t => CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P t γ) hk₁ hk₂)
    (b1 : Bool) (Δ qep tStar : ℕ) (cfg : CryptoGames.SM.Config M)
    (P : Party) (c c' : Header Pt × E)
    (es : EState (VP DDHSt Pt σV ssV rsV) M (Header Pt × E) HS)
    (hEs : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv es) :
    (CryptoGames.SM.Engine.deliverForgeEGen b1 hk₁ Δ qep tStar cfg (P, c, c')).run es =
      (CryptoGames.SM.Engine.deliverForgeEGen b1 hk₂ Δ qep tStar cfg (P, c, c')).run es ∧
    ∀ res ∈ support ((CryptoGames.SM.Engine.deliverForgeEGen b1 hk₂ Δ qep tStar cfg (P, c, c')).run es),
      CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv res.2 := by
  cases b1 <;> [
    unfold CryptoGames.SM.Engine.deliverForgeEGen CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE;
    unfold CryptoGames.SM.Engine.deliverForgeEGen CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 abortE] <;>
  (simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
   split_ifs
   · refine ⟨rfl, fun _ h => ?_⟩
     simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
     subst h; exact hEs
   · rcases es.g.inTransit P.other c with _ | r
     · refine ⟨rfl, fun _ h => ?_⟩
       simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
       subst h; exact hEs
     · dsimp only
       split_ifs
       · refine ⟨rfl, fun _ h => ?_⟩
         simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
         subst h; exact hEs
       · have hvr := CryptoVerification.LibsignalSession.Fig8SchemeBridge.vRecv_localCKA_eq hAg es.g P (es.g.st P) c' none es.h (hEs P)
         simp only [run_liftH_bind, hvr.1]
         refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_,
           fun res hmem => ?_⟩
         · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
           · rfl
           · rfl
           · dsimp only
             split_ifs with hqep htriv
             · rfl
             · simp only [StateT.run_bind]
               rw [(CryptoVerification.LibsignalSession.Fig8SchemeBridge.commitE_localCKA_eq hAg es.g P (es.g.st P) st'
                 ⟨P.other, t', i'⟩ { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
             · rfl
             · rfl
         · rw [mem_support_bind_iff] at hmem
           obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
           rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
           · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
           · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
             subst hmem; exact hEs
           · dsimp only at hmem
             split_ifs at hmem with hqep htriv
             · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
               subst hmem; exact hEs
             · rw [StateT.run_bind, mem_support_bind_iff] at hmem
               obtain ⟨⟨cmRes, es₁⟩, hcmMem, hmem⟩ := hmem
               have hcm := (CryptoVerification.LibsignalSession.Fig8SchemeBridge.commitE_localCKA_eq hAg es.g P (es.g.st P) st'
                 ⟨P.other, t', i'⟩ { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
               rcases cmRes with _ | s₁
               · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                 subst hmem; intro Q; dsimp [CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv] at *
                 rw [hcm.1]; exact hEs Q
               · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                   support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hcm.2 s₁ rfl
             · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
             · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
               subst hmem; exact hEs)

omit [Zero Pt] [SampleableType Pt] in
private lemma implEDFShiftedPaper_localCKA_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS RSt SS RS M E σV ssV rsV : Type} [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS DDHSt Pt RSt SS RS M E (BitVec 256) DDHSt σV ssV rsV}
    (hAg : CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree (fun P γ t => CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P t γ) hk₁ hk₂)
    (b1 : Bool) (l Δ qep maxSkip tStar : ℕ) (cfg : CryptoGames.SM.Config M) (π : Policy)
    (es : EState (VP DDHSt Pt σV ssV rsV) M (Header Pt × E) HS)
    (t : (CryptoGames.SM.specDF (PartyState DDHSt Pt RSt SS RS) M (BitVec 256) (Header Pt × E)).Domain)
    (hEs : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv es) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₁ Δ qep maxSkip tStar cfg π (.inr t)).run es =
      (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₂ Δ qep maxSkip tStar cfg π (.inr t)).run es ∧
    ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₂ Δ qep maxSkip tStar cfg π
        (.inr t)).run es),
      CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv res.2 := by
  rcases t with ((t3 | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.implE_localCKA_eq hAg Δ qep maxSkip cfg π es (.inl (.inl t3)) hEs
  · cases b1
    · exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.implE_localCKA_eq hAg Δ qep maxSkip cfg π es (.inl (.inr (P, c))) hEs
    · change (CryptoGames.SM.Construction.DeliverForge.injectEB1 hk₁ qep tStar cfg (P, c)).run es =
          (CryptoGames.SM.Construction.DeliverForge.injectEB1 hk₂ qep tStar cfg (P, c)).run es ∧
        ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.injectEB1 hk₂ qep tStar cfg (P, c)).run es),
          CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv res.2
      unfold CryptoGames.SM.Construction.DeliverForge.injectEB1 abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs
      · refine ⟨rfl, fun _ h => ?_⟩
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        subst h; exact hEs
      · have hvr := CryptoVerification.LibsignalSession.Fig8SchemeBridge.vRecv_localCKA_eq hAg es.g P (es.g.st P) c none es.h (hEs P)
        simp only [run_liftH_bind, hvr.1]
        refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_,
          fun res hmem => ?_⟩
        · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · rfl
          · rfl
          · dsimp only
            split_ifs with hqep htriv
            · rfl
            · simp only [StateT.run_bind]
              rw [(CryptoVerification.LibsignalSession.Fig8SchemeBridge.commitE_localCKA_eq hAg es.g P (es.g.st P) st'
                ⟨P.other, t', i'⟩ { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
            · rfl
            · rfl
        · rw [mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
            subst hmem; exact hEs
          · dsimp only at hmem
            split_ifs at hmem with hqep htriv
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hEs
            · rw [StateT.run_bind, mem_support_bind_iff] at hmem
              obtain ⟨⟨cmRes, es₁⟩, hcmMem, hmem⟩ := hmem
              have hcm := (CryptoVerification.LibsignalSession.Fig8SchemeBridge.commitE_localCKA_eq hAg es.g P (es.g.st P) st'
                ⟨P.other, t', i'⟩ { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
              rcases cmRes with _ | s₁
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; intro Q; dsimp [CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv] at *; rw [hcm.1]; exact hEs Q
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hcm.2 s₁ rfl
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hEs
  · change (CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l hk₁ π P).run es =
        (CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l hk₂ π P).run es ∧
      ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l hk₂ π P).run es),
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv res.2
    refine ⟨by unfold CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper; rw [hAg.reveal_eq], fun res hmem => ?_⟩
    unfold CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
      subst hmem; exact hEs
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases hdoom : (π.leakDoom es.g (CryptoGames.SM.Construction.DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hEs
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
        rcases revRes with _ | stP
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; intro Q
          simpa [CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv, afterCorrShifted_st_eq] using hEs Q
  · exact deliverForgeEGen_localCKA_eq hAg b1 Δ qep tStar cfg P c c' es hEs

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_implEDFShiftedPaper_localCKA_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS RSt SS RS M E σV ssV rsV α : Type} [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS DDHSt Pt RSt SS RS M E (BitVec 256) DDHSt σV ssV rsV}
    (hAg : CryptoVerification.LibsignalSession.Fig8SchemeBridge.HooksLocalCKAAgree (fun P γ t => CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P t γ) hk₁ hk₂)
    (b1 : Bool) (l Δ qep maxSkip tStar : ℕ) (cfg : CryptoGames.SM.Config M) (π : Policy)
    (oa : OracleComp (unifSpec + CryptoGames.SM.specDF (PartyState DDHSt Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)) α)
    (es : EState (VP DDHSt Pt σV ssV rsV) M (Header Pt × E) HS)
    (hEs : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv es) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₁ Δ qep maxSkip tStar cfg π) oa).run es =
      (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₂ Δ qep maxSkip tStar cfg π) oa).run es := by
  induction oa using OracleComp.inductionOn generalizing es with
  | pure x => rfl
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · change (coinsE n).run es >>= _ = (coinsE n).run es >>= _
      simp only [coinsE, StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u es hEs
    · obtain ⟨hEq, hInv⟩ := implEDFShiftedPaper_localCKA_eq hAg b1 l Δ qep maxSkip tStar cfg π es t_sm hEs
      change (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₁ Δ qep maxSkip tStar cfg π (.inr t_sm)).run es >>= _ =
        (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l hk₂ Δ qep maxSkip tStar cfg π (.inr t_sm)).run es >>= _
      rw [hEq]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem =>
        ih u es' (hInv _ hmem)

omit [Zero Pt] [SampleableType Pt] in
private lemma implEDFShiftedPaper_hooksFS_ext_skippedLenLe
    {KC Γ CCoins I KR RSt M C : Type} [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I]
    {K MK : Type} [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header Pt) M C) (G : ℕ → PRGScheme K (K × MK))
    (l maxSkip k Δcka qep tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode) (cfg : CryptoGames.SM.Config M) (π : Policy)
    (j : ℕ)
    (es : EState (VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK))) M (Header Pt × (ℕ × C))
      (FSState Pt RSt K I (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (q : (CryptoGames.SM.specDF (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header Pt × (ℕ × C))).Domain)
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header Pt) M (ℕ × C))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FsAtomicBSwap.OptSkippedLenLe (es.h.ext.map Prod.snd))
    (hSt : FsAtomicBSwap.SkippedLenLe st.receiverState) :
    ∀ z ∈ support ((simulateQ (CryptoGames.SM.Construction.fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
        ((CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
          (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (2 + Δcka) qep maxSkip tStar cfg π (.inr q)).run es)).run st),
      FsAtomicBSwap.OptSkippedLenLe (z.1.2.h.ext.map Prod.snd) := by
  have hCommitEq : ∀ s₀ P₀ old₀ new₀ pos₀ (es₀ : EState _ M (Header Pt × (ℕ × C)) _),
      (commitE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        s₀ P₀ old₀ new₀ pos₀).run es₀ = pure (some (s₀.accept P₀ new₀ pos₀), es₀) := by
    intros; unfold commitE CryptoGames.SM.Engine.liftH hooksFS; simp [StateT.run]; rfl
  intro z hz
  rcases q with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((transmitE _ _ _ _ (P, m, r)).run es) at hmem
    unfold transmitE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt
    · rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [hep] at hmem; split_ifs at hmem
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt
        · simp only [run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hext' := vSend_ext_snd cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka mo j s₁ P (s₁.st P) m none r es.h (vsRes, h') hvs
          rcases vsRes with _ | ⟨stP, ct⟩ <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((challE _ _ _ _ _ (P, m₀, m₁, r)).run es) at hmem
    unfold challE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !(cfg.challAllowedIn (s₁.epoch P)))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hdoom : π.leakDoom es.g s₁
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
            have hext' := vSend_ext_snd cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r es.h (vsRes, h') hvs
            rcases vsRes with _ | ⟨stP, ct⟩ <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((deliverE _ maxSkip _ (P, c)).run es) at hmem
    unfold deliverE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt
    · rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hExt' := FsAtomicBSwap.vRecv_ext_skippedLenLe cka prng ae G maxSkip k Δcka mo j
          es.g P (es.g.st P) c (some r) es.h (hVR P) hExt (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨stP, t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · split_ifs at hmem <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; exact hExt')
        · simp only [StateT.run_bind, hCommitEq, pure_bind, StateT.run_modify, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((CryptoGames.SM.Engine.injectEGen b1 _ (2 + Δcka) qep tStar cfg (P, c)).run es) at hmem
    cases b1 <;> [unfold CryptoGames.SM.Engine.injectEGen injectE abortE at hmem;
      unfold CryptoGames.SM.Engine.injectEGen CryptoGames.SM.Construction.DeliverForge.injectEB1 abortE at hmem] <;>
    (simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
     split_ifs at hmem
     · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
       rcases hmem with ⟨_, rfl⟩; exact hExt
     · simp only [run_liftH_bind, mem_support_bind_iff] at hmem
       obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
       have hExt' := FsAtomicBSwap.vRecv_ext_skippedLenLe cka prng ae G maxSkip k Δcka mo j
         es.g P (es.g.st P) c none es.h (hVR P) hExt (vrRes, h') hvr
       rcases vrRes with _ | _ | ⟨stP, t', i', m'⟩
       · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
         rcases hmem with ⟨_, rfl⟩; exact hExt'
       · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
         rcases hmem with ⟨_, rfl⟩; exact hExt'
       · dsimp only at hmem
         split_ifs at hmem
         · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
           rcases hmem with ⟨_, rfl⟩; exact hExt'
         · simp only [StateT.run_bind, hCommitEq, pure_bind, StateT.run_modify, StateT.run_pure,
             support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
           rcases hmem with ⟨_, rfl⟩; exact hExt'
         · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
           rcases hmem with ⟨_, rfl⟩; exact hExt'
         · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
           rcases hmem with ⟨_, rfl⟩; exact hExt')
  · change z ∈ support ((simulateQ (CryptoGames.SM.Construction.fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j) π P).run es)).run st) at hz
    unfold CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper abortE at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact hExt
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hdoom : (π.leakDoom es.g (CryptoGames.SM.Construction.DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hExt
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind] at hz
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨revRes, h'⟩, st'⟩, hrev, hz⟩ := hz
        have hExt' := FsAtomicBSwap.fsReveal_ext_skippedLenLe cka prng ae G maxSkip Δcka mo j
          es.g P (es.g.st P) es.h st hExt hSt ((revRes, h'), st') hrev
        rcases revRes with _ | stP <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz;
           subst hz; exact hExt')
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((CryptoGames.SM.Engine.deliverForgeEGen b1 _ (2 + Δcka) qep tStar cfg (P, c, c')).run es) at hmem
    cases b1 <;> [unfold CryptoGames.SM.Engine.deliverForgeEGen CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE at hmem;
      unfold CryptoGames.SM.Engine.deliverForgeEGen CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 abortE at hmem] <;>
    (simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at hmem
     split_ifs at hmem
     · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
       rcases hmem with ⟨_, rfl⟩; exact hExt
     · rcases htr : es.g.inTransit P.other c with _ | r
       · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
         rcases hmem with ⟨_, rfl⟩; exact hExt
       · simp only [htr] at hmem; split_ifs at hmem
         · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
           rcases hmem with ⟨_, rfl⟩; exact hExt
         · simp only [run_liftH_bind, mem_support_bind_iff] at hmem
           obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
           have hExt' := FsAtomicBSwap.vRecv_ext_skippedLenLe cka prng ae G maxSkip k Δcka mo j
             es.g P (es.g.st P) c' none es.h (hVR P) hExt (vrRes, h') hvr
           rcases vrRes with _ | _ | ⟨stP, t', i', m'⟩
           · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
             rcases hmem with ⟨_, rfl⟩; exact hExt'
           · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
             rcases hmem with ⟨_, rfl⟩; exact hExt'
           · dsimp only at hmem
             split_ifs at hmem
             · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
               rcases hmem with ⟨_, rfl⟩; exact hExt'
             · simp only [StateT.run_bind, hCommitEq, pure_bind, StateT.run_modify, StateT.run_pure,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
               rcases hmem with ⟨_, rfl⟩; exact hExt'
             · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
               rcases hmem with ⟨_, rfl⟩; exact hExt'
             · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
               rcases hmem with ⟨_, rfl⟩; exact hExt')

omit [Zero Pt] [SampleableType Pt] in
private lemma implEDFShiftedPaper_hooksFS_fsClamp_fsAtomicB_eq
    {KC Γ CCoins I KR RSt : Type} [DecidableEq I] [SampleableType CCoins] [SampleableType I]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (l B B0 B_q q' Δcka qep tStar : ℕ) (mo mo' : CryptoGames.SM.Construction.Mode) (j : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP Γ Pt RSt (Option SS256) (Option RS256)) (MsgPt ℓ) (Header Pt × Ct32)
      (FSState Pt RSt (BitVec 256) I SS256 RS256 Ct32))
    (t : (CryptoGames.SM.specDF (PartyState Γ Pt RSt SS256 RS256) (MsgPt ℓ) CCoins (Header Pt × Ct32)).Domain)
    (hBad : badSendMsgDF (St := PartyState Γ Pt RSt SS256 RS256) (Coins := CCoins)
      (C := Header Pt × Ct32) (fun m => atomicShortPubB m.1) (.inr t) = false)
    (hVR : SMVRInv (FSVROkStep maxForwardJumps) B_q (q' + 1) es.g)
    (hLen : SMVRInv (fun _ => FsAtomicBSwap.OptSkippedLenLe) B_q (q' + 1) es.g)
    (hExt : FSVROkStep maxForwardJumps (B_q - (q' + 1)) (es.h.ext.map Prod.snd))
    (hExtLen : FsAtomicBSwap.OptSkippedLenLe (es.h.ext.map Prod.snd)) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
      (hooksFS cka prng (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
      (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy (.inr t)).run es =
    (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
      (hooksFS cka prng
        (CryptoGames.SM.Construction.fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j)
      (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy (.inr t)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  have hCommit :
      commitE (hooksFS cka prng (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j) =
      commitE (hooksFS cka prng
        (CryptoGames.SM.Construction.fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j) := by
    unfold commitE hooksFS; rfl
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · dsimp only
        by_cases hdoom : mo'.policy.leakDoom es.g s₁ = true
        · simp [hdoom]
        · have hm : atomicShortPubB m.1 = true :=
            CryptoVerification.LibsignalSession.Fig8SchemeBridge.badSendMsg_transmit_false
              (ok := fun (x : MsgPt ℓ) => atomicShortPubB x.1)
              (badSendMsgDF_to_badSendMsg (fun m => atomicShortPubB m.1) (.inl (.inl (P, m, r))) hBad)
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
          exact congrArg (· >>= _)
            (FsAtomicBSwap.vSend_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 Δcka mo j
              s₁ P (s₁.st P) m none r hm es.h)
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es = (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    obtain ⟨hm₀, hm₁⟩ := CryptoVerification.LibsignalSession.Fig8SchemeBridge.badSendMsg_chall_false
      (badSendMsgDF_to_badSendMsg (fun m => atomicShortPubB m.1) (.inl (.inr (P, m₀, m₁, r))) hBad)
    have hm : atomicShortPubB (if es.g.b then m₁ else m₀).1 = true := by
      cases es.g.b <;> simp [hm₀, hm₁]
    unfold challE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · dsimp only
        by_cases hch : (!(s₁.safeCh (2 + Δcka) P) ||
            !((mo'.cfg (M := MsgPt ℓ)).challAllowedIn (s₁.epoch P))) = true
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          by_cases hdoom : mo'.policy.leakDoom es.g s₁ = true
          · simp [hdoom]
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
              CryptoVerification.LibsignalSession.Fig8SchemeBridge.mode_cfg_challMsg, Option.getD_none, run_liftH_bind,
              FsAtomicBSwap.vSend_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 Δcka mo j
                s₁ P (s₁.st P) (if es.g.b then m₁ else m₀) (some (m₀, m₁)) r hm es.h]
  · change (deliverE _ maxForwardJumps mo'.cfg (P, c)).run es =
      (deliverE _ maxForwardJumps mo'.cfg (P, c)).run es
    unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · rcases es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only
        simp only [run_liftH_bind,
          FsAtomicBSwap.vRecv_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0
            (B_q - (q' + 1)) Δcka mo j hkB es.g P (es.g.st P) c (some r) es.h
            (hVR P) (hLen P) hExt hExtLen, hCommit]
  · cases b1 <;> [
      (change (injectE _ (2 + Δcka) qep mo'.cfg (P, c)).run es =
         (injectE _ (2 + Δcka) qep mo'.cfg (P, c)).run es
       unfold injectE);
      (change (CryptoGames.SM.Construction.DeliverForge.injectEB1 _ qep tStar mo'.cfg (P, c)).run es =
         (CryptoGames.SM.Construction.DeliverForge.injectEB1 _ qep tStar mo'.cfg (P, c)).run es
       unfold CryptoGames.SM.Construction.DeliverForge.injectEB1)] <;>
    (simp only [StateT.run_bind, StateT.run_get, pure_bind]
     split_ifs
     · rfl
     · simp only [run_liftH_bind,
         FsAtomicBSwap.vRecv_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0
           (B_q - (q' + 1)) Δcka mo j hkB es.g P (es.g.st P) c none es.h
           (hVR P) (hLen P) hExt hExtLen, hCommit])
  · change (CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l _ mo'.policy P).run es =
      (CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l _ mo'.policy P).run es
    unfold CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper hooksFS; rfl
  · cases b1 <;> [
      (change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE _ (2 + Δcka) qep mo'.cfg (P, c, c')).run es =
         (CryptoGames.SM.Construction.DeliverForge.deliverForgeE _ (2 + Δcka) qep mo'.cfg (P, c, c')).run es
       unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE);
      (change (CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 _ qep tStar mo'.cfg (P, c, c')).run es =
         (CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 _ qep tStar mo'.cfg (P, c, c')).run es
       unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1)] <;>
    (simp only [StateT.run_bind, StateT.run_get, pure_bind]
     split_ifs
     · rfl
     · rcases es.g.inTransit P.other c with _ | r
       · rfl
       · dsimp only
         split_ifs
         · rfl
         · simp only [run_liftH_bind,
             FsAtomicBSwap.vRecv_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0
               (B_q - (q' + 1)) Δcka mo j hkB es.g P (es.g.st P) c' none es.h
               (hVR P) (hLen P) hExt hExtLen, hCommit])

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_implEDFShiftedPaper_fsClamp_fsAtomicB_eq
    {KC Γ CCoins I KR RSt α : Type} [DecidableEq I] [SampleableType CCoins] [SampleableType I]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L l B B0 B_q q Δcka qep tStar : ℕ) (mo mo' : CryptoGames.SM.Construction.Mode) (j : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : OracleComp (unifSpec + CryptoGames.SM.specDF (PartyState Γ Pt RSt SS256 RS256)
      (MsgPt ℓ) CCoins (Header Pt × Ct32)) α}
    (hoa : oa.IsQueryBoundP (ReductionDsl.isGameQuery
      (G := CryptoGames.SM.specDF (PartyState Γ Pt RSt SS256 RS256) (MsgPt ℓ) CCoins (Header Pt × Ct32))) q)
    (hSendOk : oa.IsQueryBoundP (fun t => badSendMsgDF (St := PartyState Γ Pt RSt SS256 RS256)
      (Coins := CCoins) (C := Header Pt × Ct32) (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP Γ Pt RSt (Option SS256) (Option RS256)) (MsgPt ℓ) (Header Pt × Ct32)
      (FSState Pt RSt (BitVec 256) I SS256 RS256 Ct32))
    (st : CryptoGames.FSAEAD.State SS256 RS256 (Header Pt) (MsgPt ℓ) Ct32)
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (FSVROkStep maxForwardJumps) B_q q es.g)
    (hLen : SMVRInv (fun _ => FsAtomicBSwap.OptSkippedLenLe) B_q q es.g)
    (hExt : FSVROkStep maxForwardJumps (B_q - q) (es.h.ext.map Prod.snd))
    (hExtLen : FsAtomicBSwap.OptSkippedLenLe (es.h.ext.map Prod.snd))
    (hSt : RSReach maxForwardJumps (B_q - q) st.receiverState)
    (hStLen : FsAtomicBSwap.SkippedLenLe st.receiverState) :
    (simulateQ (CryptoGames.SM.Construction.fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
        (hooksFS cka prng (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy) oa).run es)).run st =
    (simulateQ (CryptoGames.SM.Construction.fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
        (hooksFS cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy) oa).run es)).run st := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  induction oa using OracleComp.inductionOn generalizing q es st with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa; rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ := badSendMsgDF_query_bind_step (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      have hInl1 :
          (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
            (hooksFS cka prng (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
            (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl2 :
          (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
            (hooksFS cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
            (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy (.inl n)).run es =
          (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      obtain ⟨_, _, _, rfl⟩ := hmem1
      have hQbCoins := CryptoGames.SM.Construction.ReductionsQueries.qb_coinsE
        (CryptoGames.SM.Construction.ReductionsQueries.hQu_QFSDec SS256 RS256 Pt (MsgPt ℓ) Ct32) n es'
      have hSt' : RSReach maxForwardJumps (B_q - q) st'.receiverState := by
        simpa using receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps
          hQbCoins st hSt ((u, es'), st') hmem
      have hStLen' : FsAtomicBSwap.SkippedLenLe st'.receiverState :=
        FsAtomicBSwap.fsFullImpl_skippedLenLe ae G maxForwardJumps ((coinsE n).run es') st hStLen
          ((u, es'), st') hmem
      exact ih u q (hmx u) (hSendMx u) es' st' hInv hVR hLen hExt hExtLen hSt' hStLen'
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq0.resolve_left (by decide); omega⟩
      have hStep1 := implEDFShiftedPaper_hooksFS_fsClamp_fsAtomicB_eq b1 cka prng C ℓ encT idOf
        l B B0 B_q q' Δcka qep tStar mo mo' j hB0 es t_sm hBad hVR hLen hExt hExtLen
      have hStep2 :
          (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
            (hooksFS cka prng
              (CryptoGames.SM.Construction.fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
              Δcka mo j) (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy (.inr t_sm)).run es =
          (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
            (hooksFS cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
            (2 + Δcka) qep maxForwardJumps tStar mo'.cfg mo'.policy (.inr t_sm)).run es :=
        CryptoGames.SM.Construction.implEDFShiftedPaper_fsClamp_eq b1 cka prng ae G l maxForwardJumps B B_q q'
          Δcka qep tStar mo mo'.cfg mo'.policy j hB es t_sm hVR hExt
      rw [hStep1, hStep2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      have hInv' := CryptoGames.SM.Engine.implEDFShiftedPaper_inv b1
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        l mo'.cfg mo'.policy es t_sm hInv (u, es') hmem1
      have hVR' := CryptoGames.SM.Engine.implEDFShiftedPaper_vrInv b1
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        (hooksFS_vrInv_fromAEADPRG cka prng ae G maxForwardJumps Δcka mo j)
        l mo'.cfg mo'.policy es t_sm hInv hVR (u, es') hmem1
      have hLen' := CryptoGames.SM.Engine.implEDFShiftedPaper_vrInv b1
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        (FsAtomicBSwap.hooksFS_vrInv_skippedLenLe cka prng ae G maxForwardJumps Δcka mo j)
        l mo'.cfg mo'.policy es t_sm hInv hLen (u, es') hmem1
      have hBq : B_q - (q' + 1) + 1 ≤ B_q - q' := by have := hInv.1; omega
      have hExt' := (CryptoGames.SM.Construction.implEDFShiftedPaper_ext_snd_fromAEADPRG b1 cka prng ae G l
        maxForwardJumps (B_q - (q' + 1)) Δcka qep tStar mo mo'.cfg mo'.policy j es t_sm st
        (fun P _ _ hv => hVR P _ _ hv) hExt hSt ((u, es'), st') hmem).mono hBq
      have hExtLen' := implEDFShiftedPaper_hooksFS_ext_skippedLenLe b1 cka prng ae G l
        maxForwardJumps (B_q - (q' + 1)) Δcka qep tStar mo mo'.cfg mo'.policy j es t_sm st
        (fun P _ _ hv => hVR P _ _ hv) hExtLen hStLen ((u, es'), st') hmem
      have hQbStep := CryptoGames.SM.Construction.qb_implEDFShiftedPaper_inr_one
        (CryptoGames.SM.Construction.ReductionsQueries.hQu_QFSDec SS256 RS256 Pt (MsgPt ℓ) Ct32)
        (CryptoGames.SM.Construction.ReductionsQueries.hQt_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQch_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQcs_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQcr_QFSDec _ _ Pt _ _)
        b1 cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) l Δcka qep tStar mo mo'.cfg mo'.policy
        j t_sm es
      have hSt' : RSReach maxForwardJumps (B_q - q') st'.receiverState :=
        (receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps hQbStep st hSt
          ((u, es'), st') hmem).mono hBq
      have hStLen' : FsAtomicBSwap.SkippedLenLe st'.receiverState :=
        FsAtomicBSwap.fsFullImpl_skippedLenLe ae G maxForwardJumps _ st hStLen ((u, es'), st') hmem
      exact ih u q' (by simpa using hmx u) (hSendMx u) es' st' hInv' hVR' hLen' hExt' hExtLen' hSt' hStLen'

theorem prngAdvantage_redPRNGAuthDFShiftedPaperGen_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka qep l t : ℕ) (useSafeCh : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l t useSafeCh A) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t useSafeCh A) := by
  suffices hRed :
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l t useSafeCh A =
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t useSafeCh A by
    rw [hRed]
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery
      (G := CryptoGames.SM.specDF (PartyState DDHSt Pt (BitVec 256) SS256 RS256)
        (MsgPt ℓ) (BitVec 256) (Header Pt × Ct32))) qAdv := by
    refine hA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  let mo : CryptoGames.SM.Construction.Mode := ⟨useSafeCh, some (l - 1), t⟩
  let mo' : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hStep1 :
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l t useSafeCh A =
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l t useSafeCh A := by
    unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen CryptoGames.SM.Construction.DeliverForge.authSimDFShiftedPaperGen
      CryptoGames.SM.Construction.DeliverForge.engRunDFShiftedPaperGen
    refine congrArg (· >>= _) ?_
    have hInit :
        initPRNG (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) lam mo =
        initPRNG (dhScheme Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) lam mo := rfl
    change (initPRNG (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) lam mo).run {} >>= _ =
      (initPRNG (dhScheme Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) lam mo).run {} >>= _
    rw [hInit]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · rfl
    · have hAll : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv (M := MsgPt ℓ) (E := Header Pt × Ct32)
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } := by
        unfold initPRNG at hmem
        simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨kc, _, ⟨rtRes, _⟩, _, hmem⟩ := hmem
        rcases rtRes with _ | ⟨σ, k⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          cases hmem.1
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hmem
          rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
          exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.localPartyInv_mkParties Dh kc σ
            ((fsAtomicB C ℓ encT idOf B0).initSender k)
            ((fsAtomicB C ℓ encT idOf B0).initReceiver k)
      dsimp only
      exact congrArg (· >>= fun res => pure (some res))
        (simulateQ_implEDFShiftedPaper_localCKA_eq
          (CryptoVerification.LibsignalSession.Fig8SchemeBridge.hooksPRNG_localCKAAgree Dh (rootPRNG C.F encPt)
            (fsAtomicB C ℓ encT idOf B0) mo)
          (!useSafeCh) l (2 + Δcka) qep (fsAtomicB C ℓ encT idOf B0).maxSkip t
          (CryptoGames.SM.Config.auth t) mo'.policy A _ hAll)
  rw [hStep1]
  unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen CryptoGames.SM.Construction.DeliverForge.authSimDFShiftedPaperGen
    CryptoGames.SM.Construction.DeliverForge.engRunDFShiftedPaperGen
  refine congrArg (· >>= _) ?_
  have hInitEq :
      initPRNG (dhScheme Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) lam mo =
      initPRNG (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo := by
    unfold initPRNG fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  change (initPRNG (dhScheme Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) lam mo).run {} >>= _ =
    (initPRNG (dhScheme Dh) (rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo).run {} >>= _
  rw [hInitEq]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
    have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
      Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
    let es₀ : EState (VP DDHSt Pt (Option (BitVec 256)) SS256 RS256) (MsgPt ℓ) (Header Pt × Ct32)
        (PRNGState Pt (BitVec 256) (BitVec 256)) :=
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
    have hInv₀ : SMEngineInv (B_q + 1) B_q qAdv es₀.g :=
      (CryptoGames.SM.Engine.SMEngineInv.init _ false hB1 hBB).mono hqB
    have hVRHk := FsAtomicBSwap.hooksPRNG_vrInv_lFS (dhScheme Dh) (rootPRNG C.F encPt) C ℓ encT idOf mo
    have hVR₀ : SMVRInv (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB maxForwardJumps)
        B_q qAdv es₀.g := by
      intro P t₀ v hv
      unfold initPRNG at hmem
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨kc, _, ⟨rtRes, _⟩, _, hmem⟩ := hmem
      rcases rtRes with _ | ⟨σ, k⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        cases hmem.1
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
        cases P <;> simp only [es₀] at hv
        · split_ifs at hv
          · cases hv
            exact hVRHk.mono (Nat.zero_le _)
              (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
                ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
                (lChainPRG C.F) maxForwardJumps k)
        · cases hv
    dsimp only
    exact congrArg (· >>= fun res => pure (some res))
      (simulateQ_implEDFShiftedPaper_localFs_eq (mo' := mo')
        (FsAtomicBSwap.hooksPRNG_localFsAgree (dhScheme Dh) (rootPRNG C.F encPt) C ℓ encT idOf B0 mo)
        hVRHk hB0 hA' hSendOk es₀ hInv₀ hVR₀)

theorem fsaeadGame_redFSAuthDFShiftedPaperGen_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep j l t : ℕ) (useSafeCh : Bool)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep j l t useSafeCh A) =
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep j l t useSafeCh A) := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  let mo : CryptoGames.SM.Construction.Mode := ⟨useSafeCh, some (l - 1), t⟩
  let mo' : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery
      (G := CryptoGames.SM.specDF (PartyState DDHSt Pt (BitVec 256) SS256 RS256)
        (MsgPt ℓ) (BitVec 256) (Header Pt × Ct32))) qAdv := by
    refine hA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  have hStepCKA :
      CryptoGames.SM.Construction.runFSDFShiftedPaper (!useSafeCh) (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam l Δcka qep t mo mo' j false A =
      CryptoGames.SM.Construction.runFSDFShiftedPaper (!useSafeCh) (dhScheme Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam l Δcka qep t mo mo' j false A := by
    unfold CryptoGames.SM.Construction.runFSDFShiftedPaper CryptoGames.SM.Construction.DeliverForge.engRunDFShiftedPaperGen
    have hInit :
        initFS (dhSchemeFb Dh) (rootPRNG C.F encPt)
          (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam mo j =
        initFS (dhScheme Dh) (rootPRNG C.F encPt)
          (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam mo j := rfl
    rw [hInit]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · rfl
    · have hAll : CryptoVerification.LibsignalSession.Fig8SchemeBridge.AllPartiesInv (M := MsgPt ℓ) (E := Header Pt × Ct32)
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } := by
        unfold initFS at hmem
        simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨kr, _, kc, _, ⟨⟨σ, k, sid⟩, _⟩, _, ⟨ext, _⟩, _, hmem⟩ := hmem
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
        exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.localPartyInv_mkParties Dh kc σ
          (if ext then none else some ((CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)).initSender k))
          (if ext then none else some ((CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)).initReceiver k))
      dsimp only
      exact congrArg (· >>= fun res => pure (some res))
        (simulateQ_implEDFShiftedPaper_localCKA_eq
          (CryptoVerification.LibsignalSession.Fig8SchemeBridge.hooksFS_localCKAAgree Dh (rootPRNG C.F encPt)
            (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
          (!useSafeCh) l (2 + Δcka) qep
          (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)).maxSkip t mo'.cfg mo'.policy
          A _ hAll)
  unfold CryptoGames.FSAEAD.game CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen
  refine bind_congr fun b => bind_congr fun k => ?_
  dsimp only [StateT.run'_eq]
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc]
  let st₀ := CryptoGames.FSAEAD.initState (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) k b
  have hRun :
      (simulateQ (CryptoGames.SM.Construction.fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        (CryptoGames.SM.Construction.runFSDFShiftedPaper (!useSafeCh) (dhSchemeFb Dh) (rootPRNG C.F encPt)
          (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam l Δcka qep t mo mo' j false A)).run st₀ =
      (simulateQ (CryptoGames.SM.Construction.fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        (CryptoGames.SM.Construction.runFSDFShiftedPaper (!useSafeCh) (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam l Δcka qep t mo mo' j false A)).run st₀ := by
    rw [hStepCKA]
    have hSt₀ : RSReach maxForwardJumps 0 st₀.receiverState :=
      CryptoGames.SM.Engine.RSReach.init ae G maxForwardJumps k
    have hStLen₀ : FsAtomicBSwap.SkippedLenLe st₀.receiverState :=
      FsAtomicBSwap.skippedLenLe_init ae G maxForwardJumps k
    rw [CryptoGames.SM.Construction.runFSDFShiftedPaper_eq_bind_initFSRaw,
      CryptoGames.SM.Construction.runFSDFShiftedPaper_eq_bind_initFSRaw]
    have hInitEq1 :
        initFSRaw (dhScheme Dh) (rootPRNG C.F encPt)
          (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam mo j false =
        initFSRaw (dhScheme Dh) (rootPRNG C.F encPt)
          (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j false := by
      unfold initFSRaw CryptoGames.SM.Construction.fsClamp fsAtomicB; rfl
    have hInitEq2 :
        initFSRaw (dhScheme Dh) (rootPRNG C.F encPt)
          (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo j false =
        initFSRaw (dhScheme Dh) (rootPRNG C.F encPt)
          (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j false := by
      unfold initFSRaw lFS; rfl
    rw [hInitEq1, hInitEq2, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨es₀, st₁⟩ hmem₀ => ?_
    have hes₀ := fst_mem_support_of_mem_support_simulateQ_run _ _ st₀ hmem₀
    have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
    have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
      Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
    have ⟨hInv₀, _⟩ := initFSRaw_inv (dhScheme Dh) (rootPRNG C.F encPt)
      (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j false hqB hB1 hBB es₀ hes₀
    have ⟨hVR₀, hext₀⟩ := initFSRaw_vrInv_fromAEADPRG (dhScheme Dh) (rootPRNG C.F encPt) ae G
      maxForwardJumps lam mo j false B_q qAdv es₀ hes₀
    have hLen₀ := FsAtomicBSwap.initFSRaw_skippedLenLe (dhScheme Dh) (rootPRNG C.F encPt) ae G
      maxForwardJumps lam mo j false B_q qAdv es₀ hes₀
    have hExt₀ : FSVROkStep maxForwardJumps (B_q - qAdv) (es₀.h.ext.map Prod.snd) := by
      simp [hext₀, FSVROkStep]
    have hExtLen₀ : FsAtomicBSwap.OptSkippedLenLe (es₀.h.ext.map Prod.snd) := by
      simp [hext₀, FsAtomicBSwap.OptSkippedLenLe]
    have hSt₁ : RSReach maxForwardJumps (B_q - qAdv) st₁.receiverState :=
      (receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps
        (isQueryBoundP_initFSRaw_dec (dhScheme Dh) (rootPRNG C.F encPt)
          (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j false)
        st₀ hSt₀ (es₀, st₁) hmem₀).mono (Nat.zero_le _)
    have hStLen₁ : FsAtomicBSwap.SkippedLenLe st₁.receiverState :=
      FsAtomicBSwap.fsFullImpl_skippedLenLe ae G maxForwardJumps
        (initFSRaw (dhScheme Dh) (rootPRNG C.F encPt)
          (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j false) st₀ hStLen₀ (es₀, st₁) hmem₀
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hSim := simulateQ_implEDFShiftedPaper_fsClamp_fsAtomicB_eq (!useSafeCh) (dhScheme Dh)
      (rootPRNG C.F encPt) C ℓ encT idOf (B_q + 1) l B B0 B_q qAdv Δcka qep t mo mo' j hB hB0
      hA' hSendOk es₀ st₁ hInv₀.sm hVR₀ hLen₀ hExt₀ hExtLen₀ hSt₁ hStLen₁
    have hms1 : (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)).maxSkip = maxForwardJumps := rfl
    have hms2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
    rw [hms1, hms2, hSim]
  simp only [CryptoGames.SM.Construction.fsFullImpl, CryptoGames.SM.Construction.runFSDFShiftedPaper, mo, mo', st₀,
    CryptoGames.SM.Construction.Mode.cfg, CryptoGames.SM.Construction.Mode.policy, ↓reduceIte] at hRun
  rw [hRun]

omit [DecidableEq Pt] in
private lemma liftCShifted_mem_to_liftC {α : Type}
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ)
    (x : CryptoGames.CKA.AdversaryComp DDHSt (BitVec 256) Pt Pt α)
    (h : CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt)
    (sc : CryptoGames.CKA.GameState DDHSt Pt)
    {z : (α × CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt) × CryptoGames.CKA.GameState DDHSt Pt}
    (hz : z ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δ tStar)
      ((CryptoGames.SM.Construction.DeliverForge.liftCShifted x).run h)).run sc)) :
    ((z.1.1, ({} : CKAState Pt Pt)), z.2) ∈
      support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δ tStar)
        ((liftC x).run {})).run sc) := by
  simp only [CryptoGames.SM.Construction.DeliverForge.liftCShifted, liftC, StateT.run_lift, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz ⊢
  obtain ⟨⟨a, sc'⟩, ha, hz⟩ := hz
  rcases Prod.mk.inj hz with ⟨h1, rfl⟩
  rcases Prod.mk.inj h1 with ⟨rfl, _⟩
  exact ⟨_, ha, rfl⟩

omit [DecidableEq Pt] in
private lemma liftCShifted_corrQuery_support
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ) (P : Party)
    (h : CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt)
    (sc : CryptoGames.CKA.GameState DDHSt Pt) (hsc : CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv sc)
    {z : (Option DDHSt × CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt) × CryptoGames.CKA.GameState DDHSt Pt}
    (hz : z ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δ tStar)
      ((CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.corrQuery P)).run h)).run sc)) :
    z.2 = sc ∧ ∀ γ, z.1.1 = some γ → CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P (sc.epoch P) γ :=
  CryptoVerification.LibsignalSession.Fig8SchemeBridge.liftC_corrQuery_support Dh Δ tStar P {} sc hsc
    (liftCShifted_mem_to_liftC Dh Δ tStar _ h sc hz)

omit [DecidableEq Pt] in
private lemma liftCShifted_receiveQuery_support
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar : ℕ) (P : Party)
    (h : CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt)
    (sc : CryptoGames.CKA.GameState DDHSt Pt) (hsc : CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv sc)
    {z : (Option Unit × CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt) × CryptoGames.CKA.GameState DDHSt Pt}
    (hz : z ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δ tStar)
      ((CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.receiveQuery P)).run h)).run sc)) :
    CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv z.2 ∧
    (z.1.1 = none → z.2 = sc) ∧
    (z.1.1 = some () → z.2.epoch P = sc.epoch P + 1 ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) :=
  CryptoVerification.LibsignalSession.Fig8SchemeBridge.liftC_receiveQuery_support Dh Δ tStar P {} sc hsc
    (liftCShifted_mem_to_liftC Dh Δ tStar _ h sc hz)

omit [DecidableEq Pt] in
private lemma liftCShifted_sendFamily_support
    (Dh : DHFun (BitVec 256) Pt) (Δ tStar tH t : ℕ) (P : Party) (r : Option (BitVec 256))
    (h : CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt)
    (sc : CryptoGames.CKA.GameState DDHSt Pt) (hsc : CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv sc)
    {z : (Option (Pt × Pt) × CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt) × CryptoGames.CKA.GameState DDHSt Pt}
    (hz : z ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δ tStar)
      ((match r with
        | some c => CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.sendWithAdversaryCoinsQuery P c)
        | none =>
          if t = tH then CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.challQuery P)
          else CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.sendQuery P)).run h)).run sc)) :
    CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv z.2 ∧
    (∀ T' Ik, z.1.1 = some (T', Ik) →
      z.2.epoch P = sc.epoch P + 1 ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) := by
  have hz' : ((z.1.1, ({} : CKAState Pt Pt)), z.2) ∈
      support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δ tStar)
        ((match r with
          | some c => liftC (CryptoGames.CKA.sendWithAdversaryCoinsQuery P c)
          | none =>
            if t = tH then liftC (CryptoGames.CKA.challQuery P)
            else liftC (CryptoGames.CKA.sendQuery P)).run {})).run sc) := by
    rcases r with _ | c
    · by_cases ht : t = tH <;> simp only [ht, ↓reduceIte] at hz ⊢ <;>
        exact liftCShifted_mem_to_liftC Dh Δ tStar _ h sc hz
    · exact liftCShifted_mem_to_liftC Dh Δ tStar _ h sc hz
  exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.liftC_sendFamily_support Dh Δ tStar tH t P r {} sc hsc hz'

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private def startSendContShifted {KR RSt K SS RS M E : Type}
    (prng : PRFPRNG KR RSt Pt K) (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (l : ℕ) (P : Party) (t : ℕ) (σ : RSt) :
    Option (Pt × Pt) →
      HM (CryptoGames.CKA.spec DDHSt (BitVec 256) Pt Pt) (CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt)
        (Option (Option DDHSt × Pt × RSt × SS))
  | none => pure none
  | some (T', Ik) => do
    CryptoGames.SM.Construction.DeliverForge.cacheCShifted t (T', Ik)
    let p := prng.up σ Ik
    if l + 2 ≤ t then
      match ← CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.corrQuery P) with
      | none => pure none
      | some γ => pure (some (some γ, T', p.1, fs.initSender p.2))
    else if t + 1 ≤ l then
      match ← CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.corrQuery P) with
      | none => pure none
      | some γ => do
        CryptoGames.SM.Construction.DeliverForge.setγPreShifted P (some γ)
        pure (some (none, T', p.1, fs.initSender p.2))
    else pure (some (none, T', p.1, fs.initSender p.2))

omit [SampleableType Pt] in
private lemma startSend_hooksCKAShifted_none_eq {KR RSt K SS RS M E : Type}
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (l tStarH : ℕ)
    (ctx : Ctx (Option DDHSt) Pt RSt SS RS M E) (P : Party) (t : ℕ) (σ : RSt)
    (r : Option (BitVec 256)) :
    (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH).startSend
        ctx P t (none : Option DDHSt) σ r =
      ((match r with
        | some c => CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.sendWithAdversaryCoinsQuery P c)
        | none =>
          if t = l + 1 then CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.challQuery P)
          else CryptoGames.SM.Construction.DeliverForge.liftCShifted (CryptoGames.CKA.sendQuery P)) >>=
        startSendContShifted prng fs l P t σ) := by
  apply StateT.ext; intro h₀
  rcases r with _ | c <;> dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted]
  · by_cases ht : t = l + 1
    · have hite : ∀ {α : Type} (x y : α), (if t = l + 1 then x else y) = x :=
        fun _ _ => by simp only [ht, ↓reduceIte]
      rw [hite, hite, StateT.run_bind, StateT.run_bind]
      congr 1; ext ⟨ans, s'⟩; rcases ans with _ | ⟨T', Ik⟩
      · rfl
      · dsimp only [startSendContShifted]
        simp only [CryptoGames.SM.Construction.DeliverForge.cacheCShifted, StateT.run_bind, StateT.run_modify, pure_bind]
        split_ifs
        · simp only [StateT.run_bind]
          congr 1; ext ⟨corrAns, s''⟩; rcases corrAns with _ | γ <;> simp only [StateT.run_pure]
        · simp only [StateT.run_bind]
          congr 1; ext ⟨corrAns, s''⟩; rcases corrAns with _ | γ
          · simp only [StateT.run_pure]
          · simp only [CryptoGames.SM.Construction.DeliverForge.setγPreShifted, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind]
        · simp only [StateT.run_pure]
    · have hite : ∀ {α : Type} (x y : α), (if t = l + 1 then x else y) = y :=
        fun _ _ => by simp only [ht, ↓reduceIte]
      rw [hite, hite, StateT.run_bind, StateT.run_bind]
      congr 1; ext ⟨ans, s'⟩; rcases ans with _ | ⟨T', Ik⟩
      · rfl
      · dsimp only [startSendContShifted]
        simp only [CryptoGames.SM.Construction.DeliverForge.cacheCShifted, StateT.run_bind, StateT.run_modify, pure_bind]
        split_ifs
        · simp only [StateT.run_bind]
          congr 1; ext ⟨corrAns, s''⟩; rcases corrAns with _ | γ <;> simp only [StateT.run_pure]
        · simp only [StateT.run_bind]
          congr 1; ext ⟨corrAns, s''⟩; rcases corrAns with _ | γ
          · simp only [StateT.run_pure]
          · simp only [CryptoGames.SM.Construction.DeliverForge.setγPreShifted, StateT.run_bind, StateT.run_modify,
              StateT.run_pure, pure_bind]
        · simp only [StateT.run_pure]
  · rw [StateT.run_bind, StateT.run_bind]
    congr 1; ext ⟨ans, s'⟩; rcases ans with _ | ⟨T', Ik⟩
    · rfl
    · dsimp only [startSendContShifted]
      simp only [CryptoGames.SM.Construction.DeliverForge.cacheCShifted, StateT.run_bind, StateT.run_modify, pure_bind]
      split_ifs
      · simp only [StateT.run_bind]
        congr 1; ext ⟨corrAns, s''⟩; rcases corrAns with _ | γ <;> simp only [StateT.run_pure]
      · simp only [StateT.run_bind]
        congr 1; ext ⟨corrAns, s''⟩; rcases corrAns with _ | γ
        · simp only [StateT.run_pure]
        · simp only [CryptoGames.SM.Construction.DeliverForge.setγPreShifted, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, pure_bind]
      · simp only [StateT.run_pure]

private lemma vSend_ckaSync_shifted {KR RSt K SS RS M E : Type} [SampleableType K] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δgame tStarGame l tStarH : ℕ)
    (ctx : Ctx (Option DDHSt) Pt RSt SS RS M E) (P : Party)
    (s : VP (Option DDHSt) Pt RSt SS RS) (m : M)
    (pair : Option (M × M)) (r : Option (BitVec 256))
    (h : CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt)
    (sc : CryptoGames.CKA.GameState DDHSt Pt)
    (hsc : CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv sc) (hs : CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc P s) :
    (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((vSend (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH)
        ctx P s m pair r).run h)).run sc =
    (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((vSend (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
        ctx P s m pair r).run h)).run sc ∧
    ∀ z ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((vSend (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
        ctx P s m pair r).run h)).run sc),
      CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv z.2 ∧
      (∀ st' ct, z.1.1 = some (st', ct) →
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync z.2 P st' ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q) := by
  have hStep1 :
      (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
        ((CryptoGames.SM.Engine.vSendStep1
          (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH) ctx P s r).run h)).run sc =
      (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
        ((CryptoGames.SM.Engine.vSendStep1
          (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH) ctx P s r).run h)).run sc ∧
      ∀ w ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
        ((CryptoGames.SM.Engine.vSendStep1
          (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH) ctx P s r).run h)).run sc),
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv w.2 ∧
        (∀ s₁, w.1.1 = some s₁ →
          CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync w.2 P s₁ ∧ ∀ Q, Q ≠ P → w.2.epoch Q = sc.epoch Q) := by
    unfold CryptoGames.SM.Engine.vSendStep1
    by_cases hSend : s.id.sendsIn (s.tcur + 1) = true
    · have hPSend : P.sendsIn (s.tcur + 1) = true := hs.1 ▸ hSend
      simp only [hSend, ↓reduceIte]
      rcases hγ : s.γ with _ | γ
      · have hPull :=
          startSend_hooksCKAShifted_none_eq Dh prng fs l tStarH
            ctx P (s.tcur + 1) s.root r
        have hEqStart :
            (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH).startSend
              ctx P (s.tcur + 1) none s.root r =
            (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH).startSend
              ctx P (s.tcur + 1) none s.root r := rfl
        rw [hEqStart]
        refine ⟨rfl, fun w hw => ?_⟩
        rw [hPull, bind_assoc] at hw
        rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
        obtain ⟨⟨⟨ans, h₁⟩, sc₁⟩, hans, hw⟩ := hw
        have ⟨hsc₁, hep₁⟩ :=
          liftCShifted_sendFamily_support Dh Δgame tStarGame (l + 1) (s.tcur + 1) P r h sc hsc hans
        have hstcur : s.tcur = sc.epoch P := by have h2 := hs.2; rw [hγ] at h2; exact h2
        rcases ans with _ | ⟨T', Ik⟩
        · dsimp only [startSendContShifted] at hw
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hw
          subst hw; exact ⟨hsc₁, fun _ hEq => nomatch hEq⟩
        · have ⟨hepP, hepQ⟩ := hep₁ T' Ik rfl
          dsimp only at hsc₁ hepP hepQ
          dsimp only [startSendContShifted] at hw
          simp only [CryptoGames.SM.Construction.DeliverForge.cacheCShifted, bind_assoc, StateT.run_bind, StateT.run_modify,
            pure_bind] at hw
          by_cases hfin : l + 2 ≤ s.tcur + 1
          · simp only [hfin, ↓reduceIte] at hw
            rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind,
              mem_support_bind_iff] at hw
            obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hw⟩ := hw
            have ⟨hsc₂_eq, hRole₂⟩ :=
              liftCShifted_corrQuery_support Dh Δgame tStarGame P _ sc₁ hsc₁ hcorr
            dsimp only at hsc₂_eq hRole₂; subst hsc₂_eq
            rcases corrAns with _ | γ'
            · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw
              subst hw; exact ⟨hsc₁, fun _ hEq => nomatch hEq⟩
            · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hw
              subst hw
              refine ⟨hsc₁, fun s₁ hs₁ => ?_⟩
              dsimp at hs₁; cases hs₁
              have hR : CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P (s.tcur + 1) γ' := by
                rw [hstcur, ← hepP]; exact hRole₂ γ' rfl
              exact ⟨⟨hs.1, hR⟩, hepQ⟩
          · simp only [hfin, ↓reduceIte] at hw
            by_cases hpre : (s.tcur + 1) + 1 ≤ l
            · simp only [hpre, ↓reduceIte] at hw
              rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind,
                mem_support_bind_iff] at hw
              obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hw⟩ := hw
              have ⟨hsc₂_eq, _⟩ :=
                liftCShifted_corrQuery_support Dh Δgame tStarGame P _ sc₁ hsc₁ hcorr
              dsimp only at hsc₂_eq; subst hsc₂_eq
              rcases corrAns with _ | γ'
              · simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hw
                subst hw; exact ⟨hsc₁, fun _ hEq => nomatch hEq⟩
              · simp only [CryptoGames.SM.Construction.DeliverForge.setγPreShifted, StateT.run_bind,
                  StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hw
                subst hw
                refine ⟨hsc₁, fun s₁ hs₁ => ?_⟩
                dsimp at hs₁; cases hs₁
                exact ⟨⟨hs.1, by dsimp; omega⟩, hepQ⟩
            · simp only [hpre, ↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure,
                support_pure, Set.mem_singleton_iff] at hw
              subst hw
              refine ⟨hsc₁, fun s₁ hs₁ => ?_⟩
              dsimp at hs₁; cases hs₁
              exact ⟨⟨hs.1, by dsimp; omega⟩, hepQ⟩
      · dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted]
        have hRole : CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P s.tcur γ := by
          have h2 := hs.2; rw [hγ] at h2; exact h2
        have hCoinsEq : ∀ coins : BitVec 256,
            (dhSchemeFb Dh).send γ coins = (dhScheme Dh).send γ coins ∧
              CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P (s.tcur + 1) ((dhScheme Dh).send γ coins).1 :=
          fun coins => CryptoVerification.LibsignalSession.Fig8SchemeBridge.dhSchemeFb_send_of_roleOk Dh hRole hPSend coins
        rcases r with _ | c
        · simp only [StateT.run_bind, StateT.run_lift, CryptoGames.SM.Construction.DeliverForge.cacheCShifted,
            StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind,
            simulateQ_pure]
          refine ⟨bind_congr fun p => by rw [(hCoinsEq p.1).1], fun w hw => ?_⟩
          rw [sampleT, CryptoVerification.LibsignalSession.Fig8SchemeBridge.simulateQ_ckaFullImpl_liftProb] at hw
          simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hw
          obtain ⟨coins, _, hw⟩ := hw
          subst hw
          refine ⟨hsc, fun s₁ hs₁ => ?_⟩
          dsimp at hs₁; cases hs₁
          exact ⟨⟨hs.1, (hCoinsEq coins).2⟩, fun _ _ => rfl⟩
        · simp only [pure_bind, (hCoinsEq c).1, CryptoGames.SM.Construction.DeliverForge.cacheCShifted, StateT.run_bind,
            StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff]
          refine ⟨trivial, fun w hw => ?_⟩
          subst hw
          refine ⟨hsc, fun s₁ hs₁ => ?_⟩
          dsimp at hs₁; cases hs₁
          exact ⟨⟨hs.1, (hCoinsEq c).2⟩, fun _ _ => rfl⟩
    · simp only [hSend, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff]
      refine ⟨trivial, fun w hw => ?_⟩
      subst hw
      exact ⟨hsc, fun s₁ hs₁ => by dsimp at hs₁; cases hs₁; exact ⟨hs, fun _ _ => rfl⟩⟩
  rw [CryptoGames.SM.Engine.vSend_eq_bind, CryptoGames.SM.Engine.vSend_eq_bind, StateT.run_bind, StateT.run_bind,
    simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, hStep1.1]
  have hFsEq :
      (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH).fsSend =
      (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH).fsSend := rfl
  rw [hFsEq]
  refine ⟨rfl, fun z hz => ?_⟩
  rw [mem_support_bind_iff] at hz
  obtain ⟨⟨⟨s₁?, h₁⟩, sc₁⟩, hw, hz⟩ := hz
  have ⟨hsc₁, hs₁Sync⟩ := hStep1.2 _ hw
  rcases s₁? with _ | s₁
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact ⟨hsc₁, fun _ _ hEq => by cases hEq⟩
  · have ⟨hs₁P, hepQ⟩ := hs₁Sync s₁ rfl
    rcases hvS : s₁.vS with _ | v
    · simp only [hvS, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨hsc₁, fun _ _ hEq => by cases hEq; exact ⟨hs₁P, hepQ⟩⟩
    · simp only [hvS, CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted, pure_bind, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨hsc₁, fun _ _ hEq => by cases hEq; exact ⟨hs₁P, hepQ⟩⟩

omit [SampleableType Pt] in
private lemma vRecv_hooksCKAShifted_pure_eq {KR RSt K SS RS M E : Type}
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (l tStarH : ℕ)
    (ctx : Ctx (Option DDHSt) Pt RSt SS RS M E) (P : Party)
    (s : VP (Option DDHSt) Pt RSt SS RS) (c : Header Pt × E)
    (rec_ : Option (CryptoGames.SM.Record M (Header Pt × E)))
    (h : CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt)
    (sc : CryptoGames.CKA.GameState DDHSt Pt) (hs : CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc P s) :
    (vRecv (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH) ctx P s c rec_).run h =
      (vRecv (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH) ctx P s c rec_).run h ∧
    ∃ out,
      (vRecv (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH) ctx P s c rec_).run h =
        pure out ∧
      ∀ st' t' i' m', out.1 = some (some (st', t', i', m')) →
        st'.id = P ∧
        (((s.tcur < st'.tcur && s.γ.isNone) = false ∧ CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc P st') ∨
         ((s.tcur < st'.tcur && s.γ.isNone) = true ∧ st'.γ = none ∧ st'.tcur = sc.epoch P + 1)) := by
  rw [CryptoGames.SM.Engine.vRecv_eq_bind, CryptoGames.SM.Engine.vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp only [href, ↓reduceIte, StateT.run_pure]
    exact ⟨trivial, _, rfl, fun _ _ _ _ hEq => by cases hEq⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hNotSend : s.id.sendsIn c.1.1 = false :=
      (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr href)).1
    have hStep1 :
        ∃ out1,
          (CryptoGames.SM.Engine.vRecvStep1
            (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH) ctx P s c).run h =
            pure out1 ∧
          (CryptoGames.SM.Engine.vRecvStep1
            (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH) ctx P s c).run h =
            pure out1 ∧
          ∀ s₁, out1.1 = some (some s₁) →
            s₁.id = P ∧
            (((s.tcur < s₁.tcur && s.γ.isNone) = false ∧ CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc P s₁) ∨
             ((s.tcur < s₁.tcur && s.γ.isNone) = true ∧ s₁.γ = none ∧
              s₁.tcur = sc.epoch P + 1)) := by
      unfold CryptoGames.SM.Engine.vRecvStep1
      by_cases ht : c.1.1 = s.tcur + 1
      · simp only [ht, ↓reduceIte]
        rcases hTn : c.1.2 with _ | Tn
        · exact ⟨_, StateT.run_pure _ _, StateT.run_pure _ _, fun _ hEq => by cases hEq⟩
        · have hPRecv : P.sendsIn (s.tcur + 1) = false := by
            rw [← hs.1, ← ht]; exact hNotSend
          dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted]
          simp only [StateT.run_bind, StateT.run_get, pure_bind]
          have hMapEq :
              (s.γ.map fun γ => ((dhSchemeFb Dh).receive γ Tn).1) =
                (s.γ.map fun γ => ((dhScheme Dh).receive γ Tn).1) := by
            rcases hγ : s.γ with _ | γ
            · rfl
            · have hRole : CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P s.tcur γ := by
                have h2 := hs.2; rw [hγ] at h2; exact h2
              exact congrArg (fun p => some p.1)
                (CryptoVerification.LibsignalSession.Fig8SchemeBridge.dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn).1
          rcases hcache : h.base.cache (s.tcur + 1) with _ | ⟨Tc, Ik⟩
          · dsimp only
            by_cases hauth : s.tcur + 1 = tStarH
            · simp only [hauth, ↓reduceIte]
              rcases hγ : s.γ with _ | γ
              · simp only [StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
              · have hRole : CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P s.tcur γ := by
                  have h2 := hs.2; rw [hγ] at h2; exact h2
                have ⟨hEq, hRole'⟩ :=
                  CryptoVerification.LibsignalSession.Fig8SchemeBridge.dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                simp only [hEq, StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
                  dsimp at hs₁; cases hs₁
                  exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hauth ▸ hRole'⟩⟩⟩⟩
            · simp only [hauth, ↓reduceIte, StateT.run_pure, pure_bind]
              exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
          · dsimp only
            by_cases hTc : Tc = Tn
            · simp only [hTc, ↓reduceIte, hMapEq, StateT.run_pure, pure_bind]
              refine ⟨_, rfl, rfl, fun s₁ hs₁ => ?_⟩
              dsimp at hs₁; cases hs₁
              rcases hγ : s.γ with _ | γ
              · refine ⟨hs.1, Or.inr ⟨by simp, rfl, ?_⟩⟩
                have h2 := hs.2; rw [hγ] at h2; dsimp; omega
              · have hRole : CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P s.tcur γ := by
                  have h2 := hs.2; rw [hγ] at h2; exact h2
                have ⟨_, hRole'⟩ :=
                  CryptoVerification.LibsignalSession.Fig8SchemeBridge.dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hRole'⟩⟩⟩
            · simp only [hTc, ↓reduceIte]
              by_cases hauth : s.tcur + 1 = tStarH
              · simp only [hauth, ↓reduceIte]
                rcases hγ : s.γ with _ | γ
                · simp only [StateT.run_pure, pure_bind]
                  exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
                · have hRole : CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk P s.tcur γ := by
                    have h2 := hs.2; rw [hγ] at h2; exact h2
                  have ⟨hEq, hRole'⟩ :=
                    CryptoVerification.LibsignalSession.Fig8SchemeBridge.dhSchemeFb_receive_of_roleOk Dh hRole hPRecv Tn
                  simp only [hEq, StateT.run_pure, pure_bind]
                  exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
                    dsimp at hs₁; cases hs₁
                    exact ⟨hs.1, Or.inl ⟨by simp, ⟨hs.1, hauth ▸ hRole'⟩⟩⟩⟩
              · simp only [hauth, ↓reduceIte, StateT.run_pure, pure_bind]
                exact ⟨_, rfl, rfl, fun _ hEq => nomatch hEq⟩
      · simp only [ht, ↓reduceIte, StateT.run_pure]
        exact ⟨_, rfl, rfl, fun s₁ hs₁ => by
          dsimp at hs₁; cases hs₁; exact ⟨hs.1, Or.inl ⟨by simp, hs⟩⟩⟩
    obtain ⟨⟨s₁?, h₁⟩, hPureFb, hPureDh, hPost1⟩ := hStep1
    rw [hPureFb, hPureDh, pure_bind, pure_bind]
    rcases s₁? with _ | (_ | s₁)
    · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
    · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
    · dsimp only
      rcases hvR : s₁.vR c.1.1 with _ | v
      · rw [StateT.run_pure]
        exact ⟨rfl, _, rfl, fun _ _ _ _ hEq => nomatch hEq⟩
      · dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted]
        rw [pure_bind]
        rcases hrc : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
        · exact ⟨rfl, _, StateT.run_pure _ _, fun _ _ _ _ hEq => nomatch hEq⟩
        · exact ⟨rfl, _, StateT.run_pure _ _, fun st' _ _ _ hEq => by
            dsimp at hEq; cases hEq; exact hPost1 s₁ rfl⟩

private lemma commitE_ckaSync_shifted {KR RSt K SS RS M E : Type}
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δgame tStarGame l tStarH : ℕ)
    (s : Ctx (Option DDHSt) Pt RSt SS RS M E) (P : Party)
    (old new : VP (Option DDHSt) Pt RSt SS RS) (pos : CryptoGames.SM.Pos)
    (es : EState (VP (Option DDHSt) Pt RSt SS RS) M (Header Pt × E)
      (CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt))
    (sc : CryptoGames.CKA.GameState DDHSt Pt)
    (hsc : CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv sc)
    (hS : ∀ Q, CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc Q (s.st Q))
    (_hEs : es.abort = false → ∀ Q, CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc Q (es.g.st Q))
    (hNew : new.id = P ∧
      (((old.tcur < new.tcur && old.γ.isNone) = false ∧ CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc P new) ∨
       ((old.tcur < new.tcur && old.γ.isNone) = true ∧ new.γ = none ∧
        new.tcur = sc.epoch P + 1))) :
    (commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH)
      s P old new pos).run es =
    (commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
      s P old new pos).run es ∧
    ∀ z ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((commitE (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
        s P old new pos).run es)).run sc),
      CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv z.2 ∧
      (z.1.1 = none → CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync z.1.2 z.2) ∧
      (∀ s₁, z.1.1 = some s₁ → z.1.2.abort = es.abort ∧
        ∀ Q, CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync z.2 Q (s₁.st Q)) := by
  refine ⟨rfl, fun z hz => ?_⟩
  unfold commitE abortE at hz
  dsimp only [CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted] at hz
  rw [run_liftH_bind] at hz
  rcases hNew.2 with ⟨hCond, hSyncNew⟩ | ⟨hCond, hγNone, htcurNew⟩
  · rw [hCond] at hz
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; dsimp only
    refine ⟨hsc, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
    cases hs₁
    by_cases hQP : Q = P
    · subst hQP; simp [CryptoVerification.LibsignalSession.Fig8SchemeBridge.accept_st_eq, hSyncNew]
    · simp [Function.update_of_ne hQP, CryptoVerification.LibsignalSession.Fig8SchemeBridge.accept_st_eq, hS Q]
  · rw [hCond] at hz
    simp only [↓reduceIte] at hz
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨⟨rcvAns, h₁⟩, sc₁⟩, hrcv, hz⟩ := hz
    have ⟨hsc₁, _, hRcvOk⟩ :=
      liftCShifted_receiveQuery_support Dh Δgame tStarGame P es.h sc hsc hrcv
    rcases rcvAns with _ | ⟨⟩
    · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; dsimp only
      exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
    · have ⟨hepP, hepQ⟩ := hRcvOk rfl
      dsimp only at hsc₁ hepP hepQ
      by_cases hfin : l + 2 ≤ new.tcur
      · simp only [hfin, ↓reduceIte] at hz
        rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind,
          mem_support_bind_iff] at hz
        obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hz⟩ := hz
        have ⟨hsc₂_eq, hRole₂⟩ :=
          liftCShifted_corrQuery_support Dh Δgame tStarGame P h₁ sc₁ hsc₁ hcorr
        dsimp only at hsc₂_eq hRole₂; subst hsc₂_eq
        rcases corrAns with _ | γ'
        · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; dsimp only
          exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
        · simp only [StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz; dsimp only
          refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
          cases hs₁
          by_cases hQP : Q = P
          · subst hQP
            have hR : CryptoVerification.LibsignalSession.Fig8SchemeBridge.DdhRoleOk Q new.tcur γ' := by
              rw [htcurNew, ← hepP]; exact hRole₂ γ' rfl
            simp only [Function.update_self, CryptoVerification.LibsignalSession.Fig8SchemeBridge.accept_st_eq]
            exact ⟨hNew.1, hR⟩
          · simp only [Function.update_of_ne hQP, CryptoVerification.LibsignalSession.Fig8SchemeBridge.accept_st_eq]
            exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)
      · simp only [hfin, ↓reduceIte] at hz
        by_cases hpre : new.tcur + 1 ≤ l
        · simp only [hpre, ↓reduceIte] at hz
          rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind,
            mem_support_bind_iff] at hz
          obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hz⟩ := hz
          have ⟨hsc₂_eq, _⟩ :=
            liftCShifted_corrQuery_support Dh Δgame tStarGame P h₁ sc₁ hsc₁ hcorr
          dsimp only at hsc₂_eq; subst hsc₂_eq
          rcases corrAns with _ | γ'
          · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; dsimp only
            exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
          · simp only [CryptoGames.SM.Construction.DeliverForge.setγPreShifted, StateT.run_bind,
              StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hz
            subst hz; dsimp only
            refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
            cases hs₁
            by_cases hQP : Q = P
            · subst hQP
              simp only [Function.update_self, CryptoVerification.LibsignalSession.Fig8SchemeBridge.accept_st_eq]
              refine ⟨hNew.1, ?_⟩
              rw [hγNone, htcurNew, hepP]
            · simp only [Function.update_of_ne hQP, CryptoVerification.LibsignalSession.Fig8SchemeBridge.accept_st_eq]
              exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)
        · simp only [hpre, ↓reduceIte, StateT.run_pure, pure_bind, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz; dsimp only
          refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩
          cases hs₁
          by_cases hQP : Q = P
          · subst hQP
            simp only [Function.update_self, CryptoVerification.LibsignalSession.Fig8SchemeBridge.accept_st_eq]
            refine ⟨hNew.1, ?_⟩
            rw [hγNone, htcurNew, hepP]
          · simp only [Function.update_of_ne hQP, CryptoVerification.LibsignalSession.Fig8SchemeBridge.accept_st_eq]
            exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)

private lemma deliverForgeEGen_ckaSync_shifted {KR RSt K SS RS M E : Type}
    [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δgame tStarGame Δcka l tStarH qep tStar : ℕ)
    (cfg : CryptoGames.SM.Config M) (P : Party) (c c' : Header Pt × E)
    (es : EState (VP (Option DDHSt) Pt RSt SS RS) M (Header Pt × E)
      (CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt))
    (sc : CryptoGames.CKA.GameState DDHSt Pt)
    (hSync : CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync es sc) :
    (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Engine.deliverForgeEGen b1
        (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH)
        (2 + Δcka) qep tStar cfg (P, c, c')).run es)).run sc =
    (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Engine.deliverForgeEGen b1
        (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
        (2 + Δcka) qep tStar cfg (P, c, c')).run es)).run sc ∧
    ∀ z ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Engine.deliverForgeEGen b1
        (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
        (2 + Δcka) qep tStar cfg (P, c, c')).run es)).run sc),
      CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync z.1.2 z.2 := by
  cases b1 <;> [
    unfold CryptoGames.SM.Engine.deliverForgeEGen CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE;
    unfold CryptoGames.SM.Engine.deliverForgeEGen CryptoGames.SM.Construction.DeliverForge.deliverForgeEB1 abortE] <;>
  (simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
   by_cases hab : (es.abort || es.g.win) = true
   · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
       Set.mem_singleton_iff]
     exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
   · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
     simp only [hab, Bool.false_eq_true, ↓reduceIte]
     rcases htr : es.g.inTransit P.other c with _ | r
     · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
       exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
     · dsimp only
       by_cases href :
           ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
       · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
           Set.mem_singleton_iff]
         exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
       · simp only [href, Bool.false_eq_true, ↓reduceIte]
         obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
           vRecv_hooksCKAShifted_pure_eq Dh prng fs l tStarH es.g P (es.g.st P) c' none es.h sc
             (hSync.2 habF P)
         rw [run_liftH_bind, run_liftH_bind]
         simp only [hvrEq, hvrPure, pure_bind]
         rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
         · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             simulateQ_pure, support_pure, Set.mem_singleton_iff]
           exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
         · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
           exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
         · dsimp only
           by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch)) = true
           · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
               Set.mem_singleton_iff]
             exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
           · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
             split_ifs with htriv
             · have hcm := commitE_ckaSync_shifted Dh prng fs Δgame tStarGame l tStarH es.g P
                 (es.g.st P) st' ⟨P.other, t', i'⟩ { es with h := h' } sc hSync.1
                 (hSync.2 habF) hSync.2 (hvrPost st' t' i' m' rfl)
               simp only [StateT.run_bind, simulateQ_bind]
               rw [hcm.1]
               refine ⟨rfl, fun z hz => ?_⟩
               rw [mem_support_bind_iff] at hz
               obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
               obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
               rcases cmRes with _ | s₁
               · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                   Set.mem_singleton_iff] at hz
                 subst hz; exact hcmNone rfl
               · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
                 simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                   simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                 subst hz; exact ⟨hsc₁, fun _ => hs₁Sync⟩
             · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 simulateQ_pure, support_pure, Set.mem_singleton_iff]
               exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
             · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
               exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)

private lemma implEDFShiftedPaper_ckaSync_eq {KR RSt K SS RS M E : Type}
    [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (Δgame tStarGame Δcka l tStarH qep maxSkip tStar : ℕ)
    (cfg : CryptoGames.SM.Config M) (π : Policy)
    (es : EState (VP (Option DDHSt) Pt RSt SS RS) M (Header Pt × E)
      (CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt))
    (sc : CryptoGames.CKA.GameState DDHSt Pt)
    (t : (CryptoGames.SM.specDF (PartyState DDHSt Pt RSt SS RS) M (BitVec 256) (Header Pt × E)).Domain)
    (hSync : CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync es sc) :
    (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
        (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH)
        (2 + Δcka) qep maxSkip tStar cfg π (.inr t)).run es)).run sc =
    (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
        (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
        (2 + Δcka) qep maxSkip tStar cfg π (.inr t)).run es)).run sc ∧
    ∀ z ∈ support ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
        (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
        (2 + Δcka) qep maxSkip tStar cfg π (.inr t)).run es)).run sc),
      CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync z.1.2 z.2 := by
  let ckaImpl := CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame
  let hk₁ := CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH
  let hk₂ := CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (simulateQ ckaImpl ((transmitE hk₁ (2 + Δcka) qep π (P, m, r)).run es)).run sc =
        (simulateQ ckaImpl ((transmitE hk₂ (2 + Δcka) qep π (P, m, r)).run es)).run sc ∧
      ∀ z ∈ support ((simulateQ ckaImpl ((transmitE hk₂ (2 + Δcka) qep π (P, m, r)).run es)).run sc),
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync z.1.2 z.2
    unfold transmitE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · dsimp only
        by_cases hdoom : π.leakDoom es.g s₁ = true
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => by cases h'⟩⟩
        · have hs₁All : ∀ Q, CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc Q (s₁.st Q) := fun Q => by
            rw [CryptoGames.SM.Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
          have hvs := vSend_ckaSync_shifted Dh prng fs Δgame tStarGame l tStarH s₁ P (s₁.st P)
            m none r es.h sc hSync.1 (hs₁All P)
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
          rw [run_liftH_bind, run_liftH_bind]
          simp only [simulateQ_bind, StateT.run_bind]
          dsimp only [hk₁, hk₂]; rw [hvs.1]
          refine ⟨rfl, fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz
          obtain ⟨⟨⟨vsRes, h'⟩, sc₁⟩, hvsMem, hz⟩ := hz
          have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
          rcases vsRes with _ | ⟨st', ct⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
          · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine ⟨hsc₁, fun _ Q => ?_⟩
            by_cases hQP : Q = P
            · subst hQP; simp [CryptoVerification.LibsignalSession.Fig8SchemeBridge.record_st_eq, hst'P]
            · simp [CryptoVerification.LibsignalSession.Fig8SchemeBridge.record_st_eq, Function.update_of_ne hQP]
              exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
  · change (simulateQ ckaImpl ((challE hk₁ (2 + Δcka) qep cfg π (P, m₀, m₁, r)).run es)).run sc =
        (simulateQ ckaImpl ((challE hk₂ (2 + Δcka) qep cfg π (P, m₀, m₁, r)).run es)).run sc ∧
      ∀ z ∈ support ((simulateQ ckaImpl ((challE hk₂ (2 + Δcka) qep cfg π (P, m₀, m₁, r)).run es)).run sc),
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync z.1.2 z.2
    unfold challE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · dsimp only
        by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !(cfg.challAllowedIn (s₁.epoch P))) = true
        · simp only [hch, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          by_cases hdoom : π.leakDoom es.g s₁ = true
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
          · have hs₁All : ∀ Q, CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptPartySync sc Q (s₁.st Q) := fun Q => by
              rw [CryptoGames.SM.Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
            have hvs := vSend_ckaSync_shifted Dh prng fs Δgame tStarGame l tStarH s₁ P (s₁.st P)
              ((cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀))
              (some (m₀, m₁)) r es.h sc hSync.1 (hs₁All P)
            simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
            rw [run_liftH_bind, run_liftH_bind]
            simp only [simulateQ_bind, StateT.run_bind]
            dsimp only [hk₁, hk₂]; rw [hvs.1]
            refine ⟨rfl, fun z hz => ?_⟩
            rw [mem_support_bind_iff] at hz
            obtain ⟨⟨⟨vsRes, h'⟩, sc₁⟩, hvsMem, hz⟩ := hz
            have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
            rcases vsRes with _ | ⟨st', ct⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
            · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz
              refine ⟨hsc₁, fun _ Q => ?_⟩
              by_cases hQP : Q = P
              · subst hQP; simp [CryptoVerification.LibsignalSession.Fig8SchemeBridge.record_st_eq, hst'P]
              · simp [CryptoVerification.LibsignalSession.Fig8SchemeBridge.record_st_eq, Function.update_of_ne hQP]
                exact CryptoVerification.LibsignalSession.Fig8SchemeBridge.optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
  · change (simulateQ ckaImpl ((deliverE hk₁ maxSkip cfg (P, c)).run es)).run sc =
        (simulateQ ckaImpl ((deliverE hk₂ maxSkip cfg (P, c)).run es)).run sc ∧
      ∀ z ∈ support ((simulateQ ckaImpl ((deliverE hk₂ maxSkip cfg (P, c)).run es)).run sc),
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync z.1.2 z.2
    unfold deliverE abortE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · dsimp only
        obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
          vRecv_hooksCKAShifted_pure_eq Dh prng fs l tStarH es.g P (es.g.st P) c (some r) es.h sc
            (hSync.2 habF P)
        rw [run_liftH_bind, run_liftH_bind]
        dsimp only [hk₁, hk₂]
        simp only [hvrEq, hvrPure, pure_bind]
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
        · split_ifs <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               simulateQ_pure, support_pure, Set.mem_singleton_iff];
             exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
        · have hcm := commitE_ckaSync_shifted Dh prng fs Δgame tStarGame l tStarH es.g P
            (es.g.st P) st' r.pos { es with h := h' } sc hSync.1 (hSync.2 habF) hSync.2
            (hvrPost st' t' i' m' rfl)
          simp only [StateT.run_bind, simulateQ_bind]
          rw [hcm.1]
          refine ⟨rfl, fun z hz => ?_⟩
          rw [mem_support_bind_iff] at hz
          obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
          obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
          rcases cmRes with _ | s₁
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hcmNone rfl
          · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine ⟨hsc₁, fun _ Q => ?_⟩
            split_ifs <;> exact hs₁Sync Q
  · change (simulateQ ckaImpl ((CryptoGames.SM.Engine.injectEGen b1 hk₁ (2 + Δcka) qep tStar cfg (P, c)).run es)).run sc =
        (simulateQ ckaImpl ((CryptoGames.SM.Engine.injectEGen b1 hk₂ (2 + Δcka) qep tStar cfg (P, c)).run es)).run sc ∧
      ∀ z ∈ support ((simulateQ ckaImpl
        ((CryptoGames.SM.Engine.injectEGen b1 hk₂ (2 + Δcka) qep tStar cfg (P, c)).run es)).run sc),
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync z.1.2 z.2
    cases b1 <;> [
      unfold CryptoGames.SM.Engine.injectEGen injectE abortE;
      unfold CryptoGames.SM.Engine.injectEGen CryptoGames.SM.Construction.DeliverForge.injectEB1 abortE] <;>
    (simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
     split_ifs with href
     · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
       exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
     · have habF : es.abort = false := by
         rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr href) with ⟨h1, _⟩
         rcases Bool.or_eq_false_iff.mp h1 with ⟨h2, _⟩
         exact (Bool.or_eq_false_iff.mp h2).1
       obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
         vRecv_hooksCKAShifted_pure_eq Dh prng fs l tStarH es.g P (es.g.st P) c none es.h sc
           (hSync.2 habF P)
       rw [run_liftH_bind, run_liftH_bind]
       dsimp only [hk₁, hk₂]
       simp only [hvrEq, hvrPure, pure_bind]
       rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
       · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           simulateQ_pure, support_pure, Set.mem_singleton_iff]
         exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
       · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
         exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
       · dsimp only
         by_cases hqep : qep + 1 < t'
         · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
             Set.mem_singleton_iff]
           exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
         · simp only [hqep, ↓reduceIte]
           split_ifs with htriv
           · have hcm := commitE_ckaSync_shifted Dh prng fs Δgame tStarGame l tStarH es.g P
               (es.g.st P) st' ⟨P.other, t', i'⟩ { es with h := h' } sc hSync.1
               (hSync.2 habF) hSync.2 (hvrPost st' t' i' m' rfl)
             simp only [StateT.run_bind, simulateQ_bind]
             rw [hcm.1]
             refine ⟨rfl, fun z hz => ?_⟩
             rw [mem_support_bind_iff] at hz
             obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
             obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem
             rcases cmRes with _ | s₁
             · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                 Set.mem_singleton_iff] at hz
               subst hz; exact hcmNone rfl
             · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
               simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
               subst hz; exact ⟨hsc₁, fun _ => hs₁Sync⟩
           · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               simulateQ_pure, support_pure, Set.mem_singleton_iff]
             exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
           · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
             exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
  · change (simulateQ ckaImpl ((CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l hk₁ π P).run es)).run sc =
        (simulateQ ckaImpl ((CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l hk₂ π P).run es)).run sc ∧
      ∀ z ∈ support ((simulateQ ckaImpl ((CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper l hk₂ π P).run es)).run sc),
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync z.1.2 z.2
    have hRevEq : hk₁.reveal = hk₂.reveal := rfl
    refine ⟨by unfold CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper; rw [hRevEq], fun z hz => ?_⟩
    unfold CryptoGames.SM.Construction.DeliverForge.corrEShiftedPaper abortE at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hSync
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hdoom :
          (π.leakDoom es.g (CryptoGames.SM.Construction.DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hz
        rw [run_liftH_bind] at hz
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨revRes, h'⟩, sc₁⟩, hrev, hz⟩ := hz
        have hsc₁_eq : sc₁ = sc := by
          dsimp only [hk₂, CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted] at hrev
          rcases hγ : (es.g.st P).γ with _ | γ
          · by_cases hpre : (es.g.st P).tcur + 1 ≤ l
            · simp only [hγ, hpre, ↓reduceIte, StateT.run_bind, StateT.run_get,
                pure_bind] at hrev
              rcases hγPre : es.h.γPre P with _ | γ' <;>
                (simp only [hγPre, StateT.run_pure, simulateQ_pure, support_pure,
                   Set.mem_singleton_iff] at hrev;
                 exact (Prod.mk.inj hrev).2)
            · simp only [hγ, hpre, ↓reduceIte, StateT.run_bind, simulateQ_bind,
                mem_support_bind_iff] at hrev
              obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hrev⟩ := hrev
              have ⟨heq, _⟩ :=
                liftCShifted_corrQuery_support Dh Δgame tStarGame P es.h sc hSync.1 hcorr
              dsimp only at heq; subst heq
              rcases corrAns with _ | γ' <;>
                (simp only [StateT.run_pure, simulateQ_pure, support_pure,
                   Set.mem_singleton_iff] at hrev;
                 exact (Prod.mk.inj hrev).2)
          · simp only [hγ, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hrev
            exact (Prod.mk.inj hrev).2
        subst hsc₁_eq
        rcases revRes with _ | stP
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hSync.1, fun hab Q => by
            dsimp only; rw [afterCorrShifted_st_eq]; exact hSync.2 hab Q⟩
  · exact deliverForgeEGen_ckaSync_shifted b1 Dh prng fs Δgame tStarGame Δcka l tStarH qep tStar
      cfg P c c' es sc hSync

private lemma simulateQ_implEDFShiftedPaper_ckaSync_eq {KR RSt K SS RS M E α : Type}
    [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (b1 : Bool) (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E)
    (Δgame tStarGame Δcka l tStarH qep maxSkip tStar : ℕ)
    (cfg : CryptoGames.SM.Config M) (π : Policy)
    (oa : OracleComp (unifSpec + CryptoGames.SM.specDF (PartyState DDHSt Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)) α)
    (es : EState (VP (Option DDHSt) Pt RSt SS RS) M (Header Pt × E)
      (CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt))
    (sc : CryptoGames.CKA.GameState DDHSt Pt)
    (hSync : CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync es sc) :
    (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
        (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH)
        (2 + Δcka) qep maxSkip tStar cfg π) oa).run es)).run sc =
    (simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
        (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
        (2 + Δcka) qep maxSkip tStar cfg π) oa).run es)).run sc := by
  induction oa using OracleComp.inductionOn generalizing es sc with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · have hInl₁ :
          (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
            (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhSchemeFb Dh) prng fs l tStarH)
            (2 + Δcka) qep maxSkip tStar cfg π (.inl n)).run es = (coinsE n).run es := rfl
      have hInl₂ :
          (CryptoGames.SM.Construction.DeliverForge.implEDFShiftedPaperGen b1 l
            (CryptoGames.SM.Construction.DeliverForge.hooksCKAShifted (dhScheme Dh) prng fs l tStarH)
            (2 + Δcka) qep maxSkip tStar cfg π (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl₁, hInl₂]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, simulateQ_bind, simulateQ_HasQuery_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at hmem
      have hInlQ : CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame (Sum.inl n) =
          StateT.lift ($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1))) := rfl
      rw [hInlQ, StateT.run_lift] at hmem
      simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨_, _, hEq⟩ := hmem
      rcases Prod.mk.inj hEq with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨rfl, hesEq⟩
      dsimp only [id]
      rw [hesEq, hscEq]
      exact ih u es sc hSync
    · obtain ⟨hEq, hPost⟩ := implEDFShiftedPaper_ckaSync_eq b1 Dh prng fs Δgame tStarGame Δcka l
        tStarH qep maxSkip tStar cfg π es sc t_sm hSync
      rw [hEq]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem =>
        ih _ es' sc' (hPost _ hmem)

theorem ckaAdvantage_authSimDFShiftedPaperGen_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δgame tStarGame Δcka qep l tStarH tStar : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.CKA.advantage (dhSchemeFb Dh) Δgame tStarGame
      (redCKAAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l tStarH tStar A) =
    CryptoGames.CKA.advantage (dhScheme Dh) Δgame tStarGame
      (redCKAAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep l tStarH tStar A) := by
  let fsL := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
  let mo' : CryptoGames.SM.Construction.Mode := ⟨true, some (l - 1), tStar⟩
  have hFsSwap :
      redCKAAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep l tStarH tStar A =
      redCKAAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
        fsL lam Δcka qep l tStarH tStar A := by
    have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery
        (G := CryptoGames.SM.specDF (PartyState DDHSt Pt (BitVec 256) SS256 RS256)
          (MsgPt ℓ) (BitVec 256) (Header Pt × Ct32))) qAdv := by
      refine hA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
    unfold redCKAAuthDFShiftedPaperGen CryptoGames.SM.Construction.DeliverForge.authSimDFShiftedPaperGen
      CryptoGames.SM.Construction.DeliverForge.engRunDFShiftedPaperGen
    refine congrArg (· >>= _) ?_
    have hInitEq :
        CryptoGames.SM.Construction.DeliverForge.initCKAShifted (dhSchemeFb Dh) (rootPRNG C.F encPt)
          (fsAtomicB C ℓ encT idOf B0) lam l =
        CryptoGames.SM.Construction.DeliverForge.initCKAShifted (dhSchemeFb Dh) (rootPRNG C.F encPt) fsL lam l := by
      unfold CryptoGames.SM.Construction.DeliverForge.initCKAShifted fsAtomicB fsL lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
    change (CryptoGames.SM.Construction.DeliverForge.initCKAShifted (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam l).run {} >>= _ =
      (CryptoGames.SM.Construction.DeliverForge.initCKAShifted (dhSchemeFb Dh) (rootPRNG C.F encPt) fsL lam l).run {} >>= _
    rw [hInitEq]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h₁⟩ hmem => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · rfl
    · have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
      have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
        Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
      let es₀ : EState (VP (Option DDHSt) Pt (BitVec 256) SS256 RS256) (MsgPt ℓ)
          (Header Pt × Ct32) (CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt) :=
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₁ }
      have hInv₀ : SMEngineInv (B_q + 1) B_q qAdv es₀.g :=
        (CryptoGames.SM.Engine.SMEngineInv.init _ false hB1 hBB).mono hqB
      have hVRHk := hooksCKAShifted_vrInv_lFS (dhSchemeFb Dh) (rootPRNG C.F encPt) C ℓ encT idOf
        l tStarH
      have hMk : ∃ σ k, (vA, vB) = mkParties (T := Pt) none none σ
          (fsL.initSender k) (fsL.initReceiver k) := by
        unfold CryptoGames.SM.Construction.DeliverForge.initCKAShifted at hmem
        simp only [CryptoGames.SM.Construction.DeliverForge.liftCShifted, StateT.run_bind, StateT.run_lift,
          bind_assoc, pure_bind, mem_support_bind_iff] at hmem
        obtain ⟨kr, _, hmem⟩ := hmem
        let p := (rootPRNG C.F encPt).up ((rootPRNG C.F encPt).init kr) lam
        by_cases hl : 1 ≤ l
        · simp only [hl, ↓reduceIte, CryptoGames.SM.Construction.DeliverForge.setγPreShifted, StateT.run_bind,
            StateT.run_lift, StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hmem
          obtain ⟨_, _, _, _, hEq, _⟩ := hmem
          exact ⟨p.1, p.2, hEq⟩
        · simp only [hl, ↓reduceIte, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
          exact ⟨p.1, p.2, hmem.1⟩
      have hVR₀ : SMVRInv (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB maxForwardJumps)
          B_q qAdv es₀.g := by
        intro P t₀ v hv
        obtain ⟨σ, k, hEq⟩ := hMk
        rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        cases P <;> simp only [es₀] at hv
        · split_ifs at hv
          · cases hv
            exact hVRHk.mono (Nat.zero_le _)
              (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
                ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
                (lChainPRG C.F) maxForwardJumps k)
        · cases hv
      dsimp only
      exact congrArg (· >>= fun res => pure (some res))
        (simulateQ_implEDFShiftedPaper_localFs_eq (mo' := mo')
          (hooksCKAShifted_localFsAgree (dhSchemeFb Dh) (rootPRNG C.F encPt) C ℓ encT idOf B0
            l tStarH)
          hVRHk hB0 hA' hSendOk es₀ hInv₀ hVR₀)
  rw [hFsSwap, CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist]
  have hBranch : ∀ b : Bool,
      CryptoGames.CKA.branch (dhSchemeFb Dh) Δgame tStarGame b
        (redCKAAuthDFShiftedPaperGen (dhSchemeFb Dh) (rootPRNG C.F encPt)
          fsL lam Δcka qep l tStarH tStar A) =
      CryptoGames.CKA.branch (dhScheme Dh) Δgame tStarGame b
        (redCKAAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
          fsL lam Δcka qep l tStarH tStar A) := by
    intro b
    rw [CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaBranch_dhSchemeFb_eq]
    unfold CryptoGames.CKA.branch redCKAAuthDFShiftedPaperGen CryptoGames.SM.Construction.DeliverForge.authSimDFShiftedPaperGen
      CryptoGames.SM.Construction.DeliverForge.engRunDFShiftedPaperGen
    refine bind_congr fun k => ?_
    rw [StateT.run'_eq, StateT.run'_eq]
    refine congrArg (Prod.fst <$> ·) ?_
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    let sc₀ := CryptoGames.CKA.initState (dhScheme Dh) k b
    have hsc₀ : CryptoVerification.LibsignalSession.Fig8SchemeBridge.CkaStateInv sc₀ := CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaStateInv_init Dh k b
    have hep₀ : ∀ P, sc₀.epoch P = 0 := fun _ => rfl
    have hInit :
        CryptoGames.SM.Construction.DeliverForge.initCKAShifted (dhSchemeFb Dh) (rootPRNG C.F encPt) fsL lam l =
        CryptoGames.SM.Construction.DeliverForge.initCKAShifted (dhScheme Dh) (rootPRNG C.F encPt) fsL lam l := rfl
    change ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
        ((CryptoGames.SM.Construction.DeliverForge.initCKAShifted (dhSchemeFb Dh) (rootPRNG C.F encPt) fsL lam l).run
          {})).run sc₀ >>= _) =
      ((simulateQ (CryptoVerification.LibsignalSession.Fig8SchemeBridge.ckaFullImpl (dhScheme Dh) Δgame tStarGame)
        ((CryptoGames.SM.Construction.DeliverForge.initCKAShifted (dhScheme Dh) (rootPRNG C.F encPt) fsL lam l).run
          {})).run sc₀ >>= _)
    rw [hInit]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨vs, h₁⟩, sc₁⟩ hmem => ?_
    have hSyncInit : sc₁ = sc₀ ∧ ∀ vA vB, vs = some (vA, vB) →
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.OptCKASync (M := LibsignalMsgPublicPart × Plain ℓ) (E := Fig8C Pt)
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₁ }
          sc₀ := by
      unfold CryptoGames.SM.Construction.DeliverForge.initCKAShifted at hmem
      have hPureLift : ∀ h₀ : CryptoGames.SM.Construction.DeliverForge.CKAStateShifted DDHSt Pt Pt,
          (CryptoGames.SM.Construction.DeliverForge.liftCShifted
            (pure () : CryptoGames.CKA.AdversaryComp DDHSt (BitVec 256) Pt Pt Unit)).run h₀ =
            pure ((), h₀) := fun h₀ => by simp [CryptoGames.SM.Construction.DeliverForge.liftCShifted]
      simp only [StateT.run_bind, hPureLift, simulateQ_bind, pure_bind] at hmem
      rw [sampleT, StateT.run_lift] at hmem
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        CryptoVerification.LibsignalSession.Fig8SchemeBridge.simulateQ_ckaFullImpl_liftProb, bind_assoc, pure_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨kr, _, hmem⟩ := hmem
      by_cases hl : 1 ≤ l
      · simp only [hl, ↓reduceIte, StateT.run_bind, simulateQ_bind,
          mem_support_bind_iff] at hmem
        obtain ⟨⟨⟨γA?, hA₁⟩, scA⟩, hcorrA, ⟨⟨⟨γB?, hB₁⟩, scB⟩, hcorrB, hmem⟩⟩ := hmem
        have ⟨hscA, _⟩ :=
          liftCShifted_corrQuery_support Dh Δgame tStarGame .A _ sc₀ hsc₀ hcorrA
        dsimp only at hscA; subst hscA
        have ⟨hscB, _⟩ :=
          liftCShifted_corrQuery_support Dh Δgame tStarGame .B _ sc₀ hsc₀ hcorrB
        dsimp only at hscB; subst hscB
        simp only [CryptoGames.SM.Construction.DeliverForge.setγPreShifted, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff, exists_eq_left] at hmem
        rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
        rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
        refine ⟨hscEq, fun vA vB hEq => ?_⟩
        rw [hvs, Option.some.injEq] at hEq; cases hEq
        refine ⟨hsc₀, fun _ P => ?_⟩
        cases P <;> exact ⟨rfl, (hep₀ _).symm⟩
      · simp only [hl, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hmem
        rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
        rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
        refine ⟨hscEq, fun vA vB hEq => ?_⟩
        rw [hvs, Option.some.injEq] at hEq; cases hEq
        refine ⟨hsc₀, fun _ P => ?_⟩
        cases P <;> exact ⟨rfl, (hep₀ _).symm⟩
    obtain ⟨hscEq, hSyncInit⟩ := hSyncInit
    rw [hscEq]
    rcases vs with _ | ⟨vA, vB⟩
    · rfl
    · dsimp only
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc]
      have hSim := simulateQ_implEDFShiftedPaper_ckaSync_eq (decide (Δcka = 0)) Dh
        (rootPRNG C.F encPt) fsL Δgame tStarGame Δcka l tStarH qep fsL.maxSkip tStar
        (CryptoGames.SM.Config.auth tStar) ⟨true, some (l - 1), tStar⟩ A
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h₁ }
        sc₀ (hSyncInit vA vB rfl)
      exact congrArg (· >>= _) hSim
  rw [hBranch true, hBranch false]

/-! ## Advantage and `FsOk` bridges -/

theorem compileCkaDFAtomic_shiftedPaperGen_advantage
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δgame tStarGame Δcka qep q l tStarH tStar : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.CKA.advantage (dhScheme Dh) Δgame tStarGame
      ((compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
            l tStarH tStar)).eval (fun _ => A) ()) =
    CryptoGames.CKA.advantage (dhScheme Dh) Δgame tStarGame
      (redCKAAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep l tStarH tStar A) := by
  intro B0
  rw [Computational.Proofs.ReductionDsl.PureAuxMacroLift.ckaAdvantage_congr (dhScheme Dh)
      Δgame tStarGame
      (compileCkaDFAtomic_shiftedPaperGen_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam
        Δcka qep q l tStarH tStar A hqA),
    ← ckaAdvantage_dhSchemeFb_eq]
  exact ckaAdvantage_authSimDFShiftedPaperGen_atomic_eq Dh encPt C ℓ encT idOf lam
    B0 q Δgame tStarGame Δcka qep l tStarH tStar (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA

theorem compilePrngDFAtomic_shiftedPaperGen_advantage
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      ((compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
            l t useSafeCh)).eval (fun _ => A) ()) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t useSafeCh A) := by
  intro B0
  rw [Computational.Proofs.ReductionDsl.PureAuxMacroLift.prngAdvantage_congr (rootPRNG C.F encPt)
      (compilePrngDFAtomic_shiftedPaperGen_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam
        Δcka qep q l t useSafeCh A),
    redPRNGAuthDFShiftedPaperGenProg_advantage_atomic Dh encPt C ℓ encT idOf lam
      Δcka qep q l t useSafeCh A hqA]
  exact prngAdvantage_redPRNGAuthDFShiftedPaperGen_atomic_eq Dh encPt C ℓ encT idOf lam
    B0 q Δcka qep l t useSafeCh (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA

theorem compileFsDFAtomic_shiftedPaperGen_game_evalDistEq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
            j l t useSafeCh)).eval (fun _ => A) ()) =ᵈ
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep j l t useSafeCh A) := by
  intro B0
  have h1 := Computational.Proofs.ReductionDsl.PureAuxMacroLift.fsaeadGame_evalDistEq_of_coinSimEquiv
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
    (compileFsDFAtomic_shiftedPaperGen_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam
      Δcka qep q j l t useSafeCh A hqA)
  have h2 := fsaeadGame_redFSAuthDFShiftedPaperGen_atomic_eq Dh encPt C ℓ encT idOf lam
    B0 B0 q Δcka qep j l t useSafeCh (Nat.le_refl _) (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA
  rwa [h2] at h1

theorem compileFsDFAtomic_shiftedPaperGen_advantage
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.FSAEAD.advantage (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
            j l t useSafeCh)).eval (fun _ => A) ()) =
    CryptoGames.FSAEAD.advantage (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep j l t useSafeCh A) := by
  intro B0
  unfold CryptoGames.FSAEAD.advantage
  rw [(compileFsDFAtomic_shiftedPaperGen_game_evalDistEq Dh encPt C ℓ hℓ encT idOf lam
    Δcka qep q j l t useSafeCh A hqA hshA).evalDist_eq]

theorem compileFsDFAtomic_shiftedPaperGen_fsOk_and_encAtomicShort
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j l t : ℕ) (useSafeCh : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (heqA : EqualPubChallsDF (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) A)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hgA : GuardedSMDFShort A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R_ev := (compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
      (CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
        j l t useSafeCh)).eval (fun _ => A) ()
    FsOk ℓ (2 * q) q R_ev ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R_ev := by
  intro B0 R_ev
  let cka := dhSchemeFb Dh
  let prng := rootPRNG C.F encPt
  let fs' := CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
  have hfsShort : CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.FsSendShort
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) fs' :=
    fsClamp_fsAtomicB_fsSendShort C ℓ hℓ encT idOf B0 B0
  have hSubProg : QuerySubsumes R_ev
      ((CryptoGames.SM.Construction.redFSAuthDFShiftedPaperGenProg (q + 1) B0 Δcka qep maxForwardJumps
          j l t useSafeCh :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) :=
    BundlesEval.compileFsDFAtomic_querySubsumes ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A
  have hSub : QuerySubsumes R_ev
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen cka prng fs' lam Δcka qep j l t useSafeCh A) :=
    compileFsDFAtomic_shiftedPaperGen_querySubsumes Dh encPt C ℓ hℓ encT idOf lam
      Δcka qep q j l t useSafeCh A hqA
  have hEncAt : CryptoGames.FSAEAD.EncMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R_ev :=
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadEncMsgsOk_of_querySubsumes hSub
      (CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSAuthDFShiftedPaperGen_short cka prng fs' lam Δcka qep j l t useSafeCh
          (CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.validQ_encBadMsg ⟨useSafeCh, some (l - 1), t⟩
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)) A hshA))
  exact ⟨⟨Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadMakesAtMostQueries_of_querySubsumes hSubProg
      (CryptoGames.SM.Construction.redFSAuthDFShiftedPaperProg_queries (q + 1) B0 Δcka qep maxForwardJumps
        j l t useSafeCh A q hqA),
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadMakesAtMostDecQueries_of_querySubsumes hSubProg
      (CryptoGames.SM.Construction.redFSAuthDFShiftedPaperProg_decQueries (q + 1) B0 Δcka qep maxForwardJumps
        j l t useSafeCh A q hqA),
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadEqualPubChallenges_of_querySubsumes hSub
      (CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSAuthDFShiftedPaperGen_restricted cka prng fs' lam Δcka qep j l t useSafeCh
          (CryptoGames.LibsignalSM.Proofs.RestrictedReds.validQ_unequalPubChall ⟨useSafeCh, some (l - 1), t⟩)
          A heqA)),
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadAllQueriesInOneADClass_of_querySubsumes hSub
      ⟨t, CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSAuthDFShiftedPaperGen_restricted cka prng fs' lam Δcka qep j l t useSafeCh
          (CryptoGames.LibsignalSM.Proofs.RestrictedReds.validQ_offClass ⟨useSafeCh, some (l - 1), t⟩
            (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)) A heqA)⟩,
    encMsgsOk_shortB_of_atomicShortPubB hEncAt,
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.guardedFSInjectShort_of_querySubsumes hSub
      (guardedFSInjectShort_redFSAuthDFShiftedPaperGen
        cka prng fs' hfsShort lam Δcka qep j l t useSafeCh A hshA hgA)⟩, hEncAt⟩

end ShiftedPaperAtomicBridges

end Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapShifted
