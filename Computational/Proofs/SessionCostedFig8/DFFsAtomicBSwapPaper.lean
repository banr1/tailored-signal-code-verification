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
public import Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapShifted

/-!
# Atomic Compiler, `FsAtomicBSwap`, and `FsOk` Bridges for Paper `DeliverForge` Reductions

Proves evaluation, `CoinSimEquiv`, `QuerySubsumes`, `FsAtomicBSwap`, and `FsOk` bridges for the
atomic-compiled `Paper`, `ShiftedPaper`, `ShiftedDir2Paper`, and `CasePaper` `DeliverForge`
reductions.
-/
open scoped ENNReal
open Computational.Proofs.ReductionDsl.Fig8Atomic (RSReachB)
open Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapShifted (compileCkaDFAtomic_shiftedPaperGen_advantage compileCkaDFAtomic_shiftedPaperGen_coinSimEquiv compileFsDFAtomic_shiftedPaperGen_coinSimEquiv compileFsDFAtomic_shiftedPaperGen_fsOk_and_encAtomicShort compileFsDFAtomic_shiftedPaperGen_game_evalDistEq compileFsDFAtomic_shiftedPaperGen_querySubsumes compilePrngDFAtomic_shiftedPaperGen_advantage redCKAAuthDFShiftedPaperGen_one redCKAAuthDFShiftedPaperGen_zero)
open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (HooksLocalFsAgree OptSkippedLenLe SkippedLenLe fsFullImpl_skippedLenLe fsReveal_ext_skippedLenLe hooksCKA_localFsAgree hooksCKA_vrInv_lFS hooksFS_vrInv_skippedLenLe hooksPRNG_localFsAgree hooksPRNG_vrInv_lFS implE_hooksFS_ext_skippedLenLe implE_hooksFS_fsClamp_fsAtomicB_eq implE_localFs_eq initFSRaw_skippedLenLe skippedLenLe_init vRecv_ext_skippedLenLe vRecv_hooksFS_fsClamp_fsAtomicB_eq vRecv_localFs_eq)
open CryptoGames (AEADScheme CKAScheme FSAEADScheme PRFPRNG Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD (RatchetReceiverState RatchetSenderState)
open CryptoGames.LibsignalSM (lBlank)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lAead lChainPRG lFS lPubOf)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St)
open CryptoGames.SM (Config Pos)
open CryptoGames.SM.Construction (CKAState FSState FSVROkStep Header Mode PRNGState PartyState cacheC fsClamp fsFullImpl fst_mem_support_of_mem_support_simulateQ_run hooksCKA hooksFS hooksFS_vrInv_fromAEADPRG implEDFPaper_ext_snd_fromAEADPRG implEDFPaper_fsClamp_eq initCKA initCKARaw initCKARaw_inv initCKARaw_vrInv initFSRaw initFSRaw_inv initFSRaw_vrInv_fromAEADPRG initPRNG isQueryBoundP_initFSRaw_dec liftC qb_implEDFPaper_inr_one receiverState_reach_of_isDecQuery_bound runCKADFPaper_eq_bind_initCKARaw runFSDFPaper runFSDFPaper_eq_bind_initFSRaw sampleT)
open CryptoGames.SM.Engine (Ctx EState HM Hooks HooksVRInv Policy RSReach SMEngineInv SMVRInv VP abortE challE coinsE commitE deliverE implEDFPaper_inv implEDFPaper_vrInv injectE run_liftH_bind transmitE vSend vSendStep1 vSend_eq_bind)
open CryptoVerification.LibsignalSession (FsOk ckaAdvantage_dhSchemeFb_eq encMsgsOk_shortB_of_atomicShortPubB fsClamp_fsAtomicB_fsSendShort)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (AllPartiesInv CkaStateInv DdhRoleOk HooksLocalCKAAgree OptCKASync OptPartySync ckaBranch_dhSchemeFb_eq ckaFullImpl ckaStateInv_init commitE_localCKA_eq ddhRoleOk_initA ddhRoleOk_initB dhSchemeFb_send_of_roleOk hooksFS_localCKAAgree hooksPRNG_localCKAAgree implE_localCKA_eq liftC_corrQuery_support liftC_receiveQuery_support liftC_sendFamily_support optPartySync_of_epoch_eq simulateQ_ckaFullImpl_liftProb vRecv_hooksCKA_pure_eq vRecv_localCKA_eq)
open CryptoVerification.LibsignalSession.HeadlineV1 (EqualPubChallsDF GuardedSMDFShort SendMsgsOkDF badSendMsgDF challSimDF'Paper_equalPub challSimDF'Paper_guardedSMDFShort challSimDF'Paper_queries challSimDF'Paper_sendOk guardedFSInjectShort_redFSAuthDFPaper safePost_redFSAuthDFPaper_restricted safePost_redFSAuthDFPaper_short)
open ReductionDsl (CostedReduction ckaTargetIface fsaeadHeaderIface prngTargetIface)

@[expose] public section

namespace Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper

set_option autoImplicit false
set_option linter.dupNamespace false


open OracleSpec OracleComp
open _root_.ReductionDsl (CostedReduction atomicFig8Ops fig8SmIfaceDF fig8SmCodecDF
  ckaTargetIface prngTargetIface fsaeadHeaderIface)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv ckaAdvantage_congr
  prngAdvantage_congr fsaeadGame_evalDistEq_of_coinSimEquiv)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic fsAtomicB atomicShortPubB
  atomicShortPubB_imp_shortB fsAtomicB_send_eq)
open Computational.Proofs.SessionCostedFig8.Bundles (fig8SmOpsShallow fig8CkaOpsShallow
  compileSmDFAtomic compileCkaDFAtomic compilePrngDFAtomic compileFsDFAtomic)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

section CasePaperDefs

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

/-- 3-way case-split `B_cka` paper reduction program (`ShiftedDir2Paper` / `ShiftedPaper` / `Paper`). -/
def redCKAAuthDFCasePaperProg (L B qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction
      (CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (CryptoGames.CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (CryptoGames.CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    CryptoGames.SM.Construction.redCKAAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B qep maxSkip (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then
    CryptoGames.SM.Construction.redCKAAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip (t - 2) t
  else
    CryptoGames.SM.Construction.redCKAAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip tL t

/-- 3-way case-split `B_prng` paper reduction program (`ShiftedDir2Paper` / `ShiftedPaper` / `Paper`). -/
def redPRNGAuthDFCasePaperProg (L B qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction
      (CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (CryptoGames.PRFPRNG.prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    CryptoGames.SM.Construction.redPRNGAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B qep maxSkip (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then
    CryptoGames.SM.Construction.redPRNGAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip (t - 2) t
  else
    CryptoGames.SM.Construction.redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip tL t

/-- 3-way case-split `B_fs` paper reduction program (`ShiftedDir2Paper` / `ShiftedPaper` / `Paper`). -/
def redFSAuthDFCasePaperProg (L B qep maxSkip j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction
      (CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (CryptoGames.PRFPRNG.fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (CryptoGames.SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (CryptoGames.PRFPRNG.prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    CryptoGames.SM.Construction.redFSAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B qep maxSkip j (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then
    CryptoGames.SM.Construction.redFSAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip j (t - 2) t
  else
    CryptoGames.SM.Construction.redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip j tL t

end CasePaperDefs

section PaperAtomicBridges

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance instInhabitedPtBSwapPaper : Inhabited Pt := ⟨0⟩

/-! ## `compileSmDFAtomic` evaluation bridge -/

theorem compileSmDFAtomic_challSimDF'PaperProg_eval
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ)
    (B_adv : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqB : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF B_adv q) :
    ((compileSmDFAtomic ℓ Pt C Dh encPt encT idOf lam
        (CryptoGames.SM.challSimDF'PaperProg q (2 + 1) qep)).eval (fun _ => B_adv) ()) =
      CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) qep B_adv := by
  rw [BundlesEval.compileSmDFAtomic_eval ℓ Pt C Dh encPt encT idOf lam hℓ]
  exact CryptoGames.SM.challSimDF'PaperProg_eval
    (Key := Unit) (St := Fig8St Pt) (St₂ := Unit) (RCoins := Unit)
    (init := fun _ _ => none) (send := fun _ _ _ => none) (receive := fun _ _ _ => none)
    (eqMsg := @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq)
    (eqCt := @BEq.beq (Fig8C Pt) instBEqOfDecidableEq)
    (blank := lBlank ℓ) (injOK := fun _ => true) (stOK := fun _ _ => true) (φ := fun _ => none)
    (stSort := .st) q (2 + 1) qep rfl B_adv q hqB (Nat.le_refl q)

/-! ## Shallow evaluation bridges -/

omit [Zero Pt] in
theorem redCKAAuthDFPaperProg_eval_atomic
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((CryptoGames.SM.Construction.redCKAAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps tL t :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (CryptoGames.CKA.ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A := by
  intro B0
  exact CryptoGames.SM.Construction.redCKAAuthDFPaperProg_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q Δcka qep tL t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (BundlesEval.hooksCKA_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 Δcka ⟨true, tL, t⟩)
    (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (BundlesEval.fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redPRNGAuthDFPaperProg_advantage_atomic
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      ((CryptoGames.SM.Construction.redPRNGAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps tL t :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A) := by
  intro B0
  exact CryptoGames.SM.Construction.redPRNGAuthDFPaperProg_advantage_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q Δcka qep tL t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (BundlesEval.hooksPRNG_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 ⟨true, tL, t⟩)
    (CryptoGames.SM.Engine.RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (BundlesEval.fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redFSAuthDFPaperProg_eval_atomic_clamp
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((CryptoGames.SM.Construction.redFSAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps j tL t :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (CryptoGames.PRFPRNG.fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep j tL t A := by
  intro B0
  exact CryptoGames.SM.Construction.redFSAuthDFPaperProg_eval_clamp
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q Δcka qep j tL t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

/-! ## Compiled `CoinSimEquiv` and `QuerySubsumes` bridges -/

theorem compileCkaDFAtomic_paper_coinSimEquiv
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      ((compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redCKAAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps tL t)).eval
        (fun _ => A) ())
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A) := by
  intro B0
  have h := BundlesEval.compileCkaDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0
    (CryptoGames.SM.Construction.redCKAAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps tL t) A
  rwa [redCKAAuthDFPaperProg_eval_atomic Dh encPt C ℓ encT idOf lam Δcka qep q tL t A hqA] at h

theorem compileFsDFAtomic_paper_coinSimEquiv
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redFSAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps j tL t)).eval
        (fun _ => A) ())
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep j tL t A) := by
  intro B0
  have h := BundlesEval.compileFsDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0
    (CryptoGames.SM.Construction.redFSAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps j tL t) A
  rwa [redFSAuthDFPaperProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam Δcka qep q j tL t A hqA] at h

theorem compileFsDFAtomic_paper_querySubsumes
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    QuerySubsumes
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (CryptoGames.SM.Construction.redFSAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps j tL t)).eval
        (fun _ => A) ())
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep j tL t A) := by
  intro B0
  have h := BundlesEval.compileFsDFAtomic_querySubsumes ℓ Pt C Dh encPt encT idOf lam hℓ B0
    (CryptoGames.SM.Construction.redFSAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps j tL t) A
  rwa [redFSAuthDFPaperProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam Δcka qep q j tL t A hqA] at h

theorem compileCkaDFAtomic_casePaper_coinSimEquiv
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let cka := dhSchemeFb Dh
    let prng := rootPRNG C.F encPt
    let fs := fsAtomicB C ℓ encT idOf B0
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      ((compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (redCKAAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps tL t)).eval (fun _ => A) ())
      (if 2 ≤ t ∧ tL = some (t - 2) then
        CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A
      else if 3 ≤ t ∧ tL = some (t - 3) then
        CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A
      else
        CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper cka prng fs lam 1 qep tL t A) := by
  intro B0 cka prng fs
  unfold redCKAAuthDFCasePaperProg
  split_ifs
  · rw [← redCKAAuthDFShiftedPaperGen_zero cka prng fs lam qep (t - 1) t A]
    exact compileCkaDFAtomic_shiftedPaperGen_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam
      0 qep q (t - 1) 0 t A hqA
  · rw [← redCKAAuthDFShiftedPaperGen_one cka prng fs lam qep (t - 2) t A]
    exact compileCkaDFAtomic_shiftedPaperGen_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam
      1 qep q (t - 2) t t A hqA
  · exact compileCkaDFAtomic_paper_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam 1 qep q tL t A hqA

theorem compilePrngDFAtomic_casePaper_coinSimEquiv
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      ((compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (redPRNGAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps tL t)).eval (fun _ => A) ())
      ((redPRNGAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps tL t :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (CryptoGames.PRFPRNG.prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) := by
  intro B0
  exact BundlesEval.compilePrngDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0
    (redPRNGAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps tL t) A

theorem compileFsDFAtomic_casePaper_coinSimEquiv
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let cka := dhSchemeFb Dh
    let prng := rootPRNG C.F encPt
    let fsC := CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (redFSAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps j tL t)).eval (fun _ => A) ())
      (if 2 ≤ t ∧ tL = some (t - 2) then
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedDir2Paper cka prng fsC lam qep j (t - 1) t A
      else if 3 ≤ t ∧ tL = some (t - 3) then
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaper cka prng fsC lam 1 qep j (t - 2) t A
      else
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper cka prng fsC lam 1 qep j tL t A) := by
  intro B0 cka prng fsC
  unfold redFSAuthDFCasePaperProg
  split_ifs
  · rw [← CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen_false cka prng fsC lam qep j (t - 1) t A]
    exact compileFsDFAtomic_shiftedPaperGen_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam
      0 qep q j (t - 1) t false A hqA
  · rw [← CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen_true cka prng fsC lam 1 qep j (t - 2) t A]
    exact compileFsDFAtomic_shiftedPaperGen_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam
      1 qep q j (t - 2) t true A hqA
  · exact compileFsDFAtomic_paper_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam 1 qep q j tL t A hqA

theorem compileFsDFAtomic_casePaper_querySubsumes
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let cka := dhSchemeFb Dh
    let prng := rootPRNG C.F encPt
    let fsC := CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
    QuerySubsumes
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (redFSAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps j tL t)).eval (fun _ => A) ())
      (if 2 ≤ t ∧ tL = some (t - 2) then
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedDir2Paper cka prng fsC lam qep j (t - 1) t A
      else if 3 ≤ t ∧ tL = some (t - 3) then
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaper cka prng fsC lam 1 qep j (t - 2) t A
      else
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper cka prng fsC lam 1 qep j tL t A) := by
  intro B0 cka prng fsC
  unfold redFSAuthDFCasePaperProg
  split_ifs
  · rw [← CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen_false cka prng fsC lam qep j (t - 1) t A]
    exact compileFsDFAtomic_shiftedPaperGen_querySubsumes Dh encPt C ℓ hℓ encT idOf lam
      0 qep q j (t - 1) t false A hqA
  · rw [← CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen_true cka prng fsC lam 1 qep j (t - 2) t A]
    exact compileFsDFAtomic_shiftedPaperGen_querySubsumes Dh encPt C ℓ hℓ encT idOf lam
      1 qep q j (t - 2) t true A hqA
  · exact compileFsDFAtomic_paper_querySubsumes Dh encPt C ℓ hℓ encT idOf lam 1 qep q j tL t A hqA

/-! ## `FsAtomicBSwap` and advantage bridges -/

section FsAtomicBSwapPaperHelpers

open Computational.Proofs.ReductionDsl.Fig8Atomic (RSReachB)
open Computational.Proofs.SessionCostedFig8.FsAtomicBSwap (HooksLocalFsAgree SkippedLenLe
  OptSkippedLenLe hooksCKA_localFsAgree hooksPRNG_localFsAgree hooksCKA_vrInv_lFS
  hooksPRNG_vrInv_lFS vRecv_localFs_eq implE_localFs_eq hooksFS_vrInv_skippedLenLe
  vRecv_ext_skippedLenLe fsReveal_ext_skippedLenLe implE_hooksFS_ext_skippedLenLe
  fsFullImpl_skippedLenLe skippedLenLe_init initFSRaw_skippedLenLe
  vRecv_hooksFS_fsClamp_fsAtomicB_eq implE_hooksFS_fsClamp_fsAtomicB_eq)
open CryptoVerification.LibsignalSession.Fig8SchemeBridge (DdhRoleOk CkaStateInv ckaStateInv_init
  ddhRoleOk_initA ddhRoleOk_initB dhSchemeFb_send_of_roleOk ckaBranch_dhSchemeFb_eq
  LocalPartyInv AllPartiesInv HooksLocalCKAAgree hooksPRNG_localCKAAgree hooksFS_localCKAAgree
  vRecv_localCKA_eq commitE_localCKA_eq implE_localCKA_eq ckaFullImpl OptPartySync OptCKASync
  optPartySync_of_epoch_eq simulateQ_ckaFullImpl_liftProb liftC_corrQuery_support
  liftC_receiveQuery_support liftC_sendFamily_support vRecv_hooksCKA_pure_eq)

local notation "SS256" => CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)
local notation "RS256" => CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)
local notation "Msgℓ" ℓ => (LibsignalMsgPublicPart × Plain ℓ)
local notation "CtSalt" => ℕ × LibsignalCiphertextWithSalt32
local notation "DdhSt" P => CryptoGames.CKA.DDH.State (BitVec 256) P

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

private lemma badSendMsgDF_inl_to_badSendMsg {St Msg Coins C : Type} (ok : Msg → Bool)
    (t5 : (CryptoGames.SM.spec St Msg Coins C).Domain)
    (h : badSendMsgDF (St := St) (Coins := Coins) (C := C) ok (.inr (.inl t5)) = false) :
    CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
      (St := St) (Coins := Coins) (C := C) ok (.inr t5) = false := by
  rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P <;> exact h

omit [Zero Pt] [SampleableType Pt] in
private lemma implEDFPaper_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV : Type} {ℓ B0 B_q q' Δ qep : ℕ} {mo : Mode}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt SS256 RS256 (Msgℓ ℓ) CtSalt CCoins γV σV SS256 RS256}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂) (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP γV Pt σV SS256 RS256) (Msgℓ ℓ) (Header Pt × CtSalt) HS)
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins
      (Header Pt × CtSalt)).Domain)
    (hBad : badSendMsgDF (St := PartyState Γ Pt RSt SS256 RS256) (Coins := CCoins)
      (C := Header Pt × CtSalt) (fun m => atomicShortPubB m.1) (.inr t_sm) = false)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q (q' + 1) es.g) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₁ Δ qep maxForwardJumps mo.cfg mo.policy (.inr t_sm)).run es =
      (CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₂ Δ qep maxForwardJumps mo.cfg mo.policy (.inr t_sm)).run es := by
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · have hBad5 := badSendMsgDF_inl_to_badSendMsg (fun m => atomicShortPubB m.1) t5 hBad
    rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · exact implE_localFs_eq hAg hVRHk hB0 es (.inl (.inl (.inl (.inl (P, m, r))))) hBad5 hVR
    · exact implE_localFs_eq hAg hVRHk hB0 es (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))) hBad5 hVR
    · exact implE_localFs_eq (Δ := Δ) (qep := qep) hAg hVRHk hB0 es (.inl (.inl (.inr (P, c)))) hBad5 hVR
    · exact implE_localFs_eq hAg hVRHk hB0 es (.inl (.inr (P, c))) hBad5 hVR
    · change (CryptoGames.SM.Construction.DeliverForge.corrEPaper hk₁ mo.policy P).run es =
        (CryptoGames.SM.Construction.DeliverForge.corrEPaper hk₂ mo.policy P).run es
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaper; rw [hAg.reveal_eq]
  · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ Δ qep mo.cfg (P, c, c')).run es =
      (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep mo.cfg (P, c, c')).run es
    have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
    have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only; split_ifs
        · rfl
        · simp only [run_liftH_bind,
            vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c' none es.h (hVR P), hCommit]

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_implEDFPaper_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ RSt CCoins γV σV α : Type} {ℓ L B0 B_q q Δ qep : ℕ} {mo : Mode}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt SS256 RS256 (Msgℓ ℓ) CtSalt CCoins γV σV SS256 RS256}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂) (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins
      (Header Pt × CtSalt) α}
    (hoa : oa.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins (Header Pt × CtSalt))) q)
    (hSendOk : oa.IsQueryBoundP (fun t => badSendMsgDF (St := PartyState Γ Pt RSt SS256 RS256)
      (Coins := CCoins) (C := Header Pt × CtSalt) (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP γV Pt σV SS256 RS256) (Msgℓ ℓ) (Header Pt × CtSalt) HS)
    (hInv : SMEngineInv L B_q q es.g) (hVR : SMVRInv (RSReachB maxForwardJumps) B_q q es.g) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₁ Δ qep maxForwardJumps mo.cfg mo.policy) oa).run es =
      (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₂ Δ qep maxForwardJumps mo.cfg mo.policy) oa).run es := by
  induction oa using OracleComp.inductionOn generalizing q es with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa; rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ := badSendMsgDF_query_bind_step (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      change (coinsE n).run es >>= _ = (coinsE n).run es >>= _
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, _, rfl⟩ := hmem; exact ih u (hmx u) (hSendMx u) _ hInv hVR
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq0.resolve_left (by decide); omega⟩
      rw [implEDFPaper_localFs_eq hAg hVRHk hB0 es t_sm hBad hVR]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem =>
        ih u (by simpa using hmx u) (hSendMx u) es'
          (implEDFPaper_inv hk₂ mo.cfg mo.policy es t_sm hInv (u, es') hmem)
          (implEDFPaper_vrInv hk₂ hVRHk mo.cfg mo.policy es t_sm hInv hVR (u, es') hmem)

omit [Zero Pt] [SampleableType Pt] in
private lemma runCKADFPaper_fsAtomicB_eq_lFS {KC Γ CCoins I KR RSt : Type} [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (mo : Mode) (b : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ Pt RSt SS256 RS256 (Msgℓ ℓ) CCoins CtSalt)
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m => atomicShortPubB m.1) A) :
    CryptoGames.SM.Construction.DeliverForge.engRunDFPaper (hooksCKA cka prng (fsAtomicB C ℓ encT idOf B0) Δcka mo)
        (2 + Δcka) qep (fsAtomicB C ℓ encT idOf B0).maxSkip mo.cfg mo.policy
        (initCKA cka prng (fsAtomicB C ℓ encT idOf B0) lam mo) {} b A =
      CryptoGames.SM.Construction.DeliverForge.engRunDFPaper
        (hooksCKA cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo)
        (2 + Δcka) qep (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip mo.cfg mo.policy
        (initCKA cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo) {} b A := by
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins (Header Pt × CtSalt))) qAdv := by
    refine hA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  rw [runCKADFPaper_eq_bind_initCKARaw, runCKADFPaper_eq_bind_initCKARaw]
  have hS : (fsAtomicB C ℓ encT idOf B0).initSender =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender := rfl
  have hR : (fsAtomicB C ℓ encT idOf B0).initReceiver =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver := rfl
  have hInitEq : initCKARaw cka prng (fsAtomicB C ℓ encT idOf B0) lam mo b =
      initCKARaw cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b := by
    simp only [initCKARaw, hS, hR]
  rw [hInitEq]; refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b hqB le_rfl
    (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)) es₀ hes₀
  have hVRHk := hooksCKA_vrInv_lFS cka prng C ℓ encT idOf Δcka mo
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b
    (fun k => hVRHk.mono (Nat.zero_le _) (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps k)) es₀ hes₀
  have hms1 : (fsAtomicB C ℓ encT idOf B0).maxSkip = maxForwardJumps := rfl
  have hms2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms1, hms2]
  exact congrArg (· >>= _) (simulateQ_implEDFPaper_localFs_eq
    (hooksCKA_localFsAgree cka prng C ℓ encT idOf B0 Δcka mo) hVRHk hB0 hA' hSendOk es₀ hInv₀ hVR₀)

omit [Zero Pt] [SampleableType Pt] in
private lemma redPRNGAuthDFPaper_fsAtomicB_eq_lFS
    {KC Γ CCoins I KR RSt : Type}
    [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ Pt RSt SS256 RS256 (Msgℓ ℓ) CCoins CtSalt)
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m => atomicShortPubB m.1) A) :
    CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper cka prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A =
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A := by
  let mo : Mode := ⟨true, tL, t⟩
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins (Header Pt × CtSalt))) qAdv := by
    refine hA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper CryptoGames.SM.Construction.DeliverForge.authSimDFPaper CryptoGames.SM.Construction.DeliverForge.engRunDFPaper
  refine congrArg (· >>= _) ?_
  have hS : (fsAtomicB C ℓ encT idOf B0).initSender =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender := rfl
  have hR : (fsAtomicB C ℓ encT idOf B0).initReceiver =
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver := rfl
  have hInitEq : initPRNG cka prng (fsAtomicB C ℓ encT idOf B0) lam mo =
      initPRNG cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo := by
    simp only [initPRNG, hS, hR]
  rw [hInitEq]; refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · let es₀ : EState (VP Γ Pt (Option RSt) SS256 RS256) (Msgℓ ℓ) (Header Pt × CtSalt)
        (PRNGState Pt RSt (BitVec 256)) :=
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
    have hInv₀ : SMEngineInv (B_q + 1) B_q qAdv es₀.g :=
      (CryptoGames.SM.Engine.SMEngineInv.init _ false le_rfl (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))).mono hqB
    have hVRHk := hooksPRNG_vrInv_lFS cka prng C ℓ encT idOf mo
    have hVR₀ : SMVRInv (RSReachB maxForwardJumps) B_q qAdv es₀.g := by
      intro P t₀ v hv; unfold initPRNG at hmem
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨kc, _, ⟨rtRes, _⟩, _, hmem⟩ := hmem; rcases rtRes with _ | ⟨σ, k⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        cases hmem.1
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
        cases P <;> simp only [es₀] at hv
        · split_ifs at hv with ht0
          · cases hv; exact hVRHk.mono (Nat.zero_le _) (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
              ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
              (lChainPRG C.F) maxForwardJumps k)
        · cases hv
    change (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper _ (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) A).run es₀ >>= _ =
      (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper _ (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) A).run es₀ >>= _
    rw [simulateQ_implEDFPaper_localFs_eq
      (hooksPRNG_localFsAgree cka prng C ℓ encT idOf B0 mo) hVRHk hB0 hA' hSendOk es₀ hInv₀ hVR₀]

omit [Zero Pt] [SampleableType Pt] in
private lemma implEDFPaper_localCKA_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS RSt SS RS M E σV ssV rsV : Type} [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS (DdhSt Pt) Pt RSt SS RS M E (BitVec 256) (DdhSt Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (es : EState (VP (DdhSt Pt) Pt σV ssV rsV) M (Header Pt × E) HS)
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState (DdhSt Pt) Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E)).Domain)
    (hEs : AllPartiesInv es) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₁ Δ qep maxSkip cfg π (.inr t_sm)).run es =
      (CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₂ Δ qep maxSkip cfg π (.inr t_sm)).run es ∧
    ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₂ Δ qep maxSkip cfg π (.inr t_sm)).run es),
      AllPartiesInv res.2 := by
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · exact implE_localCKA_eq hAg Δ qep maxSkip cfg π es (.inl (.inl (.inl (.inl (P, m, r))))) hEs
    · exact implE_localCKA_eq hAg Δ qep maxSkip cfg π es (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))) hEs
    · exact implE_localCKA_eq hAg Δ qep maxSkip cfg π es (.inl (.inl (.inr (P, c)))) hEs
    · exact implE_localCKA_eq hAg Δ qep maxSkip cfg π es (.inl (.inr (P, c))) hEs
    · change (CryptoGames.SM.Construction.DeliverForge.corrEPaper hk₁ π P).run es = (CryptoGames.SM.Construction.DeliverForge.corrEPaper hk₂ π P).run es ∧
        ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.corrEPaper hk₂ π P).run es), AllPartiesInv res.2
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaper abortE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hAg.reveal_eq]
      refine ⟨trivial, fun res hmem => ?_⟩
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
      · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact hEs
      · simp only [href, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases hdoom : (π.leakDoom es.g (es.g.afterCorr P) || π.corrDoom es.g P) = true
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff] at hmem
          subst hmem; exact hEs
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨revRes, h'⟩, _, hmem⟩ := hmem
          rcases revRes with _ | stP <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff] at hmem; subst hmem; intro Q; exact hEs Q)
  · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ Δ qep cfg (P, c, c')).run es =
        (CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es ∧
      ∀ res ∈ support ((CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ Δ qep cfg (P, c, c')).run es), AllPartiesInv res.2
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
      · by_cases hchk : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [hchk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hEs⟩
        · have hvr := vRecv_localCKA_eq hAg es.g P (es.g.st P) c' none es.h (hEs P)
          simp only [hchk, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, hvr.1]
          refine ⟨OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vrRes, h'⟩ hvrMem => ?_,
            fun res hmem => ?_⟩
          · rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
            · rfl
            · rfl
            · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
              · simp [hqep]
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
                by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
                · simp only [htriv, ↓reduceIte, StateT.run_bind]
                  rw [(commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                    { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).1]
                · simp [htriv]
          · rw [mem_support_bind_iff] at hmem; obtain ⟨⟨vrRes, h'⟩, hvrMem, hmem⟩ := hmem
            rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
              subst hmem; exact hEs
            · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
              · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                subst hmem; exact hEs
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases htriv : es.g.trivial Δ ⟨P.other, t', i'⟩ = true
                · simp only [htriv, ↓reduceIte, StateT.run_bind, mem_support_bind_iff] at hmem
                  obtain ⟨⟨cmRes, es₁⟩, hcmMem, hmem⟩ := hmem
                  have hcm := (commitE_localCKA_eq hAg es.g P (es.g.st P) st' ⟨P.other, t', i'⟩
                    { es with h := h' } hEs (hvr.2 _ hvrMem st' t' i' m' rfl)).2 _ hcmMem
                  rcases cmRes with _ | s₁
                  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
                    subst hmem; intro Q; dsimp [AllPartiesInv] at *; rw [hcm.1]; exact hEs Q
                  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                      support_pure, Set.mem_singleton_iff] at hmem
                    subst hmem; exact hcm.2 s₁ rfl
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                  split_ifs at hmem <;>
                    (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                       support_pure, Set.mem_singleton_iff] at hmem; subst hmem; exact hEs)

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_implEDFPaper_localCKA_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS RSt SS RS M E σV ssV rsV α : Type} [DecidableEq M] [DecidableEq E] [Inhabited E]
    {hk₁ hk₂ : Hooks TSpec HS (DdhSt Pt) Pt RSt SS RS M E (BitVec 256) (DdhSt Pt) σV ssV rsV}
    (hAg : HooksLocalCKAAgree (fun P γ t => DdhRoleOk P t γ) hk₁ hk₂)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (PartyState (DdhSt Pt) Pt RSt SS RS) M (BitVec 256)
      (Header Pt × E) α)
    (es : EState (VP (DdhSt Pt) Pt σV ssV rsV) M (Header Pt × E) HS) (hEs : AllPartiesInv es) :
    (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₁ Δ qep maxSkip cfg π) oa).run es =
      (simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper hk₂ Δ qep maxSkip cfg π) oa).run es := by
  induction oa using OracleComp.inductionOn generalizing es with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · change (coinsE n).run es >>= _ = (coinsE n).run es >>= _
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, _, rfl⟩ := hmem; exact ih u _ hEs
    · have hStep := implEDFPaper_localCKA_eq hAg Δ qep maxSkip cfg π es t_sm hEs
      rw [hStep.1]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem =>
        ih u es' (hStep.2 (u, es') hmem)

omit [SampleableType Pt] in
private lemma redPRNGAuthDFPaper_dhSchemeFb_eq
    {KR RSt K SS RS M E : Type} [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType KR]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper (dhSchemeFb Dh) prng fs lam Δcka qep tL t A =
      CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper (dhScheme Dh) prng fs lam Δcka qep tL t A := by
  let mo : Mode := ⟨true, tL, t⟩
  unfold CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper CryptoGames.SM.Construction.DeliverForge.authSimDFPaper CryptoGames.SM.Construction.DeliverForge.engRunDFPaper
  refine congrArg (· >>= _) ?_
  have hInit : initPRNG (dhSchemeFb Dh) prng fs lam mo = initPRNG (dhScheme Dh) prng fs lam mo := rfl
  rw [hInit]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · have hAll : AllPartiesInv (M := M) (E := E) (HS := PRNGState Pt RSt K)
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } := by
      unfold initPRNG at hmem
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨kc, _, ⟨rtRes, _⟩, _, hmem⟩ := hmem
      rcases rtRes with _ | ⟨σ, k⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        cases hmem.1
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
        intro P; cases P
        · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
        · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
    dsimp only
    exact congrArg (· >>= fun res => pure (some res))
      (simulateQ_implEDFPaper_localCKA_eq (hooksPRNG_localCKAAgree Dh prng fs mo)
        (2 + Δcka) qep fs.maxSkip (CryptoGames.SM.Config.auth t) ⟨true, tL, t⟩ A _ hAll)

private lemma runFSDFPaper_dhSchemeFb_eq {KR RSt K SS RS M E : Type} [SampleableType KR]
    [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (b : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF (DdhSt Pt) Pt RSt SS RS M (BitVec 256) E) :
    runFSDFPaper (dhSchemeFb Dh) prng fs lam Δcka qep mo j b A =
      runFSDFPaper (dhScheme Dh) prng fs lam Δcka qep mo j b A := by
  rw [runFSDFPaper_eq_bind_initFSRaw, runFSDFPaper_eq_bind_initFSRaw]
  have hInit : initFSRaw (dhSchemeFb Dh) prng fs lam mo j b =
      initFSRaw (dhScheme Dh) prng fs lam mo j b := rfl
  rw [hInit]; refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have hEs : AllPartiesInv es₀ := by
    unfold initFSRaw at hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kr, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨kc, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, _, hes₀⟩ := hes₀
    rw [mem_support_bind_iff] at hes₀; obtain ⟨⟨ext, h₂⟩, _, hes₀⟩ := hes₀
    simp only [support_pure, Set.mem_singleton_iff] at hes₀; subst hes₀
    intro P; cases P
    · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
    · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
  exact congrArg (· >>= fun res => pure (some res)) (simulateQ_implEDFPaper_localCKA_eq
    (hooksFS_localCKAAgree Dh prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy A es₀ hEs)

private lemma vSend_ckaSync_gen_eq {KR RSt SS RS M E K : Type} [SampleableType K] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δgame tStarGame Δcka : ℕ) (mo : Mode)
    (ctx : Ctx (Option (DdhSt Pt)) Pt RSt SS RS M E) (P : Party)
    (s : VP (Option (DdhSt Pt)) Pt RSt SS RS) (m : M) (pair : Option (M × M))
    (r : Option (BitVec 256)) (h : CKAState Pt Pt) (sc : CryptoGames.CKA.GameState (DdhSt Pt) Pt)
    (hsc : CkaStateInv sc) (hs : OptPartySync sc P s) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((vSend (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) ctx P s m pair r).run h)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((vSend (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s m pair r).run h)).run sc ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((vSend (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s m pair r).run h)).run sc),
      CkaStateInv z.2 ∧ ∀ st' ct, z.1.1 = some (st', ct) →
        OptPartySync z.2 P st' ∧ ∀ Q, Q ≠ P → z.2.epoch Q = sc.epoch Q := by
  have hStep1 :
      (simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
        ((vSendStep1 (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) ctx P s r).run h)).run sc =
      (simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
        ((vSendStep1 (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s r).run h)).run sc ∧
      ∀ w ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
        ((vSendStep1 (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s r).run h)).run sc),
        CkaStateInv w.2 ∧ ∀ s₁, w.1.1 = some s₁ →
          OptPartySync w.2 P s₁ ∧ ∀ Q, Q ≠ P → w.2.epoch Q = sc.epoch Q := by
    by_cases hSend : s.id.sendsIn (s.tcur + 1) = true
    · have hPSend : P.sendsIn (s.tcur + 1) = true := by rw [← hs.1]; exact hSend
      rcases hγ : s.γ with _ | γ
      · let K : Option (Pt × Pt) → HM (CryptoGames.CKA.spec (DdhSt Pt) (BitVec 256) Pt Pt) (CKAState Pt Pt)
            (Option (VP (Option (DdhSt Pt)) Pt RSt SS RS)) :=
          fun ans => match ans with
            | none => pure none
            | some (T', Ik) => do
              cacheC (s.tcur + 1) (T', Ik); let p := prng.up s.root Ik
              if mo.tH + Δcka ≤ s.tcur + 1 then
                match ← liftC (CryptoGames.CKA.corrQuery P) with
                | none => pure none
                | some γ' => pure (some { s with tcur := s.tcur + 1, γ := some γ', curCkaMsg := some T',
                                                  root := p.1, vS := some (fs.initSender p.2) })
              else pure (some { s with tcur := s.tcur + 1, γ := none, curCkaMsg := some T',
                                        root := p.1, vS := some (fs.initSender p.2) })
        have hPull : (vSendStep1 (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s r).run h =
            (((match r with
              | some c => liftC (CryptoGames.CKA.sendWithAdversaryCoinsQuery P c)
              | none => if s.tcur + 1 = mo.tH then liftC (CryptoGames.CKA.challQuery P) else liftC (CryptoGames.CKA.sendQuery P)) >>= K)).run h := by
          unfold vSendStep1; simp only [hSend, hγ, ↓reduceIte]; dsimp only [hooksCKA, K]
          rcases r with _ | c <;> split_ifs <;> simp only [StateT.run_bind, bind_assoc] <;>
            refine bind_congr fun ⟨a, s'⟩ => ?_ <;> rcases a with _ | ⟨T', Ik⟩
          all_goals first
            | (simp only [StateT.run_pure]; done)
            | (simp only [cacheC, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]; done)
            | (simp only [cacheC, StateT.run_bind, StateT.run_modify, pure_bind, bind_assoc]
               refine bind_congr fun ⟨corrAns, s''⟩ => ?_
               rcases corrAns with _ | γ <;> simp only [StateT.run_pure, pure_bind])
        have hEqStart : vSendStep1 (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) ctx P s r =
            vSendStep1 (hooksCKA (dhScheme Dh) prng fs Δcka mo) ctx P s r := by
          unfold vSendStep1; simp only [hSend, hγ, ↓reduceIte]; rfl
        rw [hEqStart]; refine ⟨rfl, fun w hw => ?_⟩
        rw [hPull, StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
        obtain ⟨⟨⟨ans, h₁⟩, sc₁⟩, hans, hw⟩ := hw
        have ⟨hsc₁, hep₁⟩ := liftC_sendFamily_support Dh Δgame tStarGame mo.tH (s.tcur + 1) P r h sc hsc hans
        have hstcur : s.tcur = sc.epoch P := by have h2 := hs.2; rw [hγ] at h2; exact h2
        rcases ans with _ | ⟨T', Ik⟩
        · dsimp only [K] at hw
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
          subst hw; exact ⟨hsc₁, fun _ hEq => nomatch hEq⟩
        · have ⟨hepP, hepQ⟩ := hep₁ T' Ik rfl; dsimp only at hsc₁ hepP hepQ; dsimp only [K] at hw
          simp only [cacheC, StateT.run_bind, StateT.run_modify, pure_bind] at hw
          by_cases hfin : mo.tH + Δcka ≤ s.tcur + 1
          · simp only [hfin, ↓reduceIte, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hw
            obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hw⟩ := hw
            have ⟨hsc₂_eq, hRole₂⟩ := liftC_corrQuery_support Dh Δgame tStarGame P _ sc₁ hsc₁ hcorr
            dsimp only at hsc₂_eq hRole₂; subst hsc₂_eq; rcases corrAns with _ | γ'
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
              subst hw; exact ⟨hsc₁, fun _ hEq => nomatch hEq⟩
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hw
              subst hw; refine ⟨hsc₁, fun s₁ hs₁ => ?_⟩; dsimp at hs₁; cases hs₁
              exact ⟨⟨hs.1, by rw [hstcur, ← hepP]; exact hRole₂ γ' rfl⟩, hepQ⟩
          · simp only [hfin, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hw
            subst hw; refine ⟨hsc₁, fun s₁ hs₁ => ?_⟩; dsimp at hs₁; cases hs₁
            exact ⟨⟨hs.1, by dsimp; omega⟩, hepQ⟩
      · unfold vSendStep1; simp only [hSend, hγ, ↓reduceIte]; dsimp only [hooksCKA]
        have hRole : DdhRoleOk P s.tcur γ := by have h2 := hs.2; rw [hγ] at h2; exact h2
        have hCoinsEq := fun coins => dhSchemeFb_send_of_roleOk Dh hRole hPSend coins
        rcases r with _ | c
        · simp only [StateT.run_bind, StateT.run_lift, cacheC, StateT.run_modify, StateT.run_pure,
            bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure]
          refine ⟨bind_congr fun p => by rw [(hCoinsEq p.1).1], fun w hw => ?_⟩
          rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hw
          simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
          obtain ⟨coins, _, hw⟩ := hw; subst hw; refine ⟨hsc, fun s₁ hs₁ => ?_⟩
          dsimp at hs₁; cases hs₁; exact ⟨⟨hs.1, (hCoinsEq coins).2⟩, fun _ _ => rfl⟩
        · simp only [pure_bind, (hCoinsEq c).1, cacheC, StateT.run_bind, StateT.run_modify,
            StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ hw => by subst hw; refine ⟨hsc, fun s₁ hs₁ => ?_⟩; dsimp at hs₁; cases hs₁; exact ⟨⟨hs.1, (hCoinsEq c).2⟩, fun _ _ => rfl⟩⟩
    · unfold vSendStep1
      simp only [hSend, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ hw => by subst hw; exact ⟨hsc, fun s₁ hs₁ => by dsimp at hs₁; cases hs₁; exact ⟨hs, fun _ _ => rfl⟩⟩⟩
  rw [vSend_eq_bind, vSend_eq_bind, StateT.run_bind, StateT.run_bind, simulateQ_bind, simulateQ_bind,
    StateT.run_bind, StateT.run_bind, hStep1.1]
  have hFsEq : (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo).fsSend =
      (hooksCKA (dhScheme Dh) prng fs Δcka mo).fsSend := rfl
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
    · simp only [hvS, hooksCKA, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hsc₁, fun st' ct hEq => by cases hEq; exact ⟨hs₁P, hepQ⟩⟩

private lemma commitE_ckaSync_gen {KR RSt SS RS M E K : Type}
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δgame tStarGame Δcka : ℕ) (mo : Mode)
    (s : Ctx (Option (DdhSt Pt)) Pt RSt SS RS M E) (P : Party)
    (old new : VP (Option (DdhSt Pt)) Pt RSt SS RS) (pos : Pos)
    (es : EState (VP (Option (DdhSt Pt)) Pt RSt SS RS) M (Header Pt × E) (CKAState Pt Pt))
    (sc : CryptoGames.CKA.GameState (DdhSt Pt) Pt) (hsc : CkaStateInv sc)
    (hS : ∀ Q, OptPartySync sc Q (s.st Q)) (_hEs : es.abort = false → ∀ Q, OptPartySync sc Q (es.g.st Q))
    (hNew : new.id = P ∧
      (((decide (old.tcur < new.tcur) && old.γ.isNone) = false ∧ OptPartySync sc P new) ∨
       ((decide (old.tcur < new.tcur) && old.γ.isNone) = true ∧ new.γ = none ∧ new.tcur = sc.epoch P + 1))) :
    (commitE (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) s P old new pos).run es =
      (commitE (hooksCKA (dhScheme Dh) prng fs Δcka mo) s P old new pos).run es ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((commitE (hooksCKA (dhScheme Dh) prng fs Δcka mo) s P old new pos).run es)).run sc),
      CkaStateInv z.2 ∧ (z.1.1 = none → OptCKASync z.1.2 z.2) ∧
      (∀ s₁, z.1.1 = some s₁ → z.1.2.abort = es.abort ∧ ∀ Q, OptPartySync z.2 Q (s₁.st Q)) := by
  have hComm : (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo).commit =
      (hooksCKA (dhScheme Dh) prng fs Δcka mo).commit := rfl
  refine ⟨by unfold commitE; rw [hComm], fun z hz => ?_⟩
  unfold commitE abortE at hz; dsimp only [hooksCKA] at hz; rw [run_liftH_bind] at hz
  rcases hNew.2 with ⟨hCond, hSyncNew⟩ | ⟨hCond, hγNone, htcurNew⟩
  · rw [hCond] at hz
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; dsimp only
    refine ⟨hsc, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩; cases hs₁
    by_cases hQP : Q = P
    · subst hQP; simp only [CryptoGames.SM.GameState.accept, Function.update_self]; exact hSyncNew
    · simp only [CryptoGames.SM.GameState.accept, Function.update_of_ne hQP]; exact hS Q
  · rw [hCond] at hz; simp only [↓reduceIte] at hz
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨⟨rcvAns, h₁⟩, sc₁⟩, hrcv, hz⟩ := hz
    have ⟨hsc₁, _, hRcvOk⟩ := liftC_receiveQuery_support Dh Δgame tStarGame P es.h sc hsc hrcv
    rcases rcvAns with _ | ⟨⟩
    · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
      exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
    · have ⟨hepP, hepQ⟩ := hRcvOk rfl; dsimp only at hsc₁ hepP hepQ
      by_cases hfin : mo.tH + Δcka ≤ new.tcur
      · simp only [hfin, ↓reduceIte] at hz
        rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hz⟩ := hz
        have ⟨hsc₂_eq, hRole₂⟩ := liftC_corrQuery_support Dh Δgame tStarGame P h₁ sc₁ hsc₁ hcorr
        dsimp only at hsc₂_eq hRole₂; subst hsc₂_eq; rcases corrAns with _ | γ'
        · simp only [StateT.run_pure, pure_bind, StateT.run_bind, StateT.run_modify,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨hsc₁, fun _ => ⟨hsc₁, fun hab => by cases hab⟩, fun _ hEq => by cases hEq⟩
        · simp only [StateT.run_pure, pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩; cases hs₁
          by_cases hQP : Q = P
          · subst hQP; simp only [CryptoGames.SM.GameState.accept, Function.update_self]
            exact ⟨hNew.1, by rw [htcurNew, ← hepP]; exact hRole₂ γ' rfl⟩
          · simp only [CryptoGames.SM.GameState.accept, Function.update_of_ne hQP]
            exact optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)
      · simp only [hfin, ↓reduceIte, StateT.run_pure, pure_bind, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at hz; subst hz
        refine ⟨hsc₁, (fun hEq => by cases hEq), fun s₁ hs₁ => ⟨rfl, fun Q => ?_⟩⟩; cases hs₁
        by_cases hQP : Q = P
        · subst hQP; simp only [CryptoGames.SM.GameState.accept, Function.update_self]
          exact ⟨hNew.1, by rw [hγNone, htcurNew, hepP]⟩
        · simp only [CryptoGames.SM.GameState.accept, Function.update_of_ne hQP]
          exact optPartySync_of_epoch_eq (hS Q) (hepQ Q hQP)

private lemma implEDFPaper_ckaSync_gen_eq {KR RSt SS RS M E K : Type}
    [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δgame tStarGame Δcka qep maxSkip : ℕ) (mo : Mode)
    (es : EState (VP (Option (DdhSt Pt)) Pt RSt SS RS) M (Header Pt × E) (CKAState Pt Pt))
    (sc : CryptoGames.CKA.GameState (DdhSt Pt) Pt)
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState (DdhSt Pt) Pt RSt SS RS) M (BitVec 256) (Header Pt × E)).Domain)
    (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip
        mo.cfg mo.policy (.inr t_sm)).run es)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksCKA (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip
        mo.cfg mo.policy (.inr t_sm)).run es)).run sc ∧
    ∀ z ∈ support ((simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksCKA (dhScheme Dh) prng fs Δcka mo) (2 + Δcka) qep maxSkip
        mo.cfg mo.policy (.inr t_sm)).run es)).run sc), OptCKASync z.1.2 z.2 := by
  let ci := ckaFullImpl (dhScheme Dh) Δgame tStarGame
  let hk₁ := hooksCKA (dhSchemeFb Dh) prng fs Δcka mo
  let hk₂ := hooksCKA (dhScheme Dh) prng fs Δcka mo
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · change (simulateQ ci ((transmitE hk₁ (2 + Δcka) qep mo.policy (P, m, r)).run es)).run sc =
          (simulateQ ci ((transmitE hk₂ (2 + Δcka) qep mo.policy (P, m, r)).run es)).run sc ∧
        ∀ z ∈ support ((simulateQ ci ((transmitE hk₂ (2 + Δcka) qep mo.policy (P, m, r)).run es)).run sc),
          OptCKASync z.1.2 z.2
      unfold transmitE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win) = true
      · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
        simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => by cases h'⟩⟩
          · have hs₁All : ∀ Q, OptPartySync sc Q (s₁.st Q) := fun Q => by
              rw [CryptoGames.SM.Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
            have hvs := vSend_ckaSync_gen_eq Dh prng fs Δgame tStarGame Δcka mo s₁ P (s₁.st P) m none r
              es.h sc hSync.1 (hs₁All P)
            simp only [hdoom, Bool.false_eq_true, ↓reduceIte]; rw [run_liftH_bind, run_liftH_bind]
            simp only [simulateQ_bind, StateT.run_bind]; rw [hvs.1]
            refine ⟨rfl, fun z hz => ?_⟩; rw [mem_support_bind_iff] at hz
            obtain ⟨⟨⟨vsRes, h'⟩, sc₁⟩, hvsMem, hz⟩ := hz; have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
            rcases vsRes with _ | ⟨st', ct⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
            · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              refine ⟨hsc₁, fun _ Q => ?_⟩; by_cases hQP : Q = P
              · subst hQP; simp only [CryptoGames.SM.GameState.record, Function.update_self]; exact hst'P
              · simp only [CryptoGames.SM.GameState.record, Function.update_of_ne hQP]
                exact optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
    · change (simulateQ ci ((challE hk₁ (2 + Δcka) qep mo.cfg mo.policy (P, m₀, m₁, r)).run es)).run sc =
          (simulateQ ci ((challE hk₂ (2 + Δcka) qep mo.cfg mo.policy (P, m₀, m₁, r)).run es)).run sc ∧
        ∀ z ∈ support ((simulateQ ci ((challE hk₂ (2 + Δcka) qep mo.cfg mo.policy (P, m₀, m₁, r)).run es)).run sc),
          OptCKASync z.1.2 z.2
      unfold challE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win) = true
      · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
        simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((mo.cfg (M := M)).challAllowedIn (s₁.epoch P))) = true
          · simp only [hch, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
          · simp only [hch, Bool.false_eq_true, ↓reduceIte]
            by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
            · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff]
              exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => by cases h'⟩⟩
            · have hs₁All : ∀ Q, OptPartySync sc Q (s₁.st Q) := fun Q => by
                rw [CryptoGames.SM.Engine.epMgmt_st_eq hep]; exact hSync.2 habF Q
              have hvs := vSend_ckaSync_gen_eq Dh prng fs Δgame tStarGame Δcka mo s₁ P (s₁.st P)
                (((mo.cfg (M := M)).challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀))
                (some (m₀, m₁)) r es.h sc hSync.1 (hs₁All P)
              simp only [hdoom, Bool.false_eq_true, ↓reduceIte]; rw [run_liftH_bind, run_liftH_bind]
              simp only [simulateQ_bind, StateT.run_bind]; rw [hvs.1]
              refine ⟨rfl, fun z hz => ?_⟩; rw [mem_support_bind_iff] at hz
              obtain ⟨⟨⟨vsRes, h'⟩, sc₁⟩, hvsMem, hz⟩ := hz; have ⟨hsc₁, hvsPost⟩ := hvs.2 _ hvsMem
              rcases vsRes with _ | ⟨st', ct⟩
              · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact ⟨hsc₁, fun h' => nomatch h'⟩
              · obtain ⟨hst'P, hepQ⟩ := hvsPost st' ct rfl
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
                refine ⟨hsc₁, fun _ Q => ?_⟩; by_cases hQP : Q = P
                · subst hQP; simp only [CryptoGames.SM.GameState.record, Function.update_self]; exact hst'P
                · simp only [CryptoGames.SM.GameState.record, Function.update_of_ne hQP]
                  exact optPartySync_of_epoch_eq (hs₁All Q) (hepQ Q hQP)
    · change (simulateQ ci ((deliverE hk₁ maxSkip mo.cfg (P, c)).run es)).run sc =
          (simulateQ ci ((deliverE hk₂ maxSkip mo.cfg (P, c)).run es)).run sc ∧
        ∀ z ∈ support ((simulateQ ci ((deliverE hk₂ maxSkip mo.cfg (P, c)).run es)).run sc),
          OptCKASync z.1.2 z.2
      unfold deliverE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hab : (es.abort || es.g.win) = true
      · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
        simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases htr : es.g.inTransit P.other c with _ | r
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
            vRecv_hooksCKA_pure_eq Dh prng fs Δcka mo es.g P (es.g.st P) c (some r) es.h sc (hSync.2 habF P)
          rw [run_liftH_bind, run_liftH_bind]; dsimp only [hk₁, hk₂]
          simp only [hvrEq, hvrPure, pure_bind]; rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
          · split_ifs <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 simulateQ_pure, support_pure, Set.mem_singleton_iff];
               exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
          · have hcm := commitE_ckaSync_gen Dh prng fs Δgame tStarGame Δcka mo es.g P (es.g.st P) st' r.pos
              { es with h := h' } sc hSync.1 (hSync.2 habF) hSync.2 (hvrPost st' t' i' m' rfl)
            simp only [StateT.run_bind, simulateQ_bind]; rw [hcm.1]
            refine ⟨rfl, fun z hz => ?_⟩; rw [mem_support_bind_iff] at hz
            obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
            obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem; rcases cmRes with _ | s₁
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; exact hcmNone rfl
            · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              refine ⟨hsc₁, fun _ Q => ?_⟩; split_ifs <;> exact hs₁Sync Q
    · change (simulateQ ci ((injectE hk₁ (2 + Δcka) qep mo.cfg (P, c)).run es)).run sc =
          (simulateQ ci ((injectE hk₂ (2 + Δcka) qep mo.cfg (P, c)).run es)).run sc ∧
        ∀ z ∈ support ((simulateQ ci ((injectE hk₂ (2 + Δcka) qep mo.cfg (P, c)).run es)).run sc),
          OptCKASync z.1.2 z.2
      unfold injectE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      by_cases href :
          (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
      · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · have habF : es.abort = false := by
          rcases h : es.abort
          · rfl
          · simp [h] at href
        obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
          vRecv_hooksCKA_pure_eq Dh prng fs Δcka mo es.g P (es.g.st P) c none es.h sc (hSync.2 habF P)
        simp only [href, Bool.false_eq_true, ↓reduceIte]; rw [run_liftH_bind, run_liftH_bind]
        dsimp only [hk₁, hk₂]; simp only [hvrEq, hvrPure, pure_bind]
        rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
          · simp only [hqep, ↓reduceIte]
            by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
            · have hcm := commitE_ckaSync_gen Dh prng fs Δgame tStarGame Δcka mo es.g P (es.g.st P) st'
                ⟨P.other, t', i'⟩ { es with h := h' } sc hSync.1 (hSync.2 habF) hSync.2
                (hvrPost st' t' i' m' rfl)
              simp only [htriv, ↓reduceIte, StateT.run_bind, simulateQ_bind]; rw [hcm.1]
              refine ⟨rfl, fun z hz => ?_⟩; rw [mem_support_bind_iff] at hz
              obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
              obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem; rcases cmRes with _ | s₁
              · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact hcmNone rfl
              · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
                simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact ⟨hsc₁, fun _ => hs₁Sync⟩
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
              split_ifs <;>
                (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                   simulateQ_pure, support_pure, Set.mem_singleton_iff];
                 exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)
    · change (simulateQ ci ((CryptoGames.SM.Construction.DeliverForge.corrEPaper hk₁ mo.policy P).run es)).run sc =
          (simulateQ ci ((CryptoGames.SM.Construction.DeliverForge.corrEPaper hk₂ mo.policy P).run es)).run sc ∧
        ∀ z ∈ support ((simulateQ ci ((CryptoGames.SM.Construction.DeliverForge.corrEPaper hk₂ mo.policy P).run es)).run sc),
          OptCKASync z.1.2 z.2
      have hRevEq : hk₁.reveal = hk₂.reveal := rfl
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaper abortE
      simp only [StateT.run_bind, StateT.run_get, pure_bind, hRevEq]; refine ⟨trivial, fun z hz => ?_⟩
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P)) = true
      · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hSync
      · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
        by_cases hdoom : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P) = true
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hz; rw [run_liftH_bind] at hz
          simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
          obtain ⟨⟨⟨revRes, h'⟩, sc₁⟩, hrev, hz⟩ := hz
          have hsc₁_eq : sc₁ = sc := by
            dsimp only [hk₂, hooksCKA] at hrev; rcases hγ : (es.g.st P).γ with _ | γ
            · simp only [hγ, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hrev
              obtain ⟨⟨⟨corrAns, h₂⟩, sc₂⟩, hcorr, hrev⟩ := hrev
              have ⟨heq, _⟩ := liftC_corrQuery_support Dh Δgame tStarGame P es.h sc hSync.1 hcorr
              subst heq; rcases corrAns with _ | γ' <;>
                (simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hrev;
                 exact (Prod.mk.inj hrev).2)
            · simp only [hγ, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hrev
              exact (Prod.mk.inj hrev).2
          subst hsc₁_eq; rcases revRes with _ | stP
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact ⟨hSync.1, fun h' => nomatch h'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hSync
  · change (simulateQ ci ((CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₁ (2 + Δcka) qep mo.cfg (P, c, c')).run es)).run sc =
        (simulateQ ci ((CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ (2 + Δcka) qep mo.cfg (P, c, c')).run es)).run sc ∧
      ∀ z ∈ support ((simulateQ ci ((CryptoGames.SM.Construction.DeliverForge.deliverForgeE hk₂ (2 + Δcka) qep mo.cfg (P, c, c')).run es)).run sc),
        OptCKASync z.1.2 z.2
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
      exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
    · have habF : es.abort = false := (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hab)).1
      simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
        exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
      · by_cases hchk : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
        · simp only [hchk, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
          exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
        · obtain ⟨hvrEq, ⟨⟨vrRes, h'⟩, hvrPure, hvrPost⟩⟩ :=
            vRecv_hooksCKA_pure_eq Dh prng fs Δcka mo es.g P (es.g.st P) c' none es.h sc (hSync.2 habF P)
          simp only [hchk, Bool.false_eq_true, ↓reduceIte]; rw [run_liftH_bind, run_liftH_bind]
          dsimp only [hk₁, hk₂]; simp only [hvrEq, hvrPure, pure_bind]
          rcases vrRes with _ | _ | ⟨st', t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact ⟨hSync.1, fun h' => nomatch h'⟩⟩
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
            exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
          · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch) = true
            · simp only [hqep, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff]
              exact ⟨trivial, fun _ h => by subst h; exact hSync⟩
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte]
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
              · have hcm := commitE_ckaSync_gen Dh prng fs Δgame tStarGame Δcka mo es.g P (es.g.st P) st'
                  ⟨P.other, t', i'⟩ { es with h := h' } sc hSync.1 (hSync.2 habF) hSync.2
                  (hvrPost st' t' i' m' rfl)
                simp only [htriv, ↓reduceIte, StateT.run_bind, simulateQ_bind]; rw [hcm.1]
                refine ⟨rfl, fun z hz => ?_⟩; rw [mem_support_bind_iff] at hz
                obtain ⟨⟨⟨cmRes, es₁⟩, sc₁⟩, hcmMem, hz⟩ := hz
                obtain ⟨hsc₁, hcmNone, hcmSome⟩ := hcm.2 _ hcmMem; rcases cmRes with _ | s₁
                · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact hcmNone rfl
                · obtain ⟨_, hs₁Sync⟩ := hcmSome s₁ rfl
                  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                    simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
                  subst hz; exact ⟨hsc₁, fun _ => hs₁Sync⟩
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                split_ifs <;>
                  (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                     simulateQ_pure, support_pure, Set.mem_singleton_iff];
                   exact ⟨trivial, fun _ h => by subst h; exact hSync⟩)

private lemma simulateQ_implEDFPaper_ckaSync_gen_eq {KR RSt SS RS M E K α : Type}
    [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (Δgame tStarGame Δcka qep maxSkip : ℕ) (mo : Mode)
    (oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (PartyState (DdhSt Pt) Pt RSt SS RS) M (BitVec 256) (Header Pt × E) α)
    (es : EState (VP (Option (DdhSt Pt)) Pt RSt SS RS) M (Header Pt × E) (CKAState Pt Pt))
    (sc : CryptoGames.CKA.GameState (DdhSt Pt) Pt) (hSync : OptCKASync es sc) :
    (simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es)).run sc =
    (simulateQ (ckaFullImpl (dhScheme Dh) Δgame tStarGame)
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksCKA (dhScheme Dh) prng fs Δcka mo)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy) oa).run es)).run sc := by
  induction oa using OracleComp.inductionOn generalizing es sc with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · have hInl₁ :
          (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksCKA (dhSchemeFb Dh) prng fs Δcka mo)
            (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inl n)).run es = (coinsE n).run es := rfl
      have hInl₂ :
          (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksCKA (dhScheme Dh) prng fs Δcka mo)
            (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl₁, hInl₂]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, simulateQ_bind, simulateQ_HasQuery_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at hmem
      have hInlQ : ckaFullImpl (dhScheme Dh) Δgame tStarGame (Sum.inl n) =
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
    · have hStep := implEDFPaper_ckaSync_gen_eq Dh prng fs Δgame tStarGame Δcka qep maxSkip mo es sc t_sm hSync
      rw [hStep.1]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, sc'⟩ hmem =>
        ih u es' sc' (hStep.2 ((u, es'), sc') hmem)

private lemma ckaBranch_redCKAAuthDFPaper_dhSchemeFb_eq {KR RSt K SS RS M E : Type}
    [SampleableType KR] [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δgame tStarGame Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (b : Bool)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF (DdhSt Pt) Pt RSt SS RS M (BitVec 256) E) :
    CryptoGames.CKA.branch (dhSchemeFb Dh) Δgame tStarGame b
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper (dhSchemeFb Dh) prng fs lam Δcka qep tL t A) =
    CryptoGames.CKA.branch (dhScheme Dh) Δgame tStarGame b
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper (dhScheme Dh) prng fs lam Δcka qep tL t A) := by
  let mo : Mode := ⟨true, tL, t⟩
  rw [ckaBranch_dhSchemeFb_eq]
  unfold CryptoGames.CKA.branch CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper CryptoGames.SM.Construction.DeliverForge.authSimDFPaper CryptoGames.SM.Construction.DeliverForge.engRunDFPaper
  refine bind_congr fun k => ?_; rw [StateT.run'_eq, StateT.run'_eq]; refine congrArg (Prod.fst <$> ·) ?_
  have hInit : initCKA (dhSchemeFb Dh) prng fs lam mo = initCKA (dhScheme Dh) prng fs lam mo := rfl
  rw [hInit]; simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  let sc := CryptoGames.CKA.initState (dhScheme Dh) k b
  have hsc : CkaStateInv sc := ckaStateInv_init Dh k b
  have hep₀ : ∀ P, sc.epoch P = 0 := fun _ => rfl
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨vs, h⟩, sc₁⟩ hmem => ?_
  have hSyncInit : sc₁ = sc ∧ ∀ vA vB, vs = some (vA, vB) → OptCKASync (M := M) (E := E)
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } sc := by
    unfold initCKA at hmem
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, bind_assoc, pure_bind] at hmem
    rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hmem
    simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hmem; obtain ⟨kr, _, hmem⟩ := hmem
    rcases htL : mo.tL with _ | tLv
    · simp only [htL, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind] at hmem
      rw [sampleT, simulateQ_ckaFullImpl_liftProb] at hmem
      simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
      obtain ⟨kc, _, hmem⟩ := hmem; rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩
      rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
      refine ⟨hscEq, fun vA vB hEq => ?_⟩; rw [hvs, Option.some.injEq] at hEq; cases hEq
      refine ⟨hsc, fun _ P => ?_⟩; cases P
      · exact ⟨rfl, ddhRoleOk_initA Dh kc⟩
      · exact ⟨rfl, ddhRoleOk_initB Dh kc⟩
    · simp only [htL, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
      rcases Prod.mk.inj hmem with ⟨hEq1, hscEq⟩; rcases Prod.mk.inj hEq1 with ⟨hvs, _⟩
      refine ⟨hscEq, fun vA vB hEq => ?_⟩; rw [hvs, Option.some.injEq] at hEq; cases hEq
      exact ⟨hsc, fun _ P => by cases P <;> exact ⟨rfl, (hep₀ _).symm⟩⟩
  obtain ⟨hscEq, hSyncInit⟩ := hSyncInit; rw [hscEq]
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · dsimp only; simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc]
    exact congrArg (· >>= _) (simulateQ_implEDFPaper_ckaSync_gen_eq Dh prng fs Δgame tStarGame Δcka qep
      fs.maxSkip mo A _ sc (hSyncInit vA vB rfl))

omit [Zero Pt] [SampleableType Pt] in
private lemma implEDFPaper_hooksFS_ext_skippedLenLe {KC Γ CCoins I KR RSt K MK M C : Type}
    [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header Pt) M C) (G : ℕ → PRGScheme K (K × MK))
    (maxSkip k Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK))) M (Header Pt × (ℕ × C))
      (FSState Pt RSt K I (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header Pt × (ℕ × C))).Domain)
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header Pt) M (ℕ × C))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : OptSkippedLenLe (es.h.ext.map Prod.snd)) (hSt : SkippedLenLe st.receiverState)
    (z : ((unifSpec + CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState K)
          (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header Pt × (ℕ × C))).Range (.inr t_sm) ×
        EState (VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
          (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK))) M (Header Pt × (ℕ × C))
          (FSState Pt RSt K I (CryptoGames.FSAEAD.RatchetSenderState K)
            (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C))) ×
      CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
        (Header Pt) M (ℕ × C))
    (hz : z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr t_sm)).run es)).run st)) :
    OptSkippedLenLe (z.1.2.h.ext.map Prod.snd) := by
  have hCommitEq : ∀ s₀ P₀ old₀ new₀ pos₀ (es₀ : EState _ M (Header Pt × (ℕ × C)) _),
      (commitE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j) s₀ P₀ old₀ new₀ pos₀).run es₀ =
      pure (some (s₀.accept P₀ new₀ pos₀), es₀) := by
    intros; unfold commitE CryptoGames.SM.Engine.liftH hooksFS; simp [StateT.run]; rfl
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · exact implE_hooksFS_ext_skippedLenLe cka prng ae G maxSkip k Δcka qep mo j es
        (.inl (.inl (.inl (.inl (P, m, r))))) st hVR hExt hSt z hz
    · exact implE_hooksFS_ext_skippedLenLe cka prng ae G maxSkip k Δcka qep mo j es
        (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))) st hVR hExt hSt z hz
    · exact implE_hooksFS_ext_skippedLenLe cka prng ae G maxSkip k Δcka qep mo j es
        (.inl (.inl (.inr (P, c)))) st hVR hExt hSt z hz
    · exact implE_hooksFS_ext_skippedLenLe cka prng ae G maxSkip k Δcka qep mo j es
        (.inl (.inr (P, c))) st hVR hExt hSt z hz
    · change z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
        ((CryptoGames.SM.Construction.DeliverForge.corrEPaper (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          mo.policy P).run es)).run st) at hz
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaper abortE at hz; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
      by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
      · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; exact hExt
      · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
        by_cases hdoom : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P)
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hExt
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte] at hz; rw [run_liftH_bind] at hz
          simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
          obtain ⟨⟨⟨revRes, h'⟩, st'⟩, hrev, hz⟩ := hz
          have hExt' := fsReveal_ext_skippedLenLe cka prng ae G maxSkip Δcka mo j
            es.g P (es.g.st P) es.h st hExt hSt ((revRes, h'), st') hrev
          rcases revRes with _ | stP <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hExt')
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((CryptoGames.SM.Construction.DeliverForge.deliverForgeE _ (2 + Δcka) qep mo.cfg (P, c, c')).run es) at hmem
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [htr] at hmem
        by_cases hchk : ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1)
        · simp only [hchk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
        · simp only [hchk, Bool.false_eq_true, ↓reduceIte, run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
          have hExt' := vRecv_ext_skippedLenLe cka prng ae G maxSkip k Δcka mo j
            es.g P (es.g.st P) c' none es.h (hVR P) hExt (vrRes, h') hvr
          rcases vrRes with _ | _ | ⟨stP, t', i', m'⟩
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt'
          · by_cases hqep : (decide (qep + 1 < t') || t' != r.pos.epoch)
            · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
              by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
              · simp only [htriv, ↓reduceIte, StateT.run_bind, hCommitEq, pure_bind,
                  StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                split_ifs at hmem <;>
                  (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                     support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
                   rcases hmem with ⟨_, rfl⟩; exact hExt')

omit [Zero Pt] [SampleableType Pt] in
private lemma implEDFPaper_hooksFS_fsClamp_fsAtomicB_eq {KC Γ CCoins I KR RSt : Type} [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B B0 B_q q' Δcka qep : ℕ) (mo : Mode) (j : ℕ) (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP Γ Pt RSt (Option SS256) (Option RS256)) (Msgℓ ℓ) (Header Pt × CtSalt)
      (FSState Pt RSt (BitVec 256) I SS256 RS256 CtSalt))
    (t_sm : (CryptoGames.SM.Construction.DeliverForge.specDF (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins (Header Pt × CtSalt)).Domain)
    (hBad : badSendMsgDF (St := PartyState Γ Pt RSt SS256 RS256) (Coins := CCoins) (C := Header Pt × CtSalt)
      (fun m => atomicShortPubB m.1) (.inr t_sm) = false)
    (hVR : SMVRInv (FSVROkStep maxForwardJumps) B_q (q' + 1) es.g)
    (hLen : SMVRInv (fun _ => OptSkippedLenLe) B_q (q' + 1) es.g)
    (hExt : FSVROkStep maxForwardJumps (B_q - (q' + 1)) (es.h.ext.map Prod.snd))
    (hExtLen : OptSkippedLenLe (es.h.ext.map Prod.snd)) :
    (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr t_sm)).run es =
      (CryptoGames.SM.Construction.DeliverForge.implEDFPaper
        (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr t_sm)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t_sm with t5 | ⟨P, c, c'⟩
  · have hBad5 := badSendMsgDF_inl_to_badSendMsg (fun m => atomicShortPubB m.1) t5 hBad
    rcases t5 with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
    · exact implE_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 B_q q' Δcka qep mo j
        hB0 es (.inl (.inl (.inl (.inl (P, m, r))))) hBad5 hVR hLen hExt hExtLen
    · exact implE_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 B_q q' Δcka qep mo j
        hB0 es (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))) hBad5 hVR hLen hExt hExtLen
    · exact implE_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 B_q q' Δcka qep mo j
        hB0 es (.inl (.inl (.inr (P, c)))) hBad5 hVR hLen hExt hExtLen
    · exact implE_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 B_q q' Δcka qep mo j
        hB0 es (.inl (.inr (P, c))) hBad5 hVR hLen hExt hExtLen
    · change (CryptoGames.SM.Construction.DeliverForge.corrEPaper _ mo.policy P).run es =
        (CryptoGames.SM.Construction.DeliverForge.corrEPaper _ mo.policy P).run es
      unfold CryptoGames.SM.Construction.DeliverForge.corrEPaper hooksFS; rfl
  · change (CryptoGames.SM.Construction.DeliverForge.deliverForgeE _ (2 + Δcka) qep mo.cfg (P, c, c')).run es =
      (CryptoGames.SM.Construction.DeliverForge.deliverForgeE _ (2 + Δcka) qep mo.cfg (P, c, c')).run es
    have hCommit : commitE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j) =
        commitE (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j) := by
      unfold commitE hooksFS; rfl
    unfold CryptoGames.SM.Construction.DeliverForge.deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · dsimp only; split_ifs
        · rfl
        · simp only [run_liftH_bind, vRecv_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf
            B B0 (B_q - (q' + 1)) Δcka mo j hkB es.g P (es.g.st P) c' none es.h
            (hVR P) (hLen P) hExt hExtLen, hCommit]

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_implEDFPaper_fsClamp_fsAtomicB_eq {KC Γ CCoins I KR RSt α : Type}
    [DecidableEq I] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L B B0 B_q q Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B) (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : CryptoGames.SM.Construction.DeliverForge.AdversaryCompDF (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins
      (Header Pt × CtSalt) α}
    (hoa : oa.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins (Header Pt × CtSalt))) q)
    (hSendOk : oa.IsQueryBoundP (fun t => badSendMsgDF (St := PartyState Γ Pt RSt SS256 RS256)
      (Coins := CCoins) (C := Header Pt × CtSalt) (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP Γ Pt RSt (Option SS256) (Option RS256)) (Msgℓ ℓ) (Header Pt × CtSalt)
      (FSState Pt RSt (BitVec 256) I SS256 RS256 CtSalt))
    (st : CryptoGames.FSAEAD.State SS256 RS256 (Header Pt) (Msgℓ ℓ) CtSalt)
    (hInv : SMEngineInv L B_q q es.g) (hVR : SMVRInv (FSVROkStep maxForwardJumps) B_q q es.g)
    (hLen : SMVRInv (fun _ => OptSkippedLenLe) B_q q es.g)
    (hExt : FSVROkStep maxForwardJumps (B_q - q) (es.h.ext.map Prod.snd))
    (hExtLen : OptSkippedLenLe (es.h.ext.map Prod.snd))
    (hSt : RSReach maxForwardJumps (B_q - q) st.receiverState)
    (hStLen : SkippedLenLe st.receiverState) :
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper
        (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) oa).run es)).run st =
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      ((simulateQ (CryptoGames.SM.Construction.DeliverForge.implEDFPaper
        (hooksFS cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) oa).run es)).run st := by
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
          (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inl n)).run es =
            (coinsE n).run es := rfl
      have hInl2 :
          (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksFS cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inl n)).run es =
            (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem1; obtain ⟨_, _, _, rfl⟩ := hmem1
      have hQbCoins := CryptoGames.SM.Construction.ReductionsQueries.qb_coinsE
        (CryptoGames.SM.Construction.ReductionsQueries.hQu_QFSDec SS256 RS256 Pt (LibsignalMsgPublicPart × Plain ℓ) CtSalt) n es'
      have hSt' : RSReach maxForwardJumps (B_q - q) st'.receiverState := by
        simpa using receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps hQbCoins st hSt
          ((u, es'), st') hmem
      have hStLen' : SkippedLenLe st'.receiverState :=
        fsFullImpl_skippedLenLe ae G maxForwardJumps ((coinsE n).run es') st hStLen ((u, es'), st') hmem
      exact ih u q (hmx u) (hSendMx u) es' st' hInv hVR hLen hExt hExtLen hSt' hStLen'
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq0.resolve_left (by decide); omega⟩
      have hStep1 := implEDFPaper_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf
        B B0 B_q q' Δcka qep mo j hB0 es t_sm hBad hVR hLen hExt hExtLen
      have hStep2 :
          (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksFS cka prng
              (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr t_sm)).run es =
            (CryptoGames.SM.Construction.DeliverForge.implEDFPaper (hooksFS cka prng
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr t_sm)).run es :=
        implEDFPaper_fsClamp_eq cka prng ae G maxForwardJumps B B_q q' Δcka qep mo j hB es t_sm hVR hExt
      rw [hStep1, hStep2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      have hBq : B_q - (q' + 1) + 1 ≤ B_q - q' := by have := hInv.1; omega
      have hQbStep := qb_implEDFPaper_inr_one
        (CryptoGames.SM.Construction.ReductionsQueries.hQu_QFSDec SS256 RS256 Pt (LibsignalMsgPublicPart × Plain ℓ) CtSalt)
        (CryptoGames.SM.Construction.ReductionsQueries.hQt_QFSDec _ _ Pt _ _) (CryptoGames.SM.Construction.ReductionsQueries.hQch_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQcs_QFSDec _ _ Pt _ _) (CryptoGames.SM.Construction.ReductionsQueries.hQcr_QFSDec _ _ Pt _ _)
        cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka qep mo j t_sm es
      exact ih u q' (by simpa using hmx u) (hSendMx u) es' st'
        (implEDFPaper_inv (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
          mo.cfg mo.policy es t_sm hInv (u, es') hmem1)
        (implEDFPaper_vrInv (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
          (hooksFS_vrInv_fromAEADPRG cka prng ae G maxForwardJumps Δcka mo j)
          mo.cfg mo.policy es t_sm hInv hVR (u, es') hmem1)
        (implEDFPaper_vrInv (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
          (hooksFS_vrInv_skippedLenLe cka prng ae G maxForwardJumps Δcka mo j)
          mo.cfg mo.policy es t_sm hInv hLen (u, es') hmem1)
        ((implEDFPaper_ext_snd_fromAEADPRG cka prng ae G maxForwardJumps (B_q - (q' + 1)) Δcka qep
          mo j es t_sm st (fun P _ _ hv => hVR P _ _ hv) hExt hSt ((u, es'), st') hmem).mono hBq)
        (implEDFPaper_hooksFS_ext_skippedLenLe cka prng ae G maxForwardJumps (B_q - (q' + 1)) Δcka qep
          mo j es t_sm st (fun P _ _ hv => hVR P _ _ hv) hExtLen hStLen ((u, es'), st') hmem)
        ((receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps hQbStep st hSt
          ((u, es'), st') hmem).mono hBq)
        (fsFullImpl_skippedLenLe ae G maxForwardJumps _ st hStLen ((u, es'), st') hmem)

omit [Zero Pt] [SampleableType Pt] in
private lemma simulateQ_runFSDFPaper_fsClamp_fsAtomicB_eq_lFS {KC Γ CCoins I KR RSt : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B B0 B_q Δcka qep : ℕ) (lam : I) (mo : Mode) (j : ℕ) (b : Bool)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B) (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.SchemeAdversaryDF Γ Pt RSt SS256 RS256 (Msgℓ ℓ) CCoins CtSalt)
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m => atomicShortPubB m.1) A)
    (st₀ : CryptoGames.FSAEAD.State SS256 RS256 (Header Pt) (Msgℓ ℓ) CtSalt)
    (hSt₀ : RSReach maxForwardJumps 0 st₀.receiverState) (hStLen₀ : SkippedLenLe st₀.receiverState) :
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      (runFSDFPaper cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep mo j b A)).run st₀ =
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      (runFSDFPaper cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep mo j b A)).run st₀ := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  have hA' : A.IsQueryBoundP (ReductionDsl.isGameQuery (G := CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ Pt RSt SS256 RS256) (Msgℓ ℓ) CCoins (Header Pt × CtSalt))) qAdv := by
    refine hA.of_imp fun x hx => ?_; rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  rw [runFSDFPaper_eq_bind_initFSRaw, runFSDFPaper_eq_bind_initFSRaw]
  have hS1 : (fsClamp B (fsAtomicB C ℓ encT idOf B0)).initSender =
      (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps).initSender := rfl
  have hR1 : (fsClamp B (fsAtomicB C ℓ encT idOf B0)).initReceiver =
      (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps).initReceiver := rfl
  have hS2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender =
      (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps).initSender := rfl
  have hR2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver =
      (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps).initReceiver := rfl
  have hInitEq : initFSRaw cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam mo j b =
      initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b := by
    simp only [initFSRaw, hS1, hR1]
  have hInitEq2 : initFSRaw cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo j b =
      initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b := by
    simp only [initFSRaw, hS2, hR2]
  rw [hInitEq, hInitEq2, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨es₀, st₁⟩ hmem₀ => ?_
  have hes₀ := fst_mem_support_of_mem_support_simulateQ_run _ _ st₀ hmem₀
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b
    hqB le_rfl (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)) es₀ hes₀
  have ⟨hVR₀, hext₀⟩ := initFSRaw_vrInv_fromAEADPRG cka prng ae G maxForwardJumps lam mo j b
    B_q qAdv es₀ hes₀
  have hLen₀ := initFSRaw_skippedLenLe cka prng ae G maxForwardJumps lam mo j b B_q qAdv es₀ hes₀
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  have hSim := simulateQ_implEDFPaper_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf
    (B_q + 1) B B0 B_q qAdv Δcka qep mo j hB hB0 hA' hSendOk es₀ st₁ hInv₀.sm hVR₀ hLen₀
    (by simp [hext₀, FSVROkStep]) (by simp [hext₀, OptSkippedLenLe])
    ((receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps
      (isQueryBoundP_initFSRaw_dec cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b)
      st₀ hSt₀ (es₀, st₁) hmem₀).mono (Nat.zero_le _))
    (fsFullImpl_skippedLenLe ae G maxForwardJumps
      (initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b) st₀ hStLen₀
      (es₀, st₁) hmem₀)
  have hms1 : (fsClamp B (fsAtomicB C ℓ encT idOf B0)).maxSkip = maxForwardJumps := rfl
  have hms2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms1, hms2, hSim]

theorem ckaAdvantage_redCKAAuthDFPaper_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δgame tStarGame Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.CKA.advantage (dhSchemeFb Dh) Δgame tStarGame
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A) =
    CryptoGames.CKA.advantage (dhScheme Dh) Δgame tStarGame
      (CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL t A) := by
  have hFs :
      CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A =
      CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL t A := by
    have hEng := runCKADFPaper_fsAtomicB_eq_lFS
      (dhSchemeFb Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt) C ℓ encT idOf lam B0 B_q Δcka qep
      ⟨true, tL, t⟩ false hB0 A qAdv hA hqB hSendOk
    simp only [CryptoGames.SM.Construction.Mode.cfg, ↓reduceIte] at hEng
    unfold CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper
    dsimp only
    exact congrArg (· >>= _) hEng
  rw [hFs, CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
    ckaBranch_redCKAAuthDFPaper_dhSchemeFb_eq Dh (rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δgame tStarGame Δcka qep tL t true A,
    ckaBranch_redCKAAuthDFPaper_dhSchemeFb_eq Dh (rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δgame tStarGame Δcka qep tL t false A]

theorem prngAdvantage_redPRNGAuthDFPaper_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep tL t A) := by
  rw [redPRNGAuthDFPaper_dhSchemeFb_eq Dh (rootPRNG C.F encPt)
      (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A,
    redPRNGAuthDFPaper_fsAtomicB_eq_lFS (dhScheme Dh) (rootPRNG C.F encPt)
      C ℓ encT idOf lam B0 B_q Δcka qep tL t hB0 A qAdv hA hqB hSendOk]

theorem fsaeadGame_redFSAuthDFPaper_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep j : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (qAdv : ℕ) (hA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep j tL t A) =
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep j tL t A) := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  unfold CryptoGames.FSAEAD.game CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper
  dsimp only
  refine bind_congr fun b => bind_congr fun k => ?_
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine congrArg (· >>= _) ?_
  have h1 := runFSDFPaper_dhSchemeFb_eq Dh (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (CryptoGames.SM.Construction.fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep ⟨true, tL, t⟩ j false A
  have h2 := simulateQ_runFSDFPaper_fsClamp_fsAtomicB_eq_lFS (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
    C ℓ encT idOf B B0 B_q Δcka qep lam ⟨true, tL, t⟩ j false hB hB0 A qAdv hA hqB hSendOk
    (CryptoGames.FSAEAD.initState (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) k b)
    (CryptoGames.SM.Engine.RSReach.init ae G maxForwardJumps k) (skippedLenLe_init ae G maxForwardJumps k)
  exact Eq.trans
    (congrArg (fun x => StateT.run
      (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) x)
      (CryptoGames.FSAEAD.initState (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) k b)) h1)
    h2

end FsAtomicBSwapPaperHelpers

theorem compileCkaDFAtomic_casePaper_advantage
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δgame tStarGame qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let cka := dhScheme Dh; let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    CryptoGames.CKA.advantage (dhScheme Dh) Δgame tStarGame
      ((compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (redCKAAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps tL t)).eval (fun _ => A) ()) =
    CryptoGames.CKA.advantage (dhScheme Dh) Δgame tStarGame
      (if 2 ≤ t ∧ tL = some (t - 2) then
        CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A
      else if 3 ≤ t ∧ tL = some (t - 3) then
        CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A
      else
        CryptoGames.SM.Construction.DeliverForge.redCKAAuthDFPaper cka prng fs lam 1 qep tL t A) := by
  intro B0 cka prng fs
  unfold redCKAAuthDFCasePaperProg
  split_ifs
  · rw [← redCKAAuthDFShiftedPaperGen_zero cka prng fs lam qep (t - 1) t A]
    exact compileCkaDFAtomic_shiftedPaperGen_advantage Dh encPt C ℓ hℓ encT idOf lam
      Δgame tStarGame 0 qep q (t - 1) 0 t A hqA hshA
  · rw [← redCKAAuthDFShiftedPaperGen_one cka prng fs lam qep (t - 2) t A]
    exact compileCkaDFAtomic_shiftedPaperGen_advantage Dh encPt C ℓ hℓ encT idOf lam
      Δgame tStarGame 1 qep q (t - 2) t t A hqA hshA
  · rw [ckaAdvantage_congr (dhScheme Dh) Δgame tStarGame
        (compileCkaDFAtomic_paper_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam 1 qep q tL t A hqA),
      ← ckaAdvantage_dhSchemeFb_eq]
    exact ckaAdvantage_redCKAAuthDFPaper_atomic_eq Dh encPt C ℓ encT idOf lam
      B0 q Δgame tStarGame 1 qep tL t (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA

theorem compilePrngDFAtomic_casePaper_advantage
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let cka := dhScheme Dh; let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    CryptoGames.PRFPRNG.advantage prng
      ((compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (redPRNGAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps tL t)).eval (fun _ => A) ()) =
    CryptoGames.PRFPRNG.advantage prng
      (if 2 ≤ t ∧ tL = some (t - 2) then
        CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A
      else if 3 ≤ t ∧ tL = some (t - 3) then
        CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A
      else
        CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFPaper cka prng fs lam 1 qep tL t A) := by
  intro B0 cka prng fs
  unfold redPRNGAuthDFCasePaperProg
  split_ifs
  · rw [← CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen_false cka prng fs lam qep (t - 1) t A]
    exact compilePrngDFAtomic_shiftedPaperGen_advantage Dh encPt C ℓ hℓ encT idOf lam
      0 qep q (t - 1) t false A hqA hshA
  · rw [← CryptoGames.SM.Construction.DeliverForge.redPRNGAuthDFShiftedPaperGen_true cka prng fs lam 1 qep (t - 2) t A]
    exact compilePrngDFAtomic_shiftedPaperGen_advantage Dh encPt C ℓ hℓ encT idOf lam
      1 qep q (t - 2) t true A hqA hshA
  · rw [prngAdvantage_congr prng
        (BundlesEval.compilePrngDFAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0
          (CryptoGames.SM.Construction.redPRNGAuthDFPaperProg (q + 1) B0 1 qep maxForwardJumps tL t) A),
      redPRNGAuthDFPaperProg_advantage_atomic Dh encPt C ℓ encT idOf lam 1 qep q tL t A hqA]
    exact prngAdvantage_redPRNGAuthDFPaper_atomic_eq Dh encPt C ℓ encT idOf lam
      B0 q 1 qep tL t (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA

theorem compileFsDFAtomic_casePaper_game_evalDistEq
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let cka := dhScheme Dh; let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    CryptoGames.FSAEAD.game fs
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (redFSAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps j tL t)).eval (fun _ => A) ()) =ᵈ
    CryptoGames.FSAEAD.game fs
      (if 2 ≤ t ∧ tL = some (t - 2) then
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedDir2Paper cka prng fs lam qep j (t - 1) t A
      else if 3 ≤ t ∧ tL = some (t - 3) then
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaper cka prng fs lam 1 qep j (t - 2) t A
      else
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper cka prng fs lam 1 qep j tL t A) := by
  intro B0 cka prng fs
  unfold redFSAuthDFCasePaperProg
  split_ifs
  · rw [← CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen_false cka prng fs lam qep j (t - 1) t A]
    exact compileFsDFAtomic_shiftedPaperGen_game_evalDistEq Dh encPt C ℓ hℓ encT idOf lam
      0 qep q j (t - 1) t false A hqA hshA
  · rw [← CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaperGen_true cka prng fs lam 1 qep j (t - 2) t A]
    exact compileFsDFAtomic_shiftedPaperGen_game_evalDistEq Dh encPt C ℓ hℓ encT idOf lam
      1 qep q j (t - 2) t true A hqA hshA
  · have h1 := fsaeadGame_evalDistEq_of_coinSimEquiv fs
      (compileFsDFAtomic_paper_coinSimEquiv Dh encPt C ℓ hℓ encT idOf lam 1 qep q j tL t A hqA)
    have h2 := fsaeadGame_redFSAuthDFPaper_atomic_eq Dh encPt C ℓ encT idOf lam
      B0 B0 q 1 qep j tL t (Nat.le_refl _) (Nat.le_refl _) A q hqA (Nat.le_refl q) hshA
    rwa [h2] at h1

theorem compileFsDFAtomic_casePaper_advantage
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let cka := dhScheme Dh; let prng := rootPRNG C.F encPt
    let fs := lFS C protoSignalCodec ℓ encT idOf maxForwardJumps
    CryptoGames.FSAEAD.advantage fs
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
          (redFSAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps j tL t)).eval (fun _ => A) ()) =
    CryptoGames.FSAEAD.advantage fs
      (if 2 ≤ t ∧ tL = some (t - 2) then
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedDir2Paper cka prng fs lam qep j (t - 1) t A
      else if 3 ≤ t ∧ tL = some (t - 3) then
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFShiftedPaper cka prng fs lam 1 qep j (t - 2) t A
      else
        CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper cka prng fs lam 1 qep j tL t A) := by
  intro B0 cka prng fs
  unfold CryptoGames.FSAEAD.advantage
  rw [(compileFsDFAtomic_casePaper_game_evalDistEq Dh encPt C ℓ hℓ encT idOf lam
    qep q j tL t A hqA hshA).evalDist_eq]

/-! ## `FsOk` and `EncMsgsOk` bridges -/

theorem compileFsDFAtomic_paper_fsOk_and_encAtomicShort
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (Δcka qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hqA : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF A q)
    (heqA : EqualPubChallsDF (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) A)
    (hshA : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hgA : GuardedSMDFShort A) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R_ev := (compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
      (CryptoGames.SM.Construction.redFSAuthDFPaperProg (q + 1) B0 Δcka qep maxForwardJumps j tL t)).eval
        (fun _ => A) ()
    FsOk ℓ (2 * q) q R_ev ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R_ev := by
  intro B0 R_ev
  let cka := dhSchemeFb Dh
  let prng := rootPRNG C.F encPt
  let fsC := CryptoGames.SM.Construction.fsClamp B0 (fsAtomicB C ℓ encT idOf B0)
  have hSub : QuerySubsumes R_ev (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper cka prng fsC lam Δcka qep j tL t A) :=
    compileFsDFAtomic_paper_querySubsumes Dh encPt C ℓ hℓ encT idOf lam Δcka qep q j tL t A hqA
  have hEv := redFSAuthDFPaperProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam
    Δcka qep q j tL t A hqA
  have hQ : CryptoGames.FSAEAD.MakesAtMostQueries
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper cka prng fsC lam Δcka qep j tL t A) (2 * q) := by
    rw [← hEv]
    exact CryptoGames.SM.Construction.redFSAuthDFPaperProg_queries (q + 1) B0 Δcka qep maxForwardJumps j tL t A q hqA
  have hDQ : CryptoGames.FSAEAD.MakesAtMostDecQueries
      (CryptoGames.SM.Construction.DeliverForge.redFSAuthDFPaper cka prng fsC lam Δcka qep j tL t A) q := by
    rw [← hEv]
    exact CryptoGames.SM.Construction.redFSAuthDFPaperProg_decQueries (q + 1) B0 Δcka qep maxForwardJumps j tL t A q hqA
  have hEncAt : CryptoGames.FSAEAD.EncMsgsOk
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R_ev :=
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadEncMsgsOk_of_querySubsumes hSub
      (CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSAuthDFPaper_short cka prng fsC lam Δcka qep j tL t
          (CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed.validQ_encBadMsg ⟨true, tL, t⟩
            (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)) A hshA))
  exact ⟨⟨Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadMakesAtMostQueries_of_querySubsumes hSub hQ,
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadMakesAtMostDecQueries_of_querySubsumes hSub hDQ,
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadEqualPubChallenges_of_querySubsumes hSub
      (CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSAuthDFPaper_restricted cka prng fsC lam Δcka qep j tL t
          (CryptoGames.LibsignalSM.Proofs.RestrictedReds.validQ_unequalPubChall ⟨true, tL, t⟩) A heqA)),
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.fsaeadAllQueriesInOneADClass_of_querySubsumes hSub
      ⟨t, CryptoGames.LibsignalSM.Proofs.RestrictedReds.SafePost.to_isQueryBoundP
        (safePost_redFSAuthDFPaper_restricted cka prng fsC lam Δcka qep j tL t
          (CryptoGames.LibsignalSM.Proofs.RestrictedReds.validQ_offClass ⟨true, tL, t⟩
            (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1)) A heqA)⟩,
    encMsgsOk_shortB_of_atomicShortPubB hEncAt,
    Computational.Proofs.SessionCostedFig8.QuerySubsumes.QuerySubsumes.guardedFSInjectShort_of_querySubsumes hSub
      (guardedFSInjectShort_redFSAuthDFPaper cka prng fsC
        (fsClamp_fsAtomicB_fsSendShort C ℓ hℓ encT idOf B0 B0) lam Δcka qep j tL t A hshA hgA)⟩,
    hEncAt⟩

theorem compileFsDFAtomic_casePaper_challSimDF'Paper_fsOk_and_encAtomicShort
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : CryptoGames.SM.Construction.DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt))
    (hq_df : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv)
    (hg_df : GuardedSMDFShort dfAdv) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let challAdvDF := CryptoGames.SM.Construction.DeliverForge.challSimDF'Paper (2 + 1) qep dfAdv
    let R_ev := (compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
      (redFSAuthDFCasePaperProg (q + 1) B0 qep maxForwardJumps j tL t)).eval
        (fun _ => challAdvDF) ()
    FsOk ℓ (2 * q) q R_ev ∧
      CryptoGames.FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) R_ev := by
  intro B0 challAdvDF
  have hq_c : CryptoGames.SM.Construction.DeliverForge.MakesAtMostQueriesDF challAdvDF q :=
    challSimDF'Paper_queries (2 + 1) qep dfAdv hq_df
  have heq_c : EqualPubChallsDF (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) challAdvDF :=
    challSimDF'Paper_equalPub (2 + 1) qep (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) dfAdv
  have hsh_c : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1)
      challAdvDF :=
    challSimDF'Paper_sendOk (2 + 1) qep
      (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv hsh_df
  have hg_c : GuardedSMDFShort challAdvDF :=
    challSimDF'Paper_guardedSMDFShort (2 + 1) qep dfAdv hg_df
  dsimp only
  unfold redFSAuthDFCasePaperProg
  split_ifs
  · exact compileFsDFAtomic_shiftedPaperGen_fsOk_and_encAtomicShort Dh encPt C ℓ hℓ encT idOf lam
      0 qep q j (t - 1) t false challAdvDF hq_c heq_c hsh_c hg_c
  · exact compileFsDFAtomic_shiftedPaperGen_fsOk_and_encAtomicShort Dh encPt C ℓ hℓ encT idOf lam
      1 qep q j (t - 2) t true challAdvDF hq_c heq_c hsh_c hg_c
  · exact compileFsDFAtomic_paper_fsOk_and_encAtomicShort Dh encPt C ℓ hℓ encT idOf lam
      1 qep q j tL t challAdvDF hq_c heq_c hsh_c hg_c

end PaperAtomicBridges

end Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper
