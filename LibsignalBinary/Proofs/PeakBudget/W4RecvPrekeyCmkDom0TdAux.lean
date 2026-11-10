/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CmkLoopAdvanceCredit
public import LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhErr
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Tight `SR`-Parametric Credit & Group Specs for `Cmk` `try_decrypt`

`StatesRecv`-parametric (`SR : W4StatesRecvEnv`, `StatesRecvProtoEnv'` specialization) tight
`fineCostModel` `PhaseCreditSpec` and `PhaseGroupSpec` instances for:
- `w4c_SpqrRecvC07BytesSrEnvOf SR F K maxOps` (`(23313687, 605066, 621350, 302480)` credit;
  `140011 * maxOps + 459164942` split groups);
- `s3DefaultEnv C`, `s7Env C.F uuidTryParse`, `s8Env`, `w4c_s8FailEnv`, and `s9Env`;
- `w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps C K` (up to `25,000` forward jumps);
- `w4c_TryDecryptCliLinkedFailSrEnvOf SR CmkLoopAdvanceEvs maxOps C K` and
  `W4FailedTdCancelCmkSrEnvOf SR CmkLoopAdvanceEvs maxOps C K` (`Δlive = 0`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux

open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession
  (ChainKey Crypto MessageKeyGenerator MessageKeys Mut PublicKey RatchetState ReceiverChain
   SessionState ShaCompress SignalMessage TripleRatchet maxForwardJumps maxMessageKeys
   maxReceiverChains rootCreateChain)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB spqrAuthApi
   spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (fromSessionState_exec)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
  (dhRatchetStep_none dhRatchetStep_some_eq)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser coinsOf serviceIdParse uuidTryParse)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (BoundedFreshEvs aesDecCtShape_groupSpec dhCommitStep12Evs_fine_groupSpec
   fine_rustAlloc_le_28 fine_rustAlloc_le_44 growOne104Env_groupSpec s7CoreEvs_fine_groupSpec
   w2AesDecErrEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CmkLoopAdvanceCredit
  (cmkLoop25000Live cmkLoop25000MaxReq cmkLoop25000Peak cmkLoop25000TightCum cmkLoop25000TightGrpS
   tryDecryptCmkSeg4Env_fine_groupSpec_tight tryDecryptCmkSeg4Env_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked (tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
  (m2rg_SpqrRecvC07C09aBytesEnvOf' m2rg_StatesRecvEnvFam m2rg_TryDecryptCliLinkedEnvOf'
   m2rg_TryDecryptCliLinkedFailEnvOf' m2rg_W4FailedTdCancelCmkEnvOf'
   m2rg_spqrRecvC07C09aBytesEnvOf'_mono_env)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv DeallocCreditSpec PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (StatesIntoPbTightEnv spqrTightEvs_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (StatesFromPbTightEnv statesFromPb_fine_phaseCreditSpec_tight statesIntoPb_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
  (C07TightGroupSpec StatesRecvTightGroupSpec spqrRecvParts_phaseGroupSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvGhostLink spqrRecvTightDomain_of_topStateTight_and_link)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (C07TightCreditSpec StatesRecvTightCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
  (spqrTightEvs_fine_phaseGroupSpec_align16 statesFromPbTightGroupS_split
   statesFromPbTight_fine_phaseGroupSpec_split statesIntoPbTightGroupS_split
   statesIntoPbTight_fine_phaseGroupSpec_split statesRecvTightGroupS_split)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
  (spqrRecvParts_phaseCreditSpec_tight_uncondHist)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
  (StatesRecvProtoEnv' statesRecvProtoEnv'_tight_creditSpec
   statesRecvProtoEnv'_tight_split_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec (w2CmkChainTightLive)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
  (AesDecCtShape dhCommitStep12Evs phaseCreditSpec_aesDecCt phaseCreditSpec_dhCommitStep12)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs s7CoreEvs)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738 (phaseCreditSpec_boundedFresh_fine_44)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (phaseCredit_seq_freeOnly)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4FailedTdDomCmkOf W4FailedTryDecryptCallCmk W4LoopAdvEnv W4LoopAdvSub W4TryDecryptCallCmk
   W4TryDecryptCallDomCmkOf w4c_DecodeStateTightEnvOf
   w4c_TryDecryptCliEnvOfPure w4c_TryDecryptCliFailEnvOfPure w4c_s8FailEnv
   w4c_tryDecryptCmkSeg4EnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
  (W4AesDecErrEnv phaseCredit_dhCommitStep3_small phaseCredit_exists phaseCredit_fromS2GenEnv
   phaseCredit_w4AesDecErr_cancel)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (GrowOne104Env growOne104Events)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (AesDecCtEnv s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (s9Env s9From6d0Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore
  (DhCommitEnv dhCommitAllocEvents s3CommitDefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget (dhCommitStep12Events)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget
  (DhCommitStep3Env dhCommitStep3Events dhCommitStep3aEvents)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
  (dhStepPairEvents s3DefaultEnv s3EnvOf)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv FromS6GenEnv FromS7GenEnv FromS8GenEnv
   s1InitTrGhost s3AfterTrGhost seqEnv_mono stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux (s7Env vmacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
  (computeMacEvents verifyMacWithAddressesEvents)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
  (TrApplyEnv TrApplySenderAllocEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## `StatesRecv`-Parametric `spqr::recv` & `try_decrypt` Envelopes -/

/-- Parametric `<States>::recv` event-envelope family (`rfl` with `m2rg_StatesRecvEnvFam`). -/
abbrev W4StatesRecvEnv : Type := m2rg_StatesRecvEnvFam

/-- Repaired `<States>::recv` family (`@StatesRecvProtoEnv' F K`). -/
abbrev w4c_repairedStatesRecvEnvFam : W4StatesRecvEnv :=
  fun F K => @StatesRecvProtoEnv' F K

/-- Repaired `StatesRecvProtoEnv'` credit instance (`(1647247, 93776)`, `+0` B aggregate). -/
theorem w4c_repairedStatesRecv_creditSpec (F : ShaCompress) (K : MlKem) :
    StatesRecvTightCreditSpec F (w4c_repairedStatesRecvEnvFam F K) 1647247 93776 :=
  ⟨statesRecvProtoEnv'_tight_creditSpec K⟩

/-- Repaired `StatesRecvProtoEnv'` split-group instance (`statesRecvTightGroupS_split`, `+0` groups). -/
theorem w4c_repairedStatesRecv_split_groupSpec (F : ShaCompress) (K : MlKem) :
    StatesRecvTightGroupSpec F (w4c_repairedStatesRecvEnvFam F K) statesRecvTightGroupS_split :=
  ⟨statesRecvProtoEnv'_tight_split_groupSpec K⟩

/-- `SR`-parametric `∃`-lifted 12-ghost `C07` linked `spqr::recv` byte-slice envelope (`rfl` with
`m2rg_SpqrRecvC07C09aBytesEnvOf' F K maxOps (SR F K)`). -/
abbrev w4c_SpqrRecvC07BytesSrEnvOf (SR : W4StatesRecvEnv)
    (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (stBs msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  m2rg_SpqrRecvC07C09aBytesEnvOf' F K maxOps (SR F K) stBs msgBs evs

/-- `(SR, LoopAdvEnv, maxOps)`-parametric linked Block-`507` `try_decrypt_with_state` CLI envelope
(`rfl` with `m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps C K (SR C.F K)`). -/
abbrev w4c_TryDecryptCliLinkedSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) : TryDecryptEnvArgs → List AllocEvent → Prop :=
  m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps C K (SR C.F K)

/-- `(SR, LoopAdvEnv, maxOps)`-parametric failed-trial linked `try_decrypt_with_state` envelope
(`rfl` with `m2rg_TryDecryptCliLinkedFailEnvOf' LoopAdvEnv maxOps C K (SR C.F K)`). -/
abbrev w4c_TryDecryptCliLinkedFailSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) : TryDecryptEnvArgs → List AllocEvent → Prop :=
  m2rg_TryDecryptCliLinkedFailEnvOf' LoopAdvEnv maxOps C K (SR C.F K)

/-- `SR`-parametric failed-trial `try_decrypt` + drop-cancellation envelope (`Δlive = 0`,
`rfl` with `m2rg_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps C K (SR C.F K)`). -/
abbrev W4FailedTdCancelCmkSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) (fc : W4FailedTryDecryptCallCmk)
    (evs : List AllocEvent) : Prop :=
  m2rg_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps C K (SR C.F K) fc evs

theorem w4c_spqrRecvC07BytesSrEnvOf_mono {SR₁ SR₂ : W4StatesRecvEnv} {F : ShaCompress} {K : MlKem}
    (hSR : ∀ st0 msg evs, SR₁ F K st0 msg evs → SR₂ F K st0 msg evs)
    {m₁ m₂ : Nat} (hm : m₁ ≤ m₂) (stBs msgBs : List (BitVec 8)) {evs : List AllocEvent}
    (h : w4c_SpqrRecvC07BytesSrEnvOf SR₁ F K m₁ stBs msgBs evs) :
    w4c_SpqrRecvC07BytesSrEnvOf SR₂ F K m₂ stBs msgBs evs :=
  m2rg_spqrRecvC07C09aBytesEnvOf'_mono_env hm hSR stBs msgBs h

/-! ## Tight Closed-Formula Constants for `Cmk` `try_decrypt` (`S3..S9`) -/

/-- Tight `S3` (`dh_ratchet_step`: `2 × create_chain` + `dhCommitStep12` + `dhCommitStep3` at `rc ≤ 5`). -/
abbrev w4cTdS3Cum : Nat := 15309
abbrev w4cTdS3MaxReq : Nat := 1040
abbrev w4cTdS3GrpS : Nat := 5 * 16659 + 3 * FineScale

/-- Tight `S4` (`CmkLoopAdvanceEvs` at `maxJumps = 25,000`, `mk ≤ 2,000`). -/
abbrev w4cTdS4Cum : Nat := cmkLoop25000TightCum
abbrev w4cTdS4Live : Nat := cmkLoop25000Live
abbrev w4cTdS4Peak : Nat := cmkLoop25000Peak
abbrev w4cTdS4MaxReq : Nat := cmkLoop25000MaxReq
abbrev w4cTdS4GrpS : Nat := cmkLoop25000TightGrpS

/-- Tight `S5` (`spqr::recv` linked, `uncondHist`, split groups) constants. -/
abbrev w4cTdS5Cum : Nat := 23313687
abbrev w4cTdS5Live : Nat := 605066
abbrev w4cTdS5Peak : Nat := 621350
abbrev w4cTdS5MaxReq : Nat := 302480
abbrev w4cTdS5GrpSOf (maxOps : Nat) : Nat :=
  140011 * maxOps + (statesFromPbTightGroupS_split + statesRecvTightGroupS_split +
    (421107504 + statesIntoPbTightGroupS_split))

/-- Tight `S7` (`verify_mac_with_addresses` + `23`-B error box). -/
abbrev w4cTdS7Cum : Nat := 2952
abbrev w4cTdS7MaxReq : Nat := 36
abbrev w4cTdS7GrpS : Nat := 3 * 16659 + 11056

/-- Tight `S8` (`aes_cbc_decrypt` at `ctLen ≤ maxCt`) & `S9` (`apply_to_session_state` small allocs). -/
abbrev w4cTdS8CumOf (maxCt : Nat) : Nat := 2 * maxCt + 9539
abbrev w4cTdS8LiveOf (maxCt : Nat) : Nat := maxCt + 8195
abbrev w4cTdS8PeakOf (maxCt : Nat) : Nat := maxCt + 8195
abbrev w4cTdS8GrpS : Nat := 3 * FineScale

abbrev w4cTdS9Cum : Nat := 4428
abbrev w4cTdS9MaxReq : Nat := 33
abbrev w4cTdS9GrpS : Nat := 6 * 16659

/-- Total tight `PhaseCreditSpec` bounds for `w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps`. -/
abbrev w4cTdCumOf (maxCt : Nat) : Nat :=
  w4cTdS3Cum + w4cTdS4Cum + w4cTdS5Cum + w4cTdS7Cum + w4cTdS8CumOf maxCt + w4cTdS9Cum

abbrev w4cTdLiveOf (maxCt : Nat) : Nat :=
  w4cTdS4Live + w4cTdS5Live + w4cTdS8LiveOf maxCt

abbrev w4cTdPeakOf (maxCt : Nat) : Nat :=
  max w4cTdS4Peak (w4cTdS4Live + max w4cTdS5Peak (w4cTdS5Live + w4cTdS8PeakOf maxCt))

abbrev w4cTdMaxReqOf (maxCt : Nat) : Nat :=
  max w4cTdS4MaxReq maxCt

abbrev w4cTdGrpSOf (maxOps : Nat) : Nat :=
  w4cTdS3GrpS + w4cTdS4GrpS + w4cTdS5GrpSOf maxOps + w4cTdS7GrpS + w4cTdS8GrpS + w4cTdS9GrpS

/-- Total tight `PhaseCreditSpec` bounds for failed-trial `w4c_TryDecryptCliLinkedFailSrEnvOf`
(`aesOpt = none` → `S9` unreachable, `w4c_s8FailEnv` has `Δlive = 0`). -/
abbrev w4cTdFailCumOf (maxCt : Nat) : Nat :=
  w4cTdS3Cum + w4cTdS4Cum + w4cTdS5Cum + w4cTdS7Cum + w4cTdS8CumOf maxCt

abbrev w4cTdFailLive : Nat :=
  w4cTdS4Live + w4cTdS5Live

abbrev w4cTdFailPeakOf (maxCt : Nat) : Nat :=
  w4cTdPeakOf maxCt

abbrev w4cTdFailGrpSOf (maxOps : Nat) : Nat :=
  w4cTdS3GrpS + w4cTdS4GrpS + w4cTdS5GrpSOf maxOps + w4cTdS7GrpS + w4cTdS8GrpS

/-! ## `SR`-Parametric `spqr::recv` `maxOps` Credit & Split Group Specs -/

private theorem td0_phaseCredit_of_and_right {P : List AllocEvent → Prop} {Q : Prop}
    {c l p r : Nat}
    (h : Q → PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (fun evs => P evs ∧ Q) c l p r where
  req_align evs hpq ev hev := (h hpq.2).req_align evs hpq.1 ev hev
  credit_le st0 {_} hpq := (h hpq.2).credit_le st0 hpq.1

private theorem td0_phaseGroup_exists {α : Type}
    {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, PhaseGroupSpec fineCostModel (E a) g) :
    PhaseGroupSpec fineCostModel (fun evs => ∃ a, E a evs) g where
  groups_le st0 {_} hex := by
    obtain ⟨a, ha⟩ := hex
    exact (h a).groups_le st0 ha

private theorem td0_phaseGroup_of_and_right {P : List AllocEvent → Prop} {Q : Prop} {g : Nat}
    (h : Q → PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (fun evs => P evs ∧ Q) g where
  groups_le st0 {_} hpq := (h hpq.2).groups_le st0 hpq.1

theorem w4c_c07TightCreditSpec_inst (F : ShaCompress) (maxOps : Nat) :
    C07TightCreditSpec F
      (w4c_DecodeStateTightEnvOf maxOps)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      1307216 79236 359623 2560 376193 2400 :=
  ⟨fun _ _ _ _ => spqrTightEvs_fine_phaseCreditSpec maxOps 1307216 (Nat.le_refl 79236),
   fun _ _ _ => statesFromPb_fine_phaseCreditSpec_tight,
   fun _ _ _ _ => statesIntoPb_fine_phaseCreditSpec_tight⟩

theorem w4c_c07TightGroupSpec_split_inst (F : ShaCompress) (maxOps : Nat) :
    C07TightGroupSpec F
      (w4c_DecodeStateTightEnvOf maxOps)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      (140011 * maxOps)
      statesFromPbTightGroupS_split
      statesIntoPbTightGroupS_split :=
  ⟨fun _ _ _ _ => spqrTightEvs_fine_phaseGroupSpec_align16 maxOps 1307216 79236,
   fun _ _ _ => statesFromPbTight_fine_phaseGroupSpec_split,
   fun _ _ _ _ => statesIntoPbTight_fine_phaseGroupSpec_split⟩

theorem w4c_spqrRecvC07BytesSrEnvOf_phaseCreditSpec
    {SR : W4StatesRecvEnv} {F : ShaCompress} {K : MlKem} (maxOps : Nat)
    (hSr : StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    {stBs msgBs : Bytes} (hTop : TopStateTight F K stBs) :
    PhaseCreditSpec fineCostModel (w4c_SpqrRecvC07BytesSrEnvOf SR F K maxOps stBs msgBs)
      w4cTdS5Cum w4cTdS5Live w4cTdS5Peak w4cTdS5MaxReq := by
  let _ := msgBs
  refine
    phaseCredit_exists fun pre_pb =>
    phaseCredit_exists fun vn =>
    phaseCredit_exists fun pb =>
    phaseCredit_exists fun st0 =>
    phaseCredit_exists fun sckaMsg =>
    phaseCredit_exists fun v =>
    phaseCredit_exists fun xInit =>
    phaseCredit_exists fun xNew =>
    phaseCredit_exists fun xAdd =>
    phaseCredit_exists fun xRk =>
    phaseCredit_exists fun xSInto =>
    phaseCredit_exists fun xCInto => ?_
  refine td0_phaseCredit_of_and_right fun hLink => ?_
  exact (spqrRecvParts_phaseCreditSpec_tight_uncondHist
    F K (w4c_c07TightCreditSpec_inst F maxOps) hSr
    (by decide) stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
    (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem w4c_spqrRecvC07BytesSrEnvOf_phaseGroupSpec_split
    {SR : W4StatesRecvEnv} {F : ShaCompress} {K : MlKem} (maxOps : Nat)
    (hSr : StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    {stBs msgBs : Bytes} (hTop : TopStateTight F K stBs) :
    PhaseGroupSpec fineCostModel (w4c_SpqrRecvC07BytesSrEnvOf SR F K maxOps stBs msgBs)
      (w4cTdS5GrpSOf maxOps) := by
  let _ := msgBs
  refine
    td0_phaseGroup_exists fun pre_pb =>
    td0_phaseGroup_exists fun vn =>
    td0_phaseGroup_exists fun pb =>
    td0_phaseGroup_exists fun st0 =>
    td0_phaseGroup_exists fun sckaMsg =>
    td0_phaseGroup_exists fun v =>
    td0_phaseGroup_exists fun xInit =>
    td0_phaseGroup_exists fun xNew =>
    td0_phaseGroup_exists fun xAdd =>
    td0_phaseGroup_exists fun xRk =>
    td0_phaseGroup_exists fun xSInto =>
    td0_phaseGroup_exists fun xCInto => ?_
  refine td0_phaseGroup_of_and_right fun hLink => ?_
  exact spqrRecvParts_phaseGroupSpec_tight F K
    (w4c_c07TightGroupSpec_split_inst F maxOps) hSr
    stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
    (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)

/-! ## Leaf Segment Specs (`S3`, `S5`, `S7`, `S8`, `S9`) & `FromS2GenEnv` Group Composition -/

private theorem td0_rustAlloc_le_44_credit {sz : Nat} (hsz : sz ≤ 44) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents sz 1) 738 0 0 sz := by
  have hb : PhaseCreditSpec fineCostModel (BoundedFreshEvs 1 1 sz) 738 0 0 sz := by
    simpa using phaseCreditSpec_boundedFresh_fine_44 (k := 1) (maxLen := 1) hsz
  refine hb.of_imp fun evs heq => ?_
  subst heq
  unfold BoundedFreshEvs
  by_cases h0 : sz = 0
  · subst h0
    simp [rustAllocEvents, LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
      eventStepReq, eventStepAlign]
  · have h1 : 1 ≤ sz := Nat.one_le_iff_ne_zero.mpr h0
    simp [rustAllocEvents, h1, LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
      eventStepReq, eventStepAlign]

private theorem td0_dhStepPairEvents_credit (C : Crypto) (their : PublicKey)
    (our : CryptoGames.LibsignalSession.PrivateKey) :
    PhaseCreditSpec fineCostModel (· = dhStepPairEvents C their our) 738 0 0 32 := by
  have hb : PhaseCreditSpec fineCostModel (BoundedFreshEvs 1 2 32) 738 0 0 32 := by
    simpa using phaseCreditSpec_boundedFresh_fine_44 (k := 1) (maxLen := 2) (maxReq := 32) (by decide)
  refine hb.of_imp fun evs heq => ?_
  subst heq
  unfold dhStepPairEvents
  cases CryptoVerification.LibsignalTripleRatchet.calculateAgreement C.X their our with
  | none =>
    simp [BoundedFreshEvs, LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount]
  | some _ =>
    simp [BoundedFreshEvs, rustAllocEvents, rustDeallocEvents,
      LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
      eventStepReq, eventStepAlign]

private theorem td0_dhStepPairEvents_group (C : Crypto) (their : PublicKey)
    (our : CryptoGames.LibsignalSession.PrivateKey) :
    PhaseGroupSpec fineCostModel (· = dhStepPairEvents C their our) 16659 := by
  unfold dhStepPairEvents
  cases CryptoVerification.LibsignalTripleRatchet.calculateAgreement C.X their our with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | some _ =>
    have ha := fine_rustAlloc_le_44 (sz := 32) (al := 1) (by decide) (by decide)
    have hd := PhaseGroupSpec.rustDealloc fineCostModel 32 1
    exact ((ha.concat hd).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono (by omega)

private theorem td0_dhCommitStep12Events_eq : dhCommitStep12Events = dhCommitStep12Evs :=
  rfl

private theorem td0_s3Commit_credit (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (hrc : tr.ratchet.receiverChains.length ≤ 5) :
    PhaseCreditSpec fineCostModel (s3CommitDefaultEnv x trG tr) 13833 0 0 1040 := by
  unfold s3CommitDefaultEnv DhCommitEnv dhCommitAllocEvents
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hc33 := smallAllocCost_le_738_of_le_44 (req := 33) (by decide)
  have hc32 := smallAllocCost_le_738_of_le_44 (req := 32) (by decide)
  have h12 : PhaseCreditSpec fineCostModel (· = dhCommitStep12Events) 2214 0 0 33 := by
    rw [td0_dhCommitStep12Events_eq]
    exact (phaseCreditSpec_dhCommitStep12 fineCostModel h33).mono
      (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)
  let rcBv := BitVec.ofNat 64 tr.ratchet.receiverChains.length
  have h3 : PhaseCreditSpec fineCostModel (DhCommitStep3Env trG.ratchet.chainsCap rcBv)
      11619 0 0 1040 := by
    by_cases heq : rcBv = trG.ratchet.chainsCap
    · have hcap5 : trG.ratchet.chainsCap.toNat ≤ 5 := by
        rw [← heq, BitVec.toNat_ofNat]
        exact Nat.le_trans (Nat.mod_le _ _) hrc
      have hsm : max (2 * 5) 4 * 104 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; decide
      exact (phaseCredit_dhCommitStep3_small fineCostModel_modelHyps hcap5 hsm).mono
        (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    · have hd33 := PhaseCreditSpec.rustDealloc_align16 fineCostModel (req := 33) (al := 1) (by decide)
      have himp : ∀ evs, DhCommitStep3Env trG.ratchet.chainsCap rcBv evs →
          evs = rustDeallocEvents 33 1 := by
        rintro _ rfl
        simp [dhCommitStep3Events, dhCommitStep3aEvents, heq]
      exact (hd33.of_imp himp).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  have h123 : PhaseCreditSpec fineCostModel
      (· = dhCommitStep12Events ++ dhCommitStep3Events trG.ratchet.chainsCap rcBv)
      13833 0 0 1040 :=
    ((h12.concat h3).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  exact (h123.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by omega) (by omega) (by omega) (by decide)

private theorem td0_s3Commit_group (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    PhaseGroupSpec fineCostModel (s3CommitDefaultEnv x trG tr) (3 * 16659 + 3 * FineScale) := by
  unfold s3CommitDefaultEnv DhCommitEnv dhCommitAllocEvents
  have h12 : PhaseGroupSpec fineCostModel (· = dhCommitStep12Events) (3 * 16659) := by
    rw [td0_dhCommitStep12Events_eq]; exact dhCommitStep12Evs_fine_groupSpec
  let rcBv := BitVec.ofNat 64 tr.ratchet.receiverChains.length
  have h3a : PhaseGroupSpec fineCostModel
      (· = dhCommitStep3aEvents trG.ratchet.chainsCap rcBv) (3 * FineScale) := by
    unfold dhCommitStep3aEvents
    split
    · exact growOne104Env_groupSpec fineCostModel trG.ratchet.chainsCap
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  have h3 : PhaseGroupSpec fineCostModel (· = dhCommitStep3Events trG.ratchet.chainsCap rcBv)
      (3 * FineScale) := by
    unfold dhCommitStep3Events
    exact ((h3a.concat (PhaseGroupSpec.rustDealloc fineCostModel 33 1)).of_imp
      fun _ h => ⟨_, _, h, rfl, rfl⟩).mono (Nat.le_of_eq (Nat.add_zero _))
  have h123 := (h12.concat h3).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩
  exact (h123.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

private theorem td0_s3DefaultEnv_credit (C : Crypto) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (hrc : tr.ratchet.receiverChains.length ≤ 5) :
    PhaseCreditSpec fineCostModel (s3DefaultEnv C x trG tr) w4cTdS3Cum 0 0 w4cTdS3MaxReq := by
  unfold s3DefaultEnv s3EnvOf
  cases tr.ratchet.senderChain with
  | none =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some sc =>
    dsimp only
    have hp1 := td0_dhStepPairEvents_credit C x.msg.senderRatchetKey sc.ratchetKey.privateKey
    cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error _ =>
      exact hp1.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    | ok p1 =>
      rcases p1 with ⟨rk1, _⟩
      dsimp only
      have hp2 := td0_dhStepPairEvents_credit C x.msg.senderRatchetKey
        (CryptoGames.LibsignalSession.KeyPair.generate C (coinsOf x.rest)).privateKey
      cases rootCreateChain C rk1 x.msg.senderRatchetKey
          (CryptoGames.LibsignalSession.KeyPair.generate C (coinsOf x.rest)).privateKey with
      | error _ =>
        exact (hp1.seq hp2).mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
      | ok _ =>
        exact (hp1.seq (hp2.seq (td0_s3Commit_credit x trG tr hrc))).mono
          (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem td0_s3DefaultEnv_group (C : Crypto) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    PhaseGroupSpec fineCostModel (s3DefaultEnv C x trG tr) w4cTdS3GrpS := by
  unfold s3DefaultEnv s3EnvOf
  cases tr.ratchet.senderChain with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | some sc =>
    dsimp only
    have hp1 := td0_dhStepPairEvents_group C x.msg.senderRatchetKey sc.ratchetKey.privateKey
    cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error _ => exact hp1.mono (by decide)
    | ok p1 =>
      rcases p1 with ⟨rk1, _⟩
      dsimp only
      have hp2 := td0_dhStepPairEvents_group C x.msg.senderRatchetKey
        (CryptoGames.LibsignalSession.KeyPair.generate C (coinsOf x.rest)).privateKey
      cases rootCreateChain C rk1 x.msg.senderRatchetKey
          (CryptoGames.LibsignalSession.KeyPair.generate C (coinsOf x.rest)).privateKey with
      | error _ => exact (hp1.seq hp2).mono (by decide)
      | ok _ =>
        exact (hp1.seq (hp2.seq (td0_s3Commit_group x trG tr))).mono (by decide)

private theorem td0_pqRecvEnv_credit {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {c l p r : Nat} {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    (hlp : l ≤ p)
    (hR : PhaseCreditSpec fineCostModel (RecvEnv tr.pqrState x.msg.pqRatchet) c l p r) :
    PhaseCreditSpec fineCostModel (PqRecvEnv S RecvEnv FormatInnerEnv x tr) c l p r := by
  unfold PqRecvEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | ok _ => exact hR
  | error _ =>
    have hf : PhaseCreditSpec fineCostModel FormatInnerEnv 0 0 0 0 :=
      PhaseCreditSpec.nil fineCostModel
    have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
    exact ((hR.seq hf).seq hfr).mono
      (by omega) (by omega)
      (by have := Nat.max_eq_left hlp; omega)
      (by omega)

private theorem td0_pqRecvEnv_group {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {g : Nat} {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    (hR : PhaseGroupSpec fineCostModel (RecvEnv tr.pqrState x.msg.pqRatchet) g) :
    PhaseGroupSpec fineCostModel (PqRecvEnv S RecvEnv FormatInnerEnv x tr) g := by
  unfold PqRecvEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | ok _ => exact hR
  | error _ =>
    have hf : PhaseGroupSpec fineCostModel FormatInnerEnv 0 := PhaseGroupSpec.nil fineCostModel
    have hfr := PhaseGroupSpec.freeOnly fineCostModel
    exact ((hR.seq hf).seq hfr).mono (by omega)

private theorem td0_s7Env_credit (F : ShaCompress) (x : TryDecryptGhost)
    (tr : TripleRatchet (List (BitVec 8))) (mks : MessageKeys) (pqr : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (s7Env F uuidTryParse x tr mks pqr) w4cTdS7Cum 0 0 w4cTdS7MaxReq := by
  unfold s7Env
  have hvm : PhaseCreditSpec fineCostModel (· = vmacEvents F uuidTryParse x tr mks) 2214 0 0 36 := by
    have hb : PhaseCreditSpec fineCostModel (BoundedFreshEvs 3 6 36) 2214 0 0 36 := by
      simpa using phaseCreditSpec_boundedFresh_fine_44 (k := 3) (maxLen := 6) (maxReq := 36) (by decide)
    refine hb.of_imp fun evs heq => ?_
    subst heq
    unfold vmacEvents verifyMacWithAddressesEvents computeMacEvents
    dsimp only
    split <;>
      simp [BoundedFreshEvs, rustAllocEvents, rustDeallocEvents,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeEvents,
        LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
        eventStepReq, eventStepAlign]
  have h23 := td0_rustAlloc_le_44_credit (sz := 23) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact ((hvm.seq h23).seq hfr).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem td0_s7Env_group (F : ShaCompress) (x : TryDecryptGhost)
    (tr : TripleRatchet (List (BitVec 8))) (mks : MessageKeys) (pqr : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (s7Env F uuidTryParse x tr mks pqr) w4cTdS7GrpS := by
  unfold s7Env
  have hvm : PhaseGroupSpec fineCostModel (· = vmacEvents F uuidTryParse x tr mks) (3 * 16659) := by
    unfold vmacEvents verifyMacWithAddressesEvents computeMacEvents
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeEvents
    dsimp only
    have h33 := fine_rustAlloc_le_44 (sz := 33) (al := 1) (by decide) (by decide)
    have hd33 := PhaseGroupSpec.rustDealloc fineCostModel 33 1
    have h36 := fine_rustAlloc_le_44 (sz := 36) (al := 1) (by decide) (by decide)
    have hd36 := PhaseGroupSpec.rustDealloc fineCostModel 36 1
    have ht33 : PhaseGroupSpec fineCostModel
        (· = rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) 16659 :=
      ((h33.concat hd33).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
        (by decide : 16659 + 0 ≤ 16659)
    have hcm : PhaseGroupSpec fineCostModel
        (· = rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++
          (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)) (2 * 16659) :=
      ((ht33.concat ht33).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
        (by decide : 16659 + 16659 ≤ 2 * 16659)
    split
    · have ht36 : PhaseGroupSpec fineCostModel
          (· = rustAllocEvents 36 1 ++ rustDeallocEvents 36 1) 16659 :=
        ((h36.concat hd36).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
          (by decide : 16659 + 0 ≤ 16659)
      exact ((hcm.concat ht36).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
        (by decide : 2 * 16659 + 16659 ≤ 3 * 16659)
    · exact hcm.mono (by decide : 2 * 16659 ≤ 3 * 16659)
  have h23 := fine_rustAlloc_le_28 (sz := 23) (al := 1) (by decide) (by decide)
  have hfr := PhaseGroupSpec.freeOnly fineCostModel
  exact ((hvm.seq h23).seq hfr).mono (by unfold w4cTdS7GrpS; omega)

private theorem td0_s8Env_credit {maxCt : Nat} (x : TryDecryptGhost)
    (mks : MessageKeys) (pqr : List (BitVec 8))
    (hct : x.msg.ciphertext.length ≤ maxCt) :
    PhaseCreditSpec fineCostModel (s8Env x mks pqr)
      (w4cTdS8CumOf maxCt) (w4cTdS8LiveOf maxCt) (w4cTdS8PeakOf maxCt) maxCt := by
  unfold s8Env
  have haes : PhaseCreditSpec fineCostModel (AesDecCtEnv x.msg.ciphertext.length)
      (2 * maxCt + 9539) (maxCt + 8195) (maxCt + 8195) maxCt := by
    refine (phaseCreditSpec_aesDecCt fineCostModel_modelHyps hct).of_imp fun evs h => ?_
    unfold AesDecCtEnv at h
    unfold AesDecCtShape
    split at h
    · exact Or.inl h
    · exact Or.inr h
  exact (haes.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by unfold w4cTdS8CumOf; omega) (by unfold w4cTdS8LiveOf; omega)
    (by unfold w4cTdS8PeakOf; omega) (by omega)

private theorem td0_s8Env_group (x : TryDecryptGhost)
    (mks : MessageKeys) (pqr : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (s8Env x mks pqr) w4cTdS8GrpS := by
  unfold s8Env
  have haes : PhaseGroupSpec fineCostModel (AesDecCtEnv x.msg.ciphertext.length) (3 * FineScale) := by
    refine (aesDecCtShape_groupSpec fineCostModel x.msg.ciphertext.length).of_imp fun evs h => ?_
    unfold AesDecCtEnv at h
    unfold AesDecCtShape
    split at h
    · exact Or.inl h
    · exact Or.inr h
  exact (haes.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by unfold w4cTdS8GrpS; omega)

private theorem td0_s8FailEnv_credit {maxCt : Nat} (x : TryDecryptGhost)
    (mks : MessageKeys) (pqr : List (BitVec 8))
    (hct : x.msg.ciphertext.length ≤ maxCt) :
    PhaseCreditSpec fineCostModel (w4c_s8FailEnv x mks pqr)
      (w4cTdS8CumOf maxCt) 0 (w4cTdS8PeakOf maxCt) maxCt := by
  unfold w4c_s8FailEnv
  have haes : PhaseCreditSpec fineCostModel (W4AesDecErrEnv x.msg.ciphertext.length)
      (2 * maxCt + 9539) 0 (maxCt + 8195) maxCt :=
    (phaseCredit_w4AesDecErr_cancel fineCostModel_modelHyps x.msg.ciphertext.length).mono
      (by omega) (Nat.le_refl 0) (by omega) hct
  exact (haes.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by unfold w4cTdS8CumOf; omega) (by omega) (by unfold w4cTdS8PeakOf; omega) (by omega)

private theorem td0_s8FailEnv_group (x : TryDecryptGhost)
    (mks : MessageKeys) (pqr : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (w4c_s8FailEnv x mks pqr) w4cTdS8GrpS := by
  unfold w4c_s8FailEnv
  have haes : PhaseGroupSpec fineCostModel (W4AesDecErrEnv x.msg.ciphertext.length) (3 * FineScale) := by
    have hnil := (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le (3 * FineScale))
    have hex : PhaseGroupSpec fineCostModel
        (fun evs => ∃ ctLen : Nat, ctLen ≤ x.msg.ciphertext.length ∧
          evs = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1) (3 * FineScale) := by
      refine td0_phaseGroup_exists fun ctLen => ?_
      refine { groups_le := fun st0 {_} ⟨_, heq⟩ => ?_ }
      exact (w2AesDecErrEnv_groupSpec fineCostModel ctLen).groups_le st0 (Or.inr heq)
    exact (hnil.or hex).mono (Nat.le_of_eq (Nat.max_self _))
  exact (haes.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by unfold w4cTdS8GrpS; omega)

private theorem td0_s9Env_credit (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (pqr : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (s9Env x trG tr st1 pqr) w4cTdS9Cum 0 0 w4cTdS9MaxReq := by
  unfold s9Env s9From6d0Env TrApplyEnv TrApplySenderAllocEnv
  have h32 := td0_rustAlloc_le_44_credit (sz := 32) (by decide)
  have h33 := td0_rustAlloc_le_44_credit (sz := 33) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hnil := PhaseCreditSpec.nil fineCostModel
  have hsa := h33.seq (h33.seq (h32.seq (h32.seq h32)))
  have hopt := hnil.or hsa
  have htr := h32.seq (hfr.seq (hopt.seq hfr))
  exact (hfr.seq (htr.seq hfr)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem td0_s9Env_group (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (pqr : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (s9Env x trG tr st1 pqr) w4cTdS9GrpS := by
  unfold s9Env s9From6d0Env TrApplyEnv TrApplySenderAllocEnv
  have h32 := fine_rustAlloc_le_44 (sz := 32) (al := 1) (by decide) (by decide)
  have h33 := fine_rustAlloc_le_44 (sz := 33) (al := 1) (by decide) (by decide)
  have hfr := PhaseGroupSpec.freeOnly fineCostModel
  have hnil := PhaseGroupSpec.nil fineCostModel
  have hsa := h33.seq (h33.seq (h32.seq (h32.seq h32)))
  have hopt := hnil.or hsa
  have htr := h32.seq (hfr.seq (hopt.seq hfr))
  exact (hfr.seq (htr.seq hfr)).mono (by decide)

section GroupSeamComposition

variable {C : Crypto} {parse : UuidParser} {S : SpqrModel}
  {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
  {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
  {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
    List AllocEvent → Prop}
  {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
  {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
  {s7Env' : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
    List (BitVec 8) → List AllocEvent → Prop}
  {s8Env' : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
  {s9Env' : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
    SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}

private theorem td0_phaseGroup_fromS8GenEnv {g8 g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mks : MessageKeys} {newPqr : List (BitVec 8)}
    (hS8 : PhaseGroupSpec fineCostModel (s8Env' x mks newPqr) g8)
    (hS9 : PhaseGroupSpec fineCostModel (s9Env' x trG tr st1 newPqr) g9) :
    PhaseGroupSpec fineCostModel (FromS8GenEnv aesOpt s8Env' s9Env' x trG tr st1 mks newPqr)
      (g8 + g9) := by
  unfold FromS8GenEnv
  cases aesOpt mks x.msg with
  | some _ => exact hS8.seq hS9
  | none => exact (hS8.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

private theorem td0_phaseGroup_fromS7GenEnv {g7 g8 g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mks : MessageKeys} {newPqr : List (BitVec 8)}
    (hS7 : PhaseGroupSpec fineCostModel (s7Env' x tr mks newPqr) g7)
    (hS8 : PhaseGroupSpec fineCostModel (s8Env' x mks newPqr) g8)
    (hS9 : PhaseGroupSpec fineCostModel (s9Env' x trG tr st1 newPqr) g9) :
    PhaseGroupSpec fineCostModel (FromS7GenEnv C parse aesOpt s7Env' s8Env' s9Env' x trG tr st1 mks newPqr)
      (g7 + (g8 + g9)) := by
  unfold FromS7GenEnv
  split
  · exact hS7.seq (td0_phaseGroup_fromS8GenEnv hS8 hS9)
  · exact (hS7.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

private theorem td0_phaseGroup_fromS6GenEnv {g6 g7 g8 g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator}
    {newPqr : List (BitVec 8)} {pqrKey : Salt}
    (hS6 : PhaseGroupSpec fineCostModel (s6Env mkg) g6)
    (hS7 : ∀ mks, PhaseGroupSpec fineCostModel (s7Env' x tr mks newPqr) g7)
    (hS8 : ∀ mks, PhaseGroupSpec fineCostModel (s8Env' x mks newPqr) g8)
    (hS9 : PhaseGroupSpec fineCostModel (s9Env' x trG tr st1 newPqr) g9) :
    PhaseGroupSpec fineCostModel
      (FromS6GenEnv C parse aesOpt s6Env s7Env' s8Env' s9Env' x trG tr st1 mkg newPqr pqrKey)
      (g6 + (g7 + (g8 + g9))) := by
  unfold FromS6GenEnv
  exact hS6.seq (td0_phaseGroup_fromS7GenEnv (hS7 _) (hS8 _) hS9)

private theorem td0_phaseGroup_fromS5GenEnv {g5 g6 g7 g8 g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator}
    (hS5 : PhaseGroupSpec fineCostModel (s5Env x tr) g5)
    (hS6 : PhaseGroupSpec fineCostModel (s6Env mkg) g6)
    (hS7 : ∀ mks pqr, PhaseGroupSpec fineCostModel (s7Env' x tr mks pqr) g7)
    (hS8 : ∀ mks pqr, PhaseGroupSpec fineCostModel (s8Env' x mks pqr) g8)
    (hS9 : ∀ pqr, PhaseGroupSpec fineCostModel (s9Env' x trG tr st1 pqr) g9) :
    PhaseGroupSpec fineCostModel
      (FromS5GenEnv C parse S aesOpt s5Env s6Env s7Env' s8Env' s9Env' x trG tr st1 mkg)
      (g5 + (g6 + (g7 + (g8 + g9)))) := by
  unfold FromS5GenEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | ok pair =>
    exact hS5.seq (td0_phaseGroup_fromS6GenEnv hS6
      (fun mks => hS7 mks pair.1) (fun mks => hS8 mks pair.1) (hS9 pair.1))
  | error _ =>
    exact (hS5.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

end GroupSeamComposition

/-! ## Pure Ratchet Preservation Across `fromSessionState`, `dhRatchetStep`, & `consumeMessageKey` -/

private theorem td0_fromSessionState_ok {st st1 : SessionState (List (BitVec 8))}
    {tr0 : TripleRatchet (List (BitVec 8))}
    (h : Mut.exec TripleRatchet.fromSessionState st = (.ok tr0, st1)) :
    tr0.pqrState = st.pqRatchetState ∧
    tr0.ratchet.receiverChains = st.receiverChains ∧
    tr0.ratchet.maxForwardJumps = 25000 := by
  rw [fromSessionState_exec] at h
  cases hrem : st.remoteIdentity
  · rw [hrem] at h; cases h
  · rw [hrem] at h
    injection h with hok _
    injection hok with htr
    subst htr
    exact ⟨rfl, rfl, rfl⟩

private theorem td0_dhRatchetStep_ok {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (h : Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1))
    (hjumps : r0.maxForwardJumps ≤ 25000)
    (hmk : ∀ c ∈ r0.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    r1.maxForwardJumps ≤ 25000 ∧
    ∀ c ∈ r1.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
  cases hsc : r0.senderChain with
  | none =>
    rw [dhRatchetStep_none C their coins r0 hsc] at h
    cases h
  | some sc =>
    rw [dhRatchetStep_some_eq C their coins r0 sc hsc] at h
    cases hcc1 : rootCreateChain C r0.rootKey their sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at h
      cases h
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      rw [hcc1] at h
      dsimp only at h
      cases hcc2 : rootCreateChain C rk1 their
          (CryptoGames.LibsignalSession.KeyPair.generate C coins).privateKey with
      | error e =>
        rw [hcc2] at h
        cases h
      | ok p2 =>
        rcases p2 with ⟨rk2, sck⟩
        rw [hcc2] at h
        dsimp only at h
        injection h with _ hr1
        subst hr1
        refine ⟨hjumps, fun c hc => ?_⟩
        unfold RatchetState.evictReceiverChains at hc
        have hmem := List.mem_of_mem_drop hc
        rw [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with h0 | rfl
        · exact hmk c h0
        · exact Nat.zero_le _

/-! ## Full `w4c_TryDecryptCliLinked{,Fail}SrEnvOf` & `W4FailedTdCancelCmkSrEnvOf` Specs -/

/-- State-aware `FromS4GenEnv` credit composition keeping `tr.pqrState` & `tr.ratchet` invariants. -/
private theorem td0_fromS4_credit
    {SR : W4StatesRecvEnv} {C : Crypto} {K : MlKem} {maxOps maxCt : Nat}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s8Env' : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env' : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {l8 c9 : Nat}
    (hSr : StatesRecvTightCreditSpec C.F (SR C.F K) 1647247 93776)
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey}
    (hjumps : tr.ratchet.maxForwardJumps ≤ 25000)
    (hmk : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (hTop : TopStateTight C.F K tr.pqrState)
    (hS8 : ∀ mks pqr, PhaseCreditSpec fineCostModel (s8Env' x mks pqr)
      (w4cTdS8CumOf maxCt) l8 (w4cTdS8PeakOf maxCt) maxCt)
    (hS9 : ∀ trG' tr' pqr, PhaseCreditSpec fineCostModel (s9Env' x trG' tr' st1 pqr)
      c9 0 0 w4cTdS9MaxReq) :
    PhaseCreditSpec fineCostModel
      (FromS4GenEnv C uuidTryParse (spqrV1 C.F K) aesOpt
        (w4c_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
        (PqRecvEnv (spqrV1 C.F K) (w4c_SpqrRecvC07BytesSrEnvOf SR C.F K maxOps) FormatInnerEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env' s9Env' x trG tr st1 ck)
      (w4cTdS4Cum + (w4cTdS5Cum + (0 + (w4cTdS7Cum + (w4cTdS8CumOf maxCt + c9)))))
      (w4cTdS4Live + (w4cTdS5Live + (0 + (0 + (l8 + 0)))))
      (max w4cTdS4Peak (w4cTdS4Live + max w4cTdS5Peak (w4cTdS5Live +
        max 0 (0 + max 0 (0 + max (w4cTdS8PeakOf maxCt) (l8 + 0))))))
      (max w4cTdS4MaxReq (max w4cTdS5MaxReq (max 0 (max w4cTdS7MaxReq (max maxCt w4cTdS9MaxReq))))) := by
  unfold FromS4GenEnv
  have hS4 : PhaseCreditSpec fineCostModel
      (w4c_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv x trG tr ck)
      w4cTdS4Cum w4cTdS4Live w4cTdS4Peak w4cTdS4MaxReq :=
    tryDecryptCmkSeg4Env_fine_phaseCreditSpec_tight x trG tr ck hjumps hmk
  split
  · next mkg r2 _ =>
    have hS5 : PhaseCreditSpec fineCostModel
        (PqRecvEnv (spqrV1 C.F K) (w4c_SpqrRecvC07BytesSrEnvOf SR C.F K maxOps) FormatInnerEnv
          x { tr with ratchet := r2 })
        w4cTdS5Cum w4cTdS5Live w4cTdS5Peak w4cTdS5MaxReq :=
      td0_pqRecvEnv_credit (by decide)
        (w4c_spqrRecvC07BytesSrEnvOf_phaseCreditSpec maxOps hSr hTop)
    have hS6 : PhaseCreditSpec fineCostModel (s6FreeOnlyEnv mkg) 0 0 0 0 :=
      PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
    exact hS4.seq (LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak.phaseCredit_fromS5GenEnv
      fineCostModel_modelHyps hS5 hS6 (td0_s7Env_credit C.F x _) hS8 (hS9 trG _))
  · exact (phaseCredit_seq_freeOnly
      fineCostModel_modelHyps hS4).mono
      (by omega) (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _)

private theorem td0_fromS4_group
    {SR : W4StatesRecvEnv} {C : Crypto} {K : MlKem} {maxOps : Nat}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s8Env' : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env' : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {g9 : Nat}
    (hSr : StatesRecvTightGroupSpec C.F (SR C.F K) statesRecvTightGroupS_split)
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey}
    (hjumps : tr.ratchet.maxForwardJumps ≤ 25000)
    (hmk : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (hTop : TopStateTight C.F K tr.pqrState)
    (hS8 : ∀ mks pqr, PhaseGroupSpec fineCostModel (s8Env' x mks pqr) w4cTdS8GrpS)
    (hS9 : ∀ trG' tr' pqr, PhaseGroupSpec fineCostModel (s9Env' x trG' tr' st1 pqr) g9) :
    PhaseGroupSpec fineCostModel
      (FromS4GenEnv C uuidTryParse (spqrV1 C.F K) aesOpt
        (w4c_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
        (PqRecvEnv (spqrV1 C.F K) (w4c_SpqrRecvC07BytesSrEnvOf SR C.F K maxOps) FormatInnerEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env' s9Env' x trG tr st1 ck)
      (w4cTdS4GrpS + (w4cTdS5GrpSOf maxOps + (0 + (w4cTdS7GrpS + (w4cTdS8GrpS + g9))))) := by
  unfold FromS4GenEnv
  have hS4 : PhaseGroupSpec fineCostModel
      (w4c_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv x trG tr ck) w4cTdS4GrpS :=
    tryDecryptCmkSeg4Env_fine_groupSpec_tight x trG tr ck hjumps hmk
  split
  · next mkg r2 _ =>
    have hS5 : PhaseGroupSpec fineCostModel
        (PqRecvEnv (spqrV1 C.F K) (w4c_SpqrRecvC07BytesSrEnvOf SR C.F K maxOps) FormatInnerEnv
          x { tr with ratchet := r2 })
        (w4cTdS5GrpSOf maxOps) :=
      td0_pqRecvEnv_group (w4c_spqrRecvC07BytesSrEnvOf_phaseGroupSpec_split maxOps hSr hTop)
    have hS6 : PhaseGroupSpec fineCostModel (s6FreeOnlyEnv mkg) 0 :=
      PhaseGroupSpec.freeOnly fineCostModel
    exact hS4.seq (td0_phaseGroup_fromS5GenEnv hS5 hS6 (td0_s7Env_group C.F x _) hS8 (hS9 trG _))
  · exact (hS4.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

private theorem td0_grp_s4_le (s3 s4 s5 s7 s8 s9 : Nat) :
    s4 + (s5 + (0 + (s7 + (s8 + s9)))) ≤ s3 + s4 + s5 + s7 + s8 + s9 := by omega

private theorem td0_grp_s3_le (s3 s4 s5 s7 s8 s9 : Nat) :
    s3 + 0 ≤ s3 + s4 + s5 + s7 + s8 + s9 := by omega

private theorem td0_grp_s34_le (s3 s4 s5 s7 s8 s9 : Nat) :
    s3 + (s4 + (s5 + (0 + (s7 + (s8 + s9))))) ≤ s3 + s4 + s5 + s7 + s8 + s9 := by omega

private theorem td0_fgrp_s4_le (s3 s4 s5 s7 s8 : Nat) :
    s4 + (s5 + (0 + (s7 + (s8 + 0)))) ≤ s3 + s4 + s5 + s7 + s8 := by omega

private theorem td0_fgrp_s3_le (s3 s4 s5 s7 s8 : Nat) :
    s3 + 0 ≤ s3 + s4 + s5 + s7 + s8 := by omega

private theorem td0_fgrp_s34_le (s3 s4 s5 s7 s8 : Nat) :
    s3 + (s4 + (s5 + (0 + (s7 + (s8 + 0))))) ≤ s3 + s4 + s5 + s7 + s8 := by omega

private theorem td0_seq_fr_left_credit {E : List AllocEvent → Prop} {c l p r : Nat}
    (hfr : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0)
    (h : PhaseCreditSpec fineCostModel E c l p r) :
    PhaseCreditSpec fineCostModel (SeqEnv FreeOnlyEvs E) c l p r :=
  (hfr.seq h).mono
    (Nat.le_of_eq (Nat.zero_add c))
    (Nat.le_of_eq (Nat.zero_add l))
    (by omega)
    (Nat.le_of_eq (Nat.zero_max r))

private theorem td0_seq_zero_lp_credit {E1 E2 : List AllocEvent → Prop}
    {c1 m1 c2 l2 p2 m2 c l p m : Nat}
    (h1 : PhaseCreditSpec fineCostModel E1 c1 0 0 m1)
    (h2 : PhaseCreditSpec fineCostModel E2 c2 l2 p2 m2)
    (hc : c1 + c2 ≤ c) (hl : l2 ≤ l) (hp : p2 ≤ p) (hm : max m1 m2 ≤ m) :
    PhaseCreditSpec fineCostModel (SeqEnv E1 E2) c l p m :=
  (h1.seq h2).mono hc (by omega) (by omega) hm

theorem w4c_tryDecryptCliLinkedSrEnvOf_cmk_phaseCreditSpec
    {SR : W4StatesRecvEnv} {C : Crypto} {K : MlKem} {maxOps maxCt : Nat}
    (hSr : StatesRecvTightCreditSpec C.F (SR C.F K) 1647247 93776)
    {td : W4TryDecryptCallCmk}
    (hDom : W4TryDecryptCallDomCmkOf C.F K maxCt td) :
    PhaseCreditSpec fineCostModel
      (w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps C K td.a)
      (w4cTdCumOf maxCt) (w4cTdLiveOf maxCt) (w4cTdPeakOf maxCt) (w4cTdMaxReqOf maxCt) := by
  unfold w4c_TryDecryptCliLinkedSrEnvOf m2rg_TryDecryptCliLinkedEnvOf' w4c_TryDecryptCliEnvOfPure
  cases hfs : Mut.exec TripleRatchet.fromSessionState td.a.st with
  | mk res st1 =>
    cases res with
    | error _ =>
      exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok tr0 =>
      obtain ⟨hpqr, hrc_eq, hjumps0⟩ := td0_fromSessionState_ok hfs
      have hrc : tr0.ratchet.receiverChains.length ≤ 5 := hrc_eq ▸ hDom.rc_len_le
      have hmk0 : ∀ c ∈ tr0.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
        rw [hrc_eq]; exact hDom.mk_len_le
      have hj0 : tr0.ratchet.maxForwardJumps ≤ 25000 := Nat.le_of_eq hjumps0
      have hTop0 : TopStateTight C.F K tr0.pqrState := hpqr ▸ hDom.top_tight
      let x := tryDecryptEnvArgsToGhost td.a
      have hct : x.msg.ciphertext.length ≤ maxCt := hDom.ct_le
      have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      have hS2 : PhaseCreditSpec fineCostModel
          (FromS2GenEnv C uuidTryParse (spqrV1 C.F K) (stdAesOpt C)
            (s3DefaultEnv C) (w4c_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
            (PqRecvEnv (spqrV1 C.F K) (w4c_SpqrRecvC07BytesSrEnvOf SR C.F K maxOps) FormatInnerEnv)
            s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
            x (s1InitTrGhost td.a.G) tr0 st1)
          (w4cTdCumOf maxCt) (w4cTdLiveOf maxCt) (w4cTdPeakOf maxCt) (w4cTdMaxReqOf maxCt) := by
        unfold FromS2GenEnv
        split
        · next ck _ =>
          exact (td0_fromS4_credit (maxOps := maxOps) (aesOpt := stdAesOpt C) hSr hj0 hmk0 hTop0
            (fun mks pqr => td0_s8Env_credit x mks pqr hct)
            (fun trG' tr' pqr => td0_s9Env_credit x trG' tr' st1 pqr)).mono
            (by unfold w4cTdCumOf w4cTdS3Cum w4cTdS4Cum w4cTdS5Cum w4cTdS7Cum w4cTdS8CumOf
                  w4cTdS9Cum cmkLoop25000TightCum; omega)
            (by unfold w4cTdLiveOf w4cTdS8LiveOf; omega)
            (by unfold w4cTdPeakOf w4cTdS4Live w4cTdS4Peak w4cTdS5Live w4cTdS5Peak
                  w4cTdS8LiveOf w4cTdS8PeakOf cmkLoop25000Live cmkLoop25000Peak; omega)
            (by unfold w4cTdMaxReqOf w4cTdS4MaxReq w4cTdS5MaxReq w4cTdS7MaxReq w4cTdS9MaxReq
                  cmkLoop25000MaxReq; omega)
        · unfold FromS3GenEnv
          have hS3 := td0_s3DefaultEnv_credit C x (s1InitTrGhost td.a.G) tr0 hrc
          cases hs3 : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk rres r1 =>
            cases rres with
            | error _ =>
              exact (phaseCredit_seq_freeOnly
                fineCostModel_modelHyps hS3).mono
                (by unfold w4cTdCumOf; omega) (Nat.zero_le _) (Nat.zero_le _)
                (by unfold w4cTdMaxReqOf w4cTdS3MaxReq w4cTdS4MaxReq cmkLoop25000MaxReq; omega)
            | ok ck =>
              obtain ⟨hj1, hmk1⟩ := td0_dhRatchetStep_ok hs3 hj0 hmk0
              have h4 := td0_fromS4_credit (maxOps := maxOps) (aesOpt := stdAesOpt C)
                (trG := s3AfterTrGhost
                  (s1InitTrGhost td.a.G) tr0.ratchet.receiverChains.length)
                (tr := { tr0 with ratchet := r1 }) (ck := ck)
                hSr hj1 hmk1 hTop0
                (fun mks pqr => td0_s8Env_credit x mks pqr hct)
                (fun trG' tr' pqr => td0_s9Env_credit x trG' tr' st1 pqr)
              exact td0_seq_zero_lp_credit hS3 h4
                (by unfold w4cTdCumOf; omega)
                (by unfold w4cTdLiveOf w4cTdS8LiveOf; omega)
                (by unfold w4cTdPeakOf w4cTdS4Live w4cTdS4Peak w4cTdS5Live w4cTdS5Peak
                      w4cTdS8LiveOf w4cTdS8PeakOf cmkLoop25000Live cmkLoop25000Peak; omega)
                (by unfold w4cTdMaxReqOf w4cTdS3MaxReq w4cTdS4MaxReq w4cTdS5MaxReq w4cTdS7MaxReq
                      w4cTdS9MaxReq cmkLoop25000MaxReq; omega)
        · exact hfr.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      exact td0_seq_fr_left_credit hfr hS2

theorem w4c_tryDecryptCliLinkedSrEnvOf_cmk_phaseGroupSpec
    {SR : W4StatesRecvEnv} {C : Crypto} {K : MlKem} {maxOps maxCt : Nat}
    (hSr : StatesRecvTightGroupSpec C.F (SR C.F K) statesRecvTightGroupS_split)
    {td : W4TryDecryptCallCmk}
    (hDom : W4TryDecryptCallDomCmkOf C.F K maxCt td) :
    PhaseGroupSpec fineCostModel
      (w4c_TryDecryptCliLinkedSrEnvOf SR CmkLoopAdvanceEvs maxOps C K td.a)
      (w4cTdGrpSOf maxOps) := by
  unfold w4c_TryDecryptCliLinkedSrEnvOf m2rg_TryDecryptCliLinkedEnvOf' w4c_TryDecryptCliEnvOfPure
  cases hfs : Mut.exec TripleRatchet.fromSessionState td.a.st with
  | mk res st1 =>
    cases res with
    | error _ => exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | ok tr0 =>
      obtain ⟨hpqr, hrc_eq, hjumps0⟩ := td0_fromSessionState_ok hfs
      have hmk0 : ∀ c ∈ tr0.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
        rw [hrc_eq]; exact hDom.mk_len_le
      have hj0 : tr0.ratchet.maxForwardJumps ≤ 25000 := Nat.le_of_eq hjumps0
      have hTop0 : TopStateTight C.F K tr0.pqrState := hpqr ▸ hDom.top_tight
      let x := tryDecryptEnvArgsToGhost td.a
      have hfr := PhaseGroupSpec.freeOnly fineCostModel
      have hS2 : PhaseGroupSpec fineCostModel
          (FromS2GenEnv C uuidTryParse (spqrV1 C.F K) (stdAesOpt C)
            (s3DefaultEnv C) (w4c_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
            (PqRecvEnv (spqrV1 C.F K) (w4c_SpqrRecvC07BytesSrEnvOf SR C.F K maxOps) FormatInnerEnv)
            s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
            x (s1InitTrGhost td.a.G) tr0 st1)
          (w4cTdGrpSOf maxOps) := by
        unfold FromS2GenEnv
        split
        · next ck _ =>
          exact (td0_fromS4_group (maxOps := maxOps) (aesOpt := stdAesOpt C) hSr hj0 hmk0 hTop0
            (fun mks pqr => td0_s8Env_group x mks pqr)
            (fun trG' tr' pqr => td0_s9Env_group x trG' tr' st1 pqr)).mono
            (td0_grp_s4_le _ _ _ _ _ _)
        · unfold FromS3GenEnv
          have hS3 := td0_s3DefaultEnv_group C x (s1InitTrGhost td.a.G) tr0
          cases hs3 : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk rres r1 =>
            cases rres with
            | error _ =>
              exact (hS3.seq hfr).mono (td0_grp_s3_le _ _ _ _ _ _)
            | ok ck =>
              obtain ⟨hj1, hmk1⟩ := td0_dhRatchetStep_ok hs3 hj0 hmk0
              have h4 := td0_fromS4_group (maxOps := maxOps) (aesOpt := stdAesOpt C)
                (trG := s3AfterTrGhost
                  (s1InitTrGhost td.a.G) tr0.ratchet.receiverChains.length)
                (tr := { tr0 with ratchet := r1 }) (ck := ck)
                hSr hj1 hmk1 hTop0
                (fun mks pqr => td0_s8Env_group x mks pqr)
                (fun trG' tr' pqr => td0_s9Env_group x trG' tr' st1 pqr)
              exact (hS3.seq h4).mono (td0_grp_s34_le _ _ _ _ _ _)
        · exact hfr.mono (Nat.zero_le _)
      exact (hfr.seq hS2).mono (Nat.le_of_eq (Nat.zero_add _))

theorem w4c_tryDecryptCliLinkedFailSrEnvOf_cmk_phaseCreditSpec
    {SR : W4StatesRecvEnv} {C : Crypto} {K : MlKem} {maxOps maxCt : Nat}
    (hSr : StatesRecvTightCreditSpec C.F (SR C.F K) 1647247 93776)
    {td : W4TryDecryptCallCmk}
    (hDom : W4TryDecryptCallDomCmkOf C.F K maxCt td) :
    PhaseCreditSpec fineCostModel
      (w4c_TryDecryptCliLinkedFailSrEnvOf SR CmkLoopAdvanceEvs maxOps C K td.a)
      (w4cTdFailCumOf maxCt) w4cTdFailLive (w4cTdFailPeakOf maxCt) (w4cTdMaxReqOf maxCt) := by
  unfold w4c_TryDecryptCliLinkedFailSrEnvOf m2rg_TryDecryptCliLinkedFailEnvOf'
    w4c_TryDecryptCliFailEnvOfPure
  cases hfs : Mut.exec TripleRatchet.fromSessionState td.a.st with
  | mk res st1 =>
    cases res with
    | error _ =>
      exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok tr0 =>
      obtain ⟨hpqr, hrc_eq, hjumps0⟩ := td0_fromSessionState_ok hfs
      have hrc : tr0.ratchet.receiverChains.length ≤ 5 := hrc_eq ▸ hDom.rc_len_le
      have hmk0 : ∀ c ∈ tr0.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
        rw [hrc_eq]; exact hDom.mk_len_le
      have hj0 : tr0.ratchet.maxForwardJumps ≤ 25000 := Nat.le_of_eq hjumps0
      have hTop0 : TopStateTight C.F K tr0.pqrState := hpqr ▸ hDom.top_tight
      let x := tryDecryptEnvArgsToGhost td.a
      have hct : x.msg.ciphertext.length ≤ maxCt := hDom.ct_le
      have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      let s9Nil : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
          SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop :=
        fun _ _ _ _ _ => (· = [])
      have hs9Nil : ∀ trG' tr' pqr,
          PhaseCreditSpec fineCostModel (s9Nil x trG' tr' st1 pqr) 0 0 0 w4cTdS9MaxReq :=
        fun _ _ _ => (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
      have hS2 : PhaseCreditSpec fineCostModel
          (FromS2GenEnv C uuidTryParse (spqrV1 C.F K) (fun _ _ => none)
            (s3DefaultEnv C) (w4c_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
            (PqRecvEnv (spqrV1 C.F K) (w4c_SpqrRecvC07BytesSrEnvOf SR C.F K maxOps) FormatInnerEnv)
            s6FreeOnlyEnv (s7Env C.F uuidTryParse) w4c_s8FailEnv s9Nil
            x (s1InitTrGhost td.a.G) tr0 st1)
          (w4cTdFailCumOf maxCt) w4cTdFailLive (w4cTdFailPeakOf maxCt) (w4cTdMaxReqOf maxCt) := by
        unfold FromS2GenEnv
        split
        · next ck _ =>
          exact (td0_fromS4_credit (maxOps := maxOps) (aesOpt := fun _ _ => none)
            (l8 := 0) (c9 := 0) hSr hj0 hmk0 hTop0
            (fun mks pqr => td0_s8FailEnv_credit x mks pqr hct) hs9Nil).mono
            (by unfold w4cTdFailCumOf; omega)
            (by unfold w4cTdFailLive; omega)
            (by unfold w4cTdFailPeakOf w4cTdPeakOf w4cTdS4Live w4cTdS4Peak w4cTdS5Live
                  w4cTdS5Peak w4cTdS8PeakOf cmkLoop25000Live cmkLoop25000Peak; omega)
            (by unfold w4cTdMaxReqOf w4cTdS4MaxReq w4cTdS5MaxReq w4cTdS7MaxReq w4cTdS9MaxReq
                  cmkLoop25000MaxReq; omega)
        · unfold FromS3GenEnv
          have hS3 := td0_s3DefaultEnv_credit C x (s1InitTrGhost td.a.G) tr0 hrc
          cases hs3 : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk rres r1 =>
            cases rres with
            | error _ =>
              exact (phaseCredit_seq_freeOnly
                fineCostModel_modelHyps hS3).mono
                (by unfold w4cTdFailCumOf; omega) (Nat.zero_le _) (Nat.zero_le _)
                (by unfold w4cTdMaxReqOf w4cTdS3MaxReq w4cTdS4MaxReq cmkLoop25000MaxReq; omega)
            | ok ck =>
              obtain ⟨hj1, hmk1⟩ := td0_dhRatchetStep_ok hs3 hj0 hmk0
              have h4 := td0_fromS4_credit (maxOps := maxOps) (aesOpt := fun _ _ => none)
                (trG := s3AfterTrGhost
                  (s1InitTrGhost td.a.G) tr0.ratchet.receiverChains.length)
                (tr := { tr0 with ratchet := r1 }) (ck := ck) (l8 := 0) (c9 := 0)
                hSr hj1 hmk1 hTop0
                (fun mks pqr => td0_s8FailEnv_credit x mks pqr hct) hs9Nil
              exact td0_seq_zero_lp_credit hS3 h4
                (by unfold w4cTdFailCumOf; omega)
                (by unfold w4cTdFailLive; omega)
                (by unfold w4cTdFailPeakOf w4cTdPeakOf w4cTdS4Live w4cTdS4Peak w4cTdS5Live
                      w4cTdS5Peak w4cTdS8PeakOf cmkLoop25000Live cmkLoop25000Peak; omega)
                (by unfold w4cTdMaxReqOf w4cTdS3MaxReq w4cTdS4MaxReq w4cTdS5MaxReq w4cTdS7MaxReq
                      w4cTdS9MaxReq cmkLoop25000MaxReq; omega)
        · exact hfr.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      exact td0_seq_fr_left_credit hfr hS2

theorem w4c_tryDecryptCliLinkedFailSrEnvOf_cmk_phaseGroupSpec
    {SR : W4StatesRecvEnv} {C : Crypto} {K : MlKem} {maxOps maxCt : Nat}
    (hSr : StatesRecvTightGroupSpec C.F (SR C.F K) statesRecvTightGroupS_split)
    {td : W4TryDecryptCallCmk}
    (hDom : W4TryDecryptCallDomCmkOf C.F K maxCt td) :
    PhaseGroupSpec fineCostModel
      (w4c_TryDecryptCliLinkedFailSrEnvOf SR CmkLoopAdvanceEvs maxOps C K td.a)
      (w4cTdFailGrpSOf maxOps) := by
  unfold w4c_TryDecryptCliLinkedFailSrEnvOf m2rg_TryDecryptCliLinkedFailEnvOf'
    w4c_TryDecryptCliFailEnvOfPure
  cases hfs : Mut.exec TripleRatchet.fromSessionState td.a.st with
  | mk res st1 =>
    cases res with
    | error _ => exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | ok tr0 =>
      obtain ⟨hpqr, hrc_eq, hjumps0⟩ := td0_fromSessionState_ok hfs
      have hmk0 : ∀ c ∈ tr0.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
        rw [hrc_eq]; exact hDom.mk_len_le
      have hj0 : tr0.ratchet.maxForwardJumps ≤ 25000 := Nat.le_of_eq hjumps0
      have hTop0 : TopStateTight C.F K tr0.pqrState := hpqr ▸ hDom.top_tight
      let x := tryDecryptEnvArgsToGhost td.a
      have hfr := PhaseGroupSpec.freeOnly fineCostModel
      let s9Nil : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
          SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop :=
        fun _ _ _ _ _ => (· = [])
      have hs9Nil : ∀ trG' tr' pqr,
          PhaseGroupSpec fineCostModel (s9Nil x trG' tr' st1 pqr) 0 :=
        fun _ _ _ => PhaseGroupSpec.nil fineCostModel
      have hS2 : PhaseGroupSpec fineCostModel
          (FromS2GenEnv C uuidTryParse (spqrV1 C.F K) (fun _ _ => none)
            (s3DefaultEnv C) (w4c_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
            (PqRecvEnv (spqrV1 C.F K) (w4c_SpqrRecvC07BytesSrEnvOf SR C.F K maxOps) FormatInnerEnv)
            s6FreeOnlyEnv (s7Env C.F uuidTryParse) w4c_s8FailEnv s9Nil
            x (s1InitTrGhost td.a.G) tr0 st1)
          (w4cTdFailGrpSOf maxOps) := by
        unfold FromS2GenEnv
        split
        · next ck _ =>
          exact (td0_fromS4_group (maxOps := maxOps) (aesOpt := fun _ _ => none) (g9 := 0)
            hSr hj0 hmk0 hTop0
            (fun mks pqr => td0_s8FailEnv_group x mks pqr) hs9Nil).mono
            (td0_fgrp_s4_le _ _ _ _ _)
        · unfold FromS3GenEnv
          have hS3 := td0_s3DefaultEnv_group C x (s1InitTrGhost td.a.G) tr0
          cases hs3 : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk rres r1 =>
            cases rres with
            | error _ =>
              exact (hS3.seq hfr).mono (td0_fgrp_s3_le _ _ _ _ _)
            | ok ck =>
              obtain ⟨hj1, hmk1⟩ := td0_dhRatchetStep_ok hs3 hj0 hmk0
              have h4 := td0_fromS4_group (maxOps := maxOps) (aesOpt := fun _ _ => none)
                (trG := s3AfterTrGhost
                  (s1InitTrGhost td.a.G) tr0.ratchet.receiverChains.length)
                (tr := { tr0 with ratchet := r1 }) (ck := ck) (g9 := 0)
                hSr hj1 hmk1 hTop0
                (fun mks pqr => td0_s8FailEnv_group x mks pqr) hs9Nil
              exact (hS3.seq h4).mono (td0_fgrp_s34_le _ _ _ _ _)
        · exact hfr.mono (Nat.zero_le _)
      exact (hfr.seq hS2).mono (Nat.le_of_eq (Nat.zero_add _))

private theorem td0_deallocCreditSpec_mono_le {M : AllocCostModel} [HasFineReallocCredit M]
    {E : List AllocEvent → Prop} {d₁ d₂ : Nat}
    (h : DeallocCreditSpec M E d₂) (hd : d₁ ≤ d₂) :
    DeallocCreditSpec M E d₁ where
  req_align := h.req_align
  credit_sub st0 {_} hE := by
    obtain ⟨hc, hl, hp⟩ := h.credit_sub st0 hE
    exact ⟨hc, Nat.le_trans hl (Nat.sub_le_sub_left hd _), hp⟩

private theorem td0_optDeallocListEvs_freeOnly (pairs : List (Nat × Nat)) :
    FreeOnlyEvs (optDeallocListEvs pairs) := by
  induction pairs with
  | nil => exact fun _ h => nomatch h
  | cons p rest ih =>
    rcases p with ⟨req, al⟩
    intro ev hev
    simp only [optDeallocListEvs, List.mem_append] at hev
    rcases hev with he | he
    · split at he
      · nomatch he
      · unfold rustDeallocEvents at he
        rw [List.mem_singleton] at he
        exact ⟨al, req, he⟩
    · exact ih ev he

theorem w4FailedTdCancelCmkSrEnvOf_phaseCreditSpec
    {SR : W4StatesRecvEnv} {C : Crypto} {K : MlKem} {maxOps maxCt : Nat}
    (hSr : StatesRecvTightCreditSpec C.F (SR C.F K) 1647247 93776)
    {fc : W4FailedTryDecryptCallCmk}
    (hDom : W4FailedTdDomCmkOf C.F K maxCt fc) :
    PhaseCreditSpec fineCostModel
      (W4FailedTdCancelCmkSrEnvOf SR CmkLoopAdvanceEvs maxOps C K fc)
      (w4cTdFailCumOf maxCt) 0 (w4cTdFailPeakOf maxCt) (w4cTdMaxReqOf maxCt) := by
  unfold W4FailedTdCancelCmkSrEnvOf m2rg_W4FailedTdCancelCmkEnvOf'
  have hTd0 := w4c_tryDecryptCliLinkedFailSrEnvOf_cmk_phaseCreditSpec (maxOps := maxOps) hSr hDom.td_dom
  have hLiveEq : w4cTdFailLive = 0 + (w2CmkChainTightLive 2000 + 605066) := rfl
  have hTd := hTd0.mono (Nat.le_refl _) (Nat.le_of_eq hLiveEq) (Nat.le_refl _) (Nat.le_refl _)
  have hDrop := td0_deallocCreditSpec_mono_le
    (LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak.DeallocCreditSpec.optDeallocList
      fineCostModel fc.failDropPairs hDom.align_le)
    hDom.cancel_live
  have hCancel := hTd.concat_dealloc_cancel hDrop
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCancel).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem w4FailedTdCancelCmkSrEnvOf_phaseGroupSpec
    {SR : W4StatesRecvEnv} {C : Crypto} {K : MlKem} {maxOps maxCt : Nat}
    (hSr : StatesRecvTightGroupSpec C.F (SR C.F K) statesRecvTightGroupS_split)
    {fc : W4FailedTryDecryptCallCmk}
    (hDom : W4FailedTdDomCmkOf C.F K maxCt fc) :
    PhaseGroupSpec fineCostModel
      (W4FailedTdCancelCmkSrEnvOf SR CmkLoopAdvanceEvs maxOps C K fc)
      (w4cTdFailGrpSOf maxOps) := by
  unfold W4FailedTdCancelCmkSrEnvOf m2rg_W4FailedTdCancelCmkEnvOf'
  have hTd := w4c_tryDecryptCliLinkedFailSrEnvOf_cmk_phaseGroupSpec (maxOps := maxOps) hSr hDom.td_dom
  have hDrop : PhaseGroupSpec fineCostModel (· = optDeallocListEvs fc.failDropPairs) 0 :=
    (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ h => h ▸ td0_optDeallocListEvs_freeOnly _
  have hCat := (hTd.concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hCat).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
