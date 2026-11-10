/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptRecordStorePeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak

/-!
# Peak Live-Heap Interface for W2 `message_decrypt_signal`

Top-level interface for the W2 `message_decrypt_signal` slot: re-exports `W2DecryptPhasePeak`,
`W2DecryptRecordStorePeak`, and `W2DecryptCloneBounds`; defines exact-order `try_decrypt` Segments
`S1`–`S9` envelopes (`W2TryDecryptEnv` and `W2TryDecryptFailEnv`) with `Vec<104>` `realloc`
cancellation and black-box `SpqrStepEnv`; and composes the `Scope`-guarded `WithStoresDecEnv` slot
and `TrialLoopEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec

open CryptoGames.LibsignalSession (Crypto IdentityKey)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (IdentityStoreSpec SessionStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost UuidParser)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (TryDecryptEnvArgs recordTryDecryptEnvArgs)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak (v104GrowStepCum)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (s7CoreEvs)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
  (AesDecCtShape BoundedLenEvs BoundedNonFreeEvs DoublingChainLe TrApplyBoundedEnv TrialLoopEnv
   dhCommitStep12Evs dhCommitStep3Evs doublingChain104Evs
   phaseCreditSpec_aesDecCt phaseCreditSpec_aesDecCt_err phaseCreditSpec_boundedNonFree_aff
   phaseCreditSpec_boundedNonFree_small phaseCreditSpec_cmkJumpList_tower
   phaseCreditSpec_dhCommitStep12 phaseCreditSpec_dhCommitStep3_smallCap
   phaseCreditSpec_doublingChain104 phaseCreditSpec_failedTrial_done phaseCreditSpec_s7Core
   phaseCreditSpec_trApplyBounded phaseCreditSpec_trialLoop)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptRecordStorePeak
  (phaseCreditSpec_loadPollStep_smallBox phaseCreditSpec_recordDecryptEnv
   phaseCreditSpec_saveStep_smallBox phaseCreditSpec_storeStep_smallBox
   phaseCreditSpec_trustStep_smallBox phaseCreditSpec_withStoresDecEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (GhostCloneValid RecordGhostValid SessionCloneDom
   recordDecrypt_dom_phaseCredit recordDecrypt_dom_phaseCredit_tight recordDecrypt_dom_phaseGroup
   serialize_dom_phaseCredit serialize_dom_phaseCredit_tight serialize_dom_phaseGroup
   sessStorePoll_dom_phaseCredit sessStorePoll_dom_phaseCredit_tight sessStorePoll_dom_phaseGroup
   sessionCloneDom_of_scopeIn sessionCloneDom_of_scopeKit sessionCloneDom_of_scopeKit_pq
   sessionClone_dom_phaseCredit sessionClone_dom_phaseCredit_tight sessionClone_dom_phaseGroup
   sessionClone_drop_cancel_dom_phaseCredit sessionClone_drop_cancel_dom_phaseCredit_tight
   sessionClone_drop_cancel_dom_phaseGroup)

/-! ## 1. Re-Exports -/

export W2DecryptPhasePeak (BoundedNonFreeEvs BoundedLenEvs TrApplyBoundedEnv AesDecCtShape)
export W2DecryptPhasePeak (DoublingChainLe doublingChain104Evs TrialLoopEnv)
export W2DecryptPhasePeak (phaseCreditSpec_boundedNonFree_small phaseCreditSpec_boundedNonFree_aff)
export W2DecryptPhasePeak (phaseCreditSpec_trApplyBounded phaseCreditSpec_dhCommitStep12)
export W2DecryptPhasePeak (phaseCreditSpec_dhCommitStep3_smallCap phaseCreditSpec_cmkJumpList_tower)
export W2DecryptPhasePeak (phaseCreditSpec_doublingChain104 phaseCreditSpec_s7Core)
export W2DecryptPhasePeak (phaseCreditSpec_aesDecCt phaseCreditSpec_aesDecCt_err)
export W2DecryptPhasePeak (phaseCreditSpec_failedTrial_done phaseCreditSpec_trialLoop)
export W2DecryptRecordStorePeak (phaseCreditSpec_recordDecryptEnv phaseCreditSpec_withStoresDecEnv)
export W2DecryptRecordStorePeak (phaseCreditSpec_loadPollStep_smallBox phaseCreditSpec_trustStep_smallBox)
export W2DecryptRecordStorePeak (phaseCreditSpec_saveStep_smallBox phaseCreditSpec_storeStep_smallBox)
export W2DecryptCloneBounds (SessionCloneDom GhostCloneValid RecordGhostValid)
export W2DecryptCloneBounds (sessionCloneDom_of_scopeIn sessionCloneDom_of_scopeKit sessionCloneDom_of_scopeKit_pq)
export W2DecryptCloneBounds (sessionClone_dom_phaseCredit sessionClone_drop_cancel_dom_phaseCredit)
export W2DecryptCloneBounds (serialize_dom_phaseCredit sessStorePoll_dom_phaseCredit recordDecrypt_dom_phaseCredit)
export W2DecryptCloneBounds (sessionClone_dom_phaseCredit_tight sessionClone_drop_cancel_dom_phaseCredit_tight)
export W2DecryptCloneBounds (serialize_dom_phaseCredit_tight sessStorePoll_dom_phaseCredit_tight recordDecrypt_dom_phaseCredit_tight)
export W2DecryptCloneBounds (sessionClone_dom_phaseGroup sessionClone_drop_cancel_dom_phaseGroup)
export W2DecryptCloneBounds (serialize_dom_phaseGroup sessStorePoll_dom_phaseGroup recordDecrypt_dom_phaseGroup)

/-! ## 2. `try_decrypt` Segments `S1`–`S9` (`W2TryDecryptEnv`) -/

/-- W2 Segment 3 (`get_or_create_chain` DH commit) envelope. -/
def W2Seg3DhCommitEnv (dhCap : Nat) (needGrow : Bool) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (· = dhCommitStep12Evs)
      (SeqEnv (· = dhCommitStep3Evs dhCap needGrow) FreeOnlyEvs) evs

/-- W2 Segment 4 (`create_message_keys ≤ 2000`) envelope. -/
def W2Seg4CmkStepEnv (caps : List Nat) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedNonFreeEvs 2000 4000 33)
      (SeqEnv (· = doublingChain104Evs caps) FreeOnlyEvs) evs

/-- W2 Segment 7 (`verify_mac` + optional error string) envelope. -/
def W2Seg7MacEnv (withAddr errAlloc : Bool) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (· = s7CoreEvs withAddr errAlloc) FreeOnlyEvs evs

/-- Failed-trial W2 Segment 8 (`aes_256_cbc_decrypt` error exit) envelope (`Δlive = 0`). -/
def W2AesDecErrEnv (ctLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1

/-- Full W2 `try_decrypt` (`S1` → `S3` → `S4` → `S5` → `S7` → `S8` → `S9`) envelope with black-box `SpqrStepEnv`.
-/
def W2TryDecryptEnv (dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (withAddr errAlloc : Bool) (ctLen : Nat)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedNonFreeEvs 6 16 160)
      (SeqEnv (W2Seg3DhCommitEnv dhCap needGrow)
        (SeqEnv (W2Seg4CmkStepEnv caps)
          (SeqEnv SpqrStepEnv
            (SeqEnv (W2Seg7MacEnv withAddr errAlloc)
              (SeqEnv (AesDecCtShape ctLen)
                (SeqEnv TrApplyBoundedEnv FreeOnlyEvs)))))) evs

/-- Failed-trial W2 `try_decrypt` envelope (`S1` → `S3` → `S4` → `S5` → `S7` → `W2AesDecErrEnv`). -/
def W2TryDecryptFailEnv (dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (withAddr errAlloc : Bool) (ctLen : Nat)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedNonFreeEvs 6 16 160)
      (SeqEnv (W2Seg3DhCommitEnv dhCap needGrow)
        (SeqEnv (W2Seg4CmkStepEnv caps)
          (SeqEnv SpqrStepEnv
            (SeqEnv (W2Seg7MacEnv withAddr errAlloc)
              (SeqEnv (W2AesDecErrEnv ctLen) FreeOnlyEvs))))) evs

def w2TryDecryptCum (M : AllocCostModel) [HasFineReallocCredit M]
    (dhCap : Nat) (needGrow : Bool) (maxSteps maxOldCap c_spqr maxCt : Nat) : Nat :=
  6 * (2 * 160 + 9539) +
    (2 * HasFineReallocCredit.smallAllocCost M 33 +
      HasFineReallocCredit.smallAllocCost M 32 +
      (if needGrow then v104GrowStepCum M dhCap else 0)) +
    (2000 * (2 * 33 + 9539) + maxSteps * (2 * (104 * max 4 (2 * maxOldCap)) + 9539)) +
    c_spqr +
    (2 * HasFineReallocCredit.smallAllocCost M 33 +
      HasFineReallocCredit.smallAllocCost M 36 +
      HasFineReallocCredit.smallAllocCost M 23) +
    (2 * maxCt + 9539) +
    6 * (2 * 34 + 9539)

def w2CmkChainLive (maxOldCap : Nat) : Nat :=
  104 * max 4 (2 * maxOldCap) + 8195

def w2CmkChainPeak (maxOldCap : Nat) : Nat :=
  (104 * maxOldCap + 8195) + (104 * max 4 (2 * maxOldCap) + 8195)

def w2TryDecryptLive (maxOldCap l_spqr maxCt : Nat) : Nat :=
  w2CmkChainLive maxOldCap + l_spqr + (maxCt + 8195)

def w2TryDecryptPeak (maxOldCap l_spqr p_spqr maxCt : Nat) : Nat :=
  max (w2CmkChainPeak maxOldCap)
    (w2CmkChainLive maxOldCap + max p_spqr (l_spqr + (maxCt + 8195)))

def w2TryDecryptMaxReq (dhCap maxOldCap r_spqr maxCt : Nat) : Nat :=
  max 160 (max (max 416 (104 * (2 * dhCap)))
    (max (max 416 (104 * (2 * maxOldCap))) (max r_spqr (max 36 maxCt))))

private theorem max_le_max_nat {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    max a₁ b₁ ≤ max a₂ b₂ := by
  omega

private theorem or_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (fun evs => FreeOnlyEvs evs ∨ E evs) c l p r :=
  ((PhaseCreditSpec.freeOnly_of_hyps hM).or h).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem seq_zero_left {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ 0 0 r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) (c₁ + c₂) l₂ p₂ (max r₁ r₂) :=
  (h₁.seq h₂).mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)

private theorem seq_freeOnly_right_zero_live {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c p r : Nat}
    (h : PhaseCreditSpec M E c 0 p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c 0 p r :=
  (h.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem seq_zero_right_eq_peak {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ r₁ c₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ l₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ 0 0 r₂) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) (c₁ + c₂) l₁ l₁ (max r₁ r₂) :=
  (h₁.seq h₂).mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)

theorem w2TryDecryptLive_le_w2TryDecryptPeak
    (maxOldCap l_spqr p_spqr maxCt : Nat) :
    w2TryDecryptLive maxOldCap l_spqr maxCt ≤
      w2TryDecryptPeak maxOldCap l_spqr p_spqr maxCt := by
  unfold w2TryDecryptLive w2TryDecryptPeak
  have h1 : l_spqr + (maxCt + 8195) ≤ max p_spqr (l_spqr + (maxCt + 8195)) :=
    Nat.le_max_right p_spqr _
  rw [Nat.add_assoc]
  exact Nat.le_trans (Nat.add_le_add_left h1 (w2CmkChainLive maxOldCap))
    (Nat.le_max_right (w2CmkChainPeak maxOldCap) _)

theorem w2Seg3DhCommit_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dhCap : Nat} {needGrow : Bool}
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (W2Seg3DhCommitEnv dhCap needGrow)
      (2 * HasFineReallocCredit.smallAllocCost M 33 +
        HasFineReallocCredit.smallAllocCost M 32 +
        (if needGrow then v104GrowStepCum M dhCap else 0))
      0 0 (max 416 (104 * (2 * dhCap))) := by
  have h12 := phaseCreditSpec_dhCommitStep12 M h33
  have h3 := seq_freeOnly_right_zero_live hM
    (phaseCreditSpec_dhCommitStep3_smallCap M (cap := dhCap) (needGrow := needGrow) hDhSmall)
  exact (or_freeOnly hM (seq_zero_left h12 h3)).mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl 0) (Nat.le_refl 0)
    (by generalize 104 * (2 * dhCap) = r; omega)

theorem w2Seg4CmkStep_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {caps : List Nat} {maxSteps maxOldCap : Nat}
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps) :
    PhaseCreditSpec M (W2Seg4CmkStepEnv caps)
      (2000 * (2 * 33 + 9539) + maxSteps * (2 * (104 * max 4 (2 * maxOldCap)) + 9539))
      (w2CmkChainLive maxOldCap)
      (w2CmkChainPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) := by
  have hFree := PhaseCreditSpec.freeOnly_of_hyps hM
  have hSeeds : PhaseCreditSpec M (BoundedNonFreeEvs 2000 4000 33)
      (2000 * (2 * 33 + 9539)) 0 0 33 :=
    phaseCreditSpec_boundedNonFree_small hM h33
  have hGrow : PhaseCreditSpec M (· = doublingChain104Evs caps)
      (maxSteps * (2 * (104 * max 4 (2 * maxOldCap)) + 9539))
      (w2CmkChainLive maxOldCap)
      (w2CmkChainPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) :=
    (phaseCreditSpec_doublingChain104 hM maxSteps maxOldCap).of_imp
      fun _ h => ⟨caps, hlen, hchain, h⟩
  have hGrowFree : PhaseCreditSpec M (SeqEnv (· = doublingChain104Evs caps) FreeOnlyEvs)
      (maxSteps * (2 * (104 * max 4 (2 * maxOldCap)) + 9539))
      (w2CmkChainLive maxOldCap)
      (w2CmkChainPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) := by
    have hlp : w2CmkChainLive maxOldCap ≤ w2CmkChainPeak maxOldCap := by
      unfold w2CmkChainLive w2CmkChainPeak
      exact Nat.le_add_left _ _
    exact (hGrow.seq hFree).mono
      (by simp only [Nat.add_zero]; exact Nat.le_refl _)
      (by simp only [Nat.add_zero]; exact Nat.le_refl _)
      (by simp only [Nat.add_zero]; exact Nat.max_le.mpr ⟨Nat.le_refl _, hlp⟩)
      (Nat.max_eq_left (Nat.zero_le _)).le
  exact (or_freeOnly hM (seq_zero_left hSeeds hGrowFree)).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by generalize 104 * (2 * maxOldCap) = r; omega)

theorem w2Seg7Mac_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (withAddr errAlloc : Bool)
    (h36 : 36 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (W2Seg7MacEnv withAddr errAlloc)
      (2 * HasFineReallocCredit.smallAllocCost M 33 +
        HasFineReallocCredit.smallAllocCost M 36 +
        HasFineReallocCredit.smallAllocCost M 23)
      0 0 36 :=
  or_freeOnly hM (seq_freeOnly_right_zero_live hM (phaseCreditSpec_s7Core M withAddr errAlloc h36))

/-- `PhaseCreditSpec M` for `W2TryDecryptEnv` with black-box `SpqrStepEnv`. -/
theorem w2TryDecrypt_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap c_spqr l_spqr p_spqr r_spqr maxCt : Nat}
    (h160 : 160 ≤ HasFineReallocCredit.smallMaxReq M)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq M)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hSpqr : PhaseCreditSpec M SpqrStepEnv c_spqr l_spqr p_spqr r_spqr)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec M
      (W2TryDecryptEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (w2TryDecryptCum M dhCap needGrow maxSteps maxOldCap c_spqr maxCt)
      (w2TryDecryptLive maxOldCap l_spqr maxCt)
      (w2TryDecryptPeak maxOldCap l_spqr p_spqr maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap r_spqr maxCt) := by
  have hS1 := phaseCreditSpec_boundedNonFree_small hM (k := 6) (maxLen := 16) h160
  have hS3 := w2Seg3DhCommit_phaseCreditSpec hM (dhCap := dhCap) (needGrow := needGrow)
    (Nat.le_trans (by decide) h160) hDhSmall
  have hS4 := w2Seg4CmkStep_phaseCreditSpec hM (Nat.le_trans (by decide) h160) hlen hchain
  have hS7 := w2Seg7Mac_phaseCreditSpec hM withAddr errAlloc (Nat.le_trans (by decide) h160)
  have hS8 := phaseCreditSpec_aesDecCt hM hct
  have hS9 := seq_freeOnly_right_zero_live hM
    (phaseCreditSpec_trApplyBounded hM (Nat.le_trans (by decide) h160))
  have h89 := seq_zero_right_eq_peak hS8 hS9
  have h79 := seq_zero_left hS7 h89
  have h59 := hSpqr.seq h79
  have h49 := hS4.seq h59
  have h39 := seq_zero_left hS3 h49
  have h19 := seq_zero_left hS1 h39
  unfold w2TryDecryptCum w2TryDecryptLive w2TryDecryptPeak w2TryDecryptMaxReq
  refine (or_freeOnly hM h19).mono ?_ ?_ (Nat.le_refl _) ?_
  · simp only [Nat.add_assoc]; exact Nat.le_refl _
  · simp only [Nat.add_assoc]; exact Nat.le_refl _
  · generalize max 416 (104 * (2 * dhCap)) = r3
    generalize max 416 (104 * (2 * maxOldCap)) = r4
    omega

/-- Failed-trial `PhaseCreditSpec M` for `W2TryDecryptFailEnv`. -/
theorem w2TryDecryptFail_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap c_spqr l_spqr p_spqr r_spqr maxCt : Nat}
    (h160 : 160 ≤ HasFineReallocCredit.smallMaxReq M)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq M)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hSpqr : PhaseCreditSpec M SpqrStepEnv c_spqr l_spqr p_spqr r_spqr)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec M
      (W2TryDecryptFailEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (w2TryDecryptCum M dhCap needGrow maxSteps maxOldCap c_spqr maxCt)
      (w2CmkChainLive maxOldCap + l_spqr)
      (w2TryDecryptPeak maxOldCap l_spqr p_spqr maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap r_spqr maxCt) := by
  have hS1 := phaseCreditSpec_boundedNonFree_small hM (k := 6) (maxLen := 16) h160
  have hS3 := w2Seg3DhCommit_phaseCreditSpec hM (dhCap := dhCap) (needGrow := needGrow)
    (Nat.le_trans (by decide) h160) hDhSmall
  have hS4 := w2Seg4CmkStep_phaseCreditSpec hM (Nat.le_trans (by decide) h160) hlen hchain
  have hS7 := w2Seg7Mac_phaseCreditSpec hM withAddr errAlloc (Nat.le_trans (by decide) h160)
  have hS8 := seq_freeOnly_right_zero_live hM (phaseCreditSpec_aesDecCt_err hM hct)
  have h78 := seq_zero_left hS7 hS8
  have h58 := hSpqr.seq h78
  have h48 := hS4.seq h58
  have h38 := seq_zero_left hS3 h48
  have h18 := seq_zero_left hS1 h38
  have hcum_assoc : ∀ a b c d e f : Nat, a + (b + (c + (d + (e + f)))) = a + b + c + d + e + f :=
    fun _ _ _ _ _ _ => by simp only [Nat.add_assoc]
  unfold w2TryDecryptCum w2TryDecryptPeak w2TryDecryptMaxReq
  refine (or_freeOnly hM h18).mono ?_ ?_ (Nat.le_refl _) (Nat.le_refl _)
  · rw [hcum_assoc]; exact Nat.le_add_right _ _
  · simp only [Nat.add_zero]; exact Nat.le_refl _

/-! ## 3. Guarded `WithStoresDecEnv` Slot Wrapper and `Δlive ≤ Δpeak` -/

/-- `l_st ≤ p_st` on the trailing `store_session` step implies `Δlive ≤ Δpeak` for `phaseCreditSpec_withStoresDecEnv`.
-/
theorem withStoresDec_live_le_peak
    (remNameLen l_ld p_ld l_rd p_rd l_tr p_tr l_sv p_sv l_st p_st : Nat)
    (hlp_st : l_st ≤ p_st) :
    let l_sc := remNameLen + 8195
    let l_kr := l_tr + max l_sc (l_sv + l_st)
    let p_kr := max p_tr (l_tr + max l_sc (max p_sv (l_sv + p_st)))
    let l_some := l_rd + l_kr
    let p_some := max p_rd (l_rd + p_kr)
    l_ld + max l_sc l_some ≤ max p_ld (l_ld + max l_sc p_some) := by
  intro l_sc l_kr p_kr l_some p_some
  have h1 : l_sv + l_st ≤ max p_sv (l_sv + p_st) :=
    Nat.le_trans (Nat.add_le_add_left hlp_st l_sv) (Nat.le_max_right p_sv (l_sv + p_st))
  have h2 : max l_sc (l_sv + l_st) ≤ max l_sc (max p_sv (l_sv + p_st)) :=
    max_le_max_nat (Nat.le_refl l_sc) h1
  have hkr : l_kr ≤ p_kr :=
    Nat.le_trans (Nat.add_le_add_left h2 l_tr) (Nat.le_max_right p_tr _)
  have hsome : l_some ≤ p_some :=
    Nat.le_trans (Nat.add_le_add_left hkr l_rd) (Nat.le_max_right p_rd _)
  have hmax : max l_sc l_some ≤ max l_sc p_some :=
    max_le_max_nat (Nat.le_refl l_sc) hsome
  exact Nat.le_trans (Nat.add_le_add_left hmax l_ld) (Nat.le_max_right p_ld _)

/-- Small-box `PhaseCreditSpec M` for the `Scope`-guarded `WithStoresDecEnv`. -/
theorem w2WithStoresDec_creditSpec_smallBox {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} (hM : ModelHyps M)
    (hsmall1569 : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    {pqCap c_ld l_ld p_ld r_ld c_td l_td p_td r_td
     c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hboxLd : kit.loadBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hboxSt : kit.storeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hboxTr : ikit.trustBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hboxSv : ikit.saveBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hDom : ∀ rec ses,
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      SessionCloneDom pqCap ses)
    (hLoadPoll : PhaseCreditSpec M (kitEnv.loadPollEnv st0 x.rem.val) c_ld l_ld p_ld r_ld)
    (hTd : ∀ rec ses G G₁,
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      CloneRel G G₁ →
      PhaseCreditSpec M (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td)
    (hTrustPoll : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 x.rem.val k .receiving) c_tr l_tr p_tr r_tr)
    (hSavePoll : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M
        (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true))
          x.rem.val k)
        c_sv l_sv p_sv r_sv)
    (hStorePoll : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M (kitEnv.storePollEnv st0 x.rem.val rec') c_st l_st p_st r_st) :
    let c_ld_s := 2 * kit.loadBoxSize + 9539 + c_ld
    let r_ld_s := max kit.loadBoxSize r_ld
    let c_tr_s := 2 * ikit.trustBoxSize + 9539 + c_tr
    let r_tr_s := max ikit.trustBoxSize r_tr
    let c_sv_s := 2 * ikit.saveBoxSize + 9539 + c_sv
    let r_sv_s := max ikit.saveBoxSize r_sv
    let c_st_s := 2 * kit.storeBoxSize + 9539 + c_st
    let r_st_s := max kit.storeBoxSize r_st
    let c_rd := 98382860 + 2 * pqCap + c_td
    let l_rd := 1089170 + pqCap + l_td
    let p_rd := 1089170 + pqCap + max p_td l_td
    let r_rd := max (max 208000 pqCap) (max r_td 192)
    let c_sc := 2 * x.rem.name.bytes.length + 9539
    let l_sc := x.rem.name.bytes.length + 8195
    let c_kr := c_tr_s + max c_sc (c_sv_s + c_st_s)
    let l_kr := l_tr + max l_sc (l_sv + l_st)
    let p_kr := max p_tr (l_tr + max l_sc (max p_sv (l_sv + p_st)))
    let r_kr := max r_tr_s (max x.rem.name.bytes.length (max r_sv_s r_st_s))
    let c_some := c_rd + c_kr
    let l_some := l_rd + l_kr
    let p_some := max p_rd (l_rd + p_kr)
    let r_some := max r_rd r_kr
    PhaseCreditSpec M
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      (c_ld_s + max (max c_sc 9573) c_some)
      (l_ld + max l_sc l_some)
      (max p_ld (l_ld + max l_sc p_some))
      (max r_ld_s (max (max x.rem.name.bytes.length 17) r_some)) := by
  intro c_ld_s r_ld_s c_tr_s r_tr_s c_sv_s r_sv_s c_st_s r_st_s
    c_rd l_rd p_rd r_rd c_sc l_sc c_kr l_kr p_kr r_kr c_some l_some p_some r_some
  exact phaseCreditSpec_withStoresDecEnv hM (by omega)
    (phaseCreditSpec_loadPollStep_smallBox hM hboxLd hLoadPoll)
    (fun rec ses G hsc hcur hgv =>
      recordDecrypt_dom_phaseCredit hM hsmall1569 (x := recGhostOf x 0#64 G ses.state) rfl hgv
        (hDom rec ses hsc hcur) (fun G₁ hRel => hTd rec ses G G₁ hsc hcur hgv hRel))
    (fun rec pt rec' ses k hsc hdec hc hk =>
      phaseCreditSpec_trustStep_smallBox hM hboxTr (hTrustPoll rec pt rec' ses k hsc hdec hc hk))
    (fun rec pt rec' ses k hsc hdec hc hk =>
      phaseCreditSpec_saveStep_smallBox hM hboxSv (hSavePoll rec pt rec' ses k hsc hdec hc hk))
    (fun rec pt rec' ses k hsc hdec hc hk =>
      phaseCreditSpec_storeStep_smallBox hM hboxSt (hStorePoll rec pt rec' ses k hsc hdec hc hk))

/-! ## 4. Tight `fineCostModel`, `TrialLoop`, and `PhaseGroupSpec` Bounds -/

section TightFineTryDecrypt

open CryptoGames.LibsignalSession (SessionState ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB spqrAuthApi
   spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap (rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale MmapThresholdReq fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq
   smallAllocCost_le_488_of_le_28 smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec fineSmallAllocGroupS fineSmallReallocGroupS
   nonFreeCount nonFreeCount_rustAllocEvents nonFreeCount_rustReallocEvents
   smallAllocGroupS_fineCostModel_eq smallAllocGroupS_le_16659_of_le_44
   smallReallocGroupS_fineCostModel_eq)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv DeallocCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (optLargeCost_fine_mono sessionClone_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (dropClonedSessionEvents fineSmallAllocCost_le_143484 fineSmallAllocCost_le_9789_of_le_256
   fineSmallReallocCost_le_143484 fineSmallReallocCost_le_9789_of_le_256 optLargeCost
   rustAllocTightCum rustAllocTightCum_fine_le_143484 segCloneLarge segCloneMaxReq segCloneTightCum)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
  (StatesRecvTightGroupSpec spqrRecvParts_c07_phaseGroupSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvC07TightEnv SpqrRecvTightDomain)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightRecvKey (KeyHistorySmallOrReserved)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
  (StatesRecvTightCreditSpec spqrRecvParts_c07_phaseCreditSpec_tight
   spqrRecvParts_c07_phaseCreditSpec_tight_c09a spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (dropClonedSession_phaseGroup segCloneLarge_fine_le_of_dom segCloneMaxReq_le_of_dom
   segCloneTightCum_fine_le_of_dom)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak
  (cmkJumpFinalIdx cmkJumpListEvs growOne104Evs stepEvents_growOne104_pos v104Live)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak (singleAllocCum)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
  (BoundedLenEvs.toBoundedNonFreeEvs isNonFreeEv req_align_growOne104 stepEvents_growOne104_first)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

private theorem step_small_or_free_fine_256 {ev : AllocEvent} {maxReq : Nat}
    (st : fineCostModel.σ) (hmax : maxReq ≤ 256)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    let st' := fineCostModel.step ev st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (if isNonFreeEv ev then 9789 else 0) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  cases ev with
  | free al sz =>
    simp only [isNonFreeEv, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact fineCostModel_freeNonInc al sz st
  | alloc req =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq] at hreq ⊢
    have h256 : req ≤ 256 := Nat.le_trans hreq hmax
    have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans h256 (by decide)
    obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_alloc_small_any st hsm
    have hsa := fineSmallAllocCost_le_9789_of_le_256 h256
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hsa _), hl, hp⟩
  | aligned al req =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq, eventStepAlign] at hreq hal ⊢
    have h256 : req ≤ 256 := Nat.le_trans hreq hmax
    have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans h256 (by decide)
    obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_aligned_small_any st hal hsm
    have hsa := fineSmallAllocCost_le_9789_of_le_256 h256
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hsa _), hl, hp⟩
  | realloc al old newSz =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq, eventStepAlign] at hreq hal ⊢
    have h256 : newSz ≤ 256 := Nat.le_trans hreq hmax
    have hsm : newSz ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans h256 (by decide)
    have hsr := fineSmallReallocCost_le_9789_of_le_256 h256
    by_cases hold : old ≤ HasFineReallocCredit.smallMaxReq fineCostModel
    · obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_realloc_small_small_any st hal hold hsm
      exact ⟨Nat.le_trans hc (Nat.add_le_add_left hsr _), hl, hp⟩
    · have hold_gt : HasFineReallocCredit.smallMaxReq fineCostModel < old := Nat.lt_of_not_ge hold
      obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_realloc_large_small_any st hal hold_gt hsm
      exact ⟨Nat.le_trans hc (Nat.add_le_add_left hsr _),
        Nat.le_trans hl (Nat.sub_le _ _), hp⟩

private theorem stepEvents_boundedNonFree_fine_256 {maxReq : Nat} (hmax : maxReq ≤ 256) :
    ∀ (evs : List AllocEvent) (st : fineCostModel.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      let st' := fineCostModel.stepEvents evs st
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st + (evs.filter isNonFreeEv).length * 9789 ∧
      HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st
  | [], st, _ => by
    simp only [AllocCostModel.stepEvents_nil, List.filter_nil, List.length_nil,
      Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: rest, st, hall => by
    obtain ⟨hreq, hal⟩ := hall ev List.mem_cons_self
    obtain ⟨hc1, hl1, hp1⟩ := step_small_or_free_fine_256 st hmax hreq hal
    obtain ⟨hc2, hl2, hp2⟩ := stepEvents_boundedNonFree_fine_256 hmax rest (fineCostModel.step ev st)
      (fun e he => hall e (List.mem_cons_of_mem ev he))
    simp only [AllocCostModel.stepEvents_cons, List.filter_cons]
    cases hnf : isNonFreeEv ev
    · simp only [hnf, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc1 ⊢
      exact ⟨Nat.le_trans hc2 (Nat.add_le_add_right hc1 _),
        Nat.le_trans hl2 hl1, Nat.le_trans hp2 hp1⟩
    · simp only [hnf, ↓reduceIte, List.length_cons] at hc1 ⊢
      have hmul : ((rest.filter isNonFreeEv).length + 1) * 9789 =
          9789 + (rest.filter isNonFreeEv).length * 9789 := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      refine ⟨?_, Nat.le_trans hl2 hl1, Nat.le_trans hp2 hp1⟩
      rw [hmul, ← Nat.add_assoc]
      exact Nat.le_trans hc2 (Nat.add_le_add_right hc1 _)

theorem phaseCreditSpec_boundedNonFree_fine_256 (k maxLen maxReq : Nat) (hmax : maxReq ≤ 256) :
    PhaseCreditSpec fineCostModel (BoundedNonFreeEvs k maxLen maxReq)
      (k * 9789) 0 0 maxReq where
  req_align _ h := h.2.2
  credit_le st0 {evs} h := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_boundedNonFree_fine_256 hmax evs st0 h.2.2
    have hmul : (evs.filter isNonFreeEv).length * 9789 ≤ k * 9789 :=
      Nat.mul_le_mul_right 9789 h.2.1
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hmul _),
      by simpa using hl,
      Nat.le_trans hp (Nat.le_max_left _ _)⟩

theorem phaseCreditSpec_boundedLen_fine_256 (k maxReq : Nat) (hmax : maxReq ≤ 256) :
    PhaseCreditSpec fineCostModel (BoundedLenEvs k maxReq)
      (k * 9789) 0 0 maxReq :=
  (phaseCreditSpec_boundedNonFree_fine_256 k k maxReq hmax).of_imp fun _ =>
    BoundedLenEvs.toBoundedNonFreeEvs

theorem v104Live_fine_eq (c : Nat) :
    v104Live fineCostModel c = optLargeCost fineCostModel (104 * c) :=
  rfl

theorem v104Live_fine_mono {c₁ c₂ : Nat} (hc : c₁ ≤ c₂) :
    v104Live fineCostModel c₁ ≤ v104Live fineCostModel c₂ :=
  optLargeCost_fine_mono (Nat.mul_le_mul_left 104 hc)

/-- Universal `cumSmall` ceiling `v104GrowStepCum fineCostModel c ≤ 143,484` for all `c : Nat`. -/
theorem v104GrowStepCum_fine_le_143484 (c : Nat) :
    v104GrowStepCum fineCostModel c ≤ 143484 := by
  unfold v104GrowStepCum
  split
  · unfold singleAllocCum
    have h416 : 416 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; decide
    simp only [h416, ↓reduceIte]
    exact fineSmallAllocCost_le_143484 h416
  · split
    · rename_i _ hle
      exact fineSmallReallocCost_le_143484 hle
    · rw [fineCostModel_largeMetaCost_eq]; decide

def w2CmkChainTightLive (maxOldCap : Nat) : Nat :=
  optLargeCost fineCostModel (104 * max 4 (2 * maxOldCap))

def w2CmkChainTightPeak (maxOldCap : Nat) : Nat :=
  optLargeCost fineCostModel (104 * maxOldCap) +
    optLargeCost fineCostModel (104 * max 4 (2 * maxOldCap))

private def DoublingTailPredFine (maxOldCap c_cur : Nat) : List Nat → Prop
  | [] => True
  | c_next :: rest => c_next = c_cur ∧ DoublingChainLe maxOldCap (c_next :: rest)

private theorem stepEvents_doublingTail104_fine {maxOldCap L₀ : Nat} :
    ∀ (rest : List Nat) (c_cur : Nat) (st : fineCostModel.σ),
      0 < c_cur →
      c_cur ≤ max 4 (2 * maxOldCap) →
      DoublingTailPredFine maxOldCap c_cur rest →
      HasFineReallocCredit.liveLarge st ≤ L₀ + v104Live fineCostModel c_cur →
      let st' := fineCostModel.stepEvents (doublingChain104Evs rest) st
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st + rest.length * 143484 ∧
      HasFineReallocCredit.liveLarge st' ≤ L₀ + w2CmkChainTightLive maxOldCap ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st) (L₀ + w2CmkChainTightPeak maxOldCap)
  | [], c_cur, st, _, hcur_le, _, hlive => by
    simp only [doublingChain104Evs, AllocCostModel.stepEvents_nil, List.length_nil,
      Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _,
      Nat.le_trans hlive (Nat.add_le_add_left (v104Live_fine_mono hcur_le) L₀),
      Nat.le_max_left _ _⟩
  | [c], c_cur, st, hcur_pos, _, hchain, hlive => by
    dsimp only [DoublingTailPredFine, DoublingChainLe] at hchain
    obtain ⟨rfl, hc_le⟩ := hchain
    simp only [doublingChain104Evs, List.length_singleton, Nat.one_mul, List.append_nil]
    obtain ⟨hc1, hl1, hp1⟩ := stepEvents_growOne104_pos fineCostModel st hcur_pos hlive
    have hcum_c := v104GrowStepCum_fine_le_143484 c
    have h2c_le : 2 * c ≤ max 4 (2 * maxOldCap) :=
      Nat.le_trans (Nat.mul_le_mul_left 2 hc_le) (Nat.le_max_right 4 (2 * maxOldCap))
    have hl_old := v104Live_fine_mono hc_le
    have hl_new := v104Live_fine_mono h2c_le
    have hpk : L₀ + v104Live fineCostModel c + v104Live fineCostModel (2 * c) ≤
        L₀ + w2CmkChainTightPeak maxOldCap := by
      unfold w2CmkChainTightPeak
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.add_le_add hl_old hl_new) L₀
    exact ⟨Nat.le_trans hc1 (Nat.add_le_add_left hcum_c _),
      Nat.le_trans hl1 (Nat.add_le_add_left hl_new L₀),
      Nat.le_trans hp1 (max_le_max_nat (Nat.le_refl _) hpk)⟩
  | c₁ :: c₂ :: rest, c_cur, st, hcur_pos, _, hchain, hlive => by
    dsimp only [DoublingTailPredFine, DoublingChainLe] at hchain
    obtain ⟨rfl, hc1_le, hc2_eq, hrest⟩ := hchain
    have hc1_nz : c₁ ≠ 0 := Nat.ne_of_gt hcur_pos
    simp only [hc1_nz, ↓reduceIte] at hc2_eq
    dsimp only
    rw [show doublingChain104Evs (c₁ :: c₂ :: rest) =
          growOne104Evs c₁ ++ doublingChain104Evs (c₂ :: rest) from rfl,
        show (c₁ :: c₂ :: rest).length = (c₂ :: rest).length + 1 from rfl,
        fineCostModel.stepEvents_append]
    obtain ⟨hc1, hl1, hp1⟩ := stepEvents_growOne104_pos fineCostModel st hcur_pos hlive
    have hc2_pos : 0 < c₂ := by omega
    have hc2_le : c₂ ≤ max 4 (2 * maxOldCap) := by
      rw [hc2_eq]
      exact Nat.le_trans (Nat.mul_le_mul_left 2 hc1_le) (Nat.le_max_right 4 (2 * maxOldCap))
    rw [← hc2_eq] at hl1
    obtain ⟨hc2, hl2, hp2⟩ := stepEvents_doublingTail104_fine (c₂ :: rest) c₂
      (fineCostModel.stepEvents (growOne104Evs c₁) st) hc2_pos hc2_le ⟨rfl, hrest⟩ hl1
    have hcum_c1 := v104GrowStepCum_fine_le_143484 c₁
    have hmul : ((c₂ :: rest).length + 1) * 143484 =
        143484 + (c₂ :: rest).length * 143484 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hcum_tot : HasFineReallocCredit.cumSmall
        (fineCostModel.stepEvents (doublingChain104Evs (c₂ :: rest))
          (fineCostModel.stepEvents (growOne104Evs c₁) st)) ≤
        HasFineReallocCredit.cumSmall st + ((c₂ :: rest).length + 1) * 143484 := by
      rw [hmul, ← Nat.add_assoc]
      exact Nat.le_trans hc2
        (Nat.add_le_add_right (Nat.le_trans hc1 (Nat.add_le_add_left hcum_c1 _)) _)
    have hl_old := v104Live_fine_mono hc1_le
    have hl_new : v104Live fineCostModel (2 * c₁) ≤
        optLargeCost fineCostModel (104 * max 4 (2 * maxOldCap)) :=
      v104Live_fine_mono (hc2_eq ▸ hc2_le)
    have hpk1 : L₀ + v104Live fineCostModel c₁ + v104Live fineCostModel (2 * c₁) ≤
        L₀ + w2CmkChainTightPeak maxOldCap := by
      unfold w2CmkChainTightPeak
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left (Nat.add_le_add hl_old hl_new) L₀
    have hpk_tot := Nat.le_trans hp2
      (Nat.max_le.mpr
        ⟨Nat.le_trans hp1
           (Nat.max_le.mpr
             ⟨Nat.le_max_left _ _,
              Nat.le_trans hpk1 (Nat.le_max_right _ _)⟩),
         Nat.le_max_right _ _⟩)
    exact ⟨hcum_tot, hl2, hpk_tot⟩

/-- Tight `fineCostModel` `PhaseCreditSpec` for any `Vec<104>` doubling chain (`DoublingChainLe maxOldCap caps`).
-/
theorem phaseCreditSpec_doublingChain104_fine_tight (maxSteps maxOldCap : Nat) :
    PhaseCreditSpec fineCostModel
      (fun evs => ∃ caps : List Nat,
        caps.length ≤ maxSteps ∧ DoublingChainLe maxOldCap caps ∧ evs = doublingChain104Evs caps)
      (maxSteps * 143484)
      (w2CmkChainTightLive maxOldCap)
      (w2CmkChainTightPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) where
  req_align := by
    rintro _ ⟨caps, -, hchain, rfl⟩ ev hev
    induction caps with
    | nil => nomatch hev
    | cons c rest ih =>
      simp only [doublingChain104Evs, List.mem_append] at hev
      have hc_le : c ≤ maxOldCap := by
        cases rest with
        | nil => exact hchain
        | cons _ _ => exact hchain.1
      rcases hev with he | he
      · exact req_align_growOne104 hc_le ev he
      · cases rest with
        | nil => nomatch he
        | cons _ _ => exact ih hchain.2.2 he
  credit_le := by
    rintro st0 _ ⟨caps, hlen, hchain, rfl⟩
    cases caps with
    | nil =>
      simp only [doublingChain104Evs, AllocCostModel.stepEvents_nil]
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_max_left _ _⟩
    | cons c₀ rest =>
      simp only [doublingChain104Evs]
      rw [fineCostModel.stepEvents_append]
      have hc0_le : c₀ ≤ maxOldCap := by
        cases rest with
        | nil => exact hchain
        | cons _ _ => exact hchain.1
      have hc1_pos : 0 < (if c₀ = 0 then 4 else 2 * c₀) := by
        by_cases hz : c₀ = 0
        · simp [hz]
        · simp only [hz, ↓reduceIte]
          exact Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hz)
      have hc1_le : (if c₀ = 0 then 4 else 2 * c₀) ≤ max 4 (2 * maxOldCap) := by
        split
        · exact Nat.le_max_left 4 (2 * maxOldCap)
        · exact Nat.le_trans (Nat.mul_le_mul_left 2 hc0_le) (Nat.le_max_right 4 (2 * maxOldCap))
      obtain ⟨hc1, hl1, hp1⟩ := stepEvents_growOne104_first fineCostModel c₀ st0 (Nat.le_refl _)
      have htail_cond : DoublingTailPredFine maxOldCap (if c₀ = 0 then 4 else 2 * c₀) rest := by
        cases rest with
        | nil => trivial
        | cons _ _ => exact ⟨hchain.2.1, hchain.2.2⟩
      obtain ⟨hc2, hl2, hp2⟩ := stepEvents_doublingTail104_fine rest
        (if c₀ = 0 then 4 else 2 * c₀)
        (fineCostModel.stepEvents (growOne104Evs c₀) st0) hc1_pos hc1_le htail_cond hl1
      have hcum0 := v104GrowStepCum_fine_le_143484 c₀
      have hlen_mul : (rest.length + 1) * 143484 ≤ maxSteps * 143484 := by
        simp only [List.length_cons] at hlen
        exact Nat.mul_le_mul_right 143484 hlen
      have hmul : (rest.length + 1) * 143484 = 143484 + rest.length * 143484 := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      have hcum_tot : HasFineReallocCredit.cumSmall
          (fineCostModel.stepEvents (doublingChain104Evs rest)
            (fineCostModel.stepEvents (growOne104Evs c₀) st0)) ≤
          HasFineReallocCredit.cumSmall st0 + maxSteps * 143484 := by
        refine Nat.le_trans ?_ (Nat.add_le_add_left hlen_mul _)
        rw [hmul, ← Nat.add_assoc]
        exact Nat.le_trans hc2
          (Nat.add_le_add_right (Nat.le_trans hc1 (Nat.add_le_add_left hcum0 _)) _)
      have hl_c1 : v104Live fineCostModel (if c₀ = 0 then 4 else 2 * c₀) ≤
          w2CmkChainTightPeak maxOldCap := by
        unfold w2CmkChainTightPeak
        exact Nat.le_trans (v104Live_fine_mono hc1_le) (Nat.le_add_left _ _)
      have hpk_tot := Nat.le_trans hp2
        (Nat.max_le.mpr
          ⟨Nat.le_trans hp1
             (Nat.max_le.mpr
               ⟨Nat.le_max_left _ _,
                Nat.le_trans (Nat.add_le_add_left hl_c1 _) (Nat.le_max_right _ _)⟩),
           Nat.le_max_right _ _⟩)
      exact ⟨hcum_tot, hl2, hpk_tot⟩

theorem phaseCreditSpec_aesDecCt_fine_tight {ctLen maxCt : Nat} (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel (AesDecCtShape ctLen)
      143484
      (optLargeCost fineCostModel maxCt)
      (optLargeCost fineCostModel maxCt)
      maxCt := by
  have hnil : PhaseCreditSpec fineCostModel (· = [])
      143484 (optLargeCost fineCostModel maxCt) (optLargeCost fineCostModel maxCt) maxCt :=
    (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have halloc0 := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
    (req := ctLen) (al := 1) (by decide)
  have halloc : PhaseCreditSpec fineCostModel (· = rustAllocEvents ctLen 1)
      143484 (optLargeCost fineCostModel maxCt) (optLargeCost fineCostModel maxCt) maxCt :=
    halloc0.mono
      (rustAllocTightCum_fine_le_143484 ctLen)
      (optLargeCost_fine_mono hct)
      (optLargeCost_fine_mono hct)
      hct
  have ha_zero : PhaseCreditSpec fineCostModel (· = rustAllocEvents ctLen 1)
      (rustAllocTightCum fineCostModel ctLen)
      (0 + optLargeCost fineCostModel ctLen)
      (optLargeCost fineCostModel ctLen) ctLen := by
    simpa [Nat.zero_add] using halloc0
  have hd0 := SessionCloneCredit.DeallocCreditSpec.free_optLarge fineCostModel
    (req := ctLen) (al := 1) (by decide)
  have hcancel : PhaseCreditSpec fineCostModel
      (ConcatEnv (· = rustAllocEvents ctLen 1) (· = rustDeallocEvents ctLen 1))
      143484 (optLargeCost fineCostModel maxCt) (optLargeCost fineCostModel maxCt) maxCt :=
    (ha_zero.concat_dealloc_cancel hd0).mono
      (rustAllocTightCum_fine_le_143484 ctLen)
      (Nat.zero_le _)
      (optLargeCost_fine_mono hct)
      hct
  refine ((hnil.or (halloc.or hcancel)).of_imp ?_).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩⟩)
  rintro evs (rfl | rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨rustAllocEvents ctLen 1, rustDeallocEvents ctLen 1, rfl, rfl, rfl⟩)

theorem phaseCreditSpec_aesDecCt_err_fine_tight {ctLen maxCt : Nat} (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel (W2AesDecErrEnv ctLen)
      143484 0 (optLargeCost fineCostModel maxCt) maxCt := by
  have hnil : PhaseCreditSpec fineCostModel (· = [])
      143484 0 (optLargeCost fineCostModel maxCt) maxCt :=
    (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.zero_le _) (Nat.zero_le _)
  have halloc0 := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
    (req := ctLen) (al := 1) (by decide)
  have ha_zero : PhaseCreditSpec fineCostModel (· = rustAllocEvents ctLen 1)
      (rustAllocTightCum fineCostModel ctLen)
      (0 + optLargeCost fineCostModel ctLen)
      (optLargeCost fineCostModel ctLen) ctLen := by
    simpa [Nat.zero_add] using halloc0
  have hd0 := SessionCloneCredit.DeallocCreditSpec.free_optLarge fineCostModel
    (req := ctLen) (al := 1) (by decide)
  have hcancel : PhaseCreditSpec fineCostModel
      (ConcatEnv (· = rustAllocEvents ctLen 1) (· = rustDeallocEvents ctLen 1))
      143484 0 (optLargeCost fineCostModel maxCt) maxCt :=
    (ha_zero.concat_dealloc_cancel hd0).mono
      (rustAllocTightCum_fine_le_143484 ctLen)
      (Nat.le_refl 0)
      (optLargeCost_fine_mono hct)
      hct
  refine ((hnil.or hcancel).of_imp ?_).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
  rintro evs (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr ⟨rustAllocEvents ctLen 1, rustDeallocEvents ctLen 1, rfl, rfl, rfl⟩

theorem w2Seg3DhCommit_fine_phaseCreditSpec_tight {dhCap : Nat} {needGrow : Bool}
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel) :
    PhaseCreditSpec fineCostModel (W2Seg3DhCommitEnv dhCap needGrow)
      (2214 + (if needGrow then v104GrowStepCum fineCostModel dhCap else 0))
      0 0 (max 416 (104 * (2 * dhCap))) := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hc33 := smallAllocCost_le_738_of_le_44 (req := 33) (by decide)
  have hc32 := smallAllocCost_le_738_of_le_44 (req := 32) (by decide)
  have h2214 : 2 * HasFineReallocCredit.smallAllocCost fineCostModel 33 +
      HasFineReallocCredit.smallAllocCost fineCostModel 32 ≤ 2214 :=
    Nat.le_trans (Nat.add_le_add (Nat.mul_le_mul_left 2 hc33) hc32) (by decide)
  exact (w2Seg3DhCommit_phaseCreditSpec fineCostModel_modelHyps h33 hDhSmall).mono
    (Nat.add_le_add_right h2214 _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)

theorem w2Seg4CmkStep_fine_phaseCreditSpec_tight
    {caps : List Nat} {maxSteps maxOldCap : Nat}
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps) :
    PhaseCreditSpec fineCostModel (W2Seg4CmkStepEnv caps)
      (19210000 + maxSteps * 143484)
      (w2CmkChainTightLive maxOldCap)
      (w2CmkChainTightPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hFree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hSeeds : PhaseCreditSpec fineCostModel (BoundedNonFreeEvs 2000 4000 33)
      19210000 0 0 33 :=
    (phaseCreditSpec_boundedNonFree_small fineCostModel_modelHyps h33).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)
  have hGrow : PhaseCreditSpec fineCostModel (· = doublingChain104Evs caps)
      (maxSteps * 143484)
      (w2CmkChainTightLive maxOldCap)
      (w2CmkChainTightPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) :=
    (phaseCreditSpec_doublingChain104_fine_tight maxSteps maxOldCap).of_imp
      fun _ h => ⟨caps, hlen, hchain, h⟩
  have hlp : w2CmkChainTightLive maxOldCap ≤ w2CmkChainTightPeak maxOldCap :=
    Nat.le_add_left _ _
  have hGrowFree : PhaseCreditSpec fineCostModel (SeqEnv (· = doublingChain104Evs caps) FreeOnlyEvs)
      (maxSteps * 143484)
      (w2CmkChainTightLive maxOldCap)
      (w2CmkChainTightPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) :=
    (hGrow.seq hFree).mono
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_trans (Nat.le_of_eq (Nat.add_zero _)) hlp⟩)
      (Nat.max_eq_left (Nat.zero_le _)).le
  exact (or_freeOnly fineCostModel_modelHyps (seq_zero_left hSeeds hGrowFree)).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by generalize 104 * (2 * maxOldCap) = r; omega)

theorem w2Seg7Mac_fine_phaseCreditSpec_tight (withAddr errAlloc : Bool) :
    PhaseCreditSpec fineCostModel (W2Seg7MacEnv withAddr errAlloc) 2702 0 0 36 := by
  have h36 : 36 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hc33 := smallAllocCost_le_738_of_le_44 (req := 33) (by decide)
  have hc36 := smallAllocCost_le_738_of_le_44 (req := 36) (by decide)
  have hc23 := smallAllocCost_le_488_of_le_28 (req := 23) (by decide)
  have hsum : 2 * HasFineReallocCredit.smallAllocCost fineCostModel 33 +
      HasFineReallocCredit.smallAllocCost fineCostModel 36 +
      HasFineReallocCredit.smallAllocCost fineCostModel 23 ≤ 2702 :=
    Nat.le_trans
      (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hc33) hc36) hc23)
      (by decide)
  exact (w2Seg7Mac_phaseCreditSpec fineCostModel_modelHyps withAddr errAlloc h36).mono
    hsum (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 36)

/-- Tight `fineCostModel` `Δcum` for `W2TryDecryptEnv` and `W2TryDecryptFailEnv`. -/
def w2TryDecryptTightCum (dhCap : Nat) (needGrow : Bool) (maxSteps c_spqr : Nat) : Nat :=
  58734 +
    (2214 + (if needGrow then v104GrowStepCum fineCostModel dhCap else 0)) +
    (19210000 + maxSteps * 143484) +
    c_spqr +
    2702 +
    143484 +
    57642

def w2TryDecryptTightLive (maxOldCap l_spqr maxCt : Nat) : Nat :=
  w2CmkChainTightLive maxOldCap + l_spqr + optLargeCost fineCostModel maxCt

def w2TryDecryptTightPeak (maxOldCap l_spqr p_spqr maxCt : Nat) : Nat :=
  max (w2CmkChainTightPeak maxOldCap)
    (w2CmkChainTightLive maxOldCap + max p_spqr (l_spqr + optLargeCost fineCostModel maxCt))

theorem w2TryDecryptTightLive_le_w2TryDecryptTightPeak
    (maxOldCap l_spqr p_spqr maxCt : Nat) :
    w2TryDecryptTightLive maxOldCap l_spqr maxCt ≤
      w2TryDecryptTightPeak maxOldCap l_spqr p_spqr maxCt := by
  unfold w2TryDecryptTightLive w2TryDecryptTightPeak
  have h1 : l_spqr + optLargeCost fineCostModel maxCt ≤
      max p_spqr (l_spqr + optLargeCost fineCostModel maxCt) :=
    Nat.le_max_right p_spqr _
  rw [Nat.add_assoc]
  exact Nat.le_trans (Nat.add_le_add_left h1 (w2CmkChainTightLive maxOldCap))
    (Nat.le_max_right (w2CmkChainTightPeak maxOldCap) _)

theorem w2TryDecrypt_fine_phaseCreditSpec_tight
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap c_spqr l_spqr p_spqr r_spqr maxCt : Nat}
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hSpqr : PhaseCreditSpec fineCostModel SpqrStepEnv c_spqr l_spqr p_spqr r_spqr)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps c_spqr)
      (w2TryDecryptTightLive maxOldCap l_spqr maxCt)
      (w2TryDecryptTightPeak maxOldCap l_spqr p_spqr maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap r_spqr maxCt) := by
  have h34 : 34 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hS1 : PhaseCreditSpec fineCostModel (BoundedNonFreeEvs 6 16 160) 58734 0 0 160 :=
    (phaseCreditSpec_boundedNonFree_fine_256 6 16 160 (by decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 160)
  have hS3 := w2Seg3DhCommit_fine_phaseCreditSpec_tight (dhCap := dhCap) (needGrow := needGrow) hDhSmall
  have hS4 := w2Seg4CmkStep_fine_phaseCreditSpec_tight hlen hchain
  have hS7 := w2Seg7Mac_fine_phaseCreditSpec_tight withAddr errAlloc
  have hS8 := phaseCreditSpec_aesDecCt_fine_tight hct
  have hS9 : PhaseCreditSpec fineCostModel (SeqEnv TrApplyBoundedEnv FreeOnlyEvs) 57642 0 0 34 :=
    (seq_freeOnly_right_zero_live fineCostModel_modelHyps
      (phaseCreditSpec_trApplyBounded fineCostModel_modelHyps h34)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 34)
  have h89 := seq_zero_right_eq_peak hS8 hS9
  have h79 := seq_zero_left hS7 h89
  have h59 := hSpqr.seq h79
  have h49 := hS4.seq h59
  have h39 := seq_zero_left hS3 h49
  have h19 := seq_zero_left hS1 h39
  unfold w2TryDecryptTightCum w2TryDecryptTightLive w2TryDecryptTightPeak w2TryDecryptMaxReq
  refine (or_freeOnly fineCostModel_modelHyps h19).mono ?_ ?_ (Nat.le_refl _) ?_
  · simp only [Nat.add_assoc]; exact Nat.le_refl _
  · simp only [Nat.add_assoc]; exact Nat.le_refl _
  · generalize max 416 (104 * (2 * dhCap)) = r3
    generalize max 416 (104 * (2 * maxOldCap)) = r4
    omega

theorem w2TryDecryptFail_fine_phaseCreditSpec_tight
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap c_spqr l_spqr p_spqr r_spqr maxCt : Nat}
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hSpqr : PhaseCreditSpec fineCostModel SpqrStepEnv c_spqr l_spqr p_spqr r_spqr)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps c_spqr)
      (w2CmkChainTightLive maxOldCap + l_spqr)
      (w2TryDecryptTightPeak maxOldCap l_spqr p_spqr maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap r_spqr maxCt) := by
  have hS1 : PhaseCreditSpec fineCostModel (BoundedNonFreeEvs 6 16 160) 58734 0 0 160 :=
    (phaseCreditSpec_boundedNonFree_fine_256 6 16 160 (by decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 160)
  have hS3 := w2Seg3DhCommit_fine_phaseCreditSpec_tight (dhCap := dhCap) (needGrow := needGrow) hDhSmall
  have hS4 := w2Seg4CmkStep_fine_phaseCreditSpec_tight hlen hchain
  have hS7 := w2Seg7Mac_fine_phaseCreditSpec_tight withAddr errAlloc
  have hS8 := seq_freeOnly_right_zero_live fineCostModel_modelHyps
    (phaseCreditSpec_aesDecCt_err_fine_tight hct)
  have h78 := seq_zero_left hS7 hS8
  have h58 := hSpqr.seq h78
  have h48 := hS4.seq h58
  have h38 := seq_zero_left hS3 h48
  have h18 := seq_zero_left hS1 h38
  have hcum_assoc : ∀ a b c d e f : Nat, a + (b + (c + (d + (e + f)))) = a + b + c + d + e + f :=
    fun _ _ _ _ _ _ => by simp only [Nat.add_assoc]
  unfold w2TryDecryptTightCum w2TryDecryptTightPeak w2TryDecryptMaxReq
  refine (or_freeOnly fineCostModel_modelHyps h18).mono ?_ ?_ (Nat.le_refl _) (Nat.le_refl _)
  · rw [hcum_assoc]; exact Nat.le_add_right _ _
  · simp only [Nat.add_zero]; exact Nat.le_refl _

/-! ### Concrete SPQR `recv` Instantiations -/

/-- Tight `W2TryDecryptEnv` `PhaseCreditSpec` on `fineCostModel` instantiated with SPQR `recv` under `KeyHistorySmallOrReserved xRk`.
-/
theorem w2TryDecrypt_spqrC07_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 294391 maxCt)
      (w2TryDecryptTightPeak maxOldCap 294391 294391 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 286196) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    hct

theorem w2TryDecrypt_spqrC07_c09a_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv 1647247 rRecv)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 294391 maxCt)
      (w2TryDecryptTightPeak maxOldCap 294391 294391 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 286196) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight_c09a F K C09a
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    hct

theorem w2TryDecryptFail_spqrC07_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2CmkChainTightLive maxOldCap + 294391)
      (w2TryDecryptTightPeak maxOldCap 294391 294391 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 286196) maxCt) :=
  w2TryDecryptFail_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    hct

/-- Unconditional-history SPQR `recv` instantiation of `W2TryDecryptEnv` on `fineCostModel`. -/
theorem w2TryDecrypt_spqrC07_uncondHist_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 302480) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)
    hct

/-! ### Sesame `TrialStep` and `TrialLoopEnv` Instantiations -/

theorem w2TrialHaltStep_dom_fine_phaseCreditSpec_tight
    {pqCap cTd lMut pTd rTd : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {TdFailEnv : List AllocEvent → Prop}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hTdFail : PhaseCreditSpec fineCostModel TdFailEnv cTd lMut pTd rTd) :
    PhaseCreditSpec fineCostModel
      (SeqEnv (SegCloneEnv G ses.state) TdFailEnv)
      (8277456 + cTd)
      (1080975 + optLargeCost fineCostModel pqCap + lMut)
      (1080975 + optLargeCost fineCostModel pqCap + max pTd lMut)
      (max (max 208000 pqCap) rTd) := by
  have hcl := sessionClone_dom_phaseCredit_tight hgv hdom
  set L := 1080975 + optLargeCost fineCostModel pqCap
  refine (hcl.seq hTdFail).mono (Nat.le_refl _) (Nat.le_refl _) ?_ (Nat.le_refl _)
  exact Nat.max_le.mpr
    ⟨Nat.le_add_right L _,
     Nat.add_le_add_left (Nat.le_max_left pTd lMut) L⟩

/-- Completed failed Sesame trial (`Clone ++ TdFail ++ DropClone`) on `fineCostModel`, restoring `Δlive = 0`.
-/
theorem w2FailedTrial_dom_fine_phaseCreditSpec_tight
    {pqCap cTd lMut pTd rTd : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {TdFailEnv DropCloneEnv : List AllocEvent → Prop}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hTdFail : PhaseCreditSpec fineCostModel TdFailEnv cTd lMut pTd rTd)
    (hDrop : DeallocCreditSpec fineCostModel DropCloneEnv
      (segCloneLarge fineCostModel G ses.state + lMut)) :
    PhaseCreditSpec fineCostModel
      (ConcatEnv (ConcatEnv (SegCloneEnv G ses.state) TdFailEnv) DropCloneEnv)
      (8277456 + cTd)
      0
      (1080975 + optLargeCost fineCostModel pqCap + pTd)
      (max (max 208000 pqCap) rTd) := by
  have hCloneExact := sessionClone_phaseCredit_tight fineCostModel_modelHyps G ses.state
  have hDone := phaseCreditSpec_failedTrial_done hCloneExact hTdFail hDrop
  have hc := segCloneTightCum_fine_le_of_dom hgv hdom
  have hl := segCloneLarge_fine_le_of_dom hgv hdom
  have hr := segCloneMaxReq_le_of_dom hgv hdom
  exact hDone.mono
    (Nat.add_le_add_right hc cTd)
    (Nat.le_refl 0)
    (Nat.max_le.mpr
      ⟨Nat.le_trans hl (Nat.le_add_right _ pTd),
       Nat.add_le_add_right hl pTd⟩)
    (max_le_max_nat hr (Nat.le_refl rTd))

theorem w2FailedTrial_dropClone_dom_fine_phaseCreditSpec_tight
    {pqCap cTd pTd rTd : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {TdFailEnv : List AllocEvent → Prop}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hTdFail : PhaseCreditSpec fineCostModel TdFailEnv cTd 0 pTd rTd) :
    PhaseCreditSpec fineCostModel
      (ConcatEnv (ConcatEnv (SegCloneEnv G ses.state) TdFailEnv)
        (· = dropClonedSessionEvents G ses.state))
      (8277456 + cTd)
      0
      (1080975 + optLargeCost fineCostModel pqCap + pTd)
      (max (max 208000 pqCap) rTd) := by
  have hd : DeallocCreditSpec fineCostModel
      (· = dropClonedSessionEvents G ses.state)
      (segCloneLarge fineCostModel G ses.state + 0) := by
    simpa [Nat.add_zero] using
      SessionCloneCredit.DeallocCreditSpec.dropClonedSession fineCostModel G ses.state
  exact w2FailedTrial_dom_fine_phaseCreditSpec_tight hgv hdom hTdFail hd

/-- `≤ n`-session `TrialLoopEnv` instantiation on `fineCostModel`, preserving `1×` session peak. -/
theorem w2TrialLoop_dom_fine_phaseCreditSpec_tight {α : Type}
    {GOf : α → SessionGhost} {sesOf : α → Session (List (BitVec 8))}
    {TdFailOf DropCloneOf : α → List AllocEvent → Prop}
    {FinalEnv : List AllocEvent → Prop}
    {n pqCap cTd lMut pTd rTd cFinal lFinal pFinal rFinal : Nat}
    (xs : List α) (hlen : xs.length + 1 ≤ n)
    (hgv : ∀ x ∈ xs, SessionGhostValid (GOf x) (sesOf x))
    (hdom : ∀ x ∈ xs, SessionCloneDom pqCap (sesOf x))
    (hTdFail : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (TdFailOf x) cTd lMut pTd rTd)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec fineCostModel (DropCloneOf x)
      (segCloneLarge fineCostModel (GOf x) (sesOf x).state + lMut))
    (hFinal : PhaseCreditSpec fineCostModel FinalEnv cFinal lFinal pFinal rFinal) :
    let cFail := 8277456 + cTd
    let lHalt := 1080975 + optLargeCost fineCostModel pqCap + lMut
    let pFail := 1080975 + optLargeCost fineCostModel pqCap + max pTd lMut
    let rFail := max (max 208000 pqCap) rTd
    PhaseCreditSpec fineCostModel
      (TrialLoopEnv
        (fun x => SeqEnv (SegCloneEnv (GOf x) (sesOf x).state) (TdFailOf x))
        (fun x => ConcatEnv (ConcatEnv (SegCloneEnv (GOf x) (sesOf x).state) (TdFailOf x))
          (DropCloneOf x))
        FinalEnv xs)
      ((n - 1) * cFail + cFinal)
      (max lHalt lFinal)
      (max pFail pFinal)
      (max rFail rFinal) := by
  intro cFail lHalt pFail rFail
  exact phaseCreditSpec_trialLoop xs hlen
    (fun x hx => w2TrialHaltStep_dom_fine_phaseCreditSpec_tight
      (hgv x hx) (hdom x hx) (hTdFail x hx))
    (fun x hx =>
      (w2FailedTrial_dom_fine_phaseCreditSpec_tight
        (hgv x hx) (hdom x hx) (hTdFail x hx) (hDrop x hx)).mono
        (Nat.le_refl _) (Nat.le_refl 0)
        (Nat.add_le_add_left (Nat.le_max_left pTd lMut) _)
        (Nat.le_refl _))
    hFinal

/-! ### `PhaseGroupSpec fineCostModel` Bounds -/

private theorem nonFreeCount_eq_filter_isNonFreeEv :
    ∀ evs : List AllocEvent, nonFreeCount evs = (evs.filter isNonFreeEv).length
  | [] => rfl
  | .free _ _ :: tl => nonFreeCount_eq_filter_isNonFreeEv tl
  | .alloc _ :: tl => by
    have ih := nonFreeCount_eq_filter_isNonFreeEv tl
    change _ = (tl.filter isNonFreeEv).length + 1
    dsimp only [nonFreeCount]
    omega
  | .aligned _ _ :: tl => by
    have ih := nonFreeCount_eq_filter_isNonFreeEv tl
    change _ = (tl.filter isNonFreeEv).length + 1
    dsimp only [nonFreeCount]
    omega
  | .realloc _ _ _ :: tl => by
    have ih := nonFreeCount_eq_filter_isNonFreeEv tl
    change _ = (tl.filter isNonFreeEv).length + 1
    dsimp only [nonFreeCount]
    omega

theorem nonFreeBound_boundedNonFreeEvs (k maxLen maxReq : Nat) :
    NonFreeBound (BoundedNonFreeEvs k maxLen maxReq) k := by
  intro evs h
  rw [nonFreeCount_eq_filter_isNonFreeEv]
  exact h.2.1

theorem phaseGroupSpec_boundedNonFree_any (M : AllocCostModel) [HasFineGroupCredit M]
    (k maxLen maxReq : Nat) :
    PhaseGroupSpec M (BoundedNonFreeEvs k maxLen maxReq) (3 * FineScale * k) :=
  PhaseGroupSpec.of_nonFreeBound M (nonFreeBound_boundedNonFreeEvs k maxLen maxReq)

private theorem step_groupsScaled_fine_le_44 {ev : AllocEvent} {maxReq : Nat}
    (st : fineCostModel.σ) (h44 : maxReq ≤ 44)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    HasFineGroupCredit.groupsScaled (fineCostModel.step ev st) ≤
      HasFineGroupCredit.groupsScaled st + (if isNonFreeEv ev then FineScale else 0) := by
  cases ev with
  | free al sz =>
    simp only [isNonFreeEv, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact HasFineGroupCredit.step_free_le (M := fineCostModel) al sz st
  | alloc req =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq] at hreq ⊢
    have hr44 : req ≤ 44 := Nat.le_trans hreq h44
    have hm : req ≤ MmapThresholdReq := Nat.le_trans hr44 (by decide)
    have hs := HasFineGroupCredit.step_alloc_small_le (M := fineCostModel) st hm
    rw [smallAllocGroupS_fineCostModel_eq] at hs
    have h16 := Nat.le_trans (smallAllocGroupS_le_16659_of_le_44 hr44)
      (by decide : 16659 ≤ FineScale)
    exact Nat.le_trans hs (Nat.add_le_add_left h16 _)
  | aligned al req =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq, eventStepAlign] at hreq hal ⊢
    have hr44 : req ≤ 44 := Nat.le_trans hreq h44
    have hm : req ≤ MmapThresholdReq := Nat.le_trans hr44 (by decide)
    have hs := HasFineGroupCredit.step_aligned_small_le (M := fineCostModel) st hal hm
    rw [smallAllocGroupS_fineCostModel_eq] at hs
    have h16 := Nat.le_trans (smallAllocGroupS_le_16659_of_le_44 hr44)
      (by decide : 16659 ≤ FineScale)
    exact Nat.le_trans hs (Nat.add_le_add_left h16 _)
  | realloc al old newSz =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq, eventStepAlign] at hreq hal ⊢
    have hr44 : newSz ≤ 44 := Nat.le_trans hreq h44
    have hm : newSz ≤ MmapThresholdReq := Nat.le_trans hr44 (by decide)
    have hs := HasFineGroupCredit.step_realloc_small_le (M := fineCostModel) (old := old) st hal hm
    rw [smallReallocGroupS_fineCostModel_eq] at hs
    unfold fineSmallReallocGroupS at hs
    have h16 : max (fineSmallAllocGroupS newSz) FineScale ≤ FineScale :=
      Nat.max_le.mpr
        ⟨Nat.le_trans (smallAllocGroupS_le_16659_of_le_44 hr44) (by decide),
         Nat.le_refl FineScale⟩
    exact Nat.le_trans hs (Nat.add_le_add_left h16 _)

private theorem stepEvents_groupsScaled_fine_44 {maxReq : Nat} (h44 : maxReq ≤ 44) :
    ∀ (evs : List AllocEvent) (st : fineCostModel.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineGroupCredit.groupsScaled (fineCostModel.stepEvents evs st) ≤
        HasFineGroupCredit.groupsScaled st + (evs.filter isNonFreeEv).length * FineScale
  | [], st, _ => by simp
  | ev :: rest, st, hall => by
    obtain ⟨hreq, hal⟩ := hall ev List.mem_cons_self
    have h1 := step_groupsScaled_fine_le_44 st h44 hreq hal
    have h2 := stepEvents_groupsScaled_fine_44 h44 rest (fineCostModel.step ev st)
      (fun e he => hall e (List.mem_cons_of_mem ev he))
    simp only [AllocCostModel.stepEvents_cons, List.filter_cons]
    cases hnf : isNonFreeEv ev
    · simp only [hnf, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1 ⊢
      exact Nat.le_trans h2 (Nat.add_le_add_right h1 _)
    · simp only [hnf, ↓reduceIte, List.length_cons] at h1 ⊢
      have hmul : ((rest.filter isNonFreeEv).length + 1) * FineScale =
          FineScale + (rest.filter isNonFreeEv).length * FineScale := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hmul, ← Nat.add_assoc]
      exact Nat.le_trans h2 (Nat.add_le_add_right h1 _)

/-- `PhaseGroupSpec fineCostModel` for `BoundedNonFreeEvs k maxLen maxReq` (`maxReq ≤ 44`, `ΔgrpS = k * FineScale`).
-/
theorem phaseGroupSpec_boundedNonFree_fine_44 (k maxLen maxReq : Nat) (h44 : maxReq ≤ 44) :
    PhaseGroupSpec fineCostModel (BoundedNonFreeEvs k maxLen maxReq) (k * FineScale) where
  groups_le st0 {evs} h := by
    have h1 := stepEvents_groupsScaled_fine_44 h44 evs st0 h.2.2
    have hmul : (evs.filter isNonFreeEv).length * FineScale ≤ k * FineScale :=
      Nat.mul_le_mul_right FineScale h.2.1
    exact Nat.le_trans h1 (Nat.add_le_add_left hmul _)

private theorem nonFreeCount_growOne104Evs (c : Nat) :
    nonFreeCount (growOne104Evs c) = 1 := by
  unfold growOne104Evs
  split
  · rw [nonFreeCount_rustAllocEvents]
  · rw [nonFreeCount_rustReallocEvents]

private theorem nonFreeCount_doublingChain104Evs :
    ∀ caps : List Nat, nonFreeCount (doublingChain104Evs caps) = caps.length
  | [] => rfl
  | c :: rest => by
    simp only [doublingChain104Evs, GroupCreditKit.nonFreeCount_append,
      nonFreeCount_growOne104Evs, nonFreeCount_doublingChain104Evs rest,
      List.length_cons, Nat.add_comm]

theorem w2Seg3DhCommit_fine_phaseGroupSpec (dhCap : Nat) (needGrow : Bool) :
    PhaseGroupSpec fineCostModel (W2Seg3DhCommitEnv dhCap needGrow) 786432 := by
  have h12 : NonFreeBound (· = dhCommitStep12Evs) 3 := by
    rintro _ rfl
    unfold dhCommitStep12Evs
    simp [GroupCreditKit.nonFreeCount_append, nonFreeCount_rustAllocEvents]
  have h3 : NonFreeBound (· = dhCommitStep3Evs dhCap needGrow) 1 := by
    rintro _ rfl
    unfold dhCommitStep3Evs
    rw [GroupCreditKit.nonFreeCount_append, GroupCreditKit.nonFreeCount_rustDeallocEvents]
    cases needGrow
    · simp [nonFreeCount]
    · simp [nonFreeCount_growOne104Evs]
  have hnf : NonFreeBound (W2Seg3DhCommitEnv dhCap needGrow) (max 0 (3 + (1 + 0))) :=
    NonFreeBound.freeOnly.or (h12.seq (h3.seq NonFreeBound.freeOnly))
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)

theorem w2Seg4CmkStep_fine_phaseGroupSpec {caps : List Nat} {maxSteps : Nat}
    (hlen : caps.length ≤ maxSteps) :
    PhaseGroupSpec fineCostModel (W2Seg4CmkStepEnv caps)
      (131072000 + maxSteps * 196608) := by
  have hSeeds : PhaseGroupSpec fineCostModel (BoundedNonFreeEvs 2000 4000 33) 131072000 :=
    (phaseGroupSpec_boundedNonFree_fine_44 2000 4000 33 (by decide)).mono (by decide)
  have hGrowNf : NonFreeBound (· = doublingChain104Evs caps) maxSteps := by
    rintro _ rfl
    rw [nonFreeCount_doublingChain104Evs]
    exact hlen
  have hGrow : PhaseGroupSpec fineCostModel (· = doublingChain104Evs caps) (maxSteps * 196608) :=
    (PhaseGroupSpec.of_nonFreeBound fineCostModel hGrowNf).mono
      (Nat.le_of_eq (by rw [show 3 * FineScale = 196608 by decide, Nat.mul_comm]))
  have hGrowFree := (hGrow.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or (hSeeds.seq hGrowFree)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-- `PhaseGroupSpec fineCostModel` for `cmkJumpListEvs 0 jumps` (`jumps.length ≤ 2000`, `cmkJumpFinalIdx 0 jumps ≤ 10`).
-/
theorem cmkJumpList_fine_phaseGroupSpec (jumps : List (Bool × Bool))
    (hlen : jumps.length ≤ 2000)
    (hkf : cmkJumpFinalIdx 0 jumps ≤ 10) :
    PhaseGroupSpec fineCostModel (· = cmkJumpListEvs 0 jumps) 35284080 := by
  suffices hrec : ∀ (js : List (Bool × Bool)) (k : Nat),
      PhaseGroupSpec fineCostModel (· = cmkJumpListEvs k js)
        (js.length * 16659 + (cmkJumpFinalIdx k js - k) * 196608) by
    have h0 := hrec jumps 0
    simp only [Nat.sub_zero] at h0
    exact h0.mono
      (Nat.le_trans
        (Nat.add_le_add (Nat.mul_le_mul_right 16659 hlen) (Nat.mul_le_mul_right 196608 hkf))
        (by decide))
  intro js
  induction js with
  | nil =>
    intro k
    simpa [cmkJumpListEvs, cmkJumpFinalIdx] using PhaseGroupSpec.nil fineCostModel
  | cons hd tl ih =>
    rcases hd with ⟨needGrow, needEvictFree⟩
    intro k
    have ha33 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 33 1) 16659 := by
      refine (PhaseGroupSpec.rustAlloc_small fineCostModel
        (size := 33) (align := 1) (by decide) (by decide)).mono ?_
      rw [smallAllocGroupS_fineCostModel_eq]
      exact smallAllocGroupS_le_16659_of_le_44 (by decide)
    have hgr : PhaseGroupSpec fineCostModel
        (· = if needGrow then growOne104Evs (W2DecryptCmkDhPeak.v104CapSeq k) else [])
        (if needGrow then 196608 else 0) := by
      cases needGrow
      · exact PhaseGroupSpec.nil fineCostModel
      · have hnf : NonFreeBound (· = growOne104Evs (W2DecryptCmkDhPeak.v104CapSeq k)) 1 := by
          rintro _ rfl; rw [nonFreeCount_growOne104Evs]
        exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)
    have hev : PhaseGroupSpec fineCostModel
        (· = if needEvictFree then rustDeallocEvents 33 1 else []) 0 := by
      cases needEvictFree
      · exact PhaseGroupSpec.nil fineCostModel
      · exact PhaseGroupSpec.rustDealloc fineCostModel 33 1
    have htl := ih (if needGrow then k + 1 else k)
    have hcat := ((ha33.concat hgr).concat hev).concat htl
    have hcat' : PhaseGroupSpec fineCostModel (· = cmkJumpListEvs k ((needGrow, needEvictFree) :: tl))
        (((16659 + if needGrow then 196608 else 0) + 0) +
          (tl.length * 16659 +
            (cmkJumpFinalIdx (if needGrow then k + 1 else k) tl -
              (if needGrow then k + 1 else k)) * 196608)) :=
      hcat.of_imp fun _ h => by
        subst h
        exact ConcatEnv.append (ConcatEnv.append (ConcatEnv.append rfl rfl) rfl) rfl
    have hle_idx : ∀ (ys : List (Bool × Bool)) (m : Nat), m ≤ cmkJumpFinalIdx m ys := by
      intro ys
      induction ys with
      | nil => intro m; exact Nat.le_refl m
      | cons y r ihr =>
        intro m
        simp only [cmkJumpFinalIdx]
        cases y.1
        · simpa using ihr m
        · exact Nat.le_trans (Nat.le_succ m) (ihr (m + 1))
    refine hcat'.mono ?_
    simp only [List.length_cons, cmkJumpFinalIdx, Nat.add_zero]
    cases needGrow
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [Nat.add_mul, Nat.one_mul]
      generalize cmkJumpFinalIdx k tl - k = d
      generalize tl.length = L
      omega
    · simp only [↓reduceIte]
      have hk1 := hle_idx tl (k + 1)
      have hsub : cmkJumpFinalIdx (k + 1) tl - k =
          (cmkJumpFinalIdx (k + 1) tl - (k + 1)) + 1 := by omega
      rw [hsub, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
      generalize cmkJumpFinalIdx (k + 1) tl - (k + 1) = d
      generalize tl.length = L
      omega

theorem w2Seg7Mac_fine_phaseGroupSpec (withAddr errAlloc : Bool) :
    PhaseGroupSpec fineCostModel (W2Seg7MacEnv withAddr errAlloc) 786432 := by
  have hnf7 : NonFreeBound (· = s7CoreEvs withAddr errAlloc) 4 := by
    rintro _ rfl
    unfold s7CoreEvs W2DecryptTrialPeak.vmacEvs W2DecryptTrialPeak.computeMacEvs
    cases withAddr <;> cases errAlloc <;>
      simp [GroupCreditKit.nonFreeCount_append, nonFreeCount_rustAllocEvents,
        GroupCreditKit.nonFreeCount_rustDeallocEvents]
  have hnf : NonFreeBound (W2Seg7MacEnv withAddr errAlloc) (max 0 (4 + 0)) :=
    NonFreeBound.freeOnly.or (hnf7.seq NonFreeBound.freeOnly)
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)

theorem w2TryDecrypt_fine_phaseGroupSpec
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps g_spqr : Nat}
    (hlen : caps.length ≤ maxSteps)
    (hSpqr : PhaseGroupSpec fineCostModel SpqrStepEnv g_spqr) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (134791168 + maxSteps * 196608 + g_spqr) := by
  have hS1 : PhaseGroupSpec fineCostModel (BoundedNonFreeEvs 6 16 160) 1179648 :=
    (phaseGroupSpec_boundedNonFree_any fineCostModel 6 16 160).mono (by decide)
  have hS3 := w2Seg3DhCommit_fine_phaseGroupSpec dhCap needGrow
  have hS4 := w2Seg4CmkStep_fine_phaseGroupSpec hlen
  have hS7 := w2Seg7Mac_fine_phaseGroupSpec withAddr errAlloc
  have hS8 : PhaseGroupSpec fineCostModel (AesDecCtShape ctLen) 196608 := by
    have hnf : NonFreeBound (AesDecCtShape ctLen) 1 := by
      rintro evs (rfl | rfl | rfl)
      · exact Nat.zero_le 1
      · rw [nonFreeCount_rustAllocEvents]
      · rw [GroupCreditKit.nonFreeCount_append, nonFreeCount_rustAllocEvents,
            GroupCreditKit.nonFreeCount_rustDeallocEvents]
    exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)
  have hS9 : PhaseGroupSpec fineCostModel (SeqEnv TrApplyBoundedEnv FreeOnlyEvs) 393216 := by
    have hb : PhaseGroupSpec fineCostModel (BoundedLenEvs 6 34) 393216 :=
      ((phaseGroupSpec_boundedNonFree_fine_44 6 6 34 (by decide)).of_imp
        fun _ => BoundedLenEvs.toBoundedNonFreeEvs).mono (by decide)
    have htr : PhaseGroupSpec fineCostModel TrApplyBoundedEnv 393216 :=
      ((PhaseGroupSpec.freeOnly fineCostModel).seq
        (hb.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono
        (by simp)
    exact (htr.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by simp)
  have hchain := hS1.seq (hS3.seq (hS4.seq (hSpqr.seq (hS7.seq (hS8.seq hS9)))))
  refine ((PhaseGroupSpec.freeOnly fineCostModel).or hchain).mono ?_
  refine Nat.max_le.mpr ⟨Nat.zero_le _, ?_⟩
  generalize maxSteps * 196608 = ms
  have hsum : 1179648 + (786432 + ((131072000 + ms) + (g_spqr + (786432 + (196608 + 393216))))) =
      (1179648 + 786432 + 131072000 + 786432 + 196608 + 393216) + ms + g_spqr := by
    omega
  rw [hsum, show 1179648 + 786432 + 131072000 + 786432 + 196608 + 393216 = 134414336 by decide]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (by decide : 134414336 ≤ 134791168) ms) g_spqr

theorem w2TryDecryptFail_fine_phaseGroupSpec
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps g_spqr : Nat}
    (hlen : caps.length ≤ maxSteps)
    (hSpqr : PhaseGroupSpec fineCostModel SpqrStepEnv g_spqr) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptFailEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (134791168 + maxSteps * 196608 + g_spqr) := by
  have hS1 : PhaseGroupSpec fineCostModel (BoundedNonFreeEvs 6 16 160) 1179648 :=
    (phaseGroupSpec_boundedNonFree_any fineCostModel 6 16 160).mono (by decide)
  have hS3 := w2Seg3DhCommit_fine_phaseGroupSpec dhCap needGrow
  have hS4 := w2Seg4CmkStep_fine_phaseGroupSpec hlen
  have hS7 := w2Seg7Mac_fine_phaseGroupSpec withAddr errAlloc
  have hS8 : PhaseGroupSpec fineCostModel (SeqEnv (W2AesDecErrEnv ctLen) FreeOnlyEvs) 196608 := by
    have hnf : NonFreeBound (W2AesDecErrEnv ctLen) 1 := by
      rintro evs (rfl | rfl)
      · exact Nat.zero_le 1
      · rw [GroupCreditKit.nonFreeCount_append, nonFreeCount_rustAllocEvents,
            GroupCreditKit.nonFreeCount_rustDeallocEvents]
    exact ((PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).seq
      (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)
  have hchain := hS1.seq (hS3.seq (hS4.seq (hSpqr.seq (hS7.seq hS8))))
  refine ((PhaseGroupSpec.freeOnly fineCostModel).or hchain).mono ?_
  refine Nat.max_le.mpr ⟨Nat.zero_le _, ?_⟩
  generalize maxSteps * 196608 = ms
  have hsum : 1179648 + (786432 + ((131072000 + ms) + (g_spqr + (786432 + 196608)))) =
      (1179648 + 786432 + 131072000 + 786432 + 196608) + ms + g_spqr := by
    omega
  rw [hsum, show 1179648 + 786432 + 131072000 + 786432 + 196608 = 134021120 by decide]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (by decide : 134021120 ≤ 134791168) ms) g_spqr

theorem w2TryDecrypt_spqrC07_fine_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {gRecvS : Nat}
    (C09aG : StatesRecvTightGroupSpec F StatesRecvEnv gRecvS)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hlen : caps.length ≤ maxSteps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (591484720 + maxSteps * 196608 + gRecvS) := by
  refine (w2TryDecrypt_fine_phaseGroupSpec hlen
    (spqrRecvParts_c07_phaseGroupSpec_tight F K C09aG
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)).mono ?_
  generalize maxSteps * 196608 = ms
  have hsum : 134791168 + ms + (456693552 + gRecvS) =
      (134791168 + 456693552) + ms + gRecvS := by omega
  rw [hsum, show 134791168 + 456693552 = 591484720 by decide]

theorem phaseGroupSpec_trialLoop {α : Type} {M : AllocCostModel} [HasFineGroupCredit M]
    {HaltStep DoneStep : α → List AllocEvent → Prop}
    {FinalEnv : List AllocEvent → Prop}
    {n gFail gFinal : Nat}
    (xs : List α) (hlen : xs.length + 1 ≤ n)
    (hHalt : ∀ x ∈ xs, PhaseGroupSpec M (HaltStep x) gFail)
    (hDone : ∀ x ∈ xs, PhaseGroupSpec M (DoneStep x) gFail)
    (hFinal : PhaseGroupSpec M FinalEnv gFinal) :
    PhaseGroupSpec M (TrialLoopEnv HaltStep DoneStep FinalEnv xs)
      ((n - 1) * gFail + gFinal) := by
  suffices hrec : ∀ ys : List α,
      (∀ x ∈ ys, PhaseGroupSpec M (HaltStep x) gFail) →
      (∀ x ∈ ys, PhaseGroupSpec M (DoneStep x) gFail) →
      PhaseGroupSpec M (TrialLoopEnv HaltStep DoneStep FinalEnv ys)
        (ys.length * gFail + gFinal) by
    have h0 := hrec xs hHalt hDone
    have hmul : xs.length * gFail ≤ (n - 1) * gFail :=
      Nat.mul_le_mul_right gFail (by omega)
    exact h0.mono (Nat.add_le_add_right hmul gFinal)
  intro ys hH hD
  induction ys with
  | nil =>
    simp only [TrialLoopEnv, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact hFinal
  | cons y rest ih =>
    have hyH := hH y List.mem_cons_self
    have hyD := hD y List.mem_cons_self
    have hrest := ih
      (fun z hz => hH z (List.mem_cons_of_mem y hz))
      (fun z hz => hD z (List.mem_cons_of_mem y hz))
    refine ((hyH.or (hyD.concat hrest)).of_imp (fun _ h => h)).mono ?_
    rw [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm (rest.length * gFail) gFail,
        Nat.add_assoc]
    exact Nat.max_le.mpr ⟨Nat.le_add_right gFail _, Nat.le_refl _⟩

theorem w2TrialHaltStep_dom_fine_phaseGroupSpec {pqCap gTd : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {TdFailEnv : List AllocEvent → Prop}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hTdFail : PhaseGroupSpec fineCostModel TdFailEnv gTd) :
    PhaseGroupSpec fineCostModel
      (SeqEnv (SegCloneEnv G ses.state) TdFailEnv)
      (172881456 + gTd) :=
  (sessionClone_dom_phaseGroup hgv hdom).seq hTdFail

theorem w2FailedTrial_dom_fine_phaseGroupSpec {pqCap gTd : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {TdFailEnv DropCloneEnv : List AllocEvent → Prop}
    (hgv : SessionGhostValid G ses)
    (hdom : SessionCloneDom pqCap ses)
    (hTdFail : PhaseGroupSpec fineCostModel TdFailEnv gTd)
    (hDrop : PhaseGroupSpec fineCostModel DropCloneEnv 0) :
    PhaseGroupSpec fineCostModel
      (ConcatEnv (ConcatEnv (SegCloneEnv G ses.state) TdFailEnv) DropCloneEnv)
      (172881456 + gTd) :=
  (((sessionClone_dom_phaseGroup hgv hdom).concat hTdFail).concat hDrop).mono
    (Nat.le_of_eq (Nat.add_zero _))

end TightFineTryDecrypt

end LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
