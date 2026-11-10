/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.Support.Phi
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields

/-!
# Scratch-Cancellation Credit and Group Bounds for `SessionRecord::deserialize`

Proves closed `fineCostModel` `PhaseGroupSpec` (`344,462,092` scaled groups, `5,257` groups) and
`PhaseCreditSpec` (`(cum, live, peak, maxReq) = (16,890,453, 3,211,282, 5,316,629, 2,097,152)` at
wire length `≤ 2 MiB`) directly on `sessDeserEvents` (including `bytesVtableDrop` `.free` scratch
deallocations), non-vacuity witnesses, and `[LibsignalPlacement]` block-`46` bridges for
`SpecsPlacedBudget.sessDeserializeSpecPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  IdentityKey PublicKey ReceiverChain SenderChain SessionState maxMessageKeys
)
open CryptoGames.LibsignalSessionApi (PendingKyberPreKey PendingPreKey Session SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E.Bin (aliceIdKey bobIdKey)
open CryptoVerification.E2E.Record (encodeRecord recDeserializeStack sessionRecordAt)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainField ChainG DeserializeGenGhost GenField chainGAfter genFields recvChainG senderChainG
)
open CryptoVerification.E2E.Record.L1GX (GenFieldX genFieldsX pendingFieldX)
open CryptoVerification.E2E.Record.Placed (blkPl_46 lsProg_46)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (
  GenFieldQ clearPqSession genFieldsQ recFieldsQ recFieldsQ_ok
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Heap.Fine (FineScale MmapThresholdReq fineCostModel fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds (
  fineCostModel_smallMaxReq_eq fineVec104CumOfCap fineVec104CumOfCap_4
  fineVec104CumOfCap_pow2_ge_8 fineVec104CumOfCap_two_mul fineVec104StepCumCost
  smallReallocCost_832
)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (
  HasFineGroupCredit NonFreeBound PhaseGroupSpec
  fineSmallAllocGroupS fitsEnv_fineCostModel_of_phaseCredit_groups
  nonFreeCount nonFreeCount_append nonFreeCount_rustAllocEvents nonFreeCount_rustDeallocEvents
  smallAllocGroupS_fineCostModel_eq smallAllocGroupS_le_16659_of_le_44
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (
  bytesFreshSmallCost chainFieldStepEvents chainMergeEvents chainRemEvents
  chainRemEvents_eq_cons chainRemEvents_ge chainRemEvents_zero
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineInst (
  sessDeserLargeLive_fine_le_of_encode_le_2MiB sessDeserPeakLarge_fine_le_of_encode_le_2MiB
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (AllocContractsBudgetPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  basicFieldByteLen mergeFieldQEvents nextCapRecv
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  IsPow2Cap4 le_vecCap4Of vec104CumOfCap vec104GrowEvents vec104StepCumCost
  vecCap4Of vecCap4Of_pow2
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  bytesDropEvents bytesMergeAllocEvents bytesMergeEvents doReserveEvents_zero
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget (
  fieldsEventsAux nextCapRecv_eq_vecCap4Of recvCount recvCount_append
  sessDeserEvents sessDeserLargeLive sessDeserPeakLarge sessDeserSmallCost
  sessDeserializeBudgetPlacedSpec sessDeserializeBudgetRawSpec
  sessDeserialize_budget_placed_ok stepEvents_sessDeserEvents_bounds
)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (
  RecordDeserializeCancelEnv SessDeserializeCancelEnv
  chainHdrFields chainHdrFields_no_key chain_fields_eq_hdr_append_keys
  chainGAfter_keys_length_at_key deserCancelFineCumExpr deserRecvChainFineCum
  deserSenderChainFineCum filter_lt_length_mono filter_lt_succ_of_mem
  getElem_length_add getElem_prefix_of_lt growPoints2000 growPoints5
  isPow2Cap4_lt_2000 isPow2Cap4_lt_5 nil_mem_recordDeserializeCancelEnv
  recvCount_recFieldsQ_le_five recv_keys_le_2000_of_mem_recFieldsQ
  sessDeserEvents_mem_recordDeserializeCancelEnv sessDeserEvents_mem_sessDeserializeCancelEnv
  sessDeserEvents_req_align sessDeserEvents_req_align_2MiB
  sessDeserSmallCost_fine_le_expr sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv
  sum_map_le_const_mul
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (sessDeserializeSpecPlaced)

export LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (
  SessDeserializeCancelEnv RecordDeserializeCancelEnv
  sessDeserEvents_mem_sessDeserializeCancelEnv
  sessDeserEvents_mem_recordDeserializeCancelEnv
  nil_mem_recordDeserializeCancelEnv
  sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv
)

/-! ## 1. Closed `fineCostModel` Constants & Exact Reduction Lemmas -/

/-- Closed `fineCostModel` `cumSmall` bound for `SessionRecord::deserialize` on
`DeserializeScopeP_Q NonEmptyV1Q` (`16,890,453` B). -/
def deserCancelFineCum : Nat := 16890453

/-- Closed `fineCostModel` post-deserialize `sc = 63` `liveLarge` bound at `≤ 2 MiB` wire slice
(`3,211,282` B). -/
def deserCancelFineLive : Nat := 3211282

/-- Closed `fineCostModel` transient `sc = 63` `peakLarge` bound at `≤ 2 MiB` wire slice
(`5,316,629` B). -/
def deserCancelFinePeak : Nat := 5316629

/-- Closed per-step allocation request cap at `≤ 2 MiB` wire slice (`2,097,152` B). -/
def deserCancelFineMaxReq : Nat := 2097152

/-- Closed `FineScale`-scaled `groupsScaled` bound for `SessionRecord::deserialize` on
`DeserializeScopeP_Q NonEmptyV1Q` (`344,462,092`, i.e., `5,257` groups). -/
def deserCancelFineGrpS : Nat := 344462092

/-- Ceiling group count `(deserCancelFineGrpS + FineScale - 1) / FineScale` (`5,257` groups). -/
def deserCancelFineGroups : Nat :=
  (deserCancelFineGrpS + FineScale - 1) / FineScale

theorem deserCancelFineGroups_eq : deserCancelFineGroups = 5257 := by decide

private theorem vec104StepCumCost_eq_fine (M : AllocCostModel) [HasFineReallocCredit M]
    (cap : Nat) :
    vec104StepCumCost M cap = fineVec104StepCumCost M cap := rfl

theorem vec104CumOfCap_eq_fineVec104CumOfCap (M : AllocCostModel) [HasFineReallocCredit M] :
    ∀ cap : Nat, vec104CumOfCap M cap = fineVec104CumOfCap M cap := by
  intro cap
  refine Nat.strongRecOn cap fun n ih => ?_
  rw [vec104CumOfCap, fineVec104CumOfCap]
  split_ifs with h4 h8
  · rfl
  · rfl
  · rw [ih (n / 2) (by omega), vec104StepCumCost_eq_fine]

theorem vec104CumOfCap_fine_8_eq : vec104CumOfCap fineCostModel 8 = 14640 := by
  rw [vec104CumOfCap_eq_fineVec104CumOfCap, show (8 : Nat) = 2 * 4 from rfl,
    fineVec104CumOfCap_two_mul _ (by decide), fineVec104CumOfCap_4]
  have hstep : fineVec104StepCumCost fineCostModel 4 =
      HasFineReallocCredit.smallReallocCost fineCostModel 832 := by
    unfold fineVec104StepCumCost
    simp only [show (4 : Nat) ≠ 0 by decide, fineCostModel_smallMaxReq_eq,
      show 2 * 4 * 104 ≤ 135167 by decide, ↓reduceIte]
  rw [hstep, smallReallocCost_832]

theorem vec104CumOfCap_fine_2048_eq : vec104CumOfCap fineCostModel 2048 = 304783 := by
  rw [vec104CumOfCap_eq_fineVec104CumOfCap, show (2048 : Nat) = 4 * 2 ^ 9 from rfl,
    fineVec104CumOfCap_pow2_ge_8 (by decide)]

private def deserAllocPointPairs : List (Nat × Nat) :=
  [(32, 738), (33, 738), (1569, 2792)]

private def checkDeserAllocPoints : Bool :=
  deserAllocPointPairs.all fun (req, expected) =>
    fineSmallAllocCost req == expected

private theorem checkDeserAllocPoints_true : checkDeserAllocPoints = true := by
  decide +kernel

private theorem extractDeserAllocPoint {req expected : Nat}
    (hmem : (req, expected) ∈ deserAllocPointPairs) :
    HasFineReallocCredit.smallAllocCost fineCostModel req = expected := by
  change fineSmallAllocCost req = expected
  have hcell := List.all_eq_true.mp checkDeserAllocPoints_true (req, expected) hmem
  exact of_decide_eq_true hcell

theorem smallAllocCost_32_eq :
    HasFineReallocCredit.smallAllocCost fineCostModel 32 = 738 :=
  extractDeserAllocPoint (by decide)

theorem smallAllocCost_33_eq :
    HasFineReallocCredit.smallAllocCost fineCostModel 33 = 738 :=
  extractDeserAllocPoint (by decide)

theorem smallAllocCost_1569_eq :
    HasFineReallocCredit.smallAllocCost fineCostModel 1569 = 2792 :=
  extractDeserAllocPoint (by decide)

private theorem bytesFreshSmallCost_32_eq :
    bytesFreshSmallCost fineCostModel 32 = 1476 := by
  unfold bytesFreshSmallCost
  simp only [show (32 : Nat) ≠ 0 by decide, show max 32 8 = 32 by decide, ↓reduceIte,
    smallAllocCost_32_eq]

private theorem bytesFreshSmallCost_33_eq :
    bytesFreshSmallCost fineCostModel 33 = 1476 := by
  unfold bytesFreshSmallCost
  simp only [show (33 : Nat) ≠ 0 by decide, show max 33 8 = 33 by decide, ↓reduceIte,
    smallAllocCost_33_eq]

private theorem bytesFreshSmallCost_1569_eq :
    bytesFreshSmallCost fineCostModel 1569 = 5584 := by
  unfold bytesFreshSmallCost
  simp only [show (1569 : Nat) ≠ 0 by decide, show max 1569 8 = 1569 by decide, ↓reduceIte,
    smallAllocCost_1569_eq]

theorem deserSenderChainFineCum_eq : deserSenderChainFineCum = 4428 := by
  unfold deserSenderChainFineCum
  rw [bytesFreshSmallCost_33_eq, bytesFreshSmallCost_32_eq]

theorem deserRecvChainFineCum_eq : deserRecvChainFineCum = 3259735 := by
  unfold deserRecvChainFineCum
  rw [bytesFreshSmallCost_33_eq, bytesFreshSmallCost_32_eq, vec104CumOfCap_fine_2048_eq]

theorem deserCancelFineCumExpr_eq : deserCancelFineCumExpr = deserCancelFineCum := by
  unfold deserCancelFineCumExpr deserCancelFineCum
  rw [bytesFreshSmallCost_33_eq, bytesFreshSmallCost_32_eq, bytesFreshSmallCost_1569_eq,
    deserSenderChainFineCum_eq, deserRecvChainFineCum_eq, vec104CumOfCap_fine_8_eq]

theorem sessDeserSmallCost_fine_le
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    sessDeserSmallCost fineCostModel r ≤ deserCancelFineCum := by
  rw [← deserCancelFineCumExpr_eq]
  exact sessDeserSmallCost_fine_le_expr hr

/-! ## 2. Closed `PhaseGroupSpec` on `sessDeserEvents` -/

private theorem phaseGroupSpec_append_eq {M : AllocCostModel} [HasFineGroupCredit M]
    {xs ys : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M (· = xs) g₁) (h₂ : PhaseGroupSpec M (· = ys) g₂) :
    PhaseGroupSpec M (· = xs ++ ys) (g₁ + g₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨xs, ys, h, rfl, rfl⟩

private theorem smallAllocGroupS_1569_eq :
    fineSmallAllocGroupS 1569 = 32768 := by
  unfold fineSmallAllocGroupS
  rw [show (1569 + 3) / 16 = 98 by decide]
  decide

theorem bytesMergeEvents_small44_fine_groupSpec {n : Nat} (hn : n ≤ 44) :
    PhaseGroupSpec fineCostModel (· = bytesMergeEvents 0 n) 33318 := by
  by_cases hn0 : n = 0
  · subst hn0
    exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hmax44 : max n 8 ≤ 44 := Nat.max_le.mpr ⟨hn, by decide⟩
    have hm1 : n ≤ MmapThresholdReq := Nat.le_trans hn (by decide)
    have hm2 : max n 8 ≤ MmapThresholdReq := Nat.le_trans hmax44 (by decide)
    have heq : bytesMergeEvents 0 n =
        (rustAllocEvents n 1 ++ rustAllocEvents (max n 8) 1) ++ rustDeallocEvents n 1 := by
      unfold bytesMergeEvents bytesMergeAllocEvents bytesDropEvents
      simp [hn0, hpos, doReserveEvents_zero]
    rw [heq]
    have ha1 : PhaseGroupSpec fineCostModel (· = rustAllocEvents n 1) 16659 :=
      (PhaseGroupSpec.rustAlloc_small fineCostModel (by decide) hm1).mono
        (by rw [smallAllocGroupS_fineCostModel_eq]; exact smallAllocGroupS_le_16659_of_le_44 hn)
    have ha2 : PhaseGroupSpec fineCostModel (· = rustAllocEvents (max n 8) 1) 16659 :=
      (PhaseGroupSpec.rustAlloc_small fineCostModel (by decide) hm2).mono
        (by rw [smallAllocGroupS_fineCostModel_eq]; exact smallAllocGroupS_le_16659_of_le_44 hmax44)
    have hd : PhaseGroupSpec fineCostModel (· = rustDeallocEvents n 1) 0 :=
      PhaseGroupSpec.rustDealloc fineCostModel n 1
    exact (phaseGroupSpec_append_eq (phaseGroupSpec_append_eq ha1 ha2) hd).mono (by decide)

theorem bytesMergeEvents_1569_fine_groupSpec :
    PhaseGroupSpec fineCostModel (· = bytesMergeEvents 0 1569) 65536 := by
  have heq : bytesMergeEvents 0 1569 =
      (rustAllocEvents 1569 1 ++ rustAllocEvents 1569 1) ++ rustDeallocEvents 1569 1 := by
    unfold bytesMergeEvents bytesMergeAllocEvents bytesDropEvents
    simp [doReserveEvents_zero]
  rw [heq]
  have ha : PhaseGroupSpec fineCostModel (· = rustAllocEvents 1569 1) 32768 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (by decide) (by decide)).mono
      (by rw [smallAllocGroupS_fineCostModel_eq, smallAllocGroupS_1569_eq])
  have hd : PhaseGroupSpec fineCostModel (· = rustDeallocEvents 1569 1) 0 :=
    PhaseGroupSpec.rustDealloc fineCostModel 1569 1
  exact (phaseGroupSpec_append_eq (phaseGroupSpec_append_eq ha ha) hd).mono (by decide)

theorem bytesMergeEvents_any_fine_groupSpec (n : Nat) :
    PhaseGroupSpec fineCostModel (· = bytesMergeEvents 0 n) 393216 := by
  have hnf : NonFreeBound (· = bytesMergeEvents 0 n) 2 := by
    rintro _ rfl
    by_cases hn0 : n = 0
    · subst hn0; simp [bytesMergeEvents, bytesMergeAllocEvents, bytesDropEvents, nonFreeCount]
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn0
      unfold bytesMergeEvents bytesMergeAllocEvents bytesDropEvents
      simp only [hn0, hpos, ↓reduceIte, doReserveEvents_zero,
        nonFreeCount_append, nonFreeCount_rustAllocEvents, nonFreeCount_rustDeallocEvents]
      decide
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)

theorem vec104GrowEvents_fine_groupSpec (cap : Nat) :
    PhaseGroupSpec fineCostModel (· = vec104GrowEvents cap) 196608 := by
  unfold vec104GrowEvents
  split_ifs with h0
  · exact (PhaseGroupSpec.rustAlloc_any fineCostModel (4 * 104) 8).mono (by decide)
  · exact (PhaseGroupSpec.rustRealloc_any fineCostModel (cap * 104) (2 * cap * 104) 8).mono
      (by decide)

private theorem take_succ_eq_append_getElem {α : Type} (xs : List α) {k : Nat}
    (hk : k < xs.length) :
    xs.take (k + 1) = xs.take k ++ [xs[k]'hk] := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x rest ih =>
    cases k with
    | zero => simp
    | succ k' =>
      simp only [List.take_succ_cons, List.cons_append, List.getElem_cons_succ]
      rw [ih (Nat.lt_of_succ_lt_succ hk)]

private theorem chainGAfter_keys_length_mono_succ (c : ChainG) {k : Nat}
    (hk : k < c.fields.length) :
    (chainGAfter c k).keys.length ≤ (chainGAfter c (k + 1)).keys.length := by
  unfold chainGAfter
  rw [take_succ_eq_append_getElem c.fields hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set v := (c.fields.take k).foldl ChainG.apply ChainG.empty
  cases c.fields[k]'hk with
  | srk _ | priv _ | ck _ _ => exact Nat.le_refl _
  | key mk => simp [ChainG.apply]

private theorem step_linear_no_grow (gF gG d r0 r1 : Nat) (hr : r1 ≤ r0) :
    gF + (d * gF + r1 * gG) ≤ (d + 1) * gF + r0 * gG := by
  have h1 : d * gF + gF = (d + 1) * gF := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : r1 * gG ≤ r0 * gG := Nat.mul_le_mul_right gG hr
  omega

private theorem step_linear_with_grow (gF gG d a0 a1 cap : Nat)
    (ha : a0 + 1 ≤ a1) (hcap : a1 ≤ cap) :
    (gF + gG) + (d * gF + (cap - a1) * gG) ≤ (d + 1) * gF + (cap - a0) * gG := by
  have h1 : d * gF + gF = (d + 1) * gF := by rw [Nat.add_mul, Nat.one_mul]
  have hsub : 1 + (cap - a1) ≤ cap - a0 := by omega
  have h2 : gG + (cap - a1) * gG ≤ (cap - a0) * gG := by
    calc gG + (cap - a1) * gG
      _ = (1 + (cap - a1)) * gG := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (cap - a0) * gG := Nat.mul_le_mul_right gG hsub
  omega

private def remGrows2000 (c : ChainG) (k : Nat) : Nat :=
  10 - (growPoints2000.filter (· < (chainGAfter c k).keys.length)).length

private theorem chainRemEvents_fine_groupSpec {c : ChainG} (hcOk : c.Ok)
    (hkeys : c.keys.length ≤ 2000) (k : Nat) :
    PhaseGroupSpec fineCostModel (· = chainRemEvents c k)
      ((c.fields.length - k) * 33318 + remGrows2000 c k * 196608) := by
  induction hrem : c.fields.length - k generalizing k with
  | zero =>
    have hge : c.fields.length ≤ k := by omega
    rw [chainRemEvents_ge hge]
    exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | succ d ih =>
    have hlt : k < c.fields.length := by omega
    have hd_eq : c.fields.length - (k + 1) = d := by omega
    have htail := ih (k + 1) hd_eq
    rw [chainRemEvents_eq_cons hlt]
    by_cases hhdr : k < (chainHdrFields c).length
    · have hfl_eq : c.fields[k]'hlt = (chainHdrFields c)[k]'hhdr :=
        getElem_prefix_of_lt (chainHdrFields c) (c.keys.map ChainField.key) k hhdr hlt
      have hmem_hdr : (chainHdrFields c)[k]'hhdr ∈ chainHdrFields c := List.getElem_mem hhdr
      obtain ⟨n, hn33, hstep_eq⟩ := (chainHdrFields_no_key c hmem_hdr).2 hcOk
      rw [hfl_eq, hstep_eq]
      have hstepG := bytesMergeEvents_small44_fine_groupSpec (Nat.le_trans hn33 (by decide))
      have hmono := filter_lt_length_mono growPoints2000 (chainGAfter_keys_length_mono_succ c hlt)
      have hrem_le : remGrows2000 c (k + 1) ≤ remGrows2000 c k := by
        unfold remGrows2000; omega
      exact (phaseGroupSpec_append_eq hstepG htail).mono
        (step_linear_no_grow 33318 196608 d (remGrows2000 c k) (remGrows2000 c (k + 1)) hrem_le)
    · have hge_hdr : (chainHdrFields c).length ≤ k := Nat.not_lt.mp hhdr
      let j := k - (chainHdrFields c).length
      have hk_eq : k = (chainHdrFields c).length + j := by omega
      have hk1_eq : k + 1 = (chainHdrFields c).length + (j + 1) := by omega
      have hj_lt : j < c.keys.length := by
        have hlen_f : c.fields.length = (chainHdrFields c).length + c.keys.length := by
          rw [chain_fields_eq_hdr_append_keys, List.length_append, List.length_map]
        omega
      have hfl_eq : c.fields[k]'hlt = ChainField.key (c.keys[j]'hj_lt) := by
        have hk_lt2 : (chainHdrFields c).length + j <
            (chainHdrFields c ++ c.keys.map ChainField.key).length := by
          rw [← hk_eq]; exact hlt
        have h1 := getElem_length_add (chainHdrFields c) (c.keys.map ChainField.key) j
          (by rw [List.length_map]; exact hj_lt) hk_lt2
        simp only [List.getElem_map] at h1
        have h2 : c.fields[k]'hlt =
            (chainHdrFields c ++ c.keys.map ChainField.key)[(chainHdrFields c).length + j]'hk_lt2 := by
          congr 1
        exact h2.trans h1
      have hlenMk : (chainGAfter c k).keys.length = j := by
        rw [hk_eq]
        exact chainGAfter_keys_length_at_key c (Nat.le_of_lt hj_lt)
      have hlenMk1 : (chainGAfter c (k + 1)).keys.length = j + 1 := by
        rw [hk1_eq]
        exact chainGAfter_keys_length_at_key c hj_lt
      rw [hfl_eq, hlenMk]
      dsimp only [chainFieldStepEvents]
      have hseed32 : (c.keys[j]'hj_lt).seed.length = 32 :=
        hcOk.2.2.2.1 _ (List.getElem_mem hj_lt)
      rw [hseed32]
      have hbm := bytesMergeEvents_small44_fine_groupSpec (by decide : 32 ≤ 44)
      split_ifs with hjcap
      · rw [List.append_nil]
        have hmono := filter_lt_length_mono growPoints2000 (show j ≤ j + 1 by omega)
        have hrem_le : remGrows2000 c (k + 1) ≤ remGrows2000 c k := by
          unfold remGrows2000
          rw [hlenMk, hlenMk1]
          omega
        exact (phaseGroupSpec_append_eq hbm htail).mono
          (step_linear_no_grow 33318 196608 d (remGrows2000 c k) (remGrows2000 c (k + 1)) hrem_le)
      · have heq_cap : vecCap4Of j = j := Nat.le_antisymm (Nat.not_lt.mp hjcap) (le_vecCap4Of j)
        have hpj : IsPow2Cap4 j := heq_cap ▸ vecCap4Of_pow2 j
        have hj_mem : j ∈ growPoints2000 :=
          (isPow2Cap4_lt_2000 hpj (Nat.lt_of_lt_of_le hj_lt hkeys)).1
        have hsucc := filter_lt_succ_of_mem hj_mem
        have hcap10 : (growPoints2000.filter (· < j + 1)).length ≤ 10 := by
          calc (growPoints2000.filter (· < j + 1)).length
            _ ≤ growPoints2000.length := List.length_filter_le _ _
            _ = 10 := by decide
        have hstepG := phaseGroupSpec_append_eq hbm (vec104GrowEvents_fine_groupSpec (vecCap4Of j))
        refine (phaseGroupSpec_append_eq hstepG htail).mono ?_
        unfold remGrows2000
        rw [hlenMk, hlenMk1]
        exact step_linear_with_grow 33318 196608 d
          (growPoints2000.filter (· < j)).length
          (growPoints2000.filter (· < j + 1)).length 10 hsucc hcap10

private theorem chainRemEvents_sender_fine_groupSpec {c : ChainG} (hcOk : c.Ok)
    (hk0 : c.keys = []) (k : Nat) :
    PhaseGroupSpec fineCostModel (· = chainRemEvents c k) ((c.fields.length - k) * 33318) := by
  induction hrem : c.fields.length - k generalizing k with
  | zero =>
    have hge : c.fields.length ≤ k := by omega
    rw [chainRemEvents_ge hge]
    exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | succ d ih =>
    have hlt : k < c.fields.length := by omega
    have hd_eq : c.fields.length - (k + 1) = d := by omega
    have htail := ih (k + 1) hd_eq
    rw [chainRemEvents_eq_cons hlt]
    have hhdr : k < (chainHdrFields c).length := by
      have hlen_f : c.fields.length = (chainHdrFields c).length := by
        rw [chain_fields_eq_hdr_append_keys, hk0, List.map_nil, List.append_nil]
      omega
    have hfl_eq : c.fields[k]'hlt = (chainHdrFields c)[k]'hhdr :=
      getElem_prefix_of_lt (chainHdrFields c) (c.keys.map ChainField.key) k hhdr hlt
    have hmem_hdr : (chainHdrFields c)[k]'hhdr ∈ chainHdrFields c := List.getElem_mem hhdr
    obtain ⟨n, hn33, hstep_eq⟩ := (chainHdrFields_no_key c hmem_hdr).2 hcOk
    rw [hfl_eq, hstep_eq]
    have hstepG := bytesMergeEvents_small44_fine_groupSpec (Nat.le_trans hn33 (by decide))
    refine (phaseGroupSpec_append_eq hstepG htail).mono ?_
    have h1 := step_linear_no_grow 33318 0 d 0 0 (Nat.le_refl 0)
    simpa using h1

theorem chainMergeEvents_sender_fine_groupSpec {c : ChainG} (hcOk : c.Ok) (hk0 : c.keys = []) :
    PhaseGroupSpec fineCostModel (· = chainMergeEvents c) 99954 := by
  rw [← chainRemEvents_zero c]
  have hlen3 : c.fields.length ≤ 3 := by
    rw [chain_fields_eq_hdr_append_keys, hk0, List.map_nil, List.append_nil]
    unfold chainHdrFields
    rcases c.ck with _ | ⟨_, _⟩ <;> split_ifs <;> simp
  refine (chainRemEvents_sender_fine_groupSpec hcOk hk0 0).mono ?_
  calc (c.fields.length - 0) * 33318
    _ ≤ 3 * 33318 := Nat.mul_le_mul_right 33318 hlen3
    _ = 99954 := by decide

theorem chainMergeEvents_recv_fine_groupSpec {c : ChainG} (hcOk : c.Ok)
    (hpriv : c.priv = []) (hkeys : c.keys.length ≤ 2000) :
    PhaseGroupSpec fineCostModel (· = chainMergeEvents c) 68668716 := by
  rw [← chainRemEvents_zero c]
  have hhdr2 : (chainHdrFields c).length ≤ 2 := by
    unfold chainHdrFields
    rw [hpriv]
    rcases c.ck with _ | ⟨_, _⟩ <;> by_cases hs : c.srk = [] <;> simp [hs]
  have hlen2002 : c.fields.length ≤ 2002 := by
    rw [chain_fields_eq_hdr_append_keys, List.length_append, List.length_map]
    omega
  have hrem0 : remGrows2000 c 0 = 10 := by
    unfold remGrows2000
    have h0 : (chainGAfter c 0).keys.length = 0 := rfl
    rw [h0]
    decide
  refine (chainRemEvents_fine_groupSpec hcOk hkeys 0).mono ?_
  rw [Nat.sub_zero, hrem0]
  calc c.fields.length * 33318 + 10 * 196608
    _ ≤ 2002 * 33318 + 10 * 196608 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right 33318 hlen2002) _
    _ = 68668716 := by decide

/-- Per-field `FineScale`-scaled group upper bound across `recFieldsQ r`. -/
def fieldQGroupS : GenFieldQ → Nat
  | .base (.version _) | .base (.prevCounter _) | .remReg _ | .locReg _ => 0
  | .base (.lik _) | .base (.rik _) | .base (.root _)
  | .base (.pending _) | .pendingId _ _ | .pendingSpk _ _ _
  | .abk _ => 33318
  | .base (.sender _) => 99954
  | .base (.recv _) => 68668716
  | .kyber _ _ => 65536
  | .pq _ => 393216

private def remGrows5 (n : Nat) : Nat :=
  2 - (growPoints5.filter (· < n)).length

private theorem mergeFieldQEvents_nonRecv_fine_groupSpec (capRecv n : Nat) (fl : GenFieldQ)
    (hok : fl.Ok) (hnot : ∀ c, fl ≠ .base (.recv c)) :
    PhaseGroupSpec fineCostModel (· = mergeFieldQEvents capRecv n fl) (fieldQGroupS fl) := by
  cases fl with
  | base f =>
    cases f with
    | recv c => exact False.elim (hnot c rfl)
    | sender c => exact chainMergeEvents_sender_fine_groupSpec hok.1 hok.2.2.2
    | version _ | prevCounter _ => exact PhaseGroupSpec.nil fineCostModel
    | lik b | rik b | pending b =>
      have hb : b.length = 33 := hok
      dsimp only [mergeFieldQEvents, basicFieldByteLen, fieldQGroupS]
      rw [hb]
      exact bytesMergeEvents_small44_fine_groupSpec (by decide)
    | root b =>
      have hb : b.length = 32 := hok
      dsimp only [mergeFieldQEvents, basicFieldByteLen, fieldQGroupS]
      rw [hb]
      exact bytesMergeEvents_small44_fine_groupSpec (by decide)
  | pendingId _ k =>
    have hk : k.length = 33 := hok
    dsimp only [mergeFieldQEvents, basicFieldByteLen, fieldQGroupS]
    rw [hk]
    exact bytesMergeEvents_small44_fine_groupSpec (by decide)
  | pendingSpk _ k _ =>
    have hk : k.length = 33 := hok.1
    dsimp only [mergeFieldQEvents, basicFieldByteLen, fieldQGroupS]
    rw [hk]
    exact bytesMergeEvents_small44_fine_groupSpec (by decide)
  | remReg _ | locReg _ => exact PhaseGroupSpec.nil fineCostModel
  | abk b =>
    have hb : b.length = 33 := hok
    dsimp only [mergeFieldQEvents, basicFieldByteLen, fieldQGroupS]
    rw [hb]
    exact bytesMergeEvents_small44_fine_groupSpec (by decide)
  | kyber _ ct =>
    have hct : ct.length = 1569 := hok
    dsimp only [mergeFieldQEvents, basicFieldByteLen, fieldQGroupS]
    rw [hct]
    exact bytesMergeEvents_1569_fine_groupSpec
  | pq b =>
    exact bytesMergeEvents_any_fine_groupSpec b.length

private theorem fieldsEventsAux_fine_groupSpec (n : Nat) (flds : List GenFieldQ)
    (hn5 : n + recvCount flds ≤ 5)
    (hflds : ∀ fl ∈ flds, fl.Ok ∧ (∀ c : ChainG, fl = .base (.recv c) → c.keys.length ≤ 2000)) :
    PhaseGroupSpec fineCostModel (· = fieldsEventsAux (vecCap4Of n) n flds)
      ((flds.map fieldQGroupS).sum + remGrows5 n * 196608) := by
  induction flds generalizing n with
  | nil =>
    exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | cons fl rest ih =>
    obtain ⟨hok, hrc_keys⟩ := hflds fl List.mem_cons_self
    have hrest : ∀ g ∈ rest, g.Ok ∧ (∀ c : ChainG, g = .base (.recv c) → c.keys.length ≤ 2000) :=
      fun g hg => hflds g (List.mem_cons_of_mem fl hg)
    by_cases hrecv : ∃ c, fl = .base (.recv c)
    · obtain ⟨c, rfl⟩ := hrecv
      have hcap' : nextCapRecv (vecCap4Of n) n (.base (.recv c)) = vecCap4Of (n + 1) :=
        nextCapRecv_eq_vecCap4Of n (.base (.recv c))
      have hn_cnt : (n + 1) + recvCount rest ≤ 5 := by
        dsimp only [recvCount] at hn5; omega
      have htail := ih (n + 1) hn_cnt hrest
      simp only [fieldsEventsAux, hcap', mergeFieldQEvents]
      have hcm := chainMergeEvents_recv_fine_groupSpec hok.1 hok.2 (hrc_keys c rfl)
      split_ifs with heq
      · have hn_lt5 : n < 5 := by dsimp only [recvCount] at hn5; omega
        have hp : IsPow2Cap4 n := heq.symm ▸ vecCap4Of_pow2 n
        have hn_mem : n ∈ growPoints5 := (isPow2Cap4_lt_5 hp hn_lt5).1
        have hsucc := filter_lt_succ_of_mem hn_mem
        have hcap2 : (growPoints5.filter (· < n + 1)).length ≤ 2 := by
          calc (growPoints5.filter (· < n + 1)).length
            _ ≤ growPoints5.length := List.length_filter_le _ _
            _ = 2 := by decide
        have hhd := phaseGroupSpec_append_eq hcm (vec104GrowEvents_fine_groupSpec (vecCap4Of n))
        refine (phaseGroupSpec_append_eq hhd htail).mono ?_
        have hgr_le : 196608 + remGrows5 (n + 1) * 196608 ≤ remGrows5 n * 196608 := by
          unfold remGrows5
          have hsub : 1 + (2 - (growPoints5.filter (· < n + 1)).length) ≤
              2 - (growPoints5.filter (· < n)).length := by omega
          calc 196608 + (2 - (growPoints5.filter (· < n + 1)).length) * 196608
            _ = (1 + (2 - (growPoints5.filter (· < n + 1)).length)) * 196608 := by
              rw [Nat.add_mul, Nat.one_mul]
            _ ≤ (2 - (growPoints5.filter (· < n)).length) * 196608 :=
              Nat.mul_le_mul_right 196608 hsub
        simp only [List.map_cons, List.sum_cons, fieldQGroupS]
        omega
      · rw [List.append_nil]
        have hmono := filter_lt_length_mono growPoints5 (show n ≤ n + 1 by omega)
        have hgr_le : remGrows5 (n + 1) * 196608 ≤ remGrows5 n * 196608 := by
          apply Nat.mul_le_mul_right
          unfold remGrows5
          omega
        refine (phaseGroupSpec_append_eq hcm htail).mono ?_
        simp only [List.map_cons, List.sum_cons, fieldQGroupS]
        omega
    · have hnot : ∀ c, fl ≠ .base (.recv c) := fun c hc => hrecv ⟨c, hc⟩
      have hcap' : nextCapRecv (vecCap4Of n) n fl = vecCap4Of n := by
        cases fl with
        | base f => cases f with
          | recv c => exact False.elim (hnot c rfl)
          | _ => rfl
        | _ => rfl
      have hn_cnt : n + recvCount rest ≤ 5 := by
        have hrc_eq : recvCount (fl :: rest) = recvCount rest := by
          cases fl with
          | base f => cases f with
            | recv c => exact False.elim (hnot c rfl)
            | _ => rfl
          | _ => rfl
        rw [hrc_eq] at hn5
        exact hn5
      have htail := ih n hn_cnt hrest
      have hhd := mergeFieldQEvents_nonRecv_fine_groupSpec (vecCap4Of n) n fl hok hnot
      have hstep_eq : fieldsEventsAux (vecCap4Of n) n (fl :: rest) =
          mergeFieldQEvents (vecCap4Of n) n fl ++ fieldsEventsAux (vecCap4Of n) n rest := by
        cases fl with
        | base f => cases f with
          | recv c => exact False.elim (hnot c rfl)
          | _ => simp [fieldsEventsAux, hcap']
        | _ => simp [fieldsEventsAux, hcap']
      rw [hstep_eq]
      refine (phaseGroupSpec_append_eq hhd htail).mono ?_
      simp only [List.map_cons, List.sum_cons]
      omega

set_option maxHeartbeats 400000 in
private theorem recFieldsQ_fieldQGroupS_sum_le
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    ((recFieldsQ r).map fieldQGroupS).sum + remGrows5 0 * 196608 ≤ deserCancelFineGrpS := by
  have ⟨_, s, hs, hscope⟩ := hr
  have h5 : s.state.receiverChains.length ≤ 5 := hscope.1
  have hrem0 : remGrows5 0 = 2 := by decide
  rw [hrem0]
  have hrecv_sum : ((s.state.receiverChains.map
      (fun rc => GenFieldQ.base (.recv (recvChainG rc)))).map fieldQGroupS).sum ≤
      5 * 68668716 := by
    rw [List.map_map]
    exact Nat.le_trans
      (sum_map_le_const_mul s.state.receiverChains _ 68668716 fun _ _ => Nat.le_refl _)
      (Nat.mul_le_mul_right 68668716 h5)
  have hpend : (((pendingFieldX s.pendingPreKey).map
      (fieldQGroupS ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) ≤ 33318 := by
    rcases s.pendingPreKey with _ | p
    · simp [pendingFieldX]
    · dsimp only [pendingFieldX]
      split_ifs
      · rcases p.preKeyId with _ | _ <;>
          simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQGroupS]
      · simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQGroupS]
  have h1 : (((if s.state.sessionVersion = 0 then []
      else [GenField.version s.state.sessionVersion]).map
      (fieldQGroupS ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> rfl
  have h2 : (((if s.state.localIdentity.serialize = [] then []
      else [GenField.lik s.state.localIdentity.serialize]).map
      (fieldQGroupS ∘ GenFieldQ.base)).sum) ≤ 33318 := by
    split_ifs <;> simp [fieldQGroupS]
  have h3 : ∀ ik : IdentityKey,
      (((if ik.serialize = [] then [] else [GenField.rik ik.serialize]).map
        (fieldQGroupS ∘ GenFieldQ.base)).sum) ≤ 33318 := fun _ => by
    split_ifs <;> simp [fieldQGroupS]
  have h4 : (((if keyToBytes32 s.state.rootKey = [] then []
      else [GenField.root (keyToBytes32 s.state.rootKey)]).map
      (fieldQGroupS ∘ GenFieldQ.base)).sum) ≤ 33318 := by
    split_ifs <;> simp [fieldQGroupS]
  have h5_pc : (((if s.state.previousCounter = 0 then []
      else [GenField.prevCounter s.state.previousCounter]).map
      (fieldQGroupS ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> rfl
  have h10 : (((if s.remoteRegistrationId = 0 then []
      else [GenFieldX.remReg s.remoteRegistrationId]).map
      (fieldQGroupS ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs <;> rfl
  have h11 : (((if s.localRegistrationId = 0 then []
      else [GenFieldX.locReg s.localRegistrationId]).map
      (fieldQGroupS ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs <;> rfl
  have h13 : (((if s.aliceBaseKey = [] then []
      else [GenFieldX.abk s.aliceBaseKey]).map
      (fieldQGroupS ∘ Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) ≤ 33318 := by
    split_ifs <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQGroupS]
  have h15 : (((if s.state.pqRatchetState = [] then []
      else [GenFieldQ.pq s.state.pqRatchetState]).map fieldQGroupS).sum) ≤ 393216 := by
    split_ifs <;> simp [fieldQGroupS]
  have hfn : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘ GenFieldX.base) =
      GenFieldQ.base := by
    funext f; rfl
  have hfn_recv : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘ GenFieldX.base ∘
      fun c => GenField.recv (recvChainG c)) =
      (fun c => GenFieldQ.base (.recv (recvChainG c))) := by
    funext c; rfl
  unfold recFieldsQ
  rw [hs]
  dsimp only [genFieldsQ, genFieldsX, genFields, clearPqSession]
  simp only [List.map_append, List.map_map, hfn_recv, hfn, List.sum_append,
    ↓reduceIte, List.map_nil, List.sum_nil]
  simp only [List.map_map] at hrecv_sum
  rw [h1, h5_pc, h10, h11]
  have hcap_eq : 4 * 33318 + 33318 + 99954 + 5 * 68668716 + 65536 + 393216 + 2 * 196608 =
      deserCancelFineGrpS := by decide
  rw [← hcap_eq]
  generalize ((s.state.receiverChains.map
    (fieldQGroupS ∘ GenFieldQ.base ∘ fun c => GenField.recv (recvChainG c))).sum) = Rsum at hrecv_sum ⊢
  generalize 5 * 68668716 = Rcap at hrecv_sum ⊢
  rcases s.state.remoteIdentity with _ | ik <;>
    rcases s.state.senderChain with _ | sc <;>
    rcases s.pendingKyberPreKey with _ | ky
  all_goals
    try (have hrik := h3 ik)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Function.comp_apply, Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQGroupS]
    omega

theorem sessDeserEvents_fine_groupSpec
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    PhaseGroupSpec fineCostModel (· = sessDeserEvents r) deserCancelFineGrpS := by
  have hok_all := recFieldsQ_ok r hr
  have hn5 : 0 + recvCount (recFieldsQ r) ≤ 5 := by
    rw [Nat.zero_add]; exact recvCount_recFieldsQ_le_five hr
  unfold sessDeserEvents
  change PhaseGroupSpec fineCostModel (· = fieldsEventsAux (vecCap4Of 0) 0 (recFieldsQ r)) _
  refine (fieldsEventsAux_fine_groupSpec 0 (recFieldsQ r) hn5 ?_).mono
    (recFieldsQ_fieldQGroupS_sum_le hr)
  intro fl hmem
  refine ⟨hok_all fl hmem, fun c hfl => ?_⟩
  subst hfl
  exact recv_keys_le_2000_of_mem_recFieldsQ hr hmem

/-- Closed `PhaseGroupSpec` for `SessDeserializeCancelEnv r` (`344,462,092`, `5,257` groups). -/
theorem sessDeserializeCancelEnv_fine_groupSpec (r : SessionRecord (List (BitVec 8))) :
    PhaseGroupSpec fineCostModel (SessDeserializeCancelEnv r) deserCancelFineGrpS where
  groups_le st0 {_} hE := (sessDeserEvents_fine_groupSpec hE.1).groups_le st0 hE.2

/-- Closed `PhaseGroupSpec` for `RecordDeserializeCancelEnv bs` (`344,462,092`, `5,257` groups). -/
theorem recordDeserializeCancelEnv_fine_groupSpec (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (RecordDeserializeCancelEnv bs) deserCancelFineGrpS where
  groups_le st0 {evs} hE := by
    rcases hE with ⟨_, rfl⟩ | ⟨r, _, hr, rfl⟩
    · exact ((PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)).groups_le st0 rfl
    · exact (sessDeserEvents_fine_groupSpec hr).groups_le st0 rfl

/-- Monotonicity specialization to the `345,022,998` `grpS` cap. -/
theorem recordDeserializeCancelEnv_fine_groupSpec_b3q (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (RecordDeserializeCancelEnv bs) 345022998 :=
  (recordDeserializeCancelEnv_fine_groupSpec bs).mono (by decide)

/-- Monotonicity specialization to the `345,780,512` `grpS` cap. -/
theorem recordDeserializeCancelEnv_fine_groupSpec_p16_48 (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (RecordDeserializeCancelEnv bs) 345780512 :=
  (recordDeserializeCancelEnv_fine_groupSpec bs).mono (by decide)

/-- Monotonicity specialization to the `346,829,088` `grpS` cap. -/
theorem recordDeserializeCancelEnv_fine_groupSpec_p64 (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (RecordDeserializeCancelEnv bs) 346829088 :=
  (recordDeserializeCancelEnv_fine_groupSpec bs).mono (by decide)

/-- Monotonicity specialization to the `371,994,912` `grpS` cap. -/
theorem recordDeserializeCancelEnv_fine_groupSpec_p192 (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (RecordDeserializeCancelEnv bs) 371994912 :=
  (recordDeserializeCancelEnv_fine_groupSpec bs).mono (by decide)

/-! ## 3. Closed `PhaseCreditSpec` & `cliBudgetLimits` `FitsEnv` Closure -/

/-- Symbolic `PhaseCreditSpec` for `SessDeserializeCancelEnv r` over any `[HasFineReallocCredit M]`
with `33 ≤ smallMaxReq M` and `max 212992 (encodeRecord r).length ≤ maxR`. -/
theorem sessDeserializeCancelEnv_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    {r : SessionRecord (List (BitVec 8))} {maxR : Nat}
    (hmaxR : max 212992 (encodeRecord r).length ≤ maxR) :
    PhaseCreditSpec M (SessDeserializeCancelEnv r)
      (sessDeserSmallCost M r) (sessDeserLargeLive M r) (sessDeserPeakLarge M r) maxR where
  req_align _ hE ev hev := by
    rw [hE.2] at hev
    obtain ⟨hreq, hal⟩ := sessDeserEvents_req_align hE.1 ev hev
    exact ⟨Nat.le_trans hreq hmaxR, hal⟩
  credit_le st0 {_} hE := by
    rw [hE.2]
    exact stepEvents_sessDeserEvents_bounds M h33 hE.1 st0

/-- Closed `fineCostModel` `PhaseCreditSpec` for `SessDeserializeCancelEnv r` at `≤ 2 MiB` wire
slice: `(cum, live, peak, maxReq) = (16,890,453, 3,211,282, 5,316,629, 2,097,152)`. -/
theorem sessDeserializeCancelEnv_fine_phaseCreditSpec
    {r : SessionRecord (List (BitVec 8))}
    (hlen : (encodeRecord r).length ≤ deserCancelFineMaxReq) :
    PhaseCreditSpec fineCostModel (SessDeserializeCancelEnv r)
      deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq where
  req_align _ hE ev hev := by
    rw [hE.2] at hev
    exact sessDeserEvents_req_align_2MiB hE.1 hlen ev hev
  credit_le st0 {_} hE := by
    rw [hE.2]
    have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; decide
    obtain ⟨hcum, hlive, hpeak⟩ := stepEvents_sessDeserEvents_bounds fineCostModel h33 hE.1 st0
    have hc_le : sessDeserSmallCost fineCostModel r ≤ deserCancelFineCum :=
      sessDeserSmallCost_fine_le hE.1
    have hl_le : sessDeserLargeLive fineCostModel r ≤ deserCancelFineLive :=
      sessDeserLargeLive_fine_le_of_encode_le_2MiB hE.1 hlen
    have hp_le : sessDeserPeakLarge fineCostModel r ≤ deserCancelFinePeak :=
      sessDeserPeakLarge_fine_le_of_encode_le_2MiB hE.1 hlen
    exact ⟨Nat.le_trans hcum (Nat.add_le_add_left hc_le _),
      Nat.le_trans hlive (Nat.add_le_add_left hl_le _),
      Nat.le_trans hpeak (Nat.max_le.mpr
        ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left hp_le _) (Nat.le_max_right _ _)⟩)⟩

/-- Closed `fineCostModel` `PhaseCreditSpec` for `RecordDeserializeCancelEnv bs` at
`bs.length ≤ 2,097,152` (`2 MiB`):
`(cum, live, peak, maxReq) = (16,890,453, 3,211,282, 5,316,629, 2,097,152)`. -/
theorem recordDeserializeCancelEnv_fine_phaseCreditSpec
    {bs : List (BitVec 8)} (hlen : bs.length ≤ deserCancelFineMaxReq) :
    PhaseCreditSpec fineCostModel (RecordDeserializeCancelEnv bs)
      deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq where
  req_align _ hE ev hev := by
    rcases hE with ⟨_, rfl⟩ | ⟨r, rfl, hr, rfl⟩
    · nomatch hev
    · exact sessDeserEvents_req_align_2MiB hr hlen ev hev
  credit_le st0 {_} hE := by
    rcases hE with ⟨_, rfl⟩ | ⟨r, rfl, hr, rfl⟩
    · exact ((PhaseCreditSpec.nil fineCostModel).mono (r₂ := deserCancelFineMaxReq)
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)).credit_le st0 rfl
    · exact (sessDeserializeCancelEnv_fine_phaseCreditSpec hlen).credit_le st0 ⟨hr, rfl⟩

/-- Monotonicity specialization to the `19,417,728` `cum` cap. -/
theorem recordDeserializeCancelEnv_fine_phaseCreditSpec_p64
    {bs : List (BitVec 8)} (hlen : bs.length ≤ deserCancelFineMaxReq) :
    PhaseCreditSpec fineCostModel (RecordDeserializeCancelEnv bs)
      19417728 deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq :=
  (recordDeserializeCancelEnv_fine_phaseCreditSpec hlen).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Monotonicity specialization to the `20,638,720` `cum` cap. -/
theorem recordDeserializeCancelEnv_fine_phaseCreditSpec_p192
    {bs : List (BitVec 8)} (hlen : bs.length ≤ deserCancelFineMaxReq) :
    PhaseCreditSpec fineCostModel (RecordDeserializeCancelEnv bs)
      20638720 deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq :=
  (recordDeserializeCancelEnv_fine_phaseCreditSpec hlen).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Standalone `FitsEnv` closure on `cliBudgetLimits` (`1 GiB` RAM, `2 ^ 48` VA) at
`fineCostModel.init` for any `bs.length ≤ 2,097,152`. -/
theorem recordDeserializeCancelEnv_fitsEnv_cliBudgetLimits
    {bs : List (BitVec 8)} (hlen : bs.length ≤ deserCancelFineMaxReq) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RecordDeserializeCancelEnv bs) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups
    (recordDeserializeCancelEnv_fine_phaseCreditSpec hlen)
    (recordDeserializeCancelEnv_fine_groupSpec bs)
    (by decide)
    (Nat.le_refl deserCancelFineGroups)
    rfl
    (by decide)
    (by decide)

/-! ## 4. Non-Vacuity Witnesses -/

/-- Concrete single-session `SessionState` witness (`aliceIdKey` / `bobIdKey`, empty chains). -/
def witnessSessionState0 : SessionState (List (BitVec 8)) where
  sessionVersion := 4#32
  localIdentity := aliceIdKey
  remoteIdentity := some bobIdKey
  rootKey := 0#256
  previousCounter := 0#32
  senderChain := none
  receiverChains := []
  pendingPreKey := false
  pqRatchetState := []

/-- Concrete single-session `Session` witness in `SessionScopeP`. -/
def witnessSession0 : Session (List (BitVec 8)) where
  state := witnessSessionState0
  pendingPreKey := none
  pendingKyberPreKey := none
  localRegistrationId := 0#32
  remoteRegistrationId := 0#32
  aliceBaseKey := []

/-- Concrete `SessionRecord` witness in `DeserializeScopeP_Q NonEmptyV1Q`. -/
def witnessRecord0 : SessionRecord (List (BitVec 8)) :=
  { currentSession := some witnessSession0 }

theorem witnessRecord0_in_scope : DeserializeScopeP_Q NonEmptyV1Q witnessRecord0 := by
  refine ⟨⟨?_, ?_, ?_⟩, witnessSession0, rfl, ?_⟩
  · intro s hs
    injection hs with hs'
    subst hs'
    refine ⟨?_, by decide, fun k hk => nomatch hk⟩
    intro rc hrc
    nomatch hrc
  · intro s hs
    injection hs with hs'
    subst hs'
    decide
  · intro s hs
    injection hs with hs'
    subst hs'
    exact ⟨(fun rc hrc => nomatch hrc), (fun sc hsc => nomatch hsc), rfl, by decide⟩
  · exact ⟨by decide, (fun p hp => nomatch hp), (fun k hk => nomatch hk), Or.inl rfl⟩

theorem witnessRecord0_encode_le_2MiB :
    (encodeRecord witnessRecord0).length ≤ deserCancelFineMaxReq := by
  decide +kernel

theorem witnessRecord0_events_nonempty : sessDeserEvents witnessRecord0 ≠ [] := by
  intro h
  have hc : (sessDeserEvents witnessRecord0).isEmpty = false := by decide +kernel
  simp [h] at hc

/-- Non-empty trace witness for `SessDeserializeCancelEnv`. -/
theorem sessDeserializeCancelEnv_nonempty_witness :
    ∃ r evs, evs ≠ [] ∧ SessDeserializeCancelEnv r evs :=
  ⟨witnessRecord0, sessDeserEvents witnessRecord0, witnessRecord0_events_nonempty,
    sessDeserEvents_mem_sessDeserializeCancelEnv witnessRecord0_in_scope⟩

/-- Non-empty trace witness for `RecordDeserializeCancelEnv`. -/
theorem recordDeserializeCancelEnv_nonempty_witness :
    ∃ bs evs, bs.length ≤ deserCancelFineMaxReq ∧ evs ≠ [] ∧ RecordDeserializeCancelEnv bs evs :=
  ⟨encodeRecord witnessRecord0, sessDeserEvents witnessRecord0,
    witnessRecord0_encode_le_2MiB, witnessRecord0_events_nonempty,
    sessDeserEvents_mem_recordDeserializeCancelEnv witnessRecord0_in_scope⟩

/-- `FitsEnv` and non-empty trace witness on `cliBudgetLimits`. -/
theorem recordDeserializeCancelEnv_fitsEnv_nonempty_witness :
    ∃ bs evs, bs.length ≤ deserCancelFineMaxReq ∧ evs ≠ [] ∧
      RecordDeserializeCancelEnv bs evs ∧
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RecordDeserializeCancelEnv bs) :=
  ⟨encodeRecord witnessRecord0, sessDeserEvents witnessRecord0,
    witnessRecord0_encode_le_2MiB, witnessRecord0_events_nonempty,
    sessDeserEvents_mem_recordDeserializeCancelEnv witnessRecord0_in_scope,
    recordDeserializeCancelEnv_fitsEnv_cliBudgetLimits witnessRecord0_encode_le_2MiB⟩

/-! ## 5. Placed Subroutine Bridges (`SpecsPlacedBudget.sessDeserializeSpecPlaced`, Block `46`) -/

private theorem canonRecord_strip_extra {M : AllocCostModel} [HasFineReallocCredit M]
    (A : CryptoVerification.RustHeap.RustAlloc) (out : BitVec 64)
    (r : SessionRecord (List (BitVec 8))) :
    (∃∗ g : RecordGhost,
      ⌜CanonRecord g r ∧
        (∀ G, g.cur = some G →
          (∀ s_sess, r.currentSession = some s_sess →
            LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssStateLargeLive
              M G s_sess.state =
            LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssLargeLive M G) ∧
          (33 ≤ HasFineReallocCredit.smallMaxReq M →
            LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential.ssLargeLive M G =
              sessDeserLargeLive M r))⌝ ∗
        sessionRecordAt A out g r) ⊢
    (∃∗ g : RecordGhost, ⌜CanonRecord g r⌝ ∗ sessionRecordAt A out g r) := by
  apply Entails.sepExists_elim
  intro g
  refine Entails.sepExists_right g ?_
  exact Entails.pure_left fun hm => Entails.pure_right hm.1 (Entails.refl _)

/-- Placed Block `46` (`lsProg_46 H`) contract for `SpecsPlacedBudget.sessDeserializeSpecPlaced`
instantiated at `SessDeserializeCancelEnv`, parametric over `(M : AllocCostModel) [HasFineReallocCredit M]`
and any `Scope ⊆ DeserializeScopeP_Q NonEmptyV1Q`. -/
theorem sessDeserializeCancel_specPlaced_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r) :
    subroutine_ok (lsProg_46 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim SessDeserializeCancelEnv) := by
  have hbase : (blkPl_46).base = lsmpl.base 46 := rfl
  rw [← hbase]
  refine subroutine_ok_map (sessDeserialize_budget_placed_ok hA)
    fun ⟨x, st₀⟩ R s0 hpre => ⟨(x, st₀), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessDeserializeSpecPlaced, sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      sessDeserializeBudgetRawSpec] at hpre ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have hp := hpre.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    have hr : DeserializeScopeP_Q NonEmptyV1Q x.r := hsub x.r hp.1.2.2.2.1
    have hmem : SessDeserializeCancelEnv x.r (sessDeserEvents x.r) :=
      sessDeserEvents_mem_sessDeserializeCancelEnv hr
    exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hr, hp.1.2.2.2.2 _ hmem⟩, hp.2⟩
  · have hpre_pure : Scope x.r := by
      dsimp only [sessDeserializeSpecPlaced,
        CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpre
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
      have hp := hpre.2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      exact hp.1.2.2.2.1
    have hr : DeserializeScopeP_Q NonEmptyV1Q x.r := hsub x.r hpre_pure
    dsimp only [sessDeserializeBudgetPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      sessDeserializeBudgetRawSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost_mem⟩ := hpost
    dsimp only [sessDeserializeSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    refine Satisfies.mono (sepConj_mono_left ?_) hpost_mem
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (canonRecord_strip_extra A.repAlloc x.out x.r))) ?_
    refine Entails.sepExists_right (sessDeserEvents x.r) ?_
    exact Entails.pure_right ⟨htr, sessDeserEvents_mem_sessDeserializeCancelEnv hr⟩ (Entails.refl _)

/-- Placed Block `46` (`lsProg_46 H`) contract for `SpecsPlacedBudget.sessDeserializeSpecPlaced`
instantiated at `fun r => RecordDeserializeCancelEnv (encodeRecord r)`. -/
theorem sessDeserializeCancel_recordEnv_specPlaced_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r) :
    subroutine_ok (lsProg_46 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim
        (fun r => RecordDeserializeCancelEnv (encodeRecord r))) := by
  refine subroutine_ok_map (sessDeserializeCancel_specPlaced_ok hA hsub)
    fun ⟨x, st₀⟩ R s0 hpre => ⟨(x, st₀), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessDeserializeSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpre ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have hp := hpre.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    refine ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, fun evs hE => ?_⟩, hp.2⟩
    exact hp.1.2.2.2.2 evs (sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv hE)
  · dsimp only [sessDeserializeSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    apply Entails.sepExists_elim
    intro evs
    refine Entails.sepExists_right evs ?_
    exact Entails.pure_left fun hm =>
      Entails.pure_right ⟨hm.1, sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv hm.2⟩
        (Entails.refl _)

/-- Concrete `fineCostModel` specialization of `sessDeserializeCancel_specPlaced_ok`. -/
theorem sessDeserializeCancel_fine_specPlaced_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustCliAllocBudget fineCostModel} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced fineCostModel A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r) :
    subroutine_ok (lsProg_46 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim SessDeserializeCancelEnv) :=
  sessDeserializeCancel_specPlaced_ok hA hsub

/-- Concrete `fineCostModel` specialization of `sessDeserializeCancel_recordEnv_specPlaced_ok`. -/
theorem sessDeserializeCancel_recordEnv_fine_specPlaced_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustCliAllocBudget fineCostModel} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced fineCostModel A lim H)
    (hsub : ∀ r, Scope r → DeserializeScopeP_Q NonEmptyV1Q r) :
    subroutine_ok (lsProg_46 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim
        (fun r => RecordDeserializeCancelEnv (encodeRecord r))) :=
  sessDeserializeCancel_recordEnv_specPlaced_ok hA hsub

end LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
