/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure

/-!
# Budget-Threaded `SessionRecord` Codec Contracts

Budget-threaded (`RustCliAllocBudget M`) contracts for `SessionRecord::deserialize`
(`recordDeserializeSpec`) and `SessionRecord::serialize` (`recordSerializeSpec`), small-regime
`PhaseCreditSpec` bounds, and 1 GiB non-vacuity witnesses.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Bin.RecordBudget

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngAlignedEffSize MallocngMaxAllocSize)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.E2E.Record (lenField encodeRecord)
open CryptoVerification.E2E.Record.Serialization (
  encSessionMem encRecordMem CanonRecord encRecordMem_eq_of_canon
)
open CryptoVerification.E2E.Record.Serialization.SessionLenAux (
  lenField_length bytesField_rootKey_length encSessionMem_length_eq
)
open CryptoVerification.E2E.Bin (RecordDeserializeGhost RecordSerializeGhost)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Heap.Fine (FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (
  eventStepReq eventStepAlign
  fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineStepReserveOfCum
  fineCostModel_smallMaxReq_eq smallAllocCost_le_add_26365 smallReallocCost_le_add_26365
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (
  freeOnly_fineCostModel fineCostModel_modelHyps
  fitsEnv_fineCostModel_of_phaseCredit nonVacLimits
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  BoundedRustEvs SerializeEnv
)
open LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget (
  RecordDeserializeEnv recordDeserializeEnv_fitsEnv_of_len_le
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerializeEnvX)

/-! ## Budget-Threaded `recordDeserializeSpec` and `recordSerializeSpec` -/

/-- Budget-threaded `SessionRecord::deserialize` contract (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`)
    over `RecordDeserializeEnv (encodeRecord ⟨some x.s⟩)`. -/
def recordDeserializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (RecordDeserializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (RecordDeserializeEnv (encodeRecord ⟨some x.s⟩))⌝ ∗
      (CryptoVerification.E2E.Bin.recordDeserializeSpec (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜RecordDeserializeEnv (encodeRecord ⟨some x.s⟩) evs⌝ ∗
      (CryptoVerification.E2E.Bin.recordDeserializeSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded `SessionRecord::serialize` contract (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`)
    over `SerializeEnvX x.g x.r`. -/
def recordSerializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (RecordSerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (SerializeEnvX x.g x.r)⌝ ∗
      (CryptoVerification.E2E.Bin.recordSerializeSpec (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜SerializeEnvX x.g x.r evs⌝ ∗
      (CryptoVerification.E2E.Bin.recordSerializeSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-! ## Small-Regime `PhaseCreditSpec` and Non-Vacuity Witnesses -/

private theorem eventStepReq_le_reqBytes (ev : AllocEvent) :
    eventStepReq ev ≤ ev.reqBytes := by
  cases ev with
  | alloc req => exact Nat.le_refl req
  | aligned al req =>
    simp only [eventStepReq, AllocEvent.reqBytes, mallocngAlignedEffSize]
    split <;> omega
  | free _ _ => exact Nat.le_refl 0
  | realloc _ _ newSz => exact Nat.le_refl newSz

private theorem step_boundedSmall_le {maxReq : Nat} (hsmall : maxReq ≤ 135167)
    (ev : AllocEvent) (st : fineCostModel.σ)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    let st' := fineCostModel.step ev st
    HasFineReallocCredit.cumSmall (M := fineCostModel) st' ≤
      HasFineReallocCredit.cumSmall (M := fineCostModel) st + (maxReq + 26365) ∧
    HasFineReallocCredit.liveLarge (M := fineCostModel) st' ≤
      HasFineReallocCredit.liveLarge (M := fineCostModel) st ∧
    HasFineReallocCredit.peakLarge (M := fineCostModel) st' ≤
      HasFineReallocCredit.peakLarge (M := fineCostModel) st := by
  have hM := fineCostModel_modelHyps
  cases ev with
  | free al sz =>
    obtain ⟨hc, hl, hp⟩ := hM.freeNonInc al sz st
    omega
  | alloc req =>
    simp only [eventStepReq] at hreq
    have hle : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
    have hsa := smallAllocCost_le_add_26365 req
    omega
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hle : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
    have hsa := smallAllocCost_le_add_26365 req
    omega
  | realloc al old newSz =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hnew_le : newSz ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    have hsr := smallReallocCost_le_add_26365 newSz
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq fineCostModel
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
      omega
    · have hold_gt : HasFineReallocCredit.smallMaxReq fineCostModel < old := by omega
      obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st hal hold_gt hnew_le
      omega

private theorem stepEvents_boundedSmall_le {maxReq : Nat} (hsmall : maxReq ≤ 135167) :
    ∀ (evs : List AllocEvent) (st : fineCostModel.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (M := fineCostModel) (fineCostModel.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall (M := fineCostModel) st + evs.length * (maxReq + 26365) ∧
      HasFineReallocCredit.liveLarge (M := fineCostModel) (fineCostModel.stepEvents evs st) ≤
        HasFineReallocCredit.liveLarge (M := fineCostModel) st ∧
      HasFineReallocCredit.peakLarge (M := fineCostModel) (fineCostModel.stepEvents evs st) ≤
        HasFineReallocCredit.peakLarge (M := fineCostModel) st
  | [], st, _ => by
    simp only [AllocCostModel.stepEvents_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: evs, st, hbounds => by
    simp only [AllocCostModel.stepEvents_cons, List.length_cons, Nat.succ_mul]
    obtain ⟨hreq, hal⟩ := hbounds ev List.mem_cons_self
    obtain ⟨hc₁, hl₁, hp₁⟩ := step_boundedSmall_le hsmall ev st hreq hal
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_boundedSmall_le hsmall evs (fineCostModel.step ev st)
      (fun e he => hbounds e (List.mem_cons_of_mem _ he))
    omega

/-- Small-regime (`maxReq ≤ 135167`) `PhaseCreditSpec` on `fineCostModel` for
`BoundedRustEvs maxCount maxReq`. -/
theorem boundedRustEvs_small_phaseCreditSpec {maxCount maxReq : Nat}
    (hsmall : maxReq ≤ 135167) :
    PhaseCreditSpec fineCostModel (BoundedRustEvs maxCount maxReq)
      (maxCount * (maxReq + 26365)) 0 0 maxReq where
  req_align evs hE ev hev := by
    obtain ⟨_, hreqB, hal_al, hal_re⟩ := hE.2 ev hev
    refine ⟨Nat.le_trans (eventStepReq_le_reqBytes ev) hreqB, ?_⟩
    cases ev with
    | alloc _ => exact Nat.le_refl 16
    | aligned al r => exact hal_al al r rfl
    | free _ _ => exact Nat.le_refl 16
    | realloc al o n => exact hal_re al o n rfl
  credit_le st0 {evs} hE := by
    have hbounds : ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
      intro ev hev
      obtain ⟨_, hreqB, hal_al, hal_re⟩ := hE.2 ev hev
      refine ⟨Nat.le_trans (eventStepReq_le_reqBytes ev) hreqB, ?_⟩
      cases ev with
      | alloc _ => exact Nat.le_refl 16
      | aligned al r => exact hal_al al r rfl
      | free _ _ => exact Nat.le_refl 16
      | realloc al o n => exact hal_re al o n rfl
    obtain ⟨hc, hl, hp⟩ := stepEvents_boundedSmall_le hsmall evs st0 hbounds
    have hmul : evs.length * (maxReq + 26365) ≤ maxCount * (maxReq + 26365) :=
      Nat.mul_le_mul_right (maxReq + 26365) hE.1
    omega

/-- Any `(g, r)` with `(encRecordMem g r).length ≤ 80` satisfies `FitsEnv` for `SerializeEnvX g r`
under `nonVacLimits` (`1 GiB` physical RAM cap). -/
theorem serializeEnvX_fitsEnv_of_len_le (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (hlen : (encRecordMem g r).length ≤ 80) :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init (SerializeEnvX g r) := by
  have hsub : ∀ evs, SerializeEnv g r evs → BoundedRustEvs 768 24576 evs := by
    intro evs hS
    exact BoundedRustEvs.mono (by omega) (by omega) hS
  have hSer : PhaseCreditSpec fineCostModel (SerializeEnv g r) 39122688 0 0 24576 :=
    ((boundedRustEvs_small_phaseCreditSpec (maxCount := 768) (maxReq := 24576)
      (by decide)).of_imp hsub).mono (by decide) (by decide) (by decide) (by decide)
  have hSpec : PhaseCreditSpec fineCostModel (SerializeEnvX g r) 39122688 0 0 24576 :=
    (hSer.seq freeOnly_fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  refine fitsEnv_fineCostModel_of_phaseCredit hSpec (by decide) rfl ?_ ?_
  · unfold nonVacLimits fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp
      PAGE_SIZE
    decide
  · unfold nonVacLimits fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

def witnessSession : Session (List (BitVec 8)) where
  state := {
    sessionVersion := 4#32
    localIdentity := ⟨⟨List.replicate 32 0#8, by decide⟩⟩
    remoteIdentity := none
    rootKey := 0#256
    previousCounter := 0#32
    senderChain := none
    receiverChains := []
    pendingPreKey := false
    pqRatchetState := []
  }
  pendingPreKey := none
  pendingKyberPreKey := none
  localRegistrationId := 1#32
  remoteRegistrationId := 2#32
  aliceBaseKey := []

def witnessSessionGhost : SessionGhost where
  localIk := ⟨33#64, 8#64, witnessSession.state.localIdentity.serialize⟩
  remoteIk := ⟨0#64, 1#64, []⟩
  root := ⟨32#64, 128#64⟩
  chainsCap := 0#64
  chainsPtr := 8#64
  chains := []
  alice := ⟨0#64, 1#64, []⟩
  pq := ⟨0#64, 1#64⟩
  sender := none
  pending := none
  kyber := none
  regIds := List.replicate 8 0#8

def witnessRecordGhost : RecordGhost :=
  ⟨0#64, 8#64, some witnessSessionGhost⟩

def witnessRecord : SessionRecord (List (BitVec 8)) :=
  ⟨some witnessSession⟩

private theorem witnessRecord_canon : CanonRecord witnessRecordGhost witnessRecord :=
  ⟨rfl, rfl, trivial, rfl, (fun _ h => nomatch h), trivial⟩

private theorem witnessRecord_encLen_eq :
    (encRecordMem witnessRecordGhost witnessRecord).length = 77 := by
  have hsess : (encSessionMem witnessSessionGhost witnessSession).length = 75 := by
    rw [encSessionMem_length_eq, bytesField_rootKey_length]
    have h0 :
        (CryptoVerification.E2E.Record.uint32Field 1
          witnessSession.state.sessionVersion).length = 2 := by decide
    have h2 :
        (CryptoVerification.E2E.Record.bytesField 2
          witnessSessionGhost.localIk.bytes).length = 35 := by decide
    have h3 :
        (CryptoVerification.E2E.Record.bytesField 3
          witnessSessionGhost.remoteIk.bytes).length = 0 := by decide
    have h5 :
        (CryptoVerification.E2E.Record.uint32Field 5
          witnessSession.state.previousCounter).length = 0 := by decide
    have h6 :
        (CryptoVerification.E2E.Record.Serialization.encSenderFieldMem
          witnessSessionGhost.sender witnessSession.state.senderChain).length = 0 := rfl
    have h7 :
        CryptoVerification.E2E.Record.Serialization.SessionLenAux.chainsTotalLen
          (witnessSessionGhost.chains.zip witnessSession.state.receiverChains) = 0 := rfl
    have h8 :
        (CryptoVerification.E2E.Record.Serialization.encPendingFieldMem
          witnessSessionGhost.pending witnessSession.pendingPreKey).length = 0 := rfl
    have h10 :
        (CryptoVerification.E2E.Record.uint32Field 10
          witnessSession.remoteRegistrationId).length = 2 := by decide
    have h11 :
        (CryptoVerification.E2E.Record.uint32Field 11
          witnessSession.localRegistrationId).length = 2 := by decide
    have h13 :
        (CryptoVerification.E2E.Record.bytesField 13
          witnessSession.aliceBaseKey).length = 0 := by decide
    have h14 :
        (CryptoVerification.E2E.Record.msgField 14
          (witnessSession.pendingKyberPreKey.map
            CryptoVerification.E2E.Record.encPendingKyber)).length = 0 := rfl
    have h15 :
        (CryptoVerification.E2E.Record.bytesField 15
          witnessSession.state.pqRatchetState).length = 0 := by decide
    omega
  change (lenField 1 (encSessionMem witnessSessionGhost witnessSession)).length = 77
  rw [lenField_length _ rfl, hsess]
  decide

theorem serializeEnvX_witness_inhabited :
    SerializeEnvX witnessRecordGhost witnessRecord
      (rustAllocEvents 77 1 ++ rustDeallocEvents 33 8) := by
  refine SeqEnv.append ?_ (FreeOnlyEvs.singleton 8 33)
  unfold SerializeEnv BoundedRustEvs
  rw [witnessRecord_encLen_eq]
  have hev : rustAllocEvents 77 1 = [.alloc 77] := by decide
  rw [hev]
  refine ⟨by decide, ?_⟩
  intro ev hev_mem
  rw [List.mem_singleton] at hev_mem
  subst hev_mem
  refine ⟨?_, by decide, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  unfold AllocEvent.withinMaxAlloc MallocngMaxAllocSize
  decide

/-- Non-vacuity witness for `recordSerializeSpec` under `nonVacLimits`. -/
theorem recordSerializeSpec_fitsEnv_witness :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init
      (SerializeEnvX witnessRecordGhost witnessRecord) :=
  serializeEnvX_fitsEnv_of_len_le witnessRecordGhost witnessRecord
    (by rw [witnessRecord_encLen_eq]; decide)

/-- Non-vacuity witness for `recordDeserializeSpec` under `nonVacLimits`. -/
theorem recordDeserializeSpec_fitsEnv_witness :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init
      (RecordDeserializeEnv (encodeRecord ⟨some witnessSession⟩)) := by
  apply recordDeserializeEnv_fitsEnv_of_len_le
  have heq : encodeRecord witnessRecord = encRecordMem witnessRecordGhost witnessRecord :=
    (encRecordMem_eq_of_canon witnessRecordGhost witnessRecord witnessRecord_canon).symm
  change (encodeRecord witnessRecord).length ≤ 2 * 1024 * 1024
  rw [heq, witnessRecord_encLen_eq]
  decide

end LibsignalBinary.Proofs.E2E.Bin.RecordBudget
