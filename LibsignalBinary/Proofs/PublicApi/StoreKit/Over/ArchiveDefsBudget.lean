/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionLenAux.Pure

/-!
# Budget-Threaded `archive_current_state_inner` and `promote_state` Specifications

Bounded allocation-event envelopes (`ArchiveCoreEnv`, `ArchiveOverGenEnv`, `PromoteOverGenEnv`,
`ArchiveOverEnvX`, `PromoteOverEnvX`), total-correctness `RustCliAllocBudget M` contracts
(`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`), and `PhaseCreditSpec` / `fineCostModel` `FitsEnv`
witnesses for `archive_current_state_inner` and `promote_state`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey IdentityKey SessionState)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.Record.Serialization.SessionLenAux
  (bytesField_rootKey_length encSessionMem_length_eq chainsTotalLen_nil)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (clearPendingGhost clearPending
   ArchiveOverGenGhost PromoteOverGenGhost ArchiveOverGhost PromoteOverGhost)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
   SeqEnv FreeOnlyEvs rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineStepReserveOfCum)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)

/-- Allocation-event envelope of `archive_current_state_inner` and `promote_state` on
`(prevCap, G, sess)` with empty `previous_sessions`: optional pending-key deallocations
(`FreeOnlyEvs`), `Vec::with_capacity(encLen)` (`rustAllocEvents encLen 1`), optional `grow_one`
(`rustAllocEvents 96 8` when `prevCap = 0#64`), and stack-copy `drop_glue<SessionStructure>`
(`FreeOnlyEvs`). -/
def ArchiveCoreEnv (prevCap : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) : List AllocEvent → Prop :=
  let encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
  SeqEnv FreeOnlyEvs
    (SeqEnv (fun evs => evs = rustAllocEvents encLen 1)
      (SeqEnv (fun evs => if prevCap = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
        FreeOnlyEvs))

/-- Allocation envelope of `archiveOverGenSpec`. -/
abbrev ArchiveOverGenEnv (x : ArchiveOverGenGhost) : List AllocEvent → Prop :=
  ArchiveCoreEnv x.prevCap x.G x.sess

/-- Allocation envelope of `promoteOverGenSpec`. -/
abbrev PromoteOverGenEnv (x : PromoteOverGenGhost) : List AllocEvent → Prop :=
  ArchiveCoreEnv x.prevCap x.G x.sess

/-- Allocation envelope of `archiveOverSpecX` (`prevCap = 0#64`). -/
abbrev ArchiveOverEnvX (x : ArchiveOverGhost) : List AllocEvent → Prop :=
  ArchiveCoreEnv 0#64 x.G x.sess

/-- Allocation envelope of `promoteOverSpecX` (`prevCap = 0#64`). -/
abbrev PromoteOverEnvX (x : PromoteOverGhost) : List AllocEvent → Prop :=
  ArchiveCoreEnv 0#64 x.G x.sess

/-- Budget-threaded `archive_current_state_inner(recPtr)` contract with empty `previous_sessions`
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def archiveOverGenSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ArchiveOverGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (ArchiveOverGenEnv x)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverGenSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ArchiveOverGenEnv x evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverGenSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded `promote_state(recPtr, src)` contract with empty `previous_sessions`
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def promoteOverGenSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PromoteOverGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (PromoteOverGenEnv x)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverGenSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜PromoteOverGenEnv x evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverGenSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded zero-capacity (`prevCap = 0#64`) `archive_current_state_inner` contract
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def archiveOverSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ArchiveOverGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (ArchiveOverEnvX x)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverSpecX
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ArchiveOverEnvX x evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.archiveOverSpecX
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded zero-capacity (`prevCap = 0#64`) `promote_state` contract
    (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def promoteOverSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PromoteOverGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (PromoteOverEnvX x)⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverSpecX
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜PromoteOverEnvX x evs⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteOverSpecX
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-! ## `PhaseCreditSpec` and `fineCostModel` Non-Vacuity Witnesses -/

/-- Parametric `PhaseCreditSpec` for `ArchiveCoreEnv prevCap G sess` under `ModelHyps M`. -/
theorem archiveCoreEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (prevCap : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) :
    let encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
    PhaseCreditSpec M (ArchiveCoreEnv prevCap G sess)
      (2 * encLen + 19270)
      (encLen + 16486)
      (encLen + 16486)
      (max encLen 96) := by
  dsimp only
  set encLen := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  have henc := PhaseCreditSpec.rustAlloc_aff hM (req := encLen) (al := 1) (by decide)
  have hgrow : PhaseCreditSpec M
      (fun evs => if prevCap = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
      9731 8291 8291 96 := by
    by_cases h0 : prevCap = 0#64
    · simp only [h0, ↓reduceIte]
      exact (PhaseCreditSpec.rustAlloc_aff hM (req := 96) (al := 8) (by decide)).mono
        (by decide) (by decide) (by decide) (by decide)
    · simp only [h0, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono (by decide) (by decide) (by decide) (by decide)
  exact (hfr.seq (henc.seq (hgrow.seq hfr))).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Any `(prevCap, G, sess)` whose cleared session encoding is `≤ 4096` bytes satisfies
    `FitsEnv fineCostModel` from `fineCostModel.init` under an explicit `1 GiB` RAM budget. -/
theorem archiveCoreEnv_fitsEnv_of_len_le (prevCap : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (clearPendingGhost G) (clearPending sess)).length ≤ 4096) :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init (ArchiveCoreEnv prevCap G sess) := by
  have hSpec : PhaseCreditSpec fineCostModel (ArchiveCoreEnv prevCap G sess)
      27462 20582 20582 4096 :=
    (archiveCoreEnv_phaseCreditSpec fineCostModel_modelHyps prevCap G sess).mono
      (by omega) (by omega) (by omega) (by omega)
  refine fitsEnv_fineCostModel_of_phaseCredit hSpec (by decide) rfl ?_ ?_
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    decide
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

/-- Concrete `SessionGhost` witness for `ArchiveCoreEnv` non-vacuity. -/
def witnessSessionGhost : SessionGhost where
  localIk := ⟨33#64, 8#64, List.replicate 33 0x05#8⟩
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

/-- Concrete `Session` witness for `ArchiveCoreEnv` non-vacuity. -/
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
    pqRatchetState := [1#8, 2#8, 3#8, 4#8]
  }
  pendingPreKey := none
  pendingKyberPreKey := none
  localRegistrationId := 1#32
  remoteRegistrationId := 2#32
  aliceBaseKey := []

private theorem witnessSession_encLen_bounds :
    let encLen := (encSessionMem (clearPendingGhost witnessSessionGhost)
      (clearPending witnessSession)).length
    0 < encLen ∧ encLen ≤ 4096 := by
  dsimp only
  rw [encSessionMem_length_eq, bytesField_rootKey_length]
  have h0 :
      (CryptoVerification.E2E.Record.uint32Field 1
        (clearPending witnessSession).state.sessionVersion).length = 2 := by decide
  have h2 :
      (CryptoVerification.E2E.Record.bytesField 2
        (clearPendingGhost witnessSessionGhost).localIk.bytes).length = 35 := by decide
  have h3 :
      (CryptoVerification.E2E.Record.bytesField 3
        (clearPendingGhost witnessSessionGhost).remoteIk.bytes).length = 0 := by decide
  have h5 :
      (CryptoVerification.E2E.Record.uint32Field 5
        (clearPending witnessSession).state.previousCounter).length = 0 := by decide
  have h6 :
      (CryptoVerification.E2E.Record.Serialization.encSenderFieldMem
        (clearPendingGhost witnessSessionGhost).sender
        (clearPending witnessSession).state.senderChain).length = 0 := rfl
  have h7 :
      CryptoVerification.E2E.Record.Serialization.SessionLenAux.chainsTotalLen
        ((clearPendingGhost witnessSessionGhost).chains.zip
          (clearPending witnessSession).state.receiverChains) = 0 := rfl
  have h8 :
      (CryptoVerification.E2E.Record.Serialization.encPendingFieldMem
        (clearPendingGhost witnessSessionGhost).pending
        (clearPending witnessSession).pendingPreKey).length = 0 := rfl
  have h10 :
      (CryptoVerification.E2E.Record.uint32Field 10
        (clearPending witnessSession).remoteRegistrationId).length = 2 := by decide
  have h11 :
      (CryptoVerification.E2E.Record.uint32Field 11
        (clearPending witnessSession).localRegistrationId).length = 2 := by decide
  have h13 :
      (CryptoVerification.E2E.Record.bytesField 13
        (clearPending witnessSession).aliceBaseKey).length = 0 := by decide
  have h14 :
      (CryptoVerification.E2E.Record.msgField 14
        ((clearPending witnessSession).pendingKyberPreKey.map
          CryptoVerification.E2E.Record.encPendingKyber)).length = 0 := rfl
  have h15 :
      (CryptoVerification.E2E.Record.bytesField 15
        (clearPending witnessSession).state.pqRatchetState).length = 6 := by decide
  omega

/-- Verifies that `ArchiveCoreEnv 0#64` on `witnessSession` exercises both the `encLen > 0`
buffer allocation and the 96-byte `grow_one` allocation. -/
theorem archiveCoreEnv_zero_allocs_mem :
    let encLen := (encSessionMem (clearPendingGhost witnessSessionGhost)
      (clearPending witnessSession)).length
    0 < encLen ∧
      ArchiveCoreEnv 0#64 witnessSessionGhost witnessSession
        (rustAllocEvents encLen 1 ++ rustAllocEvents 96 8) := by
  dsimp only
  refine ⟨witnessSession_encLen_bounds.1, ?_⟩
  set encLen := (encSessionMem (clearPendingGhost witnessSessionGhost)
    (clearPending witnessSession)).length
  have h1 : SeqEnv (fun evs => if (0#64 : BitVec 64) = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
      FreeOnlyEvs (rustAllocEvents 96 8) := by
    simpa using SeqEnv.append (by simp) FreeOnlyEvs.nil
  have h2 : SeqEnv (fun evs => evs = rustAllocEvents encLen 1)
      (SeqEnv (fun evs => if (0#64 : BitVec 64) = 0#64 then evs = rustAllocEvents 96 8 else evs = [])
        FreeOnlyEvs)
      (rustAllocEvents encLen 1 ++ rustAllocEvents 96 8) :=
    SeqEnv.append rfl h1
  simpa [ArchiveCoreEnv] using SeqEnv.append FreeOnlyEvs.nil h2

/-- Non-vacuity witness showing `ArchiveCoreEnv 0#64` satisfies `FitsEnv fineCostModel` from
`fineCostModel.init` under a 1 GiB physical cap. -/
theorem archiveCoreEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init
      (ArchiveCoreEnv 0#64 witnessSessionGhost witnessSession) :=
  archiveCoreEnv_fitsEnv_of_len_le 0#64 witnessSessionGhost witnessSession
    witnessSession_encLen_bounds.2

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefsBudget
