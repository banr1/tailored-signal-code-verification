/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.VecGrowCredit
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec

@[expose] public section

/-!
# CLI Small-Allocation Group Bounds

`PhaseGroupSpec` bounds for the CLI phase envelopes. High-trip small-allocation loops
(`cmkJump` `33 B` keys and `32 B` out-of-order message-key seeds) use the exact
`fineCostModel` per-size-class scaled weights from `GroupCreditKit` (`16659` scaled units
for `≤ 44 B`, `11056` for `≤ 28 B`) rather than the coarse `3 * FineScale` per-allocation
bound.
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliGroupBounds

open Arm64 (FsEntry)
open Arm64.Process (initFsState)
open CryptoGames.LibsignalSession
  (Crypto IdentityKey MessageKeyGenerator OutgoingTripleRatchet
   ReceiverChain SenderChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord execOk)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E.Pqxdh.Shared (TryAllocateInCall)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.LibsignalProtoCodec (mergeBytes)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord recGhostOf)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityStoreSpec SessionStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost VecGhost)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall PqRatchetState V1State)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall RecordDecryptGhost SpqrModel reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeGhost)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SenderChainGhost SessionGhost TailVecGhost UuidParser)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli
  (DirGhost GrowOneDirGhost ReadRule addressText cliInputs decimalText pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddressCall CallV Reserve16Call RunCall addrParse)
open CryptoVerification.SpqrV1.ChainProofs (VecDequeGrowGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale MmapThresholdReq fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (GrowOneU8Env GrowOneU8Env_iff_rawVecGrowEnv GrowOneVecU8Env RawVecGrowEnv
   StringCloneEnv rawVecGrowEvents)
open LibsignalBinary.Heap.SpecBudget
  (ReadFileEnv ReadStdinEnv allocBytes1Events cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
  (CliIoReadStdinEnv addrParse_name_bounds specCliIoReadSchedule_events_eq)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainEnv CliMainSetupEnv CliWriteFileEnv CliWriteStdoutEnv
   M1PhaseEnv M2CollectEnv M2CollectStepEnv M3PhaseEnv
   M5DirStepEnv M5LoopAEntryEnv M5PhaseEnv M5WriteStepEnv M6Env)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
  (cliIoCapEvents cliIoCapEventsGo cliIoCapIdx cliIoCapIdx_le cliIoReadCaps)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (CliAddrTextEnv CliDecimalEnv CliDirGetEnv CliDirPutEnv CliDirPutStrEnv
   CliIoReadFileEnv CliPathEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec
   nonFreeCount nonFreeCount_append nonFreeCount_nil
   nonFreeCount_rustAllocEvents nonFreeCount_rustDeallocEvents
   nonFreeCount_rustReallocEvents smallAllocGroupS_fineCostModel_eq
   smallAllocGroupS_le_11056_of_le_28 smallAllocGroupS_le_16659_of_le_44
   smallAllocGroupS_le_24623_of_le_60 smallAllocGroupS_le_43464_of_le_108)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSessStorePollPrev1Env
   CliSmallStorePollEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (dropClonedChainEvents dropClonedMessageKeysEvents dropClonedSessionEvents optTailCloneLen)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeCancelEnv RecordSerializeSeqFreeEnv
   SerializePrev1CancelEnv SerializePrev1SeqFreeEnv
   SerializeSomeCancelEnv SerializeSomeSeqFreeEnv
   dropVecVecClone1Events vecVecClone1Events)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrBoundedTotalEvs freshAllocCount reallocCount)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateBoundedEnv DecodeStateLinearBoundedEnv StatesFromPbBoundedEnv)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCredit
  (doublingCaps doublingCapsFrom growOrReallocEvents)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
  (FromApplySegEnv FromCmSegEnv FromKeySegEnv FromSaveSegEnv
   KyberOptStepEnv OtrApplyEnvTight OtrEncryptStepEnv WithStoresEncSegEnv)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
  (FromApplyTightEnv FromCmTightEnv FromOtrTightEnv FromSaveTightEnv
   WithStoresEncTightEnv otrAfterNone otrAfterSome)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (GhostCloneValid RecordGhostValid SessionCloneDom ghostCloneValid_of_sessionGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak
  (cmkJumpFinalIdx cmkJumpListEvs growOne104Evs v104CapSeq)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
  (AesDecCtShape BoundedLenEvs BoundedNonFreeEvs TrApplyBoundedEnv
   TrialLoopEnv dhCommitStep12Evs dhCommitStep3Evs doublingChain104Evs
   isNonFreeEv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (W2AesDecErrEnv W2Seg3DhCommitEnv W2Seg4CmkStepEnv W2Seg7MacEnv
   W2TryDecryptEnv W2TryDecryptFailEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
  (computeMacEvs s7CoreEvs vmacEvs)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
  (W3BoxedStoreStepEnv W3InitiateSlotEnv W3InitiateSlotParams
   W3SessLoadStepEnv W3SessStoreStepEnv W3SmallStoreStepEnv W3Stage4SpqrEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (W3BoundedEvs W3InitiateFullEnv W3InitiateFullEnvWide W3Stage1Env W3Stage1EnvWide
   W3Stage23BracketEnv W3Stage2Env W3Stage4Env W3Stage5Env)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromPostSomeEnv FromRegionNoneEnv FromRegionSomeEnv
   FromStoreCallEnv FromTrustedFalseEnv FromTrustedTrueEnv LoadPollStepEnv
   SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (LoadStepEnv SessionStoreBudgetEnv StoreStepEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
  (GrowOne104Env growOne104Events)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
  (GrowOneDirBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget
  (GrowOneDirEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (AddressEnv Reserve16Env TryAllocateInEnv addressEvents
   reserve16Events tryAllocateInEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (VecDequeGrowEnv vecDequeGrowEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv SpqrBoundedEvs StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
  (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents finishGrowEvents)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (GrowOneSpeEnv growOneSpeEvents_eq_of_env)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (ChainCloneEnv SenderChainCloneEnv chainCloneEvents
   senderChainAsProtoGhost senderChainCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromFEnv FromMEnv FromVEnv FromVPostTdEnv RecordDecryptEnv SegCloneEnv
   SegTailEnv TryDecryptEnvArgs optTailCloneEvents recordTryDecryptEnvArgs
   segCloneEvents vecCloneEvents)

/-! ## Singleton, Append, and Bounded-Event Helpers -/

theorem phaseGroupSpec_append_eq (M : AllocCostModel) [HasFineGroupCredit M]
    {l₁ l₂ : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M (· = l₁) g₁)
    (h₂ : PhaseGroupSpec M (· = l₂) g₂) :
    PhaseGroupSpec M (· = l₁ ++ l₂) (g₁ + g₂) := by
  refine (h₁.concat h₂).of_imp ?_
  intro evs h
  subst h
  exact ⟨l₁, l₂, rfl, rfl, rfl⟩

theorem phaseGroupSpec_exists_guarded {α : Sort _} (M : AllocCostModel) [HasFineGroupCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, P a → PhaseGroupSpec M (E a) g) :
    PhaseGroupSpec M (fun evs => ∃ a, P a ∧ E a evs) g where
  groups_le st0 {_} := fun ⟨a, ha, hevs⟩ => (h a ha).groups_le st0 hevs

theorem fine_rustAlloc_le_28 {sz al : Nat} (hal : al ≤ 16) (hsz : sz ≤ 28) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents sz al) 11056 := by
  have hm : sz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  refine (PhaseGroupSpec.rustAlloc_small fineCostModel hal hm).mono ?_
  rw [smallAllocGroupS_fineCostModel_eq]
  exact smallAllocGroupS_le_11056_of_le_28 hsz

theorem fine_rustAlloc_le_44 {sz al : Nat} (hal : al ≤ 16) (hsz : sz ≤ 44) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents sz al) 16659 := by
  have hm : sz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  refine (PhaseGroupSpec.rustAlloc_small fineCostModel hal hm).mono ?_
  rw [smallAllocGroupS_fineCostModel_eq]
  exact smallAllocGroupS_le_16659_of_le_44 hsz

theorem fine_rustAlloc_le_60 {sz al : Nat} (hal : al ≤ 16) (hsz : sz ≤ 60) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents sz al) 24623 := by
  have hm : sz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  refine (PhaseGroupSpec.rustAlloc_small fineCostModel hal hm).mono ?_
  rw [smallAllocGroupS_fineCostModel_eq]
  exact smallAllocGroupS_le_24623_of_le_60 hsz

theorem fine_rustAlloc_le_108 {sz al : Nat} (hal : al ≤ 16) (hsz : sz ≤ 108) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents sz al) 43464 := by
  have hm : sz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  refine (PhaseGroupSpec.rustAlloc_small fineCostModel hal hm).mono ?_
  rw [smallAllocGroupS_fineCostModel_eq]
  exact smallAllocGroupS_le_43464_of_le_108 hsz

theorem nonFreeCount_le_length : ∀ evs : List AllocEvent, nonFreeCount evs ≤ evs.length
  | [] => by simp [nonFreeCount_nil]
  | ev :: rest => by
      have ih := nonFreeCount_le_length rest
      cases ev <;> simp [nonFreeCount] <;> omega

theorem boundedRustEvs_nonFreeBound (maxCount maxReq : Nat) :
    NonFreeBound (BoundedRustEvs maxCount maxReq) maxCount :=
  fun evs h => Nat.le_trans (nonFreeCount_le_length evs) h.1

theorem boundedRustEvs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (maxCount maxReq : Nat) :
    PhaseGroupSpec M (BoundedRustEvs maxCount maxReq) (3 * FineScale * maxCount) :=
  PhaseGroupSpec.of_nonFreeBound M (boundedRustEvs_nonFreeBound maxCount maxReq)

theorem boundedLenEvs_nonFreeBound (maxLen maxReq : Nat) :
    NonFreeBound (BoundedLenEvs maxLen maxReq) maxLen :=
  fun evs h => Nat.le_trans (nonFreeCount_le_length evs) h.1

theorem boundedLenEvs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (maxLen maxReq : Nat) :
    PhaseGroupSpec M (BoundedLenEvs maxLen maxReq) (3 * FineScale * maxLen) :=
  PhaseGroupSpec.of_nonFreeBound M (boundedLenEvs_nonFreeBound maxLen maxReq)

theorem filter_isNonFreeEv_length_eq :
    ∀ evs : List AllocEvent, (evs.filter isNonFreeEv).length = nonFreeCount evs
  | [] => by simp [nonFreeCount_nil]
  | ev :: rest => by
      have ih := filter_isNonFreeEv_length_eq rest
      cases ev <;> simp [List.filter, isNonFreeEv, nonFreeCount, ih]

theorem boundedNonFreeEvs_nonFreeBound (k maxLen maxReq : Nat) :
    NonFreeBound (BoundedNonFreeEvs k maxLen maxReq) k := by
  intro evs h
  rw [← filter_isNonFreeEv_length_eq]
  exact h.2.1

theorem boundedNonFreeEvs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (k maxLen maxReq : Nat) :
    PhaseGroupSpec M (BoundedNonFreeEvs k maxLen maxReq) (3 * FineScale * k) :=
  PhaseGroupSpec.of_nonFreeBound M (boundedNonFreeEvs_nonFreeBound k maxLen maxReq)

/-- Bounded non-free event trace (`evs.length ≤ maxLen`, `nonFreeCount evs ≤ k`,
`eventStepReq ≤ maxReq`, `eventStepAlign ≤ 16`) with no `.realloc` events. -/
def BoundedFreshEvs (k maxLen maxReq : Nat) (evs : List AllocEvent) : Prop :=
  evs.length ≤ maxLen ∧ nonFreeCount evs ≤ k ∧
    (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) ∧
    (∀ ev ∈ evs, ∀ al o n, ev ≠ .realloc al o n)

private theorem stepEvents_noRealloc_le_44 :
    ∀ (evs : List AllocEvent) (st0 : fineCostModel.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ 44 ∧ eventStepAlign ev ≤ 16) →
      (∀ ev ∈ evs, ∀ al o n, ev ≠ .realloc al o n) →
      HasFineGroupCredit.groupsScaled (fineCostModel.stepEvents evs st0) ≤
        HasFineGroupCredit.groupsScaled st0 + nonFreeCount evs * 16659
  | [], st0, _, _ => by
      simp [AllocCostModel.stepEvents_nil, nonFreeCount_nil]
  | ev :: rest, st0, hreq, hnr => by
      have hrest_req' : ∀ e ∈ rest, eventStepReq e ≤ 44 ∧ eventStepAlign e ≤ 16 :=
        fun e he => hreq e (List.mem_cons_of_mem _ he)
      have hrest_nr : ∀ e ∈ rest, ∀ al o n, e ≠ .realloc al o n :=
        fun e he => hnr e (List.mem_cons_of_mem _ he)
      have hev := hreq ev List.mem_cons_self
      rw [AllocCostModel.stepEvents_cons]
      cases ev with
      | free al sz =>
          have hstep := HasFineGroupCredit.step_free_le (M := fineCostModel) al sz st0
          have ih := stepEvents_noRealloc_le_44 rest (fineCostModel.step (.free al sz) st0) hrest_req' hrest_nr
          simp only [nonFreeCount]
          omega
      | alloc req =>
          have hle44 : req ≤ 44 := by simpa [eventStepReq] using hev.1
          have hm : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
          have hstep := HasFineGroupCredit.step_alloc_small_le (M := fineCostModel) st0 hm
          rw [smallAllocGroupS_fineCostModel_eq] at hstep
          have hw := smallAllocGroupS_le_16659_of_le_44 hle44
          have ih := stepEvents_noRealloc_le_44 rest (fineCostModel.step (.alloc req) st0) hrest_req' hrest_nr
          simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
          omega
      | aligned al req =>
          have hle44 : req ≤ 44 := by simpa [eventStepReq] using hev.1
          have hal16 : al ≤ 16 := by simpa [eventStepAlign] using hev.2
          have hm : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
          have hstep := HasFineGroupCredit.step_aligned_small_le (M := fineCostModel) st0 hal16 hm
          rw [smallAllocGroupS_fineCostModel_eq] at hstep
          have hw := smallAllocGroupS_le_16659_of_le_44 hle44
          have ih := stepEvents_noRealloc_le_44 rest (fineCostModel.step (.aligned al req) st0) hrest_req' hrest_nr
          simp only [nonFreeCount, Nat.add_mul, Nat.one_mul]
          omega
      | realloc al o n =>
          exact False.elim (hnr (.realloc al o n) List.mem_cons_self al o n rfl)

theorem boundedFreshEvs_le_44_fine_groupSpec
    {k maxLen maxReq : Nat} (hmr : maxReq ≤ 44) :
    PhaseGroupSpec fineCostModel (BoundedFreshEvs k maxLen maxReq) (k * 16659) where
  groups_le st0 {evs} := fun ⟨_, hnf, hb, hnr⟩ => by
    have hreq : ∀ ev ∈ evs, eventStepReq ev ≤ 44 ∧ eventStepAlign ev ≤ 16 :=
      fun ev hev => ⟨Nat.le_trans (hb ev hev).1 hmr, (hb ev hev).2⟩
    have hstep := stepEvents_noRealloc_le_44 evs st0 hreq hnr
    exact Nat.le_trans hstep (Nat.add_le_add_left (Nat.mul_le_mul_right 16659 hnf) _)

theorem boundedFreshEvs_of_boundedNonFreeEvs {k maxLen maxReq : Nat} {evs : List AllocEvent}
    (hb : BoundedNonFreeEvs k maxLen maxReq evs)
    (hnr : ∀ ev ∈ evs, ∀ al o n, ev ≠ .realloc al o n) :
    BoundedFreshEvs k maxLen maxReq evs :=
  ⟨hb.1, boundedNonFreeEvs_nonFreeBound k maxLen maxReq evs hb, hb.2.2, hnr⟩

theorem w3NonFreeCount_eq :
    ∀ evs : List AllocEvent, W3InitiateStagesPeak.nonFreeCount evs = nonFreeCount evs
  | [] => rfl
  | ev :: rest => by
      have ih := w3NonFreeCount_eq rest
      cases ev <;> simp [W3InitiateStagesPeak.nonFreeCount, nonFreeCount, ih]

theorem w3BoundedEvs_nonFreeBound (maxOps maxReq : Nat) :
    NonFreeBound (W3BoundedEvs maxOps maxReq) maxOps := by
  intro evs h
  rw [← w3NonFreeCount_eq]
  exact h.1

theorem w3BoundedEvs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (maxOps maxReq : Nat) :
    PhaseGroupSpec M (W3BoundedEvs maxOps maxReq) (3 * FineScale * maxOps) :=
  PhaseGroupSpec.of_nonFreeBound M (w3BoundedEvs_nonFreeBound maxOps maxReq)

theorem spqrNonFreeCount_eq :
    ∀ evs : List AllocEvent,
      LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.nonFreeCount evs = nonFreeCount evs
  | [] => rfl
  | ev :: rest => by
      have ih := spqrNonFreeCount_eq rest
      cases ev <;>
        simp [LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.nonFreeCount, nonFreeCount, ih]

theorem spqrBoundedEvs_nonFreeBound (maxAllocs maxReq : Nat) :
    NonFreeBound (SpqrBoundedEvs maxAllocs maxReq) maxAllocs := by
  intro evs h
  rw [← spqrNonFreeCount_eq]
  exact h.1

theorem spqrBoundedEvs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (maxAllocs maxReq : Nat) :
    PhaseGroupSpec M (SpqrBoundedEvs maxAllocs maxReq) (3 * FineScale * maxAllocs) :=
  PhaseGroupSpec.of_nonFreeBound M (spqrBoundedEvs_nonFreeBound maxAllocs maxReq)

theorem spqrFreshPlusRealloc_eq :
    ∀ evs : List AllocEvent, freshAllocCount evs + reallocCount evs = nonFreeCount evs
  | [] => rfl
  | ev :: rest => by
      have ih := spqrFreshPlusRealloc_eq rest
      cases ev <;> simp [freshAllocCount, reallocCount, nonFreeCount] <;> omega

theorem spqrBoundedTotalEvs_nonFreeBound (maxAllocs maxReallocs totalReq maxReq : Nat) :
    NonFreeBound (SpqrBoundedTotalEvs maxAllocs maxReallocs totalReq maxReq)
      (maxAllocs + maxReallocs) := by
  intro evs h
  rw [← spqrFreshPlusRealloc_eq]
  exact Nat.add_le_add h.1 h.2.1

theorem spqrBoundedTotalEvs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (maxAllocs maxReallocs totalReq maxReq : Nat) :
    PhaseGroupSpec M (SpqrBoundedTotalEvs maxAllocs maxReallocs totalReq maxReq)
      (3 * FineScale * (maxAllocs + maxReallocs)) :=
  PhaseGroupSpec.of_nonFreeBound M
    (spqrBoundedTotalEvs_nonFreeBound maxAllocs maxReallocs totalReq maxReq)

/-! ## `RawVec` Grows, Doubling Chains, and `BytesMerge` -/

theorem growOrReallocEvents_nonFreeBound (oldReq newReq align : Nat) :
    NonFreeBound (· = growOrReallocEvents oldReq newReq align) 1 := by
  rintro _ rfl
  unfold growOrReallocEvents
  split
  · rw [nonFreeCount_rustAllocEvents]
  · rw [nonFreeCount_rustReallocEvents]

theorem growOrReallocEvents_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (oldReq newReq align : Nat) :
    PhaseGroupSpec M (· = growOrReallocEvents oldReq newReq align) (3 * FineScale) := by
  simpa using PhaseGroupSpec.of_nonFreeBound M (growOrReallocEvents_nonFreeBound oldReq newReq align)

theorem rawVecGrowEvents_nonFreeBound (elemSz minCap align : Nat) (oldCap : BitVec 64) :
    NonFreeBound (· = rawVecGrowEvents elemSz minCap align oldCap) 1 := by
  rintro _ rfl
  unfold rawVecGrowEvents
  split
  · rw [nonFreeCount_rustAllocEvents]
  · rw [nonFreeCount_rustReallocEvents]

theorem rawVecGrowEnv_nonFreeBound (elemSz minCap align : Nat) (x : GrowOneCall) :
    NonFreeBound (RawVecGrowEnv elemSz minCap align x) 1 := by
  rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
  · rw [nonFreeCount_rustAllocEvents]
  · rw [nonFreeCount_rustReallocEvents]

theorem rawVecGrowEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (elemSz minCap align : Nat) (x : GrowOneCall) :
    PhaseGroupSpec M (RawVecGrowEnv elemSz minCap align x) (3 * FineScale) := by
  simpa using PhaseGroupSpec.of_nonFreeBound M (rawVecGrowEnv_nonFreeBound elemSz minCap align x)

theorem growOne104Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (cap : BitVec 64) :
    PhaseGroupSpec M (GrowOne104Env cap) (3 * FineScale) := by
  have hnf : NonFreeBound (GrowOne104Env cap) 1 := by
    intro evs h
    unfold GrowOne104Env at h
    rw [VecGrowCredit.growOne104Events_eq_rawVecGrowEvents] at h
    exact rawVecGrowEvents_nonFreeBound 104 4 8 cap evs h
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem growOneDirEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (x : GrowOneDirGhost) :
    PhaseGroupSpec M (GrowOneDirEnv x) (3 * FineScale) := by
  have hnf : NonFreeBound (GrowOneDirEnv x) 1 := by
    intro evs h
    unfold GrowOneDirEnv at h
    exact rawVecGrowEvents_nonFreeBound 48 4 8 x.cap evs h
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem growOneDirBytesEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (c : BitVec 64) :
    PhaseGroupSpec M (GrowOneDirBytesEnv c) (3 * FineScale) := by
  have hnf : NonFreeBound (GrowOneDirBytesEnv c) 1 := by
    intro evs h
    unfold GrowOneDirBytesEnv at h
    exact rawVecGrowEvents_nonFreeBound 48 4 8 c evs h
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem growOneSpeEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (cap : BitVec 64) :
    PhaseGroupSpec M (GrowOneSpeEnv cap) (3 * FineScale) := by
  have hnf : NonFreeBound (GrowOneSpeEnv cap) 1 :=
    fun evs h => rawVecGrowEvents_nonFreeBound 48 4 8 cap evs (growOneSpeEvents_eq_of_env h)
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem growOneU8Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (x : GrowOneCall) :
    PhaseGroupSpec M (GrowOneU8Env x) (3 * FineScale) :=
  (rawVecGrowEnv_groupSpec M 1 8 1 x).of_imp fun evs h =>
    (GrowOneU8Env_iff_rawVecGrowEnv x evs).mp h

theorem growOneVecU8Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (x : GrowOneCall) :
    PhaseGroupSpec M (GrowOneVecU8Env x) (3 * FineScale) :=
  rawVecGrowEnv_groupSpec M 24 4 8 x

theorem vecDequeGrowEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (x : VecDequeGrowGhost) :
    PhaseGroupSpec M (VecDequeGrowEnv x) (3 * FineScale) := by
  have hnf : NonFreeBound (VecDequeGrowEnv x) 1 := by
    intro evs h
    unfold VecDequeGrowEnv vecDequeGrowEvents at h
    subst h
    split
    · rw [nonFreeCount_rustAllocEvents]
    · rw [nonFreeCount_rustReallocEvents]
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem doReserveEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (x : DoReserveCall) :
    PhaseGroupSpec M (DoReserveEnv x) (3 * FineScale) := by
  have hnf : NonFreeBound (DoReserveEnv x) 1 := by
    intro evs h
    unfold DoReserveEnv doReserveEvents at h
    dsimp only at h
    subst h
    split
    · rw [nonFreeCount_rustAllocEvents]
    · rw [nonFreeCount_rustReallocEvents]
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem doublingCapsFrom_length (minCap : Nat) :
    ∀ j k : Nat, (doublingCapsFrom minCap j k).length = k
  | _, 0 => rfl
  | j, k + 1 => by
      simp [doublingCapsFrom, doublingCapsFrom_length minCap (j + 1) k]

theorem doublingCaps_length (minCap k : Nat) :
    (doublingCaps minCap k).length = k :=
  doublingCapsFrom_length minCap 0 k

theorem doublingCaps_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {Step : BitVec 64 → List AllocEvent → Prop} {g : Nat}
    (minCap k : Nat)
    (hstep : ∀ c ∈ doublingCaps minCap k, PhaseGroupSpec M (Step c) g) :
    PhaseGroupSpec M (IterSeqEnv Step (doublingCaps minCap k)) (k * g) := by
  have h := PhaseGroupSpec.iterSeq_const g (doublingCaps minCap k) hstep
  rw [doublingCaps_length] at h
  exact h

theorem doReserveClearEvents_nonFreeCount_le_one (valCap need : Nat) :
    nonFreeCount (doReserveClearEvents valCap need) ≤ 1 := by
  unfold doReserveClearEvents
  dsimp only
  split
  · rw [nonFreeCount_nil]; exact Nat.zero_le 1
  · split
    · rw [nonFreeCount_rustAllocEvents]
    · rw [nonFreeCount_rustReallocEvents]

theorem bytesMergeEnv_nonFreeBound (x : BytesMergeGhost) :
    NonFreeBound (BytesMergeEnv x) 2 := by
  intro evs h
  unfold BytesMergeEnv bytesMergeEventsCore at h
  subst h
  cases mergeBytes x.wt x.bs with
  | none =>
      rw [nonFreeCount_rustAllocEvents]
      omega
  | some p =>
      rcases p with ⟨v, _⟩
      dsimp only
      split
      · rw [nonFreeCount_nil]; exact Nat.zero_le 2
      · rw [nonFreeCount_append, nonFreeCount_append,
            nonFreeCount_rustAllocEvents, nonFreeCount_rustDeallocEvents]
        have h2 := doReserveClearEvents_nonFreeCount_le_one x.valCap.toNat v.length
        omega

theorem bytesMergeEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (x : BytesMergeGhost) :
    PhaseGroupSpec M (BytesMergeEnv x) (6 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M (bytesMergeEnv_nonFreeBound x)).mono (by decide)

/-- Scaled group bound (`33318` = `2 × 16659`, `0.5084` grp/field) for a fresh
(`valCap = 0`) successful `BytesMergeEnv` on a small field (`≤ 44 B`). -/
def deserSmallFieldFineGrpS : Nat := 33318

theorem bytesMergeEnv_fresh_ok_le_44_fine_groupSpec (x : BytesMergeGhost)
    (hcap : x.valCap = 0#64)
    (hok : ∃ v rest, mergeBytes x.wt x.bs = some (v, rest) ∧ v.length ≤ 44) :
    PhaseGroupSpec fineCostModel (BytesMergeEnv x) deserSmallFieldFineGrpS where
  groups_le st0 {evs} hevs := by
    rcases hok with ⟨v, rest, hm, hvlen⟩
    unfold BytesMergeEnv bytesMergeEventsCore at hevs
    rw [hm] at hevs
    dsimp only at hevs
    by_cases hv0 : v.length = 0
    · simp [hv0] at hevs
      subst hevs
      simp [AllocCostModel.stepEvents_nil]
    · simp only [hv0, ↓reduceIte] at hevs
      have hcap0 : x.valCap.toNat = 0 := by simp [hcap]
      rw [hcap0] at hevs
      have hrc : doReserveClearEvents 0 v.length = rustAllocEvents (reserveCap 0 0 v.length) 1 := by
        unfold doReserveClearEvents
        dsimp only
        have hnotle : ¬ (v.length ≤ 0) := by omega
        simp [hnotle]
      rw [hrc] at hevs
      have hres_le : reserveCap 0 0 v.length ≤ 44 := by
        unfold reserveCap
        omega
      have hp1 := fine_rustAlloc_le_44 (sz := v.length) (al := 1) (by omega) hvlen
      have hp2 := fine_rustAlloc_le_44 (sz := reserveCap 0 0 v.length) (al := 1) (by omega) hres_le
      have hp3 := PhaseGroupSpec.rustDealloc fineCostModel v.length 1
      have hp := phaseGroupSpec_append_eq fineCostModel
        (phaseGroupSpec_append_eq fineCostModel hp1 hp2) hp3
      have hbound := hp.groups_le st0 hevs
      unfold deserSmallFieldFineGrpS
      omega

theorem bytesMergeEnv_fresh_le_44_fine_groupSpec (x : BytesMergeGhost)
    (hcap : x.valCap = 0#64)
    (hsz : ∀ v rest, mergeBytes x.wt x.bs = some (v, rest) → v.length ≤ 44) :
    PhaseGroupSpec fineCostModel (BytesMergeEnv x) 43464 := by
  cases hm : mergeBytes x.wt x.bs with
  | none =>
      refine (fine_rustAlloc_le_108 (sz := 72) (al := 8) (by omega) (by omega)).of_imp ?_
      intro evs hevs
      unfold BytesMergeEnv bytesMergeEventsCore at hevs
      rw [hm] at hevs
      exact hevs
  | some p =>
      rcases p with ⟨v, rest⟩
      have hok : ∃ v' rest', mergeBytes x.wt x.bs = some (v', rest') ∧ v'.length ≤ 44 :=
        ⟨v, rest, hm, hsz v rest hm⟩
      refine (bytesMergeEnv_fresh_ok_le_44_fine_groupSpec x hcap hok).mono ?_
      unfold deserSmallFieldFineGrpS
      omega

/-! ## CLI Directory, Formatting, and File Read Helpers -/

theorem allocBytes1Events_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (bs : List (BitVec 8)) :
    PhaseGroupSpec M (· = allocBytes1Events bs) (3 * FineScale) := by
  unfold allocBytes1Events
  split
  · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  · exact PhaseGroupSpec.rustAlloc_any M bs.length 1

theorem allocBytes1Events_le_44_fine_groupSpec {bs : List (BitVec 8)} (hbs : bs.length ≤ 44) :
    PhaseGroupSpec fineCostModel (· = allocBytes1Events bs) 16659 := by
  unfold allocBytes1Events
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact fine_rustAlloc_le_44 (al := 1) (by omega) hbs

theorem cliDecimalEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (n : BitVec 32) :
    PhaseGroupSpec M (CliDecimalEnv n) (3 * FineScale) := by
  unfold CliDecimalEnv
  have hbr : PhaseGroupSpec M
      (fun evs => ∃ cap : Nat, (decimalText n.toNat).length ≤ cap ∧ cap ≤ 32 ∧
        SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs evs)
      (3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨cap, _, _, hseq⟩ =>
        (((PhaseGroupSpec.rustAlloc_any M cap 1).seq
          (PhaseGroupSpec.freeOnly M)).mono (Nat.le_of_eq (Nat.add_zero _))).groups_le st0 hseq }
  exact ((PhaseGroupSpec.nil M).or hbr).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem cliDecimalEnv_fine_groupSpec (n : BitVec 32) :
    PhaseGroupSpec fineCostModel (CliDecimalEnv n) 16659 := by
  unfold CliDecimalEnv
  have hbr : PhaseGroupSpec fineCostModel
      (fun evs => ∃ cap : Nat, (decimalText n.toNat).length ≤ cap ∧ cap ≤ 32 ∧
        SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs evs)
      16659 :=
    { groups_le := fun st0 {_} ⟨cap, _, hle32, hseq⟩ =>
        (((fine_rustAlloc_le_44 (sz := cap) (al := 1) (by omega) (by omega)).seq
          (PhaseGroupSpec.freeOnly fineCostModel)).mono
          (Nat.le_of_eq (Nat.add_zero _))).groups_le st0 hseq }
  exact ((PhaseGroupSpec.nil fineCostModel).or hbr).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem cliPathEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dir name : List (BitVec 8)) :
    PhaseGroupSpec M (CliPathEnv dir name) (9 * FineScale) := by
  unfold CliPathEnv
  dsimp only
  split
  · exact (allocBytes1Events_groupSpec M name).mono (by decide)
  · have h1 := PhaseGroupSpec.rustAlloc_any M dir.length 1
    have h2 := PhaseGroupSpec.rustRealloc_any M dir.length (reserveCap dir.length dir.length 1) 1
    have h3 : PhaseGroupSpec M
        (if decide (reserveCap dir.length dir.length 1 - (dir.length + 1) < name.length) then
           (· = rustReallocEvents (reserveCap dir.length dir.length 1)
             (if decide (reserveCap dir.length dir.length 1 - (dir.length + 1) < name.length) then
                reserveCap (reserveCap dir.length dir.length 1) (dir.length + 1) name.length
              else reserveCap dir.length dir.length 1) 1)
         else (· = []))
        (3 * FineScale) := by
      split
      · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
      · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    exact ((h1.concat h2).concat h3).mono (by decide)

theorem cliAddrTextEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (g : AddrGhost) :
    PhaseGroupSpec M (CliAddrTextEnv g) (3 * FineScale) := by
  unfold CliAddrTextEnv
  dsimp only
  exact phaseGroupSpec_exists_guarded M fun cap _ =>
    ((PhaseGroupSpec.rustAlloc_any M cap 1).seq (PhaseGroupSpec.freeOnly M)).mono
      (Nat.le_of_eq (Nat.add_zero _))

private theorem cliIoCapEventsGo_nonFreeCount :
    ∀ (prev : Nat) (cs : List Nat),
      nonFreeCount (cliIoCapEventsGo prev cs) ≤ cs.length
  | _, [] => by rw [cliIoCapEventsGo, nonFreeCount_nil]; exact Nat.zero_le 0
  | prev, c :: rest => by
      simp only [cliIoCapEventsGo, nonFreeCount_append, List.length_cons]
      have h1 := nonFreeCount_rustReallocEvents prev c 1
      have ih := cliIoCapEventsGo_nonFreeCount c rest
      omega

private theorem cliIoCapEvents_nonFreeCount :
    ∀ cs : List Nat, nonFreeCount (cliIoCapEvents cs) ≤ cs.length
  | [] => by rw [cliIoCapEvents, nonFreeCount_nil]; exact Nat.zero_le 0
  | c0 :: cs => by
      simp only [cliIoCapEvents, nonFreeCount_append, List.length_cons]
      have h1 := nonFreeCount_rustAllocEvents c0 1
      have h2 := cliIoCapEventsGo_nonFreeCount c0 cs
      omega

theorem cliIoReadStdinEnv_nonFreeBound (r : Nat) :
    NonFreeBound (CliIoReadStdinEnv r) 9 := by
  intro evs h
  unfold CliIoReadStdinEnv at h
  subst h
  have h1 := cliIoCapEvents_nonFreeCount (cliIoReadCaps 8 r)
  have h2 : (cliIoReadCaps 8 r).length ≤ 9 := by
    unfold cliIoReadCaps
    split
    · exact Nat.zero_le 9
    · simp only [List.length_map, List.length_range]
      have hidx := cliIoCapIdx_le 8 r
      omega
  exact Nat.le_trans h1 h2

theorem cliIoReadStdinEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (r : Nat) :
    PhaseGroupSpec M (CliIoReadStdinEnv r) (27 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M (cliIoReadStdinEnv_nonFreeBound r)).mono (by decide)

theorem cliIoReadFileEnv_nonFreeBound (r : Nat) :
    NonFreeBound (CliIoReadFileEnv r) 10 := by
  intro evs h
  unfold CliIoReadFileEnv at h
  subst h
  have h1 := cliIoCapEvents_nonFreeCount (cliIoReadCaps 9 r)
  have h2 : (cliIoReadCaps 9 r).length ≤ 10 := by
    unfold cliIoReadCaps
    split
    · exact Nat.zero_le 10
    · simp only [List.length_map, List.length_range]
      have hidx := cliIoCapIdx_le 9 r
      omega
  exact Nat.le_trans h1 h2

theorem cliIoReadFileEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (r : Nat) :
    PhaseGroupSpec M (CliIoReadFileEnv r) (30 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M (cliIoReadFileEnv_nonFreeBound r)).mono (by decide)

theorem readFileRuleEnv_nonFreeBound (rd : ReadRule) (files : FsFiles) (path : List (BitVec 8)) :
    NonFreeBound (ReadFileRuleEnv rd files path) 10 := by
  intro evs h
  unfold ReadFileRuleEnv at h
  cases hres : rd files path with
  | error u =>
    rw [hres] at h
    dsimp only at h
    subst h
    rw [nonFreeCount_nil]
    exact Nat.zero_le 10
  | ok bs =>
    rw [hres] at h
    dsimp only at h
    rcases h with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · unfold allocBytes1Events
      split
      · rw [nonFreeCount_nil]; exact Nat.zero_le 10
      · rw [nonFreeCount_rustAllocEvents]; decide
    · rw [nonFreeCount_nil]; exact Nat.zero_le 10
    · rw [specCliIoReadSchedule_events_eq 9 bs.length]
      exact cliIoReadFileEnv_nonFreeBound bs.length _ rfl
    · rw [nonFreeCount_append, nonFreeCount_rustDeallocEvents, Nat.add_zero,
          specCliIoReadSchedule_events_eq 9 2097152]
      exact cliIoReadFileEnv_nonFreeBound 2097152 _ rfl

theorem readFileRuleEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (rd : ReadRule) (files : FsFiles) (path : List (BitVec 8)) :
    PhaseGroupSpec M (ReadFileRuleEnv rd files path) (30 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M (readFileRuleEnv_nonFreeBound rd files path)).mono (by decide)

theorem cliDirGetEnv_of_io_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {IoEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop} {g_io : Nat}
    (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    (hio : PhaseGroupSpec M (IoEnv files (pathOf dir.path name)) g_io) :
    PhaseGroupSpec M (CliDirGetEnv IoEnv files dir name) (9 * FineScale + g_io) := by
  unfold CliDirGetEnv
  have hhit : PhaseGroupSpec M
      (fun evs => ∃ k v, (k, v) ∈ dir.changed ∧ k = name ∧ evs = allocBytes1Events v)
      (3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨_, v, _, _, heq⟩ =>
        (allocBytes1Events_groupSpec M v).groups_le st0 heq }
  have hmiss : PhaseGroupSpec M
      (SeqEnv (CliPathEnv dir.path name)
        (SeqEnv (IoEnv files (pathOf dir.path name)) FreeOnlyEvs))
      (9 * FineScale + g_io) :=
    ((cliPathEnv_groupSpec M dir.path name).seq
      (hio.seq (PhaseGroupSpec.freeOnly M))).mono
      (by rw [Nat.add_zero])
  have hle39 : 3 * FineScale ≤ 9 * FineScale := by decide
  exact (hhit.or hmiss).mono
    (Nat.max_le.mpr ⟨Nat.le_trans hle39 (Nat.le_add_right _ _), Nat.le_refl _⟩)

theorem cliDirGetEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (rd : ReadRule) (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec M (CliDirGetEnv (ReadFileRuleEnv rd) files dir name) (39 * FineScale) :=
  (cliDirGetEnv_of_io_groupSpec M files dir name
    (readFileRuleEnv_groupSpec M rd files _)).mono (by decide)

theorem cliDirPutEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dir : DirGhost) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec M (CliDirPutEnv dir name bytes) (3 * FineScale) := by
  unfold CliDirPutEnv
  have hgrow := phaseGroupSpec_exists_guarded M
    (P := fun x : GrowOneDirGhost => x.cap.toNat ≤ max 4 (2 * dir.changed.length))
    (fun x _ => growOneDirEnv_groupSpec M x)
  exact ((PhaseGroupSpec.freeOnly M).or hgrow).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem cliDirPutStrEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dir : DirGhost) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec M (CliDirPutStrEnv dir name bytes) (6 * FineScale) :=
  ((allocBytes1Events_groupSpec M name).seq
    (cliDirPutEnv_groupSpec M dir name bytes)).mono (by decide)

theorem cliDirPutStrEnv_le_44_fine_groupSpec (dir : DirGhost) {name : List (BitVec 8)}
    (bytes : List (BitVec 8)) (hname : name.length ≤ 44) :
    PhaseGroupSpec fineCostModel (CliDirPutStrEnv dir name bytes) (16659 + 3 * FineScale) :=
  (allocBytes1Events_le_44_fine_groupSpec hname).seq (cliDirPutEnv_groupSpec fineCostModel dir name bytes)

/-! ## `SessionRecord::deserialize` Per-Size-Class Group Bounds -/

/-- Tight `fineCostModel` scaled group bound (`68,702,034` = `1,049` groups at `(2000, 10)`) for
deserializing one receiver chain: `3` small scalar/key fields (`srk`, `priv`, `chainKey`),
`≤ maxKeys` `32 B` out-of-order message-key seeds (`33318` = `0.5084` grp/seed), and `≤ maxGrows`
`Vec<MessageKey>` doubling grows. -/
def deserChainFineGrpS (maxKeys maxGrows : Nat) : Nat :=
  3 * deserSmallFieldFineGrpS + maxKeys * deserSmallFieldFineGrpS + maxGrows * (3 * FineScale)

/-- Tight `fineCostModel` scaled group bound (`345,022,998` = `5,265` groups) for deserializing one
`SessionStructure`: `3` header small fields, `≤ 5` chains (`≤ 2000` seeds, `≤ 10` grows each),
`≤ 2` `receiverChains` `Vec` grows, `7` scalar/sender/pending small fields, and `2` large/general
`BytesMerge` fields (`kyber`, `pqRatchetState`). -/
def deserSessionFineGrpS : Nat :=
  3 * deserSmallFieldFineGrpS + 5 * deserChainFineGrpS 2000 10 +
    2 * (3 * FineScale) + 7 * deserSmallFieldFineGrpS + 2 * (6 * FineScale)

/-- Tight `fineCostModel` scaled group bound (`347,382,294` = `5,301` groups) for
`SessionRecord::deserialize`: current session (`deserSessionFineGrpS`), `≤ 5` archived session
`BytesMerge` fields, and `≤ 2` `previousSessions` `Vec` grows. -/
def deserRecordFineGrpS : Nat :=
  deserSessionFineGrpS + 5 * (6 * FineScale) + 2 * (3 * FineScale)

theorem deserSmallFields_fine_groupSpec
    {Step : BytesMergeGhost → List AllocEvent → Prop} (xs : List BytesMergeGhost)
    (hstep : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (Step x) deserSmallFieldFineGrpS) :
    PhaseGroupSpec fineCostModel (IterSeqEnv Step xs) (xs.length * deserSmallFieldFineGrpS) :=
  PhaseGroupSpec.iterSeq_const deserSmallFieldFineGrpS xs hstep

theorem deserChain_fine_groupSpec
    {E_hdr E_keys E_grows : List AllocEvent → Prop} {maxKeys maxGrows : Nat}
    (hhdr : PhaseGroupSpec fineCostModel E_hdr (3 * deserSmallFieldFineGrpS))
    (hkeys : PhaseGroupSpec fineCostModel E_keys (maxKeys * deserSmallFieldFineGrpS))
    (hgrows : PhaseGroupSpec fineCostModel E_grows (maxGrows * (3 * FineScale))) :
    PhaseGroupSpec fineCostModel
      (SeqEnv E_hdr (SeqEnv E_keys (SeqEnv E_grows FreeOnlyEvs)))
      (deserChainFineGrpS maxKeys maxGrows) := by
  refine (hhdr.seq (hkeys.seq (hgrows.seq (PhaseGroupSpec.freeOnly fineCostModel)))).mono ?_
  unfold deserChainFineGrpS
  omega

theorem deserSession_fine_groupSpec
    {E_hdr E_chains E_rcGrows E_tailSmall E_large : List AllocEvent → Prop}
    (hhdr : PhaseGroupSpec fineCostModel E_hdr (3 * deserSmallFieldFineGrpS))
    (hchains : PhaseGroupSpec fineCostModel E_chains (5 * deserChainFineGrpS 2000 10))
    (hrc : PhaseGroupSpec fineCostModel E_rcGrows (2 * (3 * FineScale)))
    (htail : PhaseGroupSpec fineCostModel E_tailSmall (7 * deserSmallFieldFineGrpS))
    (hlarge : PhaseGroupSpec fineCostModel E_large (2 * (6 * FineScale))) :
    PhaseGroupSpec fineCostModel
      (SeqEnv E_hdr (SeqEnv E_chains (SeqEnv E_rcGrows
        (SeqEnv E_tailSmall (SeqEnv E_large FreeOnlyEvs)))))
      deserSessionFineGrpS :=
  (hhdr.seq (hchains.seq (hrc.seq (htail.seq
    (hlarge.seq (PhaseGroupSpec.freeOnly fineCostModel)))))).mono (by decide)

theorem deserRecord_fine_groupSpec
    {E_cur E_prev E_prevGrows : List AllocEvent → Prop}
    (hcur : PhaseGroupSpec fineCostModel E_cur deserSessionFineGrpS)
    (hprev : PhaseGroupSpec fineCostModel E_prev (5 * (6 * FineScale)))
    (hgrows : PhaseGroupSpec fineCostModel E_prevGrows (2 * (3 * FineScale))) :
    PhaseGroupSpec fineCostModel
      (SeqEnv E_cur (SeqEnv E_prev (SeqEnv E_prevGrows FreeOnlyEvs)))
      deserRecordFineGrpS :=
  (hcur.seq (hprev.seq (hgrows.seq (PhaseGroupSpec.freeOnly fineCostModel)))).mono (by decide)


/-! ## `SessionClone`, `SessionRecord::serialize`, and `StoreKit` Polls -/

private theorem snd_mem_of_mem_zip {α β : Type} :
    ∀ {xs : List α} {ys : List β} {p : α × β}, p ∈ xs.zip ys → p.2 ∈ ys
  | _ :: _, _ :: _, _, h => by
    rcases List.mem_cons.mp h with rfl | hrest
    · exact List.Mem.head _
    · exact List.Mem.tail _ (snd_mem_of_mem_zip hrest)

private theorem zip_length_le_right {α β : Type} :
    ∀ (xs : List α) (ys : List β), (xs.zip ys).length ≤ ys.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.le_refl 0
  | _ :: xs, _ :: ys => Nat.succ_le_succ (zip_length_le_right xs ys)

private theorem flatMap_eq_groupSpec {α : Type} (M : AllocCostModel) [HasFineGroupCredit M]
    (f : α → List AllocEvent) (g : Nat) :
    ∀ (xs : List α),
      (∀ x ∈ xs, PhaseGroupSpec M (· = f x) g) →
      PhaseGroupSpec M (· = xs.flatMap f) (xs.length * g)
  | [], _ => by simpa using PhaseGroupSpec.nil M
  | x :: xs, h => by
      have hx := h x (List.Mem.head _)
      have hxs := flatMap_eq_groupSpec M f g xs (fun y hy => h y (List.Mem.tail _ hy))
      refine (phaseGroupSpec_append_eq M hx hxs).mono ?_
      simp [List.length_cons, Nat.succ_mul]
      omega

private theorem nonFreeCount_flatMap_eq_zero {α : Type} (f : α → List AllocEvent) :
    ∀ (xs : List α), (∀ x ∈ xs, nonFreeCount (f x) = 0) → nonFreeCount (xs.flatMap f) = 0
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.flatMap_cons, nonFreeCount_append]
      rw [h x (List.Mem.head _), nonFreeCount_flatMap_eq_zero f xs (fun y hy => h y (List.Mem.tail _ hy))]

theorem vecCloneEvents_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (v : VecGhost) :
    PhaseGroupSpec M (· = vecCloneEvents v) (3 * FineScale) := by
  unfold vecCloneEvents
  split
  · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  · exact PhaseGroupSpec.rustAlloc_any M v.bytes.length 1

theorem vecCloneEvents_le_44_fine_groupSpec {v : VecGhost} (hlen : v.bytes.length ≤ 44) :
    PhaseGroupSpec fineCostModel (· = vecCloneEvents v) 16659 := by
  unfold vecCloneEvents
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact fine_rustAlloc_le_44 (al := 1) (by omega) hlen

theorem optTailCloneEvents_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (o : Option TailVecGhost) :
    PhaseGroupSpec M (· = optTailCloneEvents o) (3 * FineScale) := by
  cases o with
  | none => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  | some g => exact vecCloneEvents_groupSpec M g.vec

theorem optTailCloneEvents_le_44_fine_groupSpec {o : Option TailVecGhost}
    (hlen : optTailCloneLen o ≤ 44) :
    PhaseGroupSpec fineCostModel (· = optTailCloneEvents o) 16659 := by
  cases o with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | some g => exact vecCloneEvents_le_44_fine_groupSpec hlen

/-- Tight `fineCostModel` scaled group bound (`33,547,926` = `512` groups) for cloning one
receiver chain under `SessionCloneDom` (`srk ≤ 44`, `priv = 0`, `≤ 2000` `32 B` seeds). -/
def chainCloneDomFineGrpS : Nat :=
  16659 + 16659 + 3 * FineScale + 2000 * 16659

/-- Tight `fineCostModel` scaled group bound (`49,977` = `< 1` group) for cloning `SenderChain`. -/
def senderChainCloneDomFineGrpS : Nat := 3 * 16659

/-- Tight `fineCostModel` scaled group bound (`168,462,726` = `2,571` groups) for
`SessionStructure::clone` (`SegCloneEnv G ses.state`) under `GhostCloneValid` + `SessionCloneDom`. -/
def segCloneDomFineGrpS : Nat :=
  16659 + 16659 + 16659 + senderChainCloneDomFineGrpS +
    (3 * FineScale + 5 * chainCloneDomFineGrpS) +
    16659 + 3 * FineScale + 16659 + 3 * FineScale

theorem chainCloneEnv_dom_fine_groupSpec {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length ≤ 44)
    (hpriv : gc.1.priv.bytes.length = 0)
    (hmk : gc.2.messageKeys.length ≤ 2000)
    (hseeds : ∀ k ∈ gc.2.messageKeys, k.seed.length ≤ 44) :
    PhaseGroupSpec fineCostModel (ChainCloneEnv gc) chainCloneDomFineGrpS := by
  have h1 := vecCloneEvents_le_44_fine_groupSpec hsrk
  have h2 : PhaseGroupSpec fineCostModel (· = vecCloneEvents gc.1.priv) 0 := by
    unfold vecCloneEvents
    rw [hpriv]
    simpa using PhaseGroupSpec.nil fineCostModel
  have h3 : PhaseGroupSpec fineCostModel
      (· = match gc.2.chainKey with | none => [] | some _ => rustAllocEvents 32 1) 16659 := by
    cases gc.2.chainKey with
    | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | some _ => exact fine_rustAlloc_le_44 (al := 1) (by omega) (by omega)
  have h4 : PhaseGroupSpec fineCostModel
      (· = if gc.2.messageKeys = [] then []
           else rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
             gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1))
      (3 * FineScale + 2000 * 16659) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · have hbuf := PhaseGroupSpec.rustAlloc_any fineCostModel (104 * gc.2.messageKeys.length) 8
      have hs := flatMap_eq_groupSpec fineCostModel
        (fun mkg : MessageKeyGenerator => rustAllocEvents mkg.seed.length 1) 16659
        gc.2.messageKeys
        (fun mkg hm => fine_rustAlloc_le_44 (al := 1) (by omega) (hseeds mkg hm))
      have hmul : gc.2.messageKeys.length * 16659 ≤ 2000 * 16659 :=
        Nat.mul_le_mul_right 16659 hmk
      exact (phaseGroupSpec_append_eq fineCostModel hbuf hs).mono (Nat.add_le_add_left hmul _)
  have hall := phaseGroupSpec_append_eq fineCostModel
    (phaseGroupSpec_append_eq fineCostModel (phaseGroupSpec_append_eq fineCostModel h1 h2) h3) h4
  exact hall.mono (by decide)

theorem senderChainCloneEnv_dom_fine_groupSpec {gs : SenderChainGhost} (sc : SenderChain)
    (hsrk : gs.srk.bytes.length ≤ 44) (hpriv : gs.priv.bytes.length ≤ 44) :
    PhaseGroupSpec fineCostModel (SenderChainCloneEnv gs sc) senderChainCloneDomFineGrpS := by
  unfold SenderChainCloneEnv senderChainCloneEvents chainCloneEvents senderChainAsProtoGhost
  dsimp only
  have h1 := vecCloneEvents_le_44_fine_groupSpec hsrk
  have h2 := vecCloneEvents_le_44_fine_groupSpec hpriv
  have h3 := fine_rustAlloc_le_44 (sz := 32) (al := 1) (by omega) (by omega)
  have h4 : PhaseGroupSpec fineCostModel (· = ([] : List AllocEvent)) 0 :=
    PhaseGroupSpec.nil fineCostModel
  have hall := phaseGroupSpec_append_eq fineCostModel
    (phaseGroupSpec_append_eq fineCostModel (phaseGroupSpec_append_eq fineCostModel h1 h2) h3) h4
  exact hall.mono (by decide)

theorem segCloneEnv_ghostValid_dom_fine_groupSpec {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : GhostCloneValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G ses.state) segCloneDomFineGrpS := by
  have hloc := vecCloneEvents_le_44_fine_groupSpec (v := G.localIk) (by rw [hgv.localIk_len]; omega)
  have hrem := vecCloneEvents_le_44_fine_groupSpec (v := G.remoteIk) (Nat.le_trans hgv.remoteIk_len (by omega))
  have hroot := fine_rustAlloc_le_44 (sz := 32) (al := 1) (by omega) (by omega)
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, ses.state.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => [])
      senderChainCloneDomFineGrpS := by
    rcases hgv.sender_ok with ⟨hn1, hn2⟩ | ⟨gs, sc, hgs, hsc, hsrk, hpriv⟩
    · rw [hn1, hn2]
      exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rw [hgs, hsc]
      exact senderChainCloneEnv_dom_fine_groupSpec sc (by omega) (by omega)
  have hrc : PhaseGroupSpec fineCostModel
      (· = if ses.state.receiverChains = [] then []
           else rustAllocEvents (104 * ses.state.receiverChains.length) 8 ++
             (G.chains.zip ses.state.receiverChains).flatMap chainCloneEvents)
      (3 * FineScale + 5 * chainCloneDomFineGrpS) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · have hbuf := PhaseGroupSpec.rustAlloc_any fineCostModel (104 * ses.state.receiverChains.length) 8
      have hch := flatMap_eq_groupSpec fineCostModel chainCloneEvents chainCloneDomFineGrpS
        (G.chains.zip ses.state.receiverChains)
        (fun gc hmem => by
          obtain ⟨hsrk, hpriv, hmk⟩ := hgv.chains_ok gc hmem
          have hs32 := hdom.seeds32 gc.2 (snd_mem_of_mem_zip hmem)
          exact chainCloneEnv_dom_fine_groupSpec (by omega) hpriv hmk
            (fun k hk => by rw [hs32 k hk]; omega))
      have hzlen : (G.chains.zip ses.state.receiverChains).length ≤ 5 :=
        Nat.le_trans (zip_length_le_right _ _) hdom.rc_len
      have hmul : (G.chains.zip ses.state.receiverChains).length * chainCloneDomFineGrpS ≤
          5 * chainCloneDomFineGrpS :=
        Nat.mul_le_mul_right chainCloneDomFineGrpS hzlen
      exact (phaseGroupSpec_append_eq fineCostModel hbuf hch).mono (Nat.add_le_add_left hmul _)
  have hpend := optTailCloneEvents_le_44_fine_groupSpec (Nat.le_trans hgv.pending_len (by omega))
  have hkyb := optTailCloneEvents_groupSpec fineCostModel G.kyber
  have halice : PhaseGroupSpec fineCostModel (· = vecCloneEvents G.alice) 16659 :=
    vecCloneEvents_le_44_fine_groupSpec (by rw [hgv.alice_eq]; exact Nat.le_trans hdom.alice_len (by omega))
  have hpq : PhaseGroupSpec fineCostModel
      (· = if ses.state.pqRatchetState.length = 0 then []
           else rustAllocEvents ses.state.pqRatchetState.length 1)
      (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel ses.state.pqRatchetState.length 1
  have s1 := phaseGroupSpec_append_eq fineCostModel hloc hrem
  have s2 := phaseGroupSpec_append_eq fineCostModel s1 hroot
  have s3 := phaseGroupSpec_append_eq fineCostModel s2 hsnd
  have s4 := phaseGroupSpec_append_eq fineCostModel s3 hrc
  have s5 := phaseGroupSpec_append_eq fineCostModel s4 hpend
  have s6 := phaseGroupSpec_append_eq fineCostModel s5 hkyb
  have s7 := phaseGroupSpec_append_eq fineCostModel s6 halice
  have s8 := phaseGroupSpec_append_eq fineCostModel s7 hpq
  unfold SegCloneEnv segCloneEvents
  exact s8.mono (by decide)

theorem segCloneEnv_dom_fine_groupSpec {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G ses.state) segCloneDomFineGrpS :=
  segCloneEnv_ghostValid_dom_fine_groupSpec (ghostCloneValid_of_sessionGhostValid hgv) hdom

private theorem optDealloc_nonFreeCount_zero (p : Prop) [Decidable p] (sz al : Nat) :
    nonFreeCount (if p then [] else rustDeallocEvents sz al) = 0 := by
  split
  · rfl
  · exact nonFreeCount_rustDeallocEvents sz al

private theorem dropClonedMessageKeysEvents_nonFreeCount (mks : List MessageKeyGenerator) :
    nonFreeCount (dropClonedMessageKeysEvents mks) = 0 := by
  unfold dropClonedMessageKeysEvents
  split
  · rfl
  · rw [nonFreeCount_append, nonFreeCount_rustDeallocEvents]
    have hf := nonFreeCount_flatMap_eq_zero
      (fun mkg : MessageKeyGenerator =>
        if mkg.seed.length = 0 then [] else rustDeallocEvents mkg.seed.length 1)
      mks
      (fun mkg _ => optDealloc_nonFreeCount_zero (mkg.seed.length = 0) mkg.seed.length 1)
    omega

private theorem dropClonedChainEvents_nonFreeCount (gc : ChainGhost × ReceiverChain) :
    nonFreeCount (dropClonedChainEvents gc) = 0 := by
  unfold dropClonedChainEvents
  rw [nonFreeCount_append, nonFreeCount_append, nonFreeCount_append,
      optDealloc_nonFreeCount_zero, optDealloc_nonFreeCount_zero,
      dropClonedMessageKeysEvents_nonFreeCount]
  cases gc.2.chainKey <;> simp [nonFreeCount_nil, nonFreeCount_rustDeallocEvents]

theorem dropClonedSessionEvents_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    PhaseGroupSpec M (· = dropClonedSessionEvents G st) 0 := by
  have hnf : NonFreeBound (· = dropClonedSessionEvents G st) 0 := by
    rintro _ rfl
    unfold dropClonedSessionEvents
    repeat rw [nonFreeCount_append]
    have hrc : nonFreeCount
        (if st.receiverChains = [] then []
         else (G.chains.zip st.receiverChains).flatMap dropClonedChainEvents ++
           rustDeallocEvents (104 * st.receiverChains.length) 8) = 0 := by
      split
      · rfl
      · rw [nonFreeCount_append, nonFreeCount_rustDeallocEvents,
            nonFreeCount_flatMap_eq_zero dropClonedChainEvents _
              (fun gc _ => dropClonedChainEvents_nonFreeCount gc)]
    cases G.sender <;> cases st.senderChain <;>
      simp only [optDealloc_nonFreeCount_zero, nonFreeCount_rustDeallocEvents,
        nonFreeCount_nil, dropClonedChainEvents_nonFreeCount, hrc, Nat.add_zero] <;>
      exact Nat.le_refl 0
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem dropVecVecClone1Events_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (enc : List (BitVec 8)) :
    PhaseGroupSpec M (· = dropVecVecClone1Events enc) 0 := by
  have hnf : NonFreeBound (· = dropVecVecClone1Events enc) 0 := by
    rintro _ rfl
    unfold dropVecVecClone1Events
    rw [nonFreeCount_append, optDealloc_nonFreeCount_zero, nonFreeCount_rustDeallocEvents]
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem vecVecClone1Events_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (enc : List (BitVec 8)) :
    PhaseGroupSpec M (· = vecVecClone1Events enc) (6 * FineScale) := by
  have h24 := PhaseGroupSpec.rustAlloc_any M 24 8
  have henc : PhaseGroupSpec M
      (· = if enc.length = 0 then [] else rustAllocEvents enc.length 1) (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any M enc.length 1
  exact (phaseGroupSpec_append_eq M h24 henc).mono (by decide)

theorem vecVecClone1Events_fine_groupSpec (enc : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (· = vecVecClone1Events enc) (11056 + 3 * FineScale) := by
  have h24 := fine_rustAlloc_le_28 (sz := 24) (al := 8) (by omega) (by omega)
  have henc : PhaseGroupSpec fineCostModel
      (· = if enc.length = 0 then [] else rustAllocEvents enc.length 1) (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel enc.length 1
  exact phaseGroupSpec_append_eq fineCostModel h24 henc

/-- Tight `fineCostModel` scaled group bound (`168,659,334` = `2,574` groups) for `0`-prev
`SessionRecord::serialize`. -/
def recordSerializeDomFineGrpS : Nat := segCloneDomFineGrpS + 3 * FineScale

/-- Tight `fineCostModel` scaled group bound (`168,866,998` = `2,577` groups) for `prev1`
`SessionRecord::serialize`. -/
def serializePrev1DomFineGrpS : Nat := segCloneDomFineGrpS + (11056 + 3 * FineScale) + 3 * FineScale

theorem serializeSomeCancelEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {g_cl : Nat}
    (hcl : PhaseGroupSpec M (SegCloneEnv G sess.state) g_cl) :
    PhaseGroupSpec M (SerializeSomeCancelEnv G sess) (g_cl + 3 * FineScale) := by
  unfold SerializeSomeCancelEnv
  have hout := PhaseGroupSpec.rustAlloc_any M (lenField 1 (encSessionMem G sess)).length 1
  have hdrop := dropClonedSessionEvents_groupSpec M G sess.state
  exact ((hcl.concat hout).concat hdrop).mono (by rw [Nat.add_zero])

theorem serializeSomeSeqFreeEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {g_cl : Nat}
    (hcl : PhaseGroupSpec M (SegCloneEnv G sess.state) g_cl) :
    PhaseGroupSpec M (SerializeSomeSeqFreeEnv G sess) (g_cl + 3 * FineScale) := by
  unfold SerializeSomeSeqFreeEnv
  have hout := PhaseGroupSpec.rustAlloc_any M (lenField 1 (encSessionMem G sess)).length 1
  exact (hcl.seq (hout.seq (PhaseGroupSpec.freeOnly M))).mono (by rw [Nat.add_zero])

theorem recordSerializeCancelEnv_dom_fine_groupSpec {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hgv : RecordGhostValid g r)
    (hdom : ∀ ses, r.currentSession = some ses → SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g r) recordSerializeDomFineGrpS := by
  unfold RecordSerializeCancelEnv recordSerializeDomFineGrpS
  cases hgc : g.cur <;> cases hrc : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G ses
    have hgv' : SessionGhostValid G ses := by simpa [RecordGhostValid, hgc, hrc] using hgv
    exact serializeSomeCancelEnv_groupSpec fineCostModel
      (segCloneEnv_dom_fine_groupSpec hgv' (hdom ses hrc))

theorem recordSerializeSeqFreeEnv_dom_fine_groupSpec {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hgv : RecordGhostValid g r)
    (hdom : ∀ ses, r.currentSession = some ses → SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (RecordSerializeSeqFreeEnv g r) recordSerializeDomFineGrpS := by
  unfold RecordSerializeSeqFreeEnv recordSerializeDomFineGrpS
  cases hgc : g.cur <;> cases hrc : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G ses
    have hgv' : SessionGhostValid G ses := by simpa [RecordGhostValid, hgc, hrc] using hgv
    exact serializeSomeSeqFreeEnv_groupSpec fineCostModel
      (segCloneEnv_dom_fine_groupSpec hgv' (hdom ses hrc))

theorem serializePrev1CancelEnv_dom_fine_groupSpec {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} (enc : List (BitVec 8))
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv G ses enc) serializePrev1DomFineGrpS := by
  unfold SerializePrev1CancelEnv
  have hcl := segCloneEnv_dom_fine_groupSpec hgv hdom
  have hvv := vecVecClone1Events_fine_groupSpec enc
  have hout := PhaseGroupSpec.rustAlloc_any fineCostModel (encodeRecordPrev1Mem G ses enc).length 1
  have hd1 := dropClonedSessionEvents_groupSpec fineCostModel G ses.state
  have hd2 := dropVecVecClone1Events_groupSpec fineCostModel enc
  exact (((hcl.concat hvv).concat hout).concat (hd1.concat hd2)).mono (by decide)

theorem serializePrev1SeqFreeEnv_dom_fine_groupSpec {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} (enc : List (BitVec 8))
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (SerializePrev1SeqFreeEnv G ses enc) serializePrev1DomFineGrpS := by
  unfold SerializePrev1SeqFreeEnv
  have hcl := segCloneEnv_dom_fine_groupSpec hgv hdom
  have hvv := vecVecClone1Events_fine_groupSpec enc
  have hout := PhaseGroupSpec.rustAlloc_any fineCostModel (encodeRecordPrev1Mem G ses enc).length 1
  exact (hcl.seq (hvv.seq (hout.seq (PhaseGroupSpec.freeOnly fineCostModel)))).mono (by decide)

theorem cliSessLoadPollEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop} {g_deser : Nat}
    (files : FsFiles) (dir : DirGhost) (peer : AddrGhost)
    (hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec M (DeserEnv bs) g_deser) :
    PhaseGroupSpec M (CliSessLoadPollEnv rd DeserEnv files dir peer)
      (42 * FineScale + g_deser) := by
  unfold CliSessLoadPollEnv
  have had := cliAddrTextEnv_groupSpec M peer
  have hget := cliDirGetEnv_groupSpec M rd files dir (addressText peer.val)
  have hex := phaseGroupSpec_exists_guarded M (P := fun bs : List (BitVec 8) => bs.length ≤ 2097152) hdeser
  have hopt : PhaseGroupSpec M _ g_deser :=
    ((PhaseGroupSpec.nil M).or hex).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  refine (had.seq (hget.seq (hopt.seq (PhaseGroupSpec.freeOnly M)))).mono ?_
  have hc : 3 * FineScale + 39 * FineScale = 42 * FineScale := by decide
  rw [Nat.add_zero, ← Nat.add_assoc, hc]

theorem cliSessStorePollEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dir : DirGhost) (peer : AddrGhost)
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))} {g_ser : Nat}
    (hser : PhaseGroupSpec M (RecordSerializeCancelEnv g r) g_ser) :
    PhaseGroupSpec M (CliSessStorePollEnv dir peer g r) (6 * FineScale + g_ser) := by
  unfold CliSessStorePollEnv
  refine ((cliAddrTextEnv_groupSpec M peer).seq
    (hser.seq ((cliDirPutEnv_groupSpec M dir [] []).seq (PhaseGroupSpec.freeOnly M)))).mono ?_
  have hc : 3 * FineScale + 3 * FineScale = 6 * FineScale := by decide
  omega

theorem cliSessStorePollEnv_dom_fine_groupSpec {pqCap : Nat}
    (dir : DirGhost) (peer : AddrGhost)
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hgv : RecordGhostValid g r)
    (hdom : ∀ ses, r.currentSession = some ses → SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (CliSessStorePollEnv dir peer g r)
      (6 * FineScale + recordSerializeDomFineGrpS) :=
  cliSessStorePollEnv_groupSpec fineCostModel dir peer
    (recordSerializeCancelEnv_dom_fine_groupSpec hgv hdom)

theorem cliSessStorePollPrev1Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dir : DirGhost) (peer : AddrGhost)
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)} {g_ser1 : Nat}
    (hser1 : PhaseGroupSpec M (SerializePrev1CancelEnv G sess enc) g_ser1) :
    PhaseGroupSpec M (CliSessStorePollPrev1Env dir peer G sess enc) (6 * FineScale + g_ser1) := by
  unfold CliSessStorePollPrev1Env
  refine ((cliAddrTextEnv_groupSpec M peer).seq
    (hser1.seq ((cliDirPutEnv_groupSpec M dir [] []).seq (PhaseGroupSpec.freeOnly M)))).mono ?_
  have hc : 3 * FineScale + 3 * FineScale = 6 * FineScale := by decide
  omega

theorem cliSessStorePollPrev1Env_dom_fine_groupSpec {pqCap : Nat}
    (dir : DirGhost) (peer : AddrGhost)
    {G : SessionGhost} {ses : Session (List (BitVec 8))} (enc : List (BitVec 8))
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (CliSessStorePollPrev1Env dir peer G ses enc)
      (6 * FineScale + serializePrev1DomFineGrpS) :=
  cliSessStorePollPrev1Env_groupSpec fineCostModel dir peer
    (serializePrev1CancelEnv_dom_fine_groupSpec enc hgv hdom)

theorem cliSmallStorePollEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (rd : ReadRule) (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec M (CliSmallStorePollEnv rd files dir name) (144 * FineScale) := by
  unfold CliSmallStorePollEnv
  have h1 := cliDecimalEnv_groupSpec M 0#32
  have h2 := cliDirGetEnv_groupSpec M rd files dir name
  have h3 := boundedRustEvs_groupSpec M 32 8192
  have h4 := cliDirPutStrEnv_groupSpec M dir name []
  exact (h1.seq (h2.seq (h3.seq (h4.seq (PhaseGroupSpec.freeOnly M))))).mono (by decide)

theorem cliSmallStorePollEnv_fine_groupSpec
    (rd : ReadRule) (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (CliSmallStorePollEnv rd files dir name)
      (16659 + 141 * FineScale) := by
  unfold CliSmallStorePollEnv
  have h1 := cliDecimalEnv_fine_groupSpec 0#32
  have h2 := cliDirGetEnv_groupSpec fineCostModel rd files dir name
  have h3 := boundedRustEvs_groupSpec fineCostModel 32 8192
  have h4 := cliDirPutStrEnv_groupSpec fineCostModel dir name []
  exact (h1.seq (h2.seq (h3.seq (h4.seq (PhaseGroupSpec.freeOnly fineCostModel))))).mono (by decide)

/-! ## `InitialState` and `SpqrCodecPeakSpec` -/

theorem statesIntoPbEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {F : ShaCompress} (x : StatesIntoPbGhost F) :
    PhaseGroupSpec M (StatesIntoPbEnv x) (3 * FineScale * 64) :=
  spqrBoundedEvs_groupSpec M 64 (2 * (V1State.encodeRaw x.st.into_pb).length + 1024)

theorem initInnerEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (F : ShaCompress) (x : InitInnerGhost) :
    PhaseGroupSpec M (InitInnerEnv F x) (3 * FineScale * 96) := by
  unfold InitInnerEnv
  cases x.v with
  | v0 => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  | v1 => exact spqrBoundedEvs_groupSpec M 96 (2 * x.authKey.length + 2048)

theorem initialStateEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (F : ShaCompress) (x : InitialStateGhost) :
    PhaseGroupSpec M (InitialStateEnv F x) (3 * FineScale * 128) := by
  unfold InitialStateEnv
  cases x.p.version with
  | v0 => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  | v1 => exact spqrBoundedEvs_groupSpec M 128 (4 * x.p.authKey.length + 4096)

theorem pqRatchetStateEncodeToVecEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (st : PqRatchetState) :
    PhaseGroupSpec M (PqRatchetStateEncodeToVecEnv st) (3 * FineScale) where
  groups_le st0 {_} := fun h => by
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simp [AllocCostModel.stepEvents_nil]
    · exact (PhaseGroupSpec.rustAlloc_any M _ 1).groups_le st0 rfl

theorem decodeStateBoundedEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (bsLen : Nat) :
    PhaseGroupSpec M (DecodeStateBoundedEnv bsLen)
      (3 * FineScale * ((2 * bsLen + 64) + 128)) :=
  spqrBoundedTotalEvs_groupSpec M (2 * bsLen + 64) 128 (8 * bsLen + 16384) (2 * bsLen + 4096)

theorem decodeStateLinearBoundedEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (bsLen : Nat) :
    PhaseGroupSpec M (DecodeStateLinearBoundedEnv bsLen)
      (3 * FineScale * ((2 * bsLen + 64) + (bsLen / 18 + 128))) :=
  spqrBoundedTotalEvs_groupSpec M (2 * bsLen + 64) (bsLen / 18 + 128)
    (8 * bsLen + 16384) (2 * bsLen + 4096)

theorem statesFromPbBoundedEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (pb : V1State) :
    PhaseGroupSpec M (StatesFromPbBoundedEnv pb)
      (3 * FineScale * ((rawV1State pb + 64) + 64)) :=
  spqrBoundedTotalEvs_groupSpec M (rawV1State pb + 64) 64
    (4 * rawV1State pb + 16384) (2 * rawV1State pb + 4096)

/-! ## `W1EncryptSegments` and `W1EncryptSlotPeak` -/

theorem boxAllocEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (boxSize : Nat) :
    PhaseGroupSpec M (BoxAllocEnv boxSize) (3 * FineScale) where
  groups_le st0 {_} := fun h => by
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simp [AllocCostModel.stepEvents_nil]
    · exact (PhaseGroupSpec.rustAlloc_any M boxSize 8).groups_le st0 rfl

theorem boxAllocEnv_le_44_fine_groupSpec {boxSize : Nat} (hbox : boxSize ≤ 44) :
    PhaseGroupSpec fineCostModel (BoxAllocEnv boxSize) 16659 where
  groups_le st0 {_} := fun h => by
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simp [AllocCostModel.stepEvents_nil]
    · exact (fine_rustAlloc_le_44 (al := 8) (by omega) hbox).groups_le st0 rfl

theorem stringCloneEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (g : VecGhost) :
    PhaseGroupSpec M (StringCloneEnv g) (3 * FineScale) where
  groups_le st0 {_} := fun h => by
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simp [AllocCostModel.stepEvents_nil]
    · exact (PhaseGroupSpec.rustAlloc_any M g.bytes.length 1).groups_le st0 rfl

theorem stringCloneEnv_le_44_fine_groupSpec {g : VecGhost} (hlen : g.bytes.length ≤ 44) :
    PhaseGroupSpec fineCostModel (StringCloneEnv g) 16659 where
  groups_le st0 {_} := fun h => by
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simp [AllocCostModel.stepEvents_nil]
    · exact (fine_rustAlloc_le_44 (al := 1) (by omega) hlen).groups_le st0 rfl

theorem kyberOptStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (ct : Option (List (BitVec 8))) :
    PhaseGroupSpec M (KyberOptStepEnv ct) (3 * FineScale) where
  groups_le st0 {_} := fun h => by
    cases ct with
    | none =>
        subst h
        simp [AllocCostModel.stepEvents_nil]
    | some bs =>
        rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · simp [AllocCostModel.stepEvents_nil]
        · exact (PhaseGroupSpec.rustAlloc_any M bs.length 1).groups_le st0 rfl

theorem boxPollDrop_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {boxSize g_p : Nat} {E_poll : List AllocEvent → Prop}
    (hpoll : PhaseGroupSpec M E_poll g_p) :
    PhaseGroupSpec M
      (SeqEnv (BoxAllocEnv boxSize) (SeqEnv E_poll (· = rustDeallocEvents boxSize 8)))
      (3 * FineScale + g_p) := by
  exact ((boxAllocEnv_groupSpec M boxSize).seq
    (hpoll.seq (PhaseGroupSpec.rustDealloc M boxSize 8))).mono (by omega)

theorem loadStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal) {g_p : Nat}
    (hpoll : PhaseGroupSpec M (kitEnv.loadPollEnv st0 rem) g_p) :
    PhaseGroupSpec M (LoadStepEnv kit kitEnv st0 rem) (3 * FineScale + g_p) :=
  boxPollDrop_groupSpec M hpoll

theorem storeStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal) (rec : SessionRecord (List (BitVec 8))) {g_p : Nat}
    (hpoll : PhaseGroupSpec M (kitEnv.storePollEnv st0 rem rec) g_p) :
    PhaseGroupSpec M (StoreStepEnv kit kitEnv st0 rem rec) (3 * FineScale + g_p) :=
  boxPollDrop_groupSpec M hpoll

theorem trustStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey) (d : Direction) {g_p : Nat}
    (hpoll : PhaseGroupSpec M (ikitEnv.trustPollEnv ist0 rem key d) g_p) :
    PhaseGroupSpec M (TrustStepEnv ikit ikitEnv ist0 rem key d) (3 * FineScale + g_p) :=
  boxPollDrop_groupSpec M hpoll

theorem saveStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey) {g_p : Nat}
    (hpoll : PhaseGroupSpec M (ikitEnv.savePollEnv ist0 rem key) g_p) :
    PhaseGroupSpec M (SaveStepEnv ikit ikitEnv ist0 rem key) (3 * FineScale + g_p) :=
  boxPollDrop_groupSpec M hpoll

theorem otrApplyEnvTight_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M OtrApplyEnvTight (3 * FineScale) :=
  ((PhaseGroupSpec.rustAlloc_any M 32 1).seq (PhaseGroupSpec.freeOnly M)).mono (by omega)

theorem otrApplyEnvTight_fine_groupSpec :
    PhaseGroupSpec fineCostModel OtrApplyEnvTight 16659 :=
  ((fine_rustAlloc_le_44 (sz := 32) (al := 1) (by omega) (by omega)).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

theorem otrEncryptStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_send E_sigNew : List AllocEvent → Prop} {ptextLen g_s g_n : Nat}
    (hSend : PhaseGroupSpec M E_send g_s)
    (hSigNew : PhaseGroupSpec M E_sigNew g_n) :
    PhaseGroupSpec M (OtrEncryptStepEnv E_send ptextLen E_sigNew)
      (g_s + 6 * FineScale + g_n) := by
  have hok := (otrApplyEnvTight_groupSpec M).seq
    ((PhaseGroupSpec.rustAlloc_any M ((ptextLen / 16 + 1) * 16) 1).seq
      (hSigNew.seq (PhaseGroupSpec.freeOnly M)))
  exact (hSend.seq ((PhaseGroupSpec.freeOnly M).or hok)).mono (by omega)

theorem fromApplySegEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {boxStore g_sp : Nat} {E_storePoll : List AllocEvent → Prop}
    (hStore : PhaseGroupSpec M E_storePoll g_sp) :
    PhaseGroupSpec M (FromApplySegEnv boxStore E_storePoll) (6 * FineScale + g_sp) := by
  have htail := (boxAllocEnv_groupSpec M boxStore).seq
    (hStore.seq ((PhaseGroupSpec.rustDealloc M boxStore 8).seq (PhaseGroupSpec.freeOnly M)))
  exact ((otrApplyEnvTight_groupSpec M).seq htail).mono (by omega)

theorem fromSaveSegEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {boxSave g_sv g_ap : Nat} {E_savePoll E_apply : List AllocEvent → Prop}
    (hSave : PhaseGroupSpec M E_savePoll g_sv)
    (hApply : PhaseGroupSpec M E_apply g_ap) :
    PhaseGroupSpec M (FromSaveSegEnv boxSave E_savePoll E_apply)
      (3 * FineScale + g_sv + g_ap) :=
  ((boxPollDrop_groupSpec M hSave).seq ((PhaseGroupSpec.freeOnly M).or hApply)).mono (by omega)

theorem fromCmSegEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {boxTrust g_tr g_sv : Nat} {E_trustPoll E_save : List AllocEvent → Prop} (remName : VecGhost)
    (hTrust : PhaseGroupSpec M E_trustPoll g_tr)
    (hSave : PhaseGroupSpec M E_save g_sv) :
    PhaseGroupSpec M (FromCmSegEnv boxTrust E_trustPoll remName E_save)
      (3 * FineScale + g_tr + max (3 * FineScale) g_sv) := by
  have hcl : PhaseGroupSpec M (SeqEnv (StringCloneEnv remName) FreeOnlyEvs) (3 * FineScale) :=
    ((stringCloneEnv_groupSpec M remName).seq (PhaseGroupSpec.freeOnly M)).mono
      (Nat.le_of_eq (Nat.add_zero _))
  have hbr := (PhaseGroupSpec.freeOnly M).or (hcl.or hSave)
  refine ((boxPollDrop_groupSpec M hTrust).seq hbr).mono ?_
  omega

theorem fromKeySegEnv_groupSpec {α : Type} (M : AllocCostModel) [HasFineGroupCredit M]
    (pendingPreKey : Option α) (remName : VecGhost) (kyberCt : Option (List (BitVec 8)))
    {E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome : List AllocEvent → Prop}
    {g_otr g_pk g_cm : Nat}
    (hOtrNone : PhaseGroupSpec M E_otrNone g_otr)
    (hOtrSome : PhaseGroupSpec M E_otrSome g_otr)
    (hPksmNew : PhaseGroupSpec M E_pksmNew g_pk)
    (hCmNone : PhaseGroupSpec M E_cmNone g_cm)
    (hCmSome : PhaseGroupSpec M E_cmSome g_cm) :
    PhaseGroupSpec M
      (FromKeySegEnv pendingPreKey remName kyberCt E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome)
      (3 * FineScale + g_otr + g_pk + g_cm) := by
  have hf := PhaseGroupSpec.freeOnly M
  have hNone := hOtrNone.seq (hf.or hCmNone)
  have hClone := (stringCloneEnv_groupSpec M remName).seq hf
  have hSomeOk := (kyberOptStepEnv_groupSpec M kyberCt).seq
    (hOtrSome.seq (hf.or (hPksmNew.seq (hf.or hCmSome))))
  have hSome := hClone.or hSomeOk
  refine ((hNone.or hSome).of_imp ?_).mono (by omega)
  intro evs h
  exact h.elim (fun h1 => Or.inl h1.2) (fun h2 => Or.inr h2.2)

theorem withStoresEncSegEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {boxLoad g_ld g_fo : Nat} {E_loadPoll E_fromOtr : List AllocEvent → Prop} (remName : VecGhost)
    (hLoad : PhaseGroupSpec M E_loadPoll g_ld)
    (hFromOtr : PhaseGroupSpec M E_fromOtr g_fo) :
    PhaseGroupSpec M (WithStoresEncSegEnv boxLoad E_loadPoll remName E_fromOtr)
      (3 * FineScale + g_ld + max (3 * FineScale) g_fo) := by
  have hf := PhaseGroupSpec.freeOnly M
  have hcl : PhaseGroupSpec M (SeqEnv (StringCloneEnv remName) FreeOnlyEvs) (3 * FineScale) :=
    ((stringCloneEnv_groupSpec M remName).seq hf).mono (Nat.le_of_eq (Nat.add_zero _))
  have hcur : PhaseGroupSpec M (SeqEnv FreeOnlyEvs (fun evs => FreeOnlyEvs evs ∨ E_fromOtr evs)) g_fo :=
    (hf.seq (hf.or hFromOtr)).mono (by omega)
  exact ((boxPollDrop_groupSpec M hLoad).seq (hf.or (hcl.or hcur))).mono (by omega)

theorem fromCmTightEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {A : RustAlloc} {bs bi : BitVec 64}
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (rem : AddrVal) (remName : VecGhost)
    (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey)
    {g_tr g_sv g_st : Nat}
    (hTrust : PhaseGroupSpec M (ikitEnv.trustPollEnv ist0 rem k .sending) g_tr)
    (hSave : PhaseGroupSpec M
      (ikitEnv.savePollEnv (ikit.trustUpdate ist0 rem k .sending (.ok true)) rem k) g_sv)
    (hStore : PhaseGroupSpec M
      (kitEnv.storePollEnv st0 rem (storedRecord sess otr' taken)) g_st) :
    PhaseGroupSpec M
      (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 rem remName sess otr' taken k)
      (12 * FineScale + g_tr + g_sv + g_st) := by
  unfold FromCmTightEnv FromSaveTightEnv FromApplyTightEnv
  have hap := fromApplySegEnv_groupSpec M (boxStore := kit.storeBoxSize) hStore
  have hsv := fromSaveSegEnv_groupSpec M (boxSave := ikit.saveBoxSize) hSave hap
  refine (fromCmSegEnv_groupSpec M (boxTrust := ikit.trustBoxSize) remName hTrust hsv).mono ?_
  have hc39 : 3 * FineScale ≤ 3 * FineScale + (6 * FineScale) := by decide
  have hc12 : 3 * FineScale + (3 * FineScale + 6 * FineScale) = 12 * FineScale := by decide
  omega

theorem withStoresEncTightEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {A : RustAlloc} {bs bi : BitVec 64}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser) (x : WithStoresEncGhost)
    {E_otrNone E_otrSome E_pksmNew :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      List AllocEvent → Prop}
    {g_ld g_otr g_pk g_tr g_sv g_st : Nat}
    (hLoad : PhaseGroupSpec M (kitEnv.loadPollEnv st0 x.rem.val) g_ld)
    (hOtrNone : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseGroupSpec M (E_otrNone r sess otr taken) g_otr)
    (hOtrSome : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseGroupSpec M (E_otrSome r sess otr taken) g_otr)
    (hPksmNew : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseGroupSpec M (E_pksmNew r sess otr taken) g_pk)
    (hTrust : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseGroupSpec M (ikitEnv.trustPollEnv ist0 x.rem.val k .sending) g_tr)
    (hSave : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseGroupSpec M
        (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k) g_sv)
    (hStoreNone : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseGroupSpec M
        (kitEnv.storePollEnv st0 x.rem.val (storedRecord sess (otrAfterNone C S x otr) taken)) g_st)
    (hStoreSome : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseGroupSpec M
        (kitEnv.storePollEnv st0 x.rem.val (storedRecord sess (otrAfterSome C S parse x otr) taken)) g_st) :
    PhaseGroupSpec M
      (WithStoresEncTightEnv Scope kit kitEnv st0 ikit ikitEnv ist0 C S parse x
        E_otrNone E_otrSome E_pksmNew)
      (18 * FineScale + g_ld + g_otr + g_pk + g_tr + g_sv + g_st) := by
  unfold WithStoresEncTightEnv
  have hfo : PhaseGroupSpec M
      (fun evs' =>
        ∃ r sess otr taken,
          kit.ScopeAt Scope st0 x.rem.val r ∧
          r.currentSession = some sess ∧
          execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
          FromOtrTightEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken
            (E_otrNone r sess otr taken) (E_otrSome r sess otr taken)
            (E_pksmNew r sess otr taken) evs')
      (15 * FineScale + g_otr + g_pk + g_tr + g_sv + g_st) :=
    { groups_le := fun st0' {_} ⟨r, sess, otr, taken, hsc, hcur, hex, hfo'⟩ => by
        have hk := phaseGroupSpec_exists_guarded M
          (P := fun k : IdentityKey => taken.remoteIdentity = some k)
          (fun k hk =>
            fromKeySegEnv_groupSpec M sess.pendingPreKey x.rem.name
              (sess.pendingKyberPreKey.map (·.ciphertext))
              (hOtrNone r sess otr taken hsc hcur hex)
              (hOtrSome r sess otr taken hsc hcur hex)
              (hPksmNew r sess otr taken hsc hcur hex)
              (fromCmTightEnv_groupSpec M kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
                sess (otrAfterNone C S x otr) taken k
                (hTrust r sess otr taken k hsc hcur hex hk)
                (hSave r sess otr taken k hsc hcur hex hk)
                (hStoreNone r sess otr taken k hsc hcur hex hk))
              (fromCmTightEnv_groupSpec M kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
                sess (otrAfterSome C S parse x otr) taken k
                (hTrust r sess otr taken k hsc hcur hex hk)
                (hSave r sess otr taken k hsc hcur hex hk)
                (hStoreSome r sess otr taken k hsc hcur hex hk)))
        exact (((PhaseGroupSpec.freeOnly M).or hk).mono (by omega)).groups_le st0' hfo' }
  exact (withStoresEncSegEnv_groupSpec M x.rem.name hLoad hfo).mono (by omega)

/-! ## `cmkJump` Per-Size-Class, `W2TryDecrypt`, and `WithStoresDec` -/

theorem growOne104Evs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (c : Nat) :
    PhaseGroupSpec M (· = growOne104Evs c) (3 * FineScale) := by
  have hnf : NonFreeBound (· = growOne104Evs c) 1 := by
    rintro _ rfl
    unfold growOne104Evs
    split
    · rw [nonFreeCount_rustAllocEvents]
    · rw [nonFreeCount_rustReallocEvents]
  simpa using PhaseGroupSpec.of_nonFreeBound M hnf

theorem doublingChain104Evs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    ∀ caps : List Nat,
      PhaseGroupSpec M (· = doublingChain104Evs caps) (caps.length * (3 * FineScale))
  | [] => by simpa [doublingChain104Evs] using PhaseGroupSpec.nil M
  | c :: rest => by
      have hc := growOne104Evs_groupSpec M c
      have hr := doublingChain104Evs_groupSpec M rest
      refine (phaseGroupSpec_append_eq M hc hr).mono ?_
      simp [List.length_cons, Nat.succ_mul]
      omega

theorem dhCommitStep12Evs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M (· = dhCommitStep12Evs) (9 * FineScale) := by
  unfold dhCommitStep12Evs
  have h33 := PhaseGroupSpec.rustAlloc_any M 33 1
  have h32 := PhaseGroupSpec.rustAlloc_any M 32 1
  exact (phaseGroupSpec_append_eq M (phaseGroupSpec_append_eq M h33 h33) h32).mono (by omega)

theorem dhCommitStep12Evs_fine_groupSpec :
    PhaseGroupSpec fineCostModel (· = dhCommitStep12Evs) (3 * 16659) := by
  unfold dhCommitStep12Evs
  have h33 := fine_rustAlloc_le_44 (sz := 33) (al := 1) (by omega) (by omega)
  have h32 := fine_rustAlloc_le_44 (sz := 32) (al := 1) (by omega) (by omega)
  exact (phaseGroupSpec_append_eq fineCostModel
    (phaseGroupSpec_append_eq fineCostModel h33 h33) h32).mono (by omega)

theorem dhCommitStep3Evs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (cap : Nat) (needGrow : Bool) :
    PhaseGroupSpec M (· = dhCommitStep3Evs cap needGrow) (3 * FineScale) := by
  unfold dhCommitStep3Evs
  have hg : PhaseGroupSpec M (· = if needGrow then growOne104Evs cap else []) (3 * FineScale) := by
    cases needGrow
    · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    · exact growOne104Evs_groupSpec M cap
  exact (phaseGroupSpec_append_eq M hg (PhaseGroupSpec.rustDealloc M 33 1)).mono (by omega)

theorem w2Seg3DhCommitEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dhCap : Nat) (needGrow : Bool) :
    PhaseGroupSpec M (W2Seg3DhCommitEnv dhCap needGrow) (12 * FineScale) := by
  unfold W2Seg3DhCommitEnv
  have hok := (dhCommitStep12Evs_groupSpec M).seq
    ((dhCommitStep3Evs_groupSpec M dhCap needGrow).seq (PhaseGroupSpec.freeOnly M))
  exact ((PhaseGroupSpec.freeOnly M).or hok).mono (by omega)

theorem w2Seg3DhCommitEnv_fine_groupSpec (dhCap : Nat) (needGrow : Bool) :
    PhaseGroupSpec fineCostModel (W2Seg3DhCommitEnv dhCap needGrow) (3 * 16659 + 3 * FineScale) := by
  unfold W2Seg3DhCommitEnv
  have hok := (dhCommitStep12Evs_fine_groupSpec).seq
    ((dhCommitStep3Evs_groupSpec fineCostModel dhCap needGrow).seq
      (PhaseGroupSpec.freeOnly fineCostModel))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hok).mono (by omega)

private theorem le_cmkJumpFinalIdx : ∀ (jumps : List (Bool × Bool)) (k : Nat),
    k ≤ cmkJumpFinalIdx k jumps
  | [], k => Nat.le_refl k
  | (needGrow, _) :: rest, k => by
    simp only [cmkJumpFinalIdx]
    have h := le_cmkJumpFinalIdx rest (if needGrow then k + 1 else k)
    cases needGrow
    · simpa using h
    · simp only [↓reduceIte] at h ⊢
      omega

/-- Exact `fineCostModel` per-size-class group bound for `cmkJumpListEvs k jumps`:
each jump's `33 B` key allocates `16659` scaled units (`0.2542` grp/jump) and each
`Vec<104>` doubling step contributes `3 * FineScale`. -/
theorem cmkJumpListEvs_fine_groupSpec :
    ∀ (jumps : List (Bool × Bool)) (k : Nat),
      PhaseGroupSpec fineCostModel (· = cmkJumpListEvs k jumps)
        (jumps.length * 16659 + (cmkJumpFinalIdx k jumps - k) * (3 * FineScale))
  | [], _ => by simpa [cmkJumpListEvs, cmkJumpFinalIdx] using PhaseGroupSpec.nil fineCostModel
  | (needGrow, needEvictFree) :: rest, k => by
      have ha := fine_rustAlloc_le_44 (sz := 33) (al := 1) (by omega) (by omega)
      have hf : PhaseGroupSpec fineCostModel
          (· = if needEvictFree then rustDeallocEvents 33 1 else []) 0 := by
        cases needEvictFree
        · exact PhaseGroupSpec.nil fineCostModel
        · exact PhaseGroupSpec.rustDealloc fineCostModel 33 1
      have hrest := cmkJumpListEvs_fine_groupSpec rest (if needGrow then k + 1 else k)
      cases needGrow
      · simp only [cmkJumpListEvs, cmkJumpFinalIdx, Bool.false_eq_true, ↓reduceIte] at hrest ⊢
        rw [List.length_cons, Nat.succ_mul]
        have hg : PhaseGroupSpec fineCostModel (· = ([] : List AllocEvent)) 0 :=
          PhaseGroupSpec.nil fineCostModel
        have hstep := phaseGroupSpec_append_eq fineCostModel
          (phaseGroupSpec_append_eq fineCostModel ha hg) hf
        exact (phaseGroupSpec_append_eq fineCostModel hstep hrest).mono (by omega)
      · simp only [cmkJumpListEvs, cmkJumpFinalIdx, ↓reduceIte] at hrest ⊢
        rw [List.length_cons, Nat.succ_mul]
        have hle := le_cmkJumpFinalIdx rest (k + 1)
        have hsub : 1 + (cmkJumpFinalIdx (k + 1) rest - (k + 1)) =
            cmkJumpFinalIdx (k + 1) rest - k := by omega
        have hg := growOne104Evs_groupSpec fineCostModel (v104CapSeq k)
        have hstep := phaseGroupSpec_append_eq fineCostModel
          (phaseGroupSpec_append_eq fineCostModel ha hg) hf
        refine (phaseGroupSpec_append_eq fineCostModel hstep hrest).mono ?_
        have hmul : (3 * FineScale) + (cmkJumpFinalIdx (k + 1) rest - (k + 1)) * (3 * FineScale) =
            (cmkJumpFinalIdx (k + 1) rest - k) * (3 * FineScale) := by
          rw [← hsub, Nat.add_mul, Nat.one_mul]
        omega

/-- Scaled group bound (`35,284,080` = `539` groups) for a `≤ 2000`-step `cmkJump` loop with
`≤ 10` `Vec<104>` doubling steps (`2000 × 16659 + 10 × 3 × FineScale`). -/
def w2Seg4CmkFineGrpS (maxSteps : Nat) : Nat :=
  2000 * 16659 + maxSteps * (3 * FineScale)

theorem cmkJumpListEvs_tower_fine_groupSpec {jumps : List (Bool × Bool)}
    (hlen : jumps.length ≤ 2000) (hk : cmkJumpFinalIdx 0 jumps ≤ 10) :
    PhaseGroupSpec fineCostModel (· = cmkJumpListEvs 0 jumps) (w2Seg4CmkFineGrpS 10) := by
  refine (cmkJumpListEvs_fine_groupSpec jumps 0).mono ?_
  unfold w2Seg4CmkFineGrpS
  have h1 : jumps.length * 16659 ≤ 2000 * 16659 := Nat.mul_le_mul_right 16659 hlen
  have h2 : (cmkJumpFinalIdx 0 jumps - 0) * (3 * FineScale) ≤ 10 * (3 * FineScale) :=
    Nat.mul_le_mul_right (3 * FineScale) (by rw [Nat.sub_zero]; exact hk)
  exact Nat.add_le_add h1 h2

/-- Fresh-alloc (`BoundedFreshEvs`) refinement of `W2Seg4CmkStepEnv caps` capturing that the `≤ 2000`
`33 B` message-key allocations never emit `.realloc`. -/
def W2Seg4CmkTightEnv (caps : List Nat) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedFreshEvs 2000 4000 33)
      (SeqEnv (· = doublingChain104Evs caps) FreeOnlyEvs) evs

theorem w2Seg4CmkTightEnv_fine_groupSpec {caps : List Nat} {maxSteps : Nat}
    (hcaps : caps.length ≤ maxSteps) :
    PhaseGroupSpec fineCostModel (W2Seg4CmkTightEnv caps) (w2Seg4CmkFineGrpS maxSteps) := by
  unfold W2Seg4CmkTightEnv w2Seg4CmkFineGrpS
  have h1 := @boundedFreshEvs_le_44_fine_groupSpec 2000 4000 33 (by omega)
  have h2 := (doublingChain104Evs_groupSpec fineCostModel caps).mono
    (Nat.mul_le_mul_right (3 * FineScale) hcaps)
  have hok := (h1.seq (h2.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono
    (by rw [Nat.add_zero])
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hok).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem w2Seg4CmkStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {caps : List Nat} {maxSteps : Nat} (hcaps : caps.length ≤ maxSteps) :
    PhaseGroupSpec M (W2Seg4CmkStepEnv caps)
      (3 * FineScale * 2000 + maxSteps * (3 * FineScale)) := by
  unfold W2Seg4CmkStepEnv
  have h1 := boundedNonFreeEvs_groupSpec M 2000 4000 33
  have h2 := (doublingChain104Evs_groupSpec M caps).mono
    (Nat.mul_le_mul_right (3 * FineScale) hcaps)
  exact ((PhaseGroupSpec.freeOnly M).or (h1.seq (h2.seq (PhaseGroupSpec.freeOnly M)))).mono (by omega)

theorem s7CoreEvs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (withAddr errAlloc : Bool) :
    PhaseGroupSpec M (· = s7CoreEvs withAddr errAlloc) (12 * FineScale) := by
  unfold s7CoreEvs vmacEvs computeMacEvs
  have h33 := PhaseGroupSpec.rustAlloc_any M 33 1
  have hd33 := PhaseGroupSpec.rustDealloc M 33 1
  have hmac := phaseGroupSpec_append_eq M
    (phaseGroupSpec_append_eq M (phaseGroupSpec_append_eq M h33 hd33) h33) hd33
  have hv : PhaseGroupSpec M
      (· = if withAddr then
             (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++
               rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) ++
               (rustAllocEvents 36 1 ++ rustDeallocEvents 36 1)
           else
             rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++
               rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)
      (9 * FineScale) := by
    cases withAddr
    · exact hmac.mono (by omega)
    · have h36 := phaseGroupSpec_append_eq M
        (PhaseGroupSpec.rustAlloc_any M 36 1) (PhaseGroupSpec.rustDealloc M 36 1)
      exact (phaseGroupSpec_append_eq M hmac h36).mono (by omega)
  have herr : PhaseGroupSpec M
      (· = if errAlloc then rustAllocEvents 23 1 else []) (3 * FineScale) := by
    cases errAlloc
    · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any M 23 1
  exact (phaseGroupSpec_append_eq M hv herr).mono (by omega)

theorem s7CoreEvs_fine_groupSpec (withAddr errAlloc : Bool) :
    PhaseGroupSpec fineCostModel (· = s7CoreEvs withAddr errAlloc) (3 * 16659 + 11056) := by
  unfold s7CoreEvs vmacEvs computeMacEvs
  have h33 := fine_rustAlloc_le_44 (sz := 33) (al := 1) (by omega) (by omega)
  have hd33 := PhaseGroupSpec.rustDealloc fineCostModel 33 1
  have hmac := phaseGroupSpec_append_eq fineCostModel
    (phaseGroupSpec_append_eq fineCostModel (phaseGroupSpec_append_eq fineCostModel h33 hd33) h33) hd33
  have hv : PhaseGroupSpec fineCostModel
      (· = if withAddr then
             (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++
               rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) ++
               (rustAllocEvents 36 1 ++ rustDeallocEvents 36 1)
           else
             rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++
               rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)
      (3 * 16659) := by
    cases withAddr
    · exact hmac.mono (by omega)
    · have h36 := phaseGroupSpec_append_eq fineCostModel
        (fine_rustAlloc_le_44 (sz := 36) (al := 1) (by omega) (by omega))
        (PhaseGroupSpec.rustDealloc fineCostModel 36 1)
      exact (phaseGroupSpec_append_eq fineCostModel hmac h36).mono (by omega)
  have herr : PhaseGroupSpec fineCostModel
      (· = if errAlloc then rustAllocEvents 23 1 else []) 11056 := by
    cases errAlloc
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact fine_rustAlloc_le_28 (sz := 23) (al := 1) (by omega) (by omega)
  exact (phaseGroupSpec_append_eq fineCostModel hv herr).mono (by omega)

theorem w2Seg7MacEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (withAddr errAlloc : Bool) :
    PhaseGroupSpec M (W2Seg7MacEnv withAddr errAlloc) (12 * FineScale) :=
  ((PhaseGroupSpec.freeOnly M).or
    ((s7CoreEvs_groupSpec M withAddr errAlloc).seq (PhaseGroupSpec.freeOnly M))).mono (by omega)

theorem w2Seg7MacEnv_fine_groupSpec (withAddr errAlloc : Bool) :
    PhaseGroupSpec fineCostModel (W2Seg7MacEnv withAddr errAlloc) (3 * 16659 + 11056) :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((s7CoreEvs_fine_groupSpec withAddr errAlloc).seq
      (PhaseGroupSpec.freeOnly fineCostModel))).mono (by omega)

theorem aesDecCtShape_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (ctLen : Nat) :
    PhaseGroupSpec M (AesDecCtShape ctLen) (3 * FineScale) where
  groups_le st0 {_} := fun h => by
    rcases h with rfl | rfl | rfl
    · simp [AllocCostModel.stepEvents_nil]
    · exact (PhaseGroupSpec.rustAlloc_any M ctLen 1).groups_le st0 rfl
    · exact ((phaseGroupSpec_append_eq M
        (PhaseGroupSpec.rustAlloc_any M ctLen 1)
        (PhaseGroupSpec.rustDealloc M ctLen 1)).mono (by omega)).groups_le st0 rfl

theorem w2AesDecErrEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (ctLen : Nat) :
    PhaseGroupSpec M (W2AesDecErrEnv ctLen) (3 * FineScale) :=
  (aesDecCtShape_groupSpec M ctLen).of_imp fun _ h =>
    h.elim Or.inl (fun h2 => Or.inr (Or.inr h2))

theorem trApplyBoundedEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M TrApplyBoundedEnv (18 * FineScale) :=
  ((PhaseGroupSpec.freeOnly M).seq
    ((boundedLenEvs_groupSpec M 6 34).seq (PhaseGroupSpec.freeOnly M))).mono (by omega)

theorem w2TryDecryptEnv_of_seg4_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    {SpqrStepEnv : List AllocEvent → Prop} {g_cmk g_spqr : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (hcmk : PhaseGroupSpec M (W2Seg4CmkStepEnv caps) g_cmk)
    (hspqr : PhaseGroupSpec M SpqrStepEnv g_spqr) :
    PhaseGroupSpec M (W2TryDecryptEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (63 * FineScale + g_cmk + g_spqr) := by
  unfold W2TryDecryptEnv
  have hs1 := boundedNonFreeEvs_groupSpec M 6 16 160
  have hs3 := w2Seg3DhCommitEnv_groupSpec M dhCap needGrow
  have hs7 := w2Seg7MacEnv_groupSpec M withAddr errAlloc
  have hs8 := aesDecCtShape_groupSpec M ctLen
  have hs9 := trApplyBoundedEnv_groupSpec M
  have hok := hs1.seq (hs3.seq (hcmk.seq (hspqr.seq
    (hs7.seq (hs8.seq (hs9.seq (PhaseGroupSpec.freeOnly M)))))))
  exact ((PhaseGroupSpec.freeOnly M).or hok).mono (by omega)

theorem w2TryDecryptFailEnv_of_seg4_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    {SpqrStepEnv : List AllocEvent → Prop} {g_cmk g_spqr : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (hcmk : PhaseGroupSpec M (W2Seg4CmkStepEnv caps) g_cmk)
    (hspqr : PhaseGroupSpec M SpqrStepEnv g_spqr) :
    PhaseGroupSpec M (W2TryDecryptFailEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (45 * FineScale + g_cmk + g_spqr) := by
  unfold W2TryDecryptFailEnv
  have hs1 := boundedNonFreeEvs_groupSpec M 6 16 160
  have hs3 := w2Seg3DhCommitEnv_groupSpec M dhCap needGrow
  have hs7 := w2Seg7MacEnv_groupSpec M withAddr errAlloc
  have hs8 := w2AesDecErrEnv_groupSpec M ctLen
  have hok := hs1.seq (hs3.seq (hcmk.seq (hspqr.seq
    (hs7.seq (hs8.seq (PhaseGroupSpec.freeOnly M))))))
  exact ((PhaseGroupSpec.freeOnly M).or hok).mono (by omega)

/-- Tight `fineCostModel` `W2TryDecrypt` envelope pairing `W2Seg4CmkTightEnv` (`16659`/jump)
with per-size-class small-allocation weights. -/
def W2TryDecryptTightEnv (dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (withAddr errAlloc : Bool) (ctLen : Nat)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedNonFreeEvs 6 16 160)
      (SeqEnv (W2Seg3DhCommitEnv dhCap needGrow)
        (SeqEnv (W2Seg4CmkTightEnv caps)
          (SeqEnv SpqrStepEnv
            (SeqEnv (W2Seg7MacEnv withAddr errAlloc)
              (SeqEnv (AesDecCtShape ctLen)
                (SeqEnv TrApplyBoundedEnv FreeOnlyEvs)))))) evs

private theorem tryDecTight_sum_le (fs s16 s11 cmk spqr : Nat) :
    max 0 ((3 * fs * 6) + ((3 * s16 + 3 * fs) + (cmk + (spqr +
      ((3 * s16 + s11) + (3 * fs + (18 * fs + 0))))))) ≤
      42 * fs + 6 * s16 + s11 + cmk + spqr :=
  Nat.max_le.mpr ⟨Nat.zero_le _, by omega⟩

theorem w2TryDecryptTightEnv_fine_groupSpec
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps g_spqr : Nat}
    {SpqrStepEnv : List AllocEvent → Prop} (withAddr errAlloc : Bool) (ctLen : Nat)
    (hcaps : caps.length ≤ maxSteps)
    (hspqr : PhaseGroupSpec fineCostModel SpqrStepEnv g_spqr) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (42 * FineScale + 6 * 16659 + 11056 + w2Seg4CmkFineGrpS maxSteps + g_spqr) := by
  unfold W2TryDecryptTightEnv
  have hs1 := boundedNonFreeEvs_groupSpec fineCostModel 6 16 160
  have hs3 := w2Seg3DhCommitEnv_fine_groupSpec dhCap needGrow
  have hs4 := w2Seg4CmkTightEnv_fine_groupSpec hcaps
  have hs7 := w2Seg7MacEnv_fine_groupSpec withAddr errAlloc
  have hs8 := aesDecCtShape_groupSpec fineCostModel ctLen
  have hs9 := trApplyBoundedEnv_groupSpec fineCostModel
  have hok := hs1.seq (hs3.seq (hs4.seq (hspqr.seq
    (hs7.seq (hs8.seq (hs9.seq (PhaseGroupSpec.freeOnly fineCostModel)))))))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hok).mono
    (tryDecTight_sum_le FineScale 16659 11056 (w2Seg4CmkFineGrpS maxSteps) g_spqr)

theorem trialLoopEnv_groupSpec {α : Type} (M : AllocCostModel) [HasFineGroupCredit M]
    {HaltStep DoneStep : α → List AllocEvent → Prop} {FinalEnv : List AllocEvent → Prop}
    {n g_fail g_final : Nat}
    (xs : List α) (hlen : xs.length + 1 ≤ n)
    (hHalt : ∀ x ∈ xs, PhaseGroupSpec M (HaltStep x) g_fail)
    (hDone : ∀ x ∈ xs, PhaseGroupSpec M (DoneStep x) g_fail)
    (hFinal : PhaseGroupSpec M FinalEnv g_final) :
    PhaseGroupSpec M (TrialLoopEnv HaltStep DoneStep FinalEnv xs)
      ((n - 1) * g_fail + g_final) := by
  have hrec : ∀ ys : List α,
      (∀ x ∈ ys, PhaseGroupSpec M (HaltStep x) g_fail) →
      (∀ x ∈ ys, PhaseGroupSpec M (DoneStep x) g_fail) →
      PhaseGroupSpec M (TrialLoopEnv HaltStep DoneStep FinalEnv ys)
        (ys.length * g_fail + g_final) := by
    intro ys
    induction ys with
    | nil =>
        intro _ _
        simpa [TrialLoopEnv] using hFinal
    | cons y rest ih =>
        intro hh hd
        have hyh := hh y (List.Mem.head _)
        have hyd := hd y (List.Mem.head _)
        have htl := ih (fun z hz => hh z (List.Mem.tail _ hz))
          (fun z hz => hd z (List.Mem.tail _ hz))
        change PhaseGroupSpec M
          (fun evs => HaltStep y evs ∨
            ConcatEnv (DoneStep y) (TrialLoopEnv HaltStep DoneStep FinalEnv rest) evs)
          ((y :: rest).length * g_fail + g_final)
        refine (hyh.or (hyd.concat htl)).mono ?_
        rw [List.length_cons, Nat.succ_mul]
        omega
  have hm : xs.length * g_fail ≤ (n - 1) * g_fail :=
    Nat.mul_le_mul_right g_fail (by omega)
  exact (hrec xs hHalt hDone).mono (by omega)

theorem segTailEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M SegTailEnv (3 * FineScale) :=
  ((PhaseGroupSpec.freeOnly M).seq (PhaseGroupSpec.rustAlloc_any M 17 1)).mono (by omega)

theorem fromFEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M FromFEnv (3 * FineScale) :=
  ((segTailEnv_groupSpec M).seq (PhaseGroupSpec.freeOnly M)).mono (by omega)

theorem fromMEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M FromMEnv (6 * FineScale) :=
  ((growOneSpeEnv_groupSpec M 0#64).seq (fromFEnv_groupSpec M)).mono (by omega)

theorem fromVPostTdEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M FromVPostTdEnv (6 * FineScale) :=
  ((PhaseGroupSpec.freeOnly M).or (fromMEnv_groupSpec M)).mono (by omega)

theorem fromVEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {G₁ : SessionGhost} {g_td : Nat}
    (htd : PhaseGroupSpec M (tdEnv (recordTryDecryptEnvArgs x G₁)) g_td) :
    PhaseGroupSpec M (FromVEnv tdEnv x G₁) (g_td + 6 * FineScale) :=
  (htd.seq (fromVPostTdEnv_groupSpec M)).mono (by omega)

theorem recordDecryptEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {g_cl g_td : Nat}
    (hClone : PhaseGroupSpec M (SegCloneEnv x.G x.st) g_cl)
    (hTd : ∀ G₁ : SessionGhost, CloneRel x.G G₁ →
      PhaseGroupSpec M (tdEnv (recordTryDecryptEnvArgs x G₁)) g_td) :
    PhaseGroupSpec M (RecordDecryptEnv tdEnv x) (g_cl + g_td + 6 * FineScale) := by
  unfold RecordDecryptEnv
  split
  · refine phaseGroupSpec_exists_guarded M fun G₁ hRel => ?_
    exact (hClone.seq (fromVEnv_groupSpec M (hTd G₁ hRel))).mono (by omega)
  · exact (hClone.seq (fromMEnv_groupSpec M)).mono (by omega)

theorem fromRegionNoneEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M FromRegionNoneEnv (3 * FineScale) :=
  ((PhaseGroupSpec.rustAlloc_any M 17 1).seq (PhaseGroupSpec.freeOnly M)).mono (by omega)

theorem fromKeyReadyEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {x : DecryptGhost} {rec' : SessionRecord (List (BitVec 8))} {k : IdentityKey}
    {g_tr g_sv g_st : Nat}
    (htrust : PhaseGroupSpec M (TrustStepEnv ikit ikitEnv ist0 x.rem.val k .receiving) g_tr)
    (hsave : PhaseGroupSpec M
      (SaveStepEnv ikit ikitEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true))
        x.rem.val k) g_sv)
    (hstore : PhaseGroupSpec M (StoreStepEnv kit kitEnv st0 x.rem.val rec') g_st) :
    PhaseGroupSpec M (FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (g_tr + max (3 * FineScale) (g_sv + g_st)) := by
  have hf := PhaseGroupSpec.freeOnly M
  have hStoreCall : PhaseGroupSpec M (FromStoreCallEnv kit kitEnv st0 x.rem.val rec') g_st :=
    (hstore.seq hf).mono (by omega)
  have hFalse : PhaseGroupSpec M (FromTrustedFalseEnv x) (3 * FineScale) :=
    ((stringCloneEnv_groupSpec M x.rem.name).seq hf).mono (by omega)
  have hTrue : PhaseGroupSpec M (FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (g_sv + g_st) :=
    (hsave.seq (hf.or hStoreCall)).mono (by omega)
  exact (htrust.seq (hf.or (hFalse.or hTrue))).mono (by omega)

theorem withStoresDecEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    {g_ld g_rd g_tr g_sv g_st : Nat}
    (hLoad : PhaseGroupSpec M (LoadPollStepEnv kit kitEnv st0 x.rem.val) g_ld)
    (hRecDec : ∀ rec ses G,
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      PhaseGroupSpec M (RecordDecryptEnv tdEnv (recGhostOf x 0#64 G ses.state)) g_rd)
    (hTrust : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseGroupSpec M (TrustStepEnv ikit ikitEnv ist0 x.rem.val k .receiving) g_tr)
    (hSave : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseGroupSpec M
        (SaveStepEnv ikit ikitEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true))
          x.rem.val k) g_sv)
    (hStore : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseGroupSpec M (StoreStepEnv kit kitEnv st0 x.rem.val rec') g_st) :
    PhaseGroupSpec M
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      (g_ld + g_rd + g_tr + max (3 * FineScale) (g_sv + g_st)) := by
  have hf := PhaseGroupSpec.freeOnly M
  have hArm2 : PhaseGroupSpec M (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs) (3 * FineScale) :=
    ((stringCloneEnv_groupSpec M x.rem.name).seq hf).mono (Nat.le_of_eq (Nat.add_zero _))
  have hArm3 := fromRegionNoneEnv_groupSpec M
  have hArm4 : PhaseGroupSpec M
      (fun evs => ∃ rec ses G,
        kit.ScopeAt Scope st0 x.rem.val rec ∧
        rec.currentSession = some ses ∧
        SessionGhostValid G ses ∧
        FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 x rec G ses.state evs)
      (g_rd + (g_tr + max (3 * FineScale) (g_sv + g_st))) :=
    { groups_le := fun st0' {_} ⟨rec, ses, G, hsc, hcur, hgv, hfs⟩ => by
        have hexKr : PhaseGroupSpec M
            (fun evs' => ∃ pt rec' ses' k,
              decryptRecord C S parse x rec = .ok (pt, rec') ∧
              rec'.currentSession = some ses' ∧
              ses'.state.remoteIdentity = some k ∧
              FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs')
            (g_tr + max (3 * FineScale) (g_sv + g_st)) :=
          { groups_le := fun st0'' {_} ⟨pt, rec', ses', k, hdec, hc', hk, hfe⟩ =>
              (fromKeyReadyEnv_groupSpec M
                (hTrust rec pt rec' ses' k hsc hdec hc' hk)
                (hSave rec pt rec' ses' k hsc hdec hc' hk)
                (hStore rec pt rec' ses' k hsc hdec hc' hk)).groups_le st0'' hfe }
        have hPost : PhaseGroupSpec M _ (g_tr + max (3 * FineScale) (g_sv + g_st)) :=
          (hf.or hexKr).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
        exact ((hRecDec rec ses G hsc hcur hgv).seq hPost).groups_le st0' hfs }
  have hBr := hf.or (hArm2.or (hArm3.or hArm4))
  have hTail := (PhaseGroupSpec.rustDealloc M kit.loadBoxSize 8).seq hBr
  exact (hLoad.seq hTail).mono (by omega)

/-! ## `process_prekey_bundle` Group Bounds -/

theorem w3BoxedStoreStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (boxSz : Nat) {E_poll : List AllocEvent → Prop} {g_p : Nat}
    (hpoll : PhaseGroupSpec M E_poll g_p) :
    PhaseGroupSpec M (W3BoxedStoreStepEnv boxSz E_poll) (3 * FineScale + g_p) :=
  ((boxAllocEnv_groupSpec M boxSz).seq (hpoll.seq (PhaseGroupSpec.freeOnly M))).mono (by omega)

theorem w3BoxedStoreStepEnv_le_44_fine_groupSpec
    {boxSz : Nat} (hbox : boxSz ≤ 44) {E_poll : List AllocEvent → Prop} {g_p : Nat}
    (hpoll : PhaseGroupSpec fineCostModel E_poll g_p) :
    PhaseGroupSpec fineCostModel (W3BoxedStoreStepEnv boxSz E_poll) (16659 + g_p) :=
  ((boxAllocEnv_le_44_fine_groupSpec hbox).seq
    (hpoll.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono (by omega)

theorem w3SmallStoreStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (boxSz : Nat) (rd : ReadRule) (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec M (W3SmallStoreStepEnv boxSz rd files dir name) (147 * FineScale) :=
  (w3BoxedStoreStepEnv_groupSpec M boxSz
    (cliSmallStorePollEnv_groupSpec M rd files dir name)).mono (by omega)

theorem w3SessLoadStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop} {g_deser : Nat}
    (files : FsFiles) (sessDir : DirGhost) (peer : AddrGhost)
    (hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec M (DeserEnv bs) g_deser) :
    PhaseGroupSpec M (W3SessLoadStepEnv rd DeserEnv files sessDir peer)
      (45 * FineScale + g_deser) :=
  (w3BoxedStoreStepEnv_groupSpec M 24
    (cliSessLoadPollEnv_groupSpec M files sessDir peer hdeser)).mono (by omega)

theorem w3SessStoreStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (sessDir : DirGhost) (peer : AddrGhost)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {g_ser : Nat}
    (hser : PhaseGroupSpec M (RecordSerializeCancelEnv g_rec r_rec) g_ser) :
    PhaseGroupSpec M (W3SessStoreStepEnv sessDir peer g_rec r_rec)
      (9 * FineScale + g_ser) :=
  (w3BoxedStoreStepEnv_groupSpec M 32
    (cliSessStorePollEnv_groupSpec M sessDir peer hser)).mono (by omega)

theorem w3Stage1Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_trust E_sessLoad : List AllocEvent → Prop} {g_t g_s : Nat} (nameLen : Nat)
    (htrust : PhaseGroupSpec M E_trust g_t)
    (hload : PhaseGroupSpec M E_sessLoad g_s) :
    PhaseGroupSpec M (W3Stage1Env E_trust E_sessLoad nameLen)
      (g_t + 6 * FineScale + g_s) := by
  have hf := PhaseGroupSpec.freeOnly M
  have herr := (PhaseGroupSpec.rustAlloc_any M (nameLen + 1) 1).seq hf
  have hpass := (PhaseGroupSpec.rustAlloc_any M 33 1).seq
    (hf.seq ((PhaseGroupSpec.rustAlloc_any M 1569 1).seq (hf.seq hload)))
  exact (htrust.seq (herr.or hpass)).mono (by omega)

theorem w3Stage2Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_idKp : List AllocEvent → Prop} {g_k : Nat}
    (hkp : PhaseGroupSpec M E_idKp g_k) :
    PhaseGroupSpec M (W3Stage2Env E_idKp) (g_k + 3 * FineScale) := by
  have hf := PhaseGroupSpec.freeOnly M
  have hd16 := (PhaseGroupSpec.rustDealloc M 16 8).seq hf
  have h1568 := PhaseGroupSpec.rustAlloc_any M 1568 1
  have hsame := (h1568.concat (PhaseGroupSpec.rustDealloc M 1568 1)).seq hf
  exact (hkp.seq (hd16.or (hsame.or h1568))).mono (by omega)

theorem w3Stage23BracketEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_idKp E_stage3Body : List AllocEvent → Prop} {g_k g_3 : Nat}
    (hkp : PhaseGroupSpec M E_idKp g_k)
    (hs3 : PhaseGroupSpec M E_stage3Body g_3) :
    PhaseGroupSpec M (W3Stage23BracketEnv E_idKp E_stage3Body)
      (g_k + 3 * FineScale + g_3) := by
  have hf := PhaseGroupSpec.freeOnly M
  have hd16 := (PhaseGroupSpec.rustDealloc M 16 8).seq hf
  have h1568 := PhaseGroupSpec.rustAlloc_any M 1568 1
  have hd1568 := PhaseGroupSpec.rustDealloc M 1568 1
  have hsame := (h1568.concat hd1568).seq hf
  have hpass := ((h1568.concat hs3).concat hd1568).seq hf
  exact (hkp.seq (hd16.or (hsame.or hpass))).mono (by omega)

theorem w3Stage4Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_spqrInit : List AllocEvent → Prop} {g_q : Nat}
    (hspqr : PhaseGroupSpec M E_spqrInit g_q) :
    PhaseGroupSpec M (W3Stage4Env E_spqrInit) (42 * FineScale + g_q) :=
  ((w3BoundedEvs_groupSpec M 1 33).seq
    (hspqr.seq (w3BoundedEvs_groupSpec M 13 416))).mono (by omega)

theorem w3Stage4SpqrEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (F : ShaCompress) (x_spqr : InitialStateGhost) :
    PhaseGroupSpec M (W3Stage4SpqrEnv F x_spqr) (426 * FineScale) :=
  (w3Stage4Env_groupSpec M (initialStateEnv_groupSpec M F x_spqr)).mono (by decide)

theorem w3Stage5Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_idRegId E_idSave E_sessStore : List AllocEvent → Prop} {g_r g_i g_s : Nat}
    (hreg : PhaseGroupSpec M E_idRegId g_r)
    (hsave : PhaseGroupSpec M E_idSave g_i)
    (hstore : PhaseGroupSpec M E_sessStore g_s) :
    PhaseGroupSpec M (W3Stage5Env E_idRegId E_idSave E_sessStore)
      (12 * FineScale + g_r + g_i + g_s) :=
  ((w3BoundedEvs_groupSpec M 4 68).seq
    (hreg.seq (hsave.seq (hstore.seq (PhaseGroupSpec.freeOnly M))))).mono (by omega)

private theorem w3InitiateSlot_sum_le (fs gd gs : Nat) :
    87 * fs + 147 * fs + (45 * fs + gd) + 147 * fs + (3 * fs * 128) +
      147 * fs + 147 * fs + (9 * fs + gs) ≤ 1113 * fs + gd + gs := by
  omega

theorem w3InitiateFullEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore :
      List AllocEvent → Prop}
    {g_t g_l g_k g_q g_r g_i g_s : Nat} (nameLen : Nat)
    (htrust : PhaseGroupSpec M E_trust g_t)
    (hload : PhaseGroupSpec M E_sessLoad g_l)
    (hkp : PhaseGroupSpec M E_idKp g_k)
    (hspqr : PhaseGroupSpec M E_spqrInit g_q)
    (hreg : PhaseGroupSpec M E_idRegId g_r)
    (hsave : PhaseGroupSpec M E_idSave g_i)
    (hstore : PhaseGroupSpec M E_sessStore g_s) :
    PhaseGroupSpec M
      (W3InitiateFullEnv E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore nameLen)
      (87 * FineScale + g_t + g_l + g_k + g_q + g_r + g_i + g_s) := by
  have hs1 := w3Stage1Env_groupSpec M nameLen htrust hload
  have hs2 := w3Stage2Env_groupSpec M hkp
  have hs3 := w3BoundedEvs_groupSpec M 8 1569
  have hs4 := w3Stage4Env_groupSpec M hspqr
  have hs5 := w3Stage5Env_groupSpec M hreg hsave hstore
  exact ((((hs1.seq hs2).seq hs3).seq hs4).seq hs5).mono (by omega)

theorem w3Stage1EnvWide_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_trust E_sessLoad : List AllocEvent → Prop} {g_t g_s : Nat} (nameLen : Nat)
    (htrust : PhaseGroupSpec M E_trust g_t)
    (hload : PhaseGroupSpec M E_sessLoad g_s) :
    PhaseGroupSpec M (W3Stage1EnvWide E_trust E_sessLoad nameLen)
      (g_t + 6 * FineScale + g_s) := by
  have hf := PhaseGroupSpec.freeOnly M
  have herr := ((PhaseGroupSpec.rustAlloc_any M (nameLen + 1) 1).or
    (PhaseGroupSpec.rustAlloc_any M nameLen 1)).seq hf
  have hpass := (PhaseGroupSpec.rustAlloc_any M 33 1).seq
    (hf.seq ((PhaseGroupSpec.rustAlloc_any M 1569 1).seq (hf.seq hload)))
  exact (htrust.seq (herr.or hpass)).mono (by omega)

theorem w3InitiateFullEnvWide_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore :
      List AllocEvent → Prop}
    {g_t g_l g_k g_q g_r g_i g_s : Nat} (nameLen : Nat)
    (htrust : PhaseGroupSpec M E_trust g_t)
    (hload : PhaseGroupSpec M E_sessLoad g_l)
    (hkp : PhaseGroupSpec M E_idKp g_k)
    (hspqr : PhaseGroupSpec M E_spqrInit g_q)
    (hreg : PhaseGroupSpec M E_idRegId g_r)
    (hsave : PhaseGroupSpec M E_idSave g_i)
    (hstore : PhaseGroupSpec M E_sessStore g_s) :
    PhaseGroupSpec M
      (W3InitiateFullEnvWide E_trust E_sessLoad E_idKp E_spqrInit E_idRegId E_idSave E_sessStore nameLen)
      (87 * FineScale + g_t + g_l + g_k + g_q + g_r + g_i + g_s) := by
  have hs1 := w3Stage1EnvWide_groupSpec M nameLen htrust hload
  have hs2 := w3Stage2Env_groupSpec M hkp
  have hs3 := w3BoundedEvs_groupSpec M 8 1569
  have hs4 := w3Stage4Env_groupSpec M hspqr
  have hs5 := w3Stage5Env_groupSpec M hreg hsave hstore
  exact ((((hs1.seq hs2).seq hs3).seq hs4).seq hs5).mono (by omega)

theorem w3InitiateSlotEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (P : W3InitiateSlotParams) {g_deser g_ser : Nat}
    (hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec M (P.DeserEnv bs) g_deser)
    (hser : PhaseGroupSpec M (RecordSerializeCancelEnv P.g_rec P.r_rec) g_ser) :
    PhaseGroupSpec M (W3InitiateSlotEnv P)
      (1113 * FineScale + g_deser + g_ser) :=
  (w3InitiateFullEnv_groupSpec M P.peer.name.bytes.length
    (w3SmallStoreStepEnv_groupSpec M 32 P.rd P.files P.peersDir (addressText P.peer.val))
    (w3SessLoadStepEnv_groupSpec M P.files P.sessDir P.peer hdeser)
    (w3SmallStoreStepEnv_groupSpec M 16 P.rd P.files P.ownDir P.ownKeyName)
    (initialStateEnv_groupSpec M P.F P.x_spqr)
    (w3SmallStoreStepEnv_groupSpec M 16 P.rd P.files P.ownDir P.ownRegName)
    (w3SmallStoreStepEnv_groupSpec M 32 P.rd P.files P.peersDir (addressText P.peer.val))
    (w3SessStoreStepEnv_groupSpec M P.sessDir P.peer hser)).mono
    (w3InitiateSlot_sum_le FineScale g_deser g_ser)

theorem w3InitiateSlotEnv_dom_fine_groupSpec {pqCap g_deser : Nat}
    (P : W3InitiateSlotParams)
    (hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hgv : RecordGhostValid P.g_rec P.r_rec)
    (hdom : ∀ ses, P.r_rec.currentSession = some ses → SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (W3InitiateSlotEnv P)
      (1113 * FineScale + g_deser + recordSerializeDomFineGrpS) :=
  w3InitiateSlotEnv_groupSpec fineCostModel P hdeser
    (recordSerializeCancelEnv_dom_fine_groupSpec hgv hdom)

/-! ## PreKey Responder Trial Loop and `initBob` Core -/

theorem w4PrevTrials_groupSpec {α : Type} (M : AllocCostModel) [HasFineGroupCredit M]
    {HaltStep DoneStep : α → List AllocEvent → Prop} {FinalEnv : List AllocEvent → Prop}
    {g_clone g_td g_final : Nat}
    (xs : List α) (hlen : xs.length + 1 ≤ 5)
    (hHalt : ∀ x ∈ xs, PhaseGroupSpec M (HaltStep x) (g_clone + g_td))
    (hDone : ∀ x ∈ xs, PhaseGroupSpec M (DoneStep x) (g_clone + g_td))
    (hFinal : PhaseGroupSpec M FinalEnv g_final) :
    PhaseGroupSpec M (TrialLoopEnv HaltStep DoneStep FinalEnv xs)
      (4 * (g_clone + g_td) + g_final) :=
  trialLoopEnv_groupSpec M xs hlen hHalt hDone hFinal

/-- `PhaseGroupSpec` for W4 `initBob` core (`≤ 25` native ops + `InitialStateEnv` `128` ops =
`459 * FineScale` = `459` groups). -/
theorem w4InitBob_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {E_pre E_post : List AllocEvent → Prop} (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hpre : PhaseGroupSpec M E_pre (3 * FineScale * 12))
    (hpost : PhaseGroupSpec M E_post (3 * FineScale * 13)) :
    PhaseGroupSpec M (SeqEnv E_pre (SeqEnv (InitialStateEnv F x_spqr) (SeqEnv E_post FreeOnlyEvs)))
      (459 * FineScale) :=
  (hpre.seq ((initialStateEnv_groupSpec M F x_spqr).seq
    (hpost.seq (PhaseGroupSpec.freeOnly M)))).mono (by decide)

/-! ## `Cli.run` Dispatch and `main` Setup -/

/-- Subcommand-dispatch `PhaseGroupSpec` for `Cli.run` across `.keygen`, `.init`, `.send`, and `.recv`. -/
theorem cliRunDispatch_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {RunEnv : RunCall → List AllocEvent → Prop}
    {g_kg g_init g_send g_recv : Nat} (g : RunCall)
    (hkg : ∀ me n, g.c = .keygen me n → PhaseGroupSpec M (RunEnv g) g_kg)
    (hinit : ∀ peer bundle, g.c = .init peer bundle → PhaseGroupSpec M (RunEnv g) g_init)
    (hsend : ∀ peer, g.c = .send peer → PhaseGroupSpec M (RunEnv g) g_send)
    (hrecv : ∀ peer, g.c = .recv peer → PhaseGroupSpec M (RunEnv g) g_recv) :
    PhaseGroupSpec M (RunEnv g) (max (max g_kg g_init) (max g_send g_recv)) := by
  cases hc : g.c with
  | keygen me n => exact (hkg me n hc).mono (by omega)
  | init peer bundle => exact (hinit peer bundle hc).mono (by omega)
  | send peer => exact (hsend peer hc).mono (by omega)
  | recv peer => exact (hrecv peer hc).mono (by omega)

theorem addressEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (uuidParse : UuidParser) (x : AddressCall) :
    PhaseGroupSpec M (AddressEnv uuidParse x) (3 * FineScale) := by
  unfold AddressEnv addressEvents
  cases addrParse uuidParse x.bs with
  | none => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  | some a => exact PhaseGroupSpec.rustAlloc_any M a.name.length 1

theorem addressEnv_fine_groupSpec (uuidParse : UuidParser) (x : AddressCall) :
    PhaseGroupSpec fineCostModel (AddressEnv uuidParse x) 16659 := by
  unfold AddressEnv addressEvents
  cases ha : addrParse uuidParse x.bs with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | some a =>
      obtain ⟨hle40, _⟩ := addrParse_name_bounds uuidParse x.bs ha
      exact fine_rustAlloc_le_44 (al := 1) (by omega) (by omega)

theorem reserve16Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (x : Reserve16Call) :
    PhaseGroupSpec M (Reserve16Env x) (3 * FineScale) := by
  unfold Reserve16Env reserve16Events
  dsimp only
  split
  · exact PhaseGroupSpec.rustAlloc_any M _ 8
  · exact PhaseGroupSpec.rustRealloc_any M _ _ 8

theorem tryAllocateInEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (x : TryAllocateInCall) :
    PhaseGroupSpec M (TryAllocateInEnv x) (3 * FineScale) :=
  PhaseGroupSpec.rustAlloc_any M (x.new.toNat * x.stride.toNat) x.align.toNat

theorem m1PhaseEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (argvLen : Nat) :
    PhaseGroupSpec M (M1PhaseEnv argvLen) (3 * FineScale) :=
  ((PhaseGroupSpec.nil M).or (PhaseGroupSpec.rustAlloc_any M (16 * argvLen) 8)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem m1PhaseEnv_le_3_fine_groupSpec {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseGroupSpec fineCostModel (M1PhaseEnv argvLen) 24623 :=
  ((PhaseGroupSpec.nil fineCostModel).or
    (fine_rustAlloc_le_60 (sz := 16 * argvLen) (al := 8) (by omega) (by omega))).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem m2CollectStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (k : Nat) :
    PhaseGroupSpec M (M2CollectStepEnv k) (3 * FineScale) :=
  ((PhaseGroupSpec.nil M).or (PhaseGroupSpec.rustRealloc_any M (16 * k) _ 8)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem m2CollectEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (argvLen : Nat) :
    PhaseGroupSpec M (M2CollectEnv argvLen) (argvLen * (3 * FineScale)) := by
  unfold M2CollectEnv
  have h := PhaseGroupSpec.iterSeq_const (3 * FineScale) (List.range argvLen)
    (fun k _ => m2CollectStepEnv_groupSpec M k)
  rw [List.length_range] at h
  exact h

theorem readStdinEnv_nonFreeBound (bs : List (BitVec 8)) :
    NonFreeBound (ReadStdinEnv bs) 9 := by
  intro evs h
  unfold ReadStdinEnv at h
  rcases h with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · unfold allocBytes1Events
    split
    · rw [nonFreeCount_nil]; exact Nat.zero_le 9
    · rw [nonFreeCount_rustAllocEvents]; decide
  · rw [specCliIoReadSchedule_events_eq 8 bs.length]
    exact cliIoReadStdinEnv_nonFreeBound bs.length _ rfl
  · rw [nonFreeCount_append, nonFreeCount_rustDeallocEvents, Nat.add_zero,
        specCliIoReadSchedule_events_eq 8 1048576]
    exact cliIoReadStdinEnv_nonFreeBound 1048576 _ rfl

theorem readStdinEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (bs : List (BitVec 8)) :
    PhaseGroupSpec M (ReadStdinEnv bs) (27 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M (readStdinEnv_nonFreeBound bs)).mono (by decide)

theorem readFileEnv_nonFreeBound (files : String → Option FsEntry) (path : List (BitVec 8)) :
    NonFreeBound (ReadFileEnv files path) 10 := by
  intro evs h
  unfold ReadFileEnv at h
  split at h
  · rcases h with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · unfold allocBytes1Events
      split
      · rw [nonFreeCount_nil]; exact Nat.zero_le 10
      · rw [nonFreeCount_rustAllocEvents]; decide
    · rw [nonFreeCount_nil]; exact Nat.zero_le 10
    · rw [specCliIoReadSchedule_events_eq 9 _]
      exact cliIoReadFileEnv_nonFreeBound _ _ rfl
    · rw [nonFreeCount_append, nonFreeCount_rustDeallocEvents, Nat.add_zero,
          specCliIoReadSchedule_events_eq 9 2097152]
      exact cliIoReadFileEnv_nonFreeBound 2097152 _ rfl
  · subst h
    rw [nonFreeCount_nil]; exact Nat.zero_le 10

theorem readFileEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (files : String → Option FsEntry) (path : List (BitVec 8)) :
    PhaseGroupSpec M (ReadFileEnv files path) (30 * FineScale) :=
  (PhaseGroupSpec.of_nonFreeBound M (readFileEnv_nonFreeBound files path)).mono (by decide)

theorem m3PhaseEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (needStdin : Bool) (stdin : List (BitVec 8))
    (files : String → Option FsEntry) (coinsPath : List (BitVec 8)) :
    PhaseGroupSpec M (M3PhaseEnv needStdin stdin files coinsPath) (57 * FineScale) := by
  have hst : PhaseGroupSpec M (if needStdin then ReadStdinEnv stdin else (· = []))
      (27 * FineScale) := by
    cases needStdin
    · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    · exact readStdinEnv_groupSpec M stdin
  have hrf := (readFileEnv_groupSpec M files coinsPath).seq (PhaseGroupSpec.freeOnly M)
  exact (hst.seq hrf).mono (by decide)

theorem cliWriteFileEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (len : Nat) :
    PhaseGroupSpec M (CliWriteFileEnv len) (3 * FineScale) where
  groups_le st0 {_} := fun h => by
    rcases h with rfl | ⟨_, rfl⟩
    · simp [AllocCostModel.stepEvents_nil]
    · exact ((phaseGroupSpec_append_eq M
        (PhaseGroupSpec.rustAlloc_any M (len + 1) 1)
        (PhaseGroupSpec.rustDealloc M (len + 1) 1)).mono
        (Nat.le_of_eq (Nat.add_zero _))).groups_le st0 rfl

theorem m5LoopAEntryEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dir name : List (BitVec 8)) :
    PhaseGroupSpec M (M5LoopAEntryEnv dir name) (12 * FineScale) := by
  unfold M5LoopAEntryEnv
  dsimp only
  let cap1 := reserveCap dir.length dir.length 1
  let need2 := decide (cap1 - (dir.length + 1) < name.length)
  let capFinal := if need2 then reserveCap cap1 (dir.length + 1) name.length else cap1
  have h1 := PhaseGroupSpec.rustAlloc_any M dir.length 1
  have h2 := PhaseGroupSpec.rustRealloc_any M dir.length cap1 1
  have h3 : PhaseGroupSpec M
      (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = []))
      (3 * FineScale) := by
    split
    · exact PhaseGroupSpec.rustRealloc_any M cap1 capFinal 1
    · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  have h4 := cliWriteFileEnv_groupSpec M (pathOf dir name).length
  have h5 := PhaseGroupSpec.rustDealloc M capFinal 1
  exact ((((h1.concat h2).concat h3).concat h4).concat h5).mono (by decide)

theorem m5WriteStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (entry : List (BitVec 8) × List (BitVec 8)) :
    PhaseGroupSpec M (M5WriteStepEnv entry) (12 * FineScale) := by
  unfold M5WriteStepEnv
  split
  · exact (cliWriteFileEnv_groupSpec M entry.2.length).mono (by omega)
  · exact m5LoopAEntryEnv_groupSpec M entry.1 entry.2

theorem m5DirStepEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dir : List (BitVec 8)) (names : List (List (BitVec 8))) :
    PhaseGroupSpec M (M5DirStepEnv dir names) (names.length * (12 * FineScale)) :=
  ((PhaseGroupSpec.iterSeq_const (12 * FineScale) names
    (fun nm _ => m5WriteStepEnv_groupSpec M (dir, nm))).seq
    (PhaseGroupSpec.freeOnly M)).mono (by omega)

theorem m5PhaseEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (dirs : List (List (BitVec 8) × List (List (BitVec 8)))) :
    PhaseGroupSpec M (M5PhaseEnv dirs)
      (((dirs.map (fun dn => dn.2.length)).sum) * (12 * FineScale)) := by
  have hit : PhaseGroupSpec M
      (IterSeqEnv (fun dn => M5DirStepEnv dn.1 dn.2) dirs)
      (((dirs.map (fun dn => dn.2.length)).sum) * (12 * FineScale)) := by
    induction dirs with
    | nil => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    | cons dn dns ih =>
        refine ((m5DirStepEnv_groupSpec M dn.1 dn.2).seq ih).mono ?_
        simp [List.map_cons, List.sum_cons, Nat.add_mul]
  exact (hit.seq (PhaseGroupSpec.freeOnly M)).mono (by omega)

theorem cliWriteStdoutEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M CliWriteStdoutEnv (3 * FineScale) :=
  ((PhaseGroupSpec.nil M).or (PhaseGroupSpec.rustAlloc_any M 1024 1)).mono (by omega)

theorem m6Env_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (ok : Bool) :
    PhaseGroupSpec M (M6Env ok) (3 * FineScale) := by
  have h1 : PhaseGroupSpec M (if ok then CliWriteStdoutEnv else (· = [])) (3 * FineScale) := by
    cases ok
    · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    · exact cliWriteStdoutEnv_groupSpec M
  exact (h1.seq (PhaseGroupSpec.freeOnly M)).mono (by omega)

theorem cliMainSetupEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (uuidParse : UuidParser) (i : Inputs) (addrOpt : Option AddressCall) (needStdin : Bool) :
    PhaseGroupSpec M (CliMainSetupEnv uuidParse i addrOpt needStdin)
      ((i.argv.length + 21) * (3 * FineScale)) := by
  have hm1 := m1PhaseEnv_groupSpec M i.argv.length
  have hm2 := m2CollectEnv_groupSpec M i.argv.length
  have had : PhaseGroupSpec M
      (match addrOpt with | none => (· = []) | some ag => AddressEnv uuidParse ag)
      (3 * FineScale) := by
    cases addrOpt
    · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    · rename_i ag; exact addressEnv_groupSpec M uuidParse ag
  have hm3 := m3PhaseEnv_groupSpec M needStdin i.stdin
    (initFsState (cliInputs i)).files (utf8 "coins")
  refine (hm1.seq (hm2.seq (had.seq hm3))).mono ?_
  rw [Nat.add_mul]
  omega

/-- Tight `fineCostModel` setup group bound (`4,366,658` = `67` groups) when `i.argv.length ≤ 3`. -/
def cliMainSetupFineGrpS : Nat :=
  24623 + 3 * (3 * FineScale) + 16659 + 57 * FineScale

theorem cliMainSetupEnv_le_3_fine_groupSpec
    (uuidParse : UuidParser) {i : Inputs} (hargv : i.argv.length ≤ 3)
    (addrOpt : Option AddressCall) (needStdin : Bool) :
    PhaseGroupSpec fineCostModel (CliMainSetupEnv uuidParse i addrOpt needStdin)
      cliMainSetupFineGrpS := by
  have hm1 := m1PhaseEnv_le_3_fine_groupSpec hargv
  have hm2 := (m2CollectEnv_groupSpec fineCostModel i.argv.length).mono
    (Nat.mul_le_mul_right (3 * FineScale) hargv)
  have had : PhaseGroupSpec fineCostModel
      (match addrOpt with | none => (· = []) | some ag => AddressEnv uuidParse ag) 16659 := by
    cases addrOpt
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rename_i ag; exact addressEnv_fine_groupSpec uuidParse ag
  have hm3 := m3PhaseEnv_groupSpec fineCostModel needStdin i.stdin
    (initFsState (cliInputs i)).files (utf8 "coins")
  exact (hm1.seq (hm2.seq (had.seq hm3))).mono (by decide)

theorem cliMainEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {g_setup g_run : Nat}
    (hsetup : PhaseGroupSpec M (CliMainSetupEnv uuidParse g.i addrOpt needStdin) g_setup)
    (hrun : PhaseGroupSpec M (RunEnv g) g_run) :
    PhaseGroupSpec M (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok)
      (g_setup + g_run + ((dirs.map (fun dn => dn.2.length)).sum) * (12 * FineScale) +
        3 * FineScale) := by
  have htail := (PhaseGroupSpec.freeOnly M).or
    (hrun.seq ((m5PhaseEnv_groupSpec M dirs).seq (m6Env_groupSpec M ok)))
  exact (hsetup.seq htail).mono (by omega)

end LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
