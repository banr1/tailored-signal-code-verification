/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433Placed
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable S3 Commit Sub-Segment on Block `433`

Defines pinned and unpinned budget-threaded S3 commit seams (`+0x8ac → +0x3e4`) under
`RustCliAllocBudget M` and proves both no-OOM and conditional-OOM seam theorems for block `433`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open Arm64 ProofLib
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair RatchetState ReceiverChain RootKey SenderChain
  SessionState TripleRatchet
)
open CryptoVerification (
  LibsignalPlacement lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser protocolAddressAt sessionStateAt signalMessageAt uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost TryDecryptGhost extHookStack trAt
)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack dropChainStackX)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkPl_434 growOneChainStackX tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (growOneStack)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ConsumeMsgKeyStatePlaced
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudgetAux (
  dhCommit_pinned_withStack_env_of_wp
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (growOneChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpec chainKeyToPbSpecX framelessMemcpyBudgetSpec noAllocShimBudgetSpec
  publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  tryDecryptFnOnPanic tryDecryptOnPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (
  DhCommitBlockVmWp dhCommitBlockVmWp_549
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (growOneSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (
  tryDecryptOnPanicTight tryDecryptOnPanicTight_weaken
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  s3AfterCaps trGhostCaps
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropChainSpec dropChainSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)

export LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (
  DhCommitEnv dhCommitAllocEvents s3CommitDefaultEnv
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Budget-Threaded `CliDhCommitStatePlaced` and S3 Commit Seams -/

/-- Budget-threaded CLI relocatable `[LibsignalPlacement]` S3 commit checkpoint state at
`entry + 2220#64` (`+0x8ac`). -/
def CliDhCommitStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.CliDhCommitStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 receiverChainKey newSenderKey
    finalRootKey senderChainKey R s0 s

/-- Pinned tight-panic CLI S3 commit seam (`+0x8ac → +0x3e4` or `tryDecryptOnPanicTight`),
recording `trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length`. -/
def CliS3CommitSeamPinnedTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State),
    tr.ratchet.senderChain = some sc →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
    FitsEnv M lim st (s3CommitEnv x trG tr) →
    CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s →
    prog.CodeLoaded s.mem →
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s', Steps prog s s' ∧ ((∃ evs trG', s3CommitEnv x trG tr evs ∧
          trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧ (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))

/-- Unpinned tight-panic CLI S3 commit seam (`+0x8ac → +0x3e4` or `tryDecryptOnPanicTight`). -/
def CliS3CommitSeamTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State),
    tr.ratchet.senderChain = some sc →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
    FitsEnv M lim st (s3CommitEnv x trG tr) →
    CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s →
    prog.CodeLoaded s.mem →
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s', Steps prog s s' ∧ ((∃ evs trG', s3CommitEnv x trG tr evs ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧ (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))

/-- Pinned loose-panic CLI S3 commit seam (`+0x8ac → +0x3e4` or `tryDecryptOnPanic`). -/
def CliS3CommitSeamPinnedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State),
    tr.ratchet.senderChain = some sc →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
    FitsEnv M lim st (s3CommitEnv x trG tr) →
    CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s →
    prog.CodeLoaded s.mem →
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s', Steps prog s s' ∧ ((∃ evs trG', s3CommitEnv x trG tr evs ∧
          trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧ (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))

/-- Unpinned loose-panic budget-threaded CLI S3 commit seam (`+0x8ac → +0x3e4` or `tryDecryptOnPanic`). -/
def CliS3CommitSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State),
    tr.ratchet.senderChain = some sc →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
    FitsEnv M lim st (s3CommitEnv x trG tr) →
    CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s →
    prog.CodeLoaded s.mem →
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s', Steps prog s s' ∧ ((∃ evs trG', s3CommitEnv x trG tr evs ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧ (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))

/-- Pinned `Stage2ContractsX` (`X`) budget-threaded CLI S3 commit seam. -/
def CliS3CommitSeamPinnedXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State),
    tr.ratchet.senderChain = some sc →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
    FitsEnv M lim st (s3CommitEnv x trG tr) →
    CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s →
    prog.CodeLoaded s.mem →
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s', Steps prog s s' ∧ ((∃ evs trG', s3CommitEnv x trG tr evs ∧
          trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧ (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))

/-- Unpinned `Stage2ContractsX` (`X`) budget-threaded CLI S3 commit seam. -/
def CliS3CommitSeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State),
    tr.ratchet.senderChain = some sc →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
    FitsEnv M lim st (s3CommitEnv x trG tr) →
    CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s →
    prog.CodeLoaded s.mem →
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s', Steps prog s s' ∧ ((∃ evs trG', s3CommitEnv x trG tr evs ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧ (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))

/-! ## Seam Weakening Projections -/

theorem CliS3CommitSeamPinnedTightPlaced.toUnpinned [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop}
    (h : CliS3CommitSeamPinnedTightPlaced prog entry C A lim ctl parse S s3CommitEnv) :
    CliS3CommitSeamTightPlaced prog entry C A lim ctl parse S s3CommitEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', hsteps, ⟨evs, trG', henv, _, hcmk⟩ | hpan⟩ :=
    h x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  · exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hcmk⟩⟩
  · exact ⟨s', hsteps, Or.inr hpan⟩

theorem CliS3CommitSeamPinnedPlaced.ofTight [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop}
    (h : CliS3CommitSeamPinnedTightPlaced prog entry C A lim ctl parse S s3CommitEnv) :
    CliS3CommitSeamPinnedPlaced prog entry C A lim ctl parse S s3CommitEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩ :=
    h x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  · exact ⟨s', hsteps, Or.inl hok⟩
  · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩⟩

theorem CliS3CommitSeamPinnedPlaced.toUnpinned [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop}
    (h : CliS3CommitSeamPinnedPlaced prog entry C A lim ctl parse S s3CommitEnv) :
    CliS3CommitSeamPlaced prog entry C A lim ctl parse S s3CommitEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', hsteps, ⟨evs, trG', henv, _, hcmk⟩ | hpan⟩ :=
    h x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  · exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hcmk⟩⟩
  · exact ⟨s', hsteps, Or.inr hpan⟩

theorem CliS3CommitSeamPlaced.ofTight [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop}
    (h : CliS3CommitSeamTightPlaced prog entry C A lim ctl parse S s3CommitEnv) :
    CliS3CommitSeamPlaced prog entry C A lim ctl parse S s3CommitEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩ :=
    h x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  · exact ⟨s', hsteps, Or.inl hok⟩
  · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩⟩

theorem CliS3CommitSeamPinnedXPlaced.toUnpinned [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop}
    (h : CliS3CommitSeamPinnedXPlaced prog entry C decFn A lim ctl parse S s3CommitEnv) :
    CliS3CommitSeamXPlaced prog entry C decFn A lim ctl parse S s3CommitEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', hsteps, ⟨evs, trG', henv, _, hcmk⟩ | hpan⟩ :=
    h x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  · exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hcmk⟩⟩
  · exact ⟨s', hsteps, Or.inr hpan⟩

/-! ## Total-Correctness `Steps` Entrypoints -/

/-- Pinned-capacity total-correctness CLI S3 Commit (`+0x8ac → +0x3e4`, zero panic branch)
at `allocHookStack`. -/
theorem dhCommit_cli_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hclamp : clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes)
    (hfits : FitsEnv M lim st (s3CommitDefaultEnv x trG tr))
    (hS3 : CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s)
    (hL : prog.CodeLoaded s.mem)
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s' evs trG',
      Steps prog s s' ∧ s3CommitDefaultEnv x trG tr evs ∧
      trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
      ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
        x trG' { tr with ratchet := r1 } st1 receiverChainKey (min 32 x.rest.length) R s0 s' := by
  rcases hS3 with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htr, hcro, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx25, hx27, hx28, msgW, hmsgW, hm⟩
  have hm_env : s.mem ⊨
      sessionStateAt (A.atState lim st s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st s) ((s0.sp - 1504#64) + 0x38#64) trG
        { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗ memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x10 ∗
      (((s0.sp - 1504#64) + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion ((s0.sp - 1504#64) + 0x14#64) 8 ∗ (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗ (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗ (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗ (((s0.sp - 1504#64) + 0x190#64) ↦₃₂ 0#32) ∗
      (((s0.sp - 1504#64) + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      (((s0.sp - 1504#64) + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion ((s0.sp - 1504#64) + 0x1d8#64) 0xd8 ∗ memRegion ((s0.sp - 1504#64) + 0x2b0#64) 0x10 ∗
      memRegion ((s0.sp - 1504#64) + 0x2c0#64) 0x110 ∗
      (((s0.sp - 1504#64) + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion ((s0.sp - 1504#64) + 0x3f4#64) 12 ∗
      (((s0.sp - 1504#64) + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      (((s0.sp - 1504#64) + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 0x440#64) 0x80 ∗
      (((s0.sp - 1504#64) + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      (((s0.sp - 1504#64) + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion ((s0.sp - 1504#64) + 0x4e0#64) 0xa0 ∗
      (protocolAddressAt (A.atState lim st s) x.rem x.remA ∗
       protocolAddressAt (A.atState lim st s) x.loc x.locA ∗
       signalMessageAt (A.atState lim st s) x.msgG x.msgA x.msg ∗
       (cliTapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st s) ∗ R := by
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced] at hm ⊢
    refine Satisfies.mono (Entails.of_eq ?_) hm
    sep_ac_rfl
  obtain ⟨sf, evs, trG', hsteps, henv, hcaps, hpcf,
      ⟨hrunf, hspf, hsp0_alignf, hsp_alignf, hx29f, htrf, hvregsf⟩,
      hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hmf⟩ :=
    dhCommit_pinned_withStack_env_of_wp hwp A lim st allocHookStack growOneStack dropChainStack
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      (cliTapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗
       CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff) R s0 s
      hsc hrc_len hclamp hfits hpc hrun hsp hsp0_align hsp_align hx29 htr hvregs
      hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx28 msgW hmsgW hm_env hL
  refine ⟨sf, evs, trG', hsteps, henv, hcaps, hpcf,
    ⟨hrunf, hspf, hsp0_alignf, hsp_alignf, hx29f, htrf, hcro.of_keepsFrozen hsteps.keepsFrozen, hvregsf⟩,
    hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, ?_⟩
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced]
  refine Satisfies.mono (Entails.of_eq ?_) hmf
  sep_ac_rfl

/-- Unpinned total-correctness CLI S3 Commit (`+0x8ac → +0x3e4`, zero panic branch)
at `allocHookStack`. -/
theorem dhCommit_cli_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hclamp : clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes)
    (hfits : FitsEnv M lim st (s3CommitDefaultEnv x trG tr))
    (hS3 : CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s)
    (hL : prog.CodeLoaded s.mem)
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s' evs trG',
      Steps prog s s' ∧ s3CommitDefaultEnv x trG tr evs ∧
      ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
        x trG' { tr with ratchet := r1 } st1 receiverChainKey (min 32 x.rest.length) R s0 s' := by
  obtain ⟨s', evs, trG', hsteps, henv, _, hpost⟩ :=
    dhCommit_cli_pinned_placed_ok hwp A lim st ctl hPkSer hToPb hGrowOne hDropChain
      hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  exact ⟨s', evs, trG', hsteps, henv, hpost⟩

/-- Pinned-capacity total-correctness CLI S3 Commit (`+0x8ac → +0x3e4`, zero panic branch)
at `extHookStack` (`X`). -/
theorem dhCommit_cli_pinned_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpecX M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hclamp : clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes)
    (hfits : FitsEnv M lim st (s3CommitDefaultEnv x trG tr))
    (hS3 : CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s)
    (hL : prog.CodeLoaded s.mem)
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s' evs trG',
      Steps prog s s' ∧ s3CommitDefaultEnv x trG tr evs ∧
      trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
      ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
        x trG' { tr with ratchet := r1 } st1 receiverChainKey (min 32 x.rest.length) R s0 s' := by
  rcases hS3 with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htr, hcro, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx25, hx27, hx28, msgW, hmsgW, hm⟩
  have hm_env : s.mem ⊨
      sessionStateAt (A.atState lim st s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st s) ((s0.sp - 1504#64) + 0x38#64) trG
        { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗ memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x10 ∗
      (((s0.sp - 1504#64) + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion ((s0.sp - 1504#64) + 0x14#64) 8 ∗ (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗ (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗ (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗ (((s0.sp - 1504#64) + 0x190#64) ↦₃₂ 0#32) ∗
      (((s0.sp - 1504#64) + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      (((s0.sp - 1504#64) + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion ((s0.sp - 1504#64) + 0x1d8#64) 0xd8 ∗ memRegion ((s0.sp - 1504#64) + 0x2b0#64) 0x10 ∗
      memRegion ((s0.sp - 1504#64) + 0x2c0#64) 0x110 ∗
      (((s0.sp - 1504#64) + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion ((s0.sp - 1504#64) + 0x3f4#64) 12 ∗
      (((s0.sp - 1504#64) + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      (((s0.sp - 1504#64) + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 0x440#64) 0x80 ∗
      (((s0.sp - 1504#64) + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      (((s0.sp - 1504#64) + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion ((s0.sp - 1504#64) + 0x4e0#64) 0xa0 ∗
      (protocolAddressAt (A.atState lim st s) x.rem x.remA ∗
       protocolAddressAt (A.atState lim st s) x.loc x.locA ∗
       signalMessageAt (A.atState lim st s) x.msgG x.msgA x.msg ∗
       (cliTapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st s) ∗ R := by
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced] at hm ⊢
    refine Satisfies.mono (Entails.of_eq ?_) hm
    sep_ac_rfl
  obtain ⟨sf, evs, trG', hsteps, henv, hcaps, hpcf,
      ⟨hrunf, hspf, hsp0_alignf, hsp_alignf, hx29f, htrf, hvregsf⟩,
      hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hmf⟩ :=
    dhCommit_pinned_withStack_env_of_wp hwp A lim st extHookStack growOneChainStackX dropChainStackX
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      (cliTapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗
       CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff) R s0 s
      hsc hrc_len hclamp hfits hpc hrun hsp hsp0_align hsp_align hx29 htr hvregs
      hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx28 msgW hmsgW hm_env hL
  refine ⟨sf, evs, trG', hsteps, henv, hcaps, hpcf,
    ⟨hrunf, hspf, hsp0_alignf, hsp_alignf, hx29f, htrf, hcro.of_keepsFrozen hsteps.keepsFrozen, hvregsf⟩,
    hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, ?_⟩
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced]
  refine Satisfies.mono (Entails.of_eq ?_) hmf
  sep_ac_rfl

/-- Unpinned total-correctness CLI S3 Commit (`+0x8ac → +0x3e4`, zero panic branch)
at `extHookStack` (`X`). -/
theorem dhCommit_cli_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpecX M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hclamp : clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes)
    (hfits : FitsEnv M lim st (s3CommitDefaultEnv x trG tr))
    (hS3 : CliDhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s)
    (hL : prog.CodeLoaded s.mem)
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s' evs trG',
      Steps prog s s' ∧ s3CommitDefaultEnv x trG tr evs ∧
      ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
        x trG' { tr with ratchet := r1 } st1 receiverChainKey (min 32 x.rest.length) R s0 s' := by
  obtain ⟨s', evs, trG', hsteps, henv, _, hpost⟩ :=
    dhCommit_cli_pinned_x_placed_ok hwp A lim st ctl hPkSer hToPb hGrowOne hDropChain
      hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  exact ⟨s', evs, trG', hsteps, henv, hpost⟩

/-! ## Generic Placed and Block `433` Seam Theorems -/

theorem s3_commit_pinned_tight_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    CliS3CommitSeamPinnedTightPlaced prog entry C A lim ctl parse S s3CommitDefaultEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', evs, trG', hsteps, henv, hcaps, hpost⟩ :=
    dhCommit_cli_pinned_placed_ok hwp A lim st ctl hPkSer hToPb hGrowOne hDropChain
      hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hcaps, hpost⟩⟩

theorem s3_commit_tight_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    CliS3CommitSeamTightPlaced prog entry C A lim ctl parse S s3CommitDefaultEnv :=
  (s3_commit_pinned_tight_placed_ok_cli hwp C A lim ctl parse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem s3_commit_pinned_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    CliS3CommitSeamPinnedPlaced prog entry C A lim ctl parse S s3CommitDefaultEnv :=
  CliS3CommitSeamPinnedPlaced.ofTight (s3_commit_pinned_tight_placed_ok_cli hwp C A lim ctl parse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove)

theorem s3_commit_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    CliS3CommitSeamPlaced prog entry C A lim ctl parse S s3CommitDefaultEnv :=
  (s3_commit_pinned_placed_ok_cli hwp C A lim ctl parse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem s3_commit_pinned_x_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpecX M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    CliS3CommitSeamPinnedXPlaced prog entry C decFn A lim ctl parse S s3CommitDefaultEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', evs, trG', hsteps, henv, hcaps, hpost⟩ :=
    dhCommit_cli_pinned_x_placed_ok hwp A lim st ctl hPkSer hToPb hGrowOne hDropChain
      hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hcaps, hpost⟩⟩

theorem s3_commit_x_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpecX M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX))
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    CliS3CommitSeamXPlaced prog entry C decFn A lim ctl parse S s3CommitDefaultEnv :=
  (s3_commit_pinned_x_placed_ok_cli hwp C decFn A lim ctl parse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem s3_commit_433_pinned_tight_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    CliS3CommitSeamPinnedTightPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  s3_commit_pinned_tight_placed_ok_cli (dhCommitBlockVmWp_549 H) C A lim ctl uuidTryParse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

theorem s3_commit_433_pinned_tight_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    CliS3CommitSeamPinnedTightPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  s3_commit_433_pinned_tight_placed_ok H C A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim (subroutine_ok_allocNoOom_of_budget hAlloc)
    hDealloc hMemcpy hMemmove

theorem s3_commit_433_tight_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    CliS3CommitSeamTightPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  (s3_commit_433_pinned_tight_placed_ok H C A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem s3_commit_433_tight_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    CliS3CommitSeamTightPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  (s3_commit_433_pinned_tight_budget_placed_ok H C A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem s3_commit_433_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    CliS3CommitSeamPinnedPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  CliS3CommitSeamPinnedPlaced.ofTight (s3_commit_433_pinned_tight_placed_ok H C A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove)

theorem s3_commit_433_pinned_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    CliS3CommitSeamPinnedPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  CliS3CommitSeamPinnedPlaced.ofTight (s3_commit_433_pinned_tight_budget_placed_ok H C A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove)

theorem s3_commit_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    CliS3CommitSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  (s3_commit_433_pinned_placed_ok H C A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem s3_commit_433_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    CliS3CommitSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  (s3_commit_433_pinned_budget_placed_ok H C A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem s3_commit_433_pinned_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpecX M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX)) :
    CliS3CommitSeamPinnedXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C decFn A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  s3_commit_pinned_x_placed_ok_cli (dhCommitBlockVmWp_549 H) C decFn A lim ctl uuidTryParse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

theorem s3_commit_433_pinned_x_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpecX M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX)) :
    CliS3CommitSeamPinnedXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C decFn A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  s3_commit_433_pinned_x_placed_ok H C decFn A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim (subroutine_ok_allocNoOom_of_budget hAlloc)
    hDealloc hMemcpy hMemmove

theorem s3_commit_433_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpecX M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX)) :
    CliS3CommitSeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C decFn A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  (s3_commit_433_pinned_x_placed_ok H C decFn A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem s3_commit_433_x_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205)
      (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22)
      (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43)
      (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445)
      (dropChainSpecX M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX)) :
    CliS3CommitSeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C decFn A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  (s3_commit_433_pinned_x_budget_placed_ok H C decFn A lim ctl S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget
