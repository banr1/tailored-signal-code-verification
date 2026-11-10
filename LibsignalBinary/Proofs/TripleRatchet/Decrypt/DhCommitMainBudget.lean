/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded DH Step Commit Sub-Segment (`+0x8ac → +0x3e4`)

Re-exports `DhCommitMainBudgetCore` and proves the relocatable `[LibsignalPlacement]`
budget-threaded commit contracts (`DhCommitStatePlaced`, `S3CommitSeamPlaced`, `S3CommitSeamXPlaced`,
`dhCommit_placed_ok`, `s3_commit_placed_ok`, and block `130` / `433` specializations) over
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudget

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
  UuidParser protocolAddressAt sessionStateAt signalMessageAt tapeAfter uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost TryDecryptGhost extHookStack logOff trAt
)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack dropChainStackX)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_131 blkPC_434 blkPl_131 blkPl_434 growOneChainStackX
  tryDecryptCommonHeap tryDecryptPlacedImg tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (growOneStack)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (growOneChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpec chainKeyToPbSpecX framelessMemcpyBudgetSpec noAllocShimBudgetSpec
  publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  ConsumeMsgKeyStatePlaced tryDecryptFnOnPanic tryDecryptOnPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (growOneSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropChainSpec dropChainSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)

open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (
  DhCommitBlockVmWp dhCommitBlockVmWp_159 dhCommitBlockVmWp_549
  dhCommit_withStack_env_of_wp fitsEvents_of_fitsEnv_dhCommitEnv
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (
  DhCommitEnv dhCommitAllocEvents s3CommitDefaultEnv
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Budget-Threaded `DhCommitStatePlaced`, `S3CommitSeamPlaced`, and `S3CommitSeamXPlaced` -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` S3 commit checkpoint state at `entry + 0x8ac`. -/
def DhCommitStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 receiverChainKey newSenderKey
    finalRootKey senderChainKey R s0 s

/-- Budget-threaded relocatable `[LibsignalPlacement]` S3 commit seam (`+0x8ac → +0x3e4` or panic). -/
def S3CommitSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    DhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
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
    ∃ s', Steps prog s s' ∧
      ((∃ evs trG', s3CommitEnv x trG tr evs ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))

/-- `Stage2ContractsX` (`X`) budget-threaded relocatable `[LibsignalPlacement]` S3 commit seam. -/
def S3CommitSeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    DhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
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
    ∃ s', Steps prog s s' ∧
      ((∃ evs trG', s3CommitEnv x trG tr evs ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))

/-! ## 2. Relocatable `[LibsignalPlacement]` Total-Correctness & Seam Entrypoints -/

/-- Total-correctness S3 Commit (`+0x8ac → +0x3e4`, zero panic branch) at `allocHookStack`. -/
theorem dhCommit_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    (hS3 : DhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
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
      Steps prog s s' ∧
      s3CommitDefaultEnv x trG tr evs ∧
      ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
        x trG' { tr with ratchet := r1 } st1 receiverChainKey (min 32 x.rest.length) R s0 s' := by
  rcases hS3 with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htr, hcro, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx25, hx27, hx28, msgW, hmsgW, hm⟩
  have hm_env : s.mem ⊨
      sessionStateAt (A.atState lim st s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st s) ((s0.sp - 1504#64) + 0x38#64) trG
        { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x10 ∗
      (((s0.sp - 1504#64) + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion ((s0.sp - 1504#64) + 0x14#64) 8 ∗
      (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      (((s0.sp - 1504#64) + 0x190#64) ↦₃₂ 0#32) ∗
      (((s0.sp - 1504#64) + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      (((s0.sp - 1504#64) + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion ((s0.sp - 1504#64) + 0x1d8#64) 0xd8 ∗
      memRegion ((s0.sp - 1504#64) + 0x2b0#64) 0x10 ∗
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
       (tapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗ logOff tryDecryptPlacedImg) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st s) ∗ R := by
    dsimp only [tryDecryptCommonHeap] at hm ⊢
    refine Satisfies.mono (Entails.of_eq ?_) hm
    sep_ac_rfl
  obtain ⟨sf, evs, trG', hsteps, henv, hpcf,
      ⟨hrunf, hspf, hsp0_alignf, hsp_alignf, hx29f, htrf, hvregsf⟩,
      hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hmf⟩ :=
    dhCommit_withStack_env_of_wp hwp A lim st allocHookStack growOneStack dropChainStack
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      (tapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗ logOff tryDecryptPlacedImg) R s0 s
      hsc hrc_len hclamp hfits hpc hrun hsp hsp0_align hsp_align hx29 htr hvregs
      hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx28 msgW hmsgW hm_env hL
  refine ⟨sf, evs, trG', hsteps, henv, hpcf,
    ⟨hrunf, hspf, hsp0_alignf, hsp_alignf, hx29f, htrf, hcro.of_keepsFrozen hsteps.keepsFrozen, hvregsf⟩,
    hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, ?_⟩
  dsimp only [tryDecryptCommonHeap]
  refine Satisfies.mono (Entails.of_eq ?_) hmf
  sep_ac_rfl

/-- Total-correctness S3 Commit (`+0x8ac → +0x3e4`, zero panic branch) at `extHookStack` (`X`). -/
theorem dhCommit_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    (hS3 : DhCommitStatePlaced entry A lim st ctl x trG tr st1 receiverChainKey newSenderKey
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
      Steps prog s s' ∧
      s3CommitDefaultEnv x trG tr evs ∧
      ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
        x trG' { tr with ratchet := r1 } st1 receiverChainKey (min 32 x.rest.length) R s0 s' := by
  rcases hS3 with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htr, hcro, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx25, hx27, hx28, msgW, hmsgW, hm⟩
  have hm_env : s.mem ⊨
      sessionStateAt (A.atState lim st s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st s) ((s0.sp - 1504#64) + 0x38#64) trG
        { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x10 ∗
      (((s0.sp - 1504#64) + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion ((s0.sp - 1504#64) + 0x14#64) 8 ∗
      (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗
      (((s0.sp - 1504#64) + 0x190#64) ↦₃₂ 0#32) ∗
      (((s0.sp - 1504#64) + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      (((s0.sp - 1504#64) + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion ((s0.sp - 1504#64) + 0x1d8#64) 0xd8 ∗
      memRegion ((s0.sp - 1504#64) + 0x2b0#64) 0x10 ∗
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
       (tapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗ logOff tryDecryptPlacedImg) ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st s) ∗ R := by
    dsimp only [tryDecryptCommonHeap] at hm ⊢
    refine Satisfies.mono (Entails.of_eq ?_) hm
    sep_ac_rfl
  obtain ⟨sf, evs, trG', hsteps, henv, hpcf,
      ⟨hrunf, hspf, hsp0_alignf, hsp_alignf, hx29f, htrf, hvregsf⟩,
      hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hmf⟩ :=
    dhCommit_withStack_env_of_wp hwp A lim st extHookStack growOneChainStackX dropChainStackX
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      (tapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗ logOff tryDecryptPlacedImg) R s0 s
      hsc hrc_len hclamp hfits hpc hrun hsp hsp0_align hsp_align hx29 htr hvregs
      hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx28 msgW hmsgW hm_env hL
  refine ⟨sf, evs, trG', hsteps, henv, hpcf,
    ⟨hrunf, hspf, hsp0_alignf, hsp_alignf, hx29f, htrf, hcro.of_keepsFrozen hsteps.keepsFrozen, hvregsf⟩,
    hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, ?_⟩
  dsimp only [tryDecryptCommonHeap]
  refine Satisfies.mono (Entails.of_eq ?_) hmf
  sep_ac_rfl

/-- Top-level proof of `S3CommitSeamPlaced` (`+0x8ac → +0x3e4` or panic) for any placed block. -/
theorem s3_commit_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    S3CommitSeamPlaced prog entry C A lim ctl parse S s3CommitDefaultEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', evs, trG', hsteps, henv, hpost⟩ :=
    dhCommit_placed_ok hwp A lim st ctl hPkSer hToPb hGrowOne hDropChain
      hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hpost⟩⟩

/-- Conditional-OOM (`rustCliAllocBudgetSpec`) wrapper for `s3_commit_placed_ok`. -/
theorem s3_commit_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpec M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
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
    S3CommitSeamPlaced prog entry C A lim ctl parse S s3CommitDefaultEnv :=
  s3_commit_placed_ok hwp C A lim ctl parse S hPkSer hToPb hGrowOne hDropChain
    hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove

/-- Top-level proof of `S3CommitSeamXPlaced` (`+0x8ac → +0x3e4` or panic) at `extHookStack` (`X`). -/
theorem s3_commit_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    S3CommitSeamXPlaced prog entry C decFn A lim ctl parse S s3CommitDefaultEnv := by
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', evs, trG', hsteps, henv, hpost⟩ :=
    dhCommit_x_placed_ok hwp A lim st ctl hPkSer hToPb hGrowOne hDropChain
      hShim hAlloc hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hpost⟩⟩

/-- Conditional-OOM (`rustCliAllocBudgetSpec`) wrapper for `s3_commit_x_placed_ok`. -/
theorem s3_commit_x_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
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
    S3CommitSeamXPlaced prog entry C decFn A lim ctl parse S s3CommitDefaultEnv :=
  s3_commit_x_placed_ok hwp C decFn A lim ctl parse S hPkSer hToPb hGrowOne hDropChain
    hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove

/-- S3 Commit seam (`S3CommitSeamPlaced`) for Block `130` (`try_decrypt_with_state::<HookRng>`). -/
theorem s3_commit_159_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 205)
      (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 22)
      (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 43)
      (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 142)
      (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3CommitSeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 131)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  s3_commit_placed_ok (dhCommitBlockVmWp_159 H) C A lim ctl uuidTryParse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

/-- S3 Commit seam (`S3CommitSeamXPlaced`) for Block `130` (`try_decrypt_with_state::<HookRng>`). -/
theorem s3_commit_159_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hPkSer : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 205)
      (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 22)
      (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 43)
      (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 142)
      (dropChainSpecX M A lim))
    (hShim : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX)) :
    S3CommitSeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 131)
      C decFn A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  s3_commit_x_placed_ok (dhCommitBlockVmWp_159 H) C decFn A lim ctl uuidTryParse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

/-- S3 Commit seam (`S3CommitSeamPlaced`) for Block `433` (`try_decrypt_with_state::<Coins>`). -/
theorem s3_commit_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    S3CommitSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  s3_commit_placed_ok (dhCommitBlockVmWp_549 H) C A lim ctl uuidTryParse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

/-- S3 Commit seam (`S3CommitSeamXPlaced`) for Block `433` (`try_decrypt_with_state::<Coins>`). -/
theorem s3_commit_549_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    S3CommitSeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C decFn A lim ctl uuidTryParse S s3CommitDefaultEnv :=
  s3_commit_x_placed_ok (dhCommitBlockVmWp_549 H) C decFn A lim ctl uuidTryParse S
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudget
