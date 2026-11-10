/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMain
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep5
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
import ProofLib.RegChain

/-!
# Budget-Threaded DH Step Commit Core Composition (`+0x8ac → +0x3e4`)

Defines the `dhCommit` allocator event envelopes (`dhCommitAllocEvents`, `DhCommitEnv`,
`s3CommitDefaultEnv`), the `DhCommitBlockVmWp` bundle with block `130` and `433` instances, and the
stack- and environment-parametric total-correctness composition `dhCommit_withStack_env_of_wp`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open Arm64 ProofLib
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey KeyPair RatchetState ReceiverChain RootKey SenderChain
  SessionState TripleRatchet macLength
)
open CryptoVerification (
  LibsignalPlacement lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl
)
open CryptoVerification.RustHeap (allocHookStack vecAt vecBuf vecU8At)
open CryptoVerification.LibsignalSessionRepr (
  chainAt chainKeyBytes msgTypeByte optSenderChainBytes ratchetAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  boxU8At optBoxU8At protocolAddressAt sessionStateAt signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (TrGhost TryDecryptGhost trAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_131 blkPC_434 blkPl_131 blkPl_434
  tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (
  add_assoc_const cell_to_memRegion_8 chainKeyBytes_pointsTo
  newChainGhost newReceiverChain optChainKeyHeap optChainKeyTailBytes
  optSenderChainBytes_some_pointsTo setWidth8_zeroExtend64_shared_lb stackAt_split_from
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts (
  evictGcs le_of_eq_succ_lt map_snd_evictGcs map_snd_zip_append
  sckWord0 sckWord16 sckWord20 sckWord28 sckWord8 vecAt_chains_eq zip_map_fst_snd
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
  SeqEnv fitsEvents_append rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpecWithStack framelessMemcpyBudgetSpec noAllocShimBudgetSpec
  publicKeySerializeSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep4 (
  DhCommitStep45BlockWp dhCommitStep45BlockWp_159 dhCommitStep45BlockWp_549
  dhCommit_evict_one_of_wp dhCommit_step4_of_wp dropChainSpecWithStack evictActiveWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep5 (
  dhCommit_step5_of_wp
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget (
  DhCommitStep12BlockWp dhCommitStep12BlockWp_159 dhCommitStep12BlockWp_549
  dhCommitStep12Events dhCommitStep12Pre dhCommit_step1_2_withStack_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (
  DhCommitStep3BlockWp dhCommitStep3BlockWp_159 dhCommitStep3BlockWp_549
  dhCommitStep3Events dhCommitStep3aEvents dhCommit_step3_of_wp
  fitsEvents_dhCommitStep3a_of_step3 growOneSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Allocator Event Lists, Envelopes, and `DhCommitBlockVmWp` Bundle -/

/-- Deterministic `AllocEvent` prefix emitted by `dhCommit` Steps 1–3 (`+0x8ac → +0xaf0`). -/
def dhCommitAllocEvents (chainsCap rcLen : BitVec 64) : List AllocEvent :=
  dhCommitStep12Events ++ dhCommitStep3Events chainsCap rcLen

/-- Allocation envelope for the full `dhCommit` sub-segment (`+0x8ac → +0x3e4`):
    deterministic Steps 1–3 events followed by `FreeOnlyEvs` from Step 4 receiver-chain eviction. -/
def DhCommitEnv (chainsCap rcLen : BitVec 64) : List AllocEvent → Prop :=
  SeqEnv (· = dhCommitAllocEvents chainsCap rcLen) FreeOnlyEvs

/-- Default `s3CommitEnv` argument for `S3CommitSeamPlaced` / `S3CommitSeamXPlaced`. -/
def s3CommitDefaultEnv (_x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : List AllocEvent → Prop :=
  DhCommitEnv trG.ratchet.chainsCap (BitVec.ofNat 64 tr.ratchet.receiverChains.length)

/-- Extract the Step 1–2 and Step 3a `FitsEvents` obligations from `FitsEnv M lim st0 (DhCommitEnv ...)`. -/
theorem fitsEvents_of_fitsEnv_dhCommitEnv {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {chainsCap rcLen : BitVec 64}
    (hfits : FitsEnv M lim st0 (DhCommitEnv chainsCap rcLen)) :
    FitsEvents M lim st0 dhCommitStep12Events ∧
      FitsEvents M lim (M.stepEvents dhCommitStep12Events st0)
        (dhCommitStep3aEvents chainsCap rcLen) := by
  have h123 : FitsEvents M lim st0 (dhCommitAllocEvents chainsCap rcLen) :=
    hfits (dhCommitAllocEvents chainsCap rcLen) (Or.inl rfl)
  unfold dhCommitAllocEvents at h123
  rw [fitsEvents_append] at h123
  exact ⟨h123.1, fitsEvents_dhCommitStep3a_of_step3 h123.2⟩

/-- Bundled `VmPreserved`-carrying basic-block `SepWP` obligations for `dhCommit` (`+0x8ac → +0x3e4`). -/
structure DhCommitBlockVmWp [LibsignalPlacement] (prog : Program)
    (entry dropChainEntry : BitVec 64) : Prop where
  step12 : DhCommitStep12BlockWp prog entry
  step3 : DhCommitStep3BlockWp prog entry (lsmpl.base 43) (lsmpl.ρ lsRustDeallocSym)
  step45 : DhCommitStep45BlockWp prog entry (lsmpl.ρ "memmove") dropChainEntry

/-- `DhCommitBlockVmWp` instance for Block `130` (`try_decrypt_with_state::<HookRng>`). -/
theorem dhCommitBlockVmWp_159 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitBlockVmWp ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.base 131) (lsmpl.base 142) :=
  ⟨dhCommitStep12BlockWp_159 H, dhCommitStep3BlockWp_159 H, dhCommitStep45BlockWp_159 H⟩

/-- `DhCommitBlockVmWp` instance for Block `433` (`try_decrypt_with_state::<Coins>`). -/
theorem dhCommitBlockVmWp_549 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitBlockVmWp ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.base 434) (lsmpl.base 445) :=
  ⟨dhCommitStep12BlockWp_549 H, dhCommitStep3BlockWp_549 H, dhCommitStep45BlockWp_549 H⟩

/-! ## 2. Core Stack- & Environment-Parametric Total-Correctness Composition -/

/-- Unified total-correctness `Steps` composition for S3 Commit (`+0x8ac → +0x3e4`),
    parameterized by stack heights `(hookStack, growStk, dropStk)` and an untouched environment
    heap predicate `envHeap` (covering both `tapeAfter ∗ logOff` and CLI `coinsAfterPlaced ∗ lsLogOff`). -/
theorem dhCommit_withStack_env_of_wp [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hookStack growStk dropStk : Nat)
    (hhook_lo : allocHookStack ≤ hookStack)
    (hhook_hi : hookStack + 48 < 2 ^ 64)
    (hpb_le : hookStack + 48 ≤ tryDecryptSubStack)
    (_hpb_align : (hookStack + 48) % 16 = 0)
    (hgrow_lo : allocHookStack ≤ growStk)
    (hgrow_hi : growStk < 2 ^ 64)
    (hgrow_le : growStk ≤ tryDecryptSubStack)
    (_hgrow_align : growStk % 16 = 0)
    (hdrop_le : dropStk ≤ tryDecryptSubStack)
    (_hdrop_align : dropStk % 16 = 0)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecWithStack M A lim hookStack))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecWithStack M A lim hookStack))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpecWithStack growStk M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpecWithStack dropStk M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropStk))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (envHeap R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hclamp : clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes)
    (hfits : FitsEnv M lim st0
      (DhCommitEnv trG.ratchet.chainsCap (BitVec.ofNat 64 tr.ratchet.receiverChains.length)))
    (hpc_s : s.pc = entry + 0x8ac#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1504#64)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x3d0#64)
    (msgW : BitVec 32)
    (hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType)
    (hm : s.mem ⊨
      sessionStateAt (A.atState lim st0 s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st0 s) ((s0.sp - 1504#64) + 0x38#64) trG
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
      (protocolAddressAt (A.atState lim st0 s) x.rem x.remA ∗
       protocolAddressAt (A.atState lim st0 s) x.loc x.locA ∗
       signalMessageAt (A.atState lim st0 s) x.msgG x.msgA x.msg ∗
       envHeap ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st0 s) ∗ R)
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
    let sp := s0.sp - 1504#64
    ∃ sf evs trG',
      Steps prog s sf ∧
      DhCommitEnv trG.ratchet.chainsCap (BitVec.ofNat 64 tr.ratchet.receiverChains.length) evs ∧
      sf.pc = entry + 0x3e4#64 ∧
      (sf.status = .Running ∧
       sf.sp = sp ∧
       s0.spAligned = true ∧
       sf.spAligned = true ∧
       sf.readReg64 .x29 = s0.sp - 96#64 ∧
       sf.trace = s0.trace ∧
       calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
      sf.readReg64 .x12 = sp + 0x2c0#64 ∧
      sf.readReg64 .x19 = x.ret ∧
      sf.readReg64 .x20 = sp + 0x140#64 ∧
      sf.readReg64 .x21 = x.ss ∧
      sf.readReg64 .x22 = x.msgA ∧
      sf.readReg64 .x23 = sp + 0x500#64 ∧
      (sf.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
      sf.readReg64 .x25 = sp + 0x190#64 ∧
      (sf.mem ⊨
        sessionStateAt (A.atState lim (M.stepEvents evs st0) sf) x.ss x.G.afterTrFrom st1 ∗
        trAt (A.atState lim (M.stepEvents evs st0) sf) (sp + 0x38#64) trG' { tr with ratchet := r1 } ∗
        memRegion x.ret 48 ∗
        memRegion sp 0x20 ∗
        ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 0x140#64) 0x170 ∗
        ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
        ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗
        memRegion (sp + 0x2d4#64) 0x2ac ∗
        (protocolAddressAt (A.atState lim (M.stepEvents evs st0) sf) x.rem x.remA ∗
         protocolAddressAt (A.atState lim (M.stepEvents evs st0) sf) x.loc x.locA ∗
         signalMessageAt (A.atState lim (M.stepEvents evs st0) sf) x.msgG x.msgA x.msg ∗
         envHeap ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool lim (M.stepEvents evs st0) sf) ∗ R) := by
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
  let sp := s0.sp - 1504#64
  have ⟨hfits12, hfits3a_rc⟩ := fitsEvents_of_fitsEnv_dhCommitEnv hfits
  dsimp only [trAt, ratchetAt, signalMessageAt] at hm
  rw [hsc] at hm
  have h_sc_50_eq :
      ∀ (pad : List (BitVec 8)), pad.length = 100 →
        ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) pad) =
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
         ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗
         ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) := by
    intro pad _hpad
    rw [show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
        optSenderChainBytes_some_pointsTo (sp + 0x50#64) sc pad,
        show sp + 0x50#64 + 4#64 = sp + 0x54#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 36#64 = sp + 0x74#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 68#64 = sp + 0x94#64 from add_assoc_const _ _ _ _,
        chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey,
        show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _]
  have hm_pures : s.mem ⊨
      ⌜∀ sc', some sc = some sc' →
        clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
        trG.ratchet.senderPad.length = 100 ∧
        tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜macLength + 1 ≤ x.msg.serialized.length ∧
        x.msg.serialized.length < 2 ^ 40 ∧
        x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
         (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
       ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) trG.ratchet.senderPad) ∗
       ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
       ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       memRegion (sp + 0x38#64 + 172#64) 4 ∗
       vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
       ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗
       ((sp + 0x1c#64) ↦₃₂ msgW) ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
       memRegion (sp + 0x1d8#64) 0xd8 ∗
       memRegion (sp + 0x2b0#64) 0x10 ∗
       memRegion (sp + 0x2c0#64) 0x110 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
       memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       memRegion (sp + 0x440#64) 0x80 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       memRegion (sp + 0x4e0#64) 0xa0 ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗
       vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
       boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
       boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
       ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
       optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
       ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
       ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
       memRegion (x.msgA + 0x71#64) 7 ∗
       envHeap ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st0 s ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [sp]
    rw [show sessionStateAt (A.atState lim st0 s) = sessionStateAt A.repAlloc from rfl,
        show protocolAddressAt (A.atState lim st0 s) = protocolAddressAt A.repAlloc from rfl,
        show vecAt (A.atState lim st0 s) 104 8 (chainAt (A.atState lim st0 s)) =
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) from rfl,
        show vecU8At (A.atState lim st0 s) = vecU8At A.repAlloc from rfl,
        show boxU8At (A.atState lim st0 s) = boxU8At A.repAlloc from rfl,
        show optBoxU8At (A.atState lim st0 s) = optBoxU8At A.repAlloc from rfl]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨_hclamp_old, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨⟨hchains_len, hpad_len, hmfj⟩, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨hmsg_pure, hm_body⟩
  rw [h_sc_50_eq trG.ratchet.senderPad hpad_len,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 160#64 = sp + 0xd8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 172#64 = sp + 0xe4#64 from add_assoc_const _ _ _ _] at hm_body
  have hsplit_1d8 := memRegion_split (sp + 0x1d8#64) 0x60 0x78 (by decide)
  rw [show (0x60 + 0x78 : Nat) = 0xd8 from rfl,
      show sp + 0x1d8#64 + 96#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hsplit_1d8
  have hsplit_2c0 := memRegion_split (sp + 0x2c0#64) 0x14 0xfc (by decide)
  rw [show (0x14 + 0xfc : Nat) = 0x110 from rfl,
      show sp + 0x2c0#64 + 20#64 = sp + 0x2d4#64 from add_assoc_const _ _ _ _] at hsplit_2c0
  have hsplit_440 := memRegion_split (sp + 0x440#64) 0x10 0x70 (by decide)
  rw [show (0x10 + 0x70 : Nat) = 0x80 from rfl,
      show sp + 0x440#64 + 16#64 = sp + 0x450#64 from add_assoc_const _ _ _ _] at hsplit_440
  have hsplit_450 := memRegion_split (sp + 0x450#64) 0x50 0x20 (by decide)
  rw [show (0x50 + 0x20 : Nat) = 0x70 from rfl,
      show sp + 0x450#64 + 80#64 = sp + 0x4a0#64 from add_assoc_const _ _ _ _] at hsplit_450
  have hsplit_4e0 := memRegion_split (sp + 0x4e0#64) 0x20 0x80 (by decide)
  rw [show (0x20 + 0x80 : Nat) = 0xa0 from rfl,
      show sp + 0x4e0#64 + 32#64 = sp + 0x500#64 from add_assoc_const _ _ _ _] at hsplit_4e0
  have hsplit_500 := memRegion_split (sp + 0x500#64) 0x60 0x20 (by decide)
  rw [show (0x60 + 0x20 : Nat) = 0x80 from rfl,
      show sp + 0x500#64 + 96#64 = sp + 0x560#64 from add_assoc_const _ _ _ _] at hsplit_500
  have hstk_pb := stackAt_split_from sp tryDecryptSubStack (hookStack + 48) hpb_le (by decide)
  rw [hsplit_1d8, hsplit_2c0, hsplit_440, hsplit_450, hsplit_4e0, hsplit_500, hstk_pb] at hm_body
  let BaseFrame : SepProp :=
    sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
    ((sp + 0x50#64) ↦₃₂ 1#32) ∗
    ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
    ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗
    ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
    memRegion (sp + 0xe4#64) 4 ∗
    vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
    ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
    memRegion x.ret 48 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
    memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x238#64) 0x78 ∗
    memRegion (sp + 0x2b0#64) 0x10 ∗
    memRegion (sp + 0x2c0#64) 0x14 ∗
    memRegion (sp + 0x2d4#64) 0xfc ∗
    memRegion (sp + 0x3f4#64) 12 ∗
    ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
    memRegion (sp + 0x450#64) 0x50 ∗
    memRegion (sp + 0x4a0#64) 0x20 ∗
    ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
    memRegion (sp + 0x560#64) 0x20 ∗
    protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗
    vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
    boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
    boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
    optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
    ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
    ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
    ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
    memRegion (x.msgA + 0x71#64) 7 ∗
    envHeap ∗
    tryDecryptSavedRegs s0.sp s0
  let gcs0 := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hsplit_sp16 := memRegion_split sp 12 4 (by decide)
  rw [show (12 + 4 : Nat) = 0x10 from rfl,
      show sp + 12#64 = sp + 0xc#64 from rfl] at hsplit_sp16
  rw [hsplit_sp16] at hm_body
  let Frame12 : SepProp :=
    vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
    memRegion (sp + 0xc#64) 4 ∗
    memRegion (sp + 0x1d8#64) 0x60 ∗
    memRegion (sp + 0x500#64) 0x60 ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - (hookStack + 48)) ∗
    BaseFrame
  have hm_step12 : s.mem ⊨
      dhCommitStep12Pre A lim st0 (hookStack + 48) s sp x.msgA sc.chainKey.index
        tr.ratchet.previousCounter finalRootKey senderChainKey receiverChainKey
        x.msg.senderRatchetKey ∗
      (Frame12 ∗ R) := by
    dsimp only [dhCommitStep12Pre, Frame12, BaseFrame]
    refine Satisfies.mono (Entails.of_eq ?_) hm_body
    sep_ac_rfl
  obtain ⟨s1, hsteps12, boxPtr, srkPtr, ckPtr, pad, hsrk0, hpad, hpc1, hrun1, hsp1, hsp_align1,
      htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
      hvregs_1, hL1, hm1⟩ :=
    dhCommit_step1_2_withStack_placed hwp.step12 A lim st0 hookStack hhook_lo hhook_hi
      hPkSer hShim hAlloc hMemcpy hToPb hfits12
      R Frame12 s0 s sp x.msgA sc.chainKey.index tr.ratchet.previousCounter
      finalRootKey senderChainKey receiverChainKey x.msg.senderRatchetKey
      hpc_s hrun hsp hsp_align htr hx22 hx25 hx27 hx28 hL hm_step12
  let st_12 := M.stepEvents dhCommitStep12Events st0
  have hstk_grow := stackAt_split_from sp tryDecryptSubStack growStk hgrow_le (by decide)
  have hsplit_1d8_32 := memRegion_split (sp + 0x1d8#64) 32 0x40 (by decide)
  rw [show (32 + 0x40 : Nat) = 0x60 from rfl,
      show sp + 0x1d8#64 + 32#64 = sp + 0x1f8#64 from add_assoc_const _ _ _ _] at hsplit_1d8_32
  have hjoin_1b0_72 := (memRegion_split (sp + 0x1b0#64) 40 32 (by decide)).symm
  rw [show (40 + 32 : Nat) = 72 from rfl,
      show sp + 0x1b0#64 + 40#64 = sp + 0x1d8#64 from add_assoc_const _ _ _ _] at hjoin_1b0_72
  have hm1_sp8 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (cell_to_memRegion_8 sp boxPtr))) hm1
  have hm1_prep : s1.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
          (tryDecryptSubStack - (hookStack + 48)) ∗
       stackAt sp (hookStack + 48)) ∗
      (memRegion (sp + 0x1b0#64) 40 ∗ memRegion (sp + 0x1d8#64) 32) ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
      memRegion sp 8 ∗
      ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗
      ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
      ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
      memRegion (sp + 0x1f8#64) 0x40 ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 0x60 ∗
      ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
      (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
      A.pool lim st_12 s1 ∗
      BaseFrame ∗ R := by
    dsimp only [Frame12, st_12] at hm1_sp8 ⊢
    rw [hsplit_1d8_32] at hm1_sp8
    refine Satisfies.mono (Entails.of_eq ?_) hm1_sp8
    sep_ac_rfl
  rw [← hstk_pb, hstk_grow, hjoin_1b0_72, vecAt_chains_eq] at hm1_prep
  let Frame3 : SepProp :=
    memRegion sp 8 ∗
    ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗
    memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗
    ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
    memRegion (sp + 0x1f8#64) 0x40 ∗
    ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
    ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
    ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
    ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x500#64) 0x60 ∗
    ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - growStk) ∗
    BaseFrame
  have hm_step3 : s1.mem ⊨
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs0.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗
       A.pool lim st_12 s1 ∗
       stackAt sp growStk) ∗
      (Frame3 ∗ R) := by
    dsimp only [Frame3]
    refine Satisfies.mono (Entails.of_eq ?_) hm1_prep
    sep_ac_rfl
  have hgcs0_len_eq : gcs0.length = tr.ratchet.receiverChains.length := by
    dsimp only [gcs0]
    rw [List.length_zip, hchains_len, Nat.min_self]
  have hgcs0_len : gcs0.length < 2 ^ 32 := hgcs0_len_eq ▸ hrc_len
  have hfits3a : FitsEvents M lim st_12
      (dhCommitStep3aEvents trG.ratchet.chainsCap (BitVec.ofNat 64 gcs0.length)) := by
    rw [hgcs0_len_eq]
    exact hfits3a_rc
  obtain ⟨s2, hsteps3, cap', ptr', hpc2, hrun2, hsp2, hsp_align2, htr2,
      hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx25_2, hx29_2, hvregs_2, hL2, hm2⟩ :=
    dhCommit_step3_of_wp hwp.step3 hgrow_lo hgrow_hi A lim st_12 hGrowOne hDealloc
      R Frame3 s0 s1 sp trG.ratchet.chainsCap trG.ratchet.chainsPtr boxPtr srkPtr ckPtr gcs0
      x.msg.senderRatchetKey receiverChainKey pad hgcs0_len hpad hsrk0 hfits3a
      hpc1 hrun1 hsp1 hsp_align1 htr1 hx25_1 hx26_1 hx27_1 hx28_1 hL1 hm_step3
  let st_123 := M.stepEvents (dhCommitAllocEvents trG.ratchet.chainsCap
    (BitVec.ofNat 64 tr.ratchet.receiverChains.length)) st0
  have hst_123_eq :
      M.stepEvents (dhCommitStep3Events trG.ratchet.chainsCap (BitVec.ofNat 64 gcs0.length)) st_12 =
        st_123 := by
    dsimp only [st_123, st_12, dhCommitAllocEvents]
    rw [hgcs0_len_eq, ← M.stepEvents_append]
  rw [hst_123_eq] at hm2
  let gcs1 := gcs0 ++ [(newChainGhost srkPtr ckPtr x.msg.senderRatchetKey, newChain)]
  have hstk_drop := stackAt_split_from sp tryDecryptSubStack dropStk hdrop_le (by decide)
  have hjoin_1f8 := (memRegion_split (sp + 0x1f8#64) 0x40 0x78 (by decide)).symm
  rw [show (0x40 + 0x78 : Nat) = 0xb8 from rfl,
      show sp + 0x1f8#64 + 64#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hjoin_1f8
  have hck_94 := (chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey).symm
  rw [show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _] at hck_94
  have hm2_prep : s2.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
          (tryDecryptSubStack - growStk) ∗
       stackAt sp growStk) ∗
      (memRegion (sp + 0x1f8#64) 0x40 ∗ memRegion (sp + 0x238#64) 0x78) ∗
      (((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) ∗
      ((sp + 0x38#64) ↦₆₄ cap') ∗
      ((sp + 0x40#64) ↦₆₄ ptr') ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs1.length) ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) cap' ptr' gcs1 ∗
      memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x500#64) 96 ∗
      memRegion sp 8 ∗
      A.pool lim st_123 s2 ∗
      ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
      memRegion (sp + 0xe4#64) 4 ∗
      vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
      ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
      memRegion x.ret 48 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 0x2c#64) 4 ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x14 ∗
      memRegion (sp + 0x2d4#64) 0xfc ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion (sp + 0x450#64) 0x50 ∗
      memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion (sp + 0x560#64) 0x20 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
      boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
      boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
      optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
      ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
      ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
      ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
      memRegion (x.msgA + 0x71#64) 7 ∗
      envHeap ∗
      tryDecryptSavedRegs s0.sp s0 ∗ R := by
    dsimp only [Frame3, BaseFrame, gcs1, newReceiverChain, newChain] at hm2 ⊢
    refine Satisfies.mono (Entails.of_eq ?_) hm2
    sep_ac_rfl
  rw [← hstk_grow, hstk_drop, hjoin_1f8, hck_94] at hm2_prep
  let TailFrame : SepProp :=
    sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
    ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
    memRegion (sp + 0xe4#64) 4 ∗
    vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
    ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
    memRegion x.ret 48 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗
    vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
    boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
    boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
    ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
    ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
    ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
    ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
    memRegion (x.msgA + 0x71#64) 7 ∗
    envHeap ∗
    tryDecryptSavedRegs s0.sp s0
  let Step5Cells : SepProp :=
    memRegion sp 8 ∗
    ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
    memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
    memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗
    ((sp + 0x50#64) ↦₃₂ 1#32) ∗
    ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
    ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1f8#64) 0xb8 ∗
    memRegion (sp + 0x2b0#64) 0x10 ∗
    memRegion (sp + 0x2c0#64) 0x14 ∗
    memRegion (sp + 0x2d4#64) 0xfc ∗
    ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    memRegion (sp + 0x3f4#64) 12 ∗
    ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
    ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x450#64) 0x50 ∗
    memRegion (sp + 0x4a0#64) 0x20 ∗
    ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
    ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
    ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x560#64) 0x20
  let Frame4 : SepProp :=
    ((sp + 0x38#64) ↦₆₄ cap') ∗
    Step5Cells ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - dropStk) ∗
    TailFrame
  have hm_step4 : s2.mem ⊨
      evictActiveWithStack dropStk A lim st_123 s2 sp cap' ptr' gcs1 ∗ (Frame4 ∗ R) := by
    dsimp only [evictActiveWithStack, Frame4, Step5Cells, TailFrame]
    refine Satisfies.mono (Entails.of_eq ?_) hm2_prep
    sep_ac_rfl
  have hgcs1_len : gcs1.length = tr.ratchet.receiverChains.length + 1 := by
    dsimp only [gcs1, gcs0]
    rw [List.length_append, List.length_zip, hchains_len, Nat.min_self]
    rfl
  have hle4 : gcs1.length ≤ 2 ^ 32 := le_of_eq_succ_lt hgcs1_len hrc_len
  obtain ⟨s3, hsteps4, evs_free, hfree, hpc3, hrun3, hsp3, hsp_align3, htr3,
      hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx29_3, hvregs_3, hL3, hm3⟩ :=
    dhCommit_step4_of_wp A lim st_123 R Frame4 s0 s2 sp cap' ptr'
      hwp.step45.step4a_lo hwp.step45.step4a_ge
      (fun s' st' gc₀ gcs' hlen' hpc' hrun' hsp' hal' htr' hx23' hx24' hx25' hx27' hx28' hL' hm' =>
        dhCommit_evict_one_of_wp A lim st' hwp.step45.step4b_pre_memmove
          hwp.step45.step4b_post_memmove hMemmove hDropChain R Frame4 s0 s' sp cap' ptr' gc₀ gcs'
          hlen' hpc' hrun' hsp' hal' htr' hx23' hx24' hx25' hx27' hx28' hL' hm' hlr_ls)
      hwp.step45.step4c_hi hwp.step45.step4c_le
      gcs1 hle4 hpc2 hrun2 hsp2 hsp_align2 htr2
      (hx23_2.trans (hx23_1.trans hx23)) hx25_2 hL2 hm_step4
  let evs_all := dhCommitAllocEvents trG.ratchet.chainsCap
    (BitVec.ofNat 64 tr.ratchet.receiverChains.length) ++ evs_free
  let st_f := M.stepEvents evs_all st0
  have hst_f_eq : M.stepEvents evs_free st_123 = st_f := by
    dsimp only [st_f, evs_all, st_123]
    exact (M.stepEvents_append _ _ _).symm
  rw [hst_f_eq] at hm3
  let Frame5 : SepProp :=
    vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
    A.pool lim st_f s3 ∗
    stackAt sp tryDecryptSubStack ∗
    TailFrame
  have hm_step5 : s3.mem ⊨
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗
      memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x1f8#64) 0xb8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x14 ∗
      memRegion (sp + 0x2d4#64) 0xfc ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x450#64) 0x50 ∗
      memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
      ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x500#64) 96 ∗
      memRegion (sp + 0x560#64) 0x20 ∗
      (Frame5 ∗ R) := by
    dsimp only [evictActiveWithStack, Frame4, Step5Cells, Frame5, evictGcs] at hm3 ⊢
    rw [vecAt_chains_eq, hstk_drop]
    refine Satisfies.mono (Entails.of_eq ?_) hm3
    sep_ac_rfl
  obtain ⟨sf, hsteps5, hvm5, hpcf, hrunf, hspf, hsp_alignf, htrf,
      hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx29f, _hx30f, hvregsf, _hLf, hmf⟩ :=
    dhCommit_step5_of_wp trG.ratchet.senderPad sc receiverChainKey newSenderKey senderChainKey
      msgW Frame5 R s3 sp hwp.step45.step5 hpc3 hrun3 hsp3 hsp_align3 hx25_3 hL3 hm_step5
  let trG' : TrGhost :=
    { trG with
      ratchet :=
        { trG.ratchet with
          chainsCap := cap'
          chainsPtr := ptr'
          chains := (evictGcs gcs1).map Prod.fst } }
  have henv_all :
      DhCommitEnv trG.ratchet.chainsCap (BitVec.ofNat 64 tr.ratchet.receiverChains.length) evs_all :=
    Or.inr ⟨_, _, rfl, rfl, hfree⟩
  have hsteps_all : Steps prog s sf :=
    ((hsteps12.trans hsteps3).trans hsteps4).trans hsteps5
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 :=
    hx29f.trans (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29)))
  have hx19_f : sf.readReg64 .x19 = x.ret :=
    hx19f.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19)))
  have hx20_f : sf.readReg64 .x20 = sp + 0x140#64 :=
    hx20f.trans (hx20_3.trans (hx20_2.trans (hx20_1.trans hx20)))
  have hx21_f : sf.readReg64 .x21 = x.ss :=
    hx21f.trans (hx21_3.trans (hx21_2.trans (hx21_1.trans hx21)))
  have hx22_f : sf.readReg64 .x22 = x.msgA :=
    hx22f.trans (hx22_3.trans (hx22_2.trans hx22_1))
  have hx23_f : sf.readReg64 .x23 = sp + 0x500#64 :=
    hx23f.trans hx23_3
  have hx24_f : (sf.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
    rw [hx24f, setWidth8_zeroExtend64_shared_lb, hmsgW]
  have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    hvregsf.trans (hvregs_3.trans (hvregs_2.trans (hvregs_1.trans hvregs)))
  refine ⟨sf, evs_all, trG', hsteps_all, henv_all, hpcf,
    ⟨hrunf, hspf, hsp0_align, hsp_alignf, hx29_f, htrf.trans htr3, hvregs_f⟩,
    hx12f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25f, ?_⟩
  have h_map_snd_gcs1 : gcs1.map Prod.snd = tr.ratchet.receiverChains ++ [newChain] :=
    map_snd_zip_append trG.ratchet.chains tr.ratchet.receiverChains
      (newChainGhost srkPtr ckPtr x.msg.senderRatchetKey) newChain hchains_len
  have h_evict_snd : (evictGcs gcs1).map Prod.snd = r1.receiverChains := by
    rw [map_snd_evictGcs, h_map_snd_gcs1]
  have h_zip_trG' : trG'.ratchet.chains.zip r1.receiverChains = evictGcs gcs1 := by
    dsimp only [trG']
    rw [← h_evict_snd, zip_map_fst_snd]
  have h_len_trG' : trG'.ratchet.chains.length = r1.receiverChains.length := by
    dsimp only [trG']
    rw [← h_evict_snd, List.length_map, List.length_map]
  have h_clamp_r1 : ∀ sc', r1.senderChain = some sc' →
      clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
    intro sc' hsc'
    injection hsc' with hsc'_eq
    subst hsc'_eq
    exact hclamp
  dsimp only [trAt, ratchetAt, signalMessageAt, Frame5, TailFrame, st_f] at hmf ⊢
  rw [← A.pool_transport lim (M.stepEvents evs_all st0) s3 sf hvm5] at hmf
  rw [h_zip_trG',
      show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 160#64 = sp + 0xd8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 172#64 = sp + 0xe4#64 from add_assoc_const _ _ _ _]
  have hmf_pures : sf.mem ⊨
      ⌜∀ sc', r1.senderChain = some sc' →
        clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG'.ratchet.chains.length = r1.receiverChains.length ∧
        trG'.ratchet.senderPad.length = 100 ∧
        r1.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜macLength + 1 ≤ x.msg.serialized.length ∧
        x.msg.serialized.length < 2 ^ 40 ∧
        x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) trG.ratchet.senderPad) ∗
       memRegion sp 0x20 ∗
       memRegion (sp + 0x140#64) 0x170 ∗
       ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗
       memRegion (sp + 0x2d4#64) 0x2ac ∗
       ((vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
         A.pool lim (M.stepEvents evs_all st0) sf ∗
         stackAt sp tryDecryptSubStack ∗
         (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
          ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
          memRegion (sp + 0xe4#64) 4 ∗
          vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
          ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          memRegion x.ret 48 ∗
          ((sp + 0x20#64) ↦₆₄ x.locA) ∗
          ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗
          ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
          boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
          boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
          ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
          optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
          ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
          ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
          ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
          memRegion (x.msgA + 0x71#64) 7 ∗
          envHeap ∗
          tryDecryptSavedRegs s0.sp s0)) ∗ R)) := by
    rw [satisfies_pure_sepConj]
    refine ⟨h_clamp_r1, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨h_len_trG', hpad_len, hmfj⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hmsg_pure, hmf⟩
  refine Satisfies.mono (Entails.of_eq ?_) hmf_pures
  dsimp only [sp, r1, newChain, trG']
  rw [show sessionStateAt (A.atState lim (M.stepEvents evs_all st0) sf) = sessionStateAt A.repAlloc from rfl,
      show protocolAddressAt (A.atState lim (M.stepEvents evs_all st0) sf) = protocolAddressAt A.repAlloc from rfl,
      show vecAt (A.atState lim (M.stepEvents evs_all st0) sf) 104 8
          (chainAt (A.atState lim (M.stepEvents evs_all st0) sf)) =
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) from rfl,
      show vecU8At (A.atState lim (M.stepEvents evs_all st0) sf) = vecU8At A.repAlloc from rfl,
      show boxU8At (A.atState lim (M.stepEvents evs_all st0) sf) = boxU8At A.repAlloc from rfl,
      show optBoxU8At (A.atState lim (M.stepEvents evs_all st0) sf) = optBoxU8At A.repAlloc from rfl]
  sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore
