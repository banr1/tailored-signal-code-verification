/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClStep12PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClStep3PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClStep4PlacedBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Cross-Block Budget-Threaded CLI S3 Commit Seam (`+0x8ac → +0x3e4`)

Composes the `withLsCodeLoaded` step proofs (`DhCommitClStep12PlacedBudget`,
`DhCommitClStep3PlacedBudget`, `DhCommitClStep4PlacedBudget`) with Step 5 to establish
`CliS3CommitSeamPinnedPlaced` parametric in `DhCommitBlockVmWp`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClMainPlacedBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open scoped CryptoVerification.RustHeap
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair PublicKey RatchetState ReceiverChain RootKey SenderChain SessionState
  TripleRatchet macLength
)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  lsmpl withLsCodeLoaded
)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost chainAt chainKeyBytes msgTypeByte optSenderChainBytes ratchetAt
)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost trAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (
  add_assoc_const cell_to_memRegion_8 chainKeyBytes_pointsTo evictList growOneStack newChainGhost
  newReceiverChain optChainKeyHeap optChainKeyTailBytes optSenderChainBytes_some_pointsTo
  setWidth8_zeroExtend64_shared_lb stackAt_split_from
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts (
  evictGcs le_of_eq_succ_lt map_snd_evictGcs map_snd_zip_append sckWord0 sckWord16 sckWord20
  sckWord28 sckWord8 vecAt_chains_eq zip_map_fst_snd
)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser boxU8At optBoxU8At protocolAddressAt sessionStateAt signalMessageAt
)
open CryptoVerification.RustHeap (allocHookStack vecAt vecBuf vecU8At)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget rustCliAllocBudgetSpec
  rustCliAllocNoOomSpec rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (ConsumeMsgKeyStatePlaced)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget (
  CliDhCommitStatePlaced CliS3CommitSeamPinnedPlaced s3CommitDefaultEnv
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudgetAux (
  trGhostCaps_after_commit
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClStep12PlacedBudget (
  dhCommit_step1_2_cl_withStack_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClStep3PlacedBudget (
  dhCommitGrowOne_cl_of_cmkGrowOne_cl dhCommit_step3_cl_pinned_of_wp
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClStep4PlacedBudget (
  dhCommit_step4_cl_of_wp
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpec framelessMemcpyBudgetSpec noAllocShimBudgetSpec publicKeySerializeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (
  DhCommitBlockVmWp dhCommitAllocEvents fitsEvents_of_fitsEnv_dhCommitEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep4 (evictActiveWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep5 (dhCommit_step5_of_wp)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget (
  dhCommitStep12Events dhCommitStep12Pre
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (
  dhCommitStep3Events growOneSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  dhStepNewChainsCap s3AfterCaps trGhostCaps
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)

/-- Pinned-capacity total-correctness CLI S3 Commit (`+0x8ac → +0x3e4`) with `withLsCodeLoaded`
cross-block callees (`hPkSer`, `hToPb`, `hGrowOne`, `hDropChain`). -/
theorem dhCommit_cli_cl_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (hPkSer : subroutine_ok prog (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hToPb : subroutine_ok prog (lsmpl.base 22)
      (withLsCodeLoaded lsmpl (chainKeyToPbSpec M A lim)))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (growOneSpec M A lim)))
    (hDropChain : subroutine_ok prog dropChainEntry
      (withLsCodeLoaded lsmpl (dropChainSpec M A lim)))
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
  let newChain : ReceiverChain :=
    { senderRatchetKey := x.msg.senderRatchetKey, chainKey := some receiverChainKey, messageKeys := [] }
  let r1 : RatchetState := { tr.ratchet with
    senderChain := some ⟨newSenderKey, senderChainKey⟩, rootKey := finalRootKey
    previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
    receiverChains := RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
  let sp := s0.sp - 1504#64
  let envHeap : SepProp :=
    cliTapeAfter ctl x.cur x.rest (min 32 x.rest.length) ∗
    CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff
  rcases hS3 with ⟨hpc_s, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htr, hcro, hvregs⟩,
    hx19, hx20, hx21, hx22, hx23, hx25, hx27, hx28, msgW, hmsgW, hm⟩
  have ⟨hfits12, hfits3a_rc⟩ := fitsEvents_of_fitsEnv_dhCommitEnv hfits
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced,
    trAt, ratchetAt, signalMessageAt] at hm; rw [hsc] at hm
  have h_sc_50_eq : ∀ (pad : List (BitVec 8)), pad.length = 100 →
      ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) pad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
       ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) := by
    intro pad _
    rw [show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
        optSenderChainBytes_some_pointsTo (sp + 0x50#64) sc pad,
        show sp + 0x50#64 + 4#64 = sp + 0x54#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 36#64 = sp + 0x74#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 68#64 = sp + 0x94#64 from add_assoc_const _ _ _ _,
        chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey,
        show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _]
  let TailCommon : SepProp :=
    sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
    ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
    memRegion (sp + 0x38#64 + 172#64) 4 ∗
    vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
    ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗ memRegion x.ret 48 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗
    vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
    boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
    boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
    optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
    ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
    ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ memRegion (x.msgA + 0x71#64) 7 ∗
    envHeap ∗ tryDecryptSavedRegs s0.sp s0
  let CommonCells : SepProp :=
    ((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗
    memRegion (sp + 0x2c0#64) 0x14 ∗ memRegion (sp + 0x2d4#64) 0xfc ∗ memRegion (sp + 0x3f4#64) 12 ∗
    ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x450#64) 0x50 ∗
    memRegion (sp + 0x4a0#64) 0x20 ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗ memRegion (sp + 0x560#64) 0x20
  let SckCells : SepProp :=
    ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗ ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey)
  have hm_pures : s.mem ⊨
      ⌜∀ sc', some sc = some sc' → clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
        trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜macLength + 1 ≤ x.msg.serialized.length ∧ x.msg.serialized.length < 2 ^ 40 ∧
        x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (TailCommon ∗ vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap
         trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
       ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) trG.ratchet.senderPad) ∗
       ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 0) ∗ ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       ((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ memRegion (sp + 0x1d8#64) 0xd8 ∗
       memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x110 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x440#64) 0x80 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
       ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
       stackAt sp tryDecryptSubStack ∗ A.pool lim st s ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm; dsimp only [TailCommon, envHeap, sp]
    rw [show (A.atState lim st s).pool = A.pool lim st s from rfl,
        show sessionStateAt (A.atState lim st s) = sessionStateAt A.repAlloc from rfl,
        show protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc from rfl,
        show vecAt (A.atState lim st s) 104 8 (chainAt (A.atState lim st s)) =
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) from rfl,
        show vecU8At (A.atState lim st s) = vecU8At A.repAlloc from rfl,
        show boxU8At (A.atState lim st s) = boxU8At A.repAlloc from rfl,
        show optBoxU8At (A.atState lim st s) = optBoxU8At A.repAlloc from rfl]; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm_pures; rcases hm_pures with ⟨_, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures; rcases hm_pures with ⟨⟨hchains_len, hpad_len, hmfj⟩, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures; rcases hm_pures with ⟨hmsg_pure, hm_body⟩
  rw [h_sc_50_eq trG.ratchet.senderPad hpad_len,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _] at hm_body
  have hsplit_1d8 := memRegion_split (sp + 0x1d8#64) 0x60 0x78 (by decide)
  rw [show (0x60 + 0x78 : Nat) = 0xd8 from rfl, show sp + 0x1d8#64 + 96#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hsplit_1d8
  have hsplit_2c0 := memRegion_split (sp + 0x2c0#64) 0x14 0xfc (by decide)
  rw [show (0x14 + 0xfc : Nat) = 0x110 from rfl, show sp + 0x2c0#64 + 20#64 = sp + 0x2d4#64 from add_assoc_const _ _ _ _] at hsplit_2c0
  have hsplit_440 := memRegion_split (sp + 0x440#64) 0x10 0x70 (by decide)
  rw [show (0x10 + 0x70 : Nat) = 0x80 from rfl, show sp + 0x440#64 + 16#64 = sp + 0x450#64 from add_assoc_const _ _ _ _] at hsplit_440
  have hsplit_450 := memRegion_split (sp + 0x450#64) 0x50 0x20 (by decide)
  rw [show (0x50 + 0x20 : Nat) = 0x70 from rfl, show sp + 0x450#64 + 80#64 = sp + 0x4a0#64 from add_assoc_const _ _ _ _] at hsplit_450
  have hsplit_4e0 := memRegion_split (sp + 0x4e0#64) 0x20 0x80 (by decide)
  rw [show (0x20 + 0x80 : Nat) = 0xa0 from rfl, show sp + 0x4e0#64 + 32#64 = sp + 0x500#64 from add_assoc_const _ _ _ _] at hsplit_4e0
  have hsplit_500 := memRegion_split (sp + 0x500#64) 0x60 0x20 (by decide)
  rw [show (0x60 + 0x20 : Nat) = 0x80 from rfl, show sp + 0x500#64 + 96#64 = sp + 0x560#64 from add_assoc_const _ _ _ _] at hsplit_500
  have hstk_pb := stackAt_split_from sp tryDecryptSubStack (allocHookStack + 48) (by decide) (by decide)
  have hsplit_sp16 := memRegion_split sp 12 4 (by decide)
  rw [show (12 + 4 : Nat) = 0x10 from rfl, show sp + 12#64 = sp + 0xc#64 from rfl] at hsplit_sp16
  rw [hsplit_1d8, hsplit_2c0, hsplit_440, hsplit_450, hsplit_4e0, hsplit_500, hstk_pb, hsplit_sp16] at hm_body
  let BaseFrame : SepProp :=
    TailCommon ∗ CommonCells ∗ ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗ memRegion (sp + 0x238#64) 0x78
  let gcs0 := trG.ratchet.chains.zip tr.ratchet.receiverChains
  let Frame12 : SepProp :=
    vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
    memRegion (sp + 0xc#64) 4 ∗ memRegion (sp + 0x1d8#64) 0x60 ∗ memRegion (sp + 0x500#64) 0x60 ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - (allocHookStack + 48)) ∗ BaseFrame
  obtain ⟨s1, hsteps12, boxPtr, srkPtr, ckPtr, pad, hsrk0, hpad, hpc1, hrun1, hsp1, hsp_align1,
      htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
      hvregs_1, hL1, hm1⟩ :=
    dhCommit_step1_2_cl_withStack_placed hwp.step12 A lim st allocHookStack (by decide) (by decide)
      hPkSer hShim hAlloc hMemcpy hToPb hfits12 R Frame12 s0 s sp x.msgA sc.chainKey.index
      tr.ratchet.previousCounter finalRootKey senderChainKey receiverChainKey x.msg.senderRatchetKey
      hpc_s hrun hsp hsp_align htr hx22 hx25 hx27 hx28 hcro.1 hL
      (by dsimp only [dhCommitStep12Pre, Frame12, BaseFrame, CommonCells]
          refine Satisfies.mono (Entails.of_eq ?_) hm_body; sep_ac_rfl)
  have hcl1 : LibsignalCodeLoaded lsmpl s1.mem := hcro.1.of_keepsFrozen hsteps12.keepsFrozen
  let st_12 := M.stepEvents dhCommitStep12Events st
  have hstk_grow := stackAt_split_from sp tryDecryptSubStack growOneStack (by decide) (by decide)
  have hsplit_1d8_32 := memRegion_split (sp + 0x1d8#64) 32 0x40 (by decide)
  rw [show (32 + 0x40 : Nat) = 0x60 from rfl, show sp + 0x1d8#64 + 32#64 = sp + 0x1f8#64 from add_assoc_const _ _ _ _] at hsplit_1d8_32
  have hjoin_1b0_72 := (memRegion_split (sp + 0x1b0#64) 40 32 (by decide)).symm
  rw [show (40 + 32 : Nat) = 72 from rfl, show sp + 0x1b0#64 + 40#64 = sp + 0x1d8#64 from add_assoc_const _ _ _ _] at hjoin_1b0_72
  have hm1_sp8 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (cell_to_memRegion_8 sp boxPtr))) hm1
  have hm1_prep : s1.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - (allocHookStack + 48)) ∗
        stackAt sp (allocHookStack + 48)) ∗ (memRegion (sp + 0x1b0#64) 40 ∗ memRegion (sp + 0x1d8#64) 32) ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
      memRegion sp 8 ∗ SckCells ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗
      ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
      ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
      memRegion (sp + 0x1f8#64) 0x40 ∗ memRegion (sp + 0x500#64) 0x60 ∗
      ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
      (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗ A.pool lim st_12 s1 ∗ BaseFrame ∗ R := by
    dsimp only [Frame12, SckCells, st_12] at hm1_sp8 ⊢; rw [hsplit_1d8_32] at hm1_sp8
    refine Satisfies.mono (Entails.of_eq ?_) hm1_sp8; sep_ac_rfl
  rw [← hstk_pb, hstk_grow, hjoin_1b0_72, vecAt_chains_eq] at hm1_prep
  let Frame3 : SepProp :=
    memRegion sp 8 ∗ SckCells ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗
    ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
    memRegion (sp + 0x1f8#64) 0x40 ∗ memRegion (sp + 0x500#64) 0x60 ∗
    ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - growOneStack) ∗ BaseFrame
  have hgcs0_len_eq : gcs0.length = tr.ratchet.receiverChains.length := by
    dsimp only [gcs0]; rw [List.length_zip, hchains_len, Nat.min_self]
  let cap' := dhStepNewChainsCap trG.ratchet.chainsCap tr.ratchet.receiverChains.length
  obtain ⟨s2, hsteps3, ptr', hpc2, hrun2, hsp2, hsp_align2, htr2,
      hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx25_2, hx29_2, hvregs_2, hL2, hm2⟩ :=
    dhCommit_step3_cl_pinned_of_wp hwp.step3 (by decide) (by decide) A lim st_12 hGrowOne hDealloc
      R Frame3 s0 s1 sp trG.ratchet.chainsCap trG.ratchet.chainsPtr boxPtr srkPtr ckPtr gcs0
      x.msg.senderRatchetKey receiverChainKey pad (hgcs0_len_eq ▸ hrc_len) hpad hsrk0
      (hgcs0_len_eq.symm ▸ hfits3a_rc) hpc1 hrun1 hsp1 hsp_align1 htr1 hx25_1 hx26_1 hx27_1 hx28_1 hcl1 hL1
      (by dsimp only [Frame3]; refine Satisfies.mono (Entails.of_eq ?_) hm1_prep; sep_ac_rfl)
  have hcl2 : LibsignalCodeLoaded lsmpl s2.mem := hcl1.of_keepsFrozen hsteps3.keepsFrozen
  let st_123 := M.stepEvents (dhCommitAllocEvents trG.ratchet.chainsCap
    (BitVec.ofNat 64 tr.ratchet.receiverChains.length)) st
  have hcap'_eq : dhStepNewChainsCap trG.ratchet.chainsCap gcs0.length = cap' := by
    dsimp only [cap']; rw [hgcs0_len_eq]
  have hst_123_eq :
      M.stepEvents (dhCommitStep3Events trG.ratchet.chainsCap (BitVec.ofNat 64 gcs0.length)) st_12 = st_123 := by
    dsimp only [st_123, st_12, dhCommitAllocEvents]; rw [hgcs0_len_eq, ← M.stepEvents_append]
  rw [hcap'_eq, hst_123_eq] at hm2
  let gcs1 := gcs0 ++ [(newChainGhost srkPtr ckPtr x.msg.senderRatchetKey, newChain)]
  have hstk_drop := stackAt_split_from sp tryDecryptSubStack dropChainStack (by decide) (by decide)
  have hjoin_1f8 := (memRegion_split (sp + 0x1f8#64) 0x40 0x78 (by decide)).symm
  rw [show (0x40 + 0x78 : Nat) = 0xb8 from rfl, show sp + 0x1f8#64 + 64#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hjoin_1f8
  have hck_94 := (chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey).symm
  rw [show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _] at hck_94
  let TailFrame : SepProp :=
    TailCommon ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
    ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList)
  have hm2_prep : s2.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - growOneStack) ∗ stackAt sp growOneStack) ∗
      (memRegion (sp + 0x1f8#64) 0x40 ∗ memRegion (sp + 0x238#64) 0x78) ∗
      (((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) ∗
      ((sp + 0x38#64) ↦₆₄ cap') ∗ ((sp + 0x40#64) ↦₆₄ ptr') ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs1.length) ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) cap' ptr' gcs1 ∗ memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x500#64) 96 ∗ memRegion sp 8 ∗ A.pool lim st_123 s2 ∗
      SckCells ∗ CommonCells ∗ TailFrame ∗ R := by
    dsimp only [Frame3, BaseFrame, TailFrame, gcs1, newReceiverChain, newChain] at hm2 ⊢
    refine Satisfies.mono (Entails.of_eq ?_) hm2; sep_ac_rfl
  rw [← hstk_grow, hstk_drop, hjoin_1f8, hck_94] at hm2_prep
  let Step5Cells : SepProp :=
    memRegion sp 8 ∗ SckCells ∗ CommonCells ∗ ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
    memRegion (sp + 0x1f8#64) 0xb8
  let Frame4 : SepProp :=
    ((sp + 0x38#64) ↦₆₄ cap') ∗ Step5Cells ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - dropChainStack) ∗ TailFrame
  have hgcs1_len : gcs1.length = tr.ratchet.receiverChains.length + 1 := by
    dsimp only [gcs1, gcs0]; rw [List.length_append, List.length_zip, hchains_len, Nat.min_self]; rfl
  obtain ⟨s3, hsteps4, evs_free, hfree, hpc3, hrun3, hsp3, hsp_align3, htr3,
      hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx29_3, hvregs_3, hL3, hm3⟩ :=
    dhCommit_step4_cl_of_wp A lim st_123 hwp.step45.step4a_lo hwp.step45.step4a_ge
      hwp.step45.step4b_pre_memmove hwp.step45.step4b_post_memmove
      hwp.step45.step4c_hi hwp.step45.step4c_le hMemmove hDropChain R Frame4 s0 s2 sp cap' ptr'
      gcs1 (le_of_eq_succ_lt hgcs1_len hrc_len) hpc2 hrun2 hsp2 hsp_align2 htr2
      (hx23_2.trans (hx23_1.trans hx23)) hx25_2 hcl2 hL2
      (by dsimp only [evictActiveWithStack, Frame4, Step5Cells]
          refine Satisfies.mono (Entails.of_eq ?_) hm2_prep; sep_ac_rfl)
  let evs_all := dhCommitAllocEvents trG.ratchet.chainsCap
    (BitVec.ofNat 64 tr.ratchet.receiverChains.length) ++ evs_free
  let st_f := M.stepEvents evs_all st
  have hst_f_eq : M.stepEvents evs_free st_123 = st_f := by
    dsimp only [st_f, evs_all, st_123]; exact (M.stepEvents_append _ _ _).symm
  rw [hst_f_eq] at hm3
  let Frame5 : SepProp :=
    vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
    A.pool lim st_f s3 ∗ stackAt sp tryDecryptSubStack ∗ TailFrame
  obtain ⟨sf, hsteps5, hvm5, hpcf, hrunf, hspf, hsp_alignf, htrf,
      hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx29f, _hx30f, hvregsf, _hLf, hmf⟩ :=
    dhCommit_step5_of_wp trG.ratchet.senderPad sc receiverChainKey newSenderKey senderChainKey
      msgW Frame5 R s3 sp hwp.step45.step5 hpc3 hrun3 hsp3 hsp_align3 hx25_3 hL3
      (by dsimp only [evictActiveWithStack, Frame4, Step5Cells, SckCells, CommonCells, Frame5, evictGcs] at hm3 ⊢
          rw [vecAt_chains_eq, hstk_drop]; refine Satisfies.mono (Entails.of_eq ?_) hm3; sep_ac_rfl)
  let trG' : TrGhost := { trG with ratchet := { trG.ratchet with
    chainsCap := cap', chainsPtr := ptr', chains := (evictGcs gcs1).map Prod.fst } }
  have hsteps_all : Steps prog s sf := ((hsteps12.trans hsteps3).trans hsteps4).trans hsteps5
  refine ⟨sf, evs_all, trG', hsteps_all, Or.inr ⟨_, _, rfl, rfl, hfree⟩,
    trGhostCaps_after_commit trG tr.ratchet.receiverChains ptr' srkPtr ckPtr
      x.msg.senderRatchetKey newChain hchains_len,
    hpcf, ⟨hrunf, hspf, hsp0_align, hsp_alignf,
      hx29f.trans (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))), htrf.trans htr3,
      hcro.of_keepsFrozen hsteps_all.keepsFrozen,
      hvregsf.trans (hvregs_3.trans (hvregs_2.trans (hvregs_1.trans hvregs)))⟩,
    hx12f, hx19f.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19))),
    hx20f.trans (hx20_3.trans (hx20_2.trans (hx20_1.trans hx20))),
    hx21f.trans (hx21_3.trans (hx21_2.trans (hx21_1.trans hx21))),
    hx22f.trans (hx22_3.trans (hx22_2.trans hx22_1)), hx23f.trans hx23_3,
    by rw [hx24f, setWidth8_zeroExtend64_shared_lb, hmsgW], hx25f, ?_⟩
  have h_evict_snd : (evictGcs gcs1).map Prod.snd = r1.receiverChains := by
    rw [map_snd_evictGcs, map_snd_zip_append trG.ratchet.chains tr.ratchet.receiverChains
      (newChainGhost srkPtr ckPtr x.msg.senderRatchetKey) newChain hchains_len]
  have h_zip_trG' : trG'.ratchet.chains.zip r1.receiverChains = evictGcs gcs1 := by
    dsimp only [trG']; rw [← h_evict_snd, zip_map_fst_snd]
  have h_len_trG' : trG'.ratchet.chains.length = r1.receiverChains.length := by
    dsimp only [trG']; rw [← h_evict_snd, List.length_map, List.length_map]
  have h_clamp_r1 : ∀ sc', r1.senderChain = some sc' →
      clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
    intro sc' hsc'; injection hsc' with hsc'_eq; subst hsc'_eq; exact hclamp
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced,
    trAt, ratchetAt, signalMessageAt, Frame5, TailFrame, TailCommon, envHeap, st_f] at hmf ⊢
  rw [← A.pool_transport lim (M.stepEvents evs_all st) s3 sf hvm5] at hmf
  rw [h_zip_trG',
      show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _]
  have hmf_pures : sf.mem ⊨
      ⌜∀ sc', r1.senderChain = some sc' → clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG'.ratchet.chains.length = r1.receiverChains.length ∧ trG'.ratchet.senderPad.length = 100 ∧
        r1.maxForwardJumps < 2 ^ 64⌝ ∗ ⌜macLength + 1 ≤ x.msg.serialized.length ∧
        x.msg.serialized.length < 2 ^ 40 ∧ x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) trG.ratchet.senderPad) ∗
       memRegion sp 0x20 ∗ memRegion (sp + 0x140#64) 0x170 ∗
       ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗ memRegion (sp + 0x2d4#64) 0x2ac ∗
       ((vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
         A.pool lim (M.stepEvents evs_all st) sf ∗ stackAt sp tryDecryptSubStack ∗
         (((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
          ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗ TailCommon)) ∗ R)) := by
    dsimp only [TailCommon, envHeap]; rw [satisfies_pure_sepConj]; refine ⟨h_clamp_r1, ?_⟩
    rw [satisfies_pure_sepConj]; refine ⟨⟨h_len_trG', hpad_len, hmfj⟩, ?_⟩
    rw [satisfies_pure_sepConj]; exact ⟨hmsg_pure, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf⟩
  dsimp only [TailCommon, envHeap, sp, r1, newChain, trG'] at hmf_pures ⊢
  refine Satisfies.mono (Entails.of_eq ?_) hmf_pures
  rw [show (A.atState lim (M.stepEvents evs_all st) sf).pool = A.pool lim (M.stepEvents evs_all st) sf from rfl,
      show sessionStateAt (A.atState lim (M.stepEvents evs_all st) sf) = sessionStateAt A.repAlloc from rfl,
      show protocolAddressAt (A.atState lim (M.stepEvents evs_all st) sf) = protocolAddressAt A.repAlloc from rfl,
      show vecAt (A.atState lim (M.stepEvents evs_all st) sf) 104 8
          (chainAt (A.atState lim (M.stepEvents evs_all st) sf)) =
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) from rfl,
      show vecU8At (A.atState lim (M.stepEvents evs_all st) sf) = vecU8At A.repAlloc from rfl,
      show boxU8At (A.atState lim (M.stepEvents evs_all st) sf) = boxU8At A.repAlloc from rfl,
      show optBoxU8At (A.atState lim (M.stepEvents evs_all st) sf) = optBoxU8At A.repAlloc from rfl]
  sep_ac_rfl

theorem s3_commit_pinned_cl_budget_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry) (C : Crypto) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (withLsCodeLoaded lsmpl (chainKeyToPbSpec M A lim)))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (withLsCodeLoaded lsmpl (growOneSpec M A lim)))
    (hDropChain : subroutine_ok prog dropChainEntry (withLsCodeLoaded lsmpl (dropChainSpec M A lim)))
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
    CliS3CommitSeamPinnedPlaced prog entry C A lim ctl parse S s3CommitDefaultEnv := by
  apply CliS3CommitSeamPinnedPlaced.ofTight
  intro x st trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
    R s0 s hsc hrc_len hclamp hfits hS3 hL
  obtain ⟨s', evs, trG', hsteps, henv, hcaps, hpost⟩ :=
    dhCommit_cli_cl_pinned_placed_ok hwp A lim st ctl hPkSer hToPb hGrowOne hDropChain
      hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove
      x trG tr st1 sc receiverChainKey newSenderKey finalRootKey senderChainKey
      R s0 s hsc hrc_len hclamp hfits hS3 hL
  exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hcaps, hpost⟩⟩

/-- Specialization of `s3_commit_pinned_cl_budget_placed_ok_cli` accepting
`ConsumeMessageKey.DefsBudget.growOneSpec` directly. -/
theorem s3_commit_pinned_cmk_cl_budget_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry) (C : Crypto) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (withLsCodeLoaded lsmpl (chainKeyToPbSpec M A lim)))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.growOneSpec M A lim)))
    (hDropChain : subroutine_ok prog dropChainEntry (withLsCodeLoaded lsmpl (dropChainSpec M A lim)))
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
    CliS3CommitSeamPinnedPlaced prog entry C A lim ctl parse S s3CommitDefaultEnv :=
  s3_commit_pinned_cl_budget_placed_ok_cli hwp C A lim ctl parse S
    hPkSer hToPb (dhCommitGrowOne_cl_of_cmkGrowOne_cl hGrowOne) hDropChain
    hShim hAlloc hDealloc hMemcpy hMemmove

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClMainPlacedBudget
