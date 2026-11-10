/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433Placed
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import ProofLib.RegChain

/-!
# Budget-Threaded Relocatable Segment S3 (`DhStep`) on Block `433`

Proves pinned and unpinned budget-threaded S3 (`DhStep`) seam contracts (`S3TightSeamPinnedPlaced`,
`S3TightSeamPlaced`, `CliS3Seam*`, and `Stage2ContractsX` variants) under `RustCliAllocBudget M`
for `try_decrypt_with_state::<Coins>` (block `433`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux (
  CliDhStepAfterRecvChainStatePlaced add_lscro_pre coinsFillAtBudgetPlaced_of_after0_cl
  coinsFillAtBudgetPlaced_of_after0_cro coinsFillAtBudgetSpecPlaced coinsFillBudgetSpecPlaced
  dhStep_after_cc1_to_cc2_call_vm_placed_cli dhStep_missing_sender_chain_vm_placed_cli
  dhStep_recv_create_chain_withStack_cro_placed_cli
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ConsumeMsgKeyStatePlaced DhStepStatePlaced ErrTailStatePlaced S3TightSeamPinnedPlaced
  S3TightSeamPlaced
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget (
  CliDhCommitStatePlaced CliS3CommitSeamPinnedPlaced CliS3CommitSeamPinnedXPlaced
  CliS3CommitSeamPlaced DhCommitEnv dhCommitAllocEvents s3CommitDefaultEnv
  s3_commit_433_pinned_placed_ok s3_commit_433_pinned_x_budget_placed_ok
)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair Mut RatchetState ReceiverChain RootKey SenderChain SessionState
  TripleRatchet rootCreateChain
)
open CryptoGames.Ratchet (clampScalar createChain)
open CryptoVerification (
  LibsignalPlacement lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl
  withLsCodeLoaded
)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes)
open CryptoVerification.LibsignalTripleRatchet (
  CreateChainGhost SpqrModel TrGhost TryDecryptGhost createChainResultAt createChainStack
  createChainStackX rootStack subroutine_ok_withLsCodeRoLoaded_of_plain
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded trAt withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkPl_434 speBodyAt tryDecryptMidMetaPlaced tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (
  clampScalar_keyPair_generate decryptDraws_of_cc1_err decryptDraws_of_cc1_ok
  decryptDraws_of_senderChain_none dhRatchetStep_none dhRatchetStep_some_err1
  dhRatchetStep_some_err2 dhRatchetStep_some_ok fold_1d8_after_cc2_err fold_after_cc2_ok
  fold_sp_20_after_cc2_err rk_ne_zero signalMessageAt_senderRatchetKey signalMessageRestAt
  stackAt_subStack_createChain
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd (spqrNoPanic)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack dropChainStackX)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser coinsOf decryptDraws protocolAddressAt sessionStateAt utf8 uuidTryParse
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (growOneChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpec chainKeyToPbSpecX derivePublicKeyBytesBudgetSpec framelessMemcpyBudgetSpec
  noAllocShimBudgetSpec publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  tryDecryptFnOnPanic tryDecryptOnPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (growOneSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux (
  dhStep_cc2_err_branch_vm_placed dhStep_cc2_ok_branch_vm_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (
  dhStepPairEvents fitsEnv_cc1_of_s3EnvOf onPanicTightBudget_of_spqrNoPanic s3DefaultEnv
  s3EnvOf stackAt_subStack_createChainX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps (
  lsStaticDropSym zeroizeSecretBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (
  DhStepBlockVmWp dhStepBlockVmWp_549
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (
  tryDecryptOnPanicTight tryDecryptOnPanicTight_weaken
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (s3AfterCaps trGhostCaps)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec dropChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (
  createChainSpec createChainSpecWithStack createChainSpecX
)

export LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux (
  CliDhStepAfterRecvChainStatePlaced
  coinsFillAtBudgetPlaced_of_after0_cl
  coinsFillAtBudgetPlaced_of_after0_cro
  coinsFillAtBudgetSpecPlaced
  coinsFillBudgetSpecPlaced
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
  (dhStepPairEvents s3DefaultEnv s3EnvOf)
export LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget
  (DhCommitEnv dhCommitAllocEvents s3CommitDefaultEnv)
export LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
  (S3TightSeamPinnedPlaced S3TightSeamPlaced)

/-! ## Keygen and Sending `create_chain` Stepper -/

theorem dhStep_keygen_and_send_create_chain_withStack_cro_placed_cli [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {ctl : BitVec 64}
    (ccStack : Nat)
    (hstack_split : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        (stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
         stackAt sp ccStack))
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hcc : subroutine_ok prog (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecWithStack M A lim C ccStack)))
    (hdpk : subroutine_ok prog (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey)
    (R : SepProp) (s0 s : State)
    (hrng : subroutine_ok prog rngFillEntry
      (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack x.cur x.rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hrk2_ne : s0.sp - 1504#64 + 0x4a0#64 ≠ 0#64)
    (hfits2 : FitsEnv M lim st
      (· = dhStepPairEvents C x.msg.senderRatchetKey
        (KeyPair.generate C (coinsOf x.rest)).privateKey))
    (hafter : CliDhStepAfterRecvChainStatePlaced entry A lim st ctl x trG tr st1 rk1 rck R s0 s)
    (hcode : prog.CodeLoaded s.mem) :
    let newSenderKey := KeyPair.generate C (coinsOf x.rest)
    let evs2 := dhStepPairEvents C x.msg.senderRatchetKey newSenderKey.privateKey
    match rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
    | .ok (finalRootKey, senderChainKey) =>
      ∃ s', Steps prog s s' ∧
        CliDhCommitStatePlaced entry A lim (M.stepEvents evs2 st) ctl
          x trG tr st1 rck newSenderKey finalRootKey senderChainKey R s0 s'
    | .error e =>
      ∃ s' trG' r1, Steps prog s s' ∧
        ErrTailStatePlaced entry A lim (M.stepEvents evs2 st) ctl
          x trG' { tr with ratchet := r1 } st1 e (min 32 x.rest.length) R s0 s' := by
  set sp := s0.sp - 1504#64
  set draws := min 32 x.rest.length
  set newSenderKey := KeyPair.generate C (coinsOf x.rest)
  obtain ⟨s5, hsteps5, hvm5, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, hx19_5, hx20_5, hx21_5,
    hx22_5, hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, hx30_5, msgW, hmsgW, hmem5⟩ :=
    dhStep_after_cc1_to_cc2_call_vm_placed_cli hwp hdpk x trG tr st1 rk1 rck R s0 s
      hrng hsd hafter hcode
  obtain ⟨hrun5, hsp5, hsp0_al, hsp_al5, hx29_5, htrace5, hcl5, hvregs5⟩ := hmeta5
  rw [A.atState_eq_of_vmPreserved lim st hvm5.symm] at hmem5
  let ccG2 : CreateChainGhost :=
    { rkA := sp + 0x4a0#64
      rk := rk1
      theirA := x.msgA + 56#64
      their := x.msg.senderRatchetKey
      ourA := sp + 0x420#64
      our := newSenderKey.privateKey
      ret := sp + 0x190#64 }
  let Frame2 : SepProp :=
    sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
    trAt A.repAlloc (sp + 0x38#64) trG
      { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
    ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1d8#64) 0x1f8 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
    memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    memRegion (sp + 0x440#64) 0x60 ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
    protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
    signalMessageRestAt A.repAlloc x.msgG x.msgA x.msg ∗
    cliTapeAfter ctl x.cur x.rest draws ∗ lsLogOff ∗
    stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
    tryDecryptSavedRegs s0.sp s0
  have hpre_cc2 :
      s5.mem ⊨ (withLsCodeRoLoaded lsmpl (createChainSpecWithStack M A lim C ccStack)).pre
        (ccG2, st) s5 ∗ (Frame2 ∗ R) := by
    refine add_lscro_pre hcl5 ?_
    dsimp only [createChainSpecWithStack, ccG2, Frame2]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_5, hx1_5, hx2_5, hx8_5, hrk2_ne, hfits2⟩, ?_⟩
    rw [show s5.sp = sp from hsp5]
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced at hmem5
    rw [signalMessageAt_senderRatchetKey (A.atState lim st s5) x.msgG x.msgA x.msg,
        show sessionStateAt (A.atState lim st s5) = sessionStateAt A.repAlloc from rfl,
        show trAt (A.atState lim st s5) = trAt A.repAlloc from rfl,
        show protocolAddressAt (A.atState lim st s5) = protocolAddressAt A.repAlloc from rfl,
        show signalMessageRestAt (A.atState lim st s5) = signalMessageRestAt A.repAlloc from rfl,
        show (A.atState lim st s5).pool = A.pool lim st s5 from rfl,
        show s0.sp - 1504#64 = sp from rfl, hstack_split sp] at hmem5
    exact Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [sp, draws, newSenderKey]; sep_ac_rfl)) hmem5
  obtain ⟨sm, hsteps_cc2, hout_cc2, _⟩ :=
    hcc.no_fault_before_outcome (ccG2, st) (Frame2 ∗ R) s5 hpc5 hrun5 hpre_cc2 hsp_al5
      (hsteps5.codeLoaded hcode)
  have hsteps5m : Steps prog s sm := Steps.trans hsteps5 hsteps_cc2
  rcases hout_cc2 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, -, hpost⟩ | ⟨_, hpost⟩
  · have hpcm : sm.pc = entry + 2008#64 := hret_m.1.trans hx30_5
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [createChainSpecWithStack, ccG2] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨evs, ⟨htrace_m0, henv_m⟩, hpost⟩
    have hevs_eq : evs = dhStepPairEvents C x.msg.senderRatchetKey newSenderKey.privateKey := henv_m
    subst hevs_eq
    set st' := M.stepEvents (dhStepPairEvents C x.msg.senderRatchetKey newSenderKey.privateKey) st
    have hcl_m := hcl5.of_keepsFrozen hsteps_cc2.keepsFrozen
    have hsp_al_m : sm.spAligned = true := by
      unfold State.spAligned at hsp_al5 ⊢; rw [hspm]; exact hsp_al5
    have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
      ⟨hrunm, by reg_chain, hsp0_al, hsp_al_m, by reg_chain, by reg_chain, hcl_m, by reg_chain⟩
    have hpost_grouped : sm.mem ⊨
        createChainResultAt (sp + 0x190#64)
          (rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey) ∗
        sessionStateAt (A.atState lim st' sm) x.ss x.G.afterTrFrom st1 ∗
        trAt (A.atState lim st' sm) (sp + 0x38#64) trG
          { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0x1f8 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
        memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
        ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
        memRegion (sp + 0x440#64) 0x60 ∗ ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
        ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' sm) ctl x draws s0 ∗ R := by
      dsimp only [Frame2] at hpost
      rw [show s5.sp = sp from hsp5] at hpost
      unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
      rw [signalMessageAt_senderRatchetKey (A.atState lim st' sm) x.msgG x.msgA x.msg,
          show sessionStateAt (A.atState lim st' sm) = sessionStateAt A.repAlloc from rfl,
          show trAt (A.atState lim st' sm) = trAt A.repAlloc from rfl,
          show protocolAddressAt (A.atState lim st' sm) = protocolAddressAt A.repAlloc from rfl,
          show signalMessageRestAt (A.atState lim st' sm) = signalMessageRestAt A.repAlloc from rfl,
          show (A.atState lim st' sm).pool = A.pool lim st' sm from rfl,
          show s0.sp - 1504#64 = sp from rfl, hstack_split sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hpost
    dsimp only
    unfold rootCreateChain at hpost_grouped ⊢
    cases hcc2 : createChain C.F C.X rk1 x.msg.senderRatchetKey.bytes
        newSenderKey.privateKey.bytes with
    | none =>
      rw [hcc2] at hpost_grouped
      dsimp only at hpost_grouped ⊢
      have hpost_err0 : sm.mem ⊨
          (memRegion (sp + 0x1d8#64) 0x1f8 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
           memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
           ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
           memRegion (sp + 0x440#64) 0x60 ∗ ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
           ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
           ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0) ∗
          (((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x140#64) 0x50 ∗
           createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
           sessionStateAt (A.atState lim st' sm) x.ss x.G.afterTrFrom st1 ∗
           trAt (A.atState lim st' sm) (sp + 0x38#64) trG
             { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
           ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
           ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
           CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' sm) ctl x draws s0 ∗ R) :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hpost_grouped
      have hpost_err1 := Satisfies.mono (sepConj_mono_left
        (fold_1d8_after_cc2_err sp rck newSenderKey.publicKey.bytes.toList
          newSenderKey.privateKey.bytes.toList rk1
          newSenderKey.publicKey.bytes.2 newSenderKey.privateKey.bytes.2)) hpost_err0
      let Rest_err : SepProp :=
        sessionStateAt (A.atState lim st' sm) x.ss x.G.afterTrFrom st1 ∗
        trAt (A.atState lim st' sm) (sp + 0x38#64) trG
          { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' sm) ctl x draws s0 ∗ R
      have hmem_err : sm.mem ⊨
          ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x140#64) 0x50 ∗
          createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
          memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err]; sep_ac_rfl)) hpost_err1
      obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
        dhStep_cc2_err_branch_vm_placed (A := A.atState lim st' sm) hwp msgW Rest_err s0 sm
          hpcm hmeta_m (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
          hmem_err (hsteps5m.codeLoaded hcode)
      refine ⟨s', trG, { tr.ratchet with rootKey := (0 : RootKey) },
        Steps.trans hsteps5m hsteps2, ?_⟩
      refine ⟨hpcs', hmetas', by reg_chain, hx20s', hx26s', ?_⟩
      dsimp only [Rest_err] at hmems'
      rw [A.atState_eq_of_vmPreserved lim st' hvm2.symm] at hmems'
      have hmems0 : s'.mem ⊨
          (memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
           memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW)) ∗
          (((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
           sessionStateAt (A.atState lim st' s') x.ss x.G.afterTrFrom st1 ∗
           trAt (A.atState lim st' s') (sp + 0x38#64) trG
             { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗ memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt (A.atState lim st' s') (utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗
           CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' s') ctl x draws s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; sep_ac_rfl)) hmems'
      have hmems0' := Satisfies.mono (sepConj_mono_left (fold_sp_20_after_cc2_err sp rck msgW)) hmems0
      have hsp38_ent :
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ⊢ memRegion sp 0x38 := by
        rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k := 0x18) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k := 0x10) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k := 0xc) rfl (by bv_arith) (by decide),
            memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k := 0x8) rfl (by bv_arith) (by decide)]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo32_entails_memRegion _ _)
            (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))
      have hmems1 : s'.mem ⊨
          (memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA)) ∗
          (sessionStateAt (A.atState lim st' s') x.ss x.G.afterTrFrom st1 ∗
           trAt (A.atState lim st' s') (sp + 0x38#64) trG
             { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗ memRegion (sp + 0x140#64) 0x28 ∗
           speBodyAt (A.atState lim st' s') (utf8 "decrypt") (sp + 0x168#64) .invalidKeyAgreement ∗
           memRegion (sp + 0x190#64) 0x3f0 ∗
           CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' s') ctl x draws s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by sep_ac_rfl)) hmems0'
      have hmems2 := Satisfies.mono (sepConj_mono_left hsp38_ent) hmems1
      dsimp only [sp, draws] at hmems2 ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by sep_ac_rfl)) hmems2
    | some p2 =>
      rcases p2 with ⟨finalRootKey, sckKey⟩
      rw [hcc2] at hpost_grouped
      dsimp only at hpost_grouped ⊢
      have hpost_ok0 : sm.mem ⊨
          (memRegion (sp + 0x1d8#64) 0x1f8 ∗ memRegion (sp + 0x440#64) 0x60 ∗
           ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1)) ∗
          (createChainResultAt (sp + 0x190#64) (.ok (finalRootKey, ⟨sckKey, 0⟩)) ∗
           sessionStateAt (A.atState lim st' sm) x.ss x.G.afterTrFrom st1 ∗
           trAt (A.atState lim st' sm) (sp + 0x38#64) trG
             { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
           memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
           ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
           ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
           ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
           ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
           ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗
           ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
           ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
           ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
           ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
           CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' sm) ctl x draws s0 ∗ R) :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hpost_grouped
      have hpost_ok1 := Satisfies.mono (sepConj_mono_left (fold_after_cc2_ok sp rk1)) hpost_ok0
      let Rest_ok : SepProp :=
        sessionStateAt (A.atState lim st' sm) x.ss x.G.afterTrFrom st1 ∗
        trAt (A.atState lim st' sm) (sp + 0x38#64) trG
          { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
        ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
        ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0xd8 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗
        memRegion (sp + 0x2c0#64) 0x110 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗
        memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
        ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
        memRegion (sp + 0x440#64) 0x80 ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
        ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' sm) ctl x draws s0 ∗ R
      have hmem_ok : sm.mem ⊨
          createChainResultAt (sp + 0x190#64) (.ok (finalRootKey, ⟨sckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok]; sep_ac_rfl)) hpost_ok1
      obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hcss', hmems'⟩ :=
        dhStep_cc2_ok_branch_vm_placed hwp finalRootKey ⟨sckKey, 0⟩ Rest_ok s0 sm
          hpcm hmeta_m (by reg_chain) hmem_ok (hsteps5m.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps5m hsteps2, ?_⟩
      refine ⟨hpcs', hmetas', by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, msgW, hmsgW, ?_⟩
      dsimp only [Rest_ok, sp, draws, newSenderKey] at hmems' ⊢
      rw [A.atState_eq_of_vmPreserved lim st' hvm2.symm] at hmems'
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by sep_ac_rfl)) hmems'
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-! ## S3 Seams, Master Composition, and Block `433` Specializations -/

/-- Pinned loose CLI `S3` (`DhStep`) seam recording `trGhostCaps` on `.ok ck`. -/
def CliS3SeamPinnedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) :
    Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    FitsEnv M lim st (s3Env x trG tr) →
    DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    ∃ s', Steps prog s s' ∧
      ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | (.ok ck, r1) =>
          ∃ evs trG', s3Env x trG tr evs ∧
            trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
        | (.error e, _) =>
          ∃ evs trG' r1, s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R))

/-- Unpinned loose CLI `S3` (`DhStep`) seam. -/
def CliS3SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) :
    Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    FitsEnv M lim st (s3Env x trG tr) →
    DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    ∃ s', Steps prog s s' ∧
      ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | (.ok ck, r1) =>
          ∃ evs trG', s3Env x trG tr evs ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
        | (.error e, _) =>
          ∃ evs trG' r1, s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R))

/-- Pinned `Stage2ContractsX` (`X`) CLI `S3` (`DhStep`) seam. -/
def CliS3SeamPinnedXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) :
    Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    FitsEnv M lim st (s3Env x trG tr) →
    DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    ∃ s', Steps prog s s' ∧
      ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | (.ok ck, r1) =>
          ∃ evs trG', s3Env x trG tr evs ∧
            trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
        | (.error e, _) =>
          ∃ evs trG' r1, s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R))

/-- Unpinned `Stage2ContractsX` (`X`) CLI `S3` (`DhStep`) seam. -/
def CliS3SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) :
    Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    FitsEnv M lim st (s3Env x trG tr) →
    DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    ∃ s', Steps prog s s' ∧
      ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | (.ok ck, r1) =>
          ∃ evs trG', s3Env x trG tr evs ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
        | (.error e, _) =>
          ∃ evs trG' r1, s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R))

theorem CliS3SeamPinnedPlaced.ofTight [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (h : S3TightSeamPinnedPlaced prog entry C A lim ctl parse S s3Env) :
    CliS3SeamPinnedPlaced prog entry C A lim ctl parse S s3Env := by
  intro x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  obtain ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩ :=
    h x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  · exact ⟨s', hsteps, Or.inl hok⟩
  · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩⟩

theorem CliS3SeamPinnedPlaced.toUnpinned [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (h : CliS3SeamPinnedPlaced prog entry C A lim ctl parse S s3Env) :
    CliS3SeamPlaced prog entry C A lim ctl parse S s3Env := by
  intro x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  obtain ⟨s', hsteps, hok | hpan⟩ :=
    h x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  · refine ⟨s', hsteps, Or.inl ?_⟩
    revert hok
    rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
        tr.ratchet with ⟨_ | ck, r1⟩
    · exact id
    · rintro ⟨evs, trG', hevs, _, hcmk⟩
      exact ⟨evs, trG', hevs, hcmk⟩
  · exact ⟨s', hsteps, Or.inr hpan⟩

theorem CliS3SeamPlaced.ofTight [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (h : S3TightSeamPlaced prog entry C A lim ctl parse S s3Env) :
    CliS3SeamPlaced prog entry C A lim ctl parse S s3Env := by
  intro x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  obtain ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩ :=
    h x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  · exact ⟨s', hsteps, Or.inl hok⟩
  · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩⟩

theorem CliS3SeamPinnedXPlaced.toUnpinned [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (h : CliS3SeamPinnedXPlaced prog entry C decFn A lim ctl parse S s3Env) :
    CliS3SeamXPlaced prog entry C decFn A lim ctl parse S s3Env := by
  intro x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  obtain ⟨s', hsteps, hok | hpan⟩ :=
    h x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  · refine ⟨s', hsteps, Or.inl ?_⟩
    revert hok
    rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
        tr.ratchet with ⟨_ | ck, r1⟩
    · exact id
    · rintro ⟨evs, trG', hevs, _, hcmk⟩
      exact ⟨evs, trG', hevs, hcmk⟩
  · exact ⟨s', hsteps, Or.inr hpan⟩

/-- Stack- and panic-parametric CLI `S3` (`DhStep`) composition with `trGhostCaps` pinning. -/
theorem dhStep_cli_withStack_cro_pinned_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (ccStack : Nat)
    (hstack_split : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        (stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
         stackAt sp ccStack))
    (P_panic : TryDecryptGhost → State → State → SepProp)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecWithStack M A lim C ccStack)))
    (hdpk : subroutine_ok prog (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry
        (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit :
      ∀ (x : TryDecryptGhost) (st_c : M.σ) (trG : TrGhost)
        (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
        (sc : SenderChain) (rck : ChainKey) (newSenderKey : KeyPair)
        (finalRootKey : RootKey) (senderChainKey : ChainKey) (R : SepProp) (s0 s_c : State),
        tr.ratchet.senderChain = some sc →
        tr.ratchet.receiverChains.length < 2 ^ 32 →
        clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
        FitsEnv M lim st_c (s3CommitEnv x trG tr) →
        CliDhCommitStatePlaced entry A lim st_c ctl x trG tr st1
          rck newSenderKey finalRootKey senderChainKey R s0 s_c →
        prog.CodeLoaded s_c.mem →
        let newChain : ReceiverChain :=
          { senderRatchetKey := x.msg.senderRatchetKey
            chainKey := some rck
            messageKeys := [] }
        let r1 : RatchetState :=
          { tr.ratchet with
            senderChain := some ⟨newSenderKey, senderChainKey⟩
            rootKey := finalRootKey
            previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
            receiverChains :=
              RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
        ∃ s', Steps prog s_c s' ∧
          ((∃ evs trG', s3CommitEnv x trG tr evs ∧
              trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
              ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st_c) ctl
                x trG' { tr with ratchet := r1 } st1 rck (min 32 x.rest.length) R s0 s') ∨
           (s'.status = .Panicked ∧ s'.mem ⊨ P_panic x s0 s' ∗ R)))
    (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hfrom : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (hfind : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hsp0 : rootStack ≤ s0.sp.toNat)
    (hx_rest : x.rest.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (s3EnvOf C s3CommitEnv x trG tr))
    (hs3 : DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s)
    (hcode : prog.CodeLoaded s.mem) :
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    ∃ s', Steps prog s s' ∧
      ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | (.ok ck, r1) =>
          ∃ evs trG', s3EnvOf C s3CommitEnv x trG tr evs ∧
            trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
        | (.error e, _) =>
          ∃ evs trG' r1, s3EnvOf C s3CommitEnv x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧ s'.mem ⊨ P_panic x s0 s' ∗ R)) := by
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, hvm, herr⟩ :=
      dhStep_missing_sender_chain_vm_placed_cli (A := A.atState lim st s) hwp
        x trG tr st1 R s0 s hsc hs3 hcode
    have herr' : ErrTailStatePlaced entry A lim (M.stepEvents [] st) ctl
        x trG tr st1 (.invalidSessionStructure .missingSenderChain) 0 R s0 s' := by
      rw [M.stepEvents_nil st]
      simpa only [ErrTailStatePlaced, A.atState_eq_of_vmPreserved lim st hvm] using herr
    have henv : s3EnvOf C s3CommitEnv x trG tr [] := by unfold s3EnvOf; rw [hsc]
    exact ⟨s', hsteps, Or.inl ⟨[], trG, tr.ratchet, henv, herr'⟩⟩
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hfits1 := fitsEnv_cc1_of_s3EnvOf hsc hfits
    have hstep1 := dhStep_recv_create_chain_withStack_cro_placed_cli A lim st ccStack
      hstack_split hwp hcc x trG tr st1 sc R s0 s hsc hrk1_ne hfits1 hs3 hcode
    dsimp only at hstep1
    set evs1 := dhStepPairEvents C x.msg.senderRatchetKey sc.ratchetKey.privateKey
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at hstep1
      rw [dhRatchetStep_some_err1 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc e hsc hcc1,
          decryptDraws_of_cc1_err C x.st st1 tr x.msg.senderRatchetKey x.rest sc e hfrom hfind hsc hcc1]
      obtain ⟨s1, trG', r1', hsteps1, herr1⟩ := hstep1
      have henv : s3EnvOf C s3CommitEnv x trG tr evs1 := by
        unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1]
      exact ⟨s1, hsteps1, Or.inl ⟨evs1, trG', r1', henv, herr1⟩⟩
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      rw [hcc1] at hstep1
      rw [decryptDraws_of_cc1_ok C x.st st1 tr x.msg.senderRatchetKey x.rest sc rk1 rck hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, hafter⟩ := hstep1
      set newSenderKey := KeyPair.generate C (coinsOf x.rest)
      set evs2 := dhStepPairEvents C x.msg.senderRatchetKey newSenderKey.privateKey
      have hfits_after1 : FitsEnv M lim (M.stepEvents evs1 st)
          (match rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
           | .error _ => (· = evs2)
           | .ok _ => SeqEnv (· = evs2) (s3CommitEnv x trG tr)) := by
        unfold s3EnvOf at hfits; rw [hsc] at hfits; dsimp only at hfits; rw [hcc1] at hfits; dsimp only at hfits
        cases hcc2' : rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey <;>
          (rw [hcc2'] at hfits; exact hfits.seq_right rfl)
      have hfits2 : FitsEnv M lim (M.stepEvents evs1 st) (· = evs2) := by
        cases hcc2' : rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey <;>
          rw [hcc2'] at hfits_after1
        · exact hfits_after1
        · exact hfits_after1.seq_left
      have hstep2 := dhStep_keygen_and_send_create_chain_withStack_cro_placed_cli
        A lim (M.stepEvents evs1 st) ccStack hstack_split hwp hcc hdpk
        x trG tr st1 rk1 rck R s0 s1 (hrng x.cur x.rest hx_rest) hsd hrk2_ne hfits2
        hafter (hsteps1.codeLoaded hcode)
      dsimp only at hstep2
      cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
      | error e =>
        rw [hcc2] at hstep2 hfits_after1
        rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 rck e hsc hcc1 hcc2]
        obtain ⟨s2, trG', r1', hsteps2, herr2⟩ := hstep2
        rw [← M.stepEvents_append evs1 evs2 st] at herr2
        have henv : s3EnvOf C s3CommitEnv x trG tr (evs1 ++ evs2) := by
          unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1]; dsimp only; rw [hcc2]
          exact SeqEnv.append rfl rfl
        exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inl ⟨evs1 ++ evs2, trG', r1', henv, herr2⟩⟩
      | ok p2 =>
        rcases p2 with ⟨finalRootKey, senderChainKey⟩
        rw [hcc2] at hstep2 hfits_after1
        rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
        obtain ⟨s2, hsteps2, hcm⟩ := hstep2
        have hsteps12 := Steps.trans hsteps1 hsteps2
        have hclamp := clampScalar_keyPair_generate C (coinsOf x.rest)
        obtain ⟨s3, hsteps3, ⟨evs3, trG', henv3, hcaps3, hpost3⟩ | ⟨hpan3, hq3⟩⟩ :=
          hcommit x (M.stepEvents evs2 (M.stepEvents evs1 st)) trG tr st1 sc rck
            newSenderKey finalRootKey senderChainKey R s0 s2
            hsc hrc_len hclamp (hfits_after1.seq_right rfl) hcm (hsteps12.codeLoaded hcode)
        · rw [← M.stepEvents_append evs1 evs2 st,
              ← M.stepEvents_append (evs1 ++ evs2) evs3 st,
              List.append_assoc] at hpost3
          have henv : s3EnvOf C s3CommitEnv x trG tr (evs1 ++ (evs2 ++ evs3)) := by
            unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1]; dsimp only; rw [hcc2]
            exact SeqEnv.append rfl (SeqEnv.append rfl henv3)
          exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inl ⟨evs1 ++ (evs2 ++ evs3), trG', henv, hcaps3, hpost3⟩⟩
        · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inr ⟨hpan3, hq3⟩⟩

theorem s3_pinned_cro_placed_okT_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : CliS3CommitSeamPinnedPlaced prog entry C A lim ctl uuidTryParse spqrNoPanic s3CommitEnv) :
    S3TightSeamPinnedPlaced prog entry C A lim ctl uuidTryParse S (s3EnvOf C s3CommitEnv) := by
  intro x st trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode
  refine dhStep_cli_withStack_cro_pinned_ok hwp C A lim ctl createChainStack
    stackAt_subStack_createChain (tryDecryptOnPanicTight C S uuidTryParse)
    hcc hdpk hrng hsd ?_ x st trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode
  intro x' st_c trG' tr' st1' sc rck newSenderKey finalRootKey senderChainKey R' s0' s_c
    hsc hlen hclamp hfit_c hcm hcode_c
  obtain ⟨s3, hsteps3, hok | ⟨hpan3, hq3⟩⟩ :=
    hcommit x' st_c trG' tr' st1' sc rck newSenderKey finalRootKey senderChainKey R' s0' s_c
      hsc hlen hclamp hfit_c hcm hcode_c
  · exact ⟨s3, hsteps3, Or.inl hok⟩
  · exact ⟨s3, hsteps3, Or.inr ⟨hpan3, onPanicTightBudget_of_spqrNoPanic hq3⟩⟩

theorem s3_cro_placed_okT_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : CliS3CommitSeamPlaced prog entry C A lim ctl uuidTryParse spqrNoPanic s3CommitEnv) :
    S3TightSeamPlaced prog entry C A lim ctl uuidTryParse S (s3EnvOf C s3CommitEnv) := by
  intro x st trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, hvm, herr⟩ :=
      dhStep_missing_sender_chain_vm_placed_cli (A := A.atState lim st s) hwp x trG tr st1 R s0 s hsc hs3 hcode
    have herr' : ErrTailStatePlaced entry A lim (M.stepEvents [] st) ctl
        x trG tr st1 (.invalidSessionStructure .missingSenderChain) 0 R s0 s' := by
      rw [M.stepEvents_nil st]
      simpa only [ErrTailStatePlaced, A.atState_eq_of_vmPreserved lim st hvm] using herr
    exact ⟨s', hsteps, Or.inl ⟨[], trG, tr.ratchet, by unfold s3EnvOf; rw [hsc], herr'⟩⟩
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hfits1 := fitsEnv_cc1_of_s3EnvOf hsc hfits
    have hstep1 := dhStep_recv_create_chain_withStack_cro_placed_cli A lim st createChainStack
      stackAt_subStack_createChain hwp hcc x trG tr st1 sc R s0 s hsc hrk1_ne hfits1 hs3 hcode
    dsimp only at hstep1
    set evs1 := dhStepPairEvents C x.msg.senderRatchetKey sc.ratchetKey.privateKey
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at hstep1
      rw [dhRatchetStep_some_err1 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc e hsc hcc1,
          decryptDraws_of_cc1_err C x.st st1 tr x.msg.senderRatchetKey x.rest sc e hfrom hfind hsc hcc1]
      obtain ⟨s1, trG', r1', hsteps1, herr1⟩ := hstep1
      exact ⟨s1, hsteps1, Or.inl ⟨evs1, trG', r1', by unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1], herr1⟩⟩
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩; rw [hcc1] at hstep1
      rw [decryptDraws_of_cc1_ok C x.st st1 tr x.msg.senderRatchetKey x.rest sc rk1 rck hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, hafter⟩ := hstep1
      set newSenderKey := KeyPair.generate C (coinsOf x.rest)
      set evs2 := dhStepPairEvents C x.msg.senderRatchetKey newSenderKey.privateKey
      have hfits_after1 : FitsEnv M lim (M.stepEvents evs1 st)
          (match rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
           | .error _ => (· = evs2)
           | .ok _ => SeqEnv (· = evs2) (s3CommitEnv x trG tr)) := by
        unfold s3EnvOf at hfits; rw [hsc] at hfits; dsimp only at hfits; rw [hcc1] at hfits; dsimp only at hfits
        cases hcc2' : rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey <;>
          (rw [hcc2'] at hfits; exact hfits.seq_right rfl)
      have hfits2 : FitsEnv M lim (M.stepEvents evs1 st) (· = evs2) := by
        cases hcc2' : rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey <;>
          rw [hcc2'] at hfits_after1
        · exact hfits_after1
        · exact hfits_after1.seq_left
      have hstep2 := dhStep_keygen_and_send_create_chain_withStack_cro_placed_cli
        A lim (M.stepEvents evs1 st) createChainStack stackAt_subStack_createChain hwp hcc hdpk
        x trG tr st1 rk1 rck R s0 s1 (hrng x.cur x.rest hx_rest) hsd hrk2_ne hfits2 hafter (hsteps1.codeLoaded hcode)
      dsimp only at hstep2
      cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
      | error e =>
        rw [hcc2] at hstep2 hfits_after1
        rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 rck e hsc hcc1 hcc2]
        obtain ⟨s2, trG', r1', hsteps2, herr2⟩ := hstep2
        rw [← M.stepEvents_append evs1 evs2 st] at herr2
        have henv : s3EnvOf C s3CommitEnv x trG tr (evs1 ++ evs2) := by
          unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1]; dsimp only; rw [hcc2]; exact SeqEnv.append rfl rfl
        exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inl ⟨evs1 ++ evs2, trG', r1', henv, herr2⟩⟩
      | ok p2 =>
        rcases p2 with ⟨finalRootKey, senderChainKey⟩; rw [hcc2] at hstep2 hfits_after1
        rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
        obtain ⟨s2, hsteps2, hcm⟩ := hstep2
        have hsteps12 := Steps.trans hsteps1 hsteps2
        obtain ⟨s3, hsteps3, ⟨evs3, trG', henv3, hpost3⟩ | ⟨hpan3, hq3⟩⟩ :=
          hcommit x (M.stepEvents evs2 (M.stepEvents evs1 st)) trG tr st1 sc rck
            newSenderKey finalRootKey senderChainKey R s0 s2 hsc hrc_len
            (clampScalar_keyPair_generate C (coinsOf x.rest)) (hfits_after1.seq_right rfl) hcm (hsteps12.codeLoaded hcode)
        · rw [← M.stepEvents_append evs1 evs2 st, ← M.stepEvents_append (evs1 ++ evs2) evs3 st, List.append_assoc] at hpost3
          have henv : s3EnvOf C s3CommitEnv x trG tr (evs1 ++ (evs2 ++ evs3)) := by
            unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1]; dsimp only; rw [hcc2]
            exact SeqEnv.append rfl (SeqEnv.append rfl henv3)
          exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inl ⟨evs1 ++ (evs2 ++ evs3), trG', henv, hpost3⟩⟩
        · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inr ⟨hpan3, onPanicTightBudget_of_spqrNoPanic hq3⟩⟩

theorem s3_pinned_placed_okT_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (withLsCodeLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : CliS3CommitSeamPinnedPlaced prog entry C A lim ctl uuidTryParse spqrNoPanic s3CommitEnv) :
    S3TightSeamPinnedPlaced prog entry C A lim ctl uuidTryParse S (s3EnvOf C s3CommitEnv) :=
  s3_pinned_cro_placed_okT_cli hwp C A lim ctl S
    (subroutine_ok_withLsCodeRoLoaded_of_plain hcc)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hdpk)
    (fun cur rest h => subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (hrng cur rest h))
    hsd hcommit

theorem s3_placed_okT_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (withLsCodeLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : CliS3CommitSeamPlaced prog entry C A lim ctl uuidTryParse spqrNoPanic s3CommitEnv) :
    S3TightSeamPlaced prog entry C A lim ctl uuidTryParse S (s3EnvOf C s3CommitEnv) :=
  s3_cro_placed_okT_cli hwp C A lim ctl S
    (subroutine_ok_withLsCodeRoLoaded_of_plain hcc)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hdpk)
    (fun cur rest h => subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (hrng cur rest h))
    hsd hcommit

theorem s3_pinned_cro_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : CliS3CommitSeamPinnedPlaced prog entry C A lim ctl uuidTryParse spqrNoPanic s3CommitEnv) :
    CliS3SeamPinnedPlaced prog entry C A lim ctl uuidTryParse S (s3EnvOf C s3CommitEnv) :=
  .ofTight (s3_pinned_cro_placed_okT_cli hwp C A lim ctl S hcc hdpk hrng hsd hcommit)

theorem s3_cro_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : CliS3CommitSeamPlaced prog entry C A lim ctl uuidTryParse spqrNoPanic s3CommitEnv) :
    CliS3SeamPlaced prog entry C A lim ctl uuidTryParse S (s3EnvOf C s3CommitEnv) :=
  .ofTight (s3_cro_placed_okT_cli hwp C A lim ctl S hcc hdpk hrng hsd hcommit)

theorem s3_pinned_x_cro_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : CliS3CommitSeamPinnedXPlaced prog entry C decFn A lim ctl parse S s3CommitEnv) :
    CliS3SeamPinnedXPlaced prog entry C decFn A lim ctl parse S (s3EnvOf C s3CommitEnv) := by
  intro x st trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode
  exact dhStep_cli_withStack_cro_pinned_ok hwp C A lim ctl createChainStackX
    stackAt_subStack_createChainX (tryDecryptFnOnPanic C decFn parse S)
    hcc hdpk hrng hsd hcommit x st trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode

theorem s3_x_cro_placed_ok_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : CliS3CommitSeamPinnedXPlaced prog entry C decFn A lim ctl parse S s3CommitEnv) :
    CliS3SeamXPlaced prog entry C decFn A lim ctl parse S (s3EnvOf C s3CommitEnv) :=
  (s3_pinned_x_cro_placed_ok_cli hwp C decFn A lim ctl parse S hcc hdpk hrng hsd hcommit).toUnpinned

theorem dhStep_433_pinned_cro_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3TightSeamPinnedPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_pinned_cro_placed_okT_cli (dhStepBlockVmWp_549 H) C A lim ctl S hcc hdpk hrng hsd
    (s3_commit_433_pinned_placed_ok H C A lim ctl spqrNoPanic hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove)

theorem dhStep_433_pinned_cro_budget_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3TightSeamPinnedPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  dhStep_433_pinned_cro_placed_okT H C A lim ctl S hcc hdpk hrng hsd
    hPkSer hToPb hGrowOne hDropChain hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove

theorem dhStep_433_cro_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3TightSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  (dhStep_433_pinned_cro_placed_okT H C A lim ctl S hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem dhStep_433_cro_budget_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3TightSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  (dhStep_433_pinned_cro_budget_placed_okT H C A lim ctl S hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem dhStep_433_pinned_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3TightSeamPinnedPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  dhStep_433_pinned_cro_placed_okT H C A lim ctl S
    (subroutine_ok_withLsCodeRoLoaded_of_plain hcc)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hdpk)
    (fun cur rest h => subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (hrng cur rest h))
    hsd hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

theorem dhStep_433_pinned_budget_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3TightSeamPinnedPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  dhStep_433_pinned_placed_okT H C A lim ctl S hcc hdpk hrng hsd
    hPkSer hToPb hGrowOne hDropChain hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove

theorem dhStep_433_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3TightSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  (dhStep_433_pinned_placed_okT H C A lim ctl S hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem dhStep_433_budget_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpec M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpec M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneSpec M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpec M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3TightSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  (dhStep_433_pinned_budget_placed_okT H C A lim ctl S hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).toUnpinned

theorem dhStep_433_pinned_x_cro_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State)) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200) (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 618) (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hPkSer : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 205) (publicKeySerializeSpecX M A lim))
    (hToPb : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 22) (chainKeyToPbSpecX M A lim))
    (hGrowOne : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 43) (growOneChainSpecX M A lim))
    (hDropChain : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 445) (dropChainSpecX M A lim))
    (hShim : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX)) :
    CliS3SeamPinnedXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434) C decFn A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_pinned_x_cro_placed_ok_cli (dhStepBlockVmWp_549 H) C decFn A lim ctl uuidTryParse S hcc hdpk hrng hsd
    (s3_commit_433_pinned_x_budget_placed_ok H C decFn A lim ctl S hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove)

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget
