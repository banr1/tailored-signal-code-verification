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
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import ProofLib.RegChain

/-!
# Budget-Threaded Segment S3 (`DhStep`) Composition & Seam Theorems

Composes `DhStepBudgetCore` with `DhCommitMainBudget` to prove total-correctness (`dhStep_placed_ok`,
`dhStep_x_placed_ok`) and seam-level (`s3_placed_ok`, `s3_placed_okT`, `s3_x_placed_ok`, and block
`130` / `433` specializations) Segment S3 contracts (`+0x500 → +0x3e4 / +0x30c`) over
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open Arm64 ProofLib
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair Mut PrivateKey PublicKey RatchetState ReceiverChain RootKey
  SenderChain SessionState TripleRatchet rootCreateChain
)
open CryptoVerification (
  LibsignalPlacement lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl
)
open CryptoVerification.RustHeap (vecAt vecU8At)
open CryptoVerification.LibsignalSessionRepr (
  chainAt chainKeyBytes length_keyToBytes32 msgTypeByte optSenderChainBytes ratchetAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser coinsOf decryptDraws protocolAddressAt sessionStateAt signalMessageAt tapeAfter utf8
  uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  CreateChainGhost SpqrModel TrGhost TryDecryptGhost calculateAgreement createChainResultAt
  createChainStack createChainStackX logOff rootStack trAt
)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack dropChainStackX)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_131 blkPC_434 blkPl_131 blkPl_434
  speBodyAt tryDecryptCommonHeap tryDecryptMidMetaPlaced
  tryDecryptPlacedImg tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (
  clampScalar_keyPair_generate decryptDraws_of_cc1_err decryptDraws_of_cc1_ok
  decryptDraws_of_senderChain_none dhRatchetStep_none dhRatchetStep_some_err1
  dhRatchetStep_some_err2 dhRatchetStep_some_ok fold_1d8_after_cc2_err fold_390_3b0_to_memRegion
  fold_after_cc2_ok fold_sp_20_after_cc2_err optSenderChainBytes_some_split
  pointsTo64_zero_32 pointsTo_32_as_four_64 rk_ne_zero signalMessageAt_senderRatchetKey
  signalMessageRestAt split_140_for_cc1 stackAt_subStack_createChain
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd (spqrNoPanic)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (growOneChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpec chainKeyToPbSpecX derivePublicKeyBytesBudgetSpec
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
  publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (growOneSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec dropChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (
  CreateChainEnv createChainEvents createChainSpec createChainSpecWithStack createChainSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  ConsumeMsgKeyStatePlaced DhStepStatePlaced ErrTailStatePlaced
  S3SeamPlaced S3SeamXPlaced tryDecryptOnPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (
  S3SeamTightPlaced S3SeamTightXPlaced tryDecryptOnPanicTight
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (
  DhCommitBlockVmWp dhCommitBlockVmWp_159 dhCommitBlockVmWp_549 s3CommitDefaultEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudget (
  DhCommitStatePlaced S3CommitSeamPlaced S3CommitSeamXPlaced
  dhCommit_placed_ok dhCommit_x_placed_ok
  s3_commit_159_placed_ok s3_commit_549_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (
  DhStepBlockVmWp dhStepBlockVmWp_159 dhStepBlockVmWp_549
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps (
  lsStaticDropSym rngFillAtBudgetSpec zeroizeSecretBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux (
  dhStep_after_cc1_to_cc2_call_vm_placed dhStep_cc1_err_branch_vm_placed
  dhStep_cc1_ok_branch_vm_placed dhStep_cc2_err_branch_vm_placed
  dhStep_cc2_ok_branch_vm_placed dhStep_missing_sender_chain_vm_placed
)

open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (
  DhStepAfterRecvChainStatePlaced createChainEnv_eq_dhStepPairEvents
  dhStepPairEvents dhStep_keygen_and_send_create_chain_withStack_placed
  dhStep_recv_create_chain_withStack_placed fitsEnv_cc1_of_s3EnvOf
  onPanicTightBudget_of_spqrNoPanic s3DefaultEnv s3EnvOf
  stackAt_subStack_createChainX
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 3. Total-Correctness `dhStep` Composition & Seam Theorems (`S3Seam*Placed`) -/

/-- Stack- and commit-callback-parametric total-correctness (`0`-panic) composition for `DhStep`. -/
theorem dhStep_withStack_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (ccStack : Nat)
    (hstack_split : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        (stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
         stackAt sp ccStack))
    (s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpecWithStack M A lim C ccStack))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit_ok :
      ∀ (x : TryDecryptGhost) (st_c : M.σ) (trG : TrGhost)
        (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
        (sc : SenderChain) (rck : ChainKey) (newSenderKey : KeyPair)
        (finalRootKey : RootKey) (senderChainKey : ChainKey) (R : SepProp) (s0 s_c : State),
        tr.ratchet.senderChain = some sc →
        tr.ratchet.receiverChains.length < 2 ^ 32 →
        clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
        FitsEnv M lim st_c (s3CommitEnv x trG tr) →
        DhCommitStatePlaced entry A lim st_c ctl x trG tr st1
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
        ∃ s' evs trG',
          Steps prog s_c s' ∧
          s3CommitEnv x trG tr evs ∧
          ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st_c) ctl
            x trG' { tr with ratchet := r1 } st1 rck (min 32 x.rest.length) R s0 s')
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
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
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet with
    | (.ok ck, r1) =>
      ∃ s' evs trG',
        Steps prog s s' ∧
        s3EnvOf C s3CommitEnv x trG tr evs ∧
        ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
          x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
    | (.error e, _) =>
      ∃ s' evs trG' r1',
        Steps prog s s' ∧
        s3EnvOf C s3CommitEnv x trG tr evs ∧
        ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
          x trG' { tr with ratchet := r1' } st1 e draws R s0 s' := by
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, hvm, herr⟩ :=
      dhStep_missing_sender_chain_vm_placed (A := A.atState lim st s) hwp
        x trG tr st1 R s0 s hsc hs3 hcode
    have herr' : ErrTailStatePlaced entry A lim (M.stepEvents [] st) ctl
        x trG tr st1 (.invalidSessionStructure .missingSenderChain) 0 R s0 s' := by
      rw [M.stepEvents_nil st]
      simpa only [ErrTailStatePlaced, A.atState_eq_of_vmPreserved lim st hvm] using herr
    have henv : s3EnvOf C s3CommitEnv x trG tr [] := by
      unfold s3EnvOf; rw [hsc]
    exact ⟨s', [], trG, tr.ratchet, hsteps, henv, herr'⟩
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hfits1 := fitsEnv_cc1_of_s3EnvOf hsc hfits
    have hstep1 := dhStep_recv_create_chain_withStack_placed A lim st ccStack hstack_split
      hwp hcc x trG tr st1 sc R s0 s hsc hrk1_ne hfits1 hs3 hcode
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
      exact ⟨s1, evs1, trG', r1', hsteps1, henv, herr1⟩
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
        unfold s3EnvOf at hfits
        rw [hsc] at hfits
        dsimp only at hfits
        rw [hcc1] at hfits
        dsimp only at hfits
        cases hcc2' : rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey <;>
          (rw [hcc2'] at hfits; exact hfits.seq_right rfl)
      have hfits2 : FitsEnv M lim (M.stepEvents evs1 st) (· = evs2) := by
        cases hcc2' : rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey <;>
          rw [hcc2'] at hfits_after1
        · exact hfits_after1
        · exact hfits_after1.seq_left
      have hstep2 := dhStep_keygen_and_send_create_chain_withStack_placed
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
        exact ⟨s2, evs1 ++ evs2, trG', r1', Steps.trans hsteps1 hsteps2, henv, herr2⟩
      | ok p2 =>
        rcases p2 with ⟨finalRootKey, senderChainKey⟩
        rw [hcc2] at hstep2 hfits_after1
        rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
        obtain ⟨s2, hsteps2, hcm⟩ := hstep2
        have hsteps12 := Steps.trans hsteps1 hsteps2
        have hclamp := clampScalar_keyPair_generate C (coinsOf x.rest)
        have hfits_commit : FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
            (s3CommitEnv x trG tr) :=
          hfits_after1.seq_right rfl
        obtain ⟨s3, evs3, trG', hsteps3, henv3, hpost3⟩ :=
          hcommit_ok x (M.stepEvents evs2 (M.stepEvents evs1 st)) trG tr st1 sc rck
            newSenderKey finalRootKey senderChainKey R s0 s2
            hsc hrc_len hclamp hfits_commit hcm (hsteps12.codeLoaded hcode)
        rw [← M.stepEvents_append evs1 evs2 st,
            ← M.stepEvents_append (evs1 ++ evs2) evs3 st,
            List.append_assoc] at hpost3
        have henv : s3EnvOf C s3CommitEnv x trG tr (evs1 ++ (evs2 ++ evs3)) := by
          unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1]; dsimp only; rw [hcc2]
          exact SeqEnv.append rfl (SeqEnv.append rfl henv3)
        exact ⟨s3, evs1 ++ (evs2 ++ evs3), trG', Steps.trans hsteps12 hsteps3, henv, hpost3⟩

/-- Total-correctness (`0`-panic) S3 segment theorem at standard stack heights. -/
theorem dhStep_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry dropChainEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hwpCommit : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hfrom : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (hfind : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hsp0 : rootStack ≤ s0.sp.toNat)
    (hx_rest : x.rest.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (s3DefaultEnv C x trG tr))
    (hs3 : DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s)
    (hcode : prog.CodeLoaded s.mem)
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
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet with
    | (.ok ck, r1) =>
      ∃ s' evs trG',
        Steps prog s s' ∧
        s3DefaultEnv C x trG tr evs ∧
        ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
          x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
    | (.error e, _) =>
      ∃ s' evs trG' r1',
        Steps prog s s' ∧
        s3DefaultEnv C x trG tr evs ∧
        ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
          x trG' { tr with ratchet := r1' } st1 e draws R s0 s' :=
  dhStep_withStack_ok hwp C A lim st ctl createChainStack stackAt_subStack_createChain
    s3CommitDefaultEnv hcc hdpk hrng hsd
    (fun x' st_c trG' tr' st1' sc rck newSenderKey finalRootKey senderChainKey R' s0' s_c
      hsc hrc hclamp hfits_c hS3_c hL =>
      dhCommit_placed_ok hwpCommit A lim st_c ctl hPkSer hToPb hGrowOne hDropChain
        hShim hAlloc hDealloc hMemcpy hMemmove
        x' trG' tr' st1' sc rck newSenderKey finalRootKey senderChainKey
        R' s0' s_c hsc hrc hclamp hfits_c hS3_c hL)
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode

/-- Total-correctness (`0`-panic) S3 segment theorem at `extHookStack` (`X`). -/
theorem dhStep_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry dropChainEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hwpCommit : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpecX M A lim C))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hfrom : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (hfind : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hsp0 : rootStack ≤ s0.sp.toNat)
    (hx_rest : x.rest.length < 2 ^ 63)
    (hfits : FitsEnv M lim st (s3DefaultEnv C x trG tr))
    (hs3 : DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s)
    (hcode : prog.CodeLoaded s.mem)
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
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet with
    | (.ok ck, r1) =>
      ∃ s' evs trG',
        Steps prog s s' ∧
        s3DefaultEnv C x trG tr evs ∧
        ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
          x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
    | (.error e, _) =>
      ∃ s' evs trG' r1',
        Steps prog s s' ∧
        s3DefaultEnv C x trG tr evs ∧
        ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
          x trG' { tr with ratchet := r1' } st1 e draws R s0 s' :=
  dhStep_withStack_ok hwp C A lim st ctl createChainStackX stackAt_subStack_createChainX
    s3CommitDefaultEnv hcc hdpk hrng hsd
    (fun x' st_c trG' tr' st1' sc rck newSenderKey finalRootKey senderChainKey R' s0' s_c
      hsc hrc hclamp hfits_c hS3_c hL =>
      dhCommit_x_placed_ok hwpCommit A lim st_c ctl hPkSer hToPb hGrowOne hDropChain
        hShim hAlloc hDealloc hMemcpy hMemmove
        x' trG' tr' st1' sc rck newSenderKey finalRootKey senderChainKey
        R' s0' s_c hsc hrc hclamp hfits_c hS3_c hL)
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode

/-- Seam-parametric proof of `S3SeamTightPlaced` from `S3CommitSeamPlaced` at `spqrNoPanic`. -/
theorem s3_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : S3CommitSeamPlaced prog entry C A lim ctl uuidTryParse spqrNoPanic s3CommitEnv) :
    S3SeamTightPlaced prog entry C A lim ctl uuidTryParse S (s3EnvOf C s3CommitEnv) := by
  intro x st trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, hvm, herr⟩ :=
      dhStep_missing_sender_chain_vm_placed (A := A.atState lim st s) hwp
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
    have hstep1 := dhStep_recv_create_chain_withStack_placed A lim st createChainStack
      stackAt_subStack_createChain hwp hcc x trG tr st1 sc R s0 s hsc hrk1_ne hfits1 hs3 hcode
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
      have hstep2 := dhStep_keygen_and_send_create_chain_withStack_placed
        A lim (M.stepEvents evs1 st) createChainStack stackAt_subStack_createChain hwp hcc hdpk
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
        obtain ⟨s3, hsteps3, ⟨evs3, trG', henv3, hpost3⟩ | ⟨hpan3, hq3⟩⟩ :=
          hcommit x (M.stepEvents evs2 (M.stepEvents evs1 st)) trG tr st1 sc rck
            newSenderKey finalRootKey senderChainKey R s0 s2
            hsc hrc_len hclamp (hfits_after1.seq_right rfl) hcm (hsteps12.codeLoaded hcode)
        · rw [← M.stepEvents_append evs1 evs2 st,
              ← M.stepEvents_append (evs1 ++ evs2) evs3 st,
              List.append_assoc] at hpost3
          have henv : s3EnvOf C s3CommitEnv x trG tr (evs1 ++ (evs2 ++ evs3)) := by
            unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1]; dsimp only; rw [hcc2]
            exact SeqEnv.append rfl (SeqEnv.append rfl henv3)
          exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inl ⟨evs1 ++ (evs2 ++ evs3), trG', henv, hpost3⟩⟩
        · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inr ⟨hpan3, onPanicTightBudget_of_spqrNoPanic hq3⟩⟩

/-- Seam-parametric proof of `S3SeamPlaced` from `S3CommitSeamPlaced` at `spqrNoPanic`. -/
theorem s3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpec M A lim C))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : S3CommitSeamPlaced prog entry C A lim ctl uuidTryParse spqrNoPanic s3CommitEnv) :
    S3SeamPlaced prog entry C A lim ctl uuidTryParse S (s3EnvOf C s3CommitEnv) :=
  (s3_placed_okT hwp C A lim ctl S hcc hdpk hrng hsd hcommit).weaken

/-- Seam-parametric proof of `S3SeamXPlaced` (`extHookStack`) from `S3CommitSeamXPlaced`. -/
theorem s3_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpecX M A lim C))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hcommit : S3CommitSeamXPlaced prog entry C decFn A lim ctl parse S s3CommitEnv) :
    S3SeamXPlaced prog entry C decFn A lim ctl parse S (s3EnvOf C s3CommitEnv) := by
  intro x st trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, hvm, herr⟩ :=
      dhStep_missing_sender_chain_vm_placed (A := A.atState lim st s) hwp
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
    have hstep1 := dhStep_recv_create_chain_withStack_placed A lim st createChainStackX
      stackAt_subStack_createChainX hwp hcc x trG tr st1 sc R s0 s hsc hrk1_ne hfits1 hs3 hcode
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
      have hstep2 := dhStep_keygen_and_send_create_chain_withStack_placed
        A lim (M.stepEvents evs1 st) createChainStackX stackAt_subStack_createChainX hwp hcc hdpk
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
        obtain ⟨s3, hsteps3, ⟨evs3, trG', henv3, hpost3⟩ | ⟨hpan3, hq3⟩⟩ :=
          hcommit x (M.stepEvents evs2 (M.stepEvents evs1 st)) trG tr st1 sc rck
            newSenderKey finalRootKey senderChainKey R s0 s2
            hsc hrc_len hclamp (hfits_after1.seq_right rfl) hcm (hsteps12.codeLoaded hcode)
        · rw [← M.stepEvents_append evs1 evs2 st,
              ← M.stepEvents_append (evs1 ++ evs2) evs3 st,
              List.append_assoc] at hpost3
          have henv : s3EnvOf C s3CommitEnv x trG tr (evs1 ++ (evs2 ++ evs3)) := by
            unfold s3EnvOf; rw [hsc]; dsimp only; rw [hcc1]; dsimp only; rw [hcc2]
            exact SeqEnv.append rfl (SeqEnv.append rfl henv3)
          exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inl ⟨evs1 ++ (evs2 ++ evs3), trG', henv, hpost3⟩⟩
        · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inr ⟨hpan3, hq3⟩⟩

/-- Tight `S3SeamTightXPlaced` from `DhCommitBlockVmWp` (`0`-panic total commit). -/
theorem s3_total_x_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry dropChainEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hwpCommit : DhCommitBlockVmWp prog entry dropChainEntry)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpecX M A lim C))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamTightXPlaced prog entry C decFn A lim ctl parse S (s3DefaultEnv C) := by
  intro x st trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode
  have htot := dhStep_x_placed_ok hwp hwpCommit C A lim st ctl
    hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hx_rest hfits hs3 hcode
  dsimp only at htot ⊢
  revert htot
  rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet
    with ⟨_ | ck, r1⟩
  · rintro ⟨s', evs, trG', r1', hsteps, henv, herr⟩
    exact ⟨s', hsteps, Or.inl ⟨evs, trG', r1', henv, herr⟩⟩
  · rintro ⟨s', evs, trG', hsteps, henv, hok⟩
    exact ⟨s', hsteps, Or.inl ⟨evs, trG', henv, hok⟩⟩

/-! ## 4. Block `130` (`_159`) and Block `433` (`_549`) Specializations -/

/-- Tight S3 seam (`S3SeamTightPlaced`) for Block `130` (`try_decrypt_with_state::<HookRng>`). -/
theorem s3_159_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 40)
      (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
        (lsmpl.ρ "libsignal_session_rng_fill") (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamTightPlaced ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 131)
      C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_placed_okT (dhStepBlockVmWp_159 H) C A lim ctl S hcc hdpk hrng hsd
    (s3_commit_159_placed_ok H C A lim ctl spqrNoPanic
      hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove)

/-- S3 seam (`S3SeamPlaced`) for Block `130` (`try_decrypt_with_state::<HookRng>`). -/
theorem s3_159_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 40)
      (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
        (lsmpl.ρ "libsignal_session_rng_fill") (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 131)
      C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  (s3_159_placed_okT H C A lim ctl S hcc hdpk hrng hsd
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).weaken

/-- Conditional-OOM (`rustCliAllocBudgetSpec`) wrapper for `s3_159_placed_ok`. -/
theorem s3_159_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 40)
      (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
        (lsmpl.ρ "libsignal_session_rng_fill") (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStack)) :
    S3SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 131)
      C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_159_placed_ok H C A lim ctl S hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain
    hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove

/-- Tight `X` S3 seam (`S3SeamTightXPlaced`) for Block `130` (`try_decrypt_with_state::<HookRng>`). -/
theorem s3_159_x_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 40)
      (createChainSpecX M A lim C))
    (hdpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
        (lsmpl.ρ "libsignal_session_rng_fill") (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamTightXPlaced ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 131)
      C decFn A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_total_x_placed_okT (dhStepBlockVmWp_159 H) (dhCommitBlockVmWp_159 H)
    C decFn A lim ctl uuidTryParse S
    hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

/-- `X` S3 seam (`S3SeamXPlaced`) for Block `130` (`try_decrypt_with_state::<HookRng>`). -/
theorem s3_159_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 40)
      (createChainSpecX M A lim C))
    (hdpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
        (lsmpl.ρ "libsignal_session_rng_fill") (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 131)
      C decFn A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  (s3_159_x_placed_okT H C decFn A lim ctl S hcc hdpk hrng hsd
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).weaken

/-- Conditional-OOM (`rustCliAllocBudgetSpec`) wrapper for `s3_159_x_placed_ok`. -/
theorem s3_159_x_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 40)
      (createChainSpecX M A lim C))
    (hdpk : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
        (lsmpl.ρ "libsignal_session_rng_fill") (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
      (lsmpl.ρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropChainStackX)) :
    S3SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 131)
      C decFn A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_159_x_placed_ok H C decFn A lim ctl S hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain
    hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove

/-- Tight S3 seam (`S3SeamTightPlaced`) for Block `433` (`try_decrypt_with_state::<Coins>`). -/
theorem s3_549_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40)
      (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
        (lsmpl.base 618) (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamTightPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_placed_okT (dhStepBlockVmWp_549 H) C A lim ctl S hcc hdpk hrng hsd
    (s3_commit_549_placed_ok H C A lim ctl spqrNoPanic
      hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove)

/-- S3 seam (`S3SeamPlaced`) for Block `433` (`try_decrypt_with_state::<Coins>`). -/
theorem s3_549_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40)
      (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
        (lsmpl.base 618) (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  (s3_549_placed_okT H C A lim ctl S hcc hdpk hrng hsd
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).weaken

/-- Conditional-OOM (`rustCliAllocBudgetSpec`) wrapper for `s3_549_placed_ok`. -/
theorem s3_549_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40)
      (createChainSpec M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
        (lsmpl.base 618) (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_549_placed_ok H C A lim ctl S hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain
    hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove

/-- Tight `X` S3 seam (`S3SeamTightXPlaced`) for Block `433` (`try_decrypt_with_state::<Coins>`). -/
theorem s3_549_x_placed_okT [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40)
      (createChainSpecX M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
        (lsmpl.base 618) (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamTightXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C decFn A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_total_x_placed_okT (dhStepBlockVmWp_549 H) (dhCommitBlockVmWp_549 H)
    C decFn A lim ctl uuidTryParse S
    hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove

/-- `X` S3 seam (`S3SeamXPlaced`) for Block `433` (`try_decrypt_with_state::<Coins>`). -/
theorem s3_549_x_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40)
      (createChainSpecX M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
        (lsmpl.base 618) (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C decFn A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  (s3_549_x_placed_okT H C decFn A lim ctl S hcc hdpk hrng hsd
    hPkSer hToPb hGrowOne hDropChain hShim hAlloc hDealloc hMemcpy hMemmove).weaken

/-- Conditional-OOM (`rustCliAllocBudgetSpec`) wrapper for `s3_549_x_placed_ok`. -/
theorem s3_549_x_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (H : String → Option (State → State))
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (hcc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 40)
      (createChainSpecX M A lim C))
    (hdpk : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 200)
      (derivePublicKeyBytesBudgetSpec C.pubKey))
    (hrng : ∀ cur rest, rest.length < 2 ^ 63 →
      subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
        (lsmpl.base 618) (rngFillAtBudgetSpec ctl cur rest))
    (hsd : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
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
    S3SeamXPlaced ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      C decFn A lim ctl uuidTryParse S (s3DefaultEnv C) :=
  s3_549_x_placed_ok H C decFn A lim ctl S hcc hdpk hrng hsd hPkSer hToPb hGrowOne hDropChain
    hShim (subroutine_ok_allocNoOom_of_budget hAlloc) hDealloc hMemcpy hMemmove

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudget
