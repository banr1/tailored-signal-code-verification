/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import ProofLib.RegChain

/-!
# Budget-Threaded `DhStep` Core Envelopes & `create_chain` Stepping

Defines the post-receiving-chain checkpoint `DhStepAfterRecvChainStatePlaced` (`entry + 0x70c`),
the Segment S3 allocator event envelopes (`dhStepPairEvents`, `s3EnvOf`, `s3DefaultEnv`), and
total-correctness stepping theorems across both `RootKey::create_chain` calls
(`dhStep_recv_create_chain_withStack_placed`, `dhStep_keygen_and_send_create_chain_withStack_placed`)
over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore

open Arm64 ProofLib
open CryptoGames.Ratchet (clampScalar createChain)
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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd (model_fst_eq_panic_of_spqrNoPanic spqrNoPanic)
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Intermediate State, Stack Split (`X`), and Event Envelopes -/

/-- Relocatable intermediate state at `entry + 0x70c#64` after `RootKey::create_chain` #1 succeeds,
    evaluated at `A.atState lim st s`. -/
abbrev DhStepAfterRecvChainStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.DhStepAfterRecvChainStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 rk1 rck R s0 s

/-- Sub-stack decomposition of `tryDecryptSubStack` for `createChainStackX` (`Stage2ContractsX`). -/
theorem stackAt_subStack_createChainX (sp : BitVec 64) :
    stackAt sp tryDecryptSubStack =
      (stackAt (sp - BitVec.ofNat 64 createChainStackX)
         (tryDecryptSubStack - createChainStackX) ∗
       stackAt sp createChainStackX) := by
  dsimp only [stackAt]
  have hadd : BitVec.ofNat 64 tryDecryptSubStack =
      BitVec.ofNat 64 createChainStackX +
        BitVec.ofNat 64 (tryDecryptSubStack - createChainStackX) := by
    decide
  rw [show sp - BitVec.ofNat 64 createChainStackX -
        BitVec.ofNat 64 (tryDecryptSubStack - createChainStackX) =
        sp - BitVec.ofNat 64 tryDecryptSubStack by rw [hadd]; bv_arith]
  exact memRegion_split'
    (b := sp - BitVec.ofNat 64 tryDecryptSubStack)
    (b' := sp - BitVec.ofNat 64 createChainStackX)
    (n := tryDecryptSubStack - createChainStackX)
    (k := createChainStackX)
    (by decide) (by rw [hadd]; bv_arith) (by decide)

/-- Deterministic `AllocEvent` list emitted by one `RootKey::create_chain` call on `(their, our)`. -/
def dhStepPairEvents (C : Crypto) (their : PublicKey) (our : PrivateKey) : List AllocEvent :=
  match calculateAgreement C.X their our with
  | some _ => rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
  | none => []

theorem createChainEnv_eq_dhStepPairEvents (C : Crypto) (ccG : CreateChainGhost) :
    CreateChainEnv C ccG = (· = dhStepPairEvents C ccG.their ccG.our) := rfl

/-- Allocator event envelope for `DhStep` (`+0x500 → +0x3e4 / +0x30c`), parameterized by the
commit sub-segment envelope `s3CommitEnv`. -/
def s3EnvOf (C : Crypto)
    (s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) :
    List AllocEvent → Prop :=
  match tr.ratchet.senderChain with
  | none => (· = [])
  | some sc =>
    let evs1 := dhStepPairEvents C x.msg.senderRatchetKey sc.ratchetKey.privateKey
    match rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | .error _ => (· = evs1)
    | .ok (rk1, _) =>
      let newSk := (KeyPair.generate C (coinsOf x.rest)).privateKey
      let evs2 := dhStepPairEvents C x.msg.senderRatchetKey newSk
      match rootCreateChain C rk1 x.msg.senderRatchetKey newSk with
      | .error _ => SeqEnv (· = evs1) (· = evs2)
      | .ok _ => SeqEnv (· = evs1) (SeqEnv (· = evs2) (s3CommitEnv x trG tr))

/-- Default `s3Env` for `S3SeamPlaced` / `S3SeamTightPlaced` / `S3SeamXPlaced` / `S3SeamTightXPlaced`. -/
def s3DefaultEnv (C : Crypto) :
    TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop :=
  s3EnvOf C s3CommitDefaultEnv

theorem fitsEnv_cc1_of_s3EnvOf {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {C : Crypto}
    {s3CommitEnv : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {sc : SenderChain} (hsc : tr.ratchet.senderChain = some sc)
    (hfits : FitsEnv M lim st (s3EnvOf C s3CommitEnv x trG tr)) :
    FitsEnv M lim st
      (· = dhStepPairEvents C x.msg.senderRatchetKey sc.ratchetKey.privateKey) := by
  unfold s3EnvOf at hfits
  rw [hsc] at hfits
  dsimp only at hfits
  cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
  | error _ => rw [hcc1] at hfits; exact hfits
  | ok p1 =>
    rcases p1 with ⟨rk1, _⟩
    rw [hcc1] at hfits
    dsimp only at hfits
    cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
        (KeyPair.generate C (coinsOf x.rest)).privateKey with
    | error _ => rw [hcc2] at hfits; exact hfits.seq_left
    | ok _ => rw [hcc2] at hfits; exact hfits.seq_left

theorem onPanicTightBudget_of_spqrNoPanic {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptOnPanic C uuidTryParse spqrNoPanic x s0 sf ∗ R) :
    sf.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 sf ∗ R := by
  simp only [tryDecryptOnPanic] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htr⟩, hmem⟩ := h
  refine ⟨⟨?_, htr⟩, hmem⟩
  rcases hc with hp | hpan
  · exact model_fst_eq_panic_of_spqrNoPanic C S x hp
  · nomatch hpan

/-! ## 2. Total-Correctness Stepping Across `createChainSpecWithStack` #1 and #2 -/

/-- Total-correctness stepping from `DhStepStatePlaced` (`entry + 0x500`) across
    `RootKey::create_chain` #1 (`createChainSpecWithStack M A lim C ccStack`). -/
theorem dhStep_recv_create_chain_withStack_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {ctl : BitVec 64}
    (ccStack : Nat)
    (hstack_split : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        (stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
         stackAt sp ccStack))
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpecWithStack M A lim C ccStack))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain) (R : SepProp) (s0 s : State)
    (hsc : tr.ratchet.senderChain = some sc)
    (hrk1_ne : s0.sp - 1504#64 + 0x3b0#64 ≠ 0#64)
    (hfits1 : FitsEnv M lim st
      (· = dhStepPairEvents C x.msg.senderRatchetKey sc.ratchetKey.privateKey))
    (hs3 : DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s)
    (hcode : prog.CodeLoaded s.mem) :
    let evs1 := dhStepPairEvents C x.msg.senderRatchetKey sc.ratchetKey.privateKey
    match rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | .ok (rk1, rck) =>
      ∃ s', Steps prog s s' ∧
        DhStepAfterRecvChainStatePlaced entry A lim (M.stepEvents evs1 st) ctl
          x trG tr st1 rk1 rck R s0 s'
    | .error e =>
      ∃ s' trG' r1, Steps prog s s' ∧
        ErrTailStatePlaced entry A lim (M.stepEvents evs1 st) ctl
          x trG' { tr with ratchet := r1 } st1 e 0 R s0 s' := by
  obtain ⟨hpc, hmeta, hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩ := hs3
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hpriv_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
    sc.ratchetKey.privateKey.bytes.2
  have hrk_len : (keyToBytes32 tr.ratchet.rootKey).length = 32 := length_keyToBytes32 _
  obtain ⟨p0, hp0⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (sc.ratchetKey.privateKey.bytes.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((sc.ratchetKey.privateKey.bytes.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (sc.ratchetKey.privateKey.bytes.toList.drop 24) = v := ⟨_, rfl⟩
  obtain ⟨k0, hk0⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((keyToBytes32 tr.ratchet.rootKey).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (((keyToBytes32 tr.ratchet.rootKey).drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨k3, hk3⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((keyToBytes32 tr.ratchet.rootKey).drop 24) = v := ⟨_, rfl⟩
  have hsc_split :
      ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) =
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
       ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗ ((sp + 0x84#64) ↦₆₄ p2) ∗
       ((sp + 0x8c#64) ↦₆₄ p3) ∗ ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) := by
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_some_split sp sc trG.ratchet.senderPad,
        pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith,
        show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]
    sep_ac_rfl
  have hrk_split :
      ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0xb8#64) ↦₆₄ k0) ∗ ((sp + 0xc0#64) ↦₆₄ k1) ∗
       ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith,
        pointsTo_32_as_four_64 (sp + 0xb8#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len,
        hk0, hk1, hk2, hk3,
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith,
        show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  unfold trAt ratchetAt at hmem
  rw [hsc_split, hrk_split, split_140_for_cc1 sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3c8, u3c0, u3b8, u3b0, u3a8, u3a0, u398, u390, hmem⟩
  have hwp1 := hwp.wpp_pre_cc1 s0 s x p0 p1 p2 p3 k0 k1 k2 k3
    u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8
    hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 htrace hvregs
  have hmem_framed : s.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗ ((sp + 0xb8#64) ↦₆₄ k0) ∗
       ((sp + 0xc0#64) ↦₆₄ k1) ∗ ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3) ∗
       ((sp + 0x390#64) ↦₆₄ u390) ∗ ((sp + 0x398#64) ↦₆₄ u398) ∗ ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗
       ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗ ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u3c8)) ∗
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
        (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
          trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
         vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap
           trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗
         ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
         ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
         memRegion (sp + 0x38#64 + 172#64) 4) ∗
        vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
        ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
        ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
       memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
       memRegion (sp + 0x190#64) 72 ∗ memRegion (sp + 0x1d8#64) 0x1b8 ∗
       memRegion (sp + 0x3d0#64) 0x1b0 ∗
       tryDecryptCommonHeap (A.atState lim st s) ctl tryDecryptPlacedImg x 0 s0 ∗ R) := by
    rw [show sessionStateAt (A.atState lim st s) = sessionStateAt A.repAlloc from rfl,
        show vecAt (A.atState lim st s) 104 8 (chainAt (A.atState lim st s)) =
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) from rfl,
        show vecU8At (A.atState lim st s) = vecU8At A.repAlloc from rfl] at hmem
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem
  obtain ⟨sc1, hsteps1, hout1⟩ := hwp1.elim hmem_framed hcode
  obtain ⟨hpcc1, hrunc1, P_c1, hmem_c1, hvm_c1, hsp_c1, hx0_c1, hx1_c1, hx2_c1, hx8_c1,
    hx19_c1, hx20_c1, hx21_c1, hx22_c1, hx23_c1, hx24_c1, hx25_c1, hx26_c1, hx27_c1, hx28_c1,
    hx29_c1, hx30_c1, htrace_c1, hvregs_c1, hent_c1⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c1 : sc1.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c1, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hcl_c1 := hcl.of_keepsFrozen hsteps1.keepsFrozen
  have hmem_c1_0 := hent_c1 sc1.mem _ hmem_c1
  rw [A.atState_eq_of_vmPreserved lim st hvm_c1.symm] at hmem_c1_0
  have h74_fold : ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
       ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x74#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x74#64 + 8#64 = sp + 0x7c#64 by bv_arith,
        show sp + 0x74#64 + 16#64 = sp + 0x84#64 by bv_arith,
        show sp + 0x74#64 + 24#64 = sp + 0x8c#64 by bv_arith]
  have h390_fold : ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
      (((sp + 0x390#64) ↦₆₄ p0) ∗ ((sp + 0x398#64) ↦₆₄ p1) ∗
       ((sp + 0x3a0#64) ↦₆₄ p2) ∗ ((sp + 0x3a8#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x390#64) sc.ratchetKey.privateKey.bytes.toList hpriv_len,
        hp0, hp1, hp2, hp3,
        show sp + 0x390#64 + 8#64 = sp + 0x398#64 by bv_arith,
        show sp + 0x390#64 + 16#64 = sp + 0x3a0#64 by bv_arith,
        show sp + 0x390#64 + 24#64 = sp + 0x3a8#64 by bv_arith]
  have h3b0_fold : ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) =
      (((sp + 0x3b0#64) ↦₆₄ k0) ∗ ((sp + 0x3b8#64) ↦₆₄ k1) ∗
       ((sp + 0x3c0#64) ↦₆₄ k2) ∗ ((sp + 0x3c8#64) ↦₆₄ k3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x3b0#64) (keyToBytes32 tr.ratchet.rootKey) hrk_len,
        hk0, hk1, hk2, hk3,
        show sp + 0x3b0#64 + 8#64 = sp + 0x3b8#64 by bv_arith,
        show sp + 0x3b0#64 + 16#64 = sp + 0x3c0#64 by bv_arith,
        show sp + 0x3b0#64 + 24#64 = sp + 0x3c8#64 by bv_arith]
  have hb8_zero : ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 (0 : RootKey)) =
      (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
       ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) := by
    rw [show sp + 0x38#64 + 128#64 = sp + 0xb8#64 by bv_arith, ← pointsTo64_zero_32 (sp + 0xb8#64),
        show sp + 0xb8#64 + 8#64 = sp + 0xc0#64 by bv_arith,
        show sp + 0xb8#64 + 16#64 = sp + 0xc8#64 by bv_arith,
        show sp + 0xb8#64 + 24#64 = sp + 0xd0#64 by bv_arith]
  have htr0_fold :
      trAt A.repAlloc (sp + 0x38#64) trG
        { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } =
      (⌜∀ sc', tr.ratchet.senderChain = some sc' →
          clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
       (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
         trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap
          trG.ratchet.chainsPtr (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         (((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
          ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3)) ∗
         ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey)) ∗
        (((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
         ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64)) ∗
        ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
        ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
        memRegion (sp + 0x38#64 + 172#64) 4) ∗
       vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
       ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) := by
    unfold trAt ratchetAt
    dsimp only
    rw [hsc, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_some_split sp sc trG.ratchet.senderPad, h74_fold, hb8_zero]
  let ccG1 : CreateChainGhost :=
    { rkA := sp + 0x3b0#64
      rk := tr.ratchet.rootKey
      theirA := x.msgA + 56#64
      their := x.msg.senderRatchetKey
      ourA := sp + 0x390#64
      our := sc.ratchetKey.privateKey
      ret := sp + 0x190#64 }
  let Frame1 : SepProp :=
    sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
    trAt A.repAlloc (sp + 0x38#64) trG
      { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1d8#64) 0x1b8 ∗ memRegion (sp + 0x3d0#64) 0x1b0 ∗
    protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
    signalMessageRestAt A.repAlloc x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest 0 ∗ logOff tryDecryptPlacedImg ∗
    stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
    tryDecryptSavedRegs s0.sp s0
  have hpre_cc1 :
      sc1.mem ⊨ (createChainSpecWithStack M A lim C ccStack).pre (ccG1, st) sc1 ∗ (Frame1 ∗ R) := by
    dsimp only [createChainSpecWithStack, ccG1, Frame1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c1, hx1_c1, hx2_c1, hx8_c1, hrk1_ne, hfits1⟩, ?_⟩
    rw [htr0_fold, h390_fold, h3b0_fold, show sc1.sp = sp from hsp_c1]
    unfold tryDecryptCommonHeap at hmem_c1_0
    rw [signalMessageAt_senderRatchetKey (A.atState lim st sc1) x.msgG x.msgA x.msg,
        show protocolAddressAt (A.atState lim st sc1) = protocolAddressAt A.repAlloc from rfl,
        show signalMessageRestAt (A.atState lim st sc1) = signalMessageRestAt A.repAlloc from rfl,
        show (A.atState lim st sc1).pool = A.pool lim st sc1 from rfl,
        show s0.sp - 1504#64 = sp from rfl, hstack_split sp] at hmem_c1_0
    exact Eq.mp (congrArg (sc1.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem_c1_0
  obtain ⟨sm, hsteps_cc1, hout_cc1, _⟩ :=
    hcc.no_fault_before_outcome (ccG1, st) (Frame1 ∗ R) sc1 hpcc1 hrunc1 hpre_cc1 hsp_al_c1
      (hsteps1.codeLoaded hcode)
  have hsteps12 : Steps prog s sm := Steps.trans hsteps1 hsteps_cc1
  rcases hout_cc1 with ⟨hret_m, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, -, hpost⟩ | ⟨_, hpost⟩
  · have hpcm : sm.pc = entry + 1352#64 := hret_m.1.trans hx30_c1
    have hrunm : sm.status = .Running := hret_m.2.2
    dsimp only [createChainSpecWithStack, ccG1] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨evs, ⟨htrace_m0, henv_m⟩, hpost⟩
    have hevs_eq : evs = dhStepPairEvents C x.msg.senderRatchetKey sc.ratchetKey.privateKey := henv_m
    subst hevs_eq
    set st' := M.stepEvents (dhStepPairEvents C x.msg.senderRatchetKey sc.ratchetKey.privateKey) st
    have hcl_m := hcl_c1.of_keepsFrozen hsteps_cc1.keepsFrozen
    have htrace_m : sm.trace = s0.trace := htrace_m0.trans htrace_c1
    have hsp_m : sm.sp = s0.sp - 1504#64 := hspm.trans hsp_c1
    have hsp_al_m : sm.spAligned = true := by
      unfold State.spAligned at hsp_al_c1 ⊢; rw [hspm]; exact hsp_al_c1
    have hx19_m : sm.readReg64 .x19 = x.ret := hcsm.1.trans hx19_c1
    have hx20_m : sm.readReg64 .x20 = sp + 0x140#64 := hcsm.2.1.trans hx20_c1
    have hx21_m : sm.readReg64 .x21 = x.ss := hcsm.2.2.1.trans hx21_c1
    have hx22_m : sm.readReg64 .x22 = x.msgA := hcsm.2.2.2.1.trans hx22_c1
    have hx23_m : sm.readReg64 .x23 = sp + 0x500#64 := hcsm.2.2.2.2.1.trans hx23_c1
    have hx24_m : (sm.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
      rw [hcsm.2.2.2.2.2.1]; exact hx24_c1
    have hx25_m : sm.readReg64 .x25 = sp + 0x190#64 := hcsm.2.2.2.2.2.2.1.trans hx25_c1
    have hx26_m : sm.readReg64 .x26 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.1.trans hx26_c1
    have hx27_m : sm.readReg64 .x27 = sp + 0x38#64 := hcsm.2.2.2.2.2.2.2.2.1.trans hx27_c1
    have hx28_m : sm.readReg64 .x28 = sp + 0x2c0#64 := hcsm.2.2.2.2.2.2.2.2.2.1.trans hx28_c1
    have hx29_m : sm.readReg64 .x29 = s0.sp - 96#64 := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c1
    have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
      ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl_m, by reg_chain⟩
    have hpost_grouped : sm.mem ⊨
        (memRegion (sp + 0x1d8#64) 0x1b8 ∗
         ((sp + 0x390#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
         ((sp + 0x3b0#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
         memRegion (sp + 0x3d0#64) 0x1b0) ∗
        (memRegion (sp + 0x140#64) 0x50 ∗
         createChainResultAt (sp + 0x190#64)
           (rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey) ∗
         sessionStateAt (A.atState lim st' sm) x.ss x.G.afterTrFrom st1 ∗
         trAt (A.atState lim st' sm) (sp + 0x38#64) trG
           { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
         memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
         ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
         ((sp + 0x30#64) ↦₆₄ x.remA) ∗
         tryDecryptCommonHeap (A.atState lim st' sm) ctl tryDecryptPlacedImg x 0 s0 ∗ R) := by
      dsimp only [Frame1] at hpost
      rw [show sc1.sp = sp from hsp_c1] at hpost
      unfold tryDecryptCommonHeap
      rw [signalMessageAt_senderRatchetKey (A.atState lim st' sm) x.msgG x.msgA x.msg,
          show sessionStateAt (A.atState lim st' sm) = sessionStateAt A.repAlloc from rfl,
          show trAt (A.atState lim st' sm) = trAt A.repAlloc from rfl,
          show protocolAddressAt (A.atState lim st' sm) = protocolAddressAt A.repAlloc from rfl,
          show signalMessageRestAt (A.atState lim st' sm) = signalMessageRestAt A.repAlloc from rfl,
          show (A.atState lim st' sm).pool = A.pool lim st' sm from rfl,
          show s0.sp - 1504#64 = sp from rfl, hstack_split sp]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hpost
    have hpost_folded :=
      Satisfies.mono (sepConj_mono_left (fold_390_3b0_to_memRegion sp _ _ hpriv_len hrk_len))
        hpost_grouped
    dsimp only
    unfold rootCreateChain at hpost_folded ⊢
    cases hcc1 : createChain C.F C.X tr.ratchet.rootKey
        x.msg.senderRatchetKey.bytes sc.ratchetKey.privateKey.bytes with
    | none =>
      rw [hcc1] at hpost_folded
      dsimp only [hcc1] at hpost_folded ⊢
      let Rest_err : SepProp :=
        sessionStateAt (A.atState lim st' sm) x.ss x.G.afterTrFrom st1 ∗
        trAt (A.atState lim st' sm) (sp + 0x38#64) trG
          { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗
        tryDecryptCommonHeap (A.atState lim st' sm) ctl tryDecryptPlacedImg x 0 s0 ∗ R
      have hmem_err : sm.mem ⊨
          memRegion (sp + 0x140#64) 0x50 ∗
          createChainResultAt (sp + 0x190#64) (.error .invalidKeyAgreement) ∗
          memRegion (sp + 0x1d8#64) 0x3a8 ∗ Rest_err :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_err, sp]; sep_ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
        dhStep_cc1_err_branch_vm_placed (A := A.atState lim st' sm) hwp Rest_err s0 sm
          hpcm hmeta_m hx20_m hx23_m hx25_m hx26_m hmem_err (hsteps12.codeLoaded hcode)
      refine ⟨s', trG, { tr.ratchet with rootKey := (0 : RootKey) },
        Steps.trans hsteps12 hsteps2, ?_⟩
      refine ⟨hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s', ?_⟩
      dsimp only [Rest_err] at hmems'
      rw [A.atState_eq_of_vmPreserved lim st' hvm2.symm] at hmems'
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
           tryDecryptCommonHeap (A.atState lim st' s') ctl tryDecryptPlacedImg x 0 s0 ∗ R) :=
        Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp] at hmems' ⊢; sep_ac_rfl)) hmems'
      have hmems2 := Satisfies.mono (sepConj_mono_left hsp38_ent) hmems1
      dsimp only [sp] at hmems2 ⊢
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by sep_ac_rfl)) hmems2
    | some p1 =>
      rcases p1 with ⟨rk1, rckKey⟩
      rw [hcc1] at hpost_folded
      dsimp only [hcc1] at hpost_folded ⊢
      let Rest_ok : SepProp :=
        sessionStateAt (A.atState lim st' sm) x.ss x.G.afterTrFrom st1 ∗
        trAt (A.atState lim st' sm) (sp + 0x38#64) trG
          { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50 ∗
        memRegion (sp + 0x1d8#64) 0x3a8 ∗
        tryDecryptCommonHeap (A.atState lim st' sm) ctl tryDecryptPlacedImg x 0 s0 ∗ R
      have hmem_ok : sm.mem ⊨
          createChainResultAt (sp + 0x190#64) (.ok (rk1, ⟨rckKey, 0⟩)) ∗ Rest_ok :=
        Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [Rest_ok, sp]; sep_ac_rfl)) hpost_folded
      obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hcss', hmems'⟩ :=
        dhStep_cc1_ok_branch_vm_placed hwp rk1 ⟨rckKey, 0⟩ Rest_ok s0 sm
          hpcm hmeta_m hx25_m hmem_ok (hsteps12.codeLoaded hcode)
      refine ⟨s', Steps.trans hsteps12 hsteps2, ?_⟩
      refine ⟨hpcs', hmetas',
        hcss'.1.trans hx19_m, hcss'.2.1.trans hx20_m, hcss'.2.2.1.trans hx21_m,
        hcss'.2.2.2.1.trans hx22_m, hcss'.2.2.2.2.1.trans hx23_m,
        by rw [hcss'.2.2.2.2.2.1]; exact hx24_m,
        hcss'.2.2.2.2.2.2.1.trans hx25_m, hcss'.2.2.2.2.2.2.2.1.trans hx26_m,
        hcss'.2.2.2.2.2.2.2.2.1.trans hx27_m, hcss'.2.2.2.2.2.2.2.2.2.1.trans hx28_m, ?_⟩
      dsimp only [Rest_ok, sp] at hmems' ⊢
      rw [A.atState_eq_of_vmPreserved lim st' hvm2.symm] at hmems'
      exact Eq.mp (congrArg (s'.mem ⊨ ·) (by sep_ac_rfl)) hmems'
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Total-correctness stepping from `DhStepAfterRecvChainStatePlaced` (`entry + 0x70c`) through
    keygen and `RootKey::create_chain` #2 (`createChainSpecWithStack M A lim C ccStack`). -/
theorem dhStep_keygen_and_send_create_chain_withStack_placed [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {ctl : BitVec 64}
    (ccStack : Nat)
    (hstack_split : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        (stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
         stackAt sp ccStack))
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hcc : subroutine_ok prog (lsmpl.base 40) (createChainSpecWithStack M A lim C ccStack))
    (hdpk : subroutine_ok prog (lsmpl.base 200) (derivePublicKeyBytesBudgetSpec C.pubKey))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey)
    (R : SepProp) (s0 s : State)
    (hrng : subroutine_ok prog rngFillEntry (rngFillAtBudgetSpec ctl x.cur x.rest))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hrk2_ne : s0.sp - 1504#64 + 0x4a0#64 ≠ 0#64)
    (hfits2 : FitsEnv M lim st
      (· = dhStepPairEvents C x.msg.senderRatchetKey
        (KeyPair.generate C (coinsOf x.rest)).privateKey))
    (hafter : DhStepAfterRecvChainStatePlaced entry A lim st ctl x trG tr st1 rk1 rck R s0 s)
    (hcode : prog.CodeLoaded s.mem) :
    let newSenderKey := KeyPair.generate C (coinsOf x.rest)
    let evs2 := dhStepPairEvents C x.msg.senderRatchetKey newSenderKey.privateKey
    match rootCreateChain C rk1 x.msg.senderRatchetKey newSenderKey.privateKey with
    | .ok (finalRootKey, senderChainKey) =>
      ∃ s', Steps prog s s' ∧
        DhCommitStatePlaced entry A lim (M.stepEvents evs2 st) ctl
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
    dhStep_after_cc1_to_cc2_call_vm_placed hwp hdpk x trG tr st1 rk1 rck R s0 s
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
    tapeAfter ctl x.cur x.rest draws ∗ logOff tryDecryptPlacedImg ∗
    stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
    tryDecryptSavedRegs s0.sp s0
  have hpre_cc2 :
      s5.mem ⊨ (createChainSpecWithStack M A lim C ccStack).pre (ccG2, st) s5 ∗ (Frame2 ∗ R) := by
    dsimp only [createChainSpecWithStack, ccG2, Frame2]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_5, hx1_5, hx2_5, hx8_5, hrk2_ne, hfits2⟩, ?_⟩
    rw [show s5.sp = sp from hsp5]
    unfold tryDecryptCommonHeap at hmem5
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
        tryDecryptCommonHeap (A.atState lim st' sm) ctl tryDecryptPlacedImg x draws s0 ∗ R := by
      dsimp only [Frame2] at hpost
      rw [show s5.sp = sp from hsp5] at hpost
      unfold tryDecryptCommonHeap
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
           tryDecryptCommonHeap (A.atState lim st' sm) ctl tryDecryptPlacedImg x draws s0 ∗ R) :=
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
        tryDecryptCommonHeap (A.atState lim st' sm) ctl tryDecryptPlacedImg x draws s0 ∗ R
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
           tryDecryptCommonHeap (A.atState lim st' s') ctl tryDecryptPlacedImg x draws s0 ∗ R) :=
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
           tryDecryptCommonHeap (A.atState lim st' s') ctl tryDecryptPlacedImg x draws s0 ∗ R) :=
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
           tryDecryptCommonHeap (A.atState lim st' sm) ctl tryDecryptPlacedImg x draws s0 ∗ R) :=
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
        tryDecryptCommonHeap (A.atState lim st' sm) ctl tryDecryptPlacedImg x draws s0 ∗ R
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


end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
