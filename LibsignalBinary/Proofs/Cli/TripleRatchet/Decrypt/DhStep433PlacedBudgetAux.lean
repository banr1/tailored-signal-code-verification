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
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import ProofLib.RegChain

/-!
# Budget-Threaded Segment S3 (`DhStep`) Auxiliary Steppers

Auxiliary `VmPreserved` steppers for `DhStep433PlacedBudget`: `coinsFill` budget specs,
`withLsCodeRoLoaded` adapters, missing-sender-chain error handling, key generation, and the
receiving `RootKey::create_chain` step.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux

open Arm64 ProofLib
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  DhStepStatePlaced ErrTailStatePlaced
)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair RootKey SenderChain SessionState TripleRatchet rootCreateChain
)
open CryptoGames.Ratchet (clampScalar createChain keyToBytesVec32)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep (
  cliTryDecryptCommonHeapPlaced_split_tape
)
open CryptoVerification.LibsignalSessionRepr (
  chainAt chainKeyBytes length_keyToBytes32 msgTypeByte optSenderChainBytes ratchetAt
)
open CryptoVerification.LibsignalTripleRatchet (
  CreateChainGhost DerivePublicKeyBytesCall LibsignalCodeRoLoaded TrGhost TryDecryptGhost
  createChainResultAt derivePublicKeyBytesSpec trAt withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  speBodyAt tryDecryptMidMetaPlaced tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (
  fold_32_four_64 fold_390_3b0_to_memRegion keyVec_coinsOf_toList
  optSenderChainBytes_none_pointsTo32 optSenderChainBytes_some_split pointsTo64_zero_32
  pointsTo_32_as_four_64 signalMessageAt_senderRatchetKey signalMessageRestAt
  split_140_for_cc1 split_190_4e0_for_cc2 split_32_four_64 split_400_500_for_keygen
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  coinsOf invalidSessionStructureStr issStr_lengths protocolAddressAt sessionStateAt
  signalMessageAt strRefAt utf8
)
open CryptoVerification.RustHeap (RustAlloc vecAt vecU8At)
open CryptoVerification.SignalSession.Coins (
  coinsAfterPlaced coinsFillAtSpecPlaced coinsFillSpecPlaced
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux (
  dhStep_cc1_err_branch_vm_placed dhStep_cc1_ok_branch_vm_placed
  dhStep_err_tail_from_2dc_vm_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (dhStepPairEvents)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps (
  dhStep_step_70c_to_778_vm_placed dhStep_step_780_to_7a8_vm_placed
  dhStep_step_7b4_to_7d4_vm_placed lsStaticDropSym zeroizeSecretBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (DhStepBlockVmWp)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpecWithStack)

/-! ## Coins Budget Specs, `withLsCodeRoLoaded` Adapters, and Intermediate State -/

theorem add_lscro_pre [LibsignalPlacement] {α : Type} {spec : Spec α} {x : α}
    {R : SepProp} {s : State} (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ R := by
  dsimp only [withLsCodeRoLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

theorem subroutine_ok_withLsCodeRoLoaded_vm_of_derivePublicKeyBytes
    [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {pubKey : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec pubKey))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (withVmPreserved (derivePublicKeyBytesSpec pubKey))) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCodeRoLoaded, derivePublicKeyBytesBudgetSpec, withVmPreserved, derivePublicKeyBytesSpec] at hq ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.2, hq.1.1, hq.2⟩)

/-- `VmPreserved`-strengthened `coinsFillSpecPlaced` for CLI S3 (`DhStep`) budget threading. -/
abbrev coinsFillBudgetSpecPlaced [LibsignalPlacement] (stk : Nat) :
    Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved (coinsFillSpecPlaced stk)

/-- `VmPreserved`-strengthened `coinsFillAtSpecPlaced` with fixed tape ghost `(cur, rest)`. -/
abbrev coinsFillAtBudgetSpecPlaced [LibsignalPlacement] (stk : Nat)
    (cur : BitVec 64) (rest : List (BitVec 8)) : Spec (BitVec 64 × Nat) :=
  withVmPreserved (coinsFillAtSpecPlaced stk cur rest)

theorem coinsFillAtBudgetPlaced_of_after0 [LibsignalPlacement] {P : Program}
    {addr cur : BitVec 64} {stk : Nat} {rest : List (BitVec 8)}
    (h : subroutine_ok P addr (coinsFillBudgetSpecPlaced stk)) :
    subroutine_ok P addr (coinsFillAtBudgetSpecPlaced stk cur rest) :=
  subroutine_ok_outcome_intro fun (dst, len) R s0 hpc hrun hpre hsp =>
    h.mono_outcome (dst, len, cur, rest) R s0 hpc hrun hpre hsp fun _ hout => hout

theorem coinsFillAtBudgetPlaced_of_after0_cl [LibsignalPlacement] {P : Program}
    {addr cur : BitVec 64} {stk : Nat} {rest : List (BitVec 8)}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (coinsFillBudgetSpecPlaced stk))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (coinsFillAtBudgetSpecPlaced stk cur rest)) :=
  subroutine_ok_outcome_intro fun (dst, len) R s0 hpc hrun hpre hsp =>
    h.mono_outcome (dst, len, cur, rest) R s0 hpc hrun hpre hsp fun _ hout => hout

theorem coinsFillAtBudgetPlaced_of_after0_cro [LibsignalPlacement] {P : Program}
    {addr cur : BitVec 64} {stk : Nat} {rest : List (BitVec 8)}
    (h : subroutine_ok P addr (withLsCodeRoLoaded lsmpl (coinsFillBudgetSpecPlaced stk))) :
    subroutine_ok P addr (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced stk cur rest)) :=
  subroutine_ok_outcome_intro fun (dst, len) R s0 hpc hrun hpre hsp =>
    h.mono_outcome (dst, len, cur, rest) R s0 hpc hrun hpre hsp fun _ hout => hout

/-- Budget-threaded CLI intermediate state at `entry + 0x70c#64` after `create_chain` #1 succeeds. -/
abbrev CliDhStepAfterRecvChainStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.CliDhStepAfterRecvChainStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 rk1 rck R s0 s

/-! ## `VmPreserved` and Receiving `create_chain` Steppers -/

theorem dhStep_missing_sender_chain_vm_placed_cli [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {A : RustAlloc} {ctl : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hnone : tr.ratchet.senderChain = none)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepStatePlaced entry A ctl x trG tr st1 R s0 s)
    (hcode : prog.CodeLoaded s.mem) :
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStatePlaced entry A ctl x trG tr st1 (.invalidSessionStructure .missingSenderChain) 0 R s0 s' := by
  obtain ⟨hpc, hmeta, hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩ := hs3
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64 with hsp_def
  have hsc_tag : ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) =
      (((sp + 0x50#64) ↦₃₂ 0#32) ∗ ((sp + 0x54#64) ↦ₛ trG.ratchet.senderPad)) := by
    rw [hnone, show sp + 0x38#64 + 24#64 = sp + 0x50#64 by bv_arith,
        optSenderChainBytes_none_pointsTo32 (sp + 0x50#64) trG.ratchet.senderPad,
        show sp + 0x50#64 + 4#64 = sp + 0x54#64 by bv_arith]
  have h2c0_split : memRegion (sp + 0x140#64) 0x440 =
      memRegion (sp + 0x140#64) 0x180 ∗ (∃∗ u2c0 : BitVec 64, (sp + 0x2c0#64) ↦₆₄ u2c0) ∗
      (∃∗ u2c8 : BitVec 64, (sp + 0x2c8#64) ↦₆₄ u2c8) ∗ memRegion (sp + 0x2d0#64) 0x2b0 := by
    rw [memRegion_split' (b := sp + 0x140#64) (b' := sp + 0x2c0#64) (n := 0x180) (k := 0x2c0) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2c0#64) (b' := sp + 0x2c8#64) (n := 0x8) (k := 0x2b8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := sp + 0x2c8#64) (b' := sp + 0x2d0#64) (n := 0x8) (k := 0x2b0) rfl (by bv_arith) (by decide),
        memRegion_eight (sp + 0x2c0#64), memRegion_eight (sp + 0x2c8#64)]
  unfold trAt ratchetAt at hmem
  rw [hsc_tag, h2c0_split] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u2c8, u2c0, hmem⟩
  have hwp1 := hwp.wpp_missing_sc s0 s x u2c0 u2c8 hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx25 hx27 hx28 htrace hvregs
  have hmem_framed : s.mem ⊨
      (((sp + 0x50#64) ↦₃₂ 0#32) ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ u2c8)) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       (⌜∀ sc, tr.ratchet.senderChain = some sc →
          clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
        (⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
          trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
         vecAt A 104 8 (chainAt A) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
           (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
         ((sp + 0x54#64) ↦ₛ trG.ratchet.senderPad) ∗
         ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
         ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
         ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
         memRegion (sp + 0x38#64 + 172#64) 4) ∗
        vecU8At A (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
        ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
        ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)) ∗
       memRegion x.ret 48 ∗ memRegion (sp + 0x140#64) 0x180 ∗ memRegion (sp + 0x2d0#64) 0x2b0 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem
  obtain ⟨sm, hsteps1, hout⟩ := hwp1.elim hmem_framed hcode
  obtain ⟨hpcm, hrunm, P_m, hmem_m, hvmm, hsp_m, hx29_m, hx12_m, hx19_m, hx20_m, hx25_m, hx26_m, htrace_m, hvregs_m, hent_m⟩ :=
    hout.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_m : sm.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢; rw [hsp_m, ← show s.sp = s0.sp - 1504#64 from hsp]; exact hsp_al
  have hmeta_m : tryDecryptMidMetaPlaced s0 sm :=
    ⟨hrunm, hsp_m, hsp0_al, hsp_al_m, hx29_m, htrace_m, hcl.of_keepsFrozen hsteps1.keepsFrozen, hvregs_m⟩
  have hmem_m0 := hent_m sm.mem _ hmem_m
  have hmem_m' : sm.mem ⊨ memRegion (sp + 0x140#64) 0x180 ∗
      ((sp + 0x2c0#64) ↦₆₄ hwp.missingScAddr) ∗ ((sp + 0x2c8#64) ↦₆₄ 20#64) ∗
      memRegion (sp + 0x2d0#64) 0x2b0 ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    unfold trAt ratchetAt; rw [hsc_tag]
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem_m0
  obtain ⟨s', hsteps2, hvm2, hpcs', hmetas', hx19s', hx20s', hx26s', hmems'⟩ :=
    dhStep_err_tail_from_2dc_vm_placed hwp hwp.missingScAddr 20#64
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R)
      s0 sm hpcm hmeta_m hx12_m hx20_m hx25_m hmem_m' (hsteps1.codeLoaded hcode)
  refine ⟨s', Steps.trans hsteps1 hsteps2, hvmm.trans hvm2, hpcs', hmetas', hx19s'.trans hx19_m, hx20s', hx26s'.trans hx26_m, ?_⟩
  dsimp only [speBodyAt]; unfold strRefAt
  have hro : s'.mem ⊨ (hwp.missingScAddr ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗
      (memRegion (sp + 0x140#64) 0x28 ∗ ((sp + 0x168#64) ↦₆₄ hwp.missingScAddr) ∗
       ((sp + 0x170#64) ↦₆₄ 20#64) ∗ memRegion (sp + 0x178#64) 24 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
       (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG tr ∗
        memRegion x.ret 48 ∗ memRegion sp 0x38 ∗ CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R)) :=
    hwp.hro_missingSc hmetas'.2.2.2.2.2.2.1.2 hmems'
  have hlen : BitVec.ofNat 64 (invalidSessionStructureStr .missingSenderChain).length = 20#64 := by rw [issStr_lengths.1]
  rw [hlen, show sp + 0x168#64 + 8#64 = sp + 0x170#64 by bv_arith,
      show sp + 0x168#64 + 16#64 = sp + 0x178#64 by bv_arith]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨hwp.missingScAddr, ?_⟩
  dsimp only [sp] at hro ⊢
  exact Eq.mp (congrArg (s'.mem ⊨ ·) (by sep_ac_rfl)) hro

theorem dhStep_step_778_to_780_coins_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (cur : BitVec 64) (rest : List (BitVec 8)) (Rest : SepProp) (s0 s : State)
    (hrng : subroutine_ok prog rngFillEntry
      (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)))
    (hpc : s.pc = entry + 1912#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx0 : s.readReg64 .x0 = s0.sp - 1504#64 + 0x190#64)
    (hx1 : s.readReg64 .x1 = 32#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hv0 : s.readVReg128 0#5 = 0#128)
    (hmem : s.mem ⊨
      memRegion (s0.sp - 1504#64 + 0x190#64) 0x20 ∗
      coinsAfterPlaced cur rest 0 ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧
      VmPreserved s s' ∧
      s'.pc = entry + 1920#64 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        ((sp + 0x190#64) ↦ₛ (keyToBytesVec32 (coinsOf rest)).toList) ∗
        coinsAfterPlaced cur rest (min 32 rest.length) ∗
        stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  rw [split_32_four_64 (sp + 0x190#64)] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3, u2, u1, u0, hmem⟩
  have hwp1 := hwp.wpp_778_to_rng s0 s u0 u1 u2 u3 hpc hrun hsp hsp_al hx0 hx1 hx25 hv0 htrace
  have hmem_in : s.mem ⊨
      (((sp + 0x190#64) ↦₆₄ u0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ u1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ u3)) ∗
      (coinsAfterPlaced cur rest 0 ∗ stackAt sp tryDecryptSubStack ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hmem
  obtain ⟨sc, hsteps1, hout1⟩ := hwp1.elim hmem_in hcode
  obtain ⟨hpcc, hrunc, P_c, hmem_c, hvm1, hsp_c, hx0_c, hx1_c, hx30_c, hcs_c, htrace_c, hent_c⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c : sc.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmem_c0 := hent_c sc.mem _ hmem_c
  have hmem_c1 := Satisfies.mono (sepConj_mono_left (fold_32_four_64 (sp + 0x190#64) 0#64 0#64 0#64 0#64)) hmem_c0
  have hpre_rng : sc.mem ⊨
      (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack cur rest)).pre
        (sp + 0x190#64, 32) sc ∗ Rest := by
    refine add_lscro_pre (hcl.of_keepsFrozen hsteps1.keepsFrozen) ?_
    dsimp only [coinsFillAtBudgetSpecPlaced, withVmPreserved, coinsFillAtSpecPlaced]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c, by rw [hx1_c]; rfl⟩, ?_⟩
    rw [show sc.sp = sp from hsp_c]
    exact Eq.mp (congrArg (sc.mem ⊨ ·) (by sep_ac_rfl)) hmem_c1
  obtain ⟨s', hsteps2, ⟨hret', hpres', hpost'⟩ | ⟨_, hpost'⟩ | ⟨_, -, hpost'⟩ | ⟨_, hpost'⟩, -⟩ :=
    hrng.no_fault_before_outcome (sp + 0x190#64, 32) Rest sc hpcc hrunc hpre_rng hsp_al_c
      (hsteps1.codeLoaded hcode)
  · have hsteps12 := Steps.trans hsteps1 hsteps2
    dsimp only [withLsCodeRoLoaded, coinsFillAtBudgetSpecPlaced, withVmPreserved, coinsFillAtSpecPlaced] at hpost'
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hvm2, htrace_s', hpost'⟩
    rw [← keyVec_coinsOf_toList rest, show sc.sp = sp from hsp_c] at hpost'
    have hcs' : CalleeSavedPreserved s s' := CalleeSavedPreserved.trans hcs_c hpres'.2
    have hsp' : s'.sp = sp := hpres'.1.trans hsp_c
    have hsp_al' : s'.spAligned = true := by
      unfold State.spAligned at hsp_al_c ⊢
      rw [hpres'.1]
      exact hsp_al_c
    have hx29' : s'.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
    have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
      ⟨hret'.2.2, hsp', hsp0_al, hsp_al', hx29', htrace_s'.trans htrace_c,
       hcl.of_keepsFrozen hsteps12.keepsFrozen, by reg_chain⟩
    exact ⟨s', hsteps12, hvm1.trans hvm2, hret'.1.trans hx30_c, hmeta', hcs',
      Eq.mp (congrArg (s'.mem ⊨ ·) (by sep_ac_rfl)) hpost'⟩
  · dsimp only [withLsCodeRoLoaded, coinsFillAtBudgetSpecPlaced, withVmPreserved, coinsFillAtSpecPlaced] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [withLsCodeRoLoaded, coinsFillAtBudgetSpecPlaced, withVmPreserved, coinsFillAtSpecPlaced] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [withLsCodeRoLoaded, coinsFillAtBudgetSpecPlaced, withVmPreserved, coinsFillAtSpecPlaced] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1

theorem dhStep_step_7a8_to_7b4_cro_vm_placed [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hdpk : subroutine_ok prog (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (sec : List.Vector (BitVec 8) 32) (Rest : SepProp) (s0 s : State)
    (hpc : s.pc = entry + 1960#64)
    (hmeta : tryDecryptMidMetaPlaced s0 s)
    (hx0 : s.readReg64 .x0 = s0.sp - 1504#64 + 0x500#64)
    (hx8 : s.readReg64 .x8 = s0.sp - 1504#64 + 0x400#64)
    (hx23 : s.readReg64 .x23 = s0.sp - 1504#64 + 0x500#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 1504#64 + 0x190#64)
    (hmem : s.mem ⊨
      ((s0.sp - 1504#64 + 0x190#64) ↦ₛ sec.toList) ∗
      memRegion (s0.sp - 1504#64 + 0x400#64) 32 ∗
      memRegion (s0.sp - 1504#64 + 0x500#64) 32 ∗ Rest)
    (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64
    ∃ s', Steps prog s s' ∧ VmPreserved s s' ∧
      s'.pc = entry + 1972#64 ∧
      tryDecryptMidMetaPlaced s0 s' ∧
      CalleeSavedPreserved s s' ∧
      (s'.mem ⊨
        memRegion (sp + 0x190#64) 32 ∗
        ((sp + 0x400#64) ↦ₛ (C.pubKey sec).toList) ∗
        ((sp + 0x500#64) ↦ₛ sec.toList) ∗ Rest) := by
  obtain ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩ := hmeta
  set sp := s0.sp - 1504#64
  have hsec_len : sec.toList.length = 32 := sec.2
  obtain ⟨p0, hp0⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (sec.toList.take 8) = v := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((sec.toList.drop 8).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 ((sec.toList.drop 16).take 8) = v := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ v, CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.pack64 (sec.toList.drop 24) = v := ⟨_, rfl⟩
  have h190_split : ((sp + 0x190#64) ↦ₛ sec.toList) =
      (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x190#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  have h500_fold : ((sp + 0x500#64) ↦ₛ sec.toList) =
      (((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) := by
    rw [pointsTo_32_as_four_64 (sp + 0x500#64) sec.toList hsec_len, hp0, hp1, hp2, hp3]
  rw [h190_split, split_32_four_64 (sp + 0x500#64)] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨u3, u2, u1, u0, hmem⟩
  have hwp1 := hwp.wpp_7a8_to_dpk s0 s p0 p1 p2 p3 u0 u1 u2 u3 hpc hrun hsp hsp_al hx0 hx8 hx23 hx25 htrace
  have hmem_in : s.mem ⊨
      (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3) ∗
       ((sp + 0x500#64) ↦₆₄ u0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ u1) ∗
       ((sp + 0x500#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ u3)) ∗
      (memRegion (sp + 0x400#64) 32 ∗ Rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem
  obtain ⟨sc, hsteps1, hout1⟩ := hwp1.elim hmem_in hcode
  obtain ⟨hpcc, hrunc, P_c, hmem_c, hvm1, hsp_c, hx0_c, hx8_c, hx30_c, hcs_c, htrace_c, hent_c⟩ :=
    hout1.resolve_right fun ⟨_, hoom⟩ => not_satisfies_false_sepConj hoom
  have hsp_al_c : sc.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_c, ← show s.sp = s0.sp - 1504#64 from hsp]
    exact hsp_al
  have hmem_c0 := hent_c sc.mem _ hmem_c
  have hmem_c1 : sc.mem ⊨
      (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
       ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3)) ∗
      (((sp + 0x500#64) ↦ₛ sec.toList) ∗ memRegion (sp + 0x400#64) 32 ∗ Rest) := by
    rw [h500_fold]
    exact Eq.mp (congrArg (sc.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem_c0
  have hmem_c2 := Satisfies.mono (sepConj_mono_left (fold_32_four_64 (sp + 0x190#64) p0 p1 p2 p3)) hmem_c1
  have hdpk_vm := subroutine_ok_withLsCodeRoLoaded_vm_of_derivePublicKeyBytes hdpk
  let dpkG : DerivePublicKeyBytesCall := { secret := sp + 0x500#64, sec := sec, out := sp + 0x400#64 }
  have hpre_dpk : sc.mem ⊨
      (withLsCodeRoLoaded lsmpl (withVmPreserved (derivePublicKeyBytesSpec C.pubKey))).pre dpkG sc ∗
        (memRegion (sp + 0x190#64) 32 ∗ Rest) := by
    refine add_lscro_pre (hcl.of_keepsFrozen hsteps1.keepsFrozen) ?_
    dsimp only [withVmPreserved, derivePublicKeyBytesSpec, dpkG]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c, hx8_c⟩, Eq.mp (congrArg (sc.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem_c2⟩
  obtain ⟨s', hsteps2, ⟨hret', hpres', hpost'⟩ | ⟨_, hpost'⟩ | ⟨_, -, hpost'⟩ | ⟨_, hpost'⟩, -⟩ :=
    hdpk_vm.no_fault_before_outcome dpkG (memRegion (sp + 0x190#64) 32 ∗ Rest) sc hpcc hrunc hpre_dpk hsp_al_c
      (hsteps1.codeLoaded hcode)
  · have hsteps12 := Steps.trans hsteps1 hsteps2
    dsimp only [withVmPreserved, derivePublicKeyBytesSpec, dpkG] at hpost'
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hvm2, htrace_s', hpost'⟩
    have hcs' : CalleeSavedPreserved s s' := CalleeSavedPreserved.trans hcs_c hpres'.2
    have hsp' : s'.sp = sp := hpres'.1.trans hsp_c
    have hsp_al' : s'.spAligned = true := by
      unfold State.spAligned at hsp_al_c ⊢
      rw [hpres'.1]
      exact hsp_al_c
    have hx29' : s'.readReg64 .x29 = s0.sp - 96#64 := by reg_chain
    have hmeta' : tryDecryptMidMetaPlaced s0 s' :=
      ⟨hret'.2.2, hsp', hsp0_al, hsp_al', hx29', htrace_s'.trans htrace_c,
       hcl.of_keepsFrozen hsteps12.keepsFrozen, by reg_chain⟩
    exact ⟨s', hsteps12, hvm1.trans hvm2, hret'.1.trans hx30_c, hmeta', hcs',
      Eq.mp (congrArg (s'.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hpost'⟩
  · dsimp only [withVmPreserved, derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [withVmPreserved, derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1
  · dsimp only [withVmPreserved, derivePublicKeyBytesSpec] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    exact False.elim hpost'.1

theorem dhStep_after_cc1_to_cc2_call_vm_placed_cli [LibsignalPlacement]
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hdpk : subroutine_ok prog (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec C.pubKey)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (rk1 : RootKey) (rck : ChainKey) (R : SepProp) (s0 s : State)
    (hrng : subroutine_ok prog rngFillEntry
      (withLsCodeRoLoaded lsmpl (coinsFillAtBudgetSpecPlaced tryDecryptSubStack x.cur x.rest)))
    (hsd : subroutine_ok prog (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec)
    (hafter : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.CliDhStepAfterRecvChainStatePlaced entry A ctl x trG tr st1 rk1 rck R s0 s) (hcode : prog.CodeLoaded s.mem) :
    let sp := s0.sp - 1504#64; let draws := min 32 x.rest.length; let newSenderKey := KeyPair.generate C (coinsOf x.rest)
    ∃ s5, Steps prog s s5 ∧ VmPreserved s s5 ∧ s5.pc = lsmpl.base 40 ∧ tryDecryptMidMetaPlaced s0 s5 ∧
      s5.readReg64 .x0 = sp + 0x4a0#64 ∧ s5.readReg64 .x1 = x.msgA + 56#64 ∧
      s5.readReg64 .x2 = sp + 0x420#64 ∧ s5.readReg64 .x8 = sp + 0x190#64 ∧
      s5.readReg64 .x19 = x.ret ∧ s5.readReg64 .x20 = sp + 0x140#64 ∧ s5.readReg64 .x21 = x.ss ∧ s5.readReg64 .x22 = x.msgA ∧
      s5.readReg64 .x23 = sp + 0x500#64 ∧ s5.readReg64 .x25 = sp + 0x190#64 ∧ s5.readReg64 .x26 = sp + 0x2c0#64 ∧ s5.readReg64 .x27 = sp + 0x38#64 ∧
      s5.readReg64 .x28 = sp + 0x3d0#64 ∧ s5.readReg64 .x30 = entry + 2008#64 ∧
      ∃ (msgW : BitVec 32), msgW.setWidth 8 = msgTypeByte x.msgType ∧
        (s5.mem ⊨ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
          memRegion x.ret 48 ∗ memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗ memRegion (sp + 0x14#64) 8 ∗
          ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x190#64) 72 ∗ memRegion (sp + 0x1d8#64) 0x1f8 ∗
          ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗
          ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗ ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x440#64) 0x60 ∗
          ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
          ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0xa0 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) := by
  obtain ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hmem⟩ := hafter
  set sp := s0.sp - 1504#64; set draws := min 32 x.rest.length; set newSenderKey := KeyPair.generate C (coinsOf x.rest)
  set msgW : BitVec 32 := (s.readReg64 .x24).setWidth 32
  have hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType := (by dsimp only [msgW]; bv_kernel : msgW.setWidth 8 = (s.readReg64 .x24).setWidth 8).trans hx24
  let BaseRest : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := (0 : RootKey) } } ∗
    memRegion x.ret 48 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x50
  have hmem0 : s.mem ⊨ memRegion sp 0x20 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ ((sp + 0x194#64) ↦ₛ keyToBytes32 rk1) ∗
      ((sp + 0x1b4#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x1d8#64) 0x3a8 ∗ (BaseRest ∗ CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [BaseRest, sp]; sep_ac_rfl)) hmem
  obtain ⟨s1, hsteps1, hvm1, hpc1, hmeta1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hv0_1, hmem1⟩ :=
    dhStep_step_70c_to_778_vm_placed hwp rk1 rck (BaseRest ∗ CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R)
      s0 s hpc hmeta hx23 hx25 hx26 hx28 hmem0 hcode
  rw [cliTryDecryptCommonHeapPlaced_split_tape A ctl x 0 s0] at hmem1
  have hmem1_in : s1.mem ⊨ memRegion (sp + 0x190#64) 0x20 ∗ coinsAfterPlaced x.cur x.rest 0 ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x1b0#64) 0x220 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗ memRegion (sp + 0x400#64) 0xa0 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0x20 ∗ memRegion (sp + 0x500#64) 0x80 ∗ BaseRest ∗
       (protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ lsLogOff ∗ tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ R) :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by dsimp only [msgW, sp]; sep_ac_rfl)) hmem1
  obtain ⟨s2, hsteps2, hvm2, hpc2, hmeta2, hcs2, hmem2⟩ :=
    dhStep_step_778_to_780_coins_vm_placed hwp x.cur x.rest _ s0 s1 hrng hpc1 hmeta1 hx0_1 hx1_1 hx25_1 hv0_1 hmem1_in (hsteps1.codeLoaded hcode)
  have hsteps12 := Steps.trans hsteps1 hsteps2
  have hmem2_in : s2.mem ⊨ ((sp + 0x190#64) ↦ₛ (keyToBytesVec32 (coinsOf x.rest)).toList) ∗
      (memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x1b0#64) 0x220 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗ memRegion (sp + 0x400#64) 0xa0 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0x20 ∗ memRegion (sp + 0x500#64) 0x80 ∗ BaseRest ∗ CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) := by
    rw [cliTryDecryptCommonHeapPlaced_split_tape A ctl x draws s0]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [draws, sp]; sep_ac_rfl)) hmem2
  have hx23_2 : s2.readReg64 .x23 = sp + 0x500#64 := hcs2.2.2.2.2.1.trans hx23_1
  have hx25_2 : s2.readReg64 .x25 = sp + 0x190#64 := hcs2.2.2.2.2.2.2.1.trans hx25_1
  obtain ⟨s3, hsteps3, hvm3, hpc3, hmeta3, hx0_3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hmem3⟩ :=
    dhStep_step_780_to_7a8_vm_placed hwp (keyToBytesVec32 (coinsOf x.rest)) _ s0 s2 hpc2 hmeta2 hx23_2 hx25_2 hmem2_in (hsteps12.codeLoaded hcode)
  have hsteps123 := Steps.trans hsteps12 hsteps3
  have hx23_3' : s3.readReg64 .x23 = sp + 0x500#64 := hx23_3.trans hx23_2
  have hx25_3' : s3.readReg64 .x25 = sp + 0x190#64 := hx25_3.trans hx25_2
  have hmem3_in : s3.mem ⊨ ((sp + 0x190#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion (sp + 0x400#64) 32 ∗ memRegion (sp + 0x500#64) 32 ∗
      (memRegion (sp + 0x420#64) 32 ∗ memRegion (sp + 0x440#64) 0x60 ∗ memRegion (sp + 0x520#64) 0x60 ∗
       memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x1b0#64) 0x220 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0x20 ∗ BaseRest ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) := by
    have h400 := split_400_500_for_keygen sp
    have hmem3' : s3.mem ⊨ (memRegion (sp + 0x400#64) 0xa0 ∗ memRegion (sp + 0x500#64) 0x80) ∗
        (((sp + 0x190#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
         memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
         memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x1b0#64) 0x220 ∗
         ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗
         ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
         ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0x20 ∗ BaseRest ∗
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) :=
      Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [newSenderKey, KeyPair.generate, sp]; sep_ac_rfl)) hmem3
    rw [h400] at hmem3'; exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hmem3'
  obtain ⟨s4, hsteps4, hvm4, hpc4, hmeta4, hcs4, hmem4⟩ :=
    dhStep_step_7a8_to_7b4_cro_vm_placed hwp hdpk newSenderKey.privateKey.bytes _ s0 s3 hpc3 hmeta3 hx0_3 hx8_3 hx23_3' hx25_3' hmem3_in (hsteps123.codeLoaded hcode)
  have hsteps1234 := Steps.trans hsteps123 hsteps4
  have hmem4_in : s4.mem ⊨ memRegion (sp + 0x420#64) 32 ∗ ((sp + 0x500#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      (memRegion (sp + 0x190#64) 32 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       memRegion (sp + 0x440#64) 0x60 ∗ memRegion (sp + 0x520#64) 0x60 ∗
       memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ memRegion (sp + 0x1b0#64) 0x220 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗ memRegion (sp + 0x4e0#64) 0x20 ∗ BaseRest ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by dsimp only [newSenderKey, KeyPair.generate, sp]; sep_ac_rfl)) hmem4
  obtain ⟨s5, hsteps5, hvm5, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, hx30_5, hcs5, hmem5⟩ :=
    dhStep_step_7b4_to_7d4_vm_placed hwp hsd x.msgA newSenderKey.privateKey.bytes _ s0 s4 hpc4 hmeta4
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) hmem4_in (hsteps1234.codeLoaded hcode)
  have hsteps12345 := Steps.trans hsteps1234 hsteps5
  have hmem5' : s5.mem ⊨
      (memRegion (sp + 0x190#64) 32 ∗ memRegion (sp + 0x1b0#64) 0x220 ∗ memRegion (sp + 0x4e0#64) 0x20 ∗ memRegion (sp + 0x500#64) 32 ∗ memRegion (sp + 0x520#64) 0x60) ∗
      (((sp + 0x3d0#64) ↦ₛ chainKeyBytes rck) ∗ memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗ ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
       memRegion (sp + 0x440#64) 0x60 ∗ ((sp + 0x4a0#64) ↦ₛ keyToBytes32 rk1) ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes rck).drop 20) ∗ ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes rck).take 16) ∗
       memRegion sp 0x10 ∗ ((sp + 0x10#64) ↦ₛ ((chainKeyBytes rck).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ BaseRest ∗ CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [sp]; sep_ac_rfl)) hmem5
  rw [split_190_4e0_for_cc2 sp] at hmem5'
  exact ⟨s5, hsteps12345, (((hvm1.trans hvm2).trans hvm3).trans hvm4).trans hvm5, hpc5, hmeta5, hx0_5, hx1_5, hx2_5, hx8_5, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    hx30_5, msgW, hmsgW, Eq.mp (congrArg (s5.mem ⊨ ·) (by dsimp only [BaseRest]; sep_ac_rfl)) hmem5'⟩

theorem dhStep_recv_create_chain_withStack_cro_placed_cli [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry rngFillEntry : BitVec 64} {C : Crypto}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {ctl : BitVec 64}
    (ccStack : Nat)
    (hstack_split : ∀ sp : BitVec 64,
      stackAt sp tryDecryptSubStack =
        (stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
         stackAt sp ccStack))
    (hwp : DhStepBlockVmWp prog entry rngFillEntry)
    (hcc : subroutine_ok prog (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecWithStack M A lim C ccStack)))
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
        CliDhStepAfterRecvChainStatePlaced entry A lim (M.stepEvents evs1 st) ctl
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
       CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st s) ctl x 0 s0 ∗ R) := by
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
    cliTapeAfter ctl x.cur x.rest 0 ∗ lsLogOff ∗
    stackAt (sp - BitVec.ofNat 64 ccStack) (tryDecryptSubStack - ccStack) ∗
    tryDecryptSavedRegs s0.sp s0
  have hpre_cc1 :
      sc1.mem ⊨ (withLsCodeRoLoaded lsmpl (createChainSpecWithStack M A lim C ccStack)).pre
        (ccG1, st) sc1 ∗ (Frame1 ∗ R) := by
    refine add_lscro_pre hcl_c1 ?_
    dsimp only [createChainSpecWithStack, ccG1, Frame1]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c1, hx1_c1, hx2_c1, hx8_c1, hrk1_ne, hfits1⟩, ?_⟩
    rw [htr0_fold, h390_fold, h3b0_fold, show sc1.sp = sp from hsp_c1]
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced at hmem_c1_0
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
         CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' sm) ctl x 0 s0 ∗ R) := by
      dsimp only [Frame1] at hpost
      rw [show sc1.sp = sp from hsp_c1] at hpost
      unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
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
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' sm) ctl x 0 s0 ∗ R
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
           CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' s') ctl x 0 s0 ∗ R) :=
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
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced (A.atState lim st' sm) ctl x 0 s0 ∗ R
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

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudgetAux
