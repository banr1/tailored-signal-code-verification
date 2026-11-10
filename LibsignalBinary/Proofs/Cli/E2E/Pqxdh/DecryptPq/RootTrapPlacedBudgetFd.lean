/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux

/-!
# `FdsGe3Closed`-Threaded `try_decrypt_with_state::<Coins>` Assembly (Block `508`)

Instantiates `RootTrapPlacedBudget` at the pool-carried `FdsGe3Closed` allocator
`AllocWithFds.withFds A` to derive `tryDecryptSpecTPTightAtFd` (and its `StoreKit.withLsRoCl` and
`StoreKit.withLsCodeRoLoaded` caller-block transfers) from either a single `withFdsGe3Closed`
`spqr::recv` contract or `SpqrV1PlacedSeams`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair Mut RatchetState SessionState TripleRatchet rootCreateChain
)
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl
)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508 instIsLsBlockProg_508)
open CryptoVerification.E2E (aesDecHookMallocng formatInnerHook0)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl withLsRoCl
)
open CryptoVerification.LibsignalSessionRepr (ChainGhost msgTypeByte)
open CryptoVerification.LibsignalSpqrV1 (spqrV1 spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (
  SendCall SpqrModel TryDecryptGhost VecArg spqrRecvStack
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser coinsOf uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced cliHookTablePlaced libsignalSessionLib lsFmtWriteSym lsFormatInnerSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
)
open CryptoVerification.SignalSession.Cli.Slots (
  formatInner_row_placed subroutine_ok_cliPlaced_of_trTrap trTrapExternsPlaced
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustAllocEvents
)
open LibsignalBinary.Heap.Fine (formatInnerHook0_budget_ok)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec formatInnerBudgetEnvSpec
  formatInnerBudgetSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget (
  TryDecryptCliEnv TryDecryptCliEnvOf aesDecrypt_507_cli dhStep_pinned_507_cli
  errTail_507_cli s0_507_cli s1_pinned_507_cli s2_507_cli s4_507_cli
  s4_507_cli_ofEnv s6_507_cli s7_507_cli s9_507_cli tryDecryptPqV1_placed_ok_PTight_cli
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget (CmkSeg4Env CmkStepEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (s8Env s9Env)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env vmacEvents)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (cmkLoopAdvanceEvs_nonempty)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (AesDecCtEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (
  protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState vecResultAt_atState
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (s3CommitDefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv s3EnvOf)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  FromS2GenEnv SeamEnvsInhabited TrGhostCaps freeOnlyEvs_nil s1InitTrGhost seqEnv_append seqEnv_ne
  stdAesOpt
)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget (trApplyEnv_senderSome_mem)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvTrapV1_507PlacedBudget (
  pqRecv_507_placed_ok_WT
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget (
  tryDecryptPlacedSpecP tryDecryptPlacedSpecQF_PTight
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudgetFd (
  subroutine_ok_withLsCodeRoLoaded_tryDecryptRawSpecTPTightAtFd_of_outer
  tryDecryptRawSpecTPTightAtFd tryDecryptSpecTPTightAtFd
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (
  envArgsToGhost tryDecrypt_placed_ok_of_seams
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  S5WTSeamPlaced tryDecryptRawSpecTPTightAt tryDecryptSpecTPTightAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  cliGhostAllocHooks_withFds hookOk_aesDecBudget_withFds_of_enforced withFds withFds_pool_enforced
  withFds_repAlloc
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_dealloc_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrRecvBytesEnv SpqrV1PlacedSeams instIsLsBlockProg_blockProgram_329 spqrRecvBytesEnv_nonempty
  spqrRecvPlacedInnerSpecXOfEnv spqrRecvPlacedInnerSpecXTOfEnv
  spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs tryDecryptEnvArgs)

/-! ## Formatting Hook and `spqr::recv` Lifts to `AllocWithFds.withFds A` -/

private theorem hookOk_of_pre_post {α : Type} {f : State → State} {spec1 spec2 : Spec α}
    {Q : α → State → Prop}
    (hok : HookOk f spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → Q x s0 ∧ (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, Q x s0 → (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    HookOk f spec2 := by
  intro x R s0 hrun hpre2 hsp
  obtain ⟨hq, hpre1⟩ := hpre x R s0 hpre2
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre1 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 (f s0) hq hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α} {Q : α → State → Prop}
    (hok : subroutine_ok P entry spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → Q x s0 ∧ (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, Q x s0 → (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    subroutine_ok P entry spec2 := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre2 hsp _
  obtain ⟨hq, hpre1⟩ := hpre x R s0 hpre2
  refine subroutine_ok.mono_outcome hok x R s0 hpc hrun hpre1 hsp ?_
  rintro sf (⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩)
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hq hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private theorem extract_withFdsGe3Closed_post {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (hm : sf.mem ⊨ (withFdsGe3Closed spec).post x s0 sf ∗ R) :
    FdsGe3Closed sf.fs ∧ (sf.mem ⊨ spec.post x s0 sf ∗ R) := by
  dsimp only [withFdsGe3Closed] at hm
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hm

/-- Lift `HookSat hooks sym (withFdsGe3Closed (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))` to
`fmtWriteBudgetEnvSpec M (withFds A) lim fmtWriteEnv` when `lim.enforced = true`. -/
theorem hookSat_fmtWriteBudgetEnv_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {fmtWriteEnv : List AllocEvent → Prop}
    {hooks : String → Option (State → State)} {sym : String}
    (henf : lim.enforced = true)
    (hsat : HookSat hooks sym (withFdsGe3Closed (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))) :
    HookSat hooks sym
      (fmtWriteBudgetEnvSpec M (withFds A) lim fmtWriteEnv) := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, hookOk_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_⟩
  · rintro ⟨v, bs, st⟩ R s0 hpre
    refine ⟨trivial, ?_⟩
    dsimp only [withFdsGe3Closed, fmtWriteBudgetEnvSpec, withFds_repAlloc] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre; sep_ac_rfl
  · rintro ⟨v, bs, st⟩ R s0 sf _ hpost
    obtain ⟨hClosedF, hpost'⟩ := extract_withFdsGe3Closed_post hpost
    dsimp only [fmtWriteBudgetEnvSpec, withFds_repAlloc] at hpost' ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost' ⊢
    rcases hpost' with ⟨evs, hevs⟩
    refine ⟨evs, ?_⟩
    rw [withFds_pool_enforced A henf]
    have hEq :
        (⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace ∧ fmtWriteEnv evs⌝ ∗
          (∃∗ bs' : List (BitVec 8), CryptoVerification.RustHeap.vecU8 A.repAlloc v bs') ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace ∧ fmtWriteEnv evs⌝ ∗
            (∃∗ bs' : List (BitVec 8), CryptoVerification.RustHeap.vecU8 A.repAlloc v bs') ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R) := by
      sep_ac_rfl
    rw [hEq, satisfies_pure_sepConj]
    exact ⟨hClosedF, hevs⟩

/-- Lift `HookSat hooks sym (withFdsGe3Closed (formatInnerBudgetEnvSpec M A lim fmtEnv))` to
`formatInnerBudgetEnvSpec M (withFds A) lim fmtEnv` when `lim.enforced = true`. -/
theorem hookSat_formatInnerBudgetEnv_withFds {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {fmtEnv : List AllocEvent → Prop}
    {hooks : String → Option (State → State)} {sym : String}
    (henf : lim.enforced = true)
    (hsat : HookSat hooks sym (withFdsGe3Closed (formatInnerBudgetEnvSpec M A lim fmtEnv))) :
    HookSat hooks sym
      (formatInnerBudgetEnvSpec M (withFds A) lim fmtEnv) := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, hookOk_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_⟩
  · rintro ⟨ret, st⟩ R s0 hpre
    refine ⟨trivial, ?_⟩
    dsimp only [withFdsGe3Closed, formatInnerBudgetEnvSpec] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre; sep_ac_rfl
  · rintro ⟨ret, st⟩ R s0 sf _ hpost
    obtain ⟨hClosedF, hpost'⟩ := extract_withFdsGe3Closed_post hpost
    dsimp only [formatInnerBudgetEnvSpec, withFds_repAlloc] at hpost' ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost' ⊢
    rcases hpost' with ⟨evs, hevs⟩
    refine ⟨evs, ?_⟩
    rw [withFds_pool_enforced A henf]
    have hEq :
        (⌜sf.trace = s0.trace ∧ fmtEnv evs⌝ ∗
          (∃∗ bs : List (BitVec 8), CryptoVerification.RustHeap.vecU8 A.repAlloc ret bs) ∗
          (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R =
        ⌜FdsGe3Closed sf.fs⌝ ∗
          ((⌜sf.trace = s0.trace ∧ fmtEnv evs⌝ ∗
            (∃∗ bs : List (BitVec 8), CryptoVerification.RustHeap.vecU8 A.repAlloc ret bs) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack) ∗ R) := by
      sep_ac_rfl
    rw [hEq, satisfies_pure_sepConj]
    exact ⟨hClosedF, hevs⟩

/-- Lift a `withFdsGe3Closed` Block-`329` `spqr::recv` contract to
`spqrRecvPlacedInnerSpecXTOfEnv M (withFds A) lim` when `lim.enforced = true`. -/
theorem subroutine_ok_spqrRecv_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {Rmod : CryptoVerification.LibsignalSpqrV1.SpqrRecvModel}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hRecvFd : subroutine_ok P entry
      (withFdsGe3Closed
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrRecvPlacedInnerSpecXTOfEnv M A lim Rmod RecvEnv)))) :
    subroutine_ok P entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M (withFds A) lim Rmod RecvEnv)) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hRecvFd rfl rfl rfl ?_ ?_
  · rintro ⟨⟨stArg, msgArg, ret⟩, stB⟩ R s0 hpre
    refine ⟨trivial, ?_⟩
    dsimp only [withFdsGe3Closed,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
      withFds_repAlloc] at hpre ⊢
    rw [withFds_pool_enforced A henf] at hpre
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre; sep_ac_rfl
  · rintro ⟨⟨stArg, msgArg, ret⟩, stB⟩ R s0 sf _ hpost
    obtain ⟨hClosedF, hpost'⟩ := extract_withFdsGe3Closed_post hpost
    dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
      withFds_repAlloc] at hpost' ⊢
    have hpost'' : sf.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜RecvEnv stArg msgArg evs⌝ ∗
          ⌜sf.trace = s0.trace ∧ ¬ Rmod.recvPanics stArg.bytes msgArg.bytes⌝ ∗
          stArg.at A.repAlloc ∗ msgArg.at A.repAlloc ∗
          CryptoVerification.LibsignalSpqrV1.recvResultExactKeyAt A.repAlloc ret
            (Rmod.recv stArg.bytes msgArg.bytes) ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs stB) sf ∗
          stackAt s0.sp spqrRecvStack) ∗
        (tokenInitPlacedAt ∗ R) := by
      refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hpost'; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost''
    rcases hpost'' with ⟨evs, hevs⟩
    have hex : sf.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜RecvEnv stArg msgArg evs⌝ ∗
          ⌜sf.trace = s0.trace ∧ ¬ Rmod.recvPanics stArg.bytes msgArg.bytes⌝ ∗
          stArg.at A.repAlloc ∗ msgArg.at A.repAlloc ∗
          CryptoVerification.LibsignalSpqrV1.recvResultExactKeyAt A.repAlloc ret
            (Rmod.recv stArg.bytes msgArg.bytes) ∗
          lsLogOff ∗
          (withFds A).pool lim (M.stepEvents evs stB) sf ∗
          stackAt s0.sp spqrRecvStack) ∗
        (tokenInitPlacedAt ∗ R) := by
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      have hEq :
          (⌜RecvEnv stArg msgArg evs⌝ ∗
            ⌜sf.trace = s0.trace ∧ ¬ Rmod.recvPanics stArg.bytes msgArg.bytes⌝ ∗
            stArg.at A.repAlloc ∗ msgArg.at A.repAlloc ∗
            CryptoVerification.LibsignalSpqrV1.recvResultExactKeyAt A.repAlloc ret
              (Rmod.recv stArg.bytes msgArg.bytes) ∗
            lsLogOff ∗
            (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs stB) sf) ∗
            stackAt s0.sp spqrRecvStack) ∗
          (tokenInitPlacedAt ∗ R) =
          ⌜FdsGe3Closed sf.fs⌝ ∗
            ((⌜RecvEnv stArg msgArg evs⌝ ∗
              ⌜sf.trace = s0.trace ∧ ¬ Rmod.recvPanics stArg.bytes msgArg.bytes⌝ ∗
              stArg.at A.repAlloc ∗ msgArg.at A.repAlloc ∗
              CryptoVerification.LibsignalSpqrV1.recvResultExactKeyAt A.repAlloc ret
                (Rmod.recv stArg.bytes msgArg.bytes) ∗
              lsLogOff ∗
              A.pool lim (M.stepEvents evs stB) sf ∗
              stackAt s0.sp spqrRecvStack) ∗
            (tokenInitPlacedAt ∗ R)) := by
        sep_ac_rfl
      rw [hEq, satisfies_pure_sepConj]
      exact ⟨hClosedF, hevs⟩
    refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hex; sep_ac_rfl

/-! ## Conversion from `AllocWithFds.withFds A` to `tryDecryptSpecTPTightAtFd` -/

/-- Convert `subroutine_ok P entry (tryDecryptSpecTPTightAt C (withFds A) lim ...)` to
`subroutine_ok P entry (tryDecryptSpecTPTightAtFd C A lim ...)` when `lim.enforced = true`. -/
theorem subroutine_ok_tryDecryptSpecTPTightAtFd_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (tryDecryptSpecTPTightAt C (withFds A) lim ctl parse S tdEnv)) :
    subroutine_ok P entry
      (tryDecryptSpecTPTightAtFd C A lim ctl parse S tdEnv) := by
  refine subroutine_ok_of_pre_post (Q := fun _ _ => True) hok rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    refine ⟨trivial, ?_⟩
    obtain ⟨hClosed0, hpreA⟩ := extract_withFdsGe3Closed hpre
    dsimp only [tryDecryptSpecTPTightAt,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      tryDecryptRawSpecTPTightAt, tryDecryptPlacedSpecQF_PTight, tryDecryptPlacedSpecP,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP,
      RustCliAllocBudget.atState_pool, withFds_repAlloc,
      sessionStateAt_atState, protocolAddressAt_atState, signalMessageAt_atState] at hpreA ⊢
    change s0.mem ⊨ _ at hpreA ⊢
    rw [withFds_pool_enforced A henf]
    let Head :=
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ tokenInitPlacedAt ∗
      ⌜LibsignalBinary.Heap.FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x))⌝ ∗
      ⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.ss ∧ s0.readReg64 .x2 = x.remA ∧
        s0.readReg64 .x3 = x.locA ∧ s0.readReg64 .x4 = x.msgA ∧
        (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
        (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
          CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid parse x.loc.name.bytes
            x.rem.name.bytes) ∧
        CryptoVerification.LibsignalTripleRatchet.SeedsLen32 x.st ∧
        x.st.receiverChains.length < 2 ^ 32 ∧
        CryptoVerification.LibsignalTripleRatchet.rootStack ≤ s0.sp.toNat⌝ ∗
      CryptoVerification.LibsignalTripleRatchetRepr.sessionStateAt A.repAlloc x.ss x.G x.st ∗
      CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.rem x.remA ∗
      CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.loc x.locA ∗
      CryptoVerification.LibsignalTripleRatchetRepr.signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      memRegion x.ret 48 ∗ CryptoVerification.Cli.CoinsTape.cliTapeAt ctl x.cur x.rest ∗
      lsLogOff ∗
      stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.rootStack
    have hpreA' : s0.mem ⊨
        ((Head ∗ A.pool lim st s0) ∗
          ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R := by
      dsimp only [Head]
      refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpreA; sep_ac_rfl
    have hgoal : s0.mem ⊨
        ⌜FdsGe3Closed s0.fs⌝ ∗
          (((Head ∗ A.pool lim st s0) ∗
            ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R) :=
      (satisfies_pure_sepConj _ _ _).mpr ⟨hClosed0, hpreA'⟩
    dsimp only [Head] at hgoal
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hgoal; sep_ac_rfl
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [tryDecryptSpecTPTightAtFd, withFdsGe3Closed, tryDecryptSpecTPTightAt,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      tryDecryptRawSpecTPTightAt, tryDecryptPlacedSpecQF_PTight, tryDecryptPlacedSpecP,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      RustCliAllocBudget.atState_pool, withFds_repAlloc,
      sessionStateAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      vecResultAt_atState] at hpost ⊢
    have hpost' : sf.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜tdEnv (tryDecryptEnvArgs x) evs⌝ ∗
          ⌜(x.model C S parse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G' : CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost,
            ⌜x.G.AfterTryDecrypt (x.model C S parse).1.toBool G'⌝ ∗
            CryptoVerification.LibsignalTripleRatchetRepr.sessionStateAt A.repAlloc x.ss G'
              (x.model C S parse).2) ∗
          CryptoVerification.LibsignalTripleRatchetRepr.vecResultAt A.repAlloc x.ret
            (x.model C S parse).1 ∗
          CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.rem x.remA ∗
          CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.loc x.locA ∗
          CryptoVerification.LibsignalTripleRatchetRepr.signalMessageAt A.repAlloc x.msgG x.msgA
            x.msg ∗
          CryptoVerification.Cli.CoinsTape.cliTapeAfter ctl x.cur x.rest
            (CryptoVerification.LibsignalTripleRatchetRepr.decryptDraws C x.st
              x.msg.senderRatchetKey x.rest) ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.rootStack ∗
          (withFds A).pool lim (M.stepEvents evs st) sf) ∗
        (tokenInitPlacedAt ∗ R) := by
      refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hpost; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost'
    rcases hpost' with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    let Body := fun (evs' : List AllocEvent) =>
      ⌜tdEnv (tryDecryptEnvArgs x) evs'⌝ ∗
      ⌜(x.model C S parse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ G' : CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost,
        ⌜x.G.AfterTryDecrypt (x.model C S parse).1.toBool G'⌝ ∗
        CryptoVerification.LibsignalTripleRatchetRepr.sessionStateAt A.repAlloc x.ss G'
          (x.model C S parse).2) ∗
      CryptoVerification.LibsignalTripleRatchetRepr.vecResultAt A.repAlloc x.ret
        (x.model C S parse).1 ∗
      CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.rem x.remA ∗
      CryptoVerification.LibsignalTripleRatchetRepr.protocolAddressAt A.repAlloc x.loc x.locA ∗
      CryptoVerification.LibsignalTripleRatchetRepr.signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      CryptoVerification.Cli.CoinsTape.cliTapeAfter ctl x.cur x.rest
        (CryptoVerification.LibsignalTripleRatchetRepr.decryptDraws C x.st
          x.msg.senderRatchetKey x.rest) ∗
      CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
      stackAt s0.sp CryptoVerification.LibsignalTripleRatchet.rootStack
    have hevs' : sf.mem ⊨
        ⌜FdsGe3Closed sf.fs⌝ ∗ ((Body evs ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          (tokenInitPlacedAt ∗ R)) := by
      dsimp only [Body]
      refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hevs; sep_ac_rfl
    obtain ⟨hClosedF, hbody⟩ := (satisfies_pure_sepConj _ _ _).mp hevs'
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    have hex : sf.mem ⊨
        (∃∗ evs' : List AllocEvent, Body evs' ∗ A.pool lim (M.stepEvents evs' st) sf) ∗
        (tokenInitPlacedAt ∗ R) := by
      rw [sepExists_sepConj_left, satisfies_sepExists]
      exact ⟨evs, hbody⟩
    dsimp only [Body] at hex
    refine Eq.mp (congrArg (sf.mem ⊨ ·) ?_) hex; sep_ac_rfl

/-! ## Single-Seam `spqr::recv` Top-Level Contracts -/

private theorem cliGhost_row (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ CryptoVerification.SignalSession.lsReadFileSym := by decide)
    (h8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans (cliExternsPlaced_row mmpl W hrow)

private theorem pqRecv_507_cli_of_spqrRecv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hRecv : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st msg => RecvBytesEnv st.bytes msg.bytes))))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) RecvBytesEnv fmtEnv) := by
  have _ := instIsLsBlockProg_508 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have _ := instIsLsBlockProg_508 (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
  have _ := instIsLsBlockProg_blockProgram_329
    (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
  have htr508 := subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block
      (callerProg := (blkPC_508).rebase (blkPl_508).base
        (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
      hRecv (by decide) (by decide) (by decide))
  have hcli508 : subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st msg => RecvBytesEnv st.bytes msg.bytes))) :=
    subroutine_ok_cliPlaced_of_trTrap (pc := blkPC_508) (b := (blkPl_508).base) htr508
  exact pqRecv_507_placed_ok_WT W.C A lim ctl (spqrV1 W.C.F W.Q.K)
    RecvBytesEnv fmtEnv (cliGhostExterns g (cliExternsPlaced mmpl W))
    (spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT hcli508)
    (ls_hook_ok_ultra_of_mem hFmtInner)
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

private theorem cliSeamEnvs_inhabited (C : Crypto) (S : SpqrModel)
    {fmtWriteEnv : List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs) :
    SeamEnvsInhabited
      (s3DefaultEnv C)
      (CmkSeg4Env fmtWriteEnv)
      (PqRecvEnv S RecvBytesEnv fmtEnv)
      s6FreeOnlyEnv
      (s7Env C.F uuidTryParse)
      s8Env
      s9Env where
  s4 x trG tr ck := by
    refine seqEnv_ne hFmtWrite_ne (seqEnv_ne ?_ ⟨[], freeOnlyEvs_nil⟩)
    unfold CmkStepEnv
    by_cases h1 : x.msg.counter < ck.index
    · simp only [h1, ↓reduceIte]; exact ⟨[], freeOnlyEvs_nil⟩
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (x.msg.counter - ck.index).toNat ≤ tr.ratchet.maxForwardJumps
      · simp only [h2, ↓reduceIte]
        cases tr.ratchet.findReceiverChainIndex x.msg.senderRatchetKey with
        | none =>
          by_cases h3 : ck.index < x.msg.counter
          · simp only [h3, ↓reduceIte]; exact ⟨[], Or.inl rfl⟩
          · simp only [h3, ↓reduceIte]; exact ⟨[], rfl⟩
        | some _ =>
          exact cmkLoopAdvanceEvs_nonempty _ _ _ _
      · simp only [h2, ↓reduceIte]; exact ⟨rustAllocEvents 36 1, rfl⟩
  s5 x tr := by
    unfold PqRecvEnv
    cases S.recv tr.pqrState x.msg.pqRatchet with
    | ok _ => exact hRecv_ne _ _
    | error _ => exact seqEnv_ne (seqEnv_ne (hRecv_ne _ _) hFmtInner_ne) ⟨[], freeOnlyEvs_nil⟩
  s6 _ := ⟨[], freeOnlyEvs_nil⟩
  s7 x tr mks _ :=
    ⟨vmacEvents C.F uuidTryParse x tr mks ++ rustAllocEvents 23 1,
      Or.inl (seqEnv_append rfl rfl)⟩
  s8 x _ _ := by
    unfold s8Env
    refine seqEnv_ne ?_ ⟨[], freeOnlyEvs_nil⟩
    unfold AesDecCtEnv
    by_cases h : x.msg.ciphertext.length = 0 ∨ x.msg.ciphertext.length % 16 ≠ 0
    · simp only [h, ↓reduceIte]; exact ⟨[], rfl⟩
    · simp only [h, ↓reduceIte]; exact ⟨_, Or.inl rfl⟩
  s9 _ _ _ _ _ :=
    let e_tr := rustAllocEvents 32 1 ++ (rustAllocEvents 33 1 ++
      (rustAllocEvents 33 1 ++ (rustAllocEvents 32 1 ++
        (rustAllocEvents 32 1 ++ rustAllocEvents 32 1))))
    ⟨e_tr, Or.inr ⟨[], e_tr, rfl, freeOnlyEvs_nil,
      Or.inr ⟨e_tr, [], (List.append_nil e_tr).symm, trApplyEnv_senderSome_mem, freeOnlyEvs_nil⟩⟩⟩
  s4_caps x trG₁ trG₂ tr ck evs hcaps h := by
    have hmk : List.map ChainGhost.mkCap trG₁.ratchet.chains =
        List.map ChainGhost.mkCap trG₂.ratchet.chains :=
      congrArg TrGhostCaps.mkCaps hcaps
    have hci : ∀ ci,
        trG₁.ratchet.chains[ci]?.map ChainGhost.mkCap =
          trG₂.ratchet.chains[ci]?.map ChainGhost.mkCap := fun ci => by
      rw [← List.getElem?_map, ← List.getElem?_map, hmk]
    have hstep : CmkStepEnv x.msg.counter x.msg.senderRatchetKey trG₁ tr.ratchet ck =
        CmkStepEnv x.msg.counter x.msg.senderRatchetKey trG₂ tr.ratchet ck := by
      funext e
      unfold CmkStepEnv
      cases tr.ratchet.findReceiverChainIndex x.msg.senderRatchetKey with
      | none => rfl
      | some ci => simp only [hci ci]
    unfold CmkSeg4Env at h ⊢
    rwa [← hstep]
  s9_trG _ _ _ _ _ _ _ h := h
  s3 x trG tr := by
    unfold s3DefaultEnv s3EnvOf
    cases tr.ratchet.senderChain with
    | none => exact ⟨[], rfl⟩
    | some sc =>
      dsimp only
      cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
      | error _ => exact ⟨_, rfl⟩
      | ok p1 =>
        rcases p1 with ⟨rk1, _⟩
        dsimp only
        cases rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error _ => exact seqEnv_ne ⟨_, rfl⟩ ⟨_, rfl⟩
        | ok _ =>
          exact seqEnv_ne ⟨_, rfl⟩ (seqEnv_ne ⟨_, rfl⟩ ⟨_, Or.inl rfl⟩)
  s3_caps x trG₁ trG₂ tr evs hcaps h := by
    have hcc : trG₁.ratchet.chainsCap = trG₂.ratchet.chainsCap :=
      congrArg TrGhostCaps.chainsCap hcaps
    have hs3_eq : s3DefaultEnv C x trG₁ tr = s3DefaultEnv C x trG₂ tr := by
      funext e
      unfold s3DefaultEnv s3EnvOf s3CommitDefaultEnv
      simp only [hcc]
    exact hs3_eq ▸ h

private theorem fromS2_envArgsToGhost_eq (C : Crypto) (S : SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost)
    (tr0 : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8))) :
    FromS2GenEnv C uuidTryParse S (stdAesOpt C)
      (s3DefaultEnv C) (CmkSeg4Env fmtWriteEnv) (PqRecvEnv S RecvBytesEnv fmtEnv)
      s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
      (envArgsToGhost (tryDecryptEnvArgs x))
      (s1InitTrGhost (tryDecryptEnvArgs x).G) tr0 st1 =
    FromS2GenEnv C uuidTryParse S (stdAesOpt C)
      (s3DefaultEnv C) (CmkSeg4Env fmtWriteEnv) (PqRecvEnv S RecvBytesEnv fmtEnv)
      s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
      x (s1InitTrGhost x.G) tr0 st1 := rfl

/-- Envelope-monotonic Block-`508` `tryDecryptSpecTPTightAtFd` from a `withFdsGe3Closed` `spqr::recv` contract (`hRecvFd`). -/
theorem tryDecryptPqV1_placed_ok_PTight_cli_fd_of_recv_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (henf : lim.enforced = true)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDecFd : HookOk (aesDecHookMallocng mmpl W.C.D)
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D M A lim)))
    (hRecvFd : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withFdsGe3Closed
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
            (fun st msg => RecvBytesEnv st.bytes msg.bytes)))))
    (hFmtWriteFd : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (withFdsGe3Closed (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv)))
    (hFmtInnerFd : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (withFdsGe3Closed (formatInnerBudgetEnvSpec M A lim fmtEnv)))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv a evs →
      tdEnv a evs) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (tryDecryptSpecTPTightAtFd W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv) := by
  let A' := withFds A
  have hG' := cliGhostAllocHooks_withFds hG
  have hAes' := hookOk_aesDecBudget_withFds_of_enforced henf hAesDecFd
  have hRecv' := subroutine_ok_spqrRecv_withFds henf hRecvFd
  have hFmtW' := hookSat_fmtWriteBudgetEnv_withFds henf hFmtWriteFd
  have hFmtI' := hookSat_formatInnerBudgetEnv_withFds henf hFmtInnerFd
  refine subroutine_ok_tryDecryptSpecTPTightAtFd_of_withFds henf ?_
  exact tryDecrypt_placed_ok_of_seams
    (A := A')
    (s1OkEnv := fun _ => FreeOnlyEvs)
    (fun x evs herr hfree => htd (tryDecryptEnvArgs x) evs (by
      unfold TryDecryptCliEnvOf
      change (match Mut.exec TripleRatchet.fromSessionState x.st with
        | (.error _, _) => FreeOnlyEvs
        | (.ok tr0, st1) => _) evs
      rcases h : Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | _, _⟩
      · exact hfree
      · rw [h] at herr; cases herr))
    (fun x tr0 st1 evs htr hseq => htd (tryDecryptEnvArgs x) evs (by
      unfold TryDecryptCliEnvOf
      change (match Mut.exec TripleRatchet.fromSessionState x.st with
        | (.error _, _) => FreeOnlyEvs
        | (.ok tr0, st1) => _) evs
      rw [htr]
      dsimp only
      rw [fromS2_envArgsToGhost_eq]
      exact hseq))
    (cliSeamEnvs_inhabited W.C (spqrV1 W.C.F W.Q.K) hRecv_ne hFmtWrite_ne hFmtInner_ne)
    (s0_507_cli (A := A') mmpl g W ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (s1_pinned_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (s2_507_cli (A := A') mmpl g W ctl)
    (dhStep_pinned_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K))
    (s4_507_cli_ofEnv mmpl g W hG' hFmtW' ctl (spqrV1 W.C.F W.Q.K))
    (pqRecv_507_cli_of_spqrRecv mmpl g W hG' hRecv' hFmtI' ctl)
    (s6_507_cli mmpl g W hG' ctl)
    (s7_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K))
    (aesDecrypt_507_cli mmpl g W hG' hAes' ctl (spqrV1 W.C.F W.Q.K))
    (s9_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (errTail_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K) tdEnv)

/-- Default `TryDecryptCliEnv` Block-`508` `tryDecryptSpecTPTightAtFd` from a `withFdsGe3Closed` `spqr::recv` contract. -/
theorem tryDecryptPqV1_placed_ok_PTight_cli_fd_of_recv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (henf : lim.enforced = true)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDecFd : HookOk (aesDecHookMallocng mmpl W.C.D)
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D M A lim)))
    (hRecvFd : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withFdsGe3Closed
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
            (fun st msg => SpqrRecvBytesEnv st.bytes msg.bytes))))) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (tryDecryptSpecTPTightAtFd W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
        (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))) := by
  let A' := withFds A
  have hG' := cliGhostAllocHooks_withFds hG
  have hAes' := hookOk_aesDecBudget_withFds_of_enforced henf hAesDecFd
  have hRecv' := subroutine_ok_spqrRecv_withFds henf hRecvFd
  have hFmtI' : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetSpec M A' lim) :=
    ⟨formatInnerHook0, cliGhost_row mmpl g W (formatInner_row_placed mmpl W),
      formatInnerHook0_budget_ok M A' lim⟩
  refine subroutine_ok_tryDecryptSpecTPTightAtFd_of_withFds henf ?_
  exact tryDecrypt_placed_ok_of_seams
    (A := A')
    (s1OkEnv := fun _ => FreeOnlyEvs)
    (fun x evs herr hfree => by
      unfold TryDecryptCliEnv TryDecryptCliEnvOf
      change (match Mut.exec TripleRatchet.fromSessionState x.st with
        | (.error _, _) => FreeOnlyEvs
        | (.ok tr0, st1) => _) evs
      rcases h : Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | _, _⟩
      · exact hfree
      · rw [h] at herr; cases herr)
    (fun x tr0 st1 evs htr hseq => by
      unfold TryDecryptCliEnv TryDecryptCliEnvOf
      change (match Mut.exec TripleRatchet.fromSessionState x.st with
        | (.error _, _) => FreeOnlyEvs
        | (.ok tr0, st1) => _) evs
      rw [htr]
      dsimp only
      rw [fromS2_envArgsToGhost_eq]
      exact hseq)
    (cliSeamEnvs_inhabited (fmtWriteEnv := FmtWriteEnv) (fmtEnv := FormatInnerEnv)
      W.C (spqrV1 W.C.F W.Q.K)
      spqrRecvBytesEnv_nonempty ⟨[], rfl⟩ ⟨[], rfl⟩)
    (s0_507_cli (A := A') mmpl g W ctl (spqrV1 W.C.F W.Q.K)
      (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (s1_pinned_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K)
      (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (s2_507_cli (A := A') mmpl g W ctl)
    (dhStep_pinned_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K))
    (s4_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K))
    (pqRecv_507_cli_of_spqrRecv mmpl g W hG' hRecv' hFmtI' ctl)
    (s6_507_cli mmpl g W hG' ctl)
    (s7_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K))
    (aesDecrypt_507_cli mmpl g W hG' hAes' ctl (spqrV1 W.C.F W.Q.K))
    (s9_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K)
      (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (errTail_507_cli mmpl g W hG' ctl (spqrV1 W.C.F W.Q.K)
      (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))

theorem tryDecryptPqV1_placed_ok_PTight_cli_rocl_fd_of_recv_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (henf : lim.enforced = true)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDecFd : HookOk (aesDecHookMallocng mmpl W.C.D)
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D M A lim)))
    (hRecvFd : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withFdsGe3Closed
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
            (fun st msg => RecvBytesEnv st.bytes msg.bytes)))))
    (hFmtWriteFd : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (withFdsGe3Closed (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv)))
    (hFmtInnerFd : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (withFdsGe3Closed (formatInnerBudgetEnvSpec M A lim fmtEnv)))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv a evs →
      tdEnv a evs)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg
      (lsmpl.base 508)
      (withLsRoCl lsmpl
        (tryDecryptRawSpecTPTightAtFd W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)) := by
  have _ := instIsLsBlockProg_508 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have h508 : subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAtFd W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)) :=
    subroutine_ok_withLsCodeRoLoaded_tryDecryptRawSpecTPTightAtFd_of_outer
      (tryDecryptPqV1_placed_ok_PTight_cli_fd_of_recv_of_tdEnv mmpl g W ctl henf hG hAesDecFd
        hRecvFd hFmtWriteFd hFmtInnerFd hRecv_ne hFmtWrite_ne hFmtInner_ne htd)
  exact ls_subroutine_ok_rocl_of_block h508 hi

theorem tryDecryptPqV1_placed_ok_PTight_cli_at_block_fd_of_recv_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (henf : lim.enforced = true)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDecFd : HookOk (aesDecHookMallocng mmpl W.C.D)
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D M A lim)))
    (hRecvFd : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withFdsGe3Closed
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
            (fun st msg => RecvBytesEnv st.bytes msg.bytes)))))
    (hFmtWriteFd : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (withFdsGe3Closed (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv)))
    (hFmtInnerFd : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (withFdsGe3Closed (formatInnerBudgetEnvSpec M A lim fmtEnv)))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv a evs →
      tdEnv a evs)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAtFd W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (tryDecryptPqV1_placed_ok_PTight_cli_rocl_fd_of_recv_of_tdEnv mmpl g W ctl henf hG
      hAesDecFd hRecvFd hFmtWriteFd hFmtInnerFd hRecv_ne hFmtWrite_ne hFmtInner_ne htd hi)

theorem tryDecryptPqV1_placed_ok_PTight_cli_rocl_fd_of_recv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (henf : lim.enforced = true)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDecFd : HookOk (aesDecHookMallocng mmpl W.C.D)
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D M A lim)))
    (hRecvFd : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withFdsGe3Closed
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
            (fun st msg => SpqrRecvBytesEnv st.bytes msg.bytes)))))
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg
      (lsmpl.base 508)
      (withLsRoCl lsmpl
        (tryDecryptRawSpecTPTightAtFd W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))) := by
  have _ := instIsLsBlockProg_508 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have h508 := subroutine_ok_withLsCodeRoLoaded_tryDecryptRawSpecTPTightAtFd_of_outer
    (tryDecryptPqV1_placed_ok_PTight_cli_fd_of_recv mmpl g W ctl henf hG hAesDecFd hRecvFd)
  exact ls_subroutine_ok_rocl_of_block h508 hi

theorem tryDecryptPqV1_placed_ok_PTight_cli_at_block_fd_of_recv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (henf : lim.enforced = true)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDecFd : HookOk (aesDecHookMallocng mmpl W.C.D)
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D M A lim)))
    (hRecvFd : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withFdsGe3Closed
        (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
            (fun st msg => SpqrRecvBytesEnv st.bytes msg.bytes)))))
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg
      (lsmpl.base 508)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAtFd W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (tryDecryptPqV1_placed_ok_PTight_cli_rocl_fd_of_recv mmpl g W ctl henf hG hAesDecFd
      hRecvFd hi)

/-! ## `SpqrV1PlacedSeams` Convenience Wrappers -/

/-- Block-`508` `tryDecryptSpecTPTightAtFd` directly from `SpqrV1PlacedSeams M (withFds A) lim`. -/
theorem tryDecryptPqV1_placed_ok_PTight_cli_fd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (henf : lim.enforced = true)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDecFd : HookOk (aesDecHookMallocng mmpl W.C.D)
      (withFdsGe3Closed (aesDecBudgetSpec W.C.D M A lim)))
    (hSpqrFd : SpqrV1PlacedSeams M (withFds A) lim mmpl g W) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (tryDecryptSpecTPTightAtFd W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
        (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))) :=
  subroutine_ok_tryDecryptSpecTPTightAtFd_of_withFds henf
    (tryDecryptPqV1_placed_ok_PTight_cli mmpl g W ctl
      (cliGhostAllocHooks_withFds hG)
      (hookOk_aesDecBudget_withFds_of_enforced henf hAesDecFd)
      hSpqrFd)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetFd
