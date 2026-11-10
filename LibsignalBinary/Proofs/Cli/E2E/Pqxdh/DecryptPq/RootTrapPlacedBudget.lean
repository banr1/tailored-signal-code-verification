/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookup507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupErrSym507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS0_507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS1Err507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS2Sym507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeySub507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeyTrap507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DecryptTailTrap507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart4
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart5
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvErr507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvTrapV1_507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget

/-!
# Budget-Threaded Relocatable Tight-Panic Assembly on Block `507`

Instantiates the budget-threaded (`RustCliAllocBudget M`) Block-`507` segment seams at
`cliGhostExterns g (cliExternsPlaced mmpl W)` and proves `tryDecryptPqV1_placed_ok_PTight_cli`
along with its `StoreKit.withLsRoCl` and `StoreKit.withLsCodeRoLoaded` caller-block transfers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair Mut RatchetState SessionState TripleRatchet rootCreateChain
)
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement lsmpl
)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508 instIsLsBlockProg_508)
open CryptoVerification.E2E (aesDecHookMallocng)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl withLsCodeRoLoaded
  withLsRoCl
)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall SpqrModel TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (coinsOf uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsFmtWriteSym lsFormatInnerSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget SeqEnv rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec formatInnerBudgetEnvSpec
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget (
  CmkSeg4Env CmkStepEnv s4DefaultEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (s8Env s9Env)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (
  TryDecryptCliEnv TryDecryptCliEnvOf envArgsToGhost tryDecrypt_placed_ok_of_seams
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env vmacEvents)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlacedBudget (
  S1TightSeamFreePlaced S1TightSeamPinnedFreePlaced
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ErrTailTightSeamPlaced S0PSeamPlaced S2SeamPlaced S3TightSeamPinnedPlaced S3TightSeamPlaced
  S4SeamPlaced S5WTSeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
  tryDecryptRawSpecTPTightAt tryDecryptSpecTPTightAt
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  cmkLoopAdvanceEvs_nonempty
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv spqrRecvBytesEnv_nonempty
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (AesDecCtEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (s3CommitDefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv s3EnvOf)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  FromS2GenEnv SeamEnvsInhabited TrGhostCaps freeOnlyEvs_nil s1InitTrGhost seqEnv_append seqEnv_ne
  stdAesOpt
)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget (trApplyEnv_senderSome_mem)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs tryDecryptEnvArgs)

export LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (
  TryDecryptCliEnv TryDecryptCliEnvOf
)

/-! ## Block `507` CLI Segment Seams -/

theorem errTail_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    ErrTailTightSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv :=
  RootTrapPlacedBudgetPart2.errTail_507_cli mmpl g W hG ctl S tdEnv

theorem pqRecv_507_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) RecvBytesEnv fmtEnv) :=
  RootTrapPlacedBudgetPart2.pqRecv_507_cli_ofEnv mmpl g W hG hSpqr hFmtInner ctl

theorem pqRecv_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W) (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) SpqrRecvBytesEnv FormatInnerEnv) :=
  RootTrapPlacedBudgetPart2.pqRecv_507_cli mmpl g W hG hSpqr ctl

theorem aesDecrypt_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (ctl : BitVec 64) (S : SpqrModel) :
    S8SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S s8Env :=
  RootTrapPlacedBudgetPart2.aesDecrypt_507_cli mmpl g W hG hAesDec ctl S

theorem s0_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S0PSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv :=
  RootTrapPlacedBudgetPart2.s0_507_cli mmpl g W ctl S tdEnv

theorem s1_pinned_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S1TightSeamPinnedFreePlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv (fun _ => FreeOnlyEvs) :=
  RootTrapPlacedBudgetPart2.s1_pinned_507_cli mmpl g W hG ctl S tdEnv

theorem s1_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S1TightSeamFreePlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv (fun _ => FreeOnlyEvs) :=
  RootTrapPlacedBudgetPart2.s1_507_cli mmpl g W hG ctl S tdEnv

theorem s2_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64) :
    S2SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base A lim ctl :=
  RootTrapPlacedBudgetPart2.s2_507_cli mmpl g W ctl

theorem s6_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) :
    S6SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl s6FreeOnlyEnv :=
  RootTrapPlacedBudgetPart3.s6_507_cli mmpl g W hG ctl

theorem s9_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S9SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv s9Env :=
  RootTrapPlacedBudgetPart3.s9_507_cli mmpl g W hG ctl S tdEnv

theorem dhStep_pinned_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPinnedPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) :=
  RootTrapPlacedBudgetPart4.dhStep_pinned_507_cli mmpl g W hG ctl S

theorem dhStep_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) :=
  (dhStep_pinned_507_cli mmpl g W hG ctl S).toUnpinned

theorem s4_507_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {fmtWriteEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (ctl : BitVec 64) (S : SpqrModel) :
    S4SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S (CmkSeg4Env fmtWriteEnv) :=
  RootTrapPlacedBudgetPart5.s4_507_cli_ofEnv mmpl g W hG hFmtWrite ctl S

theorem s4_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S4SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S s4DefaultEnv :=
  RootTrapPlacedBudgetPart5.s4_507_cli mmpl g W hG ctl S

theorem s7_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S7SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S (s7Env W.C.F uuidTryParse) :=
  RootTrapPlacedBudgetPart3.s7_507_cli mmpl g W hG ctl S

/-! ## Top-Level Block `507` Contracts and Caller-Block Transfers -/

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

/-- Envelope-monotonic Block-`507` `tryDecryptSpecTPTightAt` at
    `cliGhostExterns g (cliExternsPlaced mmpl W)` for any `tdEnv` containing `TryDecryptCliEnvOf`. -/
theorem tryDecryptPqV1_placed_ok_PTight_cli_of_tdEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv a evs →
      tdEnv a evs) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (tryDecryptSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv) := by
  refine tryDecrypt_placed_ok_of_seams
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
    (s0_507_cli mmpl g W ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (s1_pinned_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (s2_507_cli mmpl g W ctl)
    (dhStep_pinned_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (s4_507_cli_ofEnv mmpl g W hG hFmtWrite ctl (spqrV1 W.C.F W.Q.K))
    (pqRecv_507_cli_ofEnv mmpl g W hG hSpqr hFmtInner ctl)
    (s6_507_cli mmpl g W hG ctl)
    (s7_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (aesDecrypt_507_cli mmpl g W hG hAesDec ctl (spqrV1 W.C.F W.Q.K))
    (s9_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) tdEnv)
    (errTail_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) tdEnv)

theorem tryDecryptPqV1_placed_ok_PTight_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (tryDecryptSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
        (TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv)) :=
  tryDecryptPqV1_placed_ok_PTight_cli_of_tdEnv mmpl g W ctl hG hAesDec hSpqr hFmtWrite hFmtInner
    hRecv_ne hFmtWrite_ne hFmtInner_ne (fun _ _ h => h)

/-- Concrete placed CLI `tryDecryptSpecTPTightAt` on Block `507` at
    `S := spqrV1 W.C.F W.Q.K` and `tdEnv := TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)`. -/
theorem tryDecryptPqV1_placed_ok_PTight_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (tryDecryptSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
        (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))) :=
  tryDecrypt_placed_ok_of_seams
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
    (s0_507_cli mmpl g W ctl (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (s1_pinned_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K)
      (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (s2_507_cli mmpl g W ctl)
    (dhStep_pinned_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (s4_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (pqRecv_507_cli mmpl g W hG hSpqr ctl)
    (s6_507_cli mmpl g W hG ctl)
    (s7_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K))
    (aesDecrypt_507_cli mmpl g W hG hAesDec ctl (spqrV1 W.C.F W.Q.K))
    (s9_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))
    (errTail_507_cli mmpl g W hG ctl (spqrV1 W.C.F W.Q.K) (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))

/-- Envelope-monotonic caller-block-polymorphic `StoreKit.withLsRoCl lsmpl` transfer from Block `507`. -/
theorem tryDecryptPqV1_placed_ok_PTight_cli_rocl_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
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
        (tryDecryptRawSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)) := by
  have _ := instIsLsBlockProg_508 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact ls_subroutine_ok_rocl_of_block
    (tryDecryptPqV1_placed_ok_PTight_cli_of_tdEnv mmpl g W ctl hG hAesDec hSpqr hFmtWrite hFmtInner
      hRecv_ne hFmtWrite_ne hFmtInner_ne htd) hi

theorem tryDecryptPqV1_placed_ok_PTight_cli_rocl_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg
      (lsmpl.base 508)
      (withLsRoCl lsmpl
        (tryDecryptRawSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv))) :=
  tryDecryptPqV1_placed_ok_PTight_cli_rocl_of_tdEnv mmpl g W ctl hG hAesDec hSpqr hFmtWrite hFmtInner
    hRecv_ne hFmtWrite_ne hFmtInner_ne (fun _ _ h => h) hi

theorem tryDecryptPqV1_placed_ok_PTight_cli_rocl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg
      (lsmpl.base 508)
      (withLsRoCl lsmpl
        (tryDecryptRawSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))) := by
  have _ := instIsLsBlockProg_508 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact ls_subroutine_ok_rocl_of_block
    (tryDecryptPqV1_placed_ok_PTight_cli mmpl g W ctl hG hAesDec hSpqr) hi

/-- Envelope-monotonic caller-block-polymorphic `StoreKit.withLsCodeRoLoaded lsmpl` transfer from Block `507`. -/
theorem tryDecryptPqV1_placed_ok_PTight_cli_at_block_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
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
      (withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (tryDecryptPqV1_placed_ok_PTight_cli_rocl_of_tdEnv mmpl g W ctl hG hAesDec hSpqr hFmtWrite hFmtInner
      hRecv_ne hFmtWrite_ne hFmtInner_ne htd hi)

theorem tryDecryptPqV1_placed_ok_PTight_cli_at_block_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtWriteEnv fmtEnv : List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv))) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (tryDecryptPqV1_placed_ok_PTight_cli_rocl_ofEnv mmpl g W ctl hG hAesDec hSpqr hFmtWrite hFmtInner
      hRecv_ne hFmtWrite_ne hFmtInner_ne hi)

/-- Default `TryDecryptCliEnv` caller-block-polymorphic `StoreKit.withLsCodeRoLoaded lsmpl` transfer from Block `507`. -/
theorem tryDecryptPqV1_placed_ok_PTight_cli_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAt W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (tryDecryptPqV1_placed_ok_PTight_cli_rocl mmpl g W ctl hG hAesDec hSpqr hi)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget
