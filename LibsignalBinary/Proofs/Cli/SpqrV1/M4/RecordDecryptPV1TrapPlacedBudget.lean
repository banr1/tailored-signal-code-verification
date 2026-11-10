/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegExitPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegTailPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.DropsPlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedBudget
meta import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlacedBudget -- shake: keep
meta import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1Budget
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetStateBudget
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `try_decrypt_from_record` Region on CLI Block `463`

Defines the CLI record-decryption allocation-event envelopes (`RecordDecryptCliEnvOf`,
`RecordDecryptCliEnv`) and proves budget-threaded `region_ok` for `recordDecryptPlacedSpecTPTight`
(with `Spec.withVRegs`) on `lsProg_463` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  Crypto KeyPair Mut RatchetState TripleRatchet aesCbcDecrypt rootCreateChain
)
open CryptoVerification (
  LibsignalPlacement lsHandleErrorSym lsRustAllocSym lsRustDeallocSym
  lsRustNoAllocShimSym lsRustReallocSym ls_subroutine_ok_of_block lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.Cli.CoinsTape (cliTapeAt)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (
  LibsignalCodeRoLoaded cli_tapeAfter_tryDecrypt_entails ls_hook_ok_226
  recEntryPlaced recExitPlaced recFPCPlaced recFramePlaced recJPCPlaced
  recMPCPlaced recMetaPlaced recVPCPlaced
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463 lsProg_463)
open CryptoVerification.E2E (aesDecHookMallocng)
open CryptoVerification.LibsignalSessionRepr (ChainGhost msgTypeByte)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (
  RecordDecryptGhost SeedsLen32 SendCall SpqrModel TryDecryptGhost
  recordResultAt recordResultTag region_ok rootStack sessionShimSpec
  withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_434 blkPl_434)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.Model (
  fromSessionState_ok_inv model_of_aesDec_none model_of_aesDec_some
  model_of_cmk_error model_of_ensureReceiverChain_error
  model_of_fromSessionState_error model_of_recvPanics model_of_spqr_error
  model_of_verifyMac_false
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost SetSessionStateGhost logClosurePlacedSpec lsLogOff
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  sessionStateAt_eq_inline_sep_heap sessionStateAt_move_bytes_twice
)
open CryptoVerification.LibsignalTripleRatchet.Record (
  CloneRel recordOkRel_of_clone_dec regionOutcome region_ok_of_reaches
  region_reaches region_reaches_steps
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (
  closureStack_to_growStack decryptTarget dropLocal2Stack_to_rootStack
  eq_duplicatedMessage_of_isDupErr errsAt_nil_exists_intro errsAt_nil_unfold
  growStack_to_rootStack isDupErr memRegion48_eq_words6At memRegion_192_split48
  memRegion_5f0_join344 memRegion_5f0_split344 memRegion_5f0_split_b40
  mkTryDecryptGhost model_eq_of_version_eq model_err_of_tryDecrypt_err
  model_ok_of_tryDecrypt_ok model_panic_of_tryDecrypt_panic
  noPanic_onPanic_entails recordError_of_speTag_ne_speWord23
  segDecrypt_of_sepWP_placed segDecrypt_of_sepWP_ret_placed
  segDecrypt_replace_pre sessionStateAt_exists_intro
  sessionStateAt_ok_exists_intro setStack_to_rootStack speAt_decomp6
  speTag speTag_add2_ne_zero speTag_ne_speWord23_of_not_isDupErr
  spe_errsAt_entails stackAt_root_split_closure stackAt_root_split_dropLocal2
  stackAt_root_split_set words6At words6_4b0_to_memRegion words6_b40_to_memRegion
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts.SegDecryptRegReadSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost UuidParser coinsOf okTagVec protocolAddressAt serializeAddresses
  serviceIdParse sessionStateAt signalMessageAt speAt speWord utf8 uuidTryParse
  vecResultAt
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsFmtWriteSym lsFormatInnerSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_all cliGhostExterns_sat_of_cliExternsPlaced
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved rustAllocEvents rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  FmtWriteEnv FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec formatInnerBudgetEnvSpec
  withVmPreserved
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget (
  tryDecryptPlacedSpecP tryDecryptPlacedSpecQF_PTight
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget (
  recordDecryptPlacedSpecP recordDecryptPlacedSpecTF recordDecryptPlacedSpecTPTight
  recordDecryptPlacedSpecTPTightF
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget (
  CmkSeg4Env CmkStepEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (s8Env s9Env)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (
  TryDecryptCliEnv TryDecryptCliEnvOf envArgsToGhost
  tryDecryptV1_placed_ok_PTight_cli tryDecryptV1_placed_ok_PTight_cli_of_tdEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env vmacEvents)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  tryDecryptRawSpecTPTightAt tryDecryptSpecTPTightAt
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.DropsPlacedBudget (
  drop_session_structure_local2_placed_ok
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlacedBudget (
  chain_clone_placed_ok senderChain_clone_placed_ok
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget (
  FStatePlaced JStatePlaced MStatePlaced recordDecryptPlacedSpec
  tryDecryptPlacedSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  SegCloneHooks cliRecFramePlaced_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlacedBudget (
  TdEnvInhabited fitsEvents_segClone_of_recordDecryptEnv segClone_wp_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegExitPlacedBudget (segExit_placed_ok)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget (
  segMismatch_placed_ok sepWP_cut_here
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegTailPlacedBudget (segTail_placed_ok)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  cmkLoopAdvanceEvs_nonempty
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
  cliExternsPlaced_shim_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv spqrRecvBytesEnv_nonempty
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (AesDecCtEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (s3CommitDefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv s3EnvOf)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (tryDecryptOnPanicTight)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  SeamEnvsInhabited TrGhostCaps freeOnlyEvs_nil fromS2GenEnv_ne s1InitTrGhost
  seqEnv_append seqEnv_ne
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec growOneSpeSpec
  setSessionStateSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1Budget (
  drop_session_structure_local1_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget (
  grow_one_spe_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetStateBudget (
  set_session_state_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  chainCloneSpec senderChainCloneSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget (trApplyEnv_senderSome_mem)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromFEnv FromMEnv FromVEnv FromVPostTdEnv RecordDecryptEnv SeamBudget SegCloneEnv
  SegTailEnv TryDecryptEnvArgs recordTryDecryptEnvArgs segCloneEvents tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  errsAt_atState live_repAlloc protocolAddressAt_atState recordResultAt_atState
  sessionStateAt_atState signalMessageAt_atState
)

open scoped LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm ↓, local wp_norm ↓]
private theorem rdp_pc_6100_to_2128 (b : BitVec 64) :
    b + 6100#64 - - -3972#64 = b + 2128#64 := by
  rw [BitVec.neg_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

private theorem rdp_sepExists_errsAt_singleton_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (h : BitVec 64) :
    (∃∗ r, CryptoVerification.LibsignalTripleRatchet.Record.errsAt (A.atState lim st s) h [r]) =
      (∃∗ r, CryptoVerification.LibsignalTripleRatchet.Record.errsAt A.repAlloc h [r]) :=
  congrArg (fun f => ∃∗ r, f r) (funext fun r => errsAt_atState A lim st s h [r])

private theorem rdp_sepExists_errsAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (h : BitVec 64) :
    (∃∗ errs, CryptoVerification.LibsignalTripleRatchet.Record.errsAt (A.atState lim st s) h errs) =
      (∃∗ errs, CryptoVerification.LibsignalTripleRatchet.Record.errsAt A.repAlloc h errs) :=
  congrArg (fun f => ∃∗ errs, f errs) (funext fun errs => errsAt_atState A lim st s h errs)

private theorem rdp_sepExists2_sessionStateAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) (ss : BitVec 64) :
    (∃∗ G₂, ∃∗ st₂, sessionStateAt (A.atState lim st s) ss G₂ st₂) =
      (∃∗ G₂, ∃∗ st₂, sessionStateAt A.repAlloc ss G₂ st₂) :=
  congrArg (fun f => ∃∗ G₂, f G₂) (funext fun G₂ =>
    congrArg (fun f => ∃∗ st₂, f st₂) (funext fun st₂ => sessionStateAt_atState A lim st s ss G₂ st₂))

private theorem rdp_sepExists_ok_sessionStateAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ss : BitVec 64) (G₀ : SessionGhost) (mst : _) :
    (∃∗ G', ⌜G₀.AfterRecordDecrypt G'⌝ ∗ sessionStateAt (A.atState lim st s) ss G' mst) =
      (∃∗ G', ⌜G₀.AfterRecordDecrypt G'⌝ ∗ sessionStateAt A.repAlloc ss G' mst) :=
  congrArg (fun f => ∃∗ G', f G') (funext fun G' =>
    congrArg (⌜G₀.AfterRecordDecrypt G'⌝ ∗ ·) (sessionStateAt_atState A lim st s ss G' mst))

/-! ## 1. `VStatePPlaced` and `RecordDecryptCliEnv` -/

/-- Budget-threaded relocatable `VStatePlaced` with weakened pure identity guard `VStatePPlaced`. -/
def VStatePPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost)
    (R : SepProp) (s0 s : State) : Prop :=
  let A' := A.atState lim st s
  let sp := s0.sp
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st (FromVEnv tdEnv x G₁) ∧
  (s.pc = recVPCPlaced ∧ recMetaPlaced s0 s ∧
    ((x.st.remoteIdentity ≠ some x.st.localIdentity ∨
        CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid parse x.loc.name.bytes x.rem.name.bytes) ∧
      SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32) ∧
    CloneRel x.G G₁ ∧
    x.st.version.toNat = x.msg.messageVersion.toNat ∧
    (s.mem ⊨ recFramePlaced A' x sp ∗ sessionStateAt A' (sp + 0x138#64) x.G x.st ∗
      sessionStateAt A' (sp + 0xca0#64) G₁ x.st ∗
      CryptoVerification.LibsignalTripleRatchet.Record.errsAt A' (sp + 0x5d8#64) [] ∗
      memRegion (sp + 0x4b0#64) 48 ∗ cliTapeAt ctl x.cur x.rest ∗ R))

/-- Parametric CLI `try_decrypt_from_record` allocation-event envelope on `RecordDecryptGhost`. -/
abbrev RecordDecryptCliEnvOf (C : Crypto) (S : SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop) :
    RecordDecryptGhost → List AllocEvent → Prop :=
  RecordDecryptEnv (TryDecryptCliEnvOf C S fmtWriteEnv RecvBytesEnv fmtEnv)

/-- Default CLI `try_decrypt_from_record` allocation-event envelope at
    `(FmtWriteEnv, SpqrRecvBytesEnv, FormatInnerEnv)`. -/
abbrev RecordDecryptCliEnv (C : Crypto) (S : SpqrModel) :
    RecordDecryptGhost → List AllocEvent → Prop :=
  RecordDecryptEnv (TryDecryptCliEnv C S)

example (C : Crypto) (S : SpqrModel) (x : RecordDecryptGhost)
    (hne : x.st.version.toNat ≠ x.msg.messageVersion.toNat) :
    RecordDecryptCliEnv C S x
      (segCloneEvents x.G x.st ++
        (rustAllocEvents (4 * 48) 8 ++ (([] ++ rustAllocEvents 17 1) ++ []))) := by
  unfold RecordDecryptCliEnv RecordDecryptEnv
  simp only [hne, ↓reduceIte]
  have hgrow : GrowOneSpeEnv 0#64 (rustAllocEvents (4 * 48) 8) := Or.inl ⟨rfl, rfl⟩
  have htail : SegTailEnv ([] ++ rustAllocEvents 17 1) := SeqEnv.append FreeOnlyEvs.nil rfl
  have hfromF : FromFEnv (([] ++ rustAllocEvents 17 1) ++ []) :=
    SeqEnv.append htail FreeOnlyEvs.nil
  exact SeqEnv.append rfl (SeqEnv.append hgrow hfromF)

/-! ## 2. Envelope Inhabitedness & Segment Theorems (`segClone_placed_ok_P`, `rdp_segDecrypt_placed_ok_TPTight`) -/

private theorem rdp_cliSeamEnvs_inhabited (C : Crypto) (S : SpqrModel)
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
  s4 x _trG tr ck := by
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
  s3 x _trG tr := by
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

/-- `TryDecryptCliEnvOf` is inhabited on every version-matching `RecordDecryptGhost` input once
    its three external sub-envelopes are inhabited. -/
theorem tdEnvInhabited_tryDecryptCliEnvOf (C : Crypto) (S : SpqrModel)
    {fmtWriteEnv : List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (hFmtWrite_ne : ∃ evs, fmtWriteEnv evs)
    (hFmtInner_ne : ∃ evs, fmtEnv evs) :
    TdEnvInhabited (TryDecryptCliEnvOf C S fmtWriteEnv RecvBytesEnv fmtEnv) := by
  intro x _hver
  let a := recordTryDecryptEnvArgs x x.G
  have hcl : CloneRel x.G x.G := ⟨rfl, rfl, rfl, rfl⟩
  rcases htr : Mut.exec TripleRatchet.fromSessionState a.st with ⟨_ | tr0, st1⟩
  · refine ⟨x.G, [], hcl, ?_⟩
    unfold TryDecryptCliEnvOf
    change (match Mut.exec TripleRatchet.fromSessionState a.st with
      | (.error _, _) => FreeOnlyEvs
      | (.ok tr0, st1) => _) []
    rw [htr]
    exact FreeOnlyEvs.nil
  · obtain ⟨evs2, hevs2⟩ :=
      fromS2GenEnv_ne
        (rdp_cliSeamEnvs_inhabited C S hRecv_ne hFmtWrite_ne hFmtInner_ne)
        (envArgsToGhost a) (s1InitTrGhost a.G) tr0 st1
    refine ⟨x.G, [] ++ evs2, hcl, ?_⟩
    unfold TryDecryptCliEnvOf
    change (match Mut.exec TripleRatchet.fromSessionState a.st with
      | (.error _, _) => FreeOnlyEvs
      | (.ok tr0, st1) => _) ([] ++ evs2)
    rw [htr]
    exact SeqEnv.append FreeOnlyEvs.nil hevs2

/-- Default `TryDecryptCliEnv` satisfies `TdEnvInhabited`. -/
theorem tdEnvInhabited_tryDecryptCliEnv (C : Crypto) (S : SpqrModel) :
    TdEnvInhabited (TryDecryptCliEnv C S) :=
  tdEnvInhabited_tryDecryptCliEnvOf
    (fmtWriteEnv := FmtWriteEnv) (fmtEnv := FormatInnerEnv)
    C S spqrRecvBytesEnv_nonempty ⟨[], rfl⟩ ⟨[], rfl⟩

/-- Budget-threaded relocatable `[LibsignalPlacement]` clone segment theorem under weakened
    `recordDecryptPlacedSpecP` precondition and `TdEnvInhabited tdEnv`. -/
theorem segClone_placed_ok_P [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)}
    (htd_ne : TdEnvInhabited tdEnv)
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (hsenderClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    (hdrop1 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)))
    (x : RecordDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hpc : s0.pc = recEntryPlaced) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s0.mem) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s0 s' ∧
      ((∃ G₁ st, VStatePPlaced A lim ctl uuidTryParse tdEnv x st_init st G₁ R s0 s') ∨
       (∃ G₁ st, MStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s') ∨
       regionOutcome (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv)
         recExitPlaced (x, st_init) R s0 s') := by
  let _ := hdealloc
  let _ := hpanic
  let _ := hdrop1
  have hA : SegCloneHooks A lim H := ⟨hshim, halloc, hmemcpy⟩
  dsimp only [recEntryPlaced] at hpc
  dsimp only [recordDecryptPlacedSpecP,
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget.recordDecryptPlacedSpecP,
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfit_full, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfl, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hsp, h27, h19, h23, h24, hrem_ne, hseeds, hrc32, _⟩, hm⟩ := hpre
  rw [sessionStateAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, RustCliAllocBudget.atState_pool] at hm
  simp only [← sepConj_assoc] at hm
  have hfits_clone : FitsEvents M lim st_init (segCloneEvents x.G x.st) :=
    fitsEvents_segClone_of_recordDecryptEnv htd_ne hfit_full
  have hwp :=
    segClone_wp_placed (ctl := ctl) hA hchainClone hsenderClone x s0 hfits_clone
      hpc hrun hsp h27 h19 h23 h24 hrc32
  have hm_assoc : s0.mem ⊨
      (memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A.repAlloc (s0.sp + 0x138#64) x.G x.st ∗
        memRegion (s0.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool lim st_init s0) ∗ R :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  obtain ⟨sf, hsteps, hout⟩ := hwp hfl.1 R hm_assoc hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hspAf, hx29f, ⟨htrf, hvrf⟩, hx9f, hent⟩ |
      ⟨_, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · have hmeta : recMetaPlaced s0 sf :=
      ⟨hrunf, hspf, hspAf, hx29f, htrf,
       LibsignalCodeRoLoaded.of_keepsFrozen hfl hsteps.keepsFrozen, hvrf⟩
    have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf'
    obtain ⟨G₁, hmf'⟩ := hmf'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf'
    obtain ⟨hclone, hmf'⟩ := hmf'
    let st' := M.stepEvents (segCloneEvents x.G x.st) st_init
    by_cases hver : x.st.version.toNat = x.msg.messageVersion.toNat
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcV : sf.pc = recVPCPlaced := by simpa [recVPCPlaced] using hpcf
      have hseqV : ∀ e1 e2, SegCloneEnv x.G x.st e1 → FromVEnv tdEnv x G₁ e2 →
          RecordDecryptEnv tdEnv x (e1 ++ e2) := by
        intro e1 e2 he1 he2
        unfold RecordDecryptEnv
        simp only [hver, ↓reduceIte]
        exact ⟨G₁, hclone, SeqEnv.append he1 he2⟩
      have hsbV : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st' (FromVEnv tdEnv x G₁) :=
        (SeamBudget.init hfit_full).step hseqV rfl
      refine ⟨sf, hsteps, Or.inl ⟨G₁, st', hsbV, hpcV, hmeta, ⟨hrem_ne, hseeds, hrc32⟩,
        hclone, hver, ?_⟩⟩
      simpa only [sepConj_assoc] using hmf'
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcM : sf.pc = recMPCPlaced := by simpa [recMPCPlaced] using hpcf
      have hseqM : ∀ e1 e2, SegCloneEnv x.G x.st e1 → FromMEnv e2 →
          RecordDecryptEnv tdEnv x (e1 ++ e2) := by
        intro e1 e2 he1 he2
        unfold RecordDecryptEnv
        simp only [hver, ↓reduceIte]
        exact SeqEnv.append he1 he2
      have hsbM : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st' FromMEnv :=
        (SeamBudget.init hfit_full).step hseqM rfl
      refine ⟨sf, hsteps, Or.inr (Or.inl ⟨G₁, st', hsbM, hpcM, hmeta, hver, hx9f, ?_⟩)⟩
      simpa only [sepConj_assoc] using hmf'
  · have hfalse := Satisfies.mono (sepConj_mono_left hqp) hmf
    rw [satisfies_pure_sepConj] at hfalse
    exact False.elim hfalse.1
  · exact (not_satisfies_false_sepConj hoom).elim

private abbrev rdpTryBudgetSpecTrap [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
      ⌜FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x))⌝ ∗
      (⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
        s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
        (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
        (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
          CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidParse
            x.loc.name.bytes x.rem.name.bytes) ∧
        SeedsLen32 x.st ∧
        x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
      sessionStateAt (A.atState lim st s) x.ss x.G x.st ∗
      protocolAddressAt (A.atState lim st s) x.rem x.remA ∗
      protocolAddressAt (A.atState lim st s) x.loc x.locA ∗
      signalMessageAt (A.atState lim st s) x.msgG x.msgA x.msg ∗
      memRegion x.ret 48 ∗ cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗
      stackAt s.sp rootStack ∗ (A.atState lim st s).pool) ∗
      tokenInitPlacedAt ∗
      ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s.mem⌝
  post := fun (x, st) s0 sf =>
    (tryDecryptPlacedSpec C A lim ctl uuidParse S tdEnv).post (x, st) s0 sf ∗
      tokenInitPlacedAt
  onPanic := fun (x, _) s0 sf => tryDecryptOnPanicTight C S uuidParse x s0 sf

private theorem rdp_tryDecryptSpecTPTightAt_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    tryDecryptSpecTPTightAt C A lim ctl uuidParse S tdEnv =
      rdpTryBudgetSpecTrap C A lim ctl uuidParse S tdEnv := by
  dsimp only [tryDecryptSpecTPTightAt, withLsCodeRoLoaded, tryDecryptRawSpecTPTightAt,
    tryDecryptPlacedSpecQF_PTight, tryDecryptPlacedSpecP,
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP,
    rdpTryBudgetSpecTrap]
  congr 1
  · funext p s; sep_ac_rfl
  · funext p s0 sf; sep_ac_rfl

private theorem rdp_tryDecrypt_onPanic_entails_tight_b {C : Crypto} {S : SpqrModel}
    {x : RecordDecryptGhost} {G₁ : SessionGhost}
    {s0 s sf : State} {F : SepProp} {sp : BitVec 64}
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    (htr : s.trace = s0.trace) :
    tryDecryptOnPanicTight C S uuidTryParse (mkTryDecryptGhost sp x G₁) s sf ∗ F ⊢
      ⌜(x.model C S uuidTryParse).1 = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  dsimp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hpan, hpref⟩ => ?_
  rw [htr] at hpref
  exact Entails.pure_right
    ⟨model_panic_of_tryDecrypt_panic C S sp x G₁ heq hpan, hpref⟩ (entails_anyHeap _)

private theorem rdp_seg_of_sepWPp_JF_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_463).rebase (blkPl_463).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (∃ st', JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st'
          (tokenInitPlacedAt ∗ R) s0 sf) ∨
        (∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st'
          (tokenInitPlacedAt ∗ R) s0 sf))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv).onPanic
          (x, st_init) s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      ((∃ st', JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st'
          (tokenInitPlacedAt ∗ R) s0 s') ∨
       (∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st'
          (tokenInitPlacedAt ∗ R) s0 s') ∨
       regionOutcome (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)
         recExitPlaced (x, st_init) R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 3200000 in
/-- Budget-threaded relocatable `[LibsignalPlacement]` `SegDecrypt` theorem on Block `463` with
    tight `onPanic` (`recordDecryptPlacedSpecTPTight`). -/
theorem rdp_segDecrypt_placed_ok_TPTight [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)}
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv)))
    (hset : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)))
    (hdrop2 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hgrow : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec)))
    (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost)
    (R : SepProp) (s0 s : State)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hV : VStatePPlaced A lim ctl uuidTryParse tdEnv x st_init st G₁
      (tokenInitPlacedAt ∗ R) s0 s)
    (hstk : rootStack ≤ s0.sp.toNat)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      ((∃ st', JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st'
          (tokenInitPlacedAt ∗ R) s0 s') ∨
       (∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st'
          (tokenInitPlacedAt ∗ R) s0 s') ∨
       regionOutcome (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)
         recExitPlaced (x, st_init) R s0 s') := by
  have htry_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (rdpTryBudgetSpecTrap C A lim ctl uuidTryParse S tdEnv)) :=
    rdp_tryDecryptSpecTPTightAt_eq C A lim ctl uuidTryParse S tdEnv ▸ htd
  have _ := hQ
  rcases hV with ⟨hsb, hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfl, hvregs⟩,
    ⟨hrem_or_dist, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  dsimp only [recVPCPlaced] at hpc
  have hmemcpy_rel := ls_hook_ok_226 (by decide) hmemcpy
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  have hfit_td : FitsEnv M lim st (tdEnv (tryDecryptEnvArgs (mkTryDecryptGhost s.sp x G₁))) :=
    hsb.1.seq_left
  rw [hsp0] at hstk hmem
  rw [cliRecFramePlaced_atState, sessionStateAt_atState, sessionStateAt_atState,
    errsAt_atState] at hmem
  unfold recFramePlaced at hmem
  rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp] at hmem
  simp only [← sepConj_assoc] at hmem
  apply rdp_seg_of_sepWPp_JF_placed hmem hL
    (target := decryptTarget (blkPl_463).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_placed hfl (mid := lsmpl.base 434)
  apply sepWP_cut_here (mid := lsmpl.base 434)
  by_vm_open (
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨by wp_norm_lhs, fun _hvm => ?_⟩
  refine SepWP.transport_budgetPool _hvm (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_463).base + bv% (1720)) |>.setPC
      (lsmpl.base 434)).sp.toNat := hstk
  have hfit_td1 : FitsEnv M lim st
      (tdEnv (tryDecryptEnvArgs
        { ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
          rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
          msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
          cur := x.cur, rest := x.rest })) := hfit_td
  cli_segDecrypt_wpp_call_b htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }, st) hF1
    (rdp_tryDecrypt_onPanic_entails_tight_b heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro evs_td
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨hevs_td, ⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hevs_td hnpan hdec ⊢
  have hsb₁ : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
      (M.stepEvents evs_td st) FromVPostTdEnv :=
    hsb.step (fun _ _ => SeqEnv.append) hevs_td
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · have hsb_M : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
          (M.stepEvents evs_td st) FromMEnv :=
        hsb₁.weaken (fun _ h => Or.inr h)
      have hfit_grow : FitsEnv M lim (M.stepEvents evs_td st) (GrowOneSpeEnv 0#64) :=
        hsb_M.1.seq_left
      have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 462)
      refine segDecrypt_replace_pre
        (speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A.repAlloc s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      apply sepWP_cut_here (mid := (blkPl_463).base + 5992#64)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWP.transport_budgetPool (s1 := sf) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
      apply sepWP_cut_here (mid := lsmpl.base 462)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_b hclosure () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 42)
      segDecrypt_wp_extract_exists
      rename_i hcl
      refine SepWP.transport_budgetPool hcl.1 (hnext := ?_)
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      apply sepWP_cut_here (mid := lsmpl.base 42)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      cli_segDecrypt_wpp_call_b hgrow
        ((s.sp + 0x5d8#64, 0#64, 8#64, []), M.stepEvents evs_td st) hF3
        noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_2
      segDecrypt_wp_extract_exists
      rename_i evs_grow p' hgrow_post
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      apply sepWP_cut_here (mid := (blkPl_463).base + 2128#64)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      rw [hsp_sf_1, live_repAlloc A]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A.repAlloc s.sp p' e tag w1 w2 w3 w4 w5 H_spe hgrow_post.2.1 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A.repAlloc (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4 hmf
      right
      refine ⟨M.stepEvents evs_grow (M.stepEvents evs_td st),
        hsb_M.step (fun _ _ => SeqEnv.append) hgrow_post.1.2,
        by dsimp only [recFPCPlaced]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hgrow_post.1.1, hcl.2, htr_sf, htr],
                hF4,
                by simp only [wp_norm, arm64_norm, *]⟩
      · rw [hsp0, cliRecFramePlaced_atState, sessionStateAt_atState,
          rdp_sepExists2_sessionStateAt_atState, rdp_sepExists_errsAt_singleton_atState]
        unfold recFramePlaced
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )))
    · have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
          (M.stepEvents evs_td st) FreeOnlyEvs :=
        hsb₁.weaken (fun _ h => Or.inl h)
      obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 442)
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      apply sepWP_cut_here (mid := lsmpl.base 442)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_b hdrop2
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost },
         M.stepEvents evs_td st)
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i evs_drop hevs_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨M.stepEvents evs_drop (M.stepEvents evs_td st),
        hsb_free.step (fun _ _ => FreeOnlyEvs.append) hevs_drop.2,
        by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hevs_drop.1, htr_sf, htr],
                hF3,
                by simp only [wp_norm, arm64_norm, *]⟩
      · rw [hsp0, hmodel_dup1, cliRecFramePlaced_atState, sessionStateAt_atState,
          recordResultAt_atState, rdp_sepExists_errsAt_atState]
        unfold recFramePlaced
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )
  · have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
        (M.stepEvents evs_td st) FreeOnlyEvs :=
      hsb₁.weaken (fun _ h => Or.inl h)
    dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.ρ "memcpy")
    rw [sessionStateAt_eq_inline_sep_heap A.repAlloc (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp]
    unfold lsLogOff
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    apply sepWP_cut_here (mid := (blkPl_463).base + 1736#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWP.transport_budgetPool (s1 := sf) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
    apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    cli_segDecrypt_wpp_call_b hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 48)
    segDecrypt_wp_extract_exists
    rename_i hmc
    first
      | refine SepWP.transport_budgetPool hmc.1 (hnext := ?_)
      | (have hvm_mc : VmPreserved sf sf_1 :=
           VmPreserved.trans (by simp only [wp_norm, arm64_norm]) hmc.1
         refine SepWP.transport_budgetPool hvm_mc (hnext := ?_))
    apply sepWP_cut_here (mid := lsmpl.base 48)
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    cli_segDecrypt_wpp_call_b hset
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost },
       M.stepEvents evs_td st) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_placed hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i evs_set hevs_set
    apply sepWP_cut_here (mid := (blkPl_463).base + 7820#64)
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    rw [hsp_sf_1]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A.repAlloc (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A.repAlloc (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨M.stepEvents evs_set (M.stepEvents evs_td st),
      hsb_free.step (fun _ _ => FreeOnlyEvs.append) hevs_set.2.1,
      by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, hevs_set.1, hmc.2.2, htr_sf, htr],
              hF4,
              by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0, hmodel_ok1, hmodel_ok2, cliRecFramePlaced_atState, recordResultAt_atState,
        rdp_sepExists_ok_sessionStateAt_atState, rdp_sepExists_errsAt_atState]
      unfold recFramePlaced lsLogOff
      rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
    )))
  )

/-! ## 3. Top-Level Placed Region Assembly (`recordDecryptV1_placed_region_vregs_ok_PTight_cli`) -/

private def rdpNoPanicPlaced (S : SpqrModel) : SpqrModel :=
  { S with recvPanics := fun _ _ => false }

private theorem rdp_tryModel_noPanic_or_panic_placed (C : Crypto) (S : SpqrModel)
    (y : TryDecryptGhost) :
    y.model C (rdpNoPanicPlaced S) uuidTryParse = y.model C S uuidTryParse ∨
      (y.model C S uuidTryParse).1 = .error .panic := by
  rcases htr : Mut.exec TripleRatchet.fromSessionState y.st with ⟨e | tr, st1⟩
  · left
    rw [(model_of_fromSessionState_error (S := rdpNoPanicPlaced S) htr).1,
      (model_of_fromSessionState_error (S := S) htr).1]
  · rcases herc :
        Mut.exec (RatchetState.ensureReceiverChain C y.msg.senderRatchetKey (coinsOf y.rest))
          tr.ratchet with ⟨e | ck, r1⟩
    · left
      rw [model_of_ensureReceiverChain_error (S := rdpNoPanicPlaced S) htr herc,
        model_of_ensureReceiverChain_error (S := S) htr herc]
    · rcases hcmk :
          Mut.exec
            (RatchetState.consumeMessageKey C.F y.msg.senderRatchetKey ck y.msg.counter y.msgType)
            r1 with ⟨e | mkg, r2⟩
      · left
        rw [model_of_cmk_error (S := rdpNoPanicPlaced S) htr herc hcmk,
          model_of_cmk_error (S := S) htr herc hcmk]
      · have hpq : tr.pqrState = y.st.pqRatchetState :=
          (fromSessionState_ok_inv htr).2.2.1
        cases hp : S.recvPanics y.st.pqRatchetState y.msg.pqRatchet
        · left
          have hnp : S.recvPanics tr.pqrState y.msg.pqRatchet = false := hpq ▸ hp
          have hnp' : (rdpNoPanicPlaced S).recvPanics tr.pqrState y.msg.pqRatchet = false := rfl
          rcases hspqr : S.recv tr.pqrState y.msg.pqRatchet with sd | ⟨newPqrState, pqrKey⟩
          · rw [model_of_spqr_error (S := rdpNoPanicPlaced S) htr herc hcmk hspqr hnp',
              model_of_spqr_error (S := S) htr herc hcmk hspqr hnp]
          · cases hmac :
                y.msg.verifyMacWithAddresses C.F
                  (serializeAddresses (serviceIdParse uuidTryParse) y.rem y.loc)
                  tr.remoteIdentityKey tr.localIdentityKey
                  (mkg.generateKeys C.F pqrKey).macKey
            · rw [model_of_verifyMac_false (S := rdpNoPanicPlaced S)
                  htr herc hcmk hspqr hmac hnp',
                model_of_verifyMac_false (S := S) htr herc hcmk hspqr hmac hnp]
            · cases haes :
                  aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                    (mkg.generateKeys C.F pqrKey).iv y.msg.ciphertext
              · rw [model_of_aesDec_none (S := rdpNoPanicPlaced S)
                    htr herc hcmk hspqr hmac haes hnp',
                  model_of_aesDec_none (S := S) htr herc hcmk hspqr hmac haes hnp]
              · rw [model_of_aesDec_some (S := rdpNoPanicPlaced S)
                    htr herc hcmk hspqr hmac haes hnp',
                  model_of_aesDec_some (S := S) htr herc hcmk hspqr hmac haes hnp]
        · right
          exact model_of_recvPanics htr herc hcmk hp

private theorem rdp_model_noPanic_or_panic_placed (C : Crypto) (S : SpqrModel)
    (x : RecordDecryptGhost) :
    x.model C (rdpNoPanicPlaced S) uuidTryParse = x.model C S uuidTryParse ∨
      (x.model C S uuidTryParse).1 = .error .panic := by
  by_cases heq : x.st.version.toNat = x.msg.messageVersion.toNat
  · rw [model_eq_of_version_eq C (rdpNoPanicPlaced S) 0#64 x x.G heq]
    rcases rdp_tryModel_noPanic_or_panic_placed C S (mkTryDecryptGhost 0#64 x x.G) with h | hpan
    · left
      rw [h, ← model_eq_of_version_eq C S 0#64 x x.G heq]
    · right
      exact model_panic_of_tryDecrypt_panic C S 0#64 x x.G heq hpan
  · left
    dsimp [RecordDecryptGhost.model, CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord,
      Mut.exec, StateT.run, ExceptT.run, ExceptT.mk, pure, Except.pure, Bind.bind, Monad.toBind,
      ExceptT.bind, ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, StateT.lift, throw, throwThe, MonadExceptOf.throw]
    simp [heq]

private theorem rdp_spec_S_exists_placed (C : Crypto) (S : SpqrModel) (x : RecordDecryptGhost) :
    ∃ S' : SpqrModel,
      x.model C S' uuidTryParse = x.model C S uuidTryParse ∧
      (((x.model C S' uuidTryParse).1 = .error .panic ∨
          (x.st.version.toNat = x.msg.messageVersion.toNat ∧
            S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet)) →
        (x.model C S uuidTryParse).1 = .error .panic) := by
  rcases rdp_model_noPanic_or_panic_placed C S x with hmod_eq | hmod_pan
  · refine ⟨rdpNoPanicPlaced S, hmod_eq, fun h => ?_⟩
    rcases h with hp | ⟨_, hpan⟩
    · exact hmod_eq ▸ hp
    · exact nomatch hpan
  · exact ⟨S, rfl, fun _ => hmod_pan⟩

private theorem rdp_JStatePlaced_eq_of_model_eq [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S' S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {st_init st : M.σ} {R : SepProp} {s0 s : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    JStatePlaced C A lim ctl uuidTryParse S' tdEnv x st_init st R s0 s =
      JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st R s0 s := by
  dsimp only [JStatePlaced, CryptoVerification.Cli.LibsignalTripleRatchet.Record.JStatePlaced]
  rw [hmod]

private theorem rdp_FStatePlaced_eq_of_model_eq [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S' S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {st_init st : M.σ} {R : SepProp} {s0 s : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    FStatePlaced C A lim ctl uuidTryParse S' tdEnv x st_init st R s0 s =
      FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st R s0 s := by
  dsimp only [FStatePlaced, CryptoVerification.Cli.LibsignalTripleRatchet.Record.FStatePlaced]
  rw [hmod]

private theorem rdp_post_eq_of_model_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S' S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {st_init : M.σ} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    (recordDecryptPlacedSpec C A lim ctl uuidTryParse S' tdEnv).post (x, st_init) s0 sf =
      (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).post (x, st_init) s0 sf := by
  dsimp only [recordDecryptPlacedSpec,
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec]
  rw [hmod]

private theorem rdp_regionOutcome_of_tokenFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S' S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse)
    (hpan_imp : ((x.model C S' uuidTryParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet)) →
      (x.model C S uuidTryParse).1 = .error .panic)
    (hout : regionOutcome (recordDecryptPlacedSpec C A lim ctl uuidTryParse S' tdEnv)
      recExitPlaced (x, st_init) (tokenInitPlacedAt ∗ R) s0 sf) :
    regionOutcome (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)
      recExitPlaced (x, st_init) R s0 sf := by
  rcases hout with ⟨hpc, hrun, hvregs, hpost⟩ | ⟨hpan, hpost⟩
  · left
    refine ⟨hpc, hrun, hvregs, ?_⟩
    rw [rdp_post_eq_of_model_eq_placed hmod] at hpost
    dsimp only [recordDecryptPlacedSpecTPTight, recordDecryptPlacedSpecTPTightF,
      recordDecryptPlacedSpecTF]
    have heq :
        (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).post (x, st_init) s0 sf ∗
          (tokenInitPlacedAt ∗ R) =
        (tokenInitPlacedAt ∗
          (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).post (x, st_init) s0 sf) ∗ R := by
      sep_ac_rfl
    exact heq ▸ hpost
  · right
    refine ⟨hpan, ?_⟩
    dsimp only [recordDecryptPlacedSpec] at hpost
    dsimp only [recordDecryptPlacedSpecTPTight, recordDecryptPlacedSpecTPTightF]
    have hassoc :
        (⌜((x.model C S' uuidTryParse).1 = .error .panic ∨
            (x.st.version.toNat = x.msg.messageVersion.toNat ∧
              S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true)) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ (tokenInitPlacedAt ∗ R) =
        (⌜((x.model C S' uuidTryParse).1 = .error .panic ∨
            (x.st.version.toNat = x.msg.messageVersion.toNat ∧
              S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true)) ∧
          s0.trace <+: sf.trace⌝ ∗ (anyHeap ∗ tokenInitPlacedAt)) ∗ R := by sep_ac_rfl
    rw [hassoc] at hpost
    refine Satisfies.mono (sepConj_mono_left (Entails.pure_left fun ⟨hp, htr⟩ => ?_)) hpost
    exact Entails.pure_right ⟨hpan_imp hp, htr⟩ (entails_anyHeap _)

private theorem rdp_regionOutcome_of_specP_tokenFrame_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S' S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse)
    (hpan_imp : ((x.model C S' uuidTryParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet)) →
      (x.model C S uuidTryParse).1 = .error .panic)
    (hout : regionOutcome (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S' tdEnv)
      recExitPlaced (x, st_init) (tokenInitPlacedAt ∗ R) s0 sf) :
    regionOutcome (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)
      recExitPlaced (x, st_init) R s0 sf :=
  rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout

private theorem rdp_rootStack_le_of_recordPlacedPreP [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (recordDecryptPlacedSpecP C A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) :
    rootStack ≤ s0.sp.toNat := by
  dsimp only [recordDecryptPlacedSpecP,
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget.recordDecryptPlacedSpecP]
    at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre2 := hpre.2
  simp only [CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecP,
    sepConj_assoc, satisfies_pure_sepConj] at hpre2
  exact hpre2.2.1.2.2.2.2.2.2.2.2

private theorem rdp_hookSat_noAllocShim_of_sessionShim {H : String → Option (State → State)}
    (h : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionShimBudgetSpec, sessionShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- Parametric `[LibsignalPlacement]` `region_reaches` for `recordDecryptPlacedSpecTPTight` on
    Block `463` under `TdEnvInhabited tdEnv`. -/
theorem rdp_region_reaches_placed_TPTight [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd_ne : TdEnvInhabited tdEnv)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    ∀ (x : RecordDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced →
      s0.status = .Running →
      (s0.mem ⊨
        (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R) →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)
        recExitPlaced (x, st_init) R s0 s0 := by
  have _ := CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463 H
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434 H
  have hchainClone :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (chain_clone_placed_ok hshim halloc hmemcpy))
  have hsenderClone :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (senderChain_clone_placed_ok hshim halloc hmemcpy))
  have hdrop1 :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (drop_session_structure_local1_placed_ok hdealloc)
  have hdropLocal2 :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (drop_session_structure_local2_placed_ok hdealloc)
  have hsetState :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (set_session_state_placed_ok hmemcpy (drop_session_structure_local1_placed_ok hdealloc))
  have hgrowSpe :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (grow_one_spe_placed_ok (rdp_hookSat_noAllocShim_of_sessionShim hshim) halloc hrealloc)
  have htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H) (j := 434)
      (subroutine_ok_withLsCodeLoaded_of_plain hTry)
  intro x st_init R s0 hpc hst hpre hL
  obtain ⟨S', hmod, hpan_imp⟩ := rdp_spec_S_exists_placed C S x
  dsimp only [recordDecryptPlacedSpecTPTight, recordDecryptPlacedSpecTPTightF,
    recordDecryptPlacedSpecTF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨
      (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S' tdEnv).pre (x, st_init) s0 ∗
      (tokenInitPlacedAt ∗ R) := by
    change s0.mem ⊨
      (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗
      (tokenInitPlacedAt ∗ R)
    have heq :
        (tokenInitPlacedAt ∗
          (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0) ∗ R =
        (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗
          (tokenInitPlacedAt ∗ R) := by sep_ac_rfl
    exact heq ▸ hpre
  have hstk : rootStack ≤ s0.sp.toNat := rdp_rootStack_le_of_recordPlacedPreP hpre'
  have hJ : ∀ s st',
      JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' (tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)
        recExitPlaced (x, st_init) R s0 s := by
    intro s st' hs hLs
    rw [← rdp_JStatePlaced_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hout⟩ :=
      segExit_placed_ok (C := C) (A := A) (lim := lim) (ctl := ctl)
        (S := S') (tdEnv := tdEnv) (H := H)
        hdealloc x st_init st' (tokenInitPlacedAt ∗ R) s0 s hs hLs
    exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  have hF : ∀ s st',
      FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' (tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)
        recExitPlaced (x, st_init) R s0 s := by
    intro s st' hs hLs
    rw [← rdp_FStatePlaced_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hnext⟩ :=
      segTail_placed_ok (C := C) (A := A) (lim := lim) (ctl := ctl)
        (S := S') (tdEnv := tdEnv) (H := H)
        hshim halloc hpanic hdropLocal2
        x st_init st' (tokenInitPlacedAt ∗ R) s0 s hs hLs
    rcases hnext with ⟨st'', hj⟩ | hout
    · rw [rdp_JStatePlaced_eq_of_model_eq hmod] at hj
      exact region_reaches_steps hst' (hJ s' st'' hj) hLs
    · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    segClone_placed_ok_P (C := C) (A := A) (lim := lim) (ctl := ctl) (S := S') (tdEnv := tdEnv)
      htd_ne hshim halloc hdealloc hmemcpy hpanic hchainClone hsenderClone hdrop1
      x st_init (tokenInitPlacedAt ∗ R) s0 hpc hst hpre' hL
  rcases hnext with ⟨G₁, st₁, hv⟩ | ⟨G₁, st₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ :=
      rdp_segDecrypt_placed_ok_TPTight hmemcpy htd
        hsetState hdropLocal2 hgrowSpe hclosure x st_init st₁ G₁ R s0 s' hQ hv hstk
        (hst'.codeLoaded hL)
    rcases hnext' with ⟨st₂, hj⟩ | ⟨st₂, hf⟩ | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' st₂ hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' st₂ hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ :=
      segMismatch_placed_ok (C := C) (A := A) (lim := lim) (ctl := ctl)
        (S := S') (tdEnv := tdEnv) (H := H)
        hgrowSpe hclosure x st_init st₁ G₁ (tokenInitPlacedAt ∗ R) s0 s' hm (hst'.codeLoaded hL)
    rcases hnext' with ⟨st₂, hf⟩ | hout
    · rw [rdp_FStatePlaced_eq_of_model_eq hmod] at hf
      exact region_reaches_steps (hst'.trans hst'') (hF s'' st₂ hf) hL
    · exact ⟨s'', hst'.trans hst'', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  · exact ⟨s', hst', rdp_regionOutcome_of_specP_tokenFrame_placed hmod hpan_imp hout⟩

/-- Parametric `[LibsignalPlacement]` `region_ok` for `recordDecryptPlacedSpecTPTight` on Block `463`. -/
theorem recordDecrypt_placed_region_ok_TPTight [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd_ne : TdEnvInhabited tdEnv)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv) :=
  region_ok_of_reaches ( fun ⟨x, st_init⟩ R s0 hpc hst hpre =>
    rdp_region_reaches_placed_TPTight C A lim ctl S tdEnv htd_ne H
      hshim halloc hrealloc hdealloc hmemcpy hpanic hTry hclosure x st_init R s0 hpc hst hpre )

/-- Parametric `[LibsignalPlacement]` `region_ok` with `Spec.withVRegs` on Block `463`. -/
theorem recordDecrypt_placed_region_vregs_ok_TPTight [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd_ne : TdEnvInhabited tdEnv)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv).withVRegs := by
  intro ⟨x, st_init⟩ R s0 hpc hst hpre hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', hvregs, hpost⟩ | hpan⟩ :=
    rdp_region_reaches_placed_TPTight C A lim ctl S tdEnv htd_ne H
      hshim halloc hrealloc hdealloc hmemcpy hpanic hTry hclosure x st_init R s0 hpc hst hpre hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', ?_⟩⟩
    dsimp only [Spec.withVRegs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvregs, hpost⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Envelope-monotonic placed CLI `region_ok` with `Spec.withVRegs` on
    `lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W))`
    for any inhabited `tdEnv` containing `TryDecryptCliEnvOf`. -/
theorem recordDecryptV1_placed_region_vregs_ok_PTight_cli_of_tdEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
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
      tdEnv a evs)
    (hclosure : subroutine_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
        (spqrV1 W.C.F W.Q.K) tdEnv).withVRegs :=
  have htd_ne : TdEnvInhabited tdEnv := fun x hver =>
    let ⟨G₁, evs, hcl, he⟩ :=
      tdEnvInhabited_tryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K)
        hRecv_ne hFmtWrite_ne hFmtInner_ne x hver
    ⟨G₁, evs, hcl, htd _ _ he⟩
  recordDecrypt_placed_region_vregs_ok_TPTight
    W.C A lim ctl (spqrV1 W.C.F W.Q.K) tdEnv htd_ne
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_panic_all mmpl g W lsHandleErrorSym (by decide))
    (tryDecryptV1_placed_ok_PTight_cli_of_tdEnv mmpl g W ctl hG hAesDec hSpqr
      hFmtWrite hFmtInner hRecv_ne hFmtWrite_ne hFmtInner_ne htd)
    hclosure

/-- Envelope-parametric placed CLI `region_ok` with `Spec.withVRegs` on
    `lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W))` at `TryDecryptCliEnvOf`. -/
theorem recordDecryptV1_placed_region_vregs_ok_PTight_cli_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
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
    (hFmtInner_ne : ∃ evs, fmtEnv evs)
    (hclosure : subroutine_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
        (TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv)).withVRegs :=
  recordDecryptV1_placed_region_vregs_ok_PTight_cli_of_tdEnv mmpl g W ctl hG hAesDec hSpqr
    hFmtWrite hFmtInner hRecv_ne hFmtWrite_ne hFmtInner_ne (fun _ _ h => h) hclosure

/-- Concrete placed CLI `region_ok` with `Spec.withVRegs` on
    `lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W))` at
    `S := spqrV1 W.C.F W.Q.K` and `tdEnv := TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)`. -/
theorem recordDecryptV1_placed_region_vregs_ok_PTight_cli [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W)
    (hclosure : subroutine_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
        (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))).withVRegs :=
  recordDecrypt_placed_region_vregs_ok_TPTight
    W.C A lim ctl (spqrV1 W.C.F W.Q.K)
    (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))
    (tdEnvInhabited_tryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_panic_all mmpl g W lsHandleErrorSym (by decide))
    (tryDecryptV1_placed_ok_PTight_cli mmpl g W ctl hG hAesDec hSpqr)
    hclosure

set_option maxHeartbeats 3200000 in
private theorem rdp_region_reaches_full_placed_TPTight [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd_ne : TdEnvInhabited tdEnv)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv)) :
    ∀ (x : RecordDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced →
      s0.status = .Running →
      (s0.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)).pre (x, st_init) s0 ∗ R) →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv))
        recExitPlaced (x, st_init) R s0 s0 := by
  have _ := CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463 H
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434 H
  have hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (withVmPreserved logClosurePlacedSpec)) :=
    LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureVmPlacedBudget.log_closure_coins_frozen_vm_placed_ok_of_block
      (callerProg := (blkPC_463).rebase (blkPl_463).base H)
  have hchainClone :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (chain_clone_placed_ok hshim halloc hmemcpy))
  have hsenderClone :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (senderChain_clone_placed_ok hshim halloc hmemcpy))
  have hdrop1 :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (drop_session_structure_local1_placed_ok hdealloc)
  have hdropLocal2 :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (drop_session_structure_local2_placed_ok hdealloc)
  have hsetState :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (set_session_state_placed_ok hmemcpy (drop_session_structure_local1_placed_ok hdealloc))
  have hgrowSpe :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (grow_one_spe_placed_ok (rdp_hookSat_noAllocShim_of_sessionShim hshim) halloc hrealloc)
  have htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H) (j := 434)
      (subroutine_ok_withLsCodeLoaded_of_plain hTry)
  have hSegDec : ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost)
      (R : SepProp) (s0 s : State)
      (hQ : x.st.pqRatchetState.length < 2 ^ 32)
      (hV : VStatePPlaced A lim ctl uuidTryParse tdEnv x st_init st G₁
        (tokenInitPlacedAt ∗ R) s0 s)
      (hstk : rootStack ≤ s0.sp.toNat)
      (hFroz : CryptoVerification.LibsignalFrozen lsmpl s.mem)
      (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem),
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        ((∃ st', JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st'
            (tokenInitPlacedAt ∗ R) s0 s') ∨
         (∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st'
            (tokenInitPlacedAt ∗ R) s0 s') ∨
         regionOutcome (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)
           recExitPlaced (x, st_init) R s0 s') := by
    intro x st_init st G₁ R s0 s hQ hV hstk hFroz hL
    have hgrow := hgrowSpe
    have hdrop2 := hdropLocal2
    have hset := hsetState
    have htry_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
        (withLsCodeLoaded lsmpl (rdpTryBudgetSpecTrap C A lim ctl uuidTryParse S tdEnv)) :=
      rdp_tryDecryptSpecTPTightAt_eq C A lim ctl uuidTryParse S tdEnv ▸ htd
    have _ := hQ
    rcases hV with ⟨hsb, hpc, ⟨hrun, hsp, hsp_align, hx29, htr, _hfl, hvregs⟩,
      ⟨hrem_or_dist, hseeds, hrc_len⟩, hclone, heq, hmem⟩
    dsimp only [recVPCPlaced] at hpc
    have hmemcpy_rel := ls_hook_ok_226 (by decide) hmemcpy
    have hsp0 : s0.sp = s.sp := hsp.symm
    clear hsp
    have hfit_td : FitsEnv M lim st (tdEnv (tryDecryptEnvArgs (mkTryDecryptGhost s.sp x G₁))) :=
      hsb.1.seq_left
    rw [hsp0] at hstk hmem
    rw [cliRecFramePlaced_atState, sessionStateAt_atState, sessionStateAt_atState,
      errsAt_atState] at hmem
    unfold recFramePlaced at hmem
    rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp] at hmem
    simp only [← sepConj_assoc] at hmem
    apply rdp_seg_of_sepWPp_JF_placed hmem hL
      (target := decryptTarget (blkPl_463).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
    apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hFroz (mid := lsmpl.base 434)
    apply sepWP_cut_here (mid := lsmpl.base 434)
    by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      ⟨by wp_norm_lhs, fun _hvm => ?_⟩
    refine SepWP.transport_budgetPool _hvm (hnext := ?_)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF1
    have hsp_bound1 : rootStack ≤
        ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
                (Reg.gpr 3#5) x.locA).writeReg64
              (Reg.gpr 4#5) x.msgA).writeReg64
            (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
          (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
        (Reg.gpr 5#5) 2#64).writeReg64
      (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_463).base + bv% (1720)) |>.setPC
        (lsmpl.base 434)).sp.toNat := hstk
    have hfit_td1 : FitsEnv M lim st
        (tdEnv (tryDecryptEnvArgs
          { ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
            rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
            msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
            cur := x.cur, rest := x.rest })) := hfit_td
    cli_segDecrypt_wpp_call_lsfull_b htry_rel
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }, st) hF1
      (rdp_tryDecrypt_onPanic_entails_tight_b heq (by simp only [wp_norm, arm64_norm, htr]))
    apply SepWPp.exists_elim
    intro evs_td
    apply SepWPp.exists_elim
    intro G₂
    apply SepWPp.pure_elim
    rintro ⟨hevs_td, ⟨hnpan, htr_sf⟩, hdec⟩
    have hmk :
        ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
           rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
           msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
           cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
    rw [hmk] at hevs_td hnpan hdec ⊢
    have hsb₁ : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
        (M.stepEvents evs_td st) FromVPostTdEnv :=
      hsb.step (fun _ _ => SeqEnv.append) hevs_td
    rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
    · dsimp only [decryptTarget, vecResultAt]
      have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
      cases hdup : isDupErr e
      · have hsb_M : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
            (M.stepEvents evs_td st) FromMEnv :=
          hsb₁.weaken (fun _ h => Or.inr h)
        have hfit_grow : FitsEnv M lim (M.stepEvents evs_td st) (GrowOneSpeEnv 0#64) :=
          hsb_M.1.seq_left
        have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
        have hmodel_err : x.model C S uuidTryParse =
            (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
          rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
            recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
        have hmodel_err1 : (x.model C S uuidTryParse).1 =
            .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
        have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
        have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
        apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.base 462)
        refine segDecrypt_replace_pre
          (speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
        rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
          stackAt_root_split_closure s.sp, errsAt_nil_unfold A.repAlloc s.sp]
        unfold words6At
        segDecrypt_wp_extract_exists
        rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
        generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
        apply sepWP_cut_here (mid := (blkPl_463).base + 5992#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWP.transport_budgetPool (s1 := sf) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
        apply sepWP_cut_here (mid := lsmpl.base 462)
        by_vm_open (
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, fun _hvm => ?_⟩
        refine SepWP.transport_budgetPool _hvm (hnext := ?_)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hF2
        cli_segDecrypt_wpp_call_lsfull_b hclosure () hF2 noPanic_onPanic_entails
        apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf_1 (mid := lsmpl.base 42)
        segDecrypt_wp_extract_exists
        rename_i hcl
        refine SepWP.transport_budgetPool hcl.1 (hnext := ?_)
        rw [hsp_sf]
        refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
        apply sepWP_cut_here (mid := lsmpl.base 42)
        by_vm_open (
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, fun _hvm => ?_⟩
        refine SepWP.transport_budgetPool _hvm (hnext := ?_)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hF3
        cli_segDecrypt_wpp_call_lsfull_b hgrow
          ((s.sp + 0x5d8#64, 0#64, 8#64, []), M.stepEvents evs_td st) hF3
          noPanic_onPanic_entails
        apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_ret_lsfull hF_sf_2
        segDecrypt_wp_extract_exists
        rename_i evs_grow p' hgrow_post
        rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
        unfold words6At
        segDecrypt_wp_extract_exists
        apply sepWP_cut_here (mid := (blkPl_463).base + 2128#64)
        by_vm_open (
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, fun _hvm => ?_⟩
        refine SepWP.transport_budgetPool _hvm (hnext := ?_)
        rw [hsp_sf_1, live_repAlloc A]
        refine segDecrypt_replace_pre
          (spe_errsAt_entails A.repAlloc s.sp p' e tag w1 w2 w3 w4 w5 H_spe hgrow_post.2.1 (hreassemble p'))
          (by sep_focus) ?_
        refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
        refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
        refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
        refine segDecrypt_replace_pre
          (sessionStateAt_exists_intro A.repAlloc (s.sp + 3232#64) G₂
            ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
        refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hF4 hmf
        right
        refine ⟨M.stepEvents evs_grow (M.stepEvents evs_td st),
          hsb_M.step (fun _ _ => SeqEnv.append) hgrow_post.1.2,
          by dsimp only [recFPCPlaced]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
        · refine ⟨by wp_norm_lhs,
                  by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                  by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                  by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                  by simp only [wp_norm, arm64_norm, hgrow_post.1.1, hcl.2, htr_sf, htr],
                  CryptoVerification.Cli.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF4,
                  by simp only [wp_norm, arm64_norm, *]⟩
        · rw [hsp0, cliRecFramePlaced_atState, sessionStateAt_atState,
            rdp_sepExists2_sessionStateAt_atState, rdp_sepExists_errsAt_singleton_atState]
          unfold recFramePlaced
          rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
          exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
        )))
      · have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
            (M.stepEvents evs_td st) FreeOnlyEvs :=
          hsb₁.weaken (fun _ h => Or.inl h)
        obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
        have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
          model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
        have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
          congrArg Prod.fst hmodel_dup
        apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.base 442)
        dsimp only [speAt]
        rw [stackAt_root_split_dropLocal2 s.sp]
        apply sepWP_cut_here (mid := lsmpl.base 442)
        by_vm_open (
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
          ⟨by wp_norm_lhs, fun _hvm => ?_⟩
        refine SepWP.transport_budgetPool _hvm (hnext := ?_)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hF2
        cli_segDecrypt_wpp_call_lsfull_b hdrop2
          ({ ss := s.sp + 3232#64, G := G₂,
             st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost },
           M.stepEvents evs_td st)
          hF2 noPanic_onPanic_entails
        apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_ret_lsfull hF_sf_1
        segDecrypt_wp_extract_exists
        rename_i evs_drop hevs_drop
        rw [hsp_sf]
        refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
        refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
        refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hF3 hmf
        left
        refine ⟨M.stepEvents evs_drop (M.stepEvents evs_td st),
          hsb_free.step (fun _ _ => FreeOnlyEvs.append) hevs_drop.2,
          by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
        · refine ⟨by wp_norm_lhs,
                  by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                  by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                  by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                  by simp only [wp_norm, arm64_norm, hevs_drop.1, htr_sf, htr],
                  CryptoVerification.Cli.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF3,
                  by simp only [wp_norm, arm64_norm, *]⟩
        · rw [hsp0, hmodel_dup1, cliRecFramePlaced_atState, sessionStateAt_atState,
            recordResultAt_atState, rdp_sepExists_errsAt_atState]
          unfold recFramePlaced
          rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
          dsimp only [recordResultAt, vecResultAt, speAt]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
        )
    · have hsb_free : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init
          (M.stepEvents evs_td st) FreeOnlyEvs :=
        hsb₁.weaken (fun _ h => Or.inl h)
      dsimp only [decryptTarget, vecResultAt]
      have hmodel_ok : x.model C S uuidTryParse =
          (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
        model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
      have hmodel_ok2 : (x.model C S uuidTryParse).2 =
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
      rw [hres] at hdec
      have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.ρ "memcpy")
      rw [sessionStateAt_eq_inline_sep_heap A.repAlloc (s.sp + 3232#64) G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
        memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp]
      unfold lsLogOff
      segDecrypt_wp_extract_exists
      rename_i bs hbs
      rw [← hbs.1]
      apply sepWP_cut_here (mid := (blkPl_463).base + 1736#64)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWP.transport_budgetPool (s1 := sf) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
      apply sepWP_cut_here (mid := lsmpl.ρ "memcpy")
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_lsfull_b hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
        noPanic_onPanic_entails
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf_1 (mid := lsmpl.base 48)
      segDecrypt_wp_extract_exists
      rename_i hmc
      first
        | refine SepWP.transport_budgetPool hmc.1 (hnext := ?_)
        | (have hvm_mc : VmPreserved sf sf_1 :=
             VmPreserved.trans (by simp only [wp_norm, arm64_norm]) hmc.1
           refine SepWP.transport_budgetPool hvm_mc (hnext := ?_))
      apply sepWP_cut_here (mid := lsmpl.base 48)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      cli_segDecrypt_wpp_call_lsfull_b hset
        ({ record := s.sp + 288#64, src := s.sp + 1520#64,
           cur := some (x.G, x.st), bs := bs : SetSessionStateGhost },
         M.stepEvents evs_td st) hF3
        noPanic_onPanic_entails
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_ret_lsfull hF_sf_2
      segDecrypt_wp_extract_exists
      rename_i evs_set hevs_set
      apply sepWP_cut_here (mid := (blkPl_463).base + 7820#64)
      by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by wp_norm_lhs, fun _hvm => ?_⟩
      refine SepWP.transport_budgetPool _hvm (hnext := ?_)
      rw [hsp_sf_1]
      refine segDecrypt_replace_pre
        (sessionStateAt_move_bytes_twice A.repAlloc (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
          G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_ok_exists_intro A.repAlloc (s.sp + 312#64) x.G G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A.repAlloc s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4 hmf
      left
      refine ⟨M.stepEvents evs_set (M.stepEvents evs_td st),
        hsb_free.step (fun _ _ => FreeOnlyEvs.append) hevs_set.2.1,
        by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hevs_set.1, hmc.2.2, htr_sf, htr],
                CryptoVerification.Cli.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF4,
                by simp only [wp_norm, arm64_norm, *]⟩
      · rw [hsp0, hmodel_ok1, hmodel_ok2, cliRecFramePlaced_atState, recordResultAt_atState,
          rdp_sepExists_ok_sessionStateAt_atState, rdp_sepExists_errsAt_atState]
        unfold recFramePlaced lsLogOff
        rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
        dsimp only [recordResultAt, vecResultAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )))
    )
  intro x st_init R s0 hpc hst hpre0 hL
  obtain ⟨hFroz0, hpre⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsFrozen hpre0
  obtain ⟨S', hmod, hpan_imp⟩ := rdp_spec_S_exists_placed C S x
  dsimp only [recordDecryptPlacedSpecTPTight, recordDecryptPlacedSpecTPTightF,
    recordDecryptPlacedSpecTF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨
      (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S' tdEnv).pre (x, st_init) s0 ∗
      (tokenInitPlacedAt ∗ R) := by
    change s0.mem ⊨
      (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗
      (tokenInitPlacedAt ∗ R)
    have heq :
        (tokenInitPlacedAt ∗
          (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0) ∗ R =
        (recordDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗
          (tokenInitPlacedAt ∗ R) := by sep_ac_rfl
    exact heq ▸ hpre
  have hstk : rootStack ≤ s0.sp.toNat := rdp_rootStack_le_of_recordPlacedPreP hpre'
  have hJ : ∀ s st',
      JStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' (tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv))
        recExitPlaced (x, st_init) R s0 s := by
    intro s st' hs hLs
    rw [← rdp_JStatePlaced_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hout⟩ :=
      segExit_placed_ok (C := C) (A := A) (lim := lim) (ctl := ctl)
        (S := S') (tdEnv := tdEnv) (H := H)
        hdealloc x st_init st' (tokenInitPlacedAt ∗ R) s0 s hs hLs
    exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  have hF : ∀ s st',
      FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' (tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv))
        recExitPlaced (x, st_init) R s0 s := by
    intro s st' hs hLs
    rw [← rdp_FStatePlaced_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hnext⟩ :=
      segTail_placed_ok (C := C) (A := A) (lim := lim) (ctl := ctl)
        (S := S') (tdEnv := tdEnv) (H := H)
        hshim halloc hpanic hdropLocal2
        x st_init st' (tokenInitPlacedAt ∗ R) s0 s hs hLs
    rcases hnext with ⟨st'', hj⟩ | hout
    · rw [rdp_JStatePlaced_eq_of_model_eq hmod] at hj
      exact region_reaches_steps hst' (hJ s' st'' hj) hLs
    · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    segClone_placed_ok_P (C := C) (A := A) (lim := lim) (ctl := ctl) (S := S') (tdEnv := tdEnv)
      htd_ne hshim halloc hdealloc hmemcpy hpanic hchainClone hsenderClone hdrop1
      x st_init (tokenInitPlacedAt ∗ R) s0 hpc hst hpre' hL
  rcases hnext with ⟨G₁, st₁, hv⟩ | ⟨G₁, st₁, hm⟩ | hout
  · have hFroz' :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hFroz0 hst'.keepsFrozen
    obtain ⟨s'', hst'', hnext'⟩ :=
      hSegDec x st_init st₁ G₁ R s0 s' hQ hv hstk hFroz' (hst'.codeLoaded hL)
    rcases hnext' with ⟨st₂, hj⟩ | ⟨st₂, hf⟩ | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' st₂ hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' st₂ hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · have hFroz' :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hFroz0 hst'.keepsFrozen
    obtain ⟨s'', hst'', hnext'⟩ :=
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget.segMismatch_full_placed_ok
        (C := C) (A := A) (lim := lim) (ctl := ctl) (S := S') (tdEnv := tdEnv) (H := H)
        hgrowSpe x st_init st₁ G₁ (tokenInitPlacedAt ∗ R) s0 s' hm hFroz' (hst'.codeLoaded hL)
    rcases hnext' with ⟨st₂, hf⟩ | hout
    · rw [rdp_FStatePlaced_eq_of_model_eq hmod] at hf
      exact region_reaches_steps (hst'.trans hst'') (hF s'' st₂ hf) hL
    · exact ⟨s'', hst'.trans hst'', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  · exact ⟨s', hst', rdp_regionOutcome_of_specP_tokenFrame_placed hmod hpan_imp hout⟩

/-- `[LibsignalFullPlacement]` `region_ok` for
`withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight ...)` on Block `463` (`0` `hclosure` premise). -/
theorem recordDecrypt_full_placed_region_ok_TPTight [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd_ne : TdEnvInhabited tdEnv)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv)) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)) :=
  region_ok_of_reaches (fun ⟨x, st_init⟩ R s0 hpc hst hpre =>
    rdp_region_reaches_full_placed_TPTight C A lim ctl S tdEnv htd_ne H
      hshim halloc hrealloc hdealloc hmemcpy hpanic hTry x st_init R s0 hpc hst hpre)

/-- `[LibsignalFullPlacement]` `region_ok` with `Spec.withVRegs` on Block `463` (`0` `hclosure` premise). -/
theorem recordDecrypt_full_placed_region_vregs_ok_TPTight [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd_ne : TdEnvInhabited tdEnv)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 434)
      (tryDecryptSpecTPTightAt C A lim ctl uuidTryParse S tdEnv)) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight C A lim ctl uuidTryParse S tdEnv)).withVRegs := by
  intro ⟨x, st_init⟩ R s0 hpc hst hpre hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', hvregs, hpost⟩ | hpan⟩ :=
    rdp_region_reaches_full_placed_TPTight C A lim ctl S tdEnv htd_ne H
      hshim halloc hrealloc hdealloc hmemcpy hpanic hTry x st_init R s0 hpc hst hpre hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', ?_⟩⟩
    dsimp only [Spec.withVRegs, CryptoVerification.LibsignalTripleRatchet.withLsFrozen]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvregs, hpost⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Envelope-monotonic `[LibsignalFullPlacement]` CLI `region_ok` with `Spec.withVRegs` on
`lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W))` (`0` `hclosure` premise). -/
theorem recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv
    [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
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
    region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)).withVRegs :=
  have htd_ne : TdEnvInhabited tdEnv := fun x hver =>
    let ⟨G₁, evs, hcl, he⟩ :=
      tdEnvInhabited_tryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K)
        hRecv_ne hFmtWrite_ne hFmtInner_ne x hver
    ⟨G₁, evs, hcl, htd _ _ he⟩
  recordDecrypt_full_placed_region_vregs_ok_TPTight
    W.C A lim ctl (spqrV1 W.C.F W.Q.K) tdEnv htd_ne
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_panic_all mmpl g W lsHandleErrorSym (by decide))
    (tryDecryptV1_placed_ok_PTight_cli_of_tdEnv mmpl g W ctl hG hAesDec hSpqr
      hFmtWrite hFmtInner hRecv_ne hFmtWrite_ne hFmtInner_ne htd)

/-- Envelope-parametric `[LibsignalFullPlacement]` CLI `region_ok` with `Spec.withVRegs` on
`lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W))` at `TryDecryptCliEnvOf` (`0` `hclosure` premise). -/
theorem recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_ofEnv
    [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
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
    region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv))).withVRegs :=
  recordDecryptV1_full_placed_region_vregs_ok_PTight_cli_of_tdEnv mmpl g W ctl hG hAesDec hSpqr
    hFmtWrite hFmtInner hRecv_ne hFmtWrite_ne hFmtInner_ne (fun _ _ h => h)

/-- Concrete `[LibsignalFullPlacement]` CLI `region_ok` with `Spec.withVRegs` on
`lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W))` (`0` `hclosure` premise). -/
theorem recordDecryptV1_full_placed_region_vregs_ok_PTight_cli
    [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W) :
    region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
          (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)))).withVRegs :=
  recordDecrypt_full_placed_region_vregs_ok_TPTight
    W.C A lim ctl (spqrV1 W.C.F W.Q.K)
    (TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))
    (tdEnvInhabited_tryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_panic_all mmpl g W lsHandleErrorSym (by decide))
    (tryDecryptV1_placed_ok_PTight_cli mmpl g W ctl hG hAesDec hSpqr)

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1TrapPlacedBudget
