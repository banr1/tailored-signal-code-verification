/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart2
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart3
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart4
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS0PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.MainBudget

/-!
# Budget-Threaded Segment `S3` and Block `433` Callee Seams

Instantiates all budget-threaded (`RustCliAllocBudget M`) CLI Block `433` segment seams
(`ErrTail`, `S0`–`S9`) at `cliGhostExterns g (cliExternsPlaced mmpl W)` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement
  blkPC_57 blkPC_69 blkPl_57 blkPl_69
  ls_hook_ok_ultra_of_mem ls_subroutine_ok_of_block lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain
)
open CryptoVerification.E2E (aesDecHookMallocng fmtWriteHook0 formatInnerHook0)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks SendCall SpqrModel
  hookMemset_eq_memsetHook keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkPl_434 instIsLsBlockProg_434
)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced cliHookTablePlaced lsAesDecSym lsFmtWriteSym lsFormatInnerSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
  lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
  cliGhostExterns_shim
)
open CryptoVerification.SignalSession.Cli.Slots (
  aesDec_row_placed blackBox_row_placed cliGhostExterns_panic_all
  cliGhostExterns_sat_of_cliExternsPlaced compress256_row_placed fmtWrite_row_placed
  formatInner_row_placed memmove_row_placed
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
)
open LibsignalBinary.Heap.Fine (
  fmtWriteHook0_budget_ok formatInnerHook0_budget_ok
)
open LibsignalBinary.Heap.SpecBudget (
  FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec formatInnerBudgetEnvSpec withVmPreserved
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget (
  CmkSeg4Env consumeMsgKey_433_placed_ok_ofEnv s4DefaultEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (
  aesDecrypt_433_placed_ok applyRatchet_433_placed_ok s8Env s9Env
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1PlacedBudget (
  deriveKeys_433_placed_ok pqRecv_433_placed_ok_WT_cli_of_seams_ofEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupPlacedBudget (
  findChain_433_placed_ok_of_bb
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlacedBudget (
  S1TightSeamFreePlaced S1TightSeamPinnedFreePlaced
  errTail_433_placed_okT loadRatchet_433_placed_okT loadRatchet_pinned_433_placed_okT
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ErrTailTightSeamPlaced S0PSeamPlaced S2SeamPlaced S3TightSeamPinnedPlaced S3TightSeamPlaced
  S4SeamPlaced S5WTSeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat (
  expand_multi_info_placed_vm_ok_of_other_block_sat
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat (
  extract_placed_vm_ok_of_other_block_sat
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (
  hookSat_sessionMemmoveBoundedBudget_of_unbounded
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_realloc_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemmove_budget_sat
  cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (
  SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShim_hookOk
)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat (
  cmk_raw_placed_cro_ok_at_block_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget (
  clear_unacknowledged_pre_key_message_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExtBudget (
  drop_vec_chain_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget (
  drop_spe_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget (
  remote_identity_key_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget (
  addrDisplay_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget (
  generateKeys_placed_ok_of_contracts
)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudget (trApply_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.MainBudget (trFrom_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget (
  trFromPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

private theorem sub_ok_same_blk [LibsignalPlacement] {α : Type}
    {P Q : Program} {i : Nat} {H : LibsignalHooks}
    [hP : IsLsBlockProg P i H] [hQ : IsLsBlockProg Q i H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry spec) :
    subroutine_ok Q entry spec :=
  (hP.eq_blockProgram.trans hQ.eq_blockProgram.symm) ▸ h

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

private theorem trFrom_57_cli_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_57).rebase (blkPl_57).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_57).base
      (trFromPlacedSpec M A lim) :=
  trFrom_placed_ok
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (sub_ok_same_blk (remote_identity_key_placed_ok A.repAlloc
      (cliGhostExterns g (cliExternsPlaced mmpl W))))
    (sub_ok_same_blk (drop_spe_placed_ok (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)))
    (sub_ok_same_blk (drop_vec_chain_placed_ok (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)))

theorem blk433_s3_entry_eq [LibsignalPlacement] : (blkPl_434).base = lsmpl.base 434 := rfl

/-- Extract `HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim)` from
    `HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym (aesDecBudgetSpec W.C.D M A lim)`. -/
theorem hookOk_aesDec_of_hookSat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hsat : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecBudgetSpec W.C.D M A lim)) :
    HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim) := by
  rcases hsat with ⟨f, hf, hok⟩
  have hrow := cliGhost_row mmpl g W (aesDec_row_placed mmpl W)
  rw [hrow] at hf
  exact Option.some.inj hf ▸ hok

/-- `ErrTailTightSeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem errTail_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    ErrTailTightSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv :=
  errTail_433_placed_okT (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)

/-- Envelope-parametric `S5WTSeamPlaced` on Block `433` at
    `cliGhostExterns g (cliExternsPlaced mmpl W)` from `SpqrV1PlacedSeamsOfEnv`. -/
theorem pqRecv_433_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
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
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) RecvBytesEnv fmtEnv) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact pqRecv_433_placed_ok_WT_cli_of_seams_ofEnv hSpqr ctl
    (ls_hook_ok_ultra_of_mem hFmtInner)
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

/-- Default `SpqrRecvBytesEnv` / `FormatInnerEnv` `S5WTSeamPlaced` on Block `433` at
    `cliGhostExterns g (cliExternsPlaced mmpl W)` from `SpqrV1PlacedSeams`
    (`formatInnerHook0` discharged unconditionally). -/
theorem pqRecv_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W) (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) SpqrRecvBytesEnv FormatInnerEnv) :=
  pqRecv_433_cli_ofEnv mmpl g W hG hSpqr
    ⟨formatInnerHook0, cliGhost_row mmpl g W (formatInner_row_placed mmpl W),
      formatInnerHook0_budget_ok M A lim⟩
    ctl

/-- `S8SeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem aesDecrypt_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (ctl : BitVec 64) (S : SpqrModel) :
    S8SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S s8Env := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact aesDecrypt_433_placed_ok W.C A lim ctl S (cliGhostExterns g (cliExternsPlaced mmpl W))
    (ls_hook_ok_ultra_of_mem
      ⟨aesDecHookMallocng mmpl W.C.D, cliGhost_row mmpl g W (aesDec_row_placed mmpl W), hAesDec⟩)
    (ls_hook_ok_ultra_of_mem
      ⟨formatInnerHook0, cliGhost_row mmpl g W (formatInner_row_placed mmpl W),
        formatInnerHook0_budget_ok M A lim⟩)
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

/-- `S0PSeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s0_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S0PSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv :=
  DecryptFrontTrapPlacedBudgetPart2.s0_433_cli mmpl g W ctl S tdEnv

/-- Pinned `S1TightSeamPinnedFreePlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s1_pinned_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S1TightSeamPinnedFreePlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv (fun _ => FreeOnlyEvs) :=
  loadRatchet_pinned_433_placed_okT (trFrom_57_cli_ok mmpl g W hG) (fun _ _ h => h)

/-- Unpinned `S1TightSeamFreePlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s1_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S1TightSeamFreePlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv (fun _ => FreeOnlyEvs) :=
  loadRatchet_433_placed_okT (trFrom_57_cli_ok mmpl g W hG) (fun _ _ h => h)

/-- `S2SeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s2_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64) :
    S2SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base A lim ctl :=
  findChain_433_placed_ok_of_bb (cliGhost_row mmpl g W (blackBox_row_placed mmpl W))

/-- `S6SeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s6_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) :
    S6SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl s6FreeOnlyEnv := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_434 H
  have _ : HkdfPlacedHooksExactSat W.C.F H := HkdfPlacedHooksExactSat.of_allocHooks hG
  have _ : HkdfPlacedHooksExactBudgetSat W.C.F H :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  have hgk69 := generateKeys_placed_ok_of_contracts
    (extract_placed_vm_ok_of_other_block_sat W.C
      (callerProg := (blkPC_69).rebase (blkPl_69).base H) H)
    (expand_multi_info_placed_vm_ok_of_other_block_sat W.C
      (callerProg := (blkPC_69).rebase (blkPl_69).base H) H)
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
  exact deriveKeys_433_placed_ok W.C A lim ctl H
    (keys_ls_subroutine_ok_of_block_cro
      (callerProg := (blkPC_434).rebase (blkPl_434).base H) hgk69)

/-- `S9SeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s9_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S9SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv s9Env := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_434 H
  have hmc58 : HookSat H "memcpy" framelessMemcpyBudgetSpec := by
    rcases cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG with ⟨f, hf, hok⟩
    refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
    rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
    · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
      rcases x with ⟨dst, src, bs⟩
      dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
        framelessMemcpyBudgetSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
    · exact ⟨hkf, hsym, Or.inr hrest⟩
  have hApply58 := trApply_placed_ok
    ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    hmc58
  have hClear35 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (clear_unacknowledged_pre_key_message_placed_ok (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
  exact applyRatchet_433_placed_ok W.C A lim ctl S tdEnv H
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_434).rebase (blkPl_434).base H) hApply58))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_434).rebase (blkPl_434).base H) hClear35))
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG))
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

/-- Pinned `S3TightSeamPinnedPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem dhStep_pinned_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPinnedPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) :=
  DecryptFrontTrapPlacedBudgetPart4.dhStep_pinned_433_cli mmpl g W hG ctl S

/-- Unpinned `S3TightSeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem dhStep_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) :=
  (dhStep_pinned_433_cli mmpl g W hG ctl S).toUnpinned

/-- Envelope-parametric `S4SeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s4_433_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {fmtWriteEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (ctl : BitVec 64) (S : SpqrModel) :
    S4SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S (CmkSeg4Env fmtWriteEnv) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_434 H
  have hEx : HkdfPlacedHooksExactSat W.C.F H := HkdfPlacedHooksExactSat.of_allocHooks hG
  have hA_cmk : CmkAllocHooks A lim H :=
    ⟨cliExternsPlaced_alloc_budget_sat mmpl g W hG,
     cliExternsPlaced_dealloc_budget_sat mmpl g W hG,
     cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq,
     cliGhostExterns_panic_all mmpl g W _ (by decide),
     cliGhostExterns_panic_all mmpl g W _ (by decide),
     cliGhostExterns_panic_all mmpl g W _ (by decide)⟩
  have h215 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (addrDisplay_placed_ok hFmtWrite)
  exact consumeMsgKey_433_placed_ok_ofEnv W.C A lim ctl S fmtWriteEnv H
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_434).rebase (blkPl_434).base H) h215))
    (cmk_raw_placed_cro_ok_at_block_sat
      (callerProg := (blkPC_434).rebase (blkPl_434).base H)
      W.C.F A lim hA_cmk
      (hookSat_sessionMemmoveBoundedBudget_of_unbounded 4096
        (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
          (cliExternsPlaced_sessionMemmove_budget_sat mmpl W 4096)))
      (cliGhost_row mmpl g W (blackBox_row_placed mmpl W))
      (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
      hEx.memcpy
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
      hEx.compress256)
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

/-- Default `s4DefaultEnv` `S4SeamPlaced` on Block `433` at
    `cliGhostExterns g (cliExternsPlaced mmpl W)` (`fmtWriteHook0` discharged unconditionally). -/
theorem s4_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S4SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S s4DefaultEnv :=
  s4_433_cli_ofEnv mmpl g W hG
    ⟨fmtWriteHook0, cliGhost_row mmpl g W (fmtWrite_row_placed mmpl W),
      fmtWriteHook0_budget_ok M A lim⟩
    ctl S

/-- `S7SeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s7_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S7SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S (s7Env W.C.F uuidTryParse) :=
  DecryptFrontTrapPlacedBudgetPart3.s7_433_cli mmpl g W hG ctl S

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudget
