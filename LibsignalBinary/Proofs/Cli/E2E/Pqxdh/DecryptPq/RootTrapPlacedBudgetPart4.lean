/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetWp
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClMainPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPbBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat

/-!
# Budget-Threaded Block `507` CLI Segment `S3` Seam (`dhStep_pinned_507_cli`)

Pinned budget-threaded `S3TightSeamPinnedPlaced` instantiation at
`cliGhostExterns g (cliExternsPlaced mmpl W)` on Block `507`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart4

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement blkPC_200 blkPC_205 blkPC_22 blkPl_200 blkPl_205 blkPl_22
  lsBlackBoxU8Sym lsNoAllocShimSym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem lsmpl withLsCodeLoaded
)
open CryptoVerification.CliHandshake.Placed (blkPC_513 blkPl_513)
open CryptoVerification.CliHandshake.TryDecPlaced (
  blkPC_508 blkPl_508 instIsLsBlockProg_508
)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel keys_ls_hook_ok_of_mem
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (
  ls_subroutine_ok_transfer_of_plain
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd (spqrNoPanic)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced cliHookTablePlaced lsRustAllocSymCli lsRustAllocZeroedSymCli
  lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other cliGhostExterns_shim
)
open CryptoVerification.SignalSession.Cli.Slots (
  blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetWp (
  dhCommitBlockVmWp_507 dhStepBlockVmWp_507
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2PlacedBudget (drop_chain_placed_ok)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (S3TightSeamPinnedPlaced)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudget (
  CliS3CommitSeamPinnedPlaced s3CommitDefaultEnv
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClMainPlacedBudget (
  s3_commit_pinned_cl_budget_placed_ok_cli
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget (
  s3_pinned_cro_placed_okT_cli
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget (
  coinsFill_507_cro_placed_cli
)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (GrowOneEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat (
  createChain_placed_ok_of_block_sat
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_base_add)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  fitsEnv_growOne104_iff growOne104Events
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_derivePublicKeyBytes_budget_sat cliExternsPlaced_diffieHellman_budget_sat
  cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_realloc_budget_sat
  cliExternsPlaced_sessionMemmove_budget_sat cliExternsPlaced_sessionMemsetRegion_budget_sat
  cliExternsPlaced_sharedSecretDrop_budget_sat cliExternsPlaced_staticSecretDrop_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPbBudget (chain_key_to_pb_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpec derivePublicKeyBytesBudgetSpec finishGrowEvents framelessMemcpyBudgetSpec
  noAllocShimBudgetSpec noAllocShim_hookOk publicKeySerializeSpec
  subroutine_ok_derivePublicKeyBytes_of_withVmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget (
  derive_public_key_bytes_placed_ok_of_contract
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (
  public_key_serialize_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget (
  growOneChain_placed_ok_of_noop_at_block
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (
  growOneSpec growOneSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps (
  lsStaticDropSym zeroizeSecretBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (DhStepBlockVmWp)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec)

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

private theorem noAllocShim_budget_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim), noAllocShim_hookOk⟩

private theorem framelessMemcpy_budget_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" framelessMemcpyBudgetSpec := by
  rcases cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG with ⟨f, hf, h⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases h x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkeep, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [LibsignalBinary.Heap.SpecBudget.withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem createChain_507_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim W.C)) := by
  have _ := instIsLsBlockProg_508 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  exact createChain_placed_ok_of_block_sat
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_diffieHellman_budget_sat mmpl W))
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_sharedSecretDrop_budget_sat mmpl W))
    (cliGhost_row mmpl g W (blackBox_row_placed mmpl W))
    (noAllocShim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W))
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)

private theorem derivePk_507_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec W.C.pubKey)) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  have h200 : subroutine_ok ((blkPC_200).rebase (blkPl_200).base H)
      (blkPl_200).base (derivePublicKeyBytesBudgetSpec W.C.pubKey) :=
    derive_public_key_bytes_placed_ok_of_contract
      (subroutine_ok_derivePublicKeyBytes_of_withVmPreserved
        (ls_hook_ok_of_mem
          (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
            (cliExternsPlaced_derivePublicKeyBytes_budget_sat mmpl W))))
  exact subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_transfer_of_plain
      (callerProg := (blkPC_508).rebase (blkPl_508).base H) h200)

private theorem pkSer_507_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  exact ls_subroutine_ok_transfer_of_plain
    (callerProg := (blkPC_508).rebase (blkPl_508).base H)
    (calleeProg := (blkPC_205).rebase (blkPl_205).base H)
    (public_key_serialize_placed_ok (noAllocShim_budget_sat mmpl g W hG.shim_eq)
      (cliExternsPlaced_alloc_budget_sat mmpl g W hG))

private theorem chainKeyToPb_507_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 22) (withLsCodeLoaded lsmpl (chainKeyToPbSpec M A lim)) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  exact ls_subroutine_ok_transfer_of_plain
    (callerProg := (blkPC_508).rebase (blkPl_508).base H)
    (calleeProg := (blkPC_22).rebase (blkPl_22).base H)
    (chain_key_to_pb_placed_ok (noAllocShim_budget_sat mmpl g W hG.shim_eq)
      (cliExternsPlaced_alloc_budget_sat mmpl g W hG))

private theorem growOne_507_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 43) (withLsCodeLoaded lsmpl (growOneSpec M A lim)) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  have hraw := growOneChain_placed_ok_of_noop_at_block
    (callerProg := (blkPC_508).rebase (blkPl_508).base H)
    ((cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq))
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
  have hevs_eq : ∀ (cap : BitVec 64) (evs : List AllocEvent),
      GrowOneEnv cap evs → evs = growOne104Events cap := by
    intro cap evs henv
    unfold growOne104Events finishGrowEvents
    rcases henv with ⟨rfl, rfl⟩ | ⟨hne, rfl⟩
    · rfl
    · have hc0 : cap.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
      simp only [hc0, ↓reduceIte]
  refine subroutine_ok_mono hraw (fun ((v, cap, ptr, bs), st) R s0 hpre0 => ?_)
    (fun ((v, cap, ptr, bs), st) R s0 sf hpost => ?_)
  · dsimp only [withLsCodeLoaded, growOneSpec, growOneSpecWithStack,
      LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.growOneSpec] at hpre0 ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hlen, hptr, hmax, hfits⟩, hmem0⟩
    refine ⟨⟨hx0, hlen, hptr, hmax, fun evs henv => ?_⟩, hmem0⟩
    rw [hevs_eq cap evs henv]
    exact fitsEnv_growOne104_iff.mp hfits
  · dsimp only [withLsCodeLoaded, growOneSpec, growOneSpecWithStack,
      LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget.growOneSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨htr, henv⟩, hpost⟩
    rw [hevs_eq cap evs henv] at hpost
    rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨p', hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hp', _⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hp', by refine Satisfies.mono (Entails.of_eq ?_) hpost; sep_ac_rfl⟩

private theorem dropChain_507_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 513) (withLsCodeLoaded lsmpl (dropChainSpec M A lim)) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  exact ls_subroutine_ok_transfer_of_plain
    (callerProg := (blkPC_508).rebase (blkPl_508).base H)
    (calleeProg := (blkPC_513).rebase (blkPl_513).base H)
    (drop_chain_placed_ok (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

private theorem s3_commit_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) :
    CliS3CommitSeamPinnedPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508) W.C A lim ctl uuidTryParse spqrNoPanic s3CommitDefaultEnv := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  exact s3_commit_pinned_cl_budget_placed_ok_cli
    (dhCommitBlockVmWp_507 H) W.C A lim ctl uuidTryParse spqrNoPanic
    (pkSer_507_cl_ok mmpl g W hG) (chainKeyToPb_507_cl_ok mmpl g W hG)
    (growOne_507_cl_ok mmpl g W hG) (dropChain_507_cl_ok mmpl g W hG)
    (keys_ls_hook_ok_of_mem (noAllocShim_budget_sat mmpl g W hG.shim_eq))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_alloc_budget_sat mmpl g W hG))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
    (keys_ls_hook_ok_of_mem (framelessMemcpy_budget_sat mmpl g W hG))
    (keys_ls_hook_ok_of_mem
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_sessionMemmove_budget_sat mmpl W dropChainStack)))
    (hlr_alloc := lsRetAddr624_base_add 508 0xa00#64 (by decide) (by decide))
    (hlr_dealloc := lsRetAddr624_base_add 508 0xaf0#64 (by decide) (by decide))
    (hlr_ls := lsRetAddr624_base_add 508 0xb8c#64 (by decide) (by decide))

theorem dhStep_pinned_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPinnedPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  have hwp : DhStepBlockVmWp ((blkPC_508).rebase (blkPl_508).base H)
      (lsmpl.base 508) (lsmpl.base 618) :=
    dhStepBlockVmWp_507 H
  have hsd : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsmpl.ρ lsStaticDropSym) zeroizeSecretBudgetSpec :=
    keys_ls_hook_ok_of_mem
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W))
  exact s3_pinned_cro_placed_okT_cli hwp W.C A lim ctl S
    (createChain_507_cro_ok mmpl g W hG)
    (derivePk_507_cro_ok mmpl g W)
    (coinsFill_507_cro_placed_cli mmpl g W hG)
    hsd
    (s3_commit_507_cli mmpl g W hG ctl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart4
