/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart4 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClMainPlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.ChainPlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPbBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat

/-!
# `HookSat` Sibling of `DecryptFrontTrapPlacedBudgetPart4` (`DecryptFrontTrapPlacedBudgetPart4Sat`)

Re-proves `dhStep_pinned_433_cli` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`
under `(hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec)`
via `HkdfPlacedHooksExactBudgetSat` and `CryptoCalleesPlacedBudgetSat.createChain_placed_ok_of_block_sat`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart4Sat

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement ls_hook_ok_ultra_of_mem ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (lsMemsetSym)
open CryptoVerification.LibsignalTripleRatchet
  (SpqrModel pubFromSecretHook subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_434 blkPl_434 instIsLsBlockProg_434)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd (spqrNoPanic)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliHookTablePlaced lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.Slots
  (blackBox_row_placed cliGhostExterns_sat_of_cliExternsPlaced compress256_row_placed
   pubFromSecret_row_placed)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (S3TightSeamPinnedPlaced)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClMainPlacedBudget
  (s3_commit_pinned_cmk_cl_budget_placed_ok_cli)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget
  (s3_pinned_cro_placed_okT_cli)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget
  (coinsFill_433_cro_placed_cli)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.ChainPlacedBudget (drop_chain_placed_ok)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (growOneSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (createChain_placed_ok_of_block_sat)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_diffieHellman_budget_sat cliExternsPlaced_exactMemcpy_sat
   cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_realloc_budget_sat
   cliExternsPlaced_sessionMemmove_budget_sat cliExternsPlaced_sessionMemsetRegion_budget_sat
   cliExternsPlaced_sharedSecretDrop_budget_sat cliExternsPlaced_staticSecretDrop_budget_sat)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPbBudget (chain_key_to_pb_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (chainKeyToPbSpec derivePublicKeyBytesBudgetSpec framelessMemcpyBudgetSpec noAllocShim_hookOk
   pubFromSecret_hookOk publicKeySerializeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget
  (derive_public_key_bytes_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
  (growOneChain_placed_ok_of_noop_at_block)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (dhCommitBlockVmWp_549)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (dhStepBlockVmWp_549)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat hookSat_sessionMemsetRegion_of_budget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec)

private theorem blk433_s3_entry_eq [LibsignalPlacement] : (blkPl_434).base = lsmpl.base 434 := rfl

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

private theorem mkHkdfPlacedHooksExactSat_cli [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  { memset := hookSat_sessionMemsetRegion_of_budget
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
    memcpy := cliExternsPlaced_exactMemcpy_sat mmpl g W hG
    compress256 := cliGhost_row mmpl g W (compress256_row_placed mmpl W) }

private theorem framelessMemcpy_budget_sat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" framelessMemcpyBudgetSpec := by
  obtain ⟨f, hf, hok⟩ := cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem createChain_433_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim W.C)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have _ : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    mkHkdfPlacedHooksExactSat_cli mmpl g W hG
  have _ : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hMs
  exact createChain_placed_ok_of_block_sat
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_diffieHellman_budget_sat mmpl W))
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_sharedSecretDrop_budget_sat mmpl W))
    (cliGhost_row mmpl g W (blackBox_row_placed mmpl W))
    ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W))
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)

private theorem derivePk_433_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (derivePublicKeyBytesBudgetSpec W.C.pubKey)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (derive_public_key_bytes_placed_ok
        ⟨pubFromSecretHook W.C.pubKey, cliGhost_row mmpl g W (pubFromSecret_row_placed mmpl W),
          pubFromSecret_hookOk W.C.pubKey⟩)))

private theorem pkSer_433_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (public_key_serialize_placed_ok
      ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
      (cliExternsPlaced_alloc_budget_sat mmpl g W hG)))

private theorem chainKeyToPb_433_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 22) (withLsCodeLoaded lsmpl (chainKeyToPbSpec M A lim)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (chain_key_to_pb_placed_ok
      ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
      (cliExternsPlaced_alloc_budget_sat mmpl g W hG)))

private theorem growOne_433_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 43) (withLsCodeLoaded lsmpl (growOneSpec M A lim)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact growOneChain_placed_ok_of_noop_at_block
    ((cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq))
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)

private theorem dropChain_433_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 445) (withLsCodeLoaded lsmpl (dropChainSpec M A lim)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (drop_chain_placed_ok (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)))

/-- Pinned `S3TightSeamPinnedPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`
parameterized by `HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem dhStep_pinned_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPinnedPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := blk433_s3_entry_eq
  have _ := instIsLsBlockProg_434 H
  exact s3_pinned_cro_placed_okT_cli
    (dhStepBlockVmWp_549 H) W.C A lim ctl S
    (createChain_433_cro_ok mmpl g W hG hMs)
    (derivePk_433_cro_ok mmpl g W)
    (coinsFill_433_cro_placed_cli mmpl g W hG)
    (ls_hook_ok_ultra_of_mem
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W)))
    (s3_commit_pinned_cmk_cl_budget_placed_ok_cli
      (dhCommitBlockVmWp_549 H) W.C A lim ctl uuidTryParse spqrNoPanic
      (pkSer_433_cl_ok mmpl g W hG)
      (chainKeyToPb_433_cl_ok mmpl g W hG)
      (growOne_433_cl_ok mmpl g W hG)
      (dropChain_433_cl_ok mmpl g W hG)
      (ls_hook_ok_ultra_of_mem
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩)
      (ls_hook_ok_ultra_of_mem (cliExternsPlaced_alloc_budget_sat mmpl g W hG))
      (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
      (ls_hook_ok_ultra_of_mem (framelessMemcpy_budget_sat mmpl g W hG))
      (ls_hook_ok_ultra_of_mem
        (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
          (cliExternsPlaced_sessionMemmove_budget_sat mmpl W dropChainStack)))
      (hlr_alloc := lsRetAddr624_base_add 434 0xa00#64 (by decide) (by decide))
      (hlr_dealloc := lsRetAddr624_base_add 434 0xaf0#64 (by decide) (by decide))
      (hlr_ls := lsRetAddr624_base_add 434 0xb8c#64 (by decide) (by decide)))

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart4Sat
