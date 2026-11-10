/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat

/-!
# `HookSat` Sibling of `CliSlotCalleesInstPlacedBudgetCallees` (`CliSlotCalleesInstPlacedBudgetCalleesSat`)

Budget-threaded relocatable `[LibsignalPlacement]` W1 Block-`428` / Block-`464` callees replacing
`HkdfPlacedHooks` (`= some hookMemset`) and `cliExternsPlaced_sessionMemsetRegion_budget_sat` with
`(hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec)`,
and dropping `(h_ms : H lsMemsetSym = some memsetHook)` in `new_from_slice_114_vm_cro_ok` via
`AssemblyBudgetAuxSat.runsTo_block_lift_vm_no_memset`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCalleesSat

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   blkPC_114 blkPC_252 blkPC_38 blkPC_39 blkPC_60 blkPC_61 blkPC_69 blkPl_114
   blkPl_252 blkPl_38 blkPl_39 blkPl_60 blkPl_61 blkPl_69 libsignalMutatedBlocks
   libsignalSessionLib lsRustNoAllocShimSym ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.CliRatchet.EncPlaced (instIsLsBlockProg_464 lsProg_464)
open CryptoVerification.CliRatchet.Placed (blkPC_428 blkPl_428 instIsLsBlockProg_428)
open CryptoVerification.CliRatchet.SendPlaced (instIsLsBlockProg_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl withLsRoCl)
open CryptoVerification.LibsignalSession (hmacSpec)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (lsCompress256Sym lsMemcpySym lsMemsetSym)
open CryptoVerification.LibsignalSpqrV1 (spqrV1_emptyOk)
open CryptoVerification.LibsignalTripleRatchet
  (SpqrModel blkPC_63 blkPl_63 extract_withLsCodeRoLoaded keys_ls_hook_ok_of_mem
   keys_ls_subroutine_ok_of_block_cro lsPanicConstAddOverflowSym
   noAllocShimSpec subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded uuidTryParseCodeSpec
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced scopeIn)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
  (PublicApiEncHooksPlaced otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget
  (otrEncryptEmpty_coins_placed_ok otrEncryptV1_coins_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
  (expand_multi_info_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (extract_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact (HookSatExactMemcpy)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (CliSlotAllocHooks CliSlotEnvs SpqrV1PlacedSeamsBudget WithStoresEncVTPlacedOk
   skeletonHooks_of_slotHooks w1IdKitBudgetEnv w1IdKitPlaced_okIE w1SessKitBudgetEnv
   w1SessKitPlaced_okSE w2IdVt_placed_ok w2SessVt_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (cliExternsPlaced_rustAllocShimVm_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
  (W1InnerPlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_compress256Multi_budget_sat
   cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_framelessMemcpy_budget_sat
   cliExternsPlaced_noAllocShim_budget_sat cliExternsPlaced_realloc_budget_sat
   cliExternsPlaced_sessionMemcpyRegion_budget_sat)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget (message_keys_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
  (hmac_placed_cro_ok_at_block_sat new_from_slice_placed_cro_budget_ok_at_block_sat)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget (nextChainKeyPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
  (parseSid_placed_ok_of_code)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (generateKeysSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
  (generateKeys_placed_ok_of_contracts)
open LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget
  (serialize_addresses_placed_ok_of_rustAllocShimVm)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget (computeMac_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux (newFromSliceBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget (encode_varint_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget (encoded_len_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget (signalMessageNew_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget (signalMessageNewSpec)

export LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees
  (OtrRoCalleesPlacedOk)

/-- Cross-block transfer of `LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec`. -/
theorem transfer_tr_cro_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  keys_ls_subroutine_ok_of_block_cro hcallee hi hj hj_unmut

private theorem subroutine_ok_storeKitCro_of_trCro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hc, hpre⟩ :=
        CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
    (fun _ _ _ _ hq => hq)

private theorem subroutine_ok_trCro_of_storeKitCro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hc, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
    (fun _ _ _ _ hq => hq)

private theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- All 11 hook contracts of `PublicApiEncHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))`
hold from `CliSlotAllocHooks`. -/
theorem publicApiEncHooksBudget_cli [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    PublicApiEncHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees.publicApiEncHooksBudget_cli
    mmpl g W A lim hH

/-- `<uuid::Uuid>::try_parse` (Block `252`, calling Blocks `255` and `254` with `0` hooks)
satisfies `withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))`. -/
theorem uuidTryParse_252_vm_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees.uuidTryParse_252_vm_placed_ok
    H

/-- `ChainKey::next_chain_key` (Block `39`) satisfies
`withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec F)`. -/
theorem nextChainKey_39_vm_cro_ok [LibsignalPlacement] {F : ShaCompress}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_39).rebase (blkPl_39).base H) (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpec F))))
    (hpan : H lsPanicConstAddOverflowSym = some Rust.panicked) :
    subroutine_ok ((blkPC_39).rebase (blkPl_39).base H) (blkPl_39).base
      (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec F)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees.nextChainKey_39_vm_cro_ok
    hhmac hpan

private theorem new_from_slice_114_vm_cro_ok [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec F)) :=
  new_from_slice_placed_cro_budget_ok_at_block_sat
    (callerProg := (blkPC_114).rebase (blkPl_114).base H) (i := 114) F h_mc h_c256

private theorem new_from_slice_cro_budget_ok_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec W.C.F)) := by
  have hEx : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  exact transfer_tr_cro_of_block
    (calleeProg := (blkPC_114).rebase (blkPl_114).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (new_from_slice_114_vm_cro_ok W.C.F hEx.memcpy hEx.compress256) hi

private theorem hmac_vm_cro_ok_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpec W.C.F))) := by
  have hEx : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  exact hmac_placed_cro_ok_at_block_sat (callerProg := callerProg) (i := i) W.C.F
    hEx.memcpy hMs hEx.compress256 hi

theorem generateKeys_428_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim W.C.F)) := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hH.alloc.toCliGhostAllocHooks
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hMs
  have hext69 := extract_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hexp69 := expand_multi_info_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hdealloc69 := keys_ls_hook_ok_of_mem
    (prog := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 69)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
  have hgk69 := generateKeys_placed_ok_of_contracts (C := W.C) hext69 hexp69 hdealloc69
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact transfer_tr_cro_of_block
    (callerProg := (blkPC_428).rebase (blkPl_428).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (calleeProg := (blkPC_69).rebase (blkPl_69).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) hgk69

theorem signalMessageNew_428_placed_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 63)
      (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim W.C.F uuidTryParse)) := by
  have hNoAlloc := cliExternsPlaced_noAllocShim_budget_sat mmpl g W hH.alloc.shim_eq
  have hshim_b := hookSat_noAllocShimBudget_of_withVmPreserved hNoAlloc
  have hAlloc := cliExternsPlaced_alloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks
  have hDealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks
  have hRealloc := cliExternsPlaced_realloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks
  have hpks205 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (public_key_serialize_placed_ok hshim_b hAlloc)
  have hparse206 := parseSid_placed_ok_of_code (cliGhostExterns g (cliExternsPlaced mmpl W))
    (uuidTryParse_252_vm_placed_ok (cliGhostExterns g (cliExternsPlaced mmpl W)))
  have hparse61 := ls_subroutine_ok_of_block
    (callerProg := (blkPC_61).rebase (blkPl_61).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) hparse206
  have hser61 := serialize_addresses_placed_ok_of_rustAllocShimVm hparse61
    (cliExternsPlaced_rustAllocShimVm_sat mmpl g W hH.alloc.shim_eq)
    hAlloc
  have hmac60 := computeMac_placed_cro_ok W.C M A lim
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    (new_from_slice_cro_budget_ok_at_block mmpl g W hH.alloc.toCliGhostAllocHooks
      (callerProg := (blkPC_60).rebase (blkPl_60).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_60).rebase (blkPl_60).base
          (cliGhostExterns g (cliExternsPlaced mmpl W))) hpks205))
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_compress256Multi_budget_sat mmpl W))
    hDealloc
    hMs
  have hnew63 := signalMessageNew_placed_cro_ok (C := W.C)
    hNoAlloc
    hAlloc
    hDealloc
    (cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hpks205)
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
        (encoded_len_placed_ok A.repAlloc (cliGhostExterns g (cliExternsPlaced mmpl W)))))
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (encode_varint_placed_ok hshim_b hAlloc hRealloc))
    (ls_subroutine_ok_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hser61)
    (transfer_tr_cro_of_block
      (callerProg := (blkPC_63).rebase (blkPl_63).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (calleeProg := (blkPC_60).rebase (blkPl_60).base
        (cliGhostExterns g (cliExternsPlaced mmpl W))) hmac60)
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact transfer_tr_cro_of_block
    (callerProg := (blkPC_428).rebase (blkPl_428).base
      (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (calleeProg := (blkPC_63).rebase (blkPl_63).base
      (cliGhostExterns g (cliExternsPlaced mmpl W))) hnew63

theorem otrRoCalleesPlacedOk_cli [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    OtrRoCalleesPlacedOk mmpl g W A lim := by
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact
    { messageKeys := transfer_tr_cro_of_block
        (callerProg := (blkPC_428).rebase (blkPl_428).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (calleeProg := (blkPC_38).rebase (blkPl_38).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (message_keys_placed_cro_ok
          (hmac_vm_cro_ok_at_block mmpl g W hH.alloc.toCliGhostAllocHooks hMs
            (callerProg := (blkPC_38).rebase (blkPl_38).base
              (cliGhostExterns g (cliExternsPlaced mmpl W))))
          (cliExternsPlaced_noAllocShim_budget_sat mmpl g W hH.alloc.shim_eq)
          (cliExternsPlaced_alloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks))
      signalMessageNew := signalMessageNew_428_placed_cro_ok mmpl g W A lim hH hMs
      nextChainKey := transfer_tr_cro_of_block
        (callerProg := (blkPC_428).rebase (blkPl_428).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (calleeProg := (blkPC_39).rebase (blkPl_39).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (nextChainKey_39_vm_cro_ok
          (hmac_vm_cro_ok_at_block mmpl g W hH.alloc.toCliGhostAllocHooks hMs
            (callerProg := (blkPC_39).rebase (blkPl_39).base
              (cliGhostExterns g (cliExternsPlaced mmpl W))))
          ((skeletonHooks_of_slotHooks hH).panics
            lsPanicConstAddOverflowSym (by decide))) }

theorem otrEncryptV1_464_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs) :
    subroutine_ok (lsProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (withLsRoCl lsmpl
        (otrEncryptPlacedSpecQF (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length)
          tokenInitPlacedAt W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.spqrSend)) := by
  have hOtrRo := otrRoCalleesPlacedOk_cli mmpl g W A lim hH hMs
  have _ := instIsLsBlockProg_427 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have _ := instIsLsBlockProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hSend428 := subroutine_ok_trCro_of_storeKitCro
    (subroutine_ok_withLsCodeRoLoaded_of_rocl (ls_subroutine_ok_rocl_of_block
      (callerProg := (blkPC_428).rebase (blkPl_428).base
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      hSpqr.spqrSendCoins (by decide) (by decide) (by decide)))
  have h428 := otrEncryptV1_coins_placed_ok tokenInitPlacedAt W.C A lim 0#64
    (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.spqrSend
    (cliGhostExterns g (cliExternsPlaced mmpl W))
    hH.aesEnc hH.formatInnerEnv
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
    hSend428 hOtrRo.messageKeys (generateKeys_428_placed_ok mmpl g W A lim hH hMs)
    hOtrRo.signalMessageNew hOtrRo.nextChainKey
  have h428' := subroutine_ok_storeKitCro_of_trCro h428
  change subroutine_ok _ (lsmpl.base 428 + 0#64) _; rw [BitVec.add_zero]
  exact ls_subroutine_ok_rocl_of_block
    (callerProg := lsProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W))) (j := 428)
    h428' (by decide) (by decide) (by decide)

theorem otrEncryptEmpty_464_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (S : SpqrModel) (hEmpty : S.SendEmptyOk) :
    subroutine_ok (lsProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (withLsRoCl lsmpl
        (otrEncryptPlacedSpecQ (· = []) W.C A lim 0#64 uuidTryParse S (fun _ _ evs => evs = []))) := by
  have hOtrRo := otrRoCalleesPlacedOk_cli mmpl g W A lim hH hMs
  have _ := instIsLsBlockProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have h428 := otrEncryptEmpty_coins_placed_ok W.C A lim 0#64 S (fun _ _ evs => evs = [])
    (cliGhostExterns g (cliExternsPlaced mmpl W)) hEmpty (fun _ => rfl)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
    hH.aesEnc hH.formatInnerEnv
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
    hOtrRo.messageKeys (generateKeys_428_placed_ok mmpl g W A lim hH hMs)
    hOtrRo.signalMessageNew hOtrRo.nextChainKey
  have h428' := subroutine_ok_storeKitCro_of_trCro h428
  change subroutine_ok _ (lsmpl.base 428 + 0#64) _; rw [BitVec.add_zero]
  exact ls_subroutine_ok_rocl_of_block
    (callerProg := lsProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W))) (j := 428)
    h428' (by decide) (by decide) (by decide)

/-- Budget-threaded `W1InnerPlacedOk` on Block `464` from `hDropNz`, `CliSlotAllocHooks`,
`hMs`, `SpqrV1PlacedSeamsBudget`, and `WithStoresEncVTPlacedOk`. -/
theorem w1_inner_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hEncVT : WithStoresEncVTPlacedOk mmpl g W A lim cliRunBudgets envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)) :
    W1InnerPlacedOk mmpl g W A lim cliRunBudgets scopeIn envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile) :=
  hEncVT (publicApiEncHooksBudget_cli mmpl g W A lim hH)
    (w1SessKitPlaced_okSE mmpl g W A lim envs cliRunBudgets hDropNz hH hSpqr)
    (w1IdKitPlaced_okIE mmpl g W A lim envs.readFile cliRunBudgets hDropNz hH)
    (otrEncryptV1_464_placed_ok mmpl g W A lim envs hH hMs hSpqr)
    (otrEncryptEmpty_464_placed_ok mmpl g W A lim hH hMs (pqxdhSpqrModel ⟨W.C, W.Q⟩)
      (spqrV1_emptyOk W.C.F W.Q.K))
    (w2SessVt_placed_ok A.repAlloc cliRunBudgets hDropNz)
    (w2IdVt_placed_ok A.repAlloc cliRunBudgets hDropNz)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCalleesSat
