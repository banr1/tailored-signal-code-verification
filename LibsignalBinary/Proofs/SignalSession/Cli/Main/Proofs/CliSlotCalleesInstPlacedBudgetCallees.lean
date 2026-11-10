/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetUuid
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SpqrV1Empty
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import ProofLib.SepLogic.Entry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded TripleRatchet Encrypt Callees (`[LibsignalPlacement]`)

Budget-threaded relocatable contracts for `OutgoingTripleRatchet::encrypt` (Block `428`),
`MessageEncrypt` (Block `464`), `<uuid::Uuid>::try_parse` (Block `252`), and
`ChainKey::next_chain_key` (Block `39`) under `PublicApiEncHooksPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (ShaState hmacWith keyToBytes32 sha256IV)
open CryptoGames.LibsignalSession (ChainKey Crypto ShaCompress)
open CryptoGames.Ratchet (chainHmac chainKeySeed)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_39 blkLib_eq_114 blkPC_38 blkPC_39 blkPC_60 blkPC_61 blkPC_69 blkPC_114 blkPC_252
  blkPl_38 blkPl_39 blkPl_60 blkPl_61 blkPl_69 blkPl_114 blkPl_252
  libsignalMutatedBlocks libsignalSessionLib lsProg_114 lsRustNoAllocShimSym ls_externAt?_of_mem
  ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.CliRatchet.EncPlaced (instIsLsBlockProg_464 lsProg_464)
open CryptoVerification.CliRatchet.Placed (blkPC_428 blkPl_428 instIsLsBlockProg_428)
open CryptoVerification.CliRatchet.SendPlaced (instIsLsBlockProg_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl withLsRoCl
)
open CryptoVerification.LibsignalSession (hmacSpec)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  CallingConventionPreserved_of_calleeSaved Frame disjointRegions_of_ro_rw
  hookMemcpy_eq_memcpyHook hookMemset_eq_memsetHook lsCompress256Sym lsMemcpySym lsMemsetSym
  lsSha256IVAddr new_from_slice_placed_run rodata_placed_sha256IV
)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes)
open CryptoVerification.LibsignalSpqrV1 (spqrV1_emptyOk)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SpqrModel blkPC_63 blkPl_63
  extract_withLsCodeRoLoaded hmacWith_two_eq_chainStep keyToBytes32_bytesToKey32
  keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro lsPanicConstAddOverflowSym
  memRegion36_unpack nck_length_hmacWith newFromSliceSpec newFromSliceStack nextChainKeyStack
  nextChainKey_ok_of_ne nextChainKey_panic_of_eq noAllocShimSpec pointsTo8_eq_pointsToBytes1
  pointsToBytes_chainKeyBytes_eq sepWPp_seq_lscro stackAt_nextChainKey stackAt_nextChainKey_repack
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded uuidTryParseCodeSpec withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (isBlock_nfsResult)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_handle_alloc_error cliGhostExterns_panic_handle_error
  cliGhostExterns_panic_option_expect_failed cliGhostExterns_sat_of_cliExternsPlaced
  compress256_row_placed scopeIn
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux (
  PublicApiEncHooksPlaced otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget (
  otrEncryptEmpty_coins_placed_ok otrEncryptV1_coins_placed_ok
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (
  hmacExcHooks hmacExcHooks_compress hmacExcHooks_memcpy runsTo_block_lift_vm
  stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat (
  expand_multi_info_placed_vm_ok_of_other_block_sat
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat (
  extract_placed_vm_ok_of_other_block_sat
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams (
  CliSlotAllocHooks CliSlotEnvs SpqrV1PlacedSeamsBudget WithStoresEncVTPlacedOk
  w1IdKitBudgetEnv w1IdKitPlaced_okIE w1SessKitBudgetEnv w1SessKitPlaced_okSE
  w2IdVt_placed_ok w2SessVt_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetUuid (
  uuidTryParse_placed_vm_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (
  cliExternsPlaced_rustAllocShimVm_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget (
  W1InnerPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_compress256Multi_budget_sat
  cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_durationSinceBounded_budget_sat
  cliExternsPlaced_exactMemcpy_sat cliExternsPlaced_framelessMemcpy_budget_sat
  cliExternsPlaced_noAllocShim_budget_sat cliExternsPlaced_realloc_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemsetRegion_budget_sat
  cliExternsPlaced_shim_budget_sat cliExternsPlaced_timeAdd_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (
  public_key_serialize_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget (
  messageKeysPlacedSpec message_keys_placed_cro_ok
)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat (
  hmac_placed_cro_ok_at_block_sat new_from_slice_placed_cro_budget_ok_at_block_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (
  HkdfPlacedHooksExactBudgetSat
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (
  HkdfPlacedHooksExactSat
)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget (nextChainKeyPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceIdBudget (
  parseSid_placed_ok_of_code
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (generateKeysSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget (
  generateKeys_placed_ok_of_contracts
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget (
  serialize_addresses_placed_ok_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudget (computeMac_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux (newFromSliceBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget (encode_varint_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget (encoded_len_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget (signalMessageNew_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget (signalMessageNewSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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
    PublicApiEncHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_shim_budget_sat mmpl g W hH.alloc.shim_eq
  alloc := cliExternsPlaced_alloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks
  dealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks
  realloc := cliExternsPlaced_realloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks
  memcpy := cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks
  stringClone := hH.stringCloneEnc
  timeAdd := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_timeAdd_budget_sat mmpl W)
  durationSince := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
    (cliExternsPlaced_durationSinceBounded_budget_sat mmpl W)
  handleError := cliGhostExterns_panic_handle_error mmpl g W
  handleAllocError := cliGhostExterns_panic_handle_alloc_error mmpl g W
  expectFailed := cliGhostExterns_panic_option_expect_failed mmpl g W

/-- `<uuid::Uuid>::try_parse` (Block `252`, calling Blocks `255` and `254` with `0` hooks)
satisfies `withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))`. -/
theorem uuidTryParse_252_vm_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))) := by
  refine subroutine_ok_mono (uuidTryParse_placed_vm_ok H)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeLoaded, withVmPreserved, Spec.keepsFs] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨hvm, hq⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq.2⟩

private theorem hmacVm_placed_cro_ok_at_state [LibsignalPlacement] {prog : Program}
    {F : ShaCompress} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpec F))))
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp 2048
        post := (withVmPreserved (hmacSpec F)).post } := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeRoLoaded, withVmPreserved, hmacSpec] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

private theorem vmPreserved_trans3 {s0 s1 s2 s3 : State}
    (h01 : VmPreserved s0 s1) (h23 : VmPreserved s2 s3) (h12 : VmPreserved s1 s2) :
    VmPreserved s0 s3 :=
  (h01.trans h12).trans h23

/-- `ChainKey::next_chain_key` (Block `39`) satisfies
`withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec F)`. -/
theorem nextChainKey_39_vm_cro_ok [LibsignalPlacement] {F : ShaCompress}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_39).rebase (blkPl_39).base H) (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpec F))))
    (hpan : H lsPanicConstAddOverflowSym = some Rust.panicked) :
    subroutine_ok ((blkPC_39).rebase (blkPl_39).base H) (blkPl_39).base
      (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec F)) := by
  have hpan_ovf : ((blkPC_39).rebase (blkPl_39).base H).externAt?
      (lsρ lsPanicConstAddOverflowSym) = some Rust.panicked :=
    (ls_externAt?_of_mem).trans hpan
  apply subroutine_ok_of_sepWPp
  intro ⟨self, ck, ret⟩ R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [nextChainKeyPlacedSpec, withVmPreserved,
    CryptoVerification.LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 36 ∗ stackAt s0.sp nextChainKeyStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  rw [pointsToBytes_chainKeyBytes_eq self ck, memRegion36_unpack ret, stackAt_nextChainKey s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun b0 =>
    SepWPp.exists_elim fun v29 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v19 => ?_
  apply sepWPp_seq_lscro (mid := lsmpl.base 73) hcl0
  apply sepWP_seg_ls_vm (Q := (blkPC_39).rebase (blkPl_39).base (hooksException H))
    blkLib_eq_39 (mid := lsmpl.base 73)
  intro _m_strip1
  wp_steps
  refine SepWP.done (by simp_all) (by simp_all) fun _m_real1 hnsp1 => ?_
  have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [State.setMem_setMem] at hvm1 ⊢
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl1
  have hhmac1 := hmacVm_placed_cro_ok_at_state hhmac hcl1
  dsimp only [withVmPreserved, hmacSpec] at hhmac1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([2#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 36#64) 2#8]
  apply sepWPp_seq_lscro (mid := (blkPl_39).base + 56#64) hcl1
  wp_call hhmac1 (s0.sp - 68#64, self, keyToBytes32 ck.key, s0.sp - 36#64, [2#8])
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl2
  by_cases hidx : ck.index = BitVec.allOnes 32
  · have hidx_max : ck.index = 0xffffffff#32 := hidx
    rw [hidx_max]
    apply sepWPp_seq_lscro (mid := lsρ lsPanicConstAddOverflowSym) hcl2
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.panic (by simp_all) (by simpa using hpan_ovf) fun hm' => ?_
    simpa only [withLsCodeRoLoaded, nextChainKeyPlacedSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec, sepConj_assoc] using
      allowPanic_panicked ⟨nextChainKey_panic_of_eq F ck hidx,
        by simp_all [Rust.panicked, wp_norm, arm64_norm]⟩ hm'
  · have hz2 : (ck.index + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hidx; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := ck.index.isLt
      rw [BitVec.toNat_add] at h1
      change (ck.index.toNat + 1) % 4294967296 = 0 at h1
      change ck.index.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (nck_length_hmacWith F (keyToBytes32 ck.key) [2#8])
    have hw_sp := hw32 (s0.sp - 68#64)
    have h60 : s0.sp - 68#64 + 8#64 = s0.sp - 60#64 := by bv_arith
    have h52 : s0.sp - 68#64 + 16#64 = s0.sp - 52#64 := by bv_arith
    have h44 : s0.sp - 68#64 + 24#64 = s0.sp - 44#64 := by bv_arith
    rw [h60, h52, h44] at hw_sp
    rw [hw_sp]
    apply sepWPp_seq_lscro (mid := s0.readReg64 Reg.lr) hcl2
    apply sepWP_seg_ls_vm (Q := (blkPC_39).rebase (blkPl_39).base (hooksException H))
      blkLib_eq_39 (mid := s0.readReg64 Reg.lr)
    intro _m_strip2
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun _m_real2 hnsp3 => ?_
    have hvm3 := hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm])
    have hvm_tot := vmPreserved_trans3 hvm1 hvm3 (by assumption)
    simp only [State.setMem_setMem] at hvm_tot ⊢
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.done (by simp_all) (by simp_all)
      ⟨fun hm => ?_,
       by simp only [wp_norm, arm64_norm, *],
       by simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    have hok := nextChainKey_ok_of_ne F ck hidx
    rw [hok]
    dsimp only
    refine Entails.pure_right hvm_tot ?_
    refine Entails.pure_right ⟨by nofun, by simp_all [wp_norm, arm64_norm]⟩ ?_
    let ck' : ChainKey := ⟨bytesToKey32 (chainHmac F ck.key chainKeySeed), ck.index + 1⟩
    have hkey_eq : keyToBytes32 ck'.key = hmacWith F (keyToBytes32 ck.key) [2#8] := by
      show keyToBytes32 (bytesToKey32 (chainHmac F ck.key chainKeySeed)) = _
      rw [← hmacWith_two_eq_chainStep]
      exact keyToBytes32_bytesToKey32 _ (nck_length_hmacWith F _ _)
    rw [pointsToBytes_chainKeyBytes_eq self ck, pointsToBytes_chainKeyBytes_eq ret ck',
        hkey_eq, hw32 ret]
    have hstk := stackAt_nextChainKey_repack s0.sp w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 2#8
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right hstk))
    exact Entails.of_eq (by dsimp only [ck', Reg.x19, Reg.x20, Reg.lr, Reg.x29]; sep_ac_rfl)

private theorem stripS_read64 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read64 a = s.mem.read64 a := by
  cases s
  simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

private theorem stripExecOutside_hmacSt {F : ShaState → List (BitVec 8) → ShaState}
    {p : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} {key msg : List (BitVec 8)} :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
      (ProofLib.stripExecOutside p m) a F key msg ↔
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt m a F key msg := by
  unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
  simp only [stripExecOutside_readBytes, Memory.read64, ProofLib.strip_read8]

private theorem new_from_slice_114_vm_cro_ok [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_mc : H lsMemcpySym = some memcpyHook)
    (h_ms : H lsMemsetSym = some memsetHook)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec F)) := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre_cro hsp => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre_cro
  dsimp only [newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_iv : DisjointRegions lsSha256IVAddr 32 (s0.sp - 544#64) 544 :=
    disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
  have hdisj_out : DisjointRegions (s0.readReg64 .x0) 0x98 (s0.sp - 544#64) 544 := by
    rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
  have hdisj_key : (s0.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s0.readReg64 .x1) (s0.readReg64 .x2).toNat (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl hx2_nat
    · exact Or.inr (by
        rw [hx1, hx2_nat]
        exact hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hal_sp : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  intro _hL114_in
  have heq114 : ∀ X, lsProg_114 X = libsignalSessionLib.blockProgram lsmpl 114 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)
  have hL114_bp : (libsignalSessionLib.blockProgram lsmpl 114 H).CodeLoaded s0.mem :=
    hcl 114 (by decide) (by decide) H (fun _ => none) Syscall.standard
  let Q114 := libsignalSessionLib.blockProgram lsmpl 114 (hmacExcHooks F H)
  let kp114 := ProofLib.progKeep Q114
  have hm_s0 : (ProofLib.stripS kp114 s0).mem = ProofLib.stripExecOutside kp114 s0.mem := by
    cases s0; rfl
  have hrunsP := new_from_slice_placed_run (F := F) (s₀ := s0) h_mc h_c256
    hpc hrun (by rw [hx2_nat]; exact hkey_len) hiv_eq hread_iv hdisj_iv
    (by rw [hx0]; exact hrw_out) hrw_stk hdisj_out hdisj_key hal_sp
  have hrunsQ := new_from_slice_placed_run (F := F) (s₀ := ProofLib.stripS kp114 s0)
    (hmacExcHooks_memcpy F H) (hmacExcHooks_compress F H)
    (by cases s0; exact hpc)
    (by cases s0; exact hrun)
    (by have hr : (ProofLib.stripS kp114 s0).readReg64 .x2 = s0.readReg64 .x2 := by cases s0; rfl
        rw [hr, hx2_nat]; exact hkey_len)
    (by rw [hm_s0, stripExecOutside_readBytes]; exact hiv_eq)
    (by rw [hm_s0]; exact stripExecOutside_readable kp114 s0.mem _ _ hread_iv)
    (by have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rwa [hs])
    (by have hr : (ProofLib.stripS kp114 s0).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
        rw [hm_s0, hr, hx0]; exact stripExecOutside_rw kp114 s0.mem _ _ hrw_out)
    (by have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rw [hm_s0, hs]; exact stripExecOutside_rw kp114 s0.mem _ _ hrw_stk)
    (by have hr : (ProofLib.stripS kp114 s0).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
        have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rwa [hr, hs])
    (by have hr1 : (ProofLib.stripS kp114 s0).readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
        have hr2 : (ProofLib.stripS kp114 s0).readReg64 .x2 = s0.readReg64 .x2 := by cases s0; rfl
        have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rwa [hr1, hr2, hs])
    (by have hs : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
        rwa [hs])
  obtain ⟨sf, hsteps_bp, hvm, htr, hvregs, hsf_or⟩ :=
    runsTo_block_lift_vm h_mc h_ms h_c256 blkLib_eq_114 rfl rfl hL114_bp
      (heq114 H ▸ hrunsP) (heq114 _ ▸ hrunsQ)
      (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
  have hsteps : Steps ((blkPC_114).rebase (blkPl_114).base H) s0 sf := by
    change Steps (lsProg_114 H) s0 sf
    rwa [heq114 H]
  have hsf_raw : sf.pc = s0.readReg64 .lr ∧ sf.status = .Running ∧
      CryptoVerification.LibsignalSession.CryptoHmacSha256.CalleeSaved s0 sf ∧
      sf.mem.read64 (s0.readReg64 .x0) = 0#64 ∧
      CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt sf.mem (s0.readReg64 .x0 + 8#64)
        F (s0.mem.readBytes (s0.readReg64 .x1) (s0.readReg64 .x2).toNat) [] ∧
      Frame s0.mem sf.mem [(s0.readReg64 .x0, 0x98), (s0.sp - 544#64, 544)] := by
    rcases hsf_or with hsf_strip | hsf_real
    · rcases hsf_strip with ⟨hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩
      have hm_sf : (ProofLib.stripS kp114 sf).mem = ProofLib.stripExecOutside kp114 sf.mem := by
        cases sf; rfl
      have hr_s00 : (ProofLib.stripS kp114 s0).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
      have hr_s01 : (ProofLib.stripS kp114 s0).readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
      have hr_s02 : (ProofLib.stripS kp114 s0).readReg64 .x2 = s0.readReg64 .x2 := by cases s0; rfl
      have hr_s0lr : (ProofLib.stripS kp114 s0).readReg64 .lr = s0.readReg64 .lr := by cases s0; rfl
      have hsp_s0 : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
      rw [hm_s0, hm_sf, hr_s00, hsp_s0] at hframe1
      rw [hm_s0, hm_sf, hr_s00, hr_s01, hr_s02, stripExecOutside_readBytes] at hhmac1
      exact ⟨(by rw [hr_s0lr] at hpc1; cases sf; exact hpc1),
        (by cases sf; exact hstat1),
        ⟨by cases s0; cases sf; exact hcs1.1,
         fun r hr => by have := hcs1.2 r hr; cases s0; cases sf; exact this⟩,
        (by rw [hr_s00, stripS_read64] at htag1; exact htag1),
        stripExecOutside_hmacSt.mp hhmac1,
        unstrip_frame hframe1 hvm.perm_eq⟩
    · exact hsf_real
  rcases hsf_raw with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩⟩
  dsimp only [withLsCodeRoLoaded, newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  rw [hx1, hx2_nat, hkey_eq] at hst_sf
  have hpost_sep := Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_sep

private theorem new_from_slice_cro_budget_ok_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec W.C.F)) :=
  new_from_slice_placed_cro_budget_ok_at_block_sat W.C.F
    (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    ((cliGhostExterns_other g (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W))) hi

private theorem hmac_vm_cro_ok_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hmacSpec W.C.F))) :=
  hmac_placed_cro_ok_at_block_sat W.C.F
    (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
    ((cliGhostExterns_other g (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W))) hi

theorem generateKeys_428_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim W.C.F)) := by
  have hG := hH.alloc.toCliGhostAllocHooks
  have _ : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  have _ : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
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
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
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
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
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
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
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

/-- Budget-threaded Block-`428` (`OutgoingTripleRatchet::encrypt`) local callees under
`withLsCodeRoLoaded lsmpl`. -/
structure OtrRoCalleesPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop where
  messageKeys :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec W.C.F A lim))
  signalMessageNew :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim W.C.F uuidTryParse))
  nextChainKey :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec W.C.F))

theorem otrRoCalleesPlacedOk_cli [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    OtrRoCalleesPlacedOk mmpl g W A lim := by
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact
    { messageKeys := transfer_tr_cro_of_block
        (callerProg := (blkPC_428).rebase (blkPl_428).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (calleeProg := (blkPC_38).rebase (blkPl_38).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (message_keys_placed_cro_ok
          (hmac_vm_cro_ok_at_block mmpl g W hH.alloc.toCliGhostAllocHooks
            (callerProg := (blkPC_38).rebase (blkPl_38).base
              (cliGhostExterns g (cliExternsPlaced mmpl W))))
          (cliExternsPlaced_noAllocShim_budget_sat mmpl g W hH.alloc.shim_eq)
          (cliExternsPlaced_alloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks))
      signalMessageNew := signalMessageNew_428_placed_cro_ok mmpl g W A lim hH
      nextChainKey := transfer_tr_cro_of_block
        (callerProg := (blkPC_428).rebase (blkPl_428).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (calleeProg := (blkPC_39).rebase (blkPl_39).base
          (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (nextChainKey_39_vm_cro_ok
          (hmac_vm_cro_ok_at_block mmpl g W hH.alloc.toCliGhostAllocHooks
            (callerProg := (blkPC_39).rebase (blkPl_39).base
              (cliGhostExterns g (cliExternsPlaced mmpl W))))
          ((CliSlotCalleesInstPlacedBudgetSeams.skeletonHooks_of_slotHooks hH).panics
            lsPanicConstAddOverflowSym (by decide))) }

theorem otrEncryptV1_464_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs) :
    subroutine_ok (lsProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (withLsRoCl lsmpl
        (otrEncryptPlacedSpecQF (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length)
          tokenInitPlacedAt W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.spqrSend)) := by
  have hOtrRo := otrRoCalleesPlacedOk_cli mmpl g W A lim hH
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
    hSend428 hOtrRo.messageKeys (generateKeys_428_placed_ok mmpl g W A lim hH)
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
    (S : SpqrModel) (hEmpty : S.SendEmptyOk) :
    subroutine_ok (lsProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (withLsRoCl lsmpl
        (otrEncryptPlacedSpecQ (· = []) W.C A lim 0#64 uuidTryParse S (fun _ _ evs => evs = []))) := by
  have hOtrRo := otrRoCalleesPlacedOk_cli mmpl g W A lim hH
  have _ := instIsLsBlockProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have _ := instIsLsBlockProg_428 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have h428 := otrEncryptEmpty_coins_placed_ok W.C A lim 0#64 S (fun _ _ evs => evs = [])
    (cliGhostExterns g (cliExternsPlaced mmpl W)) hEmpty (fun _ => rfl)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
    hH.aesEnc hH.formatInnerEnv
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hH.alloc.toCliGhostAllocHooks)
    hOtrRo.messageKeys (generateKeys_428_placed_ok mmpl g W A lim hH)
    hOtrRo.signalMessageNew hOtrRo.nextChainKey
  have h428' := subroutine_ok_storeKitCro_of_trCro h428
  change subroutine_ok _ (lsmpl.base 428 + 0#64) _; rw [BitVec.add_zero]
  exact ls_subroutine_ok_rocl_of_block
    (callerProg := lsProg_464 (cliGhostExterns g (cliExternsPlaced mmpl W))) (j := 428)
    h428' (by decide) (by decide) (by decide)

/-- Budget-threaded `W1InnerPlacedOk` on Block `464` from `hDropNz`, `CliSlotAllocHooks`,
`SpqrV1PlacedSeamsBudget`, and `WithStoresEncVTPlacedOk`. -/
theorem w1_inner_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
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
    (otrEncryptV1_464_placed_ok mmpl g W A lim envs hH hSpqr)
    (otrEncryptEmpty_464_placed_ok mmpl g W A lim hH (pqxdhSpqrModel ⟨W.C, W.Q⟩)
      (spqrV1_emptyOk W.C.F W.Q.K))
    (w2SessVt_placed_ok A.repAlloc cliRunBudgets hDropNz)
    (w2IdVt_placed_ok A.repAlloc cliRunBudgets hDropNz)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees
