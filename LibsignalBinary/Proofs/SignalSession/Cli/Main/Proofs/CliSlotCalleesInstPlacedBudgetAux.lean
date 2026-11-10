/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillVmPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShimPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShimPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Inner Decrypt and Initiation Store/Local Callees

Proves the `RustCliAllocBudget M` inner decrypt instantiation/transfer (`w2_inner_placed_ok_of_region`,
`w2_inner_placed_at_block_cli`) and session-initiation store/local callee bundles (`w3Hooks_placed_ok`,
`w3Exist_placed_ok_of_putStr`, `w3A4_placed_ok`, `w3Local_placed_ok`) used by
`CliSlotCalleesInstPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_40 blkPC_59 blkPC_207
  blkPl_40 blkPl_59 blkPl_207 libsignalMutatedBlocks lsProg_40 lsProg_59 lsRustNoAllocShimSym
  lsmpl withLsCodeLoaded
)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims pqxdhSpqrModel)
open CryptoVerification.E2E.Pqxdh.Initiator (structuralPrims_initiatorModelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  ofSignalPqxdhPrimitives primitivesMatchCrypto_modelPrims
)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withEnvPre withLsCodeRoLoaded
)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks extHookStack keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro
  noAllocShimSpec publicKeySerializeStackX region_ok
)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.KitInst (
  rodata_cliIdentity_kpSlot_placed rodata_cliIdentity_regIdSlot_placed
  rodata_cliIdentity_saveSlot_placed rodata_cliIdentity_trustSlot_placed
  rodata_cliSession_loadSlot_placed rodata_cliSession_storeSlot_placed
)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (
  loadPollNeed loadShimNeed storePollNeedX storeShimNeed
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_569 lsProg_589)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (
  cliCoinsFillStack coinsFillSpecPlacedW3 initProgPlaced sessLoadPoll_stk_le stk_sub_ge_base
  stk_sub_ge_dirGet transfer_withLsCodeRoLoaded
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer cliDecModelRecOkAt_opened scopeIn scopeKit scopeKit_pqrState_lt
  scopeKit_recordInScopeP
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (
  withStoresDecPlacedSpecVX
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget (
  recordDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget (
  cliDecryptSignalWithStores_placed_okVTP_distinct_fs_of_runHooks
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget (
  PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk handshakeKeysDerive_placed_ok
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget (
  ct_eq_ro_placed_vm_ok_of_block expand_multi_info_placed_vm_ok_of_other_block
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat (
  expand_multi_info_placed_vm_ok_of_other_block_sat
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget (
  extract_placed_vm_ok_of_other_block pqxdhHkdfExpandMultiInfo_placed_ok pqxdhHkdfExtract_placed_ok
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat (
  extract_placed_vm_ok_of_other_block_sat pqxdhHkdfExpandMultiInfo_placed_ok_sat
  pqxdhHkdfExtract_placed_ok_sat
)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget (
  isSameAccountDistinctSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget (
  isSameAccountEqDistinct_placed_ok_at
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudget (AddrTextEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (
  cliAddrText_placed_ok cliDirGet_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees (
  uuidTryParse_252_vm_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams (
  CliSlotAllocHooks CliSlotEnvs SpqrV1PlacedSeamsBudget cliDirPutStrNeedPlaced
  cliGhostExterns_blackBox_eq decIdKitBudgetEnv decSessKitBudgetEnv dirPutStrPlacedOk_cli
  skeletonHooks_of_slotHooks w1IdKitBudgetEnv w1IdKitPlaced_okIE w1SessKitBudgetEnv
  w1SessKitPlaced_okSE w3DirPut_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillVmPlacedBudget (
  signal_session_coins_fill_vm_placed_ok_at_init
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (
  RunHooksPlaced instHkdfPlacedHooks_cliGhost
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget (
  InitLocalCalleesPlaced calculateAgreement_cli_placed_ok derivePubKeyBytes_cli_placed_ok
  dropSessionStructure_cli_placed_ok kemCtSerialize_cli_placed_ok
  kemPublicKeySerialize_local2_placed_ok promoteState_cli_placed_ok sessionStateNew_cli_placed_ok
  setKyberCiphertext_cli_placed_ok setUnackKyberId_cli_placed_ok setUnackPreKeyMsg_cli_placed_ok
  spqrChainParams_cli_placed_ok spqrInitialStateInnerSpec verifySignatureInnerSpec
  withReceiverChain_cli_placed_ok withSenderChain_cli_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget (
  ExistingStoreCalleesEnvs ExistingStoreCalleesPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget (
  w2_inner_placed_at_block
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget (
  InnerDecryptPlacedOk decIdKitPlaced decSessKitPlaced withStoresDecPlacedSpecVTP
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  w1IdKitPlaced w1SessKitPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_sessionMemsetRegion_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget (
  setUnackPreKeyMsgExactStackEpochSpecPlaced setUnackPreKeyMsg_exact_stack_epoch_placed_ok_cli
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  dirGetSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudget (
  CliIdSavePollEnv idSavePoll_placed_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlacedBudget (
  idSaveShim_placed_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget (
  CliIdTrustPollEnv idTrustPoll_placed_ok_of_deps identityKey_decode_placed_ok
  publicKeyEq_placed_ok_of_bb
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShimPlacedBudget (
  idTrustShim_placed_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (CliLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget (
  sessLoadPoll_placed_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShimPlacedBudget (
  sessLoadShim_placed_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlacedBudget (
  sessStoreShim_placed_ok_of_deps
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget (calculateAgreement_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget (
  createChain_placed_ok_of_contracts extractBudgetSpec
  subroutine_ok_createChainSpecX_of_createChainSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec)

/-! ## Inner Decrypt Region Instantiation and Caller Transfer -/

/-- Proves `InnerDecryptPlacedOk` on Block `463` from `CliSlotAllocHooks`,
`SpqrV1PlacedSeamsBudget`, and the Block-`463` region obligation `hreg`. -/
theorem w2_inner_placed_ok_of_region [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    {B : RunBudgets}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hreg : region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
        (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt).withVRegs.restrictPre
        (fun p => (fun _ => True) p.1.st.pqRatchetState))) :
    InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) B
      envs.tryDecrypt
      (decSessKitBudgetEnv A.repAlloc B envs.sessDeser envs.readFile)
      (decIdKitBudgetEnv A.repAlloc B envs.readFile) := by
  unfold InnerDecryptPlacedOk
  intro F0 peer hPeer
  dsimp only
  have hSess := w1SessKitPlaced_okSE mmpl g W A lim envs B hDropNz hH hSpqr F0 peer
  have hId := w1IdKitPlaced_okIE mmpl g W A lim envs.readFile B hDropNz hH F0 peer
  have hq : (w1SessKitPlaced A.repAlloc B F0 peer).Quiet ∧
      (w1IdKitPlaced A.repAlloc B F0 peer).Quiet :=
    ⟨⟨fun _ _ _ => .nil, fun _ _ _ _ => .nil⟩,
     ⟨fun _ _ _ _ => .nil, fun _ _ _ => .nil⟩⟩
  have hraw := cliDecryptSignalWithStores_placed_okVTP_distinct_fs_of_runHooks mmpl g W
    (ctl := 0#64) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (tdEnv := envs.tryDecrypt)
    (kit := w1SessKitPlaced A.repAlloc B F0 peer)
    (kitEnv := w1SessKitBudgetEnv A.repAlloc B envs.sessDeser envs.readFile F0 peer)
    (ikit := w1IdKitPlaced A.repAlloc B F0 peer)
    (ikitEnv := w1IdKitBudgetEnv A.repAlloc B envs.readFile F0 peer)
    (st0 := CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions)
    (ist0 := CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity)
    (Scope := scopeKit) (Q := fun _ => True)
    (skeletonHooks_of_slotHooks hH) hSess hId hq
    (fun _ hr => scopeKit_recordInScopeP hr)
    (fun x rec pt rec' haddr hsc hdec =>
      cliDecModelRecOkAt_opened
        (A := A.repAlloc) (b := 0#64) (pathOk := cliWrOk)
        (Scope₀ := scopeIn) (F0 := F0) (peer := peer)
        (s1 := loadShimNeed) (s2 := loadPollNeed B.readFile)
        (s3 := storeShimNeed) (s4 := storePollNeedX)
        (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
        (fun _ h => h) hPeer x rec rec' pt haddr hsc hdec)
    hreg
    (fun _ _ ses hsc hcur => ⟨scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
  refine subroutine_ok_mono hraw ?_ ?_
  · intro xs R s0 hpre
    dsimp only [withEnvPre, withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTPF,
      Spec.restrictPre, w1SessKitPlaced, w1IdKitPlaced,
      decSessKitPlaced, decIdKitPlaced, decSessKitBudgetEnv, decIdKitBudgetEnv] at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · intro xs R s0 sf hpost
    dsimp only [withEnvPre, withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTPF,
      Spec.restrictPre, w1SessKitPlaced, w1IdKitPlaced,
      decSessKitPlaced, decIdKitPlaced, decSessKitBudgetEnv, decIdKitBudgetEnv] at hpost ⊢
    exact hpost

/-- Transfers `InnerDecryptPlacedOk` from Block `463` to any caller block `i < 619` at
`decSessKitBudgetEnv` and `decIdKitBudgetEnv`. -/
theorem w2_inner_placed_at_block_cli [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hInner463 : InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
      envs.tryDecrypt
      (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hi : i < 619 := by decide)
    (F0 : FsFiles) (peer : AddrGhost) (hok : FilesOkPeer scopeIn F0 peer.val) :
    let kit := decSessKitPlaced A.repAlloc F0 peer cliRunBudgets
    let ikit := decIdKitPlaced A.repAlloc F0 peer cliRunBudgets
    subroutine_ok callerProg (lsmpl.base 463)
      (withEnvPre
        (withStoresDecPlacedSpecVTP W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt encodeRecord
          kit (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile F0 peer)
          ikit (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile F0 peer)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  w2_inner_placed_at_block ⟨W.C, W.Q⟩ A lim (cliGhostExterns g (cliExternsPlaced mmpl W))
    cliRunBudgets envs.tryDecrypt
    (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
    (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)
    hInner463 hi F0 peer hok

/-! ## Initiation Hooks, Store Callees, and Local Callees -/

theorem w3Hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  RunHooksPlaced.of_hooks mmpl g W hH.alloc hH.strClone_fsT hH.stringClone hH.formatInner

private theorem sessDeserialize_false_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} :
    subroutine_ok prog (lsmpl.base 46)
      (sessDeserializeSpecPlaced (fun _ => False) A lim (fun _ _ => False)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 _ _ hpre _ => ?_
  obtain ⟨_, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessDeserializeSpecPlaced] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1 with ⟨_, _, _, hf, _⟩
  exact False.elim hf

/-- Exact deterministic `AllocEvent` envelopes for all 6 `ExistingStoreCalleesEnvs` fields. -/
def cliExistingStoreCalleesEnvs
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    ExistingStoreCalleesEnvs where
  dirGet := DirGetEnv PathEnv ReadEnv cliIo.rd
  addressText := AddrTextEnv DecimalEnv
  dirPut := DirPutEnv
  idTrustPoll := CliIdTrustPollEnv (DirGetEnv PathEnv ReadEnv cliIo.rd)
  sessLoadPoll := CliLoadPollEnv cliIo.rd (fun _ => False) (AddrTextEnv DecimalEnv)
    (DirGetEnv PathEnv ReadEnv cliIo.rd) (fun _ _ => False)
  idSavePoll := CliIdSavePollEnv cliIo.rd (DirGetEnv PathEnv ReadEnv cliIo.rd) DirPutStrEnv

theorem w3Exist_placed_ok_of_putStr [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    ExistingStoreCalleesPlaced A lim (cliExistingStoreCalleesEnvs ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets := by
  let hh := skeletonHooks_of_slotHooks hH
  let hh3 := w3Hooks_placed_ok mmpl g W A lim hH
  have hAddr := cliAddrText_placed_ok hh
  have hGet : subroutine_ok (lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd)
        cliRunBudgets.dirGetNeed) :=
    cliDirGet_placed_ok
      (readProg := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 589)
      (fun _ hp => hp.2) hh (hH.readFile cliRunBudgets.readFile) (by decide) (by decide)
  have hPutStr := dirPutStrPlacedOk_cli mmpl g W A lim hH
  have hEq := publicKeyEq_placed_ok_of_bb (cliGhostExterns_blackBox_eq mmpl g W)
  have hDec := identityKey_decode_placed_ok (A := A) (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact
    { dirGet := hGet
      addressText := hAddr
      dirPut := w3DirPut_placed_ok mmpl g W A lim hH
      idTrustShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact idTrustShim_placed_ok_of_deps hh.alloc (by omega)
      idTrustPoll := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have := stk_sub_ge_dirGet hstk
        have : extHookStack ≤ 65536 := by decide
        exact idTrustPoll_placed_ok_of_deps hh.alloc hGet hDec hEq (by omega)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      sessLoadShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x20 + extHookStack ≤ 516880 := by decide
        exact sessLoadShim_placed_ok_of_deps hh.alloc (by omega)
      sessLoadPoll := fun {stk} hstk =>
        sessLoadPoll_placed_ok_of_deps hh.alloc hAddr hGet
          (sessDeserialize_false_placed_ok
            (prog := lsProg_569 (cliGhostExterns g (cliExternsPlaced mmpl W))))
          (hh3.fs (prog := lsProg_569 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 569))
          (sessLoadPoll_stk_le (by decide) hstk)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      idSaveShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact idSaveShim_placed_ok_of_deps hh.alloc (by omega)
      idSavePoll := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have := stk_sub_ge_dirGet hstk
        have : cliDirPutStrNeedPlaced ≤ 65536 := by decide
        have : publicKeySerializeStackX ≤ 65536 := by decide
        have : extHookStack ≤ 65536 := by decide
        exact idSavePoll_placed_ok_of_deps hh.alloc hGet hPutStr hDec hEq (by omega)
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      sessStoreShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact sessStoreShim_placed_ok_of_deps hh.alloc (by omega)
      rodata_idVt_keyPairSlot := rodata_cliIdentity_kpSlot_placed
      rodata_idVt_regIdSlot := rodata_cliIdentity_regIdSlot_placed
      rodata_idVt_saveSlot := rodata_cliIdentity_saveSlot_placed
      rodata_idVt_trustSlot := rodata_cliIdentity_trustSlot_placed
      rodata_sessVt_loadSlot := rodata_cliSession_loadSlot_placed
      rodata_sessVt_storeSlot := rodata_cliSession_storeSlot_placed }

/-- Budget-threaded Block-`33` `set_unacknowledged_pre_key_message` contract obligation. -/
def SetUnackEpochPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 33)
    (setUnackPreKeyMsgExactStackEpochSpecPlaced A lim)

theorem setUnackEpochPlacedOk_cli [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    SetUnackEpochPlacedOk mmpl g W A lim :=
  setUnackPreKeyMsg_exact_stack_epoch_placed_ok_cli mmpl g W hH.alloc.toCliGhostAllocHooks
    (by decide)

/-- Budget-threaded (`VmPreserved`) Block-`618` `coinsFillSpecPlacedW3` contract obligation. -/
def CoinsFillCliPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
    subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (coinsFillSpecPlacedW3 cStk)))

theorem coinsFillCliPlacedOk_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    CoinsFillCliPlacedOk mmpl g W :=
  fun {_cStk} hstk hstk64 => signal_session_coins_fill_vm_placed_ok_at_init mmpl g W hG hstk hstk64

theorem w3IsSameAccount_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (A : CryptoVerification.RustHeap.RustAlloc) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 17)
      (withLsCodeRoLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) := by
  have hisa := isSameAccountEqDistinct_placed_ok_at A
    (callerProg := initProgPlaced mmpl g W) (cliGhostExterns_blackBox_eq mmpl g W)
    (uuidTryParse_252_vm_placed_ok (cliGhostExterns g (cliExternsPlaced mmpl W))) (by decide)
  refine subroutine_ok_mono hisa (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hc, hpre⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withLsCodeLoaded]
  have h1 : s0.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
      ((isSameAccountDistinctSpec A uuidTryParse).pre x s0 ∗ R) := by
    rw [satisfies_pure_sepConj]; exact ⟨hc.1, hpre⟩
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1

/-- Block-`54` `extractBudgetSpec W.C.F` contract on Block `40` under `withLsCodeRoLoaded lsmpl` from `CliGhostAllocHooks`. -/
theorem w3HkdfExtract40_cro_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 54)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (extractBudgetSpec W.C.F)) := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  exact extract_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))

/-- 6-field Subset-A4 callee bundle on Block `40` with Block `54` (`extractBudgetSpec W.C.F`) wrapped
in `withLsCodeRoLoaded lsmpl`. -/
structure SubsetA4InitCalleesPlacedCro [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitStateEnv : Params → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) : Prop where
  verifySignature : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩)))
  isSameAccount :
    subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 17)
      (withLsCodeRoLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse))
  spqrInitialState :
    subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F))
  pqxdhHkdfExtract : ∀ (X : UnreachedPqxdhPrimitives),
    PqxdhHkdfExtractPlacedOk (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      ((blkPC_59).rebase (blkPl_59).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
  pqxdhHkdfExpand : ∀ (X : UnreachedPqxdhPrimitives),
    PqxdhHkdfExpandMultiInfoPlacedOk (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      ((blkPC_59).rebase (blkPl_59).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
  hkdfExtract40 :
    subroutine_ok
      ((blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 54)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (extractBudgetSpec W.C.F))

theorem w3A4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hG : CliGhostAllocHooks M A lim g)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs) :
    SubsetA4InitCalleesPlacedCro A lim envs.spqrInitState mmpl g W := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  exact
    { verifySignature := hSpqr.verifySignature
      isSameAccount := w3IsSameAccount_placed_ok mmpl g A.repAlloc W
      spqrInitialState := hSpqr.spqrInitialState_initProg
      pqxdhHkdfExtract := fun X => pqxdhHkdfExtract_placed_ok_sat
        (primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
      pqxdhHkdfExpand := fun X => pqxdhHkdfExpandMultiInfo_placed_ok_sat
        (primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
      hkdfExtract40 := w3HkdfExtract40_cro_placed_ok mmpl g W hG }

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

private theorem transfer_tr_codeRoLoaded [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    [IsLsBlockProg calleeProg j (cliGhostExterns g (cliExternsPlaced mmpl W))]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (initProgPlaced mmpl g W) entry (withLsCodeRoLoaded lsmpl spec) := by
  have hcrl : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono hcallee
      (fun _ _ _ hp => by
        obtain ⟨hc, hpre⟩ := extract_withLsCodeRoLoaded hp
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
      (fun _ _ _ _ hq => hq)
  exact transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl g W) hcrl (by decide) hj hj_unmut

private theorem hookSat_of_keepsFs {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (h : HookSat H sym spec.keepsFs) :
    HookSat H sym spec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest

private theorem createChain40_cro_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_40).base
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (createChainSpec M A lim W.C)) := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) := hh.hkdf
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat (hookSat_of_keepsFs hh.memsetRegionKeepsFs)
  have hct207 := ct_eq_ro_placed_vm_ok_of_block
    (callerProg := (blkPC_207).rebase (blkPl_207).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    hh.blackBox (by decide)
  have hag40 := keys_ls_subroutine_ok_of_block_cro
    (callerProg := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (calculateAgreement_placed_ok hh.dh hh.sharedDrop hct207
      (hookSat_noAllocShimBudget_of_withVmPreserved hh.shim) hh.rawAlloc hh.staticDrop)
  have hext40 := extract_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hexp40 := expand_multi_info_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hdealloc40 := keys_ls_hook_ok_of_mem
    (prog := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (i := 40) hh.rawDealloc
  exact createChain_placed_ok_of_contracts (C := W.C) hag40 hext40 hexp40 hdealloc40

/-- Discharges all 19 fields of `InitLocalCalleesPlaced` from `CliSlotAllocHooks` and
`SpqrV1PlacedSeamsBudget`. -/
theorem w3Local_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (B : RunBudgets)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitLocalCalleesPlaced A lim envs.spqrInitState mmpl g W stk := by
  let hh := w3Hooks_placed_ok mmpl g W A lim hH
  have ha4 := w3A4_placed_ok mmpl g W A lim envs hH.alloc.toCliGhostAllocHooks hSpqr
  have hcc40 := createChain40_cro_placed_ok mmpl g W hh
  exact
    { kemPubSerialize := kemPublicKeySerialize_local2_placed_ok mmpl g W hh (by
        have h1 := stk_sub_ge_base hstk
        have hext : extHookStack ≤ 65536 := by decide
        omega)
      dropSessionStructure := dropSessionStructure_cli_placed_ok mmpl g W hh
      verifySignature := ha4.verifySignature
      isSameAccount := ha4.isSameAccount
      calculateAgreement := calculateAgreement_cli_placed_ok mmpl g W hh
      derivePubKeyBytes := derivePubKeyBytes_cli_placed_ok mmpl g W hh
      handshakeDerive := fun X =>
        transfer_tr_codeRoLoaded
          (calleeProg := lsProg_59 (cliGhostExterns g (cliExternsPlaced mmpl W)))
          (handshakeKeysDerive_placed_ok
            (structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩)
            (ha4.pqxdhHkdfExtract X) (ha4.pqxdhHkdfExpand X))
      kemCtSerialize := kemCtSerialize_cli_placed_ok mmpl g W hh
      rootKeyCreateChain := transfer_tr_codeRoLoaded
        (calleeProg := lsProg_40 (cliGhostExterns g (cliExternsPlaced mmpl W))) hcc40
      rootKeyCreateChainX := transfer_tr_codeRoLoaded
        (calleeProg := lsProg_40 (cliGhostExterns g (cliExternsPlaced mmpl W)))
        (subroutine_ok_createChainSpecX_of_createChainSpec hcc40)
      spqrChainParams := spqrChainParams_cli_placed_ok mmpl g W
      spqrInitialState := ha4.spqrInitialState
      sessionStateNew := sessionStateNew_cli_placed_ok mmpl g W hh
      withReceiverChain := withReceiverChain_cli_placed_ok mmpl g W hh
      withSenderChain := withSenderChain_cli_placed_ok mmpl g W hh
      setKyberCiphertext := setKyberCiphertext_cli_placed_ok mmpl g W
      setUnackPreKeyMsg := setUnackPreKeyMsg_cli_placed_ok mmpl g W hh
      setUnackKyberId := setUnackKyberId_cli_placed_ok mmpl g W
      promoteState := promoteState_cli_placed_ok mmpl g W hh }

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
