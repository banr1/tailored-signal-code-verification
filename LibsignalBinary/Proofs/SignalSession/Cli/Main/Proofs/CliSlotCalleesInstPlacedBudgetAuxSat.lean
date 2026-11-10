/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCalleesSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat

/-!
# `HookSat` Sibling of `CliSlotCalleesInstPlacedBudgetAux` (`CliSlotCalleesInstPlacedBudgetAuxSat`)

Budget-threaded relocatable `[LibsignalPlacement]` W2 glue and W3 store/local callees replacing
`HooksPlacedBudget.RunHooksPlaced` / `HkdfPlacedHooks` (`= some hookMemset`) with
`HooksPlacedBudgetSat.RunHooksPlacedSat` / `HkdfPlacedHooksBudgetSat` under
`(hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec)`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAuxSat

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_207 blkPC_40 blkPl_207 blkPl_40
   libsignalMutatedBlocks lsProg_40 lsProg_59 lsRustNoAllocShimSym lsmpl)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.E2E.Pqxdh.Initiator (structuralPrims_initiatorModelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore (primitivesMatchCrypto_modelPrims)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles extract_withLsCodeRoLoaded withEnvPre withLsCodeRoLoaded)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (lsMemsetSym)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro noAllocShimSpec region_ok)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (initProgPlaced stk_sub_ge_base transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget
  (recordDecryptPlacedSpecTPTight)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget (handshakeKeysDerive_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (ct_eq_ro_placed_vm_ok_of_block)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
  (expand_multi_info_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (extract_placed_vm_ok_of_other_block_sat pqxdhHkdfExpandMultiInfo_placed_ok_sat
   pqxdhHkdfExtract_placed_ok_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget
  (isSameAccountDistinctSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (CliSlotAllocHooks CliSlotEnvs SpqrV1PlacedSeamsBudget decIdKitBudgetEnv decSessKitBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudgetSat
  (calculateAgreement_cli_placed_ok derivePubKeyBytes_cli_placed_ok
   dropSessionStructure_cli_placed_ok kemCtSerialize_cli_placed_ok
   kemPublicKeySerialize_local2_placed_ok promoteState_cli_placed_ok sessionStateNew_cli_placed_ok
   setKyberCiphertext_cli_placed_ok setUnackKyberId_cli_placed_ok setUnackPreKeyMsg_cli_placed_ok
   spqrChainParams_cli_placed_ok withReceiverChain_cli_placed_ok withSenderChain_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptPlacedOk decIdKitPlaced decSessKitPlaced withStoresDecPlacedSpecVTP)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget (calculateAgreement_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (createChain_placed_ok_of_contracts extractBudgetSpec
   subroutine_ok_createChainSpecX_of_createChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec)

export LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
  (cliExistingStoreCalleesEnvs SetUnackEpochPlacedOk CoinsFillCliPlacedOk
   SubsetA4InitCalleesPlacedCro)

/-! ## 1. W2 Inner Decrypt Region Instantiation & Caller Transfer -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` `InnerDecryptPlacedOk` on Block `463` from
`hDropNz`, `CliSlotAllocHooks`, `SpqrV1PlacedSeamsBudget`, and `hreg`. -/
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
      (decIdKitBudgetEnv A.repAlloc B envs.readFile) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux.w2_inner_placed_ok_of_region
    mmpl g W A lim envs hDropNz hH hSpqr hreg

/-- Transfers budget-threaded `InnerDecryptPlacedOk` on Block `463` to any caller block `i < 619`
at the canonical CLI store-kit budget envelopes `decSessKitBudgetEnv` / `decIdKitBudgetEnv`. -/
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
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux.w2_inner_placed_at_block_cli
    mmpl g W A lim envs hInner463 hi F0 peer hok

/-! ## 2. W3 Hooks, Store Callees, `SetUnackEpoch`, `CoinsFill`, `SubsetA4`, & `InitLocalCallees` -/

/-- Discharges `HooksPlacedBudget.RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W))`
from `CliSlotAllocHooks` and `HookSat … lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem w3Hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  let _ := hMs
  exact RunHooksPlaced.of_hooks mmpl g W hH.alloc hH.strClone_fsT hH.stringClone hH.formatInner

/-- Discharges all 16 fields of `ExistingStoreCalleesPlaced` at `cliExistingStoreCalleesEnvs`. -/
theorem w3Exist_placed_ok_of_putStr [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    ExistingStoreCalleesPlaced A lim (cliExistingStoreCalleesEnvs ReadEnv)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets :=
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux.w3Exist_placed_ok_of_putStr
    mmpl g W A lim ReadEnv hH

theorem setUnackEpochPlacedOk_cli [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : CliSlotAllocHooks mmpl g W A lim ReadEnv) :
    SetUnackEpochPlacedOk mmpl g W A lim :=
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux.setUnackEpochPlacedOk_cli
    mmpl g W A lim hH

theorem coinsFillCliPlacedOk_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    CoinsFillCliPlacedOk mmpl g W :=
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux.coinsFillCliPlacedOk_cli
    mmpl g W hG

/-- Unconditional Block-`17` `isSameAccountDistinctSpec` contract on `initProgPlaced mmpl g W`. -/
theorem w3IsSameAccount_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (A : CryptoVerification.RustHeap.RustAlloc) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl g W) (lsmpl.base 17)
      (withLsCodeRoLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux.w3IsSameAccount_placed_ok
    mmpl g A W

/-- Block-`54` `extractBudgetSpec W.C.F` contract on Block `40` under
`LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl` from `CliGhostAllocHooks` and `hMs`. -/
theorem w3HkdfExtract40_cro_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec) :
    subroutine_ok
      ((blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 54)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (extractBudgetSpec W.C.F)) := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hMs
  exact extract_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))

/-- Discharges all 6 fields of `SubsetA4InitCalleesPlacedCro` from `CliGhostAllocHooks`, `hMs`,
and `SpqrV1PlacedSeamsBudget`. -/
theorem w3A4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs) :
    SubsetA4InitCalleesPlacedCro A lim envs.spqrInitState mmpl g W := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat hMs
  exact
    { verifySignature := hSpqr.verifySignature
      isSameAccount := w3IsSameAccount_placed_ok mmpl g A.repAlloc W
      spqrInitialState := hSpqr.spqrInitialState_initProg
      pqxdhHkdfExtract := fun X => pqxdhHkdfExtract_placed_ok_sat
        (primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
      pqxdhHkdfExpand := fun X => pqxdhHkdfExpandMultiInfo_placed_ok_sat
        (primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
      hkdfExtract40 := w3HkdfExtract40_cro_placed_ok mmpl g W hG hMs }

private theorem hookSat_of_keepsFs {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (h : HookSat H sym spec.keepsFs) : HookSat H sym spec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · dsimp only [Spec.keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hkf, hsym, Or.inl ⟨hret, hcc, hpost.2⟩⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

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

/-- Discharges all 19 fields of `LocalCalleesPlacedBudget.InitLocalCalleesPlaced` from
`CliSlotAllocHooks`, `hMs`, and `SpqrV1PlacedSeamsBudget`. -/
theorem w3Local_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (B : RunBudgets)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitLocalCalleesPlaced A lim envs.spqrInitState mmpl g W stk := by
  let hh := w3Hooks_placed_ok mmpl g W A lim hH hMs
  have ha4 := w3A4_placed_ok mmpl g W A lim envs hH.alloc.toCliGhostAllocHooks hMs hSpqr
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

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAuxSat
