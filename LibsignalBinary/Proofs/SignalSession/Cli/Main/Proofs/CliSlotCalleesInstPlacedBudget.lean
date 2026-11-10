/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureVmPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `CliSlotCalleesPlaced` Assembly

`RustCliAllocBudget M` counterparts of `CliSlotCalleesInstPlaced.lean`, assembling the encrypt,
decrypt, and session-initiation callee contracts into `CliSlotCalleesPlaced` and
`CliSlotCalleesFullPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (recEntryPlaced recExitPlaced)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles IdentityVtablesPlacedOk SessionOnlyVtablesPlacedOk
)
open CryptoVerification.LibsignalTripleRatchet (region_ok)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (initDef)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget (
  recordDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux (
  CoinsFillCliPlacedOk SubsetA4InitCalleesPlacedCro cliExistingStoreCalleesEnvs
  w2_inner_placed_ok_of_region w3A4_placed_ok
  w3Exist_placed_ok_of_putStr w3Hooks_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetCallees (
  w1_inner_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams (
  CliSlotAllocHooks CliSlotEnvs SpqrV1PlacedSeamsBudget WithStoresEncVTPlacedOk
  decIdKitBudgetEnv decSessKitBudgetEnv w1IdKitBudgetEnv w1SessKitBudgetEnv
  w2IdVt_placed_ok w2SessVt_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget (
  InitLocalCalleesPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget (
  ExistingStoreCalleesPlaced InitStoreCalleesPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget (
  InnerDecryptPlacedOk decIdKitPlaced decSessKitPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget (
  W1InnerPlacedOk
)

/-- Stage-2 initiation callee contract obligation over `RustCliAllocBudget M`. -/
def Stage2PlacedBudgetOk [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem) : Prop :=
  RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
  CoinsFillCliPlacedOk mmpl g W →
  (∀ stk, InitStoreCalleesPlaced A lim (cliExistingStoreCalleesEnvs envs.readFile) mmpl g W B stk) →
  (∀ stk, InitLocalCalleesPlaced A lim envs.spqrInitState mmpl g W stk) →
  S.initiate = initDef X ⟨W.C, W.Q⟩ → True

/-- Stage-3 initiation callee contract obligation over `RustCliAllocBudget M`. -/
def Stage3PlacedBudgetOk [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (_B : RunBudgets) (S : RunSem) : Prop :=
  RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
  CoinsFillCliPlacedOk mmpl g W →
  (∀ stk, InitLocalCalleesPlaced A lim envs.spqrInitState mmpl g W stk) →
  S.initiate = initDef X ⟨W.C, W.Q⟩ → True

/-- Budget-threaded 9-field `CliSlotCalleesPlaced` bundle under `[LibsignalPlacement]`. -/
structure CliSlotCalleesPlaced [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs) : Prop where
  w1Inner : W1InnerPlacedOk mmpl g W A lim cliRunBudgets scopeIn envs.spqrSend
    (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
    (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)
  w2SessVt : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer cliRunBudgets)
  w2IdVt : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer cliRunBudgets)
  w2Inner : InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim
    (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
    envs.tryDecrypt
    (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
    (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)
  w3Hooks : RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W))
  w3Exist : ExistingStoreCalleesPlaced A lim (cliExistingStoreCalleesEnvs envs.readFile)
    (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
  w3A4 : SubsetA4InitCalleesPlacedCro A lim envs.spqrInitState mmpl g W
  w3Stage2 : ∀ (S : RunSem), S.initiate = initDef X ⟨W.C, W.Q⟩ →
    Stage2PlacedBudgetOk mmpl g A lim envs W X cliRunBudgets S
  w3Stage3 : ∀ (S : RunSem), S.initiate = initDef X ⟨W.C, W.Q⟩ →
    Stage3PlacedBudgetOk mmpl g A lim envs W X cliRunBudgets S

theorem w3Stage2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (S : RunSem) (_hS : S.initiate = initDef X ⟨W.C, W.Q⟩) :
    Stage2PlacedBudgetOk mmpl g A lim envs W X cliRunBudgets S := by
  exact fun _ _ _ _ _ => trivial

theorem w3Stage3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (S : RunSem) (_hS : S.initiate = initDef X ⟨W.C, W.Q⟩) :
    Stage3PlacedBudgetOk mmpl g A lim envs W X cliRunBudgets S := by
  exact fun _ _ _ _ => trivial

theorem cliSlotCallees_placed_of_inner [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hEncVT : WithStoresEncVTPlacedOk mmpl g W A lim cliRunBudgets envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hw2Inner : InnerDecryptPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
      envs.tryDecrypt
      (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)) :
    CliSlotCalleesPlaced mmpl g X W A lim envs :=
  { w1Inner := w1_inner_placed_ok mmpl g W A lim envs hDropNz hH hSpqr hEncVT
    w2SessVt := w2SessVt_placed_ok A.repAlloc cliRunBudgets hDropNz
    w2IdVt := w2IdVt_placed_ok A.repAlloc cliRunBudgets hDropNz
    w2Inner := hw2Inner
    w3Hooks := w3Hooks_placed_ok mmpl g W A lim hH
    w3Exist := w3Exist_placed_ok_of_putStr mmpl g W A lim envs.readFile hH
    w3A4 := w3A4_placed_ok mmpl g W A lim envs hH.alloc.toCliGhostAllocHooks hSpqr
    w3Stage2 := w3Stage2_placed_ok mmpl g X W A lim envs
    w3Stage3 := w3Stage3_placed_ok mmpl g X W A lim envs }

/-- Assembles budget-threaded `CliSlotCalleesPlaced` from the Block-`463` `recordDecryptPlacedSpecTPTight`
region obligation `hreg`. -/
theorem cliSlotCallees_placed_of_region [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hEncVT : WithStoresEncVTPlacedOk mmpl g W A lim cliRunBudgets envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hreg : region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
        (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt).withVRegs.restrictPre
        (fun p => (fun _ => True) p.1.st.pqRatchetState))) :
    CliSlotCalleesPlaced mmpl g X W A lim envs :=
  cliSlotCallees_placed_of_inner mmpl g X W A lim envs hDropNz hH hSpqr hEncVT
    (w2_inner_placed_ok_of_region mmpl g W A lim envs hDropNz hH hSpqr hreg)

/-- Assembles budget-threaded `CliSlotCalleesPlaced` from the Block-`462` `logClosurePlacedSpec` seam
`hLog462` and `hregOfLog`. -/
theorem cliSlotCallees_placed_of_seams [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hEncVT : WithStoresEncVTPlacedOk mmpl g W A lim cliRunBudgets envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hLog462 : subroutine_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 462)
      (withLsCodeLoaded lsmpl
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec))
    (hregOfLog :
      subroutine_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 462)
        (withLsCodeLoaded lsmpl
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec) →
      region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
        recEntryPlaced recExitPlaced
        ((recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt).withVRegs.restrictPre
          (fun p => (fun _ => True) p.1.st.pqRatchetState))) :
    CliSlotCalleesPlaced mmpl g X W A lim envs :=
  cliSlotCallees_placed_of_region mmpl g X W A lim envs hDropNz hH hSpqr hEncVT (hregOfLog hLog462)

/-- Budget-threaded `CliSlotCalleesFullPlaced` bundle under `[LibsignalFullPlacement]`, replacing
`w2Inner` with `InnerDecryptFrozenPlacedOk`. -/
structure CliSlotCalleesFullPlaced [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs) : Prop where
  w1Inner : W1InnerPlacedOk mmpl g W A lim cliRunBudgets scopeIn envs.spqrSend
    (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
    (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)
  w2SessVt : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer cliRunBudgets)
  w2IdVt : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer cliRunBudgets)
  w2Inner :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
      ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
      envs.tryDecrypt
      (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)
  w3Hooks : RunHooksPlaced W A lim (cliGhostExterns g (cliExternsPlaced mmpl W))
  w3Exist : ExistingStoreCalleesPlaced A lim (cliExistingStoreCalleesEnvs envs.readFile)
    (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
  w3A4 : SubsetA4InitCalleesPlacedCro A lim envs.spqrInitState mmpl g W
  w3Stage2 : ∀ (S : RunSem), S.initiate = initDef X ⟨W.C, W.Q⟩ →
    Stage2PlacedBudgetOk mmpl g A lim envs W X cliRunBudgets S
  w3Stage3 : ∀ (S : RunSem), S.initiate = initDef X ⟨W.C, W.Q⟩ →
    Stage3PlacedBudgetOk mmpl g A lim envs W X cliRunBudgets S

/-- Proves `InnerDecryptFrozenPlacedOk` on Block `463` from `CliSlotAllocHooks`,
`SpqrV1PlacedSeamsBudget`, and the `withLsFrozen` Block-`463` region obligation `hreg`. -/
theorem w2_inner_frozen_placed_ok_of_region [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    {B : RunBudgets}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hreg : region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt)).withVRegs.restrictPre
        (fun p => (fun _ => True) p.1.st.pqRatchetState))) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
      ⟨W.C, W.Q⟩ A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) B
      envs.tryDecrypt
      (decSessKitBudgetEnv A.repAlloc B envs.sessDeser envs.readFile)
      (decIdKitBudgetEnv A.repAlloc B envs.readFile) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
  intro F0 peer hPeer
  dsimp only
  have hSess := CliSlotCalleesInstPlacedBudgetSeams.w1SessKitPlaced_okSE mmpl g W A lim envs B hDropNz hH hSpqr F0 peer
  have hId := CliSlotCalleesInstPlacedBudgetSeams.w1IdKitPlaced_okIE mmpl g W A lim envs.readFile B hDropNz hH F0 peer
  have hq :
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1SessKitPlaced
        A.repAlloc B F0 peer).Quiet ∧
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1IdKitPlaced
        A.repAlloc B F0 peer).Quiet :=
    ⟨⟨fun _ _ _ => .nil, fun _ _ _ _ => .nil⟩,
     ⟨fun _ _ _ _ => .nil, fun _ _ _ => .nil⟩⟩
  have hraw :=
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_of_runHooks
      mmpl g W
      (ctl := 0#64) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (tdEnv := envs.tryDecrypt)
      (kit := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1SessKitPlaced
        A.repAlloc B F0 peer)
      (kitEnv := w1SessKitBudgetEnv A.repAlloc B envs.sessDeser envs.readFile F0 peer)
      (ikit := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1IdKitPlaced
        A.repAlloc B F0 peer)
      (ikitEnv := w1IdKitBudgetEnv A.repAlloc B envs.readFile F0 peer)
      (st0 := CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions)
      (ist0 := CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity)
      (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (Q := fun _ => True)
      (CliSlotCalleesInstPlacedBudgetSeams.skeletonHooks_of_slotHooks hH) hSess hId hq
      (fun _ hr => CryptoVerification.SignalSession.Cli.Slots.scopeKit_recordInScopeP hr)
      (fun x rec pt rec' haddr hsc hdec =>
        CryptoVerification.SignalSession.Cli.Slots.cliDecModelRecOkAt_opened
          (A := A.repAlloc) (b := 0#64) (pathOk := CryptoVerification.SignalSession.Cli.MainHops.cliWrOk)
          (Scope₀ := scopeIn) (F0 := F0) (peer := peer)
          (s1 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed)
          (s2 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed B.readFile)
          (s3 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.storeShimNeed)
          (s4 := CryptoVerification.SignalSession.Cli.KitInst.SessKit.storePollNeedX)
          (C := W.C) (K := W.Q.K) (parse := uuidTryParse)
          (fun _ h => h) hPeer x rec rec' pt haddr hsc hdec)
      hreg
      (fun _ _ ses hsc hcur =>
        ⟨CryptoVerification.SignalSession.Cli.Slots.scopeKit_pqrState_lt hsc.1 ses hcur, trivial⟩)
  refine subroutine_ok_mono hraw ?_ ?_
  · intro xs R s0 hpre
    dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTPF,
      Spec.restrictPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1SessKitPlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1IdKitPlaced,
      decSessKitPlaced, decIdKitPlaced, decSessKitBudgetEnv, decIdKitBudgetEnv] at hpre ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · intro xs R s0 sf hpost
    dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTP,
      LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget.withStoresDecPlacedSpecVTPF,
      Spec.restrictPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1SessKitPlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.w1IdKitPlaced,
      decSessKitPlaced, decIdKitPlaced, decSessKitBudgetEnv, decIdKitBudgetEnv] at hpost ⊢
    exact hpost

/-- Transfers `InnerDecryptFrozenPlacedOk` from Block `463` to any caller block `i < 619` under
`[LibsignalFullPlacement]`. -/
theorem w2_inner_full_placed_at_block_cli [CryptoVerification.LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    [CryptoVerification.IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hInner463 :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
        ⟨W.C, W.Q⟩ A lim
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
        envs.tryDecrypt
        (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
        (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hi : i < 624 := by decide)
    (F0 : FsFiles) (peer : AddrGhost)
    (hok : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer scopeIn F0 peer.val) :
    let kit := decSessKitPlaced A.repAlloc F0 peer cliRunBudgets
    let ikit := decIdKitPlaced A.repAlloc F0 peer cliRunBudgets
    subroutine_ok callerProg (lsmpl.base 463)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withEnvPre
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP
          W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt CryptoVerification.E2E.Record.encodeRecord
          kit (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile F0 peer)
          ikit (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile F0 peer)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          CryptoVerification.SignalSession.Cli.Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerGluePlacedBudget.w2_inner_full_placed_at_block
    ⟨W.C, W.Q⟩ A lim (cliGhostExterns g (cliExternsPlaced mmpl W))
    cliRunBudgets envs.tryDecrypt
    (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
    (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)
    hInner463 hi F0 peer hok

theorem cliSlotCallees_full_placed_of_inner [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hEncVT : WithStoresEncVTPlacedOk mmpl g W A lim cliRunBudgets envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hw2Inner :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.InnerDecryptFrozenPlacedOk
        ⟨W.C, W.Q⟩ A lim
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
        envs.tryDecrypt
        (decSessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
        (decIdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile)) :
    CliSlotCalleesFullPlaced mmpl g X W A lim envs :=
  { w1Inner := w1_inner_placed_ok mmpl g W A lim envs hDropNz hH hSpqr hEncVT
    w2SessVt := w2SessVt_placed_ok A.repAlloc cliRunBudgets hDropNz
    w2IdVt := w2IdVt_placed_ok A.repAlloc cliRunBudgets hDropNz
    w2Inner := hw2Inner
    w3Hooks := w3Hooks_placed_ok mmpl g W A lim hH
    w3Exist := w3Exist_placed_ok_of_putStr mmpl g W A lim envs.readFile hH
    w3A4 := w3A4_placed_ok mmpl g W A lim envs hH.alloc.toCliGhostAllocHooks hSpqr
    w3Stage2 := w3Stage2_placed_ok mmpl g X W A lim envs
    w3Stage3 := w3Stage3_placed_ok mmpl g X W A lim envs }

/-- Assembles `CliSlotCalleesFullPlaced` under `[LibsignalFullPlacement]` from the `withLsFrozen`
Block-`463` region obligation `hreg`. -/
theorem cliSlotCallees_full_placed_of_region [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hEncVT : WithStoresEncVTPlacedOk mmpl g W A lim cliRunBudgets envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hreg : region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt)).withVRegs.restrictPre
        (fun p => (fun _ => True) p.1.st.pqRatchetState))) :
    CliSlotCalleesFullPlaced mmpl g X W A lim envs :=
  cliSlotCallees_full_placed_of_inner mmpl g X W A lim envs hDropNz hH hSpqr hEncVT
    (w2_inner_frozen_placed_ok_of_region mmpl g W A lim envs hDropNz hH hSpqr hreg)

/-- Closed `[LibsignalFullPlacement]` assembly of `CliSlotCalleesFullPlaced` (with Block `462`
discharged internally via `RecordDecryptPV1TrapPlacedBudget`). -/
theorem cliSlotCallees_full_placed_of_seams [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hEncVT : WithStoresEncVTPlacedOk mmpl g W A lim cliRunBudgets envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hreg : region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt)).withVRegs.restrictPre
        (fun p => (fun _ => True) p.1.st.pqRatchetState))) :
    CliSlotCalleesFullPlaced mmpl g X W A lim envs :=
  cliSlotCallees_full_placed_of_region mmpl g X W A lim envs hDropNz hH hSpqr hEncVT hreg

/-- `[LibsignalFullPlacement]` assembly discharging a `withLsFrozen`-guarded Block-`462` premise via
`log_closure_coins_frozen_vm_placed_ok_of_block`. -/
theorem cliSlotCallees_full_placed_of_seams_of_log [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (envs : CliSlotEnvs)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hH : CliSlotAllocHooks mmpl g W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl g W A lim envs)
    (hEncVT : WithStoresEncVTPlacedOk mmpl g W A lim cliRunBudgets envs.spqrSend
      (w1SessKitBudgetEnv A.repAlloc cliRunBudgets envs.sessDeser envs.readFile)
      (w1IdKitBudgetEnv A.repAlloc cliRunBudgets envs.readFile))
    (hregOfLog :
      subroutine_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 462)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (LibsignalBinary.Heap.SpecBudget.withVmPreserved
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) →
      region_ok (lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))
        recEntryPlaced recExitPlaced
        ((CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (recordDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
            (pqxdhSpqrModel ⟨W.C, W.Q⟩) envs.tryDecrypt)).withVRegs.restrictPre
          (fun p => (fun _ => True) p.1.st.pqRatchetState))) :
    CliSlotCalleesFullPlaced mmpl g X W A lim envs :=
  cliSlotCallees_full_placed_of_region mmpl g X W A lim envs hDropNz hH hSpqr hEncVT
    (hregOfLog
      (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureVmPlacedBudget.log_closure_coins_frozen_vm_placed_ok_of_block
        (callerProg := lsProg_463 (cliGhostExterns g (cliExternsPlaced mmpl W)))))

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget
