/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlot

/-!
# Relocatable Instantiation of `run` into `main`

Instantiates the relocatable `run` subroutine contract into `main` (Block `617`) under
`[LibsignalPlacement]` and `[LibsignalFullPlacement]`, yielding the SM-domain and PQXDH-domain
functional specifications over `cliGhostExterns gh (cliExternsPlaced mmpl W)`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.Slots
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-- Hook bundle for `main` (Block `617`) under `cliHookTablePlaced mmpl W` and `CliGhostHooks`. -/
structure CliA0MainHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) : Prop where
  allocFs : AllocContractsFsPlaced E2E.HooksE.A0
    (cliGhostExterns gh (cliExternsPlaced mmpl W))
  readStdin : subroutine_ok (lsProg_617 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsρ lsReadStdinSym)
    (withLsRoCl lsmpl (readStdinSpecPlaced cliIo E2E.HooksE.A0 cliHookStack))
  readFile : subroutine_ok (lsProg_617 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsρ lsReadFileSym)
    (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo E2E.HooksE.A0 cliHookStack))

theorem CliA0MainHooks.of_hookSat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hAllocFs : AllocContractsFsPlaced E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadStdin : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo E2E.HooksE.A0 cliHookStack))
    (hReadFile : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo E2E.HooksE.A0 cliHookStack)) :
    CliA0MainHooks mmpl gh W :=
  ⟨hAllocFs, readStdin_rocl_ok_of_hookSat hReadStdin, readFile_rocl_ok_of_hookSat hReadFile⟩

/-- Hook and `read_file` bundle for `run` (Block `579`) under `cliHookTablePlaced mmpl W` and `CliGhostHooks`. -/
structure CliA0RunHooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) : Prop where
  runHooks : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
  readFile579 : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile)

/-- Default `UnreachedPqxdhPrimitives` witness for the SM domain, which never invokes `initiate` or `decrypt_prekey`. -/
def defaultModelExtras_placed : UnreachedPqxdhPrimitives where
  sigPkGen _ := []
  sigSign _ _ _ := []
  scalarMul _ _ := []
  scalarAdd _ _ := []
  kemKeyGen _ := ([], [])
  pow8 _ := []
  isValidDhTriple _ _ _ := false

/-- Concrete `RunSem` at `Slots.scopeIn`, parameterized over `decrypt_prekey` and `PreKeySignalMessage::try_from`. -/
noncomputable def cliRunSem_placed (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) : RunSem where
  encrypt := encDef ⟨W.C, W.Q⟩ Slots.scopeIn
  decryptSignal := decSigDef ⟨W.C, W.Q⟩ Slots.scopeIn
  initiate := initDef X ⟨W.C, W.Q⟩
  decryptPrekey := decPk
  pksmParse := pksmParse
  filesOk := Slots.filesOk₀ Slots.scopeIn (fun _ => True)
  encOk := Slots.encOk₀ Slots.scopeIn
  initOk := InitOk₀ ⟨W.C, W.Q⟩
  decPkOk := decPkOk

/-- Existential witness for the all-inputs `PreKeySignalMessage::try_from` slot on Block `579`. -/
def CliPksmSlotExistsPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∃ pksmParse : List (BitVec 8) → Option PreKeySignalMessage,
    ∀ S : RunSem, S.pksmParse = pksmParse →
      subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (CryptoVerification.blkPl_111).base
        (pksmSlotSpecPlaced E2E.HooksE.A0 S)

/-- Existential witness for the `decrypt_prekey` slot on Block `579`. -/
def CliDecPkSlotExistsPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∃ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
        SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (decPkNeed : Nat),
    decPkNeed ≤ 4194304 ∧
    ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPk →
      S.decPkOk = decPkOk →
      needs.decryptPrekey = decPkNeed →
      (slotsOfPlaced E2E.HooksE.A0 S needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)

/-- Existential witness for the frozen `decrypt_prekey` slot (`slotsOfSigPkFrozenPlaced`) on Block `579`. -/
def CliDecPkSlotExistsFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∃ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
        SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (decPkNeed : Nat),
    decPkNeed ≤ 4194304 ∧
    ∀ (S : RunSem) (needs : RunNeeds),
      S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
      S.decryptPrekey = decPk →
      S.decPkOk = decPkOk →
      needs.decryptPrekey = decPkNeed →
      (slotsOfSigPkFrozenPlaced E2E.HooksE.A0 S needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)

/-- Public-API and directory callee obligations on Block `579`, paired with `CliA0RunHooks` and `RunArmsPlaced`. -/
structure CliPubCalleesPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) : Prop where
  a0Run : CliA0RunHooks mmpl gh W
  dirGet : ∀ {stk : Nat}, cliRunBudgets_placed.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)
  bundleRead : ∀ {stk : Nat}, cliRunBudgets_placed.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 563)
      (bundleReadSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 593)
      (splitIdSpecPlaced E2E.HooksE.A0 stk)
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 592)
      (splitSignedSpecPlaced E2E.HooksE.A0 stk)
  dropSpeX : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (blkPl_553).base
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX E2E.HooksE.A0))
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (blkPl_553).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecStk E2E.HooksE.A0 stk))
  arms : ∀ (S : RunSem) (decPkNeed : Nat),
    RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed S
      (cliRunNeeds_placed decPkNeed) cliResStack

/-- Discharges all non-arm fields of `CliPubCalleesPlaced` from `CliA0RunHooks`, leaving only `arms`. -/
theorem cliPubCallees_of_arms_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hRunA0 : CliA0RunHooks mmpl gh W)
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed S
        (cliRunNeeds_placed decPkNeed) cliResStack) :
    CliPubCalleesPlaced mmpl gh W := by
  let hh := hRunA0.runHooks
  exact
    { a0Run := hRunA0
      dirGet := fun {_stk} hstk =>
        Get.dirGet_placed_caller_ok_of_deps
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          (pathProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jPath := 589)
          (readProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 579)
          (fun _ hp => hp.2) hh.alloc hh.panics hh.memcpyRO hh.bcmp
          (by decide) (by decide)
          (RunSkeleton.path_placed_ok
            (callerProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
            hh (Nat.le_refl RunSkeleton.pathNeed) (by decide))
          (by decide) (by decide)
          (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hRunA0.readFile579)
          (hh.fs (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 589) hstk (by decide)
      bundleRead := fun {stk} hstk => by
        have hraw := BundleRead.bundleRead_placed_caller_ok_of_deps
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          (pathProg := lsProg_563 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jPath := 563)
          (readProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 579)
          (fun _ hp => hp.2) hh.panics hh.alloc
          (by decide) (by decide)
          (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
            (RunSkeleton.path_placed_ok
              (callerProg := lsProg_563 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 563)
              hh (Nat.le_refl RunSkeleton.pathNeed) (by decide)))
          (by decide) (by decide)
          (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hRunA0.readFile579)
          (hh.fs (lsProg_563 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 563) hstk (by decide)
        refine subroutine_ok_mono hraw (fun x R s0 hpre => ?_) (fun _ _ _ _ hq => hq)
          (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
        have hpre' := hpre
        unfold bundleReadSpecPlaced at hpre'
        obtain ⟨hcrl, _⟩ := StoreKit.extract_withLsCodeRoLoaded hpre'
        dsimp only [StoreKit.withLsCodeRoLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨hcrl, hpre⟩
      splitId := fun {_stk} hstk =>
        SplitId.splitId_placed_caller_ok_of_deps
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          hh.alloc hh.panics
          (DropSpeProof.cliDropSpe_placed_caller_ok_x
            (callerProg := lsProg_593 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 593)
            hh.alloc (by decide))
          hstk (by decide)
      splitSigned := fun {_stk} hstk =>
        SplitSigned.splitSigned_placed_caller_ok_of_deps
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          hh.alloc hh.panics
          (SplitId.splitId_placed_caller_ok_of_deps
            (callerProg := lsProg_592 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 592)
            hh.alloc hh.panics
            (DropSpeProof.cliDropSpe_placed_caller_ok_x
              (callerProg := lsProg_593 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 593)
              hh.alloc (by decide))
            (Nat.le_refl splitIdNeed) (by decide))
          (DropSpeProof.cliDropSpe_placed_caller_ok_x
            (callerProg := lsProg_592 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 592)
            hh.alloc (by decide))
          hstk (by decide)
      dropSpeX := DropSpeProof.cliDropSpe_placed_caller_ok_x
        (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
        hh.alloc (by decide)
      dropSpe := fun stk hstk hstk64 =>
        DropSpeProof.cliDropSpe_placed_caller_ok_stk
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          hh.alloc stk hstk hstk64 (by decide)
      arms := harms }

/-- Frozen public-API and directory callee obligations on Block `579`, paired with `CliA0RunHooks` and `RunArmsFrozenPlaced`. -/
structure CliPubCalleesFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) : Prop where
  a0Run : CliA0RunHooks mmpl gh W
  dirGet : ∀ {stk : Nat}, cliRunBudgets_placed.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)
  bundleRead : ∀ {stk : Nat}, cliRunBudgets_placed.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 563)
      (bundleReadSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 593)
      (splitIdSpecPlaced E2E.HooksE.A0 stk)
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 592)
      (splitSignedSpecPlaced E2E.HooksE.A0 stk)
  dropSpeX : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (blkPl_553).base
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecX E2E.HooksE.A0))
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (blkPl_553).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dropSpeSpecStk E2E.HooksE.A0 stk))
  arms : ∀ (S : RunSem) (decPkNeed : Nat),
    RunArmsFrozenPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
      cliRunBudgets_placed S (cliRunNeeds_placed decPkNeed) cliResStack

/-- Discharges all non-arm fields of `CliPubCalleesFrozenPlaced` from `CliA0RunHooks`, leaving only `arms`. -/
theorem cliPubCallees_frozen_of_arms_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hRunA0 : CliA0RunHooks mmpl gh W)
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      RunArmsFrozenPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
        cliRunBudgets_placed S (cliRunNeeds_placed decPkNeed) cliResStack) :
    CliPubCalleesFrozenPlaced mmpl gh W := by
  let hh := hRunA0.runHooks
  exact
    { a0Run := hRunA0
      dirGet := fun {_stk} hstk =>
        Get.dirGet_placed_caller_ok_of_deps
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          (pathProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jPath := 589)
          (readProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 579)
          (fun _ hp => hp.2) hh.alloc hh.panics hh.memcpyRO hh.bcmp
          (by decide) (by decide)
          (RunSkeleton.path_placed_ok
            (callerProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 589)
            hh (Nat.le_refl RunSkeleton.pathNeed) (by decide))
          (by decide) (by decide)
          (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hRunA0.readFile579)
          (hh.fs (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 589) hstk (by decide)
      bundleRead := fun {stk} hstk => by
        have hraw := BundleRead.bundleRead_placed_caller_ok_of_deps
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          (pathProg := lsProg_563 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jPath := 563)
          (readProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 579)
          (fun _ hp => hp.2) hh.panics hh.alloc
          (by decide) (by decide)
          (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
            (RunSkeleton.path_placed_ok
              (callerProg := lsProg_563 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 563)
              hh (Nat.le_refl RunSkeleton.pathNeed) (by decide)))
          (by decide) (by decide)
          (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hRunA0.readFile579)
          (hh.fs (lsProg_563 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 563) hstk (by decide)
        refine subroutine_ok_mono hraw (fun x R s0 hpre => ?_) (fun _ _ _ _ hq => hq)
          (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
        have hpre' := hpre
        unfold bundleReadSpecPlaced at hpre'
        obtain ⟨hcrl, _⟩ := StoreKit.extract_withLsCodeRoLoaded hpre'
        dsimp only [StoreKit.withLsCodeRoLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨hcrl, hpre⟩
      splitId := fun {_stk} hstk =>
        SplitId.splitId_placed_caller_ok_of_deps
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          hh.alloc hh.panics
          (DropSpeProof.cliDropSpe_placed_caller_ok_x
            (callerProg := lsProg_593 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 593)
            hh.alloc (by decide))
          hstk (by decide)
      splitSigned := fun {_stk} hstk =>
        SplitSigned.splitSigned_placed_caller_ok_of_deps
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          hh.alloc hh.panics
          (SplitId.splitId_placed_caller_ok_of_deps
            (callerProg := lsProg_592 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 592)
            hh.alloc hh.panics
            (DropSpeProof.cliDropSpe_placed_caller_ok_x
              (callerProg := lsProg_593 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 593)
              hh.alloc (by decide))
            (Nat.le_refl splitIdNeed) (by decide))
          (DropSpeProof.cliDropSpe_placed_caller_ok_x
            (callerProg := lsProg_592 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 592)
            hh.alloc (by decide))
          hstk (by decide)
      dropSpeX := DropSpeProof.cliDropSpe_placed_caller_ok_x
        (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
        hh.alloc (by decide)
      dropSpe := fun stk hstk hstk64 =>
        DropSpeProof.cliDropSpe_placed_caller_ok_stk
          (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
          hh.alloc stk hstk hstk64 (by decide)
      arms := harms }

/-- Inner encrypt, decrypt, and initiate slot-callee obligations under `[LibsignalPlacement]`. -/
structure CliSlotCalleesPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop where
  w1Inner : EncryptLemmas.W1InnerPlacedOk mmpl gh W cliRunBudgets_placed Slots.scopeIn
  w2SessVt : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyVtablesPlacedOk (DecryptLemmas.decSessKitPlaced F0 peer cliRunBudgets_placed)
  w2IdVt : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityVtablesPlacedOk (DecryptLemmas.decIdKitPlaced F0 peer cliRunBudgets_placed)
  w2Inner : DecryptLemmas.InnerDecryptPlacedOk mmpl gh W cliRunBudgets_placed
  w3Hooks : Initiate.RunHooksPlaced W E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
  w3Exist : Initiate.ExistingStoreCalleesPlaced E2E.HooksE.A0
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed
  w3A4 : Initiate.SubsetA4InitCalleesPlaced E2E.HooksE.A0 mmpl gh W
  w3Stage2 : ∀ S : RunSem, S.initiate = initDef X ⟨W.C, W.Q⟩ →
    Initiate.Stage2PlacedOk E2E.HooksE.A0 mmpl gh W X cliRunBudgets_placed S
  w3Stage3 : ∀ S : RunSem, S.initiate = initDef X ⟨W.C, W.Q⟩ →
    Initiate.Stage3PlacedOk E2E.HooksE.A0 mmpl gh W X cliRunBudgets_placed S

/-- Inner encrypt, frozen-decrypt, and initiate slot-callee obligations under `[LibsignalFullPlacement]`. -/
structure CliSlotCalleesFullPlaced [LibsignalFullPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop where
  w1Inner : EncryptLemmas.W1InnerPlacedOk mmpl gh W cliRunBudgets_placed Slots.scopeIn
  w2SessVt : ∀ (F0 : FsFiles) (peer : AddrGhost),
    SessionOnlyVtablesPlacedOk (DecryptLemmas.decSessKitPlaced F0 peer cliRunBudgets_placed)
  w2IdVt : ∀ (F0 : FsFiles) (peer : AddrGhost),
    IdentityVtablesPlacedOk (DecryptLemmas.decIdKitPlaced F0 peer cliRunBudgets_placed)
  w2Inner : DecryptLemmas.InnerDecryptFrozenPlacedOk mmpl gh W cliRunBudgets_placed
  w3Hooks : Initiate.RunHooksPlaced W E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
  w3Exist : Initiate.ExistingStoreCalleesPlaced E2E.HooksE.A0
    (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed
  w3A4 : Initiate.SubsetA4InitCalleesPlaced E2E.HooksE.A0 mmpl gh W
  w3Stage2 : ∀ S : RunSem, S.initiate = initDef X ⟨W.C, W.Q⟩ →
    Initiate.Stage2PlacedOk E2E.HooksE.A0 mmpl gh W X cliRunBudgets_placed S
  w3Stage3 : ∀ S : RunSem, S.initiate = initDef X ⟨W.C, W.Q⟩ →
    Initiate.Stage3PlacedOk E2E.HooksE.A0 mmpl gh W X cliRunBudgets_placed S

/-- PQXDH pre-key slot and model-agreement bundle under `[LibsignalPlacement]`. -/
structure CliPqPrekeyBundlePlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Type where
  decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
    SlotAns (List (BitVec 8))
  decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop
  pksmParse : List (BitVec 8) → Option PreKeySignalMessage
  decPkNeed : Nat
  needLe : decPkNeed ≤ 4194304
  pksmSlot : ∀ S : RunSem, S.pksmParse = pksmParse →
    subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced E2E.HooksE.A0 S)
  decPkSlot : ∀ (S : RunSem) (needs : RunNeeds),
    S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) →
    S.decryptPrekey = decPk →
    S.decPkOk = decPkOk →
    needs.decryptPrekey = decPkNeed →
    (slotsOfPlaced E2E.HooksE.A0 S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)
  pksmAgrees : ∀ S : RunSem, S.pksmParse = pksmParse → PksmParseAgrees S
  decPkAgrees : ∀ S : RunSem, S.decryptPrekey = decPk → S.pksmParse = pksmParse →
    PqDecryptPrekeyAgrees S X ⟨W.C, W.Q⟩
  decPkDomOk : ∀ (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
      (pm : PreKeySignalMessage),
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    pksmParse m.bytes = some pm →
    decPkOk (runFiles (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc))
      (addrValE st.party.other) (addrValE st.party) pm
  decPkCommitOk : ∀ (S : RunSem) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256),
    S.decryptPrekey = decPk → S.pksmParse = pksmParse →
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
      (MainResult.ofAnswer (runAns S (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)))

/-- Discharges the `kem::Key<Public>::deserialize` (Block `590`) slot obligation on Block `579` from `RunHooksPlaced`. -/
theorem hc_kemDeserialize_of_hooks_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {S : RunSem} {needs : RunNeeds}
    (hh : RunHooksPlaced A H) :
    (slotsOfPlaced A S needs).kemDeserialize.OkPlaced (lsProg_579 H) (blkPl_590).base :=
  fun stk hstk hstk63 =>
    cliKemDeserialize_placed_at_block (callerProg := lsProg_579 H) (i := 579)
      hh.alloc hh.memcpyRO (hh.panics lsHandleAllocErrorSymCli (by decide))
      stk hstk (Nat.le_trans hstk63 (by decide))

theorem runCallees_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hpub : CliPubCalleesPlaced mmpl gh W)
    (hslots : CliSlotCalleesPlaced mmpl gh X W)
    (hdecPkSlot : (slotsOfPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse)
      (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    RunCalleesPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
      cliRunBudgets_placed
      (slotsOfPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse)
        (cliRunNeeds_placed decPkNeed)) := by
  let S := cliRunSem_placed X W decPk decPkOk pksmParse
  let hh := hpub.a0Run.runHooks
  exact
    { readFile := hpub.a0Run.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt := cliEncrypt_slotOk_placed mmpl gh W cliRunBudgets_placed S Slots.scopeIn
        (cliRunNeeds_placed decPkNeed) hh hslots.w1Inner Slots.encodeInjOn_deserializeScopeP_Q
        (fun _ h => h) rfl (fun _ _ _ _ hf he => ⟨hf.1, he⟩) rfl
      decryptSignal := cliDecryptSignal_slotOk_placed mmpl gh W cliRunBudgets_placed S Slots.scopeIn
        (cliRunNeeds_placed decPkNeed) hh hslots.w2SessVt hslots.w2IdVt hslots.w2Inner
        Slots.encodeInjOn_deserializeScopeP_Q (fun _ h => h)
        rfl (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩) rfl
      initiate := cliInitiate_slotOk_placed mmpl gh W X cliRunBudgets_placed S
        (cliRunNeeds_placed decPkNeed) hslots.w3Hooks hslots.w3Exist hslots.w3A4
        (hslots.w3Stage2 S rfl) (hslots.w3Stage3 S rfl) rfl (fun _ _ _ _ hi => hi) rfl
      decryptPrekey := hdecPkSlot
      kemDeserialize := hc_kemDeserialize_of_hooks_placed hh }

/-- Tightened `run` subroutine contract on Block `617` (`mProgPlaced`) at `cliRunSem_placed`. -/
theorem hrun_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hpub : CliPubCalleesPlaced mmpl gh W)
    (hslots : CliSlotCalleesPlaced mmpl gh X W)
    (hdecPkSlot : (slotsOfPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse)
      (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hpksmSlot : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W decPk decPkOk pksmParse)) cliWrOk cliResStack) :=
  RunCompose.run_ok_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    (hpub.arms (cliRunSem_placed X W decPk decPkOk pksmParse) decPkNeed)
    hpub.a0Run.runHooks
    (runCallees_cli_placed mmpl gh X W decPk decPkOk pksmParse decPkNeed hpub hslots hdecPkSlot)
    hpksmSlot (runNeed_cli_le_resStack_placed hdecNeed) cliResStack_le_63_placed

theorem runCallees_cli_full_placed [LibsignalFullPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hpub : CliPubCalleesFrozenPlaced mmpl gh W)
    (hslots : CliSlotCalleesFullPlaced mmpl gh X W)
    (hdecPkSlot : (slotsOfSigPkFrozenPlaced E2E.HooksE.A0
      (cliRunSem_placed X W decPk decPkOk pksmParse)
      (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    RunCalleesPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))
      cliRunBudgets_placed
      (slotsOfSigPkFrozenPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse)
        (cliRunNeeds_placed decPkNeed)) := by
  let S := cliRunSem_placed X W decPk decPkOk pksmParse
  let hh := hpub.a0Run.runHooks
  exact
    { readFile := hpub.a0Run.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt := cliEncrypt_slotOk_placed mmpl gh W cliRunBudgets_placed S Slots.scopeIn
        (cliRunNeeds_placed decPkNeed) hh hslots.w1Inner Slots.encodeInjOn_deserializeScopeP_Q
        (fun _ h => h) rfl (fun _ _ _ _ hf he => ⟨hf.1, he⟩) rfl
      decryptSignal := cliDecryptSignal_slotOk_full_placed mmpl gh W cliRunBudgets_placed S
        Slots.scopeIn (cliRunNeeds_placed decPkNeed) hh hslots.w2SessVt hslots.w2IdVt
        hslots.w2Inner Slots.encodeInjOn_deserializeScopeP_Q (fun _ h => h)
        rfl (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩) rfl
      initiate := cliInitiate_slotOk_placed mmpl gh W X cliRunBudgets_placed S
        (cliRunNeeds_placed decPkNeed) hslots.w3Hooks hslots.w3Exist hslots.w3A4
        (hslots.w3Stage2 S rfl) (hslots.w3Stage3 S rfl) rfl (fun _ _ _ _ hi => hi) rfl
      decryptPrekey := hdecPkSlot
      kemDeserialize := hc_kemDeserialize_of_hooks_placed (S := S)
        (needs := cliRunNeeds_placed decPkNeed) hh }

/-- Tightened `LibsignalFrozen`-wrapped `run` subroutine contract on Block `617` under `[LibsignalFullPlacement]`. -/
theorem hrun_cli_full_placed [LibsignalFullPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hpub : CliPubCalleesFrozenPlaced mmpl gh W)
    (hslots : CliSlotCalleesFullPlaced mmpl gh X W)
    (hdecPkSlot : (slotsOfSigPkFrozenPlaced E2E.HooksE.A0
      (cliRunSem_placed X W decPk decPkOk pksmParse)
      (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hpksmSlot : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W decPk decPkOk pksmParse)) cliWrOk cliResStack) :=
  RunCompose.run_ok_frozen_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    (hpub.arms (cliRunSem_placed X W decPk decPkOk pksmParse) decPkNeed)
    hpub.a0Run.runHooks
    (runCallees_cli_full_placed mmpl gh X W decPk decPkOk pksmParse decPkNeed hpub hslots
      hdecPkSlot)
    hpksmSlot
    (runNeed_cli_le_resStack_placed (S := cliRunSem_placed X W decPk decPkOk pksmParse) hdecNeed)
    cliResStack_le_63_placed (by decide)

theorem hrun_cli_plain_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hpub : CliPubCalleesPlaced mmpl gh W)
    (hslots : CliSlotCalleesPlaced mmpl gh X W)
    (hdecPkSlot : (slotsOfPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse)
      (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hpksmSlot : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W decPk decPkOk pksmParse)) cliWrOk cliResStack) :=
  subroutine_ok_runSpecPlaced_of_tight
    (hrun_cli_placed mmpl gh X W decPk decPkOk pksmParse decPkNeed hdecNeed hpub hslots hdecPkSlot
      hpksmSlot)

theorem main_ok_cli_placed_of_runTight [LibsignalPlacement]
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : CliA0MainHooks mmpl gh W)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (hrun : subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 579)
      (runSpecTightPlaced CodeOk E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W decPk decPkOk pksmParse)) cliWrOk cliResStack)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlaced CodeOk E2E.HooksE.A0 cliMainStk cliStaticsPlaced
        (runRel (cliRunSem_placed X W decPk decPkOk pksmParse))) :=
  main_ok_a1_tight_placed mmpl gh W hMainHooks.allocFs hMainHooks.readStdin hMainHooks.readFile
    hrun (fun _ _ hr => RunCompose.runRel_dom hr)

/-- Tightened `main` subroutine contract on Block `617` instantiated with `hrun_cli_placed`. -/
theorem main_ok_cli_tight_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : CliA0MainHooks mmpl gh W)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hpub : CliPubCalleesPlaced mmpl gh W)
    (hslots : CliSlotCalleesPlaced mmpl gh X W)
    (hdecPkSlot : (slotsOfPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse)
      (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hpksmSlot : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 cliMainStk cliStaticsPlaced
        (runRel (cliRunSem_placed X W decPk decPkOk pksmParse))) :=
  main_ok_cli_placed_of_runTight mmpl gh X W hMainHooks decPk decPkOk pksmParse
    (hrun_cli_placed mmpl gh X W decPk decPkOk pksmParse decPkNeed hdecNeed hpub hslots hdecPkSlot
      hpksmSlot)

/-- `main` subroutine contract on Block `617` under `[LibsignalPlacement]`. -/
theorem main_ok_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : CliA0MainHooks mmpl gh W)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage)
    (decPkNeed : Nat)
    (hdecNeed : decPkNeed ≤ 4194304)
    (hpub : CliPubCalleesPlaced mmpl gh W)
    (hslots : CliSlotCalleesPlaced mmpl gh X W)
    (hdecPkSlot : (slotsOfPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse)
      (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hpksmSlot : subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced E2E.HooksE.A0 (cliRunSem_placed X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 cliMainStk cliStaticsPlaced
        (runRel (cliRunSem_placed X W decPk decPkOk pksmParse))) :=
  subroutine_ok_mainSpecPlaced_of_tight
    (main_ok_cli_tight_placed mmpl gh X W hMainHooks decPk decPkOk pksmParse decPkNeed hdecNeed
      hpub hslots hdecPkSlot hpksmSlot)

end CryptoVerification.SignalSession.Cli.MainHops

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.Run.Placed
open CryptoVerification.SignalSession.Cli.Slots
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open CryptoVerification.LibsignalPublicApi.StoreKit

private theorem varint_length_le_5 {n : Nat} (hn : n < 2 ^ 32) :
    (Prost.varint n).length ≤ 5 := by
  unfold Prost.varint; split
  · simp
  · dsimp only [List.length_cons]; unfold Prost.varint; split
    · simp
    · dsimp only [List.length_cons]; unfold Prost.varint; split
      · simp
      · dsimp only [List.length_cons]; unfold Prost.varint; split
        · simp
        · dsimp only [List.length_cons]; unfold Prost.varint
          have h5 : n / 128 / 128 / 128 / 128 < 128 := by omega
          simp [h5]

private theorem key_length_le_5 {tag wt : Nat} (h : 8 * tag + wt < 2 ^ 32) :
    (Prost.key tag wt).length ≤ 5 :=
  varint_length_le_5 h

private theorem uint32Field_length_le_10 {tag : Nat} (ht : 8 * tag < 2 ^ 32)
    (ov : Option (BitVec 32)) :
    (Prost.uint32Field tag ov).length ≤ 10 := by
  cases ov with
  | none => simp [Prost.uint32Field]
  | some v =>
    simp only [Prost.uint32Field, List.length_append]
    have h1 := key_length_le_5 (wt := 0) (by omega)
    have h2 := varint_length_le_5 v.isLt
    omega

private theorem bytesField_some_length_le {tag : Nat} {bs : List (BitVec 8)}
    (ht : 8 * tag + 2 < 2 ^ 32) (hbs : bs.length < 2 ^ 32) :
    (Prost.bytesField tag (some bs)).length ≤ bs.length + 10 := by
  simp only [Prost.bytesField, List.length_append]
  have h1 := key_length_le_5 ht
  have h2 := varint_length_le_5 hbs
  omega

theorem preKeyMsgE_bytes_lt_2_32_placed {m : PreKeyMessageFields}
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    m.bytes.length < 2 ^ 32 := by
  simp only [PreKeyMessageFields.bytes, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  have h1 := uint32Field_length_le_10 (tag := 1) (by decide) m.opkId
  have h2 := bytesField_some_length_le (tag := 2) (bs := djbKey m.baseKey) (by decide)
    (by simp [djbKey])
  have h3 := bytesField_some_length_le (tag := 3) (bs := djbKey m.idPub) (by decide)
    (by simp [djbKey])
  have h4 := bytesField_some_length_le (tag := 4) (bs := m.inner) (by decide) (by omega)
  have h5 := uint32Field_length_le_10 (tag := 5) (by decide) (some m.regId)
  have h6 := uint32Field_length_le_10 (tag := 6) (by decide) (some m.spkId)
  have h7 := uint32Field_length_le_10 (tag := 7) (by decide) (some m.kpkId)
  have h8 := bytesField_some_length_le (tag := 8) (bs := kyberKey m.kyberCt) (by decide)
    (by simp [kyberKey])
  have hdjb1 : (djbKey m.baseKey).length = 33 := by simp [djbKey]
  have hdjb2 : (djbKey m.idPub).length = 33 := by simp [djbKey]
  have hkyb : (kyberKey m.kyberCt).length = 1569 := by simp [kyberKey]
  omega

/-- Relocatable `main`-level SM-domain functional specification on `mProgPlaced`. -/
def MainOkCliSmPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks, ∃ Run : Inputs → Cli.RunAnswer → Prop,
    subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 617)
      (Cli.mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) E2E.HooksE.A0
        Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
    (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
      ∃ a, Run (smSendInputs g m) a ∧
        observe (smSendInputs g m).files a =
          observe (smSendInputs g m).files (smSendModel W.C g m) ∧
        Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
    (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
      ∃ a, Run (smRecvInputs g c rc) a ∧
        observe (smRecvInputs g c rc).files a =
          observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
        Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))

/-- Tightened `main`-level SM-domain functional specification on `mProgPlaced`. -/
def MainOkCliSmTightPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks, ∃ Run : Inputs → Cli.RunAnswer → Prop,
    subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 617)
      (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
    (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
      ∃ a, Run (smSendInputs g m) a ∧
        observe (smSendInputs g m).files a =
          observe (smSendInputs g m).files (smSendModel W.C g m) ∧
        Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
    (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
      ∃ a, Run (smRecvInputs g c rc) a ∧
        observe (smRecvInputs g c rc).files a =
          observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
        Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))

theorem MainOkCliSmTightPlaced.toMainOkCliSmPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkCliSmTightPlaced mmpl gh) : MainOkCliSmPlaced mmpl gh := by
  intro hDropNz W
  obtain ⟨Run, hmain, hsend, hrecv⟩ := h hDropNz W
  exact ⟨Run, Cli.subroutine_ok_mainSpecPlaced_of_tight hmain, hsend, hrecv⟩

/-- Relocatable `main`-level 5-clause PQXDH functional specification on `mProgPlaced`. -/
def MainOkCliPqPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
          ∃ a, Run (pqInitInputs WP st b t) a ∧
            observe (pqInitInputs WP st b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
            Cli.CommitOk (pqInitInputs WP st b t) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP st m r) a ∧
            observe (pqSendInputs WP st m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
            Cli.CommitOk (pqSendInputs WP st m r) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP st c rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP st c rc) a ∧
            observe (pqRecvInputs WP st c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a))

/-- Tightened `main`-level 5-clause PQXDH functional specification on `mProgPlaced`. -/
def MainOkCliPqTightPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) : Prop :=
  lsmpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
          ∃ a, Run (pqInitInputs WP st b t) a ∧
            observe (pqInitInputs WP st b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
            Cli.CommitOk (pqInitInputs WP st b t) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP st m r) a ∧
            observe (pqSendInputs WP st m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
            Cli.CommitOk (pqSendInputs WP st m r) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP st c rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP st c rc) a ∧
            observe (pqRecvInputs WP st c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a))

theorem MainOkCliPqTightPlaced.toMainOkCliPqPlaced [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    (h : MainOkCliPqTightPlaced mmpl gh) : MainOkCliPqPlaced mmpl gh := by
  intro hDropNz X W
  obtain ⟨Run, hmain, hclauses⟩ := h hDropNz X W
  exact ⟨Run, Cli.subroutine_ok_mainSpecPlaced_of_tight hmain, hclauses⟩

/-- Tightened SM-domain `main` specification from a family of `runSpecTightPlaced` witnesses, establishing `send`/`recv` model agreement. -/
theorem main_ok_cli_sm_placed_of_runTight [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hMainHooks : Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpksm : Cli.MainHops.CliPksmSlotExistsPlaced mmpl gh W)
    (hdecPk : Cli.MainHops.CliDecPkSlotExistsPlaced mmpl gh W)
    (hrun : ∀ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
        List (BitVec 8) → SlotAns (List (BitVec 8)))
      (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
      (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      decPkNeed ≤ 4194304 →
      (slotsOfPlaced E2E.HooksE.A0
        (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)
        (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (CryptoVerification.blkPl_111).base
        (pksmSlotSpecPlaced E2E.HooksE.A0
          (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)) →
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 579)
        (Cli.MainHops.runSpecTightPlaced
          (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) E2E.HooksE.A0 uuidTryParse
          (runRel (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack)) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) := by
  obtain ⟨pksmParse, hpksmSlot⟩ := hpksm
  obtain ⟨decPk, decPkOk, decPkNeed, hdecNeed, hdecPkSlot⟩ := hdecPk
  let S : RunSem := cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse
  have hmain : subroutine_ok
      (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced (runRel S)) :=
    main_ok_cli_placed_of_runTight mmpl gh defaultModelExtras_placed W hMainHooks
      decPk decPkOk pksmParse
      (hrun decPk decPkOk pksmParse decPkNeed hdecNeed
        (hdecPkSlot S (cliRunNeeds_placed decPkNeed) rfl rfl rfl rfl)
        (hpksmSlot S rfl))
  have hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ Slots.scopeIn := rfl
  have hS_dec : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Slots.scopeIn := rfl
  have hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) := rfl
  have hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn := rfl
  clear_value S
  have hcovSm := ratchetScopeCoversSm_scopeIn_placed W.C
  have hagEnc : SmEncryptAgrees S W.C :=
    smEncryptAgrees_encDef_placed S ⟨W.C, W.Q⟩ Slots.scopeIn hS_enc encodeInjOn_scopeIn_placed
      hcovSm
  have hagDec : SmDecryptSignalAgrees S W.C :=
    smDecryptSignalAgrees_decSigDef_placed S ⟨W.C, W.Q⟩ Slots.scopeIn hS_dec
      encodeInjOn_scopeIn_placed hcovSm
  refine ⟨runRel S, hmain, fun g m hg hm => ?_, fun g c rc hg hc => ?_⟩
  · exact ⟨runAns S (smSendInputs g m),
      ⟨domainArgv_smSend g m, runBounds_smSend g m hm,
        runFilesOk_smSend_cli_placed (S := S) hS_files g m hg,
        runEncOk_smSend_cli_placed (S := S) hS_encOk g m hg,
        runHsOk_smSend_cli_placed S g m, rfl⟩,
      RunRefine.runAns_smSend S W.C hagEnc g m hg hm,
      commitOk_smSend_encDef_placed (S := S) (W := ⟨W.C, W.Q⟩) hS_enc g m⟩
  · exact ⟨runAns S (smRecvInputs g c rc),
      ⟨domainArgv_smRecv g c rc, runBounds_smRecv g c rc hc,
        runFilesOk_smRecv_cli_placed (S := S) hS_files g c rc hg,
        Slots.runEncOk_smRecv S g c rc,
        runHsOk_smRecv_cli_placed S g c rc, rfl⟩,
      RunRefine.runAns_smRecv S W.C hagDec g c rc hg hc,
      commitOk_smRecv_decSigDef_placed (S := S) (W := ⟨W.C, W.Q⟩) hS_dec g c rc⟩

/-- Tightened SM-domain `main` specification instantiated with `hrun_cli_placed`. -/
theorem main_ok_cli_sm_tight_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hMainHooks : Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpub : Cli.MainHops.CliPubCalleesPlaced mmpl gh W)
    (hslots : Cli.MainHops.CliSlotCalleesPlaced mmpl gh defaultModelExtras_placed W)
    (hpksm : Cli.MainHops.CliPksmSlotExistsPlaced mmpl gh W)
    (hdecPk : Cli.MainHops.CliDecPkSlotExistsPlaced mmpl gh W) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) :=
  main_ok_cli_sm_placed_of_runTight mmpl gh W hMainHooks hpksm hdecPk
    fun decPk decPkOk pksmParse decPkNeed hneed hdec hpk =>
      hrun_cli_placed mmpl gh defaultModelExtras_placed W decPk decPkOk pksmParse decPkNeed hneed
        hpub hslots hdec hpk

/-- Tightened SM-domain `main` specification with `LibsignalFrozen lsmpl` from a family of `runSpecTightPlaced` witnesses. -/
theorem main_ok_cli_sm_placed_of_runTight_frozen [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hMainHooks : Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpksm : Cli.MainHops.CliPksmSlotExistsPlaced mmpl gh W)
    (hdecPk : Cli.MainHops.CliDecPkSlotExistsFrozenPlaced mmpl gh W)
    (hrun : ∀ (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage →
        List (BitVec 8) → SlotAns (List (BitVec 8)))
      (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
      (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) (decPkNeed : Nat),
      decPkNeed ≤ 4194304 →
      (slotsOfSigPkFrozenPlaced E2E.HooksE.A0
        (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)
        (cliRunNeeds_placed decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (CryptoVerification.blkPl_111).base
        (pksmSlotSpecPlaced E2E.HooksE.A0
          (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse)) →
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 579)
        (Cli.MainHops.runSpecTightPlaced
          (LibsignalFrozen lsmpl) E2E.HooksE.A0 uuidTryParse
          (runRel (cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse))
          Cli.MainHops.cliWrOk Cli.MainHops.cliResStack)) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalFrozen lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) := by
  obtain ⟨pksmParse, hpksmSlot⟩ := hpksm
  obtain ⟨decPk, decPkOk, decPkNeed, hdecNeed, hdecPkSlot⟩ := hdecPk
  let S : RunSem := cliRunSem_placed defaultModelExtras_placed W decPk decPkOk pksmParse
  have hmain : subroutine_ok
      (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (Cli.mainSpecTightPlaced (LibsignalFrozen lsmpl)
        E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced (runRel S)) :=
    main_ok_cli_placed_of_runTight mmpl gh defaultModelExtras_placed W hMainHooks
      decPk decPkOk pksmParse
      (hrun decPk decPkOk pksmParse decPkNeed hdecNeed
        (hdecPkSlot S (cliRunNeeds_placed decPkNeed) rfl rfl rfl rfl)
        (hpksmSlot S rfl))
  have hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ Slots.scopeIn := rfl
  have hS_dec : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ Slots.scopeIn := rfl
  have hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) := rfl
  have hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn := rfl
  clear_value S
  have hcovSm := ratchetScopeCoversSm_scopeIn_placed W.C
  have hagEnc : SmEncryptAgrees S W.C :=
    smEncryptAgrees_encDef_placed S ⟨W.C, W.Q⟩ Slots.scopeIn hS_enc encodeInjOn_scopeIn_placed
      hcovSm
  have hagDec : SmDecryptSignalAgrees S W.C :=
    smDecryptSignalAgrees_decSigDef_placed S ⟨W.C, W.Q⟩ Slots.scopeIn hS_dec
      encodeInjOn_scopeIn_placed hcovSm
  refine ⟨runRel S, hmain, fun g m hg hm => ?_, fun g c rc hg hc => ?_⟩
  · exact ⟨runAns S (smSendInputs g m),
      ⟨domainArgv_smSend g m, runBounds_smSend g m hm,
        runFilesOk_smSend_cli_placed (S := S) hS_files g m hg,
        runEncOk_smSend_cli_placed (S := S) hS_encOk g m hg,
        runHsOk_smSend_cli_placed S g m, rfl⟩,
      RunRefine.runAns_smSend S W.C hagEnc g m hg hm,
      commitOk_smSend_encDef_placed (S := S) (W := ⟨W.C, W.Q⟩) hS_enc g m⟩
  · exact ⟨runAns S (smRecvInputs g c rc),
      ⟨domainArgv_smRecv g c rc, runBounds_smRecv g c rc hc,
        runFilesOk_smRecv_cli_placed (S := S) hS_files g c rc hg,
        Slots.runEncOk_smRecv S g c rc,
        runHsOk_smRecv_cli_placed S g c rc, rfl⟩,
      RunRefine.runAns_smRecv S W.C hagDec g c rc hg hc,
      commitOk_smRecv_decSigDef_placed (S := S) (W := ⟨W.C, W.Q⟩) hS_dec g c rc⟩

/-- Tightened SM-domain `main` specification under `[LibsignalFullPlacement]`. -/
theorem main_ok_cli_sm_tight_full_placed [LibsignalFullPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hMainHooks : Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpub : Cli.MainHops.CliPubCalleesFrozenPlaced mmpl gh W)
    (hslots : Cli.MainHops.CliSlotCalleesFullPlaced mmpl gh defaultModelExtras_placed W)
    (hpksm : Cli.MainHops.CliPksmSlotExistsPlaced mmpl gh W)
    (hdecPk : Cli.MainHops.CliDecPkSlotExistsFrozenPlaced mmpl gh W) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalFrozen lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) :=
  main_ok_cli_sm_placed_of_runTight_frozen mmpl gh W hMainHooks hpksm hdecPk
    fun decPk decPkOk pksmParse decPkNeed hneed hdec hpk =>
      hrun_cli_full_placed mmpl gh defaultModelExtras_placed W decPk decPkOk pksmParse decPkNeed
        hneed hpub hslots hdec hpk

/-- Relocatable SM-domain `main` specification satisfying `MainOkCliSmPlaced mmpl gh`. -/
theorem main_ok_cli_sm_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hMainHooks : Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpub : Cli.MainHops.CliPubCalleesPlaced mmpl gh W)
    (hslots : Cli.MainHops.CliSlotCalleesPlaced mmpl gh defaultModelExtras_placed W)
    (hpksm : Cli.MainHops.CliPksmSlotExistsPlaced mmpl gh W)
    (hdecPk : Cli.MainHops.CliDecPkSlotExistsPlaced mmpl gh W) :
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
        ∃ a, Run (smSendInputs g m) a ∧
          observe (smSendInputs g m).files a =
            observe (smSendInputs g m).files (smSendModel W.C g m) ∧
          Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
      (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
        ∃ a, Run (smRecvInputs g c rc) a ∧
          observe (smRecvInputs g c rc).files a =
            observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
          Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a)) := by
  obtain ⟨Run, hmain, hsend, hrecv⟩ :=
    main_ok_cli_sm_tight_placed mmpl gh W hMainHooks hpub hslots hpksm hdecPk
  exact ⟨Run, Cli.subroutine_ok_mainSpecPlaced_of_tight hmain, hsend, hrecv⟩

/-- Tightened PQXDH-domain `main` specification from a `runSpecTightPlaced` witness, proving all five `CliSpecPqxdh` clauses and `CommitOk`. -/
theorem main_ok_cli_pq_placed_of_runTight [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpre : Cli.MainHops.CliPqPrekeyBundlePlaced mmpl gh X W)
    (hrun : subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 579)
      (Cli.MainHops.runSpecTightPlaced
        (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) E2E.HooksE.A0 uuidTryParse
        (runRel (cliRunSem_placed X W hpre.decPk hpre.decPkOk hpre.pksmParse))
        Cli.MainHops.cliWrOk Cli.MainHops.cliResStack)) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
          ∃ a, Run (pqInitInputs WP st b t) a ∧
            observe (pqInitInputs WP st b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
            Cli.CommitOk (pqInitInputs WP st b t) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP st m r) a ∧
            observe (pqSendInputs WP st m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
            Cli.CommitOk (pqSendInputs WP st m r) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP st c rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP st c rc) a ∧
            observe (pqRecvInputs WP st c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let S : RunSem := cliRunSem_placed X W hpre.decPk hpre.decPkOk hpre.pksmParse
  have hmain : subroutine_ok
      (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced (runRel S)) :=
    main_ok_cli_placed_of_runTight mmpl gh X W hMainHooks hpre.decPk hpre.decPkOk hpre.pksmParse
      hrun
  have hS_enc : S.encrypt = encDef WP Slots.scopeIn := rfl
  have hS_dec : S.decryptSignal = decSigDef WP Slots.scopeIn := rfl
  have hS_init : S.initiate = initDef X WP := rfl
  have hS_decPk : S.decryptPrekey = hpre.decPk := rfl
  have hS_pksm : S.pksmParse = hpre.pksmParse := rfl
  have hS_files : S.filesOk = Slots.filesOk₀ Slots.scopeIn (fun _ => True) := rfl
  have hS_encOk : S.encOk = Slots.encOk₀ Slots.scopeIn := rfl
  have hS_initOk : S.initOk = InitOk₀ WP := rfl
  have hS_decPkOk : S.decPkOk = hpre.decPkOk := rfl
  clear_value S
  have hcovPq := ratchetScopeCoversPq_scopeIn_placed WP
  have hagInit : PqInitiateAgrees S X WP := InitS0.pqInitiateAgrees_initDef_proof S X WP hS_init
  have hagEnc : PqEncryptAgrees S WP :=
    pqEncryptAgrees_encDef_placed S WP Slots.scopeIn hS_enc encodeInjOn_scopeIn_placed hcovPq
  have hagDec : PqDecryptSignalAgrees S WP :=
    pqDecryptSignalAgrees_decSigDef_placed S WP Slots.scopeIn hS_dec encodeInjOn_scopeIn_placed
      hcovPq
  have hagPksm : PksmParseAgrees S := hpre.pksmAgrees S hS_pksm
  have hagDecPk : PqDecryptPrekeyAgrees S X WP := hpre.decPkAgrees S hS_decPk hS_pksm
  refine ⟨runRel S, hmain, fun st hst => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b t hnone
    exact ⟨runAns S (pqInitInputs WP st b t),
      ⟨domainArgv_pqInit WP st b t, runBounds_pqInit WP st b t,
        runFilesOk_pqInit_cli_placed (S := S) hS_files WP st b t hst,
        Slots.runEncOk_pqInit S WP st b t,
        runHsOk_pqInit_cli_placed (S := S) (W := WP) hS_initOk st b t hst hnone, rfl⟩,
      RunRefine.runAns_pqInit S X WP hagInit st b t hst hnone,
      commitOk_pqInit_initDef_placed (S := S) (X := X) (W := WP) hS_init st b t⟩
  · intro m r hm
    exact ⟨runAns S (pqSendInputs WP st m r),
      ⟨domainArgv_pqSend WP st m r, runBounds_pqSend WP st m r hm,
        runFilesOk_pqSend_cli_placed (S := S) hS_files WP st m r hst,
        Slots.runEncOk_pqSend (S := S) hS_encOk WP st m r,
        runHsOk_pqSend_cli_placed S WP st m r, rfl⟩,
      RunRefine.runAns_pqSend S WP hagEnc st m r hst hm,
      commitOk_pqSend_encDef_placed (S := S) (W := WP) hS_enc st m r⟩
  · intro c rc hc
    have hnot3 : (wireWhisper :: c).head? ≠ some wirePrekey := by simp [wireWhisper, wirePrekey]
    exact ⟨runAns S (pqRecvInputs WP st (wireWhisper :: c) rc),
      ⟨domainArgv_pqRecv WP st (wireWhisper :: c) rc,
        runBounds_pqRecv WP st (wireWhisper :: c) rc (Nat.succ_le_of_lt hc),
        runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st (wireWhisper :: c) rc hst,
        Slots.runEncOk_pqRecv S WP st (wireWhisper :: c) rc,
        runHsOk_pqRecvOther_cli_placed S WP st (wireWhisper :: c) rc hnot3, rfl⟩,
      RunRefine.runAns_pqRecvWhisper S WP hagDec st c rc hst hc,
      commitOk_pqRecvWhisper_decSigDef_placed (S := S) (W := WP) hS_dec st c rc⟩
  · intro m rc hm hmatch
    have hm32 : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
      Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32_placed hm)
    exact ⟨runAns S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc),
      ⟨domainArgv_pqRecv WP st (wirePrekey :: m.bytes) rc,
        runBounds_pqRecv WP st (wirePrekey :: m.bytes) rc hm32,
        runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st (wirePrekey :: m.bytes) rc hst,
        Slots.runEncOk_pqRecv S WP st (wirePrekey :: m.bytes) rc,
        runHsOk_pqRecvPrekey_of_decPkOk_placed (S := S) WP st m rc
          (fun pm hpm => hS_decPkOk ▸ hpre.decPkDomOk st m rc pm hst hm hmatch (hS_pksm ▸ hpm)),
        rfl⟩,
      RunRefine.runAns_pqRecvPrekey S X WP hagPksm hagDecPk st m rc hst hm hmatch,
      hpre.decPkCommitOk S st m rc hS_decPk hS_pksm hst hm hmatch⟩
  · intro c rc hc h2 h3
    refine ⟨runAns S (pqRecvInputs WP st c rc),
      ⟨domainArgv_pqRecv WP st c rc,
        runBounds_pqRecv WP st c rc (Nat.le_of_lt hc),
        runFilesOk_pqRecv_cli_placed (S := S) hS_files WP st c rc hst,
        Slots.runEncOk_pqRecv S WP st c rc,
        runHsOk_pqRecvOther_cli_placed S WP st c rc h3, rfl⟩,
      ?_, commitOk_pqRecvBad_placed S WP st c rc h2 h3⟩
    rw [runAns_pqRecvBad S WP st c rc h2 h3]
    rfl

/-- Tightened PQXDH-domain `main` specification instantiated with `hrun_cli_placed`. -/
theorem main_ok_cli_pq_tight_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpub : Cli.MainHops.CliPubCalleesPlaced mmpl gh W)
    (hslots : Cli.MainHops.CliSlotCalleesPlaced mmpl gh X W)
    (hpre : Cli.MainHops.CliPqPrekeyBundlePlaced mmpl gh X W) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecTightPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
          ∃ a, Run (pqInitInputs WP st b t) a ∧
            observe (pqInitInputs WP st b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
            Cli.CommitOk (pqInitInputs WP st b t) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP st m r) a ∧
            observe (pqSendInputs WP st m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
            Cli.CommitOk (pqSendInputs WP st m r) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP st c rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP st c rc) a ∧
            observe (pqRecvInputs WP st c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) :=
  main_ok_cli_pq_placed_of_runTight mmpl gh X W hMainHooks hpre
    (hrun_cli_placed mmpl gh X W hpre.decPk hpre.decPkOk hpre.pksmParse hpre.decPkNeed hpre.needLe
      hpub hslots
      (hpre.decPkSlot (cliRunSem_placed X W hpre.decPk hpre.decPkOk hpre.pksmParse)
        (cliRunNeeds_placed hpre.decPkNeed) rfl rfl rfl rfl)
      (hpre.pksmSlot (cliRunSem_placed X W hpre.decPk hpre.decPkOk hpre.pksmParse) rfl))

/-- Relocatable PQXDH-domain `main` specification satisfying `MainOkCliPqPlaced mmpl gh`. -/
theorem main_ok_cli_pq_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hMainHooks : Cli.MainHops.CliA0MainHooks mmpl gh W)
    (hpub : Cli.MainHops.CliPubCalleesPlaced mmpl gh W)
    (hslots : Cli.MainHops.CliSlotCalleesPlaced mmpl gh X W)
    (hpre : Cli.MainHops.CliPqPrekeyBundlePlaced mmpl gh X W) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.MainHops.mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 617)
        (Cli.mainSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          E2E.HooksE.A0 Cli.MainHops.cliMainStk Cli.cliStaticsPlaced Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
          ∃ a, Run (pqInitInputs WP st b t) a ∧
            observe (pqInitInputs WP st b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
            Cli.CommitOk (pqInitInputs WP st b t) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP st m r) a ∧
            observe (pqSendInputs WP st m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
            Cli.CommitOk (pqSendInputs WP st m r) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP st c rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP st c rc) a ∧
            observe (pqRecvInputs WP st c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a)) := by
  obtain ⟨Run, hmain, hclauses⟩ := main_ok_cli_pq_tight_placed mmpl gh X W hMainHooks hpub hslots hpre
  exact ⟨Run, Cli.subroutine_ok_mainSpecPlaced_of_tight hmain, hclauses⟩

end CryptoVerification.SignalSession
