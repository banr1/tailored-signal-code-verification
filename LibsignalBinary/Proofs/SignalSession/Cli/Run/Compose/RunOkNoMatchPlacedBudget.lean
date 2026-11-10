/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Encrypt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj

/-!
# Budget-Threaded Placed D2(c) `signal_session::run` Composition

Composes budget-threaded `signal_session::run` (Block `579`) and its Block-`617` transfer under
`[LibsignalPlacement]` and `[LibsignalFullPlacement]` (`LibsignalFrozen`) for `cliRunSem` and
D2(c) (`decPkDefD2c` / `DecPkOkD2c`) over `CliGhostHooks`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement blkPl_111 lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliResStack cliRunBudgets cliRunNeeds cliWrOk mProgPlaced
)
open CryptoVerification.SignalSession.Cli.Placed (
  blkPl_553 lsProg_563 lsProg_589 lsProg_592 lsProg_593
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost InitGhost PksmGhost RunNeeds RunSem SlotAns addrValOf runRel
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOkD2c InitOk₀ cliDecryptPrekeyNeed decPkDefD2c decSigDef encDef initDef
)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (
  CalleeSlot.OkPlaced pathNeed splitIdNeed splitSignedNeed
)
open CryptoVerification.SignalSession.Cli.Slots (encOk₀ filesOk₀ scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudget (dirGet_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks (
  CliInitSlotOkPlacedAt hRead_of_hookSat_mono_stk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (
  runSpecTightPlaced subroutine_ok_runSpecPlaced_of_tight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget (
  CliSlotCalleesPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams (
  CliSlotEnvs decIdKitBudgetEnv decSessKitBudgetEnv w1IdKitBudgetEnv w1SessKitBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudget (
  bundleRead_placed_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofPlacedBudget (
  cliDropSpe_placed_caller_ok_x
)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitId.PlacedBudget (
  splitId_placed_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.SplitSigned.PlacedBudget (
  splitSigned_placed_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget (
  cliRunArmEnvs cliRunCalleesEnvs runArmsPlaced_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (
  r1cInitGhost
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget (
  r2EncGhost r2PeerGhost0
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget (
  r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget (
  DecPkD2cSlotOkPlaced PksmSlotOkPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (
  RunArmEnvs RunArmsPlaced RunEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget (
  dropSpeSpecStkPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget (
  pksmSlotSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget (
  CliDecryptSignalSlotEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  CliEncryptSlotEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (
  RunCalleesEnvs RunCalleesPlaced RunHooksPlaced dropSpeX_placed_ok dropSpe_placed_ok path_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  bundleReadSpecPlaced dirGetSpecPlaced readFileSpecPlaced runSpecPlaced splitIdSpecPlaced
  splitSignedSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpecX)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget (
  cliRunArmEnvs cliRunCalleesEnvs
)

/-- Self-contained `RunSem` (`S₀`) constructor at `scopeIn` (definitionally equal to
`MainHops.cliRunSem` / `MainHops.cliRunSem_placed`). -/
noncomputable abbrev cliRunSem (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) : RunSem where
  encrypt := encDef ⟨W.C, W.Q⟩ scopeIn
  decryptSignal := decSigDef ⟨W.C, W.Q⟩ scopeIn
  initiate := initDef X ⟨W.C, W.Q⟩
  decryptPrekey := decPk
  pksmParse := pksmParse
  filesOk := filesOk₀ scopeIn (fun _ => True)
  encOk := encOk₀ scopeIn
  initOk := InitOk₀ ⟨W.C, W.Q⟩
  decPkOk := decPkOk

/-- Bundle of `lsProg_579` hook and `lsReadFileSym` callee obligations at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
structure CliRunHooksBundle [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) : Prop where
  runHooks : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))
  readFile579 : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)

/-- Construct `CliRunHooksBundle` from `RunHooksPlaced` and any `HookSat … lsReadFileSym` at
positive stack budget `stk0 ≤ cliRunBudgets.readFile` (e.g. `stk0 = extHookStack` or
`stk0 = cliRunBudgets.readFile`). -/
theorem cliRunHooksBundle_of_hookSat_mono_stk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk0 : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hpos : 0 < stk0) (hle : stk0 ≤ cliRunBudgets.readFile)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hsat : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk0 ReadEnv)) :
    CliRunHooksBundle mmpl g W A lim ReadEnv where
  runHooks := hh
  readFile579 := hRead_of_hookSat_mono_stk hpos hle hsat (by decide) (by decide)

/-- Seam over the `initiate` slot (`lsmpl.base 521`) at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
abbrev CliInitSlotOkPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  CliInitSlotOkPlacedAt (cliGhostExterns g (cliExternsPlaced mmpl W)) A lim InitEnv X W

/-- Budget-threaded public/arm callee seam for `signal_session::run` (Blocks `589`, `563`, `593`,
`592`, `552`, and `RunArmsPlaced`) at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
structure CliPubCalleesPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs) (aEnvs : RunSem → RunArmEnvs)
    (W : CliHooks) : Prop where
  dirGet : ∀ {stk : Nat}, cliRunBudgets.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim cEnvs.dirGet stk)
  bundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
      (bundleReadSpecPlaced cliIo.rd cliWrOk A lim cEnvs.bundleRead stk)
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 593)
      (splitIdSpecPlaced A lim cEnvs.splitId stk)
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 592)
      (splitSignedSpecPlaced A lim cEnvs.splitSigned stk)
  dropSpeX : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (blkPl_553).base (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk)
  arms : ∀ (S : RunSem) (decPkNeed : Nat),
    RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs (aEnvs S)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
      cliResStack

/-- Discharges all non-arm fields of `CliPubCalleesPlaced` at `cliRunCalleesEnvs ReadEnv` from
`CliRunHooksBundle`, leaving only `arms`. -/
theorem cliPubCallees_of_arms_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {aEnvs : RunSem → RunArmEnvs}
    (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl g W A lim ReadEnv)
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim (cliRunCalleesEnvs ReadEnv) sEnvs (aEnvs S)
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack) :
    CliPubCalleesPlaced mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs aEnvs W :=
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  let hh := hHooks.runHooks
  let hRead := hHooks.readFile579
  { dirGet := fun {_stk} hstk =>
      dirGet_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_589 H) (jPath := 589)
        (readProg := lsProg_579 H) (jRead := 579)
        (fun _ hp => hp.2) hh.alloc hh.memcpyRO hh.bcmp
        (by decide) (by decide)
        (path_placed_ok (callerProg := lsProg_589 H) (i := 589)
          hh (Nat.le_refl pathNeed) (by decide))
        (by decide) (by decide)
        (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
        (hh.fs (lsProg_589 H) 589) hstk
        (fun _ _ _ _ h => h) (by decide)
    bundleRead := fun {_stk} hstk =>
      bundleRead_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_563 H) (jPath := 563)
        (readProg := lsProg_579 H) (jRead := 579)
        (fun _ hp => hp.2) hh.alloc
        (by decide) (by decide)
        (path_placed_ok (callerProg := lsProg_563 H) (i := 563)
          hh (Nat.le_refl pathNeed) (by decide))
        (by decide) (by decide)
        (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
        (hh.fs (lsProg_563 H) 563) hstk (by decide)
    splitId := fun {_stk} hstk =>
      splitId_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        hh.alloc
        (cliDropSpe_placed_caller_ok_x
          (callerProg := lsProg_593 H) (i := 593) hh.alloc (by decide))
        hstk (by decide)
    splitSigned := fun {_stk} hstk =>
      splitSigned_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        hh.alloc
        (splitId_placed_caller_ok_of_deps
          (callerProg := lsProg_592 H) (i := 592)
          hh.alloc
          (cliDropSpe_placed_caller_ok_x
            (callerProg := lsProg_593 H) (i := 593) hh.alloc (by decide))
          (Nat.le_refl splitIdNeed) (by decide))
        (cliDropSpe_placed_caller_ok_x
          (callerProg := lsProg_592 H) (i := 592) hh.alloc (by decide))
        hstk (by decide)
    dropSpeX := dropSpeX_placed_ok
      (callerProg := lsProg_579 H) (i := 579) hh (by decide)
    dropSpe := fun stk hstk hstk64 =>
      dropSpe_placed_ok
        (callerProg := lsProg_579 H) (i := 579)
        hh stk hstk hstk64 (by decide)
    arms := harms }

/-- Discharges all 7 fields of `CliPubCalleesPlaced` at `cliRunCalleesEnvs ReadEnv` and
`cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv` from `CliRunHooksBundle` via
`AllPlacedBudget.runArmsPlaced_ok`. -/
theorem cliPubCallees_d2c_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl g W A lim ReadEnv)
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl)
    (henc_addr : ∀ g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) := by
      intros; rfl)
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl)
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    CliPubCalleesPlaced mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv) W :=
  cliPubCallees_of_arms_placed mmpl g W hHooks fun _ _ =>
    runArmsPlaced_ok hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

/-- Builds `SemPlacedBudget.RunSlotEnvs` from `CliSlotEnvs`, `InitEnv`, and `DecPkEnv` via
`CliEncryptSlotEnv` and `CliDecryptSignalSlotEnv`. -/
noncomputable def runSlotEnvsOf [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (slotEnvs : CliSlotEnvs)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs where
  encrypt := CliEncryptSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets slotEnvs.spqrSend
    (w1SessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
    (w1IdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
  decryptSignal := CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets slotEnvs.tryDecrypt
    (decSessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
    (decIdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
  initiate := InitEnv
  decryptPrekey := DecPkEnv

private theorem runProofs_encDef_eq_agree (P : CryptoVerification.E2E.PEParams)
    (Scope : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)) → Prop) :
    CryptoVerification.SignalSession.Cli.RunProofs.encDef P Scope =
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef P Scope := by
  have hFinal : ∀ F calls,
      CryptoVerification.SignalSession.Cli.RunProofs.cliFinal F calls =
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal F calls := by
    intro F calls
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliFinal
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal
    have hStep :
        CryptoVerification.SignalSession.Cli.RunProofs.cliStep F =
          CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers Scope F peer
        (CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer) =
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
          (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer) := by
    intro F peer
    have hKey :
        CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer =
          CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer := by
      unfold CryptoVerification.SignalSession.Cli.RunProofs.encKey
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey
      rcases CryptoVerification.SignalSession.Cli.Slots.loadRec Scope F peer with _ | (_ | r) <;>
        rfl
    rw [hKey]
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers
    rcases CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer with _ | _ <;>
      rfl
  funext F peer me ptext coins
  unfold CryptoVerification.SignalSession.Cli.RunProofs.encDef
    CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef
  rw [hAns F peer]
  generalize CryptoGames.LibsignalSessionApi.messageEncrypt P.C
    CryptoVerification.LibsignalProtoCodec.protoSignalCodec
    (CryptoVerification.E2E.pqxdhSpqrModel P).spqr
    (CryptoVerification.LibsignalPublicApiRepr.serializeAddrVals
      (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse))
    (CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
      (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer))
    ptext peer me CryptoVerification.SignalSession.Cli.RunCompose.unixEpoch coins = rc
  rcases rc with ⟨err | m, calls⟩
  · cases err <;> rfl
  · dsimp only
    rw [hFinal F calls]

theorem runCallees_cli_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {pksmParse : List (BitVec 8) → Option PreKeySignalMessage}
    {decPkNeed : Nat}
    (hHooks : CliRunHooksBundle mmpl g W A lim cEnvs.readFile)
    (hreadEq : slotEnvs.readFile = cEnvs.readFile)
    (hpub : CliPubCalleesPlaced mmpl g A lim cEnvs
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) aEnvs W)
    (hslots : CliSlotCalleesPlaced mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPk : (slotsOfPlaced A lim (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv)
      (cliRunSem X W decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    RunCalleesPlaced A lim cEnvs (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
      (slotsOfPlaced A lim (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv)
        (cliRunSem X W decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)) := by
  let _ := hreadEq
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  let S := cliRunSem X W decPk decPkOk pksmParse
  let sEnvs := runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv
  let needs := cliRunNeeds decPkNeed
  let hh := hHooks.runHooks
  exact
    { readFile := hHooks.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt :=
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget.cliEncrypt_slotOk_placed
          mmpl g W A lim cliRunBudgets S scopeIn sEnvs needs slotEnvs.spqrSend
          (w1SessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
          (w1IdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
          hh hslots.w1Inner
          CryptoVerification.SignalSession.Cli.Slots.encodeInjOn_deserializeScopeP_Q
          (fun _ h => h)
          (runProofs_encDef_eq_agree ⟨W.C, W.Q⟩ scopeIn)
          (fun _ _ _ _ hf he => ⟨hf.1, he⟩)
          rfl rfl
      decryptSignal :=
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget.cliDecryptSignal_slotOk_placed
          mmpl g W A lim cliRunBudgets S scopeIn sEnvs needs slotEnvs.tryDecrypt
          (decSessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
          (decIdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
          hh hslots.w2SessVt hslots.w2IdVt hslots.w2Inner
          CryptoVerification.SignalSession.Cli.Slots.encodeInjOn_deserializeScopeP_Q
          (fun _ h => h)
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget.decSigDef_eq_runProofs
            ⟨W.C, W.Q⟩ scopeIn).symm
          (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩)
          rfl rfl
      initiate := hinit S sEnvs needs rfl rfl rfl rfl rfl
      decryptPrekey := hdecPk
      kemDeserialize :=
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget.hc_kemDeserialize_placed
          (callerProg := lsProg_579 H) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }

theorem hrun_cli_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {pksmParse : List (BitVec 8) → Option PreKeySignalMessage}
    {decPkNeed : Nat}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundle mmpl g W A lim cEnvs.readFile)
    (hreadEq : slotEnvs.readFile = cEnvs.readFile)
    (hpub : CliPubCalleesPlaced mmpl g A lim cEnvs
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) aEnvs W)
    (hslots : CliSlotCalleesPlaced mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : (slotsOfPlaced A lim (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv)
      (cliRunSem X W decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hpksm : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_111).base
      (pksmSlotSpecPlaced M A lim
        (aEnvs (cliRunSem X W decPk decPkOk pksmParse)).pksmTryFrom
        (cliRunSem X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W decPk decPkOk pksmParse))) uuidTryParse
        (runRel (cliRunSem X W decPk decPkOk pksmParse)) cliWrOk cliResStack) := by
  let _ := h547
  let _ := hreadEq
  exact
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.run_ok_placed_at_block
      (callerProg := mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 617)
      (hpub.arms (cliRunSem X W decPk decPkOk pksmParse) decPkNeed)
      hHooks.runHooks
      (runCallees_cli_placed mmpl g X W hHooks hreadEq hpub hslots hinit hdecPk)
      hpksm
      (LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget.runNeed_cli_le_resStack_placed
        A lim (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) hdecPkNeed)
      (by decide)
      (by decide)

theorem hrun_cli_d2c_tight_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundle mmpl g W A lim cEnvs.readFile)
    (hreadEq : slotEnvs.readFile = cEnvs.readFile)
    (hpub : CliPubCalleesPlaced mmpl g A lim cEnvs
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) aEnvs W)
    (hslots : CliSlotCalleesPlaced mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPk : DecPkD2cSlotOkPlaced mmpl g W A lim DecPkEnv)
    (hpksm : PksmSlotOkPlaced mmpl g W A lim
      (aEnvs (cliRunSem X W
        (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
        (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
        pksmParse)).pksmTryFrom) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) :=
  hrun_cli_placed mmpl g X W
    (decPk := decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
    (decPkOk := DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
    (pksmParse := pksmParse)
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    h547 hHooks hreadEq hpub hslots hinit
    (by decide)
    (hdecPk X _ (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) rfl rfl rfl rfl rfl)
    (hpksm _ rfl)

theorem hrun_cli_d2c_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundle mmpl g W A lim cEnvs.readFile)
    (hreadEq : slotEnvs.readFile = cEnvs.readFile)
    (hpub : CliPubCalleesPlaced mmpl g A lim cEnvs
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) aEnvs W)
    (hslots : CliSlotCalleesPlaced mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPk : DecPkD2cSlotOkPlaced mmpl g W A lim DecPkEnv)
    (hpksm : PksmSlotOkPlaced mmpl g W A lim
      (aEnvs (cliRunSem X W
        (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
        (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
        pksmParse)).pksmTryFrom) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) :=
  subroutine_ok_runSpecPlaced_of_tight
    (hrun_cli_d2c_tight_placed mmpl g X W h547 hHooks hreadEq hpub hslots hinit hdecPk hpksm)

/-- One-shot D2(c) `signal_session::run` (Block `579`) assembly over any `g : CliGhostHooks`,
building `CliRunHooksBundle` and `CliPubCalleesPlaced` from `RunHooksPlaced` and
`HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym …`. -/
theorem hrun_cli_d2c_tight_of_ghost_hooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk0 : Nat}
    {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hpos : 0 < stk0) (hle : stk0 ≤ cliRunBudgets.readFile)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hsat : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk0 slotEnvs.readFile))
    (hslots : CliSlotCalleesPlaced mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPk : DecPkD2cSlotOkPlaced mmpl g W A lim DecPkEnv)
    (hpksm : PksmSlotOkPlaced mmpl g W A lim PksmTryFromEnv)
    (hinit_addr : ∀ gc d2 fsp,
      InitEnv (r1cInitGhost gc d2 fsp) = InitEnv (r1cInitGhost gc d2 0#64) := by
      intros; rfl)
    (henc_addr : ∀ gc peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv).encrypt (r2EncGhost gc peerG meG fsp) =
        (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv).encrypt
          (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64) := by
      intros; rfl)
    (hdec_ghost : ∀ gc fsp w peerV meG msgG m,
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv).decryptSignal
          (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv).decryptSignal
          (r3aDecSigGhost0 gc peerV meG m) := by
      intros; rfl)
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      DecPkEnv x = DecPkEnv y := by intros; rfl) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalCodeRoLoaded lsmpl) A lim
        (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs slotEnvs.readFile)
          (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) PksmTryFromEnv
          (cliRunSem X W
            (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
            (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
            pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) := by
  have hHooks : CliRunHooksBundle mmpl g W A lim slotEnvs.readFile :=
    cliRunHooksBundle_of_hookSat_mono_stk mmpl g W hpos hle hh hsat
  refine hrun_cli_d2c_tight_placed
    (cEnvs := cliRunCalleesEnvs slotEnvs.readFile)
    (aEnvs := cliRunArmEnvs (cliRunCalleesEnvs slotEnvs.readFile)
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) PksmTryFromEnv)
    mmpl g X W h547 hHooks rfl ?_ hslots hinit hdecPk hpksm
  exact cliPubCallees_d2c_ok mmpl g W hHooks hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost


/-! ## `LibsignalFrozen` / `[LibsignalFullPlacement]` D2(c) `signal_session::run` Composition -/

/-- `LibsignalFrozen` budget-threaded public/arm callee seam for `signal_session::run`
(Blocks `589`, `563`, `593`, `592`, `552`, and `RunArmsFrozenPlaced`) at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
structure CliPubCalleesFrozenPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs) (aEnvs : RunSem → RunArmEnvs)
    (W : CliHooks) : Prop where
  dirGet : ∀ {stk : Nat}, cliRunBudgets.dirGetNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim cEnvs.dirGet stk)
  bundleRead : ∀ {stk : Nat}, cliRunBudgets.bundleReadNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 563)
      (bundleReadSpecPlaced cliIo.rd cliWrOk A lim cEnvs.bundleRead stk)
  splitId : ∀ {stk : Nat}, splitIdNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 593)
      (splitIdSpecPlaced A lim cEnvs.splitId stk)
  splitSigned : ∀ {stk : Nat}, splitSignedNeed ≤ stk →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 592)
      (splitSignedSpecPlaced A lim cEnvs.splitSigned stk)
  dropSpeX : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (blkPl_553).base (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim))
  dropSpe : ∀ (stk : Nat), 32 + extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_553).base
      (dropSpeSpecStkPlaced A lim stk)
  arms : ∀ (S : RunSem) (decPkNeed : Nat),
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunArmsFrozenPlaced
      A lim cEnvs sEnvs (aEnvs S)
      (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
      cliResStack

/-- Discharges all non-arm fields of `CliPubCalleesFrozenPlaced` at `cliRunCalleesEnvs ReadEnv`
from `CliRunHooksBundle`, leaving only `arms`. -/
theorem cliPubCallees_of_arms_frozen_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {aEnvs : RunSem → RunArmEnvs}
    (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl g W A lim ReadEnv)
    (harms : ∀ (S : RunSem) (decPkNeed : Nat),
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.RunArmsFrozenPlaced
        A lim (cliRunCalleesEnvs ReadEnv) sEnvs (aEnvs S)
        (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets S (cliRunNeeds decPkNeed)
        cliResStack) :
    CliPubCalleesFrozenPlaced mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs aEnvs W :=
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  let hh := hHooks.runHooks
  let hRead := hHooks.readFile579
  { dirGet := fun {_stk} hstk =>
      dirGet_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_589 H) (jPath := 589)
        (readProg := lsProg_579 H) (jRead := 579)
        (fun _ hp => hp.2) hh.alloc hh.memcpyRO hh.bcmp
        (by decide) (by decide)
        (path_placed_ok (callerProg := lsProg_589 H) (i := 589)
          hh (Nat.le_refl pathNeed) (by decide))
        (by decide) (by decide)
        (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
        (hh.fs (lsProg_589 H) 589) hstk
        (fun _ _ _ _ h => h) (by decide)
    bundleRead := fun {_stk} hstk =>
      bundleRead_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        (pathProg := lsProg_563 H) (jPath := 563)
        (readProg := lsProg_579 H) (jRead := 579)
        (fun _ hp => hp.2) hh.alloc
        (by decide) (by decide)
        (path_placed_ok (callerProg := lsProg_563 H) (i := 563)
          hh (Nat.le_refl pathNeed) (by decide))
        (by decide) (by decide)
        (subroutine_ok_withLsCodeRoLoaded_of_plain hRead)
        (hh.fs (lsProg_563 H) 563) hstk (by decide)
    splitId := fun {_stk} hstk =>
      splitId_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        hh.alloc
        (cliDropSpe_placed_caller_ok_x
          (callerProg := lsProg_593 H) (i := 593) hh.alloc (by decide))
        hstk (by decide)
    splitSigned := fun {_stk} hstk =>
      splitSigned_placed_caller_ok_of_deps
        (callerProg := lsProg_579 H) (i := 579)
        hh.alloc
        (splitId_placed_caller_ok_of_deps
          (callerProg := lsProg_592 H) (i := 592)
          hh.alloc
          (cliDropSpe_placed_caller_ok_x
            (callerProg := lsProg_593 H) (i := 593) hh.alloc (by decide))
          (Nat.le_refl splitIdNeed) (by decide))
        (cliDropSpe_placed_caller_ok_x
          (callerProg := lsProg_592 H) (i := 592) hh.alloc (by decide))
        hstk (by decide)
    dropSpeX := dropSpeX_placed_ok
      (callerProg := lsProg_579 H) (i := 579) hh (by decide)
    dropSpe := fun stk hstk hstk64 =>
      dropSpe_placed_ok
        (callerProg := lsProg_579 H) (i := 579)
        hh stk hstk hstk64 (by decide)
    arms := harms }

/-- Discharges all 7 fields of `CliPubCalleesFrozenPlaced` at `cliRunCalleesEnvs ReadEnv` and
`cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv` from `CliRunHooksBundle` via
`AllPlacedBudget.runArmsFrozenPlaced_ok`. -/
theorem cliPubCallees_d2c_frozen_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl g W A lim ReadEnv)
    (hinit_addr : ∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64) := by
      intros; rfl)
    (henc_addr : ∀ g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) := by
      intros; rfl)
    (hdec_ghost : ∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m) := by
      intros; rfl)
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y := by intros; rfl) :
    CliPubCalleesFrozenPlaced mmpl g A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv) W :=
  cliPubCallees_of_arms_frozen_placed mmpl g W hHooks fun _ _ =>
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget.runArmsFrozenPlaced_ok
      hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

/-- `[LibsignalFullPlacement]` `RunCalleesPlaced` assembly at `slotsOfSigPkFrozenPlaced` from
`CliSlotCalleesFullPlaced`, `CliInitSlotOkPlaced`, and upgraded `decryptPrekey.OkPlaced`. -/
theorem runCallees_cli_full_placed [CryptoVerification.LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {pksmParse : List (BitVec 8) → Option PreKeySignalMessage}
    {decPkNeed : Nat}
    (hHooks : CliRunHooksBundle mmpl g W A lim cEnvs.readFile)
    (hreadEq : slotEnvs.readFile = cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlaced mmpl g A lim cEnvs
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) aEnvs W)
    (hslots :
      LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget.CliSlotCalleesFullPlaced
        mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPk :
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv)
        (cliRunSem X W decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    RunCalleesPlaced A lim cEnvs (cliGhostExterns g (cliExternsPlaced mmpl W)) cliRunBudgets
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv)
        (cliRunSem X W decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)) := by
  let _ := hreadEq
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  let S := cliRunSem X W decPk decPkOk pksmParse
  let sEnvs := runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv
  let needs := cliRunNeeds decPkNeed
  let hh := hHooks.runHooks
  exact
    { readFile := hHooks.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt :=
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget.cliEncrypt_slotOk_placed
          mmpl g W A lim cliRunBudgets S scopeIn sEnvs needs slotEnvs.spqrSend
          (w1SessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
          (w1IdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
          hh hslots.w1Inner
          CryptoVerification.SignalSession.Cli.Slots.encodeInjOn_deserializeScopeP_Q
          (fun _ h => h)
          (runProofs_encDef_eq_agree ⟨W.C, W.Q⟩ scopeIn)
          (fun _ _ _ _ hf he => ⟨hf.1, he⟩)
          rfl rfl
      decryptSignal :=
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget.cliDecryptSignal_slotOk_full_placed
          mmpl g W A lim cliRunBudgets S scopeIn sEnvs needs slotEnvs.tryDecrypt
          (decSessKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.sessDeser slotEnvs.readFile)
          (decIdKitBudgetEnv A.repAlloc cliRunBudgets slotEnvs.readFile)
          hh hslots.w2SessVt hslots.w2IdVt hslots.w2Inner
          CryptoVerification.SignalSession.Cli.Slots.encodeInjOn_deserializeScopeP_Q
          (fun _ h => h)
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget.decSigDef_eq_runProofs
            ⟨W.C, W.Q⟩ scopeIn).symm
          (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩)
          rfl rfl
      initiate := hinit S sEnvs needs rfl rfl rfl rfl rfl
      decryptPrekey := hdecPk
      kemDeserialize :=
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget.hc_kemDeserialize_placed
          (callerProg := lsProg_579 H) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }

/-- `[LibsignalFullPlacement]` Block-`617` transfer of `signal_session::run` (Block `579`) meeting
`runSpecTightPlaced (LibsignalFrozen lsmpl)`. -/
theorem hrun_cli_full_placed [CryptoVerification.LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8))}
    {decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop}
    {pksmParse : List (BitVec 8) → Option PreKeySignalMessage}
    {decPkNeed : Nat}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundle mmpl g W A lim cEnvs.readFile)
    (hreadEq : slotEnvs.readFile = cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlaced mmpl g A lim cEnvs
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) aEnvs W)
    (hslots :
      LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget.CliSlotCalleesFullPlaced
        mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk :
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv)
        (cliRunSem X W decPk decPkOk pksmParse) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 520))
    (hpksm : subroutine_ok (lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_111).base
      (pksmSlotSpecPlaced M A lim
        (aEnvs (cliRunSem X W decPk decPkOk pksmParse)).pksmTryFrom
        (cliRunSem X W decPk decPkOk pksmParse))) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (CryptoVerification.LibsignalFrozen lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W decPk decPkOk pksmParse))) uuidTryParse
        (runRel (cliRunSem X W decPk decPkOk pksmParse)) cliWrOk cliResStack) := by
  let _ := h547
  let _ := hreadEq
  exact
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget.run_ok_frozen_placed_at_block
      (callerProg := mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 617)
      (hpub.arms (cliRunSem X W decPk decPkOk pksmParse) decPkNeed)
      hHooks.runHooks
      (runCallees_cli_full_placed mmpl g X W hHooks hreadEq hpub hslots hinit hdecPk)
      hpksm
      (LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget.runNeed_cli_le_resStack_placed
        A lim (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) hdecPkNeed)
      (by decide)
      (by decide)

/-- `[LibsignalFullPlacement]` D2(c) `runSpecTightPlaced (LibsignalFrozen lsmpl)` assembly on
`mProgPlaced`. -/
theorem hrun_cli_d2c_tight_full_placed [CryptoVerification.LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundle mmpl g W A lim cEnvs.readFile)
    (hreadEq : slotEnvs.readFile = cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlaced mmpl g A lim cEnvs
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) aEnvs W)
    (hslots :
      LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget.CliSlotCalleesFullPlaced
        mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPk :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget.DecPkD2cSlotOkFrozenPlaced
        mmpl g W A lim DecPkEnv)
    (hpksm : PksmSlotOkPlaced mmpl g W A lim
      (aEnvs (cliRunSem X W
        (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
        (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
        pksmParse)).pksmTryFrom) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (CryptoVerification.LibsignalFrozen lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) :=
  hrun_cli_full_placed mmpl g X W
    (decPk := decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
    (decPkOk := DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
    (pksmParse := pksmParse)
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    h547 hHooks hreadEq hpub hslots hinit
    (by decide)
    (hdecPk X _ (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) rfl rfl rfl rfl rfl)
    (hpksm _ rfl)

/-- `[LibsignalFullPlacement]` D2(c) `runSpecPlaced (LibsignalFrozen lsmpl)` assembly on
`mProgPlaced`. -/
theorem hrun_cli_d2c_full_placed [CryptoVerification.LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {aEnvs : RunSem → RunArmEnvs}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hHooks : CliRunHooksBundle mmpl g W A lim cEnvs.readFile)
    (hreadEq : slotEnvs.readFile = cEnvs.readFile)
    (hpub : CliPubCalleesFrozenPlaced mmpl g A lim cEnvs
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) aEnvs W)
    (hslots :
      LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget.CliSlotCalleesFullPlaced
        mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPk :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget.DecPkD2cSlotOkFrozenPlaced
        mmpl g W A lim DecPkEnv)
    (hpksm : PksmSlotOkPlaced mmpl g W A lim
      (aEnvs (cliRunSem X W
        (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
        (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
        pksmParse)).pksmTryFrom) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecPlaced (CryptoVerification.LibsignalFrozen lsmpl) A lim
        (RunEnv (aEnvs (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) :=
  subroutine_ok_runSpecPlaced_of_tight
    (hrun_cli_d2c_tight_full_placed mmpl g X W h547 hHooks hreadEq hpub hslots hinit hdecPk hpksm)

/-- One-shot `[LibsignalFullPlacement]` D2(c) `signal_session::run` (Block `579`) assembly at
`LibsignalFrozen lsmpl` over any `g : CliGhostHooks`, building `CliRunHooksBundle` and
`CliPubCalleesFrozenPlaced` from `RunHooksPlaced` and `HookSat … lsReadFileSym …`. -/
theorem hrun_cli_d2c_tight_full_of_ghost_hooks [CryptoVerification.LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk0 : Nat}
    {slotEnvs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hpos : 0 < stk0) (hle : stk0 ≤ cliRunBudgets.readFile)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hsat : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim stk0 slotEnvs.readFile))
    (hslots :
      LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudget.CliSlotCalleesFullPlaced
        mmpl g X W A lim slotEnvs)
    (hinit : CliInitSlotOkPlaced mmpl g A lim InitEnv X W)
    (hdecPk :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget.DecPkD2cSlotOkFrozenPlaced
        mmpl g W A lim DecPkEnv)
    (hpksm : PksmSlotOkPlaced mmpl g W A lim PksmTryFromEnv)
    (hinit_addr : ∀ gc d2 fsp,
      InitEnv (r1cInitGhost gc d2 fsp) = InitEnv (r1cInitGhost gc d2 0#64) := by
      intros; rfl)
    (henc_addr : ∀ gc peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv).encrypt (r2EncGhost gc peerG meG fsp) =
        (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv).encrypt
          (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64) := by
      intros; rfl)
    (hdec_ghost : ∀ gc fsp w peerV meG msgG m,
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv).decryptSignal
          (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv).decryptSignal
          (r3aDecSigGhost0 gc peerV meG m) := by
      intros; rfl)
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmTryFromEnv x = PksmTryFromEnv y := by
      intros; rfl)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      DecPkEnv x = DecPkEnv y := by intros; rfl) :
    subroutine_ok (mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (CryptoVerification.LibsignalFrozen lsmpl) A lim
        (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs slotEnvs.readFile)
          (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) PksmTryFromEnv
          (cliRunSem X W
            (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
            (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
            pksmParse)))
        uuidTryParse
        (runRel (cliRunSem X W
          (decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn)
          (DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn)
          pksmParse))
        cliWrOk cliResStack) := by
  have hHooks : CliRunHooksBundle mmpl g W A lim slotEnvs.readFile :=
    cliRunHooksBundle_of_hookSat_mono_stk mmpl g W hpos hle hh hsat
  refine hrun_cli_d2c_tight_full_placed
    (cEnvs := cliRunCalleesEnvs slotEnvs.readFile)
    (aEnvs := cliRunArmEnvs (cliRunCalleesEnvs slotEnvs.readFile)
      (runSlotEnvsOf W A slotEnvs InitEnv DecPkEnv) PksmTryFromEnv)
    mmpl g X W h547 hHooks rfl ?_ hslots hinit hdecPk hpksm
  exact cliPubCallees_d2c_frozen_ok mmpl g W hHooks hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
