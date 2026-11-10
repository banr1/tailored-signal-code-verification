/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# `FdsGe3Closed`-Threaded `signal_session::run` Arm `R1b`

Chains the six sub-stages of Arm `R1b` (`0x074c → 0x28f0`) on Block `579` (`signal_session::run`)
— registration/SPK read (`R1bStepRegSpkPlacedFd`), KPK read (`r1b_step_kpk_placed_fd`), OPK read
(`r1b_step_opk_placed_env_fd`), KEM public-key deserialize/clone (`R1bStepDeserCloneOfKemPlacedFd`),
dealloc/OPK staging (`R1bStepTail25f4PlacedFd`), and final bundle assembly
(`r1b_step_init2_27bc_placed_fd`) — into `run_hop_init2_placed_ok_fd` (`RunHopInit2PlacedFd`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Wire (pkBytesOf)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32 splitId splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_590)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRunEntryPlaced Init1Data Init2Data PanicK RejectKind RunNeeds
   RunSem r1b_CodeOk r1b_OkCtxPlaced r1b_StackBounds r1b_invCoreBase_placed r1b_invCore_placed
   r1b_none_kpk_deser r1b_none_spk_deser r1b_opkStage1At r1b_opkStage1SpkAt r1b_opkStage3At
   r1b_spkBytesOf r1b_stackBounds_of_placed readBundleV runFiles runFsp runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (kemPkDeserialize)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame runNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
   fitsEvents_append rustAllocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (RunHopInit2PlacedFd RunHopInit2PlacedFdOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudget
  (R1bDeserCloneErrEnv R1bDeserCloneOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetFd
  (r1b_step_kpk_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
  (R1bStepOpkErrEnv R1bStepOpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudgetFd
  (r1b_step_opk_placed_env_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
  (r1b_OkCtxPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
  (Init2AfterRegOkEnv Init2Env Init2Stage2Env Init2Stage3Env Init2Stage4Env R1bStepKpkErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAuxFd
  (r1b_step_init2_27bc_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (init1MemPlaced init2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
  (AtInit1PlacedFd AtInit2PlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (kemDeserializeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd slotWithFdsGe3Closed)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAuxFd
  (r1b_step_init2_27bc_placed_fd)

/-! ## 1. External / Deferred Stage Interfaces (Stages 1, 4a, 4b) -/

/-- Stage 1 (`1868 → 4704`, `0x074c → 0x1260`) contract matching
`ReadRegSpkSpinePlacedBudgetFd.r1b_step_reg_spk_placed_fd` on `RunCalleesPlacedFd`. -/
def R1bStepRegSpkPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (cEnvs : RunCalleesEnvs)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (σ : RunSlots) (resStack : Nat) : Prop :=
  ∀ {st : M.σ} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {g : RunCall} {d : Init1Data} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B σ →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    r1b_StackBounds B resStack →
    AtRunEntryPlaced r1b_CodeOk S g s0 →
    r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x074c →
    FdsGe3Closed s.fs →
    s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
    FitsEnv M lim st (PathEnv d.dir (utf8 "registration-id")) →
    (∀ evsRegP, PathEnv d.dir (utf8 "registration-id") evsRegP →
      FitsEnv M lim (M.stepEvents evsRegP st)
        (cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id"))) →
    (∀ evsRegP evsRegRd,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FitsEvents M lim (M.stepEvents (evsRegP ++ evsRegRd) st) [AllocEvent.alloc 22]) →
    (∀ evsRegP evsRegRd evsFree,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsRegP ++ evsRegRd ++ [AllocEvent.alloc 22] ++ evsFree) st)) →
    (∀ evsRegP evsRegRd evsFreeR regBs,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length ≠ 4 →
      FitsEvents M lim (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR) st) [AllocEvent.alloc 14]) →
    (∀ evsRegP evsRegRd evsFreeR regBs evsFree,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length ≠ 4 → FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR ++ [AllocEvent.alloc 14] ++ evsFree) st)) →
    (∀ evsRegP evsRegRd evsFreeR regBs,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      FitsEnv M lim (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR) st)
        (PathEnv d.dir (utf8 "signed-pre-key"))) →
    (∀ evsRegP evsRegRd evsFreeR regBs evsSpkP,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      FitsEnv M lim (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP) st)
        (cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key"))) →
    (∀ evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FitsEvents M lim
        (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd) st)
        [AllocEvent.alloc 22]) →
    (∀ evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFree,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents
          (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            [AllocEvent.alloc 22] ++ evsFree) st)) →
    (∀ evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FreeOnlyEvs evsFreeS →
      FitsEnv M lim
        (M.stepEvents (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS) st)
        (cEnvs.splitSigned spkBs)) →
    (∀ evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs evsSp evsFree2,
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR → regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FreeOnlyEvs evsFreeS →
      splitSigned spkBs = none →
      cEnvs.splitSigned spkBs evsSp →
      FreeOnlyEvs evsFree2 →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents
          (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            evsFreeS ++ evsSp ++ evsFree2) st)) →
    PanicK g s0 Qp →
    RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom →
    (∀ (sf : State)
        (evsRegP evsRegRd evsFreeR evsSpkP evsSpkRd evsFreeS evsSp : List AllocEvent)
        (r0 r1 r2 r3 : BitVec 8)
        (regCap regPtr spkCap spkPtr : BitVec 64)
        (spkBs spkKey spkSig : List (BitVec 8)) (spkId : BitVec 32),
      PathEnv d.dir (utf8 "registration-id") evsRegP →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd →
      FreeOnlyEvs evsFreeR →
      PathEnv d.dir (utf8 "signed-pre-key") evsSpkP →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsSpkRd →
      FreeOnlyEvs evsFreeS →
      cEnvs.splitSigned spkBs evsSp →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x1260 →
      FdsGe3Closed sf.fs →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
        .ok [r0, r1, r2, r3] →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗
          memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗
          memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗
          A.pool lim
            (M.stepEvents
              (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp) st)
            sf)
        Q Qp oom) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (init1MemPlaced A lim st g d s0 s resStack) Q Qp oom

/-- Stage 4a (`9452 → 9716`, `0x24ec → 0x25f4`) contract (`DeserClonePlacedBudgetFd`),
threaded with `slotWithFdsGe3Closed` on `kemDeserialize` and `r1b_OkCtxPlacedFd`. -/
def R1bStepDeserCloneOfKemPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (sEnvs : RunSlotEnvs)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) :
    Prop :=
  ∀ {st : M.σ} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {g : RunCall} {d : Init1Data} {s0 s : State}
    {r0 r1 r2 r3 : BitVec 8}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {kpkBs kpkKey kpkSig spkBs spkKey spkSig opkBs : List (BitVec 8)}
    {kpkId spkId v11c : BitVec 32}
    {opk : Option (BitVec 32 × PublicKey)}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
    RunHooksPlaced A lim H →
    (slotWithFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced
      (lsProg_579 H) (blkPl_590).base →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    r1b_StackBounds B resStack →
    r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 s 0x24ec →
    cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      .ok [r0, r1, r2, r3] →
    cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
    splitSigned spkBs = some (spkId, spkKey, spkSig) →
    cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs →
    splitSigned kpkBs = some (kpkId, kpkKey, kpkSig) →
    cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs →
    ((opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ opkBs.length < 2 ^ 63 ∧
        splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk) ∧
        v11c = opkId ∧
        opkPk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6
          (w0e4.truncate 8) (w0e0.truncate 8) w9 w13 w15 w23 b31)) →
    s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
    s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
    s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
    s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
    s.readReg64 (.gpr 28#5) = 64#64 →
    (∀ spk, PublicKey.deserialize spkKey = .ok spk →
      FitsEvents M lim st (rustAllocEvents 64 1)) →
    (∀ spk, PublicKey.deserialize spkKey = .ok spk →
      FitsEvents M lim (M.stepEvents (rustAllocEvents 64 1) st) (kemDeserializeEvents kpkKey)) →
    (∀ spk kpk, PublicKey.deserialize spkKey = .ok spk →
      kemPkDeserialize kpkKey = .ok kpk →
      FitsEvents M lim
        (M.stepEvents (rustAllocEvents 64 1 ++ kemDeserializeEvents kpkKey) st)
        (rustAllocEvents 64 1)) →
    PanicK g s0 Qp →
    RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom →
    (∀ evs, R1bDeserCloneErrEnv spkKey kpkKey evs →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) →
    (∀ (sf : State) (evs_dc : List AllocEvent) (spk : PublicKey) (kpk : List (BitVec 8))
        (spkSigPtr kpkSigPtr kpkBuf : BitVec 64)
        (spkW0 : BitVec 64) (spkW8 spkW12 : BitVec 32) (spkW16 spkW24 : BitVec 64),
      R1bDeserCloneOkEnv kpkKey evs_dc →
      r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf 0x25f4 →
      readBundleV (runFiles g.i) d.dir d.peerV.device = some {
        idKey := d.idKey, regId := ofLe32 r0 r1 r2 r3, device := d.peerV.device,
        spkId := spkId, spk := spk, spkSig := spkSig,
        kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
      } →
      spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24 →
      (spkSigPtr ≠ 0 ∧ kpkSigPtr ≠ 0 ∧ kpkBuf ≠ 0) →
      (spkSig.length = 64 ∧ kpkSig.length = 64 ∧ kpk.length = 1568) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
          A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
          A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
          ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
            b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
          ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
          ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ kpkSigPtr) ∗
          ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ kpkBuf) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_dc st) sf)
        Q Qp oom) →
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
        ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
        ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
        ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
        ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom

/-- Stage 4b (`9716 → 10172`, `0x25f4 → 0x27bc`) contract (`DeserCloneTailPlacedBudgetFd`),
preserving `r1b_OkCtxPlacedFd` across the three `dealloc` calls and `opk` staging. -/
def R1bStepTail25f4PlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (resStack : Nat) : Prop :=
  ∀ {st : M.σ} {g : RunCall} {d : Init1Data} {s0 s : State}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {kpkId v11c : BitVec 32}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {opk : Option (BitVec 32 × PublicKey)}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
    RunHooksPlaced A lim H →
    r1b_StackBounds B resStack →
    r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 s 0x25f4 →
    ((opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ opkBs.length < 2 ^ 63 ∧
        splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk) ∧
        v11c = opkId ∧
        opkPk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6
          (w0e4.truncate 8) (w0e0.truncate 8) w9 w13 w15 w23 b31)) →
    s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
    s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
    s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
    s.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
    s.readReg64 (.gpr 28#5) = 64#64 →
    PanicK g s0 Qp →
    (∀ (sf : State) (evs : List AllocEvent)
        (c0 c1 c2 c3 c4 c5 c6 : BitVec 8) (c9 : BitVec 32) (c13 : BitVec 16)
        (c23 : BitVec 64) (c31 : BitVec 8),
      let opkFlag : BitVec 32 := if opk.isSome then 1#32 else 0#32
      FreeOnlyEvs evs →
      r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf 0x27bc →
      (∀ p, opk = some p → v11c = p.1 ∧
        p.2.bytes.toList = pkBytesOf c0 c1 c2 c3 c4 c5 c6
          (w0e4.truncate 8) (w0e0.truncate 8) c9 c13 w15 c23 c31) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32 →
      sf.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
            c0 c1 c2 c3 c4 c5 c6 w0e0 w0e4 c9 c13 w15 c23 c31 ∗
          ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) →
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 regBs ∗
        ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ F)
      Q Qp oom

/-! ## 2. Envelope Prefix Helpers & Top-Level `RunHopInit2PlacedFd` Assembly -/

private theorem seqEnv_append_eq {E₁ E₂ : List AllocEvent → Prop} {e₁ e₂ evs : List AllocEvent}
    (heq : evs = e₁ ++ e₂) (h₁ : E₁ e₁) (h₂ : E₂ e₂) :
    SeqEnv E₁ E₂ evs :=
  Or.inr ⟨e₁, e₂, heq, h₁, h₂⟩

private theorem fitsEnv_after {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E E' : List AllocEvent → Prop} (p : List AllocEvent)
    (h : FitsEnv M lim st E) (hsub : ∀ sfx, E' sfx → E (p ++ sfx)) :
    FitsEnv M lim (M.stepEvents p st) E' :=
  fun sfx hs => ((fitsEvents_append M lim p sfx st).mp (h (p ++ sfx) (hsub sfx hs))).2

private theorem fitsEvents_after {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} (p sfx : List AllocEvent)
    (h : FitsEnv M lim st E) (hmem : E (p ++ sfx)) :
    FitsEvents M lim (M.stepEvents p st) sfx :=
  ((fitsEvents_append M lim p sfx st).mp (h (p ++ sfx) hmem)).2

private def mkEnvAt {M : AllocCostModel} (E : List AllocEvent → Prop) (st : M.σ) :
    StoresGhost → RejectKind → M.σ → Prop :=
  fun _ _ st' => ∃ evs, E evs ∧ st' = M.stepEvents evs st

private theorem envAt_of_mem {M : AllocCostModel} {E : List AllocEvent → Prop} {st : M.σ}
    {evs : List AllocEvent} (h : E evs) :
    mkEnvAt E st StoresGhost.opened .postDispatch (M.stepEvents evs st) :=
  ⟨evs, h, rfl⟩

private theorem rej_lift [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {E E' : List AllocEvent → Prop} {st : M.σ} (p : List AllocEvent)
    {g : RunCall} {s0 : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim (mkEnvAt E st) g s0 resStack Q Qp)
    (hsub : ∀ sfx, E' sfx → E (p ++ sfx)) :
    RejectKPlacedEnv r1b_CodeOk H A lim (mkEnvAt E' (M.stepEvents p st)) g s0 resStack Q Qp :=
  fun sf st' g' rk hAt ⟨sfx, hsfx, hst'⟩ =>
    hrej sf st' g' rk hAt ⟨p ++ sfx, hsub sfx hsfx, by rw [hst', M.stepEvents_append]⟩

private theorem init2Env_of_afterRegOk {cEnvs : RunCalleesEnvs} {g : RunCall} {d : Init1Data}
    {evsRegP evsRegRd evsFreeR regBs sfx : List _}
    (hp : PathEnv d.dir (utf8 "registration-id") evsRegP)
    (hok_r : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs)
    (hrd : cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd)
    (hfoR : FreeOnlyEvs evsFreeR)
    (heq4 : regBs.length = 4)
    (hafter : Init2AfterRegOkEnv cEnvs (runFiles g.i) d.dir sfx) :
    Init2Env cEnvs g d ((evsRegP ++ evsRegRd ++ evsFreeR) ++ sfx) := by
  unfold Init2Env
  simp only [hok_r, heq4, ↓reduceIte]
  exact Or.inr (Or.inr
    (SeqEnv.append
      (seqEnv_append_eq (by simp only [List.append_assoc]) (SeqEnv.append hp hrd) hfoR)
      hafter))

private theorem init2Stage4Env_of_deserCloneErr {spkKey kpkKey : List (BitVec 8)}
    {evs : List AllocEvent} (herr : R1bDeserCloneErrEnv spkKey kpkKey evs) :
    Init2Stage4Env spkKey kpkKey evs := by
  unfold Init2Stage4Env
  cases hsd : PublicKey.deserialize spkKey with
  | error e =>
      unfold R1bDeserCloneErrEnv at herr
      rw [hsd] at herr
      exact herr
  | ok spk =>
      refine Or.inr (Or.inr ?_)
      split
      · rename_i kpk hk
        unfold R1bDeserCloneErrEnv at herr
        rw [hsd, hk] at herr
        exact False.elim herr
      · exact herr

/-- Shared `RunSlots`-parametric implementation backing both `run_hop_init2_placed_ok_fd` and
`run_hop_init2_of_slots_placed_ok_fd`. -/
theorem run_hop_init2_of_slots_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots} {resStack : Nat}
    (hstep1 : R1bStepRegSpkPlacedFd A lim cEnvs H B S slots resStack)
    (hstep4a : R1bStepDeserCloneOfKemPlacedFd A lim sEnvs H B S needs resStack)
    (hstep4b : R1bStepTail25f4PlacedFd A lim H B S resStack)
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs))
    (hkem_eq : slots.kemDeserialize = (slotsOfPlaced A lim sEnvs S needs).kemDeserialize) :
    RunHopInit2PlacedFdOf (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs (Init2Env cEnvs) H B S slots resStack := by
  intro g st d1 s0 s1 Q Qp hh hc hdrop hres_slots hres64 he hi1 hfit hpanic hrej hnext
  have hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack :=
    hneed_eq ▸ hres_slots
  have hres' :
      runNeed B (CryptoVerification.SignalSession.Cli.RunCompose.slotsOfPlaced A.repAlloc S needs) ≤
        resStack := hres
  have hbnd : r1b_StackBounds B resStack := r1b_stackBounds_of_placed hres' hres64
  have hok0 : r1b_OkCtxPlaced r1b_CodeOk S g d1 s0 s1 0x074c := r1b_OkCtxPlaced.of_init1 he hi1.1
  have hrej0 : RejectKPlacedEnv r1b_CodeOk H A lim (mkEnvAt (Init2Env cEnvs g d1) st)
      g s0 resStack Q Qp := hrej
  have hkem_ok :
      (slotWithFdsGe3Closed (slotsOfPlaced A lim sEnvs S needs).kemDeserialize).OkPlaced
        (lsProg_579 H) (blkPl_590).base :=
    hkem_eq ▸ hc.kemDeserialize
  refine hstep1 hh hc hdrop hbnd he hok0 hi1.2 hi1.1.x28
    (hfit.mono fun _ hp => Or.inl hp)
    (fun evsRegP hp => fitsEnv_after evsRegP hfit fun _ hrd =>
      Or.inr (Or.inl (SeqEnv.append hp hrd)))
    (fun evsRegP evsRegRd hp herr hrd =>
      fitsEvents_after (evsRegP ++ evsRegRd) [AllocEvent.alloc 22] hfit (by
        unfold Init2Env; dsimp only; rw [herr]
        exact Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hp hrd) (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFree hp herr hrd hfo =>
      envAt_of_mem (by
        unfold Init2Env; dsimp only; rw [herr]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append hp hrd) (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs hp hok_r hrd hfoR hne =>
      fitsEvents_after (evsRegP ++ evsRegRd ++ evsFreeR) [AllocEvent.alloc 14] hfit (by
        unfold Init2Env; simp only [hok_r, hne, ↓reduceIte]
        exact Or.inr (Or.inr
          (SeqEnv.append
            (seqEnv_append_eq (by simp only [List.append_assoc]) (SeqEnv.append hp hrd) hfoR)
            (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsFree hp hok_r hrd hfoR hne hfo =>
      envAt_of_mem (by
        unfold Init2Env; simp only [hok_r, hne, ↓reduceIte]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append (SeqEnv.append hp hrd) hfoR)
            (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs hp hok_r hrd hfoR heq4 =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR) hfit fun _ hsp =>
        init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 (Or.inl hsp))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP hp hok_r hrd hfoR heq4 hsp =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP) hfit fun sfx hsrd => by
        rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP) ++ sfx =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++ (evsSpkP ++ sfx) by simp only [List.append_assoc]]
        exact init2Env_of_afterRegOk hp hok_r hrd hfoR heq4
          (Or.inr (Or.inl (SeqEnv.append hsp hsrd))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd hp hok_r hrd hfoR heq4 hsp hserr hsrd =>
      fitsEvents_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd)
        [AllocEvent.alloc 22] hfit (by
          rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd) ++
              [AllocEvent.alloc 22] =
              (evsRegP ++ evsRegRd ++ evsFreeR) ++
                ((evsSpkP ++ evsSpkRd) ++ [AllocEvent.alloc 22]) by simp only [List.append_assoc]]
          refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
          unfold Init2AfterRegOkEnv; dsimp only; rw [hserr]
          exact Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hsp hsrd) (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFree
        hp hok_r hrd hfoR heq4 hsp hserr hsrd hfo =>
      envAt_of_mem (by
        rw [show evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            [AllocEvent.alloc 22] ++ evsFree =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++
              (evsSpkP ++ evsSpkRd ++ [AllocEvent.alloc 22] ++ evsFree) by
          simp only [List.append_assoc]]
        refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
        unfold Init2AfterRegOkEnv; dsimp only; rw [hserr]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append hsp hsrd) (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs
        hp hok_r hrd hfoR heq4 hsp hsok hsrd hfoS =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS) hfit
        fun sfx hssp => by
          rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS) ++ sfx =
              (evsRegP ++ evsRegRd ++ evsFreeR) ++ ((evsSpkP ++ evsSpkRd ++ evsFreeS) ++ sfx) by
            simp only [List.append_assoc]]
          refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
          unfold Init2AfterRegOkEnv; dsimp only; rw [hsok]
          exact Or.inr (Or.inr (Or.inl
            (SeqEnv.append
              (seqEnv_append_eq (by simp only [List.append_assoc]) (SeqEnv.append hsp hsrd) hfoS)
              hssp))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs evsSp evsFree2
        hp hok_r hrd hfoR heq4 hsp hsok hsrd hfoS hsnone hssp hfo2 =>
      envAt_of_mem (by
        rw [show evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            evsFreeS ++ evsSp ++ evsFree2 =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++
              (evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp ++ evsFree2) by
          simp only [List.append_assoc]]
        refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
        unfold Init2AfterRegOkEnv; simp only [hsok, hsnone]
        exact Or.inr (Or.inr (Or.inr
          (SeqEnv.append
            (SeqEnv.append (SeqEnv.append (SeqEnv.append hsp hsrd) hfoS) hssp)
            hfo2)))))
    hpanic hrej0
    fun sf1 evsRegP evsRegRd evsFreeR evsSpkP evsSpkRd evsFreeS evsSp
        r0 r1 r2 r3 regCap regPtr spkCap spkPtr spkBs spkKey spkSig spkId
        hp hrd hfoR hsp hsrd hfoS hssp hok1_plain hfds1 hreg_rd hspk_rd hspk_sp
        hx10_1 hx27_1 hx2_1 hx26_1 hx28_1 => ?_
  have hok1 : r1b_OkCtxPlacedFd r1b_CodeOk S g d1 s0 sf1 0x1260 := ⟨hok1_plain, hfds1⟩
  let pfx1 := evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp
  have hlift1 : ∀ sfx, Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey sfx →
      Init2Env cEnvs g d1 (pfx1 ++ sfx) := fun sfx hs2 => by
    dsimp only [pfx1]
    rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp) ++ sfx =
        (evsRegP ++ evsRegRd ++ evsFreeR) ++ ((evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp) ++ sfx) by
      simp only [List.append_assoc]]
    refine init2Env_of_afterRegOk hp hreg_rd hrd hfoR rfl ?_
    unfold Init2AfterRegOkEnv; simp only [hspk_rd, hspk_sp]
    exact Or.inr (Or.inr (Or.inr
      (SeqEnv.append
        (SeqEnv.append (SeqEnv.append (SeqEnv.append hsp hsrd) hfoS) hssp)
        hs2)))
  have hfit1 := fitsEnv_after pfx1 hfit hlift1
  have hrej1 := rej_lift pfx1 hrej0 hlift1
  have hnext1 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2PlacedFd r1b_CodeOk g d2 s0 s2 →
      Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs (M.stepEvents pfx1 st)) g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append pfx1 evs st]
    exact hnext s2 (pfx1 ++ evs) d2 hi2 (hlift1 evs hevs)
  refine r1b_step_kpk_placed_fd hh hc hdrop hbnd he hok1 hreg_rd hspk_rd hspk_sp
    hx10_1 hx27_1 hx2_1 hx26_1 hx28_1
    (hfit1.mono fun _ h => Or.inl h)
    (fun evsKpkBr evsFree herr hbr hfo =>
      envAt_of_mem (Or.inr (Or.inl (by
        unfold R1bStepKpkErrEnv; rw [herr]; exact SeqEnv.append hbr hfo))))
    (fun evsKpkBr kpkBs hok_k hbr =>
      fitsEnv_after evsKpkBr hfit1 fun _ hksp => by
        unfold Init2Stage2Env; rw [hok_k]
        exact Or.inr (Or.inr (Or.inl (SeqEnv.append hbr hksp))))
    (fun evsKpkBr kpkBs evsKpkSp evsFree hok_k hbr hnone hksp hfo =>
      envAt_of_mem (Or.inr (Or.inl (by
        unfold R1bStepKpkErrEnv; rw [hok_k]
        exact ⟨hnone, seqEnv_append_eq (by simp only [List.append_assoc])
          (SeqEnv.append hbr hksp) hfo⟩))))
    hpanic hrej1
    fun sf2 evsKpkBr evsKpkSp kpkCap kpkPtr kpkBs kpkKey kpkSig kpkId
        hbr hksp hok2 hkpk_rd hkpk_sp
        hx25_2 hx28_2 hx26_2 hx27_2 hx9_2 hx10_2 hx8_2 hx23_2 hx24_2 => ?_
  let pfx2 := evsKpkBr ++ evsKpkSp
  have hlift2 : ∀ sfx, Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey sfx →
      Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey (pfx2 ++ sfx) := fun sfx hs3 => by
    unfold Init2Stage2Env; simp only [hkpk_rd, hkpk_sp]
    exact Or.inr (Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hbr hksp) hs3)))
  have hfit2 := fitsEnv_after pfx2 hfit1 hlift2
  have hrej2 := rej_lift pfx2 hrej1 hlift2
  have hnext2 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2PlacedFd r1b_CodeOk g d2 s0 s2 →
      Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs (M.stepEvents pfx2 (M.stepEvents pfx1 st)))
          g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append pfx2 evs]
    exact hnext1 s2 (pfx2 ++ evs) d2 hi2 (hlift2 evs hevs)
  refine r1b_step_opk_placed_env_fd hh hc hdrop hbnd he hok2
    hx25_2 hx28_2 hx26_2 hx27_2 hx9_2 hx10_2 hx8_2 hx23_2 hx24_2
    (hfit2.mono fun _ h => Or.inl h)
    (fun evs_br opkBs hne hbr_o hok_o => by
      cases opkBs with
      | nil => exact False.elim (hne rfl)
      | cons b bs =>
          exact fitsEnv_after evs_br hfit2 fun _ hsp_o => by
            unfold Init2Stage3Env; rw [hok_o]
            exact Or.inr (Or.inr (Or.inl (SeqEnv.append hbr_o hsp_o))))
    hpanic hrej2
    (fun evs herr => envAt_of_mem (Or.inr (Or.inl herr)))
    fun sf3 evs_opk opkBs opk v11c b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31
        hopk_ok hok3 hopk_rd hopk_sem hx23_3 hx24_3 hx25_3 hx27_3 hx28_3 => ?_
  have hlift3 : ∀ sfx, Init2Stage4Env spkKey kpkKey sfx →
      Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey (evs_opk ++ sfx) := fun sfx hs4 => by
    rcases hopk_sem with ⟨rfl, _⟩ | ⟨opkId, opkKey, opkPk, hne, _, hsp_o, hdes_o, _⟩
    · unfold Init2Stage3Env; rw [hopk_rd]
      exact Or.inr (Or.inr (SeqEnv.append hopk_ok hs4))
    · cases opkBs with
      | nil => exact False.elim (hne rfl)
      | cons b bs =>
          unfold Init2Stage3Env; simp only [hopk_rd, hsp_o, hdes_o]
          exact Or.inr (Or.inr (Or.inr (SeqEnv.append hopk_ok hs4)))
  have hfit3 := fitsEnv_after evs_opk hfit2 hlift3
  have hrej3 := rej_lift evs_opk hrej2 hlift3
  have hnext3 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2PlacedFd r1b_CodeOk g d2 s0 s2 →
      Init2Stage4Env spkKey kpkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim
          (M.stepEvents evs (M.stepEvents evs_opk (M.stepEvents pfx2 (M.stepEvents pfx1 st))))
          g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append evs_opk evs]
    exact hnext2 s2 (evs_opk ++ evs) d2 hi2 (hlift3 evs hevs)
  refine hstep4a hh hkem_ok hdrop hbnd hok3
    hreg_rd hspk_rd hspk_sp hkpk_rd hkpk_sp hopk_rd hopk_sem
    hx23_3 hx24_3 hx25_3 hx27_3 hx28_3
    (fun spk hspk_d => hfit3 (rustAllocEvents 64 1) (by
      unfold Init2Stage4Env; rw [hspk_d]; exact Or.inl rfl))
    (fun spk hspk_d => fitsEvents_after (rustAllocEvents 64 1) (kemDeserializeEvents kpkKey) hfit3 (by
      unfold Init2Stage4Env; rw [hspk_d]; exact Or.inr (Or.inl rfl)))
    (fun spk kpk hspk_d hkpk_d =>
      fitsEvents_after (rustAllocEvents 64 1 ++ kemDeserializeEvents kpkKey) (rustAllocEvents 64 1)
        hfit3 (by
          unfold Init2Stage4Env; rw [hspk_d, hkpk_d]
          exact Or.inr (Or.inr (SeqEnv.inl (by
            unfold R1bDeserCloneOkEnv; simp only [List.append_assoc])))))
    hpanic hrej3
    (fun evs herr => envAt_of_mem (init2Stage4Env_of_deserCloneErr herr))
    fun sf4 evs_dc spk kpk spkSigPtr kpkSigPtr kpkBuf spkW0 spkW8 spkW12 spkW16 spkW24
        hDcOk hok4 hbundle hspk_bytes hptrs hlens hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 => ?_
  have ⟨spk', hsd⟩ : ∃ spk', PublicKey.deserialize spkKey = .ok spk' := by
    cases h : PublicKey.deserialize spkKey with
    | error e =>
        have hnone := r1b_none_spk_deser (dev := d1.peerV.device) hspk_rd hspk_sp h
        rw [hbundle] at hnone; cases hnone
    | ok v => exact ⟨v, rfl⟩
  have ⟨kpk', hkd⟩ : ∃ kpk', kemPkDeserialize kpkKey = .ok kpk' := by
    cases h : kemPkDeserialize kpkKey with
    | ok v => exact ⟨v, rfl⟩
    | _ =>
        have hnone := r1b_none_kpk_deser (dev := d1.peerV.device) hkpk_rd hkpk_sp
          (fun _ hk => by rw [h] at hk; cases hk)
        rw [hbundle] at hnone; cases hnone
  let fsp := runFsp s0
  let tailFrame : SepProp :=
    memRegion (fsp + 0x4d0#64) 48 ∗
      A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
      A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
      A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
      r1b_invCoreBase_placed A.repAlloc g d1 s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ownedBytes A.repAlloc d1.dirCap d1.dirPtr (BitVec.ofNat 64 d1.dir.length) d1.dir ∗
      ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
      ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
      ((fsp + 0x138#64) ↦₆₄ kpkSigPtr) ∗
      ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
      ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
      ((fsp + 0x178#64) ↦₆₄ kpkBuf) ∗
      ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d1.ikW3) ∗
      ((fsp + 0x1a8#64) ↦₆₄ d1.ikW1) ∗
      ((fsp + 0x1b0#64) ↦₃₂ d1.peerV.device.zeroExtend 32) ∗
      memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24
  let st4 := M.stepEvents evs_dc (M.stepEvents evs_opk (M.stepEvents pfx2 (M.stepEvents pfx1 st)))
  have htail := hstep4b
    (st := st4) (Q := Q) (Qp := Qp) (oom := fun _ => ⌜False⌝)
    (spkW0 := spkW0) (spkW8 := spkW8) (spkW16 := spkW16) (spkW24 := spkW24)
    (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkBs := kpkBs)
    (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
    (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
    (F := tailFrame)
    hh hbnd hok4 hopk_sem hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hpanic
    fun sf5 evs_tail c0 c1 c2 c3 c4 c5 c6 c9 c13 c23 c31
        hfo_tail hok5 hopk_pk hx23_5 hx24_5 hx25_5 hx26_5 hx28_5 => by
      have hStage4 : Init2Stage4Env spkKey kpkKey (evs_dc ++ evs_tail) := by
        unfold Init2Stage4Env; rw [hsd, hkd]
        exact Or.inr (Or.inr (SeqEnv.append hDcOk hfo_tail))
      have hstep := r1b_step_init2_27bc_placed_fd
        (A := A) (lim := lim) (st := M.stepEvents evs_tail st4) (H := H) (resStack := resStack)
        (Q := Q) (Qp := Qp) (oom := fun _ => ⌜False⌝)
        (kpkPtr := kpkPtr) (v130 := kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)
        (kpkCap := kpkCap) (spkPtr := spkPtr) (spkCap := spkCap)
        (regCap := regCap) (regPtr := regPtr)
        hok5 hbundle hspk_bytes hptrs hlens hopk_pk
        hx23_5 hx24_5 hx25_5 hx26_5 hx28_5
        (fun s2 d2 hi2 => by
          dsimp only [st4]
          rw [← M.stepEvents_append evs_dc evs_tail]
          exact hnext3 s2 (evs_dc ++ evs_tail) d2 hi2 hStage4)
      dsimp only [tailFrame, fsp, st4] at hstep ⊢
      exact sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep
  dsimp only [tailFrame, fsp, st4] at htail ⊢
  exact sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl)) htail

/-- `FdsGe3Closed`-threaded top-level hop theorem for Arm `R1b`
(`R + 1868 → R + 10480`, `0x074c → 0x28f0`) on `slotsOfPlaced A lim sEnvs S needs`. -/
theorem run_hop_init2_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (hstep1 : R1bStepRegSpkPlacedFd A lim cEnvs H B S (slotsOfPlaced A lim sEnvs S needs) resStack)
    (hstep4a : R1bStepDeserCloneOfKemPlacedFd A lim sEnvs H B S needs resStack)
    (hstep4b : R1bStepTail25f4PlacedFd A lim H B S resStack) :
    RunHopInit2PlacedFd (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs (Init2Env cEnvs) H B S needs resStack :=
  run_hop_init2_of_slots_placed_ok_fd hstep1 hstep4a hstep4b rfl rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetFd
