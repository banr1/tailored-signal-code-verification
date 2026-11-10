/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Budget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Placed CLI Poll Overwrite-Path (`Path C`) Stage P4 Continuation

Defines the CLI `Prev1` session-store budget envelopes (`cliPollSessPrev1StorePollEnv`,
`cliPollSessPrev1BudgetEnv`, `CliStageP4Prev1Envs`, `cliPollStageP4Prev1Envs`), states
`StageP4Prev1VRegsPlacedStmt` and `StageP4Prev1CliPlacedStmt`, and proves budget-threaded
`closure_pathC_p4_cont_placed` and `closure_pathC_p4_cont_cli_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  CliGhostHooks cliGhostExterns
)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over hiding
  stageP4Prev1SharedPlaced stageP4Prev1RawPrePlaced stageP4Prev1PrePlaced stageP4Prev1ExitAtPlaced
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  stageP4Prev1CallStack_le_subStack_placed cliFiles_eq_of_trace_eq_placed
  cliPollStageP4Prev1_fsAt_placed pathC_recPrev1Ok_of_tryDecrypt_placed
  cliPollPrev1StoresKitsAtPlaced_entails_storesAt overGenP3S5PostFrame_placed
  overGenP3Pre_placed overStageP3ErrPostPrevEmpty_placed overPathAP4RemAtPlaced
  overExit_entails_dpPollPost_placed stageP3MidPathC_entails_p4_placed
  stageP4PathCExit_entails_exit_placed
  StageP4Prev1RawBranchPlaced StageP4Prev1BranchPlaced StageP4Prev1VRegsPlacedStmt
  closure_pathC_p4_cont_placed
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (KyberPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget (
  SerializePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBridgePlacedBudget (
  SerializePrev1EnvX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget (
  StageP4StorePrev1ExitEnv StorePrev1BudgetEnv StorePrev1StepEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1BranchPlaced StageP4Prev1ExitEnv StageP4Prev1NoneExitEnv StageP4Prev1NoneStepEnv
  StageP4Prev1RawBranchPlaced StageP4Prev1StepEnv StageP4Prev1StoreBranchEnv
  fitsEnv_prev1Step_of_exit
  stageP4Prev1ExitAtPlaced stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced stageP4Prev1SharedPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (AddrTextValEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  cliPollPrev1StoresKitsAtPlaced_entails_storesAt overExit_entails_dpPollPost_placed
  overGenP3S5PostFrame_placed overPathAP4RemAtPlaced pathC_recPrev1Ok_of_tryDecrypt_placed
  stageP3MidPathC_entails_p4_placed
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Placed Stage P4 Stack-Budget, Filesystem, and 3-State Spatial Bridges on `Prev1` -/

abbrev stageP4Prev1CallStack_le_subStack_placed :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP4Prev1CallStack_le_subStack_placed

theorem cliFiles_eq_of_trace_eq_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {s0 sf : State} (hh : RunHooksPlaced A lim ext)
    (hsteps : Steps prog s0 sf) (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (hh.fs prog i).files_eq hsteps (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil

theorem cliPollStageP4Prev1_fsAt_of_sound [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (A_r : RustAlloc)
    (hfs : TraceFsSound (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (F0 : FsFiles) (peer : AddrGhost) (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (σ : DpKitStk) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4EnvOk
        (cliPollSessPrev1KitPlaced A_r F0 peer σ)
        (cliPollIdKitPlaced A_r F0 peer σ)
        (cliPollPkKitPlaced A_r F0 pid σ)
        (cliPollKpkKitPlaced A_r F0 kpkId spkId kbk σ))
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4Quiet
        (cliPollSessPrev1KitPlaced A_r F0 peer σ)
        (cliPollIdKitPlaced A_r F0 peer σ)
        (cliPollPkKitPlaced A_r F0 pid σ)
        (cliPollKpkKitPlaced A_r F0 kpkId spkId kbk σ))
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s :=
  .inr ⟨⟨cliPollSessPrev1Placed_quiet F0 peer σ,
         cliPollIdPlaced_quiet F0 peer σ,
         cliPollPkPlaced_quiet F0 pid σ,
         cliPollKpkPlaced_quiet F0 kpkId spkId kbk σ⟩,
        hfs, ⟨hf, hf, hf, hf⟩⟩

theorem cliPollStageP4Prev1_fsAt_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (A_r : RustAlloc)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (peer : AddrGhost) (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (σ : DpKitStk) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4EnvOk
        (cliPollSessPrev1KitPlaced A_r F0 peer σ)
        (cliPollIdKitPlaced A_r F0 peer σ)
        (cliPollPkKitPlaced A_r F0 pid σ)
        (cliPollKpkKitPlaced A_r F0 kpkId spkId kbk σ))
      (Cli.E2E.Pqxdh.ResponderClosure.Kits.stageP4Quiet
        (cliPollSessPrev1KitPlaced A_r F0 peer σ)
        (cliPollIdKitPlaced A_r F0 peer σ)
        (cliPollPkKitPlaced A_r F0 pid σ)
        (cliPollKpkKitPlaced A_r F0 kpkId spkId kbk σ))
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s :=
  cliPollStageP4Prev1_fsAt_of_sound A_r
    (hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518)
    F0 peer pid kpkId spkId kbk σ hf

/-- 3-state `stageP3DispatchOkMidPrev1Placed`, evaluating `A.pool` at the post-Step5 state `s'`
while indexing stack slots at `s.sp`. -/
def stageP3DispatchOkMidPrev1At_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s' : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (enc pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  Over.stageP3DispatchOkMidPrev1Placed (A.atState lim st_b s') s0 s coroPtr outPtr initErrsPtr
    prevCap prevPtr ptCap ptPtr enc pt b_2c0 G₂ st₂

/-! ## 2. Concrete CLI `Prev1` Envelopes & Placed Stage P4 Interfaces (`StageP4Prev1*PlacedStmt`) -/

/-- Exact binary allocation envelope of CLI `<SessionFiles as SessionStore>::store_session` poll
on a 1-element `previous_sessions = [enc]` record (`AddrTextValEnv` → `SerializePrev1EnvX` →
`DirPutEnv`), matching `CliStorePollPrev1Env` by `rfl` with zero existential quantifiers. -/
def cliPollSessPrev1StorePollEnv
    (d : DirGhost) (rem : AddrVal) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (AddrTextValEnv DecimalEnv rem)
    (SeqEnv (SerializePrev1EnvX G sess enc)
      (DirPutEnv d (Cli.addressText rem) (Over.encodeRecordPrev1Mem G sess enc)))

/-- Concrete `StorePrev1BudgetEnv` for `cliPollSessPrev1KitPlaced`. -/
def cliPollSessPrev1BudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) :
    StorePrev1BudgetEnv (cliPollSessPrev1KitPlaced A F0 peer σ) where
  storePollPrev1Env := cliPollSessPrev1StorePollEnv

/-- SeqFree (`SerializePrev1Env` = `SerializePrev1SeqFreeEnv`) binary allocation envelope of CLI
`<SessionFiles as SessionStore>::store_session` poll on a 1-element `previous_sessions = [enc]`
record (`AddrTextValEnv` → `SerializePrev1Env` → `DirPutEnv`), matching
`CliStorePollPrev1Env (AddrTextEnv DecimalEnv) SerializePrev1Env DirPutEnv` by `rfl`. -/
def cliPollSessPrev1SeqFreeStorePollEnv
    (d : DirGhost) (rem : AddrVal) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (AddrTextValEnv DecimalEnv rem)
    (SeqEnv (SerializePrev1Env G sess enc)
      (DirPutEnv d (Cli.addressText rem) (Over.encodeRecordPrev1Mem G sess enc)))

/-- SeqFree `StorePrev1BudgetEnv` for `cliPollSessPrev1KitPlaced` (`SerializePrev1Env`). -/
def cliPollSessPrev1SeqFreeBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) :
    StorePrev1BudgetEnv (cliPollSessPrev1KitPlaced A F0 peer σ) where
  storePollPrev1Env := cliPollSessPrev1SeqFreeStorePollEnv

/-- Bundle of the 4 placed CLI Stage P4 `Prev1` kit allocation envelopes (`storePrev1`, `identity`,
`preKey`, `kyberPreKey`). -/
structure CliStageP4Prev1Envs [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey) where
  opsEnv : StorePrev1BudgetEnv (cliPollSessPrev1KitPlaced A F0 peer (cliKitStk B))
  ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A F0 peer (cliKitStk B))
  pkKitEnv : PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 pid (cliKitStk B))
  kpkKitEnv : KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))

/-- Concrete CLI 4-kit `Prev1` Stage P4 budget envelope bundle binding `cliPollSessPrev1BudgetEnv`,
`cliPollIdBudgetEnv`, `cliPollPkBudgetEnv`, and `cliPollKpkBudgetEnv`. -/
def cliPollStageP4Prev1Envs [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk where
  opsEnv := cliPollSessPrev1BudgetEnv A F0 peer (cliKitStk B)
  ikitEnv := cliPollIdBudgetEnv A F0 peer (cliKitStk B) ReadEnv
  pkKitEnv := cliPollPkBudgetEnv A F0 pid (cliKitStk B) ReadEnv
  kpkKitEnv := cliPollKpkBudgetEnv A F0 kpkId spkId kbk (cliKitStk B) ReadEnv

/-- SeqFree CLI 4-kit `Prev1` Stage P4 budget envelope bundle binding
`cliPollSessPrev1SeqFreeBudgetEnv`, `cliPollIdBudgetEnv`, `cliPollPkBudgetEnv`, and
`cliPollKpkBudgetEnv`. -/
def cliPollStageP4Prev1SeqFreeEnvs [LibsignalPlacement] (A : RustAlloc)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk where
  opsEnv := cliPollSessPrev1SeqFreeBudgetEnv A F0 peer (cliKitStk B)
  ikitEnv := cliPollIdBudgetEnv A F0 peer (cliKitStk B) ReadEnv
  pkKitEnv := cliPollPkBudgetEnv A F0 pid (cliKitStk B) ReadEnv
  kpkKitEnv := cliPollKpkBudgetEnv A F0 kpkId spkId kbk (cliKitStk B) ReadEnv

/-- Budget-threaded placed Stage P4 (`+0x34dc → s0.readReg64 .x30`) contract over 1-element
`previous_sessions` on `dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`
parameterized by `p4Envs`, eliminating `PanicOomProp` (`onPanic := fun _ _ => False`). -/
def StageP4Prev1VRegsPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey) (st_b : M.σ),
    let σ := cliKitStk B
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer σ
    let ops : Over.StorePrev1Ops kit := cliPollStorePrev1OpsPlaced
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    let envs := p4Envs B F0 peer pid kpkId spkId kbk
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      FitsEnv M lim st_b
        (StageP4Prev1ExitEnv kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv sst0 ist0 pst0 kst0 opkId? peer.val remoteIk
          kyberPreKeyId signedPreKeyId baseKey G ss enc) →
      SessionExtraRel G ss → ops.RecPrev1Ok G ss enc →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4Prev1PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4Prev1BranchPlaced A lim st_b kit ops envs.opsEnv ikit envs.ikitEnv
            pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
            ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
            baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
        (fun _ _ => False)

/-- Concrete CLI-instantiated budget-threaded `Prev1` 4-kit Stage P4 statement binding the four
store budget envelopes to `cliPollStageP4Prev1Envs` (`cliPollSessPrev1BudgetEnv`,
`cliPollIdBudgetEnv`, `cliPollPkBudgetEnv`, `cliPollKpkBudgetEnv`), matching
`StageP4PathACliPlacedStmt`. -/
def StageP4Prev1CliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
    let σ := cliKitStk B
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer σ
    let ops : Over.StorePrev1Ops kit := cliPollStorePrev1OpsPlaced
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    let envs := cliPollStageP4Prev1Envs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      FitsEnv M lim st_b
        (StageP4Prev1ExitEnv kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv sst0 ist0 pst0 kst0 opkId? peer.val remoteIk
          kyberPreKeyId signedPreKeyId baseKey G ss enc) →
      SessionExtraRel G ss → ops.RecPrev1Ok G ss enc →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4Prev1PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4Prev1BranchPlaced A lim st_b kit ops envs.opsEnv ikit envs.ikitEnv
            pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
            ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
            baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
        (fun _ _ => False)

/-- Specializes `StageP4Prev1CliPlacedStmt` to `StageP4Prev1VRegsPlacedStmt` once `lsReadFileSym`
is discharged. -/
theorem stageP4Prev1VRegsPlaced_of_cli [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (hCli : StageP4Prev1CliPlacedStmt)
    (hRead : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets),
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    StageP4Prev1VRegsPlacedStmt A lim
      (fun B F0 peer pid kpkId spkId kbk =>
        cliPollStageP4Prev1Envs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv) :=
  fun mmpl gh W B F0 peer pid kpkId spkId kbk st_b hh =>
    hCli mmpl gh W B F0 peer pid kpkId spkId kbk hh (hRead mmpl gh W B) st_b

/-- SeqFree (`SerializePrev1Env` = `SerializePrev1SeqFreeEnv`) CLI-instantiated budget-threaded
`Prev1` 4-kit Stage P4 statement binding the four store budget envelopes to
`cliPollStageP4Prev1SeqFreeEnvs` (`cliPollSessPrev1SeqFreeBudgetEnv`, `cliPollIdBudgetEnv`,
`cliPollPkBudgetEnv`, `cliPollKpkBudgetEnv`). -/
def StageP4Prev1SeqFreeCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
    let σ := cliKitStk B
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer σ
    let ops : Over.StorePrev1Ops kit := cliPollStorePrev1OpsPlaced
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    let envs := cliPollStageP4Prev1SeqFreeEnvs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      FitsEnv M lim st_b
        (StageP4Prev1ExitEnv kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv sst0 ist0 pst0 kst0 opkId? peer.val remoteIk
          kyberPreKeyId signedPreKeyId baseKey G ss enc) →
      SessionExtraRel G ss → ops.RecPrev1Ok G ss enc →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4Prev1PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4Prev1BranchPlaced A lim st_b kit ops envs.opsEnv ikit envs.ikitEnv
            pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
            ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
            baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
        (fun _ _ => False)

/-- Specializes `StageP4Prev1SeqFreeCliPlacedStmt` to `StageP4Prev1VRegsPlacedStmt` at
`cliPollStageP4Prev1SeqFreeEnvs` once `lsReadFileSym` is discharged. -/
theorem stageP4Prev1SeqFreeVRegsPlaced_of_cli [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (hCli : StageP4Prev1SeqFreeCliPlacedStmt)
    (hRead : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets),
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    StageP4Prev1VRegsPlacedStmt A lim
      (fun B F0 peer pid kpkId spkId kbk =>
        cliPollStageP4Prev1SeqFreeEnvs A.repAlloc B F0 peer pid kpkId spkId kbk ReadEnv) :=
  fun mmpl gh W B F0 peer pid kpkId spkId kbk st_b hh =>
    hCli mmpl gh W B F0 peer pid kpkId spkId kbk hh (hRead mmpl gh W B) st_b

/-! ## 3. 3-State Exit Entailment & Placed Stage P4 Continuation on Path C -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
theorem stageP4PathCExitAt_entails_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S)) (s0 s' sf : State)
    (rngPtr initErrsPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (outSlot preKeyMsgRem coinsPost : SepProp) (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32) (pt : List (BitVec 8))
    (res : Except (ApiError AddrVal Unit) Bytes)
    (sstf pstf : DirGhost) (istf : IdGhost) (kstf : KyberGhost) (g' : StoresGhost)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout : outSlot ⊢ decResAt A.repAlloc y.out res ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sstf) (hid : g'.identity = istf) (hot : g'.oneTime = pstf)
    (hspk : g'.signed = StoresGhost.opened.signed) (hkpk : g'.kyber = kstf)
    (hpub : g'.pub = StoresGhost.opened.pub) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ
    stageP4Prev1ExitAtPlaced A lim stf prev1Kit ikit pkKit kpkKit s0 s' sf
      y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64) ptCap ptPtr initErrsPtr
      (coroOpkIdAtP4 y.fut opkId?) outSlot kpkId spkId pt y.g.peer y.g.msg.identityKey
      y.g.msg.baseKey sstf istf pstf kstf ∗
    overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId
      preKeyMsgRem coinsPost ⊢
    decResAt A.repAlloc y.out res ∗ storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗ A.pool lim stf sf ∗ (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗ stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  unfold stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced overPathAP4RemAtPlaced
  have hvt_s : (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hvt_i : (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hvt_p : (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).pk_vt =
      lsρ cliPreKeyVtSym := rfl
  have hvt_k : (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt =
      lsρ cliKyberPreKeyVtSym := rfl
  have hcall_eq :
      stageP4CallStack (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ)
        (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ) =
      stageP4CallStack (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ)
        (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ) := rfl
  rw [hs'_sp, hvt_s, hvt_i, hvt_p, hvt_k, hcall_eq]
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A.repAlloc y.g.F pid σ)
          (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
      stackAt sp (stageP4CallStack
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ)
        (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ)) =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B
      (cliPollStageP4Stack_le_subStack A.repAlloc 0#64 y.g.F Slots.scopeKit y.g.peer
        pid kpkId spkId y.g.msg.baseKey B) hsp_sub).symm
  have hstores :
      (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ).storeAt (y.g.stores + 0xf0#64) sstf ∗
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
      (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt (y.g.stores + 0xc8#64) pstf ∗
      (cliPollSpkKitPlaced A.repAlloc y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) kstf ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
      storesAt A.repAlloc y.g.stores g' := by
    rw [← hsess, ← hid, ← hot, ← hspk, ← hkpk, ← hpub]
    exact cliPollPrev1StoresKitsAtPlaced_entails_storesAt (A := A.repAlloc) y.g.F y.g.peer pid spkId
      kpkId y.g.msg.baseKey σ y.g.stores g'
  have hcopy_join :=
    (coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr).symm
  have h298 := coroOpkIdAtP4_entails_memRegion8 y.fut opkId?
  have h2a0 := coro_2a0_2a8_entails y.fut (kpkId ++ 1#32) spkId
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hstack := stageP4Exit_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA
    0xfffffffffffffffe#64 ptCap ptPtr (BitVec.ofNat 64 pt.length) 0#64 initErrsPtr 0#64 msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      outSlot ∗
      ((cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ).storeAt (y.g.stores + 0xf0#64) sstf ∗
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
          (y.g.stores + 0xc8#64) pstf ∗
        (cliPollSpkKitPlaced A.repAlloc y.g.F spkId σ).storeAt
          (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
        (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
          (y.g.stores + 0x78#64) kstf ∗
        dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim stf sf ∗
      (LsTokenInit ∗ coinsPost) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        ((((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
          ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗ ((y.fut + 0x90#64) ↦₆₄ (lsρ cliSessionVtSym)) ∗
          ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗ ((y.fut + 0xa0#64) ↦₆₄ (lsρ cliIdentityVtSym)) ∗
          ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗ ((y.fut + 0xb0#64) ↦₆₄ (lsρ cliPreKeyVtSym)) ∗
          ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗ ((y.fut + 0xd0#64) ↦₆₄ (lsρ cliKyberPreKeyVtSym))) ∗
          coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) rngPtr) ∗
        memRegion (y.fut + 0xe0#64) 368 ∗ memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        (memRegion (y.fut + 0x2c8#64) 16 ∗ memRegion (y.fut + 0x2d8#64) 184) ∗
        memRegion (y.fut + 0x390#64) 1 ∗ memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗ memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗ memRegion (y.fut + 0x4f2#64) 1 ∗
        coroPostP2UnusedAt y.fut) ∗
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
          (dpClosSubStack B - stageP4CallStack
            (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)
            (cliPollPkKitPlaced A.repAlloc y.g.F pid σ)
            (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A.repAlloc y.g.F pid σ)
          (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗
      ((sp ↦₆₄ 0#64) ∗ genP3S5SpillRem sp ∗ memRegion (sp + 0x930#64) 48 ∗
        ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
        ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗ spLowGapsAt sp ∗
        ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
        ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
        memRegion (sp + 0xbc#64) 4 ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        memRegion (sp + 0xd8#64) 376 ∗ memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x264#64) 12 ∗
        ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp + 0x278#64) ↦₆₄ ptCap) ∗
        ((sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 16 ∗
        memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
        memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ sp2b0GapsAt sp ∗
        memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x394#64) 12 ∗
        ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0x3a8#64) 4 ∗
        ((sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (sp + 0x3ad#64) 27 ∗
        ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x3e0#64) 48 ∗
        memRegion (sp + 0x410#64) 296 ∗ memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by
      sep_frame)) ?_
  rw [hcopy_join, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  have hcoro_fold :
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        memRegion (y.fut + 0xe0#64) 368 ∗ memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        memRegion (y.fut + 0x2c8#64) 200 ∗ memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗ memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗ memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗ coroPostP2UnusedAt y.fut) ⊢
      dpFutDoneAt y.fut := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) ?_
    rw [sepConj_assoc (memRegion (y.fut + 0x2a0#64) 8) (memRegion (y.fut + 0x2a8#64) 4)]
    exact hcoro
  have hstack_fold := Entails.trans (sepConj_mono_left hsp0) hstack
  exact Entails.trans
    (sepConj_mono hout (sepConj_mono hstores (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hcoro_fold (sepConj_mono_right hstack_fold))))))))))
    (Entails.of_eq (by dsimp only [lsLogOff]; sep_frame))

set_option maxHeartbeats 800000 in
theorem p4_finish_dpPollPost_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s' sf : State) (evs : List AllocEvent)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (Pf outAt preKeyMsgRem coinsPost R : SepProp)
    (opkId? : Option (BitVec 32)) (msgVer pid kpkId spkId : BitVec 32)
    (pt : List (BitVec 8))
    (ans : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (sess1 oneTime1 : DirGhost) (id1 : IdGhost) (kyber1 : KyberGhost)
    (g' : StoresGhost)
    (hevs : DecPkEnv y.g evs)
    (hs'_sp0 : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout_ent : outAt ⊢ decResAt A.repAlloc y.out ans ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sess1)
    (hsigned : g'.signed = StoresGhost.opened.signed)
    (honeTime : g'.oneTime = oneTime1)
    (hid : g'.identity = id1)
    (hkyber : g'.kyber = kyber1)
    (hpub : g'.pub = StoresGhost.opened.pub)
    (hpost_f : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs y.st)
      (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F pid (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B))
      s0 s' sf y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut opkId?) outAt kpkId spkId pt
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey sess1 id1 oneTime1 kyber1)
    (hsteps0f : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf)
    (htr_sf : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' ans s0.trace sf.trace)
    (hm_f : sf.mem ⊨
      (Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y (s0.sp - 0xcd0#64) rngPtr whisperMsgPtr whisperG
        msgVer pid kpkId spkId preKeyMsgRem coinsPost) ∗
      ((memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
        memRegion y.cx 32) ∗ R)) :
    sf.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗
      R := by
  let sp := s0.sp - 0xcd0#64
  have hexit := stageP4PathCExitAt_entails_exit_placed A lim (M.stepEvents evs y.st) B y s0 s' sf
    rngPtr 8#64 whisperMsgPtr ptCap ptPtr whisperG outAt preKeyMsgRem coinsPost opkId? msgVer
    pid kpkId spkId pt ans sess1 oneTime1 id1 kyber1 g' hs'_sp0 hsp_sub hout_ent hmsg_fold
    hsess hid honeTime hsigned hkyber hpub
  dsimp only at hexit
  have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f)) hm_f
  have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
  have hm_f3 : sf.mem ⊨
      (decResAt A.repAlloc y.out ans ∗
        storesAt A.repAlloc y.g.stores g' ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim (M.stepEvents evs y.st) sf ∗
        (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
        dpFutDoneAt y.fut ∗
        memRegion y.cx 32 ∗
        memRegion sp 3280 ∗
        stackAt sp (dpClosSubStack B) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
    Arm64.Satisfies.mono (by sep_frame) hm_f2
  have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
    s0 sf evs g' ans (LsTokenInit ∗ coinsPost ∗ anyHeap) hevs
    (hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518) hsteps0f htr_sf hout
  exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3

set_option maxHeartbeats 1200000 in
theorem closure_pathC_p4_cont_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hP4 : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (evs_pre : List AllocEvent)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hs_old : Slots.scopeIn ⟨some s_old⟩)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r))
    (hcur : r.currentSession = some s_old)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (recG G₁ G' : SessionGhost)
    (rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (pt : List (BitVec 8))
    (s0 s2 s' : State)
    (hFits4 :
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
      let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
      let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
      let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      FitsEnv M lim (M.stepEvents evs_pre y.st)
        (StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (E2E.Record.encSession (Over.clearPending s_old))))
    (hEnv4 :
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
      let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
      let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
      let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      ∀ evs4,
        StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber m.opkId y.g.peer.val
          y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey G' ses'
          (E2E.Record.encSession (Over.clearPending s_old)) evs4 →
        DecPkEnv y.g (evs_pre ++ evs4))
    (hpm_eq : y.g.msg = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys y.g.F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
      (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hex : SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk))
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hfiles2 : s2.fs.files = y.g.F)
    (htr2 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hver : (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s2 s')
    (hpc' : s'.pc = dpPollEntryPlaced + 0x34dc#64)
    (hrun' : s'.status = .Running)
    (hs'_sp : s'.sp = s2.sp)
    (htr' : s'.trace = s0.trace)
    (hvregs' : calleeSavedVRegs s' = calleeSavedVRegs s0)
    (hx19' : s'.readReg64 .x19 = y.fut)
    (hx24' : s'.readReg64 .x24 = s2.sp + 0x370#64)
    (hx25' : s'.readReg64 .x25 = s2.sp + 0x210#64)
    (hx26' : s'.readReg64 .x26 = y.out)
    (hx27' : s'.readReg64 .x27 = y.cx)
    (hx28' : s'.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hro' : StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s'
        y.fut y.out 8#64 prevCap prevPtr ptCap ptPtr
        (E2E.Record.encSession (Over.clearPending s_old)) pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins)) ∗
      Over.overScratch s2.sp) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
    let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    SepWPp prog (s0.readReg64 .x30) s' (P_s' ∗ F_p3)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let st_pre := M.stepEvents evs_pre y.st
  let A_s : RustAlloc := A.atState lim st_pre s'
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
  let ops : Over.StorePrev1Ops prev1Kit := cliPollStorePrev1OpsPlaced
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
  let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
  let enc := E2E.Record.encSession (Over.clearPending s_old)
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
  dsimp only at hFits4 hEnv4
  generalize hst'_eq :
    (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 = st' at hent_s'
  generalize hcoins_eq :
    Coins.coinsAfterPlaced y.g.coinsP y.g.coins
      (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins) = coinsPost at hent_s'
  let ses' : Session (List (BitVec 8)) :=
    { pathAInitSession ⟨W.C, W.Q⟩ meE k m dk with
      state := st', pendingPreKey := none, pendingKyberPreKey := none }
  rw [hst'_eq] at hFits4 hEnv4
  have hok_pair : genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 =
      (.ok pt, st') := Prod.ext hok hst'_eq
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := sp_frame_sub_add s0.sp
  have hf' : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed hh hsteps2' (htr'.trans htr2.symm)).trans hfiles2
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp4_64 : stageP4CallStack prev1Kit ikit pkKit kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans
      (stageP4Prev1CallStack_le_subStack_placed A.repAlloc y.g.F y.g.peer pid m.kpkId m.spkId
        y.g.msg.baseKey B)
      hsub64
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPathC_entails_p4_placed A lim st_pre B y s0 s2 s' rngPtr 8#64 prevCap
    prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem coinsPost m.opkId
    (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId enc pt G' st'
    hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hp5f : overGenP3S5PostFrame_placed A.repAlloc = overGenP3S5PostFrame_placed A_s := rfl
  have hk1 : kit.storeAt = (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ).storeAt := rfl
  have hk2 : ikit.identityAt = (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt := rfl
  have hk3 : pkKit.storeAt = (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt := rfl
  have hk4 : spkKit.storeAt = (cliPollSpkKitPlaced A_s y.g.F m.spkId σ).storeAt := rfl
  have hk5 : kpkKit.storeAt =
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt := rfl
  have hk6 : dirAt A.repAlloc = dirAt A_s := rfl
  have hm1' : s'.mem ⊨
      (Over.stageP3DispatchOkMidPrev1Placed A_s s0 s2 y.fut y.out 8#64
          prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
        overGenP3S5PostFrame_placed A_s sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
          coinsPost ∗
        Over.overScratch s2.sp) ∗
      (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced A_s y.g.F m.spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) ∗ R' := by
    unfold stageP3DispatchOkMidPrev1At_placed at hm1
    rw [hp5f, hk1, hk2, hk3, hk4, hk5, hk6] at hm1
    simpa only [hs2_sp, sepConj_assoc] using hm1
  have hp4_pre_eq :
      Over.stageP4Prev1PrePlaced 0#64
        (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ)
        s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' =
      stageP4Prev1PrePlaced A lim st_pre prev1Kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' := by
    unfold Over.stageP4Prev1PrePlaced Over.stageP4Prev1RawPrePlaced Over.stageP4Prev1SharedPlaced
      stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced stageP4Prev1SharedPlaced
    have hpa : protocolAddressAt A_s = protocolAddressAt A.repAlloc := rfl
    have hpv : prevVecAt A_s = prevVecAt A.repAlloc := rfl
    have hss : sessionStateAt A_s = sessionStateAt A.repAlloc := rfl
    have hlv : A_s.live = A.live := rfl
    have hs1 : (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).ss_vt = prev1Kit.ss_vt := rfl
    have hs2 : (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).id_vt = ikit.id_vt := rfl
    have hs3 : (cliPollPkKitPlaced A_s y.g.F pid σ).pk_vt = pkKit.pk_vt := rfl
    have hs4 : (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).kpk_vt =
        kpkKit.kpk_vt := rfl
    have hc : stageP4CallStack
        (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) =
      stageP4CallStack prev1Kit ikit pkKit kpkKit := rfl
    have hst1 : (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).storeAt = prev1Kit.storeAt := rfl
    have hst2 : (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt = ikit.identityAt := rfl
    have hst3 : (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt = pkKit.storeAt := rfl
    have hst4 : (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt =
        kpkKit.storeAt := rfl
    rw [hpa, hpv, hss, hlv, hs1, hs2, hs3, hs4, hc, hst1, hst2, hst3, hst4,
      RustCliAllocBudget.atState_pool]
  have hp4_rem_eq :
      overPathAP4RemAtPlaced A_s B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost =
      overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem
        coinsPost := rfl
  have hm2 : s'.mem ⊨
      stageP4Prev1PrePlaced A lim st_pre prev1Kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' ∗
      (overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost ∗
        R') := by
    rw [← sepConj_assoc] at hm1' ⊢
    rw [← hp4_pre_eq, ← hp4_rem_eq]
    exact Arm64.Satisfies.mono (sepConj_mono_left hmid) hm1'
  have hm_sess : s'.mem ⊨ sessionStateAt A.repAlloc (y.fut + 0xf8#64) G' st' ∗ anyHeap := by
    refine Arm64.Satisfies.mono ?_ hm2
    unfold stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced
    have hcomm : ∀ A1 A2 S A3 A4 : SepProp,
        (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 ⊢ S ∗ anyHeap := fun A1 A2 S A3 A4 =>
      Entails.trans (Entails.of_eq (by ac_rfl : (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 = S ∗ (A1 ∗ A2 ∗ A3 ∗ A4)))
        (sepConj_mono_right (entails_anyHeap _))
    exact hcomm _ _ _ _ _
  have hex0 : SessionExtraRel G'
      { pathAInitSession ⟨W.C, W.Q⟩ meE k m dk with
        state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
        pendingPreKey := none
        pendingKyberPreKey := none } := by
    rw [hst'_eq]; exact hex'
  have hm_sess0 : s'.mem ⊨ sessionStateAt A.repAlloc (y.fut + 0xf8#64) G'
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 ∗ anyHeap := by
    rw [hst'_eq]; exact hm_sess
  have hrecOk : ops.RecPrev1Ok G' ses' enc := by
    have hr := pathC_recPrev1Ok_of_tryDecrypt_placed (A := A.repAlloc) (σ := σ)
      hs_old hdecOk hver hok hex0 hm_sess0
    dsimp only at hr
    rw [hst'_eq] at hr
    exact hr
  have hwp4 := hP4 mmpl gh W B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey st_pre hh
    s0 s'
    y.fut y.cx y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
    prevCap prevPtr ptCap ptPtr 8#64
    m.opkId m.kpkId m.spkId 0#8 pt enc
    y.g.msg.identityKey y.g.msg.baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber
    G' ses'
    hFits4 hex' hrecOk rfl rfl
    (cliPollKpk_markOk_of_pmOfE (A := A.repAlloc) 0#64 y.g.F m i σ hpm_eq)
    (cliPollPk_removeIdOk_of_pmOfE (A := A.repAlloc) 0#64 y.g.F m i σ hpm_eq)
    hpt_le hpt_lt hpt_ne hp4_64
    (cliPollStageP4Prev1_fsAt_placed A.repAlloc hh y.g.F y.g.peer pid m.kpkId m.spkId
      y.g.msg.baseKey σ hf')
    hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  have hpre_id : y.g.msg.preKeyId = m.opkId := hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).1
  have hspk_id : y.g.msg.signedPreKeyId = m.spkId :=
    hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).2.1
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hro_f, hBr⟩⟩ |
    ⟨_, _, _, hpan_false⟩ |
    ⟨_, hoom⟩
  · rcases hBr with
      ⟨c, evs4, hevs4, _hsave, hmark, _hrem, _hstore, htr_f, hpost_f⟩ |
      ⟨_evs4, _hevs4, hsave, _, _⟩ |
      ⟨c, e, evs4, hevs4, _hsave, hmark, htr_f, hpost_f⟩ |
      ⟨opkId, _c, e, _evs4, hopk, _hevs4, _hsave, _hmark, hrem, _, _⟩ |
      ⟨_c, _evs4, _hevs4, _hsave, _hmark, _hrem, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have hevs_exit : StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv
          pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          m.opkId y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey
          G' ses' enc evs4 := by
        cases hop : m.opkId <;>
          simp only [hop, StageP4Prev1ExitEnv, StageP4Prev1NoneExitEnv,
            StageP4Prev1StoreBranchEnv] at hevs4 ⊢ <;>
          exact Or.inl hevs4
      have hevs_tot : DecPkEnv y.g (evs_pre ++ evs4) := hEnv4 evs4 hevs_exit
      have hpost_f' : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs4) y.st)
          prev1Kit ikit pkKit kpkKit s0 s' sf
          y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
          (vecResultAt A.repAlloc y.out (.ok pt)) m.kpkId m.spkId pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          (ops.storeUpdatePrev1 StoresGhost.opened.sessions y.g.peer.val G' ses' enc (.ok ()))
          (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
          (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ())) := by
        rw [M.stepEvents_append evs_pre evs4 y.st]
        revert hevs4 _hrem htr_f hpost_f
        cases m.opkId <;> intro _ _ _ hp <;> exact hp
      have htr_sf : sf.trace = s0.trace := by
        have h1 : ikit.saveEvs y.g.peer.val y.g.msg.identityKey (.ok c) = [] := rfl
        have h2 : kpkKit.markEvs m.kpkId m.spkId y.g.msg.baseKey (.ok ()) = [] := rfl
        have h4 : ops.storeEvsPrev1 y.g.peer.val G' ses' enc (.ok ()) = [] := rfl
        revert hevs4 _hrem htr_f hpost_f
        cases m.opkId with
        | none =>
          intro _ _ htr_f _
          dsimp only at htr_f
          rw [h1, h2, h4, List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, htr'] at htr_f
          exact htr_f
        | some opkId =>
          intro _ _ htr_f _
          have h3 : pkKit.removeEvs opkId (.ok ()) = [] := rfl
          dsimp only at htr_f
          rw [h1, h2, h3, h4, List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, htr'] at htr_f
          exact htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      let kyber' := (kpkMarkOf cliIo.rd y.g.F StoresGhost.opened.kyber
        m.kpkId m.spkId y.g.msg.baseKey).2
      have hmark_eq : StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
          y.g.msg.signedPreKeyId y.g.msg.baseKey = (.ok (), kyber') := by
        rw [hspk_id]
        exact cliKpk_markRel_ok_to_mark (A := A.repAlloc) (b := 0#64)
          (s1 := σ.kpkGetShim) (s2 := σ.kpkGetPoll) (s3 := σ.kpkMarkShim) (s4 := σ.kpkMarkPoll)
          hmark
      obtain ⟨hDec, hWr⟩ :=
        decPkDefD2c_pathC_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hfPeer hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hok_pair
          hmark_eq
      let oneTime' := match y.g.msg.preKeyId with
        | none => StoresGhost.opened.oneTime
        | some j => (Cli.removePreKey cliIo.rd y.g.F StoresGhost.opened.oneTime j).2
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          kyber := kyber'
          oneTime := oneTime'
          sessions := StoresGhost.opened.sessions.put (Cli.addressText y.g.peer.val)
            (Over.encodeRecordPrev1 ses' enc) }
      have hot_eq : g'.oneTime =
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ())) := by
        dsimp only [g', oneTime', pkKit, cliPollPkKitPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
          cliPreKeyStoreSpec]
        rw [hpre_id]
      exact p4_finish_dpPollPost_placed A lim DecPkEnv B S hh stk' hneed hstk63 y s0 s' sf
        (evs_pre ++ evs4) rngPtr whisperMsgPtr ptCap ptPtr whisperG Pf
        (vecResultAt A.repAlloc y.out (.ok pt)) preKeyMsgRem coinsPost R
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.ok pt)
        (ops.storeUpdatePrev1 StoresGhost.opened.sessions y.g.peer.val G' ses' enc (.ok ()))
        (match m.opkId with
         | none => StoresGhost.opened.oneTime
         | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ()))
        g' hevs_tot hs'_sp0 hsp_sub (decResultAt_ok_entails_decResAt_anyHeap A.repAlloc y.out pt)
        hmsg_fold rfl rfl hot_eq rfl rfl rfl hpost_f' hsteps0f htr_sf
        (slotOutTr_d2c_of_accept hS hDec hWr) hm_f
    · exact False.elim (cliId_saveRel_not_err (A := A.repAlloc) (b := 0#64)
        (F0 := y.g.F) (peer := y.g.peer) (σ := σ) hsave)
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have hevs_exit : StageP4Prev1ExitEnv prev1Kit envs.opsEnv ikit envs.ikitEnv
          pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          m.opkId y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey
          G' ses' enc evs4 := by
        cases m.opkId with
        | none => exact Or.inr (Or.inl hevs4)
        | some _ => exact Or.inr (Or.inr (Or.inl hevs4))
      have hevs_tot : DecPkEnv y.g (evs_pre ++ evs4) := hEnv4 evs4 hevs_exit
      have hpost_f' : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs4) y.st)
          prev1Kit ikit pkKit kpkKit s0 s' sf
          y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
          (speErrAt kpkKit.markErr y.out e) m.kpkId m.spkId pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          StoresGhost.opened.sessions
          (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
          StoresGhost.opened.oneTime
          (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e)) := by
        rw [M.stepEvents_append evs_pre evs4 y.st]; exact hpost_f
      have htr_sf : sf.trace = s0.trace := by
        have h1 : ikit.saveEvs y.g.peer.val y.g.msg.identityKey (.ok c) = [] := rfl
        have h2 : kpkKit.markEvs m.kpkId m.spkId y.g.msg.baseKey (.error e) = [] := rfl
        rw [h1, h2, List.append_nil, List.append_nil, htr'] at htr_f
        exact htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      have hmark_err :
          (StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
            y.g.msg.signedPreKeyId y.g.msg.baseKey).1 = .error () := by
        rw [hspk_id]
        exact cliKpk_markRel_error_to_mark (A := A.repAlloc) (b := 0#64)
          (s1 := σ.kpkGetShim) (s2 := σ.kpkGetPoll) (s3 := σ.kpkMarkShim) (s4 := σ.kpkMarkPoll)
          hmark
      have hDec := decPkDefD2c_pathC_mark_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg
        y.g.coins hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hok_pair
        hmark_err
      let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val
            y.g.msg.identityKey (.ok c)
          kyber := kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e) }
      exact p4_finish_dpPollPost_placed A lim DecPkEnv B S hh stk' hneed hstk63 y s0 s' sf
        (evs_pre ++ evs4) rngPtr whisperMsgPtr ptCap ptPtr whisperG Pf
        (speErrAt kpkKit.markErr y.out e) preKeyMsgRem coinsPost R
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.error err)
        StoresGhost.opened.sessions StoresGhost.opened.oneTime
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e))
        g' hevs_tot hs'_sp0 hsp_sub
        (cliPollKpk_markErr_entails_decResAt_anyHeap A.repAlloc 0#64 y.g.F m.kpkId m.spkId
          y.g.msg.baseKey σ y.out e err)
        hmsg_fold rfl rfl rfl rfl rfl rfl hpost_f' hsteps0f htr_sf
        (slotOutTr_d2c_of_reject g' hS nofun nofun hDec) hm_f
    · exact False.elim (cliPk_removeRel_not_err_of_pkStoreKeys (A := A.repAlloc) (b := 0#64)
        (pid := pid) (σ := σ) (e := e) hk hopk hrem)
    · exact False.elim (by cases hstore)
  · exact hpan_false.elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
