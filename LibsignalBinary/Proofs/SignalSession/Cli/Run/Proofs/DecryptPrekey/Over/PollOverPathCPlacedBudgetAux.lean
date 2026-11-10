/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCErrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCli
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Placed CLI Poll Overwrite-Path (`Path C`) Stage P2/P3/P4 Helpers

Provides `RunHooksPlaced` callee and filesystem bridges, 3-state Stage P3 spatial bundles and error
exit folds, budget-threaded `Prev1` Stage P4 allocation envelopes and interfaces
(`StageP4Prev1VRegsPlacedStmt`), and the Path C Stage P2 interface (`StageP2OverQpanCliPlacedStmt`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 hiding
  ChainClone3OkPlaced SenderChainClone3OkPlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over hiding
  stageP4Prev1SharedPlaced stageP4Prev1PrePlaced stageP4Prev1ExitAtPlaced
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
  cliChainClone3_placed_ok cliSenderChainClone3_placed_ok cliDropSessionStructure4_placed_ok_at
  cliFsAt_of_files_eq_placed cliFiles_eq_of_trace_eq_placed
  cliPollStageP4Prev1_fsAt_placed storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c
  overGenP3S5PostFrame_placed
  overGenP3Pre_placed overStageP3ErrPostPrevEmpty_placed overPathAP4RemAtPlaced
  overExit_entails_dpPollPost_placed stageP3MidPathC_entails_p4_placed
  stageP4PathCExit_entails_exit_placed stageP3ErrPathC_entails_exit_placed
  stageP3_exit_pathC_to_pollPost_placed
  StageP2OverErrPlaced StageP2OverQpanCliPlacedStmt
  StageP4Prev1RawBranchPlaced StageP4Prev1BranchPlaced StageP4Prev1VRegsPlacedStmt
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv retagPreKeyStore
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  retagSessionStore
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv SaveStepEnv retagIdentityStore
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv retagKyberPreKeyStore
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (
  drop_session_structure4_placed_ok_at
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed overGenP3S5PostFrame_placed overPathAP4RemAtPlaced
  overExit_entails_dpPollPost_placed
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

abbrev RunHooksPlaced :=
  @LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced

/-! ## 1. Callee, Filesystem, and Opened-Stores Bridges under `RunHooksPlaced` -/

private theorem hookSat_sessionShimBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsRustNoAllocShimSym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    HookSat H CryptoVerification.lsRustNoAllocShimSym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem hookSat_sessionMemcpyRegionBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec :=
  ProofLib.HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩

theorem cliChainClone3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    ChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

theorem cliSenderChainClone3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    SenderChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (hookSat_sessionShimBudget_of_codec hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

theorem cliDropSessionStructure4_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at hh.codecHooks.dealloc hi

theorem cliFsAt_of_files_eq_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {envOk : FsFiles → Prop} {Q : Prop} {F0 : FsFiles} {s : State}
    (hh : RunHooksPlaced A lim ext)
    (hQ : Q) (henv : envOk F0) (hf : s.fs.files = F0) :
    FsAt envOk Q prog s :=
  .inr ⟨hQ, hh.fs prog i, hf ▸ henv⟩

theorem cliFiles_eq_of_trace_eq_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} [IsLsBlockProg prog i ext]
    {s0 sf : State} (hh : RunHooksPlaced A lim ext)
    (hsteps : Steps prog s0 sf) (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (hh.fs prog i).files_eq hsteps (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil

theorem cliPollStageP4Prev1_fsAt_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (A_r : RustAlloc)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
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
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s :=
  .inr ⟨⟨cliPollSessPrev1Placed_quiet F0 peer σ,
         cliPollIdPlaced_quiet F0 peer σ,
         cliPollPkPlaced_quiet F0 pid σ,
         cliPollKpkPlaced_quiet F0 kpkId spkId kbk σ⟩,
        hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518, ⟨hf, hf, hf, hf⟩⟩

theorem storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c [LibsignalPlacement]
    (A : RustAlloc) {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    (σ : DpKitStk) (ptr : BitVec 64)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hfPeer : Slots.FilesOkPeer Scope F0 peer.val)
    (hd : DecPkOkD2c W Scope F0 peer.val me.val pm)
    (pid sid kid : BitVec 32) (kbk : PublicKey) :
    storesAt A ptr StoresGhost.opened ⊢
      cliPollStoresKitsAtPlaced A F0 Slots.scopeKit peer pid sid kid kbk σ ptr
        StoresGhost.opened :=
  storesAt_opened_entails_cliPollStoresKitsAt_d2c_ext (A := A) 0#64 σ ptr hsub hfPeer hd
    pid sid kid kbk

/-! ## 2. 3-State Stage P3 Spatial Bundles & Path C Error / `verNe` Exit Folds -/

/-- 3-state `stageP3DispatchOkMidPrev1Placed`, evaluating `A.pool` at the post-Step5 state `s'`
while indexing stack slots at `s.sp`. -/
def stageP3DispatchOkMidPrev1At_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s' : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (enc pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  Over.stageP3DispatchOkMidPrev1Placed (A.atState lim st_b s') s0 s coroPtr outPtr initErrsPtr
    prevCap prevPtr ptCap ptPtr enc pt b_2c0 G₂ st₂

/-- 3-state `overStageP3ErrPostPrevEmpty_placed`, evaluating `A.pool` at the exit state `sf`
while indexing stack slots at `s.sp`. -/
def overStageP3ErrPostPrevEmptyAt_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s sf : State)
    (coroPtr outPtr : BitVec 64) (e : SignalProtocolError) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.overStageP3ErrPostPrevEmpty_placed
    (A.atState lim st_b sf) s0 s coroPtr outPtr e

set_option maxHeartbeats 800000 in
theorem stageP3ErrPathC_entails_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s2 sf : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer kpkId spkId : BitVec 32)
    (e : SignalProtocolError) (err : ApiError AddrVal Unit)
    (g1 : StoresGhost)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) :
    let sp := s0.sp - 0xcd0#64
    (((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (sp + 0x3e0#64) 344 ∗
      overStageP3ErrPostPrevEmptyAt_placed A lim st_b s0 s2 sf y.fut y.out e ∗
      overGenP3S5PostFrame_placed A.repAlloc sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost ∗
      Over.overScratch sp ∗
      anyHeap) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
        ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    storesAt A.repAlloc y.g.stores g1 ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
    decResAt A.repAlloc y.out (.error err) ∗
      storesAt A.repAlloc y.g.stores g1 ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim st_b sf ∗
      (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion sp 3280 := by
  dsimp only [overGenP3S5PostFrame_placed]
  let sp := s0.sp - 0xcd0#64
  let A_f : RustAlloc := A.atState lim st_b sf
  rw [overScratch_eq_sp538_spHighGaps sp]
  unfold overStageP3ErrPostPrevEmptyAt_placed
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.overStageP3ErrPostPrevEmpty_placed
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.overGenP3S5PostFrame_placed
    stageP3CoroFrameAt stageP3OverStackFrameAt
  rw [hs2_sp]
  have hrr : recordResultAt A_f = recordResultAt A.repAlloc := rfl
  rw [hrr, RustCliAllocBudget.atState_pool]
  have hstk1 : memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      stackAt sp growOneSpeStack = stackAt sp rootStack :=
    (stackAt_root_sub_eq sp (by decide)).symm
  have hstk2 : memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      stackAt sp rootStack = stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub).symm
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
      stackAt sp (dpClosSubStack B) := by
    rw [hstk1, hstk2]
  have hdec := recordResultAt_err_entails_decResAt A.repAlloc y.out
    (SessionState.recordError .preKey e) err
  have h298 := coroOpkIdAtP4_entails_memRegion8 y.fut opkId?
  have h2a0 := coro_2a0_2a8_entails y.fut (kpkId ++ 1#32) spkId
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstack := stageP3Err_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      recordResultAt A.repAlloc y.out (.error (SessionState.recordError .preKey e)) ∗
      storesAt A.repAlloc y.g.stores g1 ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim st_b sf ∗
      (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        memRegion (y.fut + 0xe0#64) 368 ∗
        memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗
        coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        (memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12) ∗
        ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        (memRegion (y.fut + 0x2c8#64) 16 ∗ memRegion (y.fut + 0x2d8#64) 184) ∗
        memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗
        coroPostP2UnusedAt y.fut) ∗
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack)) ∗
      ((sp ↦₆₄ 0#64) ∗
        genP3S5SpillRem sp ∗
        memRegion (sp + 0x930#64) 48 ∗
        ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
        ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
        ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
        spLowGapsAt sp ∗
        ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
        ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
        ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
        ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
        memRegion (sp + 0xbc#64) 4 ∗
        ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
        ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        memRegion (sp + 0xd8#64) 376 ∗
        memRegion (sp + 0x250#64) 20 ∗
        memRegion (sp + 0x264#64) 12 ∗
        memRegion (sp + 0x270#64) 48 ∗
        memRegion (sp + 0x2a0#64) 16 ∗
        memRegion (sp + 0x2b0#64) 192 ∗
        memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x394#64) 12 ∗
        ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
        memRegion (sp + 0x3a8#64) 4 ∗
        ((sp + 0x3ac#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x3ad#64) 27 ∗
        (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((sp + 0x3d8#64) ↦₆₄ errsLen)) ∗
        memRegion (sp + 0x3e0#64) 344 ∗
        memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗
        spHighGapsAt sp ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by sep_frame)) ?_
  rw [← coro_2ac_20_eq_8_12 y.fut, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  refine sepConj_mono hdec (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono ?_ (sepConj_mono_right ?_)))))))))
  · refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) ?_
    rw [sepConj_assoc (memRegion (y.fut + 0x2a0#64) 8) (memRegion (y.fut + 0x2a8#64) 4)]
    exact hcoro
  · exact Entails.trans (sepConj_mono_left hsp0) hstack

set_option maxHeartbeats 800000 in
theorem stageP3_exit_pathC_to_pollPost_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s2 sf : State) (evs : List AllocEvent)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost P_f R : SepProp)
    (opkId? : Option (BitVec 32))
    (kpkId spkId : BitVec 32)
    (e : SignalProtocolError)
    (hevs : DecPkEnv y.g evs)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hdec : decPkDefD2c X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
      some none)
    (hent : P_f ⊢
      ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (s2.sp + 0x3e0#64) 344 ∗
      overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs y.st) s0 s2 sf y.fut y.out e ∗
      overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        coinsPost ∗
      Over.overScratch s2.sp ∗
      anyHeap)
    (hsf_sp : sf.sp = s2.sp + 0xcd0#64)
    (htr_f : sf.trace = s0.trace)
    (hcs_f : ClosureCalleeSaved s0 sf)
    (hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut opkId?)
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    (Steps prog s0 sf → (sf.mem ⊨ (P_f ∗ F_p3) ∗ (Fr_tail ∗ R)) →
      (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .decryptionFailed)
  have hsf_sp0 : sf.sp = s0.sp := by rw [hsf_sp, hs2_sp, sp_frame_sub_add]
  have hcs_full : CalleeSavedPreserved s0 sf :=
    closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
  refine ⟨?_, hsf_sp0, hcs_full⟩
  intro hsteps0f hm_f
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm_f
  rw [hs2_sp] at hm1
  have hexit := stageP3ErrPathC_entails_exit_placed A lim (M.stepEvents evs y.st) B y s0 s2 sf
    rngPtr whisperMsgPtr whisperG preKeyMsgRem coinsPost opkId?
    (y.g.msg.message.messageVersion.zeroExtend 32) kpkId spkId e err
    StoresGhost.opened hs2_sp hsp_sub hmsg_fold
  dsimp only at hexit
  have hm2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm1
  have hm3 : sf.mem ⊨
      (decResAt A.repAlloc y.out (.error err) ∗
        storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
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
    Arm64.Satisfies.mono (by dsimp only [sp]; sep_frame) hm2
  have hout : slotOutTr
      (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      StoresGhost.opened (.error err) s0.trace sf.trace :=
    slotOutTr_d2c_of_reject StoresGhost.opened hS (err := err) nofun nofun hdec
  have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
    s0 sf evs StoresGhost.opened (.error err) (LsTokenInit ∗ coinsPost ∗ anyHeap) hevs
    (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518) hsteps0f htr_f hout
  exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm3

/-! ## 3. Budget-Threaded `Prev1` Stage P4 Envelopes, Spatial Bundles, and Interface -/

/-- Poll allocation envelope for a 1-element `previous_sessions` `store_session` operation. -/
structure StorePrev1BudgetEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) where
  storePrev1PollEnv :
    kit.StoreState → AddrVal → SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop

/-- `store_session` shim + poll + `Box` dealloc step envelope on `Prev1`. -/
def StorePrev1StepEnv {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (opsEnv : StorePrev1BudgetEnv kit) (sst0 : kit.StoreState)
    (rem : AddrVal) (G : SessionGhost) (ss : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.storeBoxSize)
    (SeqEnv (opsEnv.storePrev1PollEnv sst0 rem G ss enc)
      (· = rustDeallocEvents kit.storeBoxSize 8))

/-- `mark_kyber_pre_key_used` shim + poll + `Box` dealloc step envelope. -/
def MarkStepEnv {A : RustAlloc} {b : BitVec 64} (kpkKit : KyberPreKeyStoreSpec A b)
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit) (kst0 : kpkKit.KpkState)
    (id signedId : BitVec 32) (baseKey : PublicKey) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kpkKit.markBoxSize)
    (SeqEnv (kpkKitEnv.markPollEnv kst0 id signedId baseKey)
      (· = rustDeallocEvents kpkKit.markBoxSize 8))

/-- `remove_pre_key` shim + poll + `Box` dealloc step envelope. -/
def RemoveStepEnv {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b)
    (pkKitEnv : PreKeyStoreBudgetEnv pkKit) (pst0 : pkKit.PkState)
    (opkId : BitVec 32) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv pkKit.removeBoxSize)
    (SeqEnv (pkKitEnv.removePollEnv pst0 opkId)
      (· = rustDeallocEvents pkKit.removeBoxSize 8))

/-- Optional `remove_pre_key` step envelope (`none` emits `[]`). -/
def OptRemoveStepEnv {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b)
    (pkKitEnv : PreKeyStoreBudgetEnv pkKit) (pst0 : pkKit.PkState) :
    Option (BitVec 32) → List AllocEvent → Prop
  | none => (· = [])
  | some opkId => RemoveStepEnv pkKit pkKitEnv pst0 opkId

/-- Stage P4 `Prev1` `save_identity` error branch envelope (`SaveStepEnv` followed by drop cleanup). -/
def StageP4Prev1SaveErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (remoteIk : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk) FreeOnlyEvs

/-- Stage P4 `Prev1` `mark_kyber_pre_key_used` error branch envelope. -/
def StageP4Prev1MarkErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey) : List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey) FreeOnlyEvs)

/-- Stage P4 `Prev1` `remove_pre_key` error branch envelope (`opkId? = some opkId`). -/
def StageP4Prev1RemoveErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState) (pst0 : pkKit.PkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId opkId : BitVec 32) (baseKey : PublicKey) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (SeqEnv (RemoveStepEnv pkKit pkKitEnv pst0 opkId) FreeOnlyEvs))

/-- Stage P4 `Prev1` `store_session` branch envelope (`ok` and `storeErr`). -/
def StageP4Prev1StoreStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (opkId? : Option (BitVec 32))
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (SeqEnv (OptRemoveStepEnv pkKit pkKitEnv pst0 opkId?)
        (SeqEnv (StorePrev1StepEnv kit opsEnv sst0 rem G ss enc) FreeOnlyEvs)))

/-- Combined Stage P4 `Prev1` allocation envelope covering all 5 outcomes without existentials. -/
def StageP4Prev1Env {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (opkId? : Option (BitVec 32))
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  StageP4Prev1SaveErrEnv ikit ikitEnv ist0 rem remoteIk evs ∨
  StageP4Prev1MarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0 rem remoteIk
    kyberPreKeyId signedPreKeyId baseKey evs ∨
  (match opkId? with
   | none => False
   | some opkId =>
     StageP4Prev1RemoveErrEnv ikit ikitEnv kpkKit kpkKitEnv pkKit pkKitEnv
       ist0 kst0 pst0 rem remoteIk kyberPreKeyId signedPreKeyId opkId baseKey evs) ∨
  StageP4Prev1StoreStepEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
    sst0 ist0 pst0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey opkId? G ss enc evs

/-- 3-state `stageP4Prev1SharedPlaced` over `A.atState lim st s_pool`. -/
def stageP4Prev1SharedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (b : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey) : SepProp :=
  Over.stageP4Prev1SharedPlaced b
    (retagSessionStore (A' := A.atState lim st s_pool) kit)
    (retagIdentityStore (A' := A.atState lim st s_pool) ikit)
    (retagPreKeyStore (A' := A.atState lim st s_pool) pkKit)
    (retagKyberPreKeyStore (A' := A.atState lim st s_pool) kpkKit)
    s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey

/-- Budget-threaded `stageP4Prev1PrePlaced` at `dpPollEntryPlaced + 0x34dc#64`. -/
def stageP4Prev1PrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (b : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : SessionState (List (BitVec 8))) : SepProp :=
  Over.stageP4Prev1PrePlaced b
    (retagSessionStore (A' := A.atState lim st s) kit)
    (retagIdentityStore (A' := A.atState lim st s) ikit)
    (retagPreKeyStore (A' := A.atState lim st s) pkKit)
    (retagKyberPreKeyStore (A' := A.atState lim st s) kpkKit)
    s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 opkId?
    kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss

/-- 3-state `stageP4Prev1ExitAtPlaced`, evaluating `A.pool` at exit state `sf` while indexing
stack slots at `s.sp`. -/
def stageP4Prev1ExitAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (b : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s sf : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot outSlot : SepProp) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sstf : kit.StoreState) (istf : ikit.IdState)
    (pstf : pkKit.PkState) (kstf : kpkKit.KpkState) : SepProp :=
  Over.stageP4Prev1ExitAtPlaced b
    (retagSessionStore (A' := A.atState lim st sf) kit)
    (retagIdentityStore (A' := A.atState lim st sf) ikit)
    (retagPreKeyStore (A' := A.atState lim st sf) pkKit)
    (retagKyberPreKeyStore (A' := A.atState lim st sf) kpkKit)
    s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot outSlot
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf

/-- Budget-threaded `Prev1` Stage P4 outcome classification carrying `evs : List AllocEvent`. -/
inductive StageP4Prev1RawBranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (b : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc b) (ops : Over.StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp) (opkId? : Option (BitVec 32))
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt enc : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop where
  | ok (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4Prev1StoreStepEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey opkId? G ss enc
        evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : ops.storeRelPrev1 sst0 peer.val G ss enc (.ok ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        ops.storeEvsPrev1 peer.val G ss enc (.ok ()))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st_b) b kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | saveErr (evs : List AllocEvent)
      (hevs : StageP4Prev1SaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st_b) b kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)
  | markErr (c : IdentityChange) (e : kpkKit.MarkErr) (evs : List AllocEvent)
      (hevs : StageP4Prev1MarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0 peer.val remoteIk
        kyberPreKeyId signedPreKeyId baseKey evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st_b) b kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot (speErrAt kpkKit.markErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))
  | removeErr (opkId : BitVec 32) (c : IdentityChange) (e : pkKit.RemoveErr) (evs : List AllocEvent)
      (hopk : opkId? = some opkId)
      (hevs : StageP4Prev1RemoveErrEnv ikit ikitEnv kpkKit kpkKitEnv pkKit pkKitEnv
        ist0 kst0 pst0 peer.val remoteIk kyberPreKeyId signedPreKeyId opkId baseKey evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : pkKit.removeRel pst0 opkId (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        pkKit.removeEvs opkId (.error e))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st_b) b kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot (speErrAt pkKit.removeErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (pkKit.removeUpdate pst0 opkId (.error e))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | storeErr (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4Prev1StoreStepEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey opkId? G ss enc
        evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : ops.storeRelPrev1 sst0 peer.val G ss enc (.error ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        ops.storeEvsPrev1 peer.val G ss enc (.error ()))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st_b) b kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))

abbrev StageP4Prev1BranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (b : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc b) (ops : Over.StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt enc : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop :=
  StageP4Prev1RawBranchPlaced A lim st_b b kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
    kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?) opkId?
    kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf

/-- Bundle of the 4 placed CLI Stage P4 `Prev1` kit allocation envelopes (`storePrev1`, `identity`,
`preKey`, `kyberPreKey`). -/
structure CliStageP4Prev1Envs [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey) where
  opsEnv : StorePrev1BudgetEnv (cliPollSessPrev1KitPlaced A F0 peer (cliKitStk B))
  ikitEnv : IdentityStoreBudgetEnv (cliPollIdKitPlaced A F0 peer (cliKitStk B))
  pkKitEnv : PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 pid (cliKitStk B))
  kpkKitEnv : KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))

/-- Budget-threaded placed Stage P4 (`+0x34dc → s0.readReg64 .x30`) contract over 1-element
`previous_sessions` on `dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))`, eliminating `PanicOomProp`
(`onPanic := fun _ _ => False`). -/
def StageP4Prev1VRegsPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey) (st_b : M.σ),
    let σ := cliKitStk B
    let kit := cliPollSessPrev1KitPlaced A.repAlloc F0 peer σ
    let ops : Over.StorePrev1Ops kit := cliPollStorePrev1OpsPlaced
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    let envs := p4Envs B F0 peer pid kpkId spkId kbk
    RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      FitsEnv M lim st_b
        (StageP4Prev1Env kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv sst0 ist0 pst0 kst0 peer.val remoteIk
          kyberPreKeyId signedPreKeyId baseKey opkId? G ss enc) →
      SessionExtraRel G ss → ops.RecPrev1Ok G ss enc →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x34dc#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (stageP4Prev1PrePlaced A lim st_b 0#64 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevCap prevPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc
          peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4Prev1BranchPlaced A lim st_b 0#64 kit ops envs.opsEnv ikit envs.ikitEnv
            pkKit envs.pkKitEnv kpkKit envs.kpkKitEnv s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
            ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
            baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
        (fun _ _ => False)

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
    stageP4Prev1ExitAtPlaced A lim stf 0#64 prev1Kit ikit pkKit kpkKit s0 s' sf
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
  let A_f : RustAlloc := A.atState lim stf sf
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  change
    Over.stageP4Prev1ExitAtPlaced 0#64
      (cliPollSessPrev1KitPlaced A_f y.g.F y.g.peer σ)
      (cliPollIdKitPlaced A_f y.g.F y.g.peer σ)
      (cliPollPkKitPlaced A_f y.g.F pid σ)
      (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ)
      s0 s' y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64) ptCap ptPtr initErrsPtr
      (coroOpkIdAtP4 y.fut opkId?) outSlot kpkId spkId pt y.g.peer y.g.msg.identityKey
      y.g.msg.baseKey sstf istf pstf kstf ∗
    overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId
      preKeyMsgRem coinsPost ⊢ _
  unfold Over.stageP4Prev1ExitAtPlaced Over.stageP4Prev1SharedPlaced overPathAP4RemAtPlaced
  have hvt_s : (cliPollSessPrev1KitPlaced A_f y.g.F y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hvt_i : (cliPollIdKitPlaced A_f y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hvt_p : (cliPollPkKitPlaced A_f y.g.F pid σ).pk_vt =
      lsρ cliPreKeyVtSym := rfl
  have hvt_k : (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt =
      lsρ cliKyberPreKeyVtSym := rfl
  have hcall_eq :
      stageP4CallStack (cliPollSessPrev1KitPlaced A_f y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A_f y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_f y.g.F pid σ)
        (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ) =
      stageP4CallStack (cliPollSessKitPlaced A_f y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced A_f y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_f y.g.F pid σ)
        (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ) := rfl
  rw [hs'_sp, hvt_s, hvt_i, hvt_p, hvt_k, hcall_eq]
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKitPlaced A_f y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A_f y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A_f y.g.F pid σ)
          (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
      stackAt sp (stageP4CallStack
        (cliPollSessKitPlaced A_f y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced A_f y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_f y.g.F pid σ)
        (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ)) =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B
      (cliPollStageP4Stack_le_subStack A_f 0#64 y.g.F Slots.scopeKit y.g.peer
        pid kpkId spkId y.g.msg.baseKey B) hsp_sub).symm
  have hspk_eq :
      (cliPollSpkKitPlaced A.repAlloc y.g.F spkId σ).storeAt =
        (cliPollSpkKitPlaced A_f y.g.F spkId σ).storeAt := rfl
  have hdir_eq : dirAt A.repAlloc = dirAt A_f := rfl
  have hstores :
      (cliPollSessPrev1KitPlaced A_f y.g.F y.g.peer σ).storeAt (y.g.stores + 0xf0#64) sstf ∗
      (cliPollIdKitPlaced A_f y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
      (cliPollPkKitPlaced A_f y.g.F pid σ).storeAt (y.g.stores + 0xc8#64) pstf ∗
      (cliPollSpkKitPlaced A.repAlloc y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) kstf ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
      storesAt A.repAlloc y.g.stores g' := by
    rw [hspk_eq, hdir_eq, ← hsess, ← hid, ← hot, ← hspk, ← hkpk, ← hpub]
    exact cliPollPrev1StoresKitsAtPlaced_entails_storesAt (A := A_f) y.g.F y.g.peer pid spkId kpkId
      y.g.msg.baseKey σ y.g.stores g'
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
      ((cliPollSessPrev1KitPlaced A_f y.g.F y.g.peer σ).storeAt (y.g.stores + 0xf0#64) sstf ∗
        (cliPollIdKitPlaced A_f y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
        (cliPollPkKitPlaced A_f y.g.F pid σ).storeAt
          (y.g.stores + 0xc8#64) pstf ∗
        (cliPollSpkKitPlaced A.repAlloc y.g.F spkId σ).storeAt
          (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
        (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
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
            (cliPollSessKitPlaced A_f y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKitPlaced A_f y.g.F y.g.peer σ)
            (cliPollPkKitPlaced A_f y.g.F pid σ)
            (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKitPlaced A_f y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A_f y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A_f y.g.F pid σ)
          (cliPollKpkKitPlaced A_f y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗
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
      have hpa : protocolAddressAt A_f = protocolAddressAt A.repAlloc := rfl
      rw [hpa, RustCliAllocBudget.atState_pool]
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

/-! ## 4. Budget-Threaded Path C Stage P2 Interface (`StageP2OverQpanCliPlacedStmt`) -/

/-- Combined Path C Stage P2 (`+0x0868 → +0x1778` or early reject) allocation envelope. -/
def StageP2OverEnv
    (P2OverErrEnv P2OverOkEnv : DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (g : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  P2OverErrEnv g r evs ∨ P2OverOkEnv g r evs

/-- Budget-threaded Path C Stage P2 early-reject outcome carrying `evs : List AllocEvent`. -/
inductive StageP2OverErrPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (P2OverErrEnv : DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8)))
    (s0 s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop where
  | reject (err : ApiError AddrVal Unit) (evs : List AllocEvent)
      (hevs : P2OverErrEnv y.g r evs)
      (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
      (htr : sf.trace = s1.trace)
      (hmodel : decPkDefD2c X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
        some none)
      (hpost : Pf ⊢
        dpFutDoneAt y.fut ∗
        memRegion sp 3280 ∗
        decResAt A.repAlloc y.out (.error err) ∗
        storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim (M.stepEvents evs st_b) sf ∗
        stackAt sp (dpClosSubStack B) ∗
        anyHeap)

/-- Budget-threaded general-`Qpan` CPS Stage P2 (`+0x0868 → +0x1778`) statement for Path C
under `[LibsignalPlacement]`, eliminating `PanicOomProp`. -/
def StageP2OverQpanCliPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 →
    StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2OverErrPlaced A lim st_b P2OverErrEnv X W B S Scope y r s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey) (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan


/-! ## `LibsignalFrozen` Counterparts -/

def StageP2OverQpanCliFrozenPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → Slots.scopeIn r') →
    Slots.FilesOkPeer Scope y.g.F y.g.peer.val →
    Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 →
    CryptoVerification.LibsignalFrozen lsmpl s1.mem →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2OverErrPlaced A lim st_b P2OverErrEnv X W B S Scope y r s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey) (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = dpPollEntryPlaced + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      CryptoVerification.LibsignalFrozen lsmpl s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
