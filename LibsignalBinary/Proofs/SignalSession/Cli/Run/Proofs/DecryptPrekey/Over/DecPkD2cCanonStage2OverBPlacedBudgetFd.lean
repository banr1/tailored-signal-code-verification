/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverRegErrPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib
import ProofLib.SepLogic.WPp

/-!
# Fixed-`B` `DecPkOkD2c` and `regErr` Stage-P2 Over Lifts

Fixed-`B` `DecPkOkD2c` and `regId = .error ()` (`regErr`) Stage-P2 Over statements and
`LibsignalFrozen`-guarded lifts on `dpPollEntryPlaced + 0x0868#64`.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverBPlacedBudgetFd

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalFrozen LibsignalFullPlacement LibsignalPlacement lsProg_51 lsmpl lsρ withLsCl
)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.E2E (
  PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives acceptInput modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt signalMessageAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel coroOpkIdAtP4 p1LoadedRecordAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  clearPending stageP3Sub5ExtraPrePrev1
)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  CliGhostHooks StoresGhost cliGhostExterns cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym
  cliSessionVtSym cliSignedPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c pkStoreKeys pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (SessMatchesPm)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced
  cliPollPkKitPlaced cliPollSelfKitPlaced cliPollSpkKitPlaced
  decPkDefD2c_pathC_accept_none decPkDefD2c_pathC_lookup_err dpClosSubStack dpPollEntryPlaced
  dpPollProgPlaced pathAInitSession pathAInitState scope_of_loadRec_some
  stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt
)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer loadRec scopeIn scopeKit)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
  SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissGenPlacedProp PromoteOverGenPlacedWithEnvProp
)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget (InitialStateMemInvPlacedOkOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverPlacedBudgetFd (
  stageP2PathCOver_qpan_cli_archive_frozen_of_init75_and_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverRegErrPlacedBudgetFd (
  StageP2PathCOverQpanCliRegErrMemInvPlacedAtStmt
  stageP2PathCOver_qpan_cli_archive_regErr_placed_at_of_init75_and_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv StageP2OverErrPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
  cliPromoteMatchingMissGen_placed_ok cliPromoteOverGen_archive_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux (
  StageP2PathCOverQpanCliMemInvPlacedAtStmt
)

def StageP2OverQpanCliMemInvPlacedAtXBStmt (Φ : Memory → Prop) [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 →
    Φ s1.mem →
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
      LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2OverErrPlaced A lim st_b P2OverErrEnv X W B S Scope y r s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State) (evs_p2 : List AllocEvent)
      (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
      (kp : IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey) (recG : SessionGhost)
      (prevCap prevPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2OverOkEnv y.g r evs_p2 →
      prevCap ≠ 0#64 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok i →
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
      Φ s2.mem →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_b) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (encSession (clearPending s_old)) 0#8 ∗
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
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

theorem stageP2Over_qpan_cli_memInv_placed_at_B_of_pathC {Φ : Memory → Prop} [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets}
    (hPathC :
      StageP2PathCOverQpanCliMemInvPlacedAtStmt Φ A lim PromEnv X mmpl gh W B
        P2OverErrEnv P2OverOkEnv)
    (hPromMiss : PromoteMatchingMissGenPlacedProp A.repAlloc
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver :
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PromoteOverGenPlacedWithEnvProp M A lim PromEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliMemInvPlacedAtXBStmt Φ A lim X mmpl gh W B P2OverErrEnv P2OverOkEnv := by
  intro S DecPkEnv Scope y st_b r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hfits hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 herr hok
  have hh' : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs, hh.utf8, hh.memrchr,
      hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
  have hr_scope : scopeIn r := hsub r (scope_of_loadRec_some hfPeer hload)
  exact hPathC S Scope y st_b g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss (hPromOver hh') hh' hfits hcoins hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact decPkDefD2c_pathC_lookup_err
          X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact decPkDefD2c_pathC_lookup_err
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact decPkDefD2c_pathC_accept_none
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))
    hok

def StageP2OverQpanCliRegErrPlacedAtBStmt (Φ : Memory → Prop) [LibsignalPlacement]
    {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets)
    (P2OverErrEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S)),
    StoresGhost.opened.identity.regId cliIo.rd y.g.F = .error () →
    ∀ (st_b : M.σ)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    FitsEnv M lim st_b (P2OverErrEnv y.g r) →
    y.g.coins.length < 2 ^ 63 →
    DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    (∀ r', Scope r' → scopeIn r') →
    FilesOkPeer Scope y.g.F y.g.peer.val →
    loadRec Scope y.g.F y.g.peer.val = .ok (some r) →
    r.currentSession = some s_old →
    ¬ SessMatchesPm s_old y.g.msg →
    StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey = .ok true →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 →
    Φ s1.mem →
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
      LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2OverErrPlaced A lim st_b P2OverErrEnv X W B S Scope y r s0 s1 sf sp Pf →
      Q sf Pf) →
    SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

theorem stageP2Over_qpan_cli_regErr_placed_at_of_pathC {Φ : Memory → Prop} [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets}
    (hPathC :
      StageP2PathCOverQpanCliRegErrMemInvPlacedAtStmt Φ A lim PromEnv X mmpl gh W B
        P2OverErrEnv)
    (hPromMiss : PromoteMatchingMissGenPlacedProp A.repAlloc
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromOver :
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PromoteOverGenPlacedWithEnvProp M A lim PromEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliRegErrPlacedAtBStmt Φ A lim X mmpl gh W B P2OverErrEnv := by
  intro S DecPkEnv Scope y hRegErr st_b r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hfits hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 herr
  have hh' : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs, hh.utf8, hh.memrchr,
      hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
  have hr_scope : scopeIn r := hsub r (scope_of_loadRec_some hfPeer hload)
  exact hPathC S Scope y hRegErr st_b g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hPromMiss (hPromOver hh') hh' hfits hcoins hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hCode1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hinvf
        ⟨err, evs, hevs, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact decPkDefD2c_pathC_lookup_err
          X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact decPkDefD2c_pathC_lookup_err
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact decPkDefD2c_pathC_accept_none
            X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))

theorem stageP2Over_qpan_cli_archive_frozen_at_B_of_init75_and_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {kitEnvs : ∀ F0 peer spkId kpkId opkWord kbk,
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hInit75 : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim W.C.F
      (InitialStateEnv W.C.F) (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs g r evs →
      P2OverErrEnv g r evs)
    (hOkEnv : ∀ g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv kitEnvs g r evs →
      P2OverOkEnv g r evs)
    (hFitsSplit : ∀ st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
            kitEnvs)
          (P2OverPathCOkEnvOf (A := A.repAlloc) X W B
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv kitEnvs)
          g r))
    (hSelfKit : ∀ F0 peer spkId kpkId opkWord kbk,
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ F0 peer spkId kpkId opkWord kbk,
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ F0 peer spkId kpkId opkWord kbk,
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ F0 peer spkId kpkId opkWord kbk,
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliMemInvPlacedAtXBStmt (LibsignalFrozen lsmpl) A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv :=
  stageP2Over_qpan_cli_memInv_placed_at_B_of_pathC
    (stageP2PathCOver_qpan_cli_archive_frozen_of_init75_and_kits A lim X mmpl gh W B
      hDropNz hG hInit75 hErrEnv hOkEnv hFitsSplit hSelfKit hSpkKit hKpkKit hPkKit)
    (cliPromoteMatchingMissGen_placed_ok A.repAlloc mmpl gh W)
    (fun hh => cliPromoteOverGen_archive_placed_ok mmpl gh W hh hGrow hRaw)

theorem stageP2Over_qpan_cli_archive_regErr_frozen_at_B_of_init75_and_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {kitEnvs : ∀ F0 peer spkId kpkId opkWord kbk,
      CliPollStageP2Envs (A := A.repAlloc) B F0 peer spkId kpkId opkWord kbk}
    {P2OverErrEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hInit75 : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim W.C.F
      (InitialStateEnv W.C.F) (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hErrEnv : ∀ g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X W B
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
        kitEnvs g r evs →
      P2OverErrEnv g r evs)
    (hFitsErr : ∀ st_b g r,
      StoresGhost.opened.identity.regId cliIo.rd g.F = .error () →
      FitsEnv M lim st_b (P2OverErrEnv g r) →
      FitsEnv M lim st_b
        (P2OverPathCErrEnvOf (A := A.repAlloc) X W B
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
          kitEnvs g r))
    (hSelfKit : ∀ F0 peer spkId kpkId opkWord kbk,
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).selfEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSpkKit : ∀ F0 peer spkId kpkId opkWord kbk,
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      SignedPreKeyStoreKitPlacedOk A lim
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).spkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkKit : ∀ F0 peer spkId kpkId opkWord kbk,
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      KyberPreKeyStoreKitPlacedOk A lim
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).kpkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPkKit : ∀ F0 peer spkId kpkId opkWord kbk,
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      PreKeyStoreKitPlacedOk A lim
        (cliPollPkKitPlaced A.repAlloc F0 opkWord (cliKitStk B))
        (kitEnvs F0 peer spkId kpkId opkWord kbk).pkEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2OverQpanCliRegErrPlacedAtBStmt (LibsignalFrozen lsmpl) A lim X mmpl gh W B P2OverErrEnv :=
  stageP2Over_qpan_cli_regErr_placed_at_of_pathC
    (stageP2PathCOver_qpan_cli_archive_regErr_placed_at_of_init75_and_kits A lim X mmpl gh W B
      hErrEnv hFitsErr hDropNz hG hInit75 hSelfKit hSpkKit hKpkKit hPkKit)
    (cliPromoteMatchingMissGen_placed_ok A.repAlloc mmpl gh W)
    (fun hh => cliPromoteOverGen_archive_placed_ok mmpl gh W hh hGrow hRaw)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverBPlacedBudgetFd
