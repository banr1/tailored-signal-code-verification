/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll New-Session Path A Stage P4 Continuation

Proves `cliPollStageP4_fsAt_placed` and `closure_pathA_p4_cont_placed` under `RustCliAllocBudget M`,
running `StageP4PathAPlacedStmt` across the four CLI store callbacks and folding both `.ok pt` and
`.markErr` into `dpPollSpecStateBudget.post`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp Bytes eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
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
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  cliPollKpk_markOk_of_pmOfE_placed
  cliPollPk_removeIdOk_of_pmOfE_placed
  cliPollStageP4_fsAt_placed
  closure_pathA_p4_cont_placed
  cliFiles_eq_of_trace_eq_placed
  cliPollStageP1_fsAt_placed
  exit_entails_dpPollPost_placed
  cliPollStageP4Stack_placed_le_subStack
  pathAP4RemAtPlaced
  stageP3MidPathA_eq_p4_placed
  stageP4PathAExit_entails_exit_placed
  genP3Pre_placed genP3CallFrame_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced StageP4PathAPlacedStmt
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (PreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (KyberPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
  StageP4PathAEnv
  StageP4PathAMarkErrEnv
  StageP4PathAPlacedStmt
  StageP4PathAStoreStepEnv
  stageP4ExitAtPlaced
  stageP4PrePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAPlacedBudget (
  cliPollStageP4Stack_placed_le_subStack
  pathAP4RemAtPlaced
  stageP3MidPathA_eq_p4_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4PlacedBudget (
  stageP4PathAExit_entails_exit_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget (
  cliFiles_eq_of_trace_eq_placed
  exit_entails_dpPollPost_placed
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

abbrev cliPollKpk_markOk_of_pmOfE_placed :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollKpk_markOk_of_pmOfE_placed

abbrev cliPollPk_removeIdOk_of_pmOfE_placed :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollPk_removeIdOk_of_pmOfE_placed

theorem cliPollStageP4_fsAt_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (pid sid kid : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State} (hf : s.fs.files = F0) :
    FsAt
      (stageP4EnvOk
        (cliPollSessKitPlaced A.repAlloc F0 Scope peer (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B)))
      (stageP4Quiet
        (cliPollSessKitPlaced A.repAlloc F0 Scope peer (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 pid (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kid sid kbk (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s :=
  .inr ⟨⟨cliPollSessPlaced_quiet F0 Scope peer (cliKitStk B),
         cliPollIdPlaced_quiet F0 peer (cliKitStk B),
         cliPollPk_quiet (A := A.repAlloc) 0#64 F0 pid (cliKitStk B),
         cliPollKpk_quiet (A := A.repAlloc) 0#64 F0 kid sid kbk (cliKitStk B)⟩,
        hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518,
        ⟨hf, hf, hf, hf⟩⟩

set_option maxHeartbeats 1200000 in
theorem closure_pathA_p4_cont_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hP4 : StageP4PathAPlacedStmt)
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt)
    (hcur : opt.bind (·.currentSession) = none)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (kitEnv : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)))
    (pkKitEnv : PreKeyStoreBudgetEnv
      (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)))
    (kpkKitEnv : KyberPreKeyStoreBudgetEnv
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)))
    (evs_pre : List AllocEvent)
    (recG G₁ G' : SessionGhost)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (pt : List (BitVec 8))
    (s0 s2 s' : State)
    (hpm_eq : y.g.msg = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys y.g.F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
      (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hex : SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk))
    (hfits_p4 : FitsEnv M lim (M.stepEvents evs_pre y.st)
      (StageP4PathAEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)) kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
          pendingPreKey := none
          pendingKyberPreKey := none }))
    (hevs_ok : ∀ evs_p4,
      StageP4PathAStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)) kitEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)) pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)) kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.opkId m.kpkId m.spkId y.g.msg.baseKey
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
            (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
          pendingPreKey := none
          pendingKyberPreKey := none } evs_p4 →
      DecPkEnv y.g (evs_pre ++ evs_p4))
    (hevs_markErr : ∀ evs_p4,
      StageP4PathAMarkErrEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) ikitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)) kpkKitEnv
        StoresGhost.opened.identity StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey evs_p4 →
      DecPkEnv y.g (evs_pre ++ evs_p4))
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
      stageP3DispatchOkMid_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s' y.fut y.out 8#64 8#64
        ptCap ptPtr pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins))) :
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
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
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
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
  let F_p3 : SepProp :=
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
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
  let st' := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
  let ses' : Session (List (BitVec 8)) :=
    { pathAInitSession ⟨W.C, W.Q⟩ meE k m dk with
      state := st', pendingPreKey := none, pendingKyberPreKey := none }
  let coinsPost := coinsAfterPlaced y.g.coinsP y.g.coins
    (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)
  have hok_pair : genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 =
      (.ok pt, st') := by
    rcases hg : genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 with ⟨r1, r2⟩
    have hr1 : r1 = .ok pt := by rw [hg] at hok; exact hok
    subst hr1
    have hr2 : r2 = st' := by dsimp only [st']; rw [hg]
    subst hr2
    rfl
  obtain ⟨hKit', hLen'⟩ := pathA_recOk_of_tryDecrypt hdecOk hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := sp_frame_sub_add s0.sp
  have hf' : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps2' (htr'.trans htr2.symm)).trans hfiles2
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp4_64 : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans
      (cliPollStageP4Stack_placed_le_subStack A.repAlloc y.g.F Slots.scopeKit y.g.peer
        pid m.kpkId m.spkId y.g.msg.baseKey B)
      hsub64
  have hwp4 := hP4 mmpl gh W B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
    kitEnv ikitEnv pkKitEnv kpkKitEnv hh hReadFile hDeser
    (M.stepEvents evs_pre y.st) s0 s'
    y.fut y.cx y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
    8#64 ptCap ptPtr 8#64
    m.opkId m.kpkId m.spkId 0#8 pt
    y.g.msg.identityKey y.g.msg.baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber
    G' ses'
    (by decide) hex' ⟨hKit', hLen'⟩ rfl rfl
    (cliPollKpk_markOk_of_pmOfE_placed y.g.F m i σ hpm_eq)
    (cliPollPk_removeIdOk_of_pmOfE_placed y.g.F m i σ hpm_eq)
    hfits_p4 hpt_le hpt_lt hpt_ne hp4_64
    (cliPollStageP4_fsAt_placed hh y.g.F Slots.scopeKit y.g.peer pid m.spkId m.kpkId
      y.g.msg.baseKey B hf')
    hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPathA_eq_p4_placed A lim (M.stepEvents evs_pre y.st) B y s0 s2 s'
    rngPtr 8#64 8#64 whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem coinsPost m.opkId
    (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt G' st'
    hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm2 : s'.mem ⊨
      stageP4PrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        8#64 ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' ∗
      (pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost ∗
        R') := by
    have hEq :
        ((stageP3DispatchOkMid_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s' y.fut y.out
            8#64 8#64 ptCap ptPtr pt 0#8 G' st' ∗
          genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            coinsPost) ∗ F_p3) ∗ R' =
        stageP4PrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit pkKit kpkKit s0 s'
          y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          8#64 ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          G' st' ∗
        (pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem
          coinsPost ∗ R') := by
      dsimp only [F_p3, sp, σ, kit, ikit, pkKit, spkKit, kpkKit]
      rw [hs2_sp, hmid, sepConj_assoc]
    exact hEq ▸ hm1
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  have hpre_id : y.g.msg.preKeyId = m.opkId := hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).1
  have hspk_id : y.g.msg.signedPreKeyId = m.spkId :=
    hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).2.1
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hro_f, hBr⟩⟩ |
    ⟨_hpanf, _Pf, _hmf, hfalse⟩ |
    ⟨_, hoom⟩
  · cases hBr with
    | ok c evs_p4 hevs_p4 _hsave hmark _hrem _hstore htr_f hpost_f =>
      rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        revert hevs_p4 _hrem htr_f
        generalize m.opkId = opk?
        rintro hevs_p4 _hrem htr_f _
        cases opk?
        · simpa [kit, ikit, kpkKit,
            cliPollSessKitPlaced, cliPollSessKit, cliSessionStoreSpec,
            cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
            cliIdentityStoreSpec,
            cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
            cliPollKpkKit, cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
            htr'] using htr_f
        · simpa [kit, ikit, pkKit, kpkKit,
            cliPollSessKitPlaced, cliPollSessKit, cliSessionStoreSpec,
            cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
            cliIdentityStoreSpec,
            cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced, cliPollPkKit, cliPreKeyStoreSpec,
            cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
            cliPollKpkKit, cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
            htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
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
      obtain ⟨_, _, _, hDec, hWr⟩ :=
        decPkDef_pathA_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hfPeer hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hok_pair hmark_eq
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
            (E2E.Record.encodeRecord ⟨some ses'⟩) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.ok pt) s0.trace sf.trace :=
        slotOutTr_of_accept hS hDec hWr
      have hot_eq : g'.oneTime =
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ())) := by
        dsimp only [g', oneTime', pkKit, cliPollPkKitPlaced, cliPreKeyStoreSpecPlaced,
          cliPollPkKit, cliPreKeyStoreSpec]
        rw [hpre_id]
      have hpost_f' : Pf ⊢
          stageP4ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
            kit ikit pkKit kpkKit s0 s' sf y.fut y.g.msgA y.g.peerA
            (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64)
            (y.g.stores + 0x78#64) 8#64 ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
            (vecResultAt A.repAlloc y.out (.ok pt)) m.kpkId m.spkId pt
            y.g.peer y.g.msg.identityKey y.g.msg.baseKey
            (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
            (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
            (match m.opkId with
             | none => StoresGhost.opened.oneTime
             | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
            (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ())) := by
        revert hevs_p4 _hrem htr_f hpost_f
        generalize m.opkId = opk?
        rintro hevs_p4 _hrem htr_f hpost_f
        cases opk? <;> (rw [M.stepEvents_append evs_pre evs_p4 y.st]; exact hpost_f)
      have hexit := stageP4PathAExit_entails_exit_placed A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
        B y s0 s' sf rngPtr 8#64 8#64
        whisperMsgPtr ptCap ptPtr whisperG (vecResultAt A.repAlloc y.out (.ok pt))
        preKeyMsgRem coinsPost m.opkId (y.g.msg.message.messageVersion.zeroExtend 32)
        pid m.kpkId m.spkId pt (.ok pt)
        (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (match m.opkId with
         | none => StoresGhost.opened.oneTime
         | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ()))
        g' hs'_sp0 hsp_sub (decResultAt_ok_entails_decResAt_anyHeap A.repAlloc y.out pt)
        hmsg_fold rfl rfl hot_eq rfl rfl rfl
      dsimp only at hexit
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f')) hm_f
      have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
      have hm_f3 : sf.mem ⊨
          (decResAt A.repAlloc y.out (.ok pt) ∗
            storesAt A.repAlloc y.g.stores g' ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents (evs_pre ++ evs_p4) y.st) sf ∗
            (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f2
      have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
        (evs_pre ++ evs_p4) g' (.ok pt) (LsTokenInit ∗ coinsPost ∗ anyHeap)
        (hevs_ok evs_p4 hevs_p4) hh hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3
    | saveErr _evs_p4 _hevs_p4 hsave _ _ =>
      dsimp only [ikit, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced] at hsave
      exact False.elim (cliId_saveRel_not_err hsave)
    | markErr c e evs_p4 hevs_p4 _hsave hmark htr_f hpost_f =>
      rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        simpa [ikit, kpkKit,
          cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
          cliIdentityStoreSpec,
          cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, cliKyberPreKeyStoreSpecPlaced,
          cliPollKpkKit, cliKpkStoreSpecFull, cliKyberPreKeyStoreSpec, cliKpkStoreSpec,
          htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG
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
      have hDec := decPkDef_pathA_mark_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg
        y.g.coins hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hok_pair hmark_err
      let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val
            y.g.msg.identityKey (.ok c)
          kyber := kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.error err) s0.trace sf.trace :=
        slotOutTr_of_reject g' hS nofun nofun hDec
      have hpost_f' : Pf ⊢
          stageP4ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
            kit ikit pkKit kpkKit s0 s' sf y.fut y.g.msgA y.g.peerA
            (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64)
            (y.g.stores + 0x78#64) 8#64 ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
            (speErrAt kpkKit.markErr y.out e) m.kpkId m.spkId pt
            y.g.peer y.g.msg.identityKey y.g.msg.baseKey
            StoresGhost.opened.sessions
            (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
            StoresGhost.opened.oneTime
            (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e)) := by
        rw [M.stepEvents_append evs_pre evs_p4 y.st]
        exact hpost_f
      have hexit := stageP4PathAExit_entails_exit_placed A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
        B y s0 s' sf rngPtr 8#64 8#64
        whisperMsgPtr ptCap ptPtr whisperG (speErrAt kpkKit.markErr y.out e) preKeyMsgRem
        coinsPost m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId
        pt (.error err) StoresGhost.opened.sessions StoresGhost.opened.oneTime
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e))
        g' hs'_sp0 hsp_sub
        (cliKpkMarkErrSpec_entails_decResAt_anyHeap A.repAlloc y.out e err)
        hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f')) hm_f
      have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
      have hm_f3 : sf.mem ⊨
          (decResAt A.repAlloc y.out (.error err) ∗
            storesAt A.repAlloc y.g.stores g' ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            FromRecordCallees.lsLogOff ∗
            A.pool lim (M.stepEvents (evs_pre ++ evs_p4) y.st) sf ∗
            (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f2
      have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
        (evs_pre ++ evs_p4) g' (.error err) (LsTokenInit ∗ coinsPost ∗ anyHeap)
        (hevs_markErr evs_p4 hevs_p4) hh hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3
    | removeErr opkId _c _e _evs_p4 hopk _hevs_p4 _hsave _hmark hrem _ _ =>
      exact False.elim (cliPk_removeRel_not_err_of_pkStoreKeys (A := A.repAlloc) (b := 0#64)
        (pid := pid) (σ := σ) (e := _e) hk hopk hrem)
    | storeErr _c _evs_p4 _hevs_p4 _hsave _hmark _hrem hstore _ _ =>
      dsimp only [kit, cliPollSessKitPlaced] at hstore
      exact False.elim (cliSess_storeRel_not_err hstore)
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4ContPlacedBudget
