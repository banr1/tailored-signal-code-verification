/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Poll Composition for Non-Matching Overwrite (`DecPkOkOverV4`)

Unpacks the `dpPollSpecStateBudget` entry precondition under `DecPkOkOverV4`, defines
`DecPkD3ValidOverPollEnv`, and proves the block-`518` (`dpPollEntryPlaced`) poll contracts
`decPk_d3_validOver_poll_placedBudget`, `decPk_d3_validOver_poll_full_placedBudget`, and
`decPk_d3_validOver_poll_at_full_placedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalFrozen LibsignalPlacement libsignalFrozen_of_keepsFrozen lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E (
  UnreachedPqxdhPrimitives acceptInput modelPrims
)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt
  processPrekeyInnerInitAt processPrekeyPostTrustAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel p1LoadedRecordAt sp_sub_cd0_align_std3 stageP1CallStack
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (extract_withLsFrozen withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt uuidTryParse)
open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym dirAt
)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunSem dpPollNeed dpSlotArgsPlaced
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  SessMatchesPm dpCxAt dpFutStartAt pkStoreKeys pkToE?
)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer loadRec scopeIn scopeKit)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliIdStoreSpecFull cliIdStoreSpecFullPlaced
  cliId_trustRel_eq_of_trusted cliKitStk cliKpkStoreSpecFullPlaced cliKyberPreKeyStoreSpecPlaced
  cliPollIdKit cliPollIdKitPlaced cliPollId_trustUpdate_eq_placed cliPollKpkKitPlaced
  cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced cliPollSessPrev1KitPlaced
  cliPollSpkKitPlaced cliPollStoresKitsAtPlaced cliPollStoresKitsAtPlaced_entails_storesAt
  cliPreKeyStoreSpecPlaced cliSess_loadRel_isOk cliSignedPreKeyStoreSpecPlaced
  closStackUnusedP1OkAt clos_stack_3280_split_for_p1_ok coroUnusedP1At coroUnusedP1AtPlaced
  dpClosSubStack dpCxAt_entails_memRegion32 dpFutStartAt_split_for_p1_placed dpPollEntryPlaced
  dpPollNeed_eq_frame_add_subStack dpPollProgPlaced loadRec_of_cliPollSessPlaced_loadRel
  pathAInitSession pathAInitState pmKyberId pmPreKeyId
  preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt sepWPp_conseq_pre sepWPp_sepExists_left
  stackAt_poll_entry_split stackAt_subStack_split stageP1CallStack_le_subStack
  stageP2PostP1At subStack_le_sp_of_dpPollNeed subroutine_ok_of_sepWPp_steps
  trusted_ok_of_filesOkPeer
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv fitsEvents_append
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1ExitEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (VerNeTopEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  DecPkOkOverV4 ScopeOverIn decPkOverDef
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget (
  StageP4Prev1VRegsAtPlacedStmt closure_pathCOver_d3_at_full_placedBudget_ok
  closure_pathCOver_d3_full_placedBudget_ok closure_pathCOver_d3_placedBudget_ok
  closure_untrusted_over_d3_full_placedBudget_ok closure_untrusted_over_d3_placedBudget_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget (
  StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt StageP2OverQpanCliD3FrozenPlacedBudgetStmt
  StageP2OverQpanCliD3PlacedBudgetStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage4PlacedBudget (
  storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget (
  StageP3Prev1D3FrozenPlacedStmt StageP3Prev1D3PlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  CliStageP4Prev1Envs StageP4Prev1VRegsPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv cliPollStageP1_fsAt_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1OkPreAt stageP1_ok_placed_inst
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced slotFramePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  readFileSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Budget-Threaded Entry Unpacking under `DecPkOkOverV4` -/

/-- Budget-threaded pure invariants unpacked from
`withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget ...)` under `DecPkOkOverV4`. -/
structure DpPollEntryPureOverD3Placed [LibsignalPlacement] {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 : State) : Prop where
  ro : LibsignalCodeRoLoaded lsmpl s0.mem
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg
  fits : FitsEnv M lim y.st (DecPkEnv y.g)

/-- Unpack `(withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget ...)).pre` into
`DpPollEntryPureOverD3Placed` and `dpPollEntrySpatialPlaced`. -/
theorem dpPollPre_unpack_over_d3_placed [LibsignalPlacement]
    {W : CliHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R) :
    DpPollEntryPureOverD3Placed (W := W) (Scope := Scope) stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) := by
  obtain ⟨hro, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have h2 : s0.mem ⊨
      ⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgsPlaced y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧
            FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗
              LsTokenInit ∗
              lsLogOff ∗
              A.pool lim y.st s0 ∗
              preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R)))) := by
    simpa only [dpPollSpecStateBudget, dpSlotPollKStatePlaced, slotFramePlaced, sepConj_assoc]
      using hpre0
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧
          FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗
          (dpCxAt y.cx ∗
            (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
              storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗
              LsTokenInit ∗
              lsLogOff ∗
              A.pool lim y.st s0 ∗
              preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))) := by
    convert h3 using 1
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk, hfits⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hro, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk, hfits⟩, ?_⟩
  dsimp only [dpPollEntrySpatialPlaced]
  convert h5_cx using 1
  sep_ac_rfl

/-! ## 2. Full Block-`518` Poll Envelope & Theorem (`decPk_d3_validOver_poll_placedBudget`) -/

/-- Concrete CLI Stage P1 (`is_trusted_identity = .ok true`) allocation envelope on `StoresGhost.opened`. -/
def CliStageP1OkEnv [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  StageP1OkEnv
    (cliPollSessKitPlaced A g.F scopeKit g.peer σ)
    (cliPollSessBudgetEnv A g.F g.peer σ DeserEnv ReadEnv)
    StoresGhost.opened.sessions
    (cliPollIdKitPlaced A g.F g.peer σ)
    (cliPollIdBudgetEnv A g.F g.peer σ ReadEnv)
    StoresGhost.opened.identity
    g.peer.val g.msg.identityKey evs

/-- Complete Block-`518` poll allocation-event envelope for D3 `validOver` (`DecPkOkOverV4`),
covering untrusted rejection (`CliDpPollUntrustedEnv`), Stage P1 (`CliStageP1OkEnv`), and all
`Path C Over` stage envelopes (`StageP2OverEnv`, `StageP3Prev1Env`, `StageP3ErrM3Env`,
`StageP3VerNePrev1Env`, `StageP4Prev1ExitEnv`). -/
def DecPkD3ValidOverPollEnv [LibsignalPlacement] {A : RustAlloc}
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  let σ := cliKitStk B
  let P1 := CliStageP1OkEnv (A := A) B ReadEnv DeserEnv g
  CliDpPollUntrustedEnv (A := A) B ReadEnv DeserEnv g evs ∨
  P1 evs ∨
  ∃ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
    (cliPollSessKitPlaced A g.F scopeKit g.peer σ).loadRel
      StoresGhost.opened.sessions g.peer.val (.ok (some r)) ∧
    r.currentSession = some s_old ∧
    ScopeOverIn r ∧
    ¬ SessMatchesPm s_old g.msg ∧
    (SeqEnv P1 (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) evs ∨
     (∃ m i k kp reg dk recG whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message
           (g.msg.message.messageVersion.zeroExtend 32)
           (encSession (clearPending s_old)) g.coins) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG G₁ whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       CloneRel recG G₁ ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3ErrM3Env (tdEnv W) recG G₁
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           g.peer g.me whisperG g.msg.message g.coins) evs) ∨
     (∃ m i k, ∃ kp : IdentityKeyPair, ∃ reg dk recG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
         (StageP3VerNePrev1Env VerNeTopEnv recG
           (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           (encSession (clearPending s_old))) evs) ∨
     (∃ m i k kp reg dk recG G₁ G' pt whisperG,
       pkToE? g.msg = some m ∧
       g.msg.message = i ∧
       SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
       pkStoreKeys g.F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
       StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
       SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
         (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
       SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
       CloneRel recG G₁ ∧
       G₁.AfterTryDecrypt true G' ∧
       (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
         (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt ∧
       let pid := pmPreKeyId g.msg
       let envs := p4Envs B g.F g.peer pid m.kpkId m.spkId g.msg.baseKey
       let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
       let ses' : Session (List (BitVec 8)) :=
         { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
           state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
           pendingPreKey := none
           pendingKyberPreKey := none }
       SeqEnv
         (SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
           (StageP3OkPrefixM3Env (tdEnv W) recG G₁ st0
             g.peer g.me whisperG g.msg.message g.coins))
         (StageP4Prev1ExitEnv
           (cliPollSessPrev1KitPlaced A g.F g.peer σ) envs.opsEnv
           (cliPollIdKitPlaced A g.F g.peer σ) envs.ikitEnv
           (cliPollPkKitPlaced A g.F pid σ) envs.pkKitEnv
           (cliPollKpkKitPlaced A g.F m.kpkId m.spkId g.msg.baseKey σ) envs.kpkKitEnv
           StoresGhost.opened.sessions StoresGhost.opened.identity
           StoresGhost.opened.oneTime StoresGhost.opened.kyber
           m.opkId g.peer.val g.msg.identityKey m.kpkId m.spkId g.msg.baseKey G' ses'
           (encSession (clearPending s_old))) evs))

/-- Pointwise budget-threaded `[LibsignalPlacement]` D3 `validOver` poll contract on Block `518`
(`dpPollEntryPlaced = lsmpl.base 518`) at fixed `(mmpl, gh, W, X, B, S, Scope)` under `decPkOverDef`
and `DecPkOkOverV4`. -/
def CliDpPollOkOverV4StatePlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CliGhostAllocHooks M A lim gh →
  RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
    (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
  EncodeInjOn scopeKit →
  (∀ r, Scope r → scopeIn r) →
  S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope →
  (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
    FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm) →
  ∀ stk' : Nat, (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk'))

theorem seqEnv_append_d3 {E₁ E₂ : List AllocEvent → Prop} {evs₁ evs₂ : List AllocEvent}
    (h1 : E₁ evs₁) (h2 : E₂ evs₂) : SeqEnv E₁ E₂ (evs₁ ++ evs₂) :=
  Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩

theorem fitsEnv_after_d3 {M : AllocCostModel} {lim : BudgetLimits}
    {FullEnv RemEnv : List AllocEvent → Prop} {st : M.σ} {evs_pre : List AllocEvent}
    (hfits : FitsEnv M lim st FullEnv)
    (hsub : ∀ evs, RemEnv evs → FullEnv (evs_pre ++ evs)) :
    FitsEnv M lim (M.stepEvents evs_pre st) RemEnv := fun evs hevs =>
  ((fitsEvents_append M lim evs_pre evs st).mp (hfits (evs_pre ++ evs) (hsub evs hevs))).2

theorem sepWPp_bind_p1_false_d3 {prog : Program} {mid target : BitVec 64} {s0 : State}
    {P1 Fr : SepProp} {Q1 Q Qpan : State → SepProp → Prop}
    (hwp1 : SepWPp prog mid s0 P1 Q1 (fun _ _ => False))
    (hk : ∀ s1 P_1, Steps prog s0 s1 → s1.pc = mid → s1.status = .Running →
      Q1 s1 P_1 → SepWPp prog target s1 (P_1 ∗ Fr) Q Qpan) :
    SepWPp prog target s0 (P1 ∗ Fr) Q Qpan := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨s1, hsteps01, ⟨hpc1, hrun1, P_1, hm1, hq1⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hoom⟩⟩ :=
    hwp1 (Fr ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps1f, hout⟩ :=
      hk s1 P_1 hsteps01 hpc1 hrun1 hq1 R hm1 (hsteps01.codeLoaded hL)
    exact ⟨sf, Steps.trans hsteps01 hsteps1f, hout⟩
  · exact False.elim hfalse
  · exact (not_satisfies_false_sepConj hoom).elim

theorem p1Ok_post_eq_stageP2PostP1At_budget_d3_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_p1 : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt Scope A.repAlloc y.fut opt ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      A.pool lim st_p1 s1) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48) =
    stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope A.repAlloc y.fut opt := by
  dsimp only [stageP2PostP1At, RustCliAllocBudget.atState, cliPollSessKitPlaced,
    cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced, cliPollKpkKitPlaced,
    cliIdStoreSpecFullPlaced, cliPreKeyStoreSpecPlaced,
    cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
    cliKyberPreKeyStoreSpecPlaced]
  sep_frame

theorem p1Ok_recombine_entails_stageP2_budget_d3_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem}
    (stk' : Nat) (_hneed : dpPollNeed B ≤ stk') (_hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_p1 : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗
      cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores
        (ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey
          .receiving (.ok true)) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      A.pool lim st_p1 s1 ∗
      stackAt sp (stageP1CallStack kit ikit)) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit) ⊢
    stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
    LsTokenInit ∗
    lsLogOff ∗
    stackAt sp (dpClosSubStack B) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
    stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
  have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
  have hp1_eq := p1Ok_post_eq_stageP2PostP1At_budget_d3_placed (Scope := scopeKit)
    y st_p1 s0 s1 rngPtr v_a8 v_b8 v_d0 opt
  dsimp only at hp1_eq
  have hp1_ent := Entails.of_eq hp1_eq
  have hpm_ent := Entails.of_eq
    (preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg).symm
  have hstk_ent := Entails.of_eq
    (stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64).symm
  have h4 := sepConj_mono hp1_ent (sepConj_mono hstores_back (sepConj_mono hpm_ent hstk_ent))
  let Pass : SepProp :=
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit ∗
    lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  refine Entails.trans ?_ (Entails.trans (sepConj_mono_left h4 : _ ∗ Pass ⊢ _ ∗ Pass) ?_)
  · dsimp only [cliPollId_trustUpdate_eq_placed, cliPollStoresKitsAtPlaced, Pass,
      sp, σ, pid, sid, kid, kbk, kit, ikit]
    sep_frame
  · dsimp only [Pass, sp, σ, kit, ikit]
    sep_frame

set_option maxHeartbeats 1200000 in
/-- Block-`518` poll composition (`dpPollEntryPlaced = lsmpl.base 518`) for `validOver`
(`DecPkOkOverV4`), combining `closure_untrusted_over_d3_placedBudget_ok`, `stageP1_ok_placed_inst`,
and `closure_pathCOver_d3_placedBudget_ok`. -/
theorem decPk_d3_validOver_poll_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hP2O : StageP2OverQpanCliD3PlacedBudgetStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3PlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      DecPkD3ValidOverPollEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StatePlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hG hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_over_d3_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨⟨hd3False, _hd3Scope⟩, r0, s_old0, hload0, hcur0, hScopeOver0, hnot_match0⟩ :=
    hpure.decPkOk
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_over_d3_placedBudget_ok A lim hDropNz mmpl gh W X B S Scope
      hh hRead hDeser hinjK hsub hS stk' hneed' hstk63 y
      (fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inl hevs)))
      (fun evs hevs => hEnv y.g evs (Or.inl hevs))
      R s0 hpc hrun hsp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hd3False htrusted hm_base
  | true =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hhSt :
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
          A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
      ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs,
       hh.utf8, hh.memrchr, hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed' hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3 A.repAlloc
      σ y.g.stores hsub hpure.filesOkPeer hd3False pid sid kid kbk
    have hm_stores : s0.mem ⊨
        memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
      Satisfies.mono (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
    have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
      have := dpPollNeed_eq_frame_add_subStack B; omega
    have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
      stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
    rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
        preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        stackAt_poll_entry_split s0.sp B stk' hneed' hstk63,
        stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
        clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
    rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
      b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
    rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
    simp only [Nat.reduceMul] at hm_flat
    dsimp only [cliPollStoresKitsAtPlaced, coroUnusedP1AtPlaced] at hm_flat
    let P_p1 : SepProp :=
      stageP1OkPreAt A lim y.st kit ikit StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer y.g.msg.identityKey s0 sp y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) y.g.stores
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
        v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2
    let Fr_inner : SepProp :=
      memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
      Satisfies.mono (by
        dsimp only [P_p1, Fr_inner, stageP1OkPreAt, kit, ikit, pkKit, spkKit, kpkKit,
          cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
          cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
          cliPreKeyStoreSpecPlaced, cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
          cliKyberPreKeyStoreSpecPlaced]
        sep_frame) hm_flat
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inr (Or.inl hevs)))
    have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
      hhSt hRead hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity
      (Nat.le_trans hp1_le hsub64) rfl rfl
      (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
        StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
      (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
        cliId_trustRel_eq_of_trusted htrusted h)
      hfits_p1
      s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
      v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2
      hpure.ro
      (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_false_d3 hwp ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hP1_raw, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
    have hP1 : CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs_p1 := hP1_raw
    have htr1 : s1.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := p1Ok_recombine_entails_stageP2_budget_d3_placed stk' hneed' hstk63 y
      (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    have hload_opt : loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
    cases opt with
    | none =>
      cases hload0.symm.trans hload_opt
    | some r =>
      have hr_eq0 : r = r0 := Option.some.inj (Except.ok.inj (hload_opt.symm.trans hload0))
      subst hr_eq0
      exact closure_pathCOver_d3_placedBudget_ok A lim DecPkEnv hP2O hP3O hP4O
        mmpl gh W X B S Scope hG hh hTry hinjK hsub hS stk' hneed' hstk63
        y evs_p1 r s_old0 s0 s1 coins v_a8 v_b8 v_d0 R
        (fitsEnv_after_d3 hpure.fits fun evs2 h2 =>
          hEnv y.g (evs_p1 ++ evs2)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inl (seqEnv_append_d3 hP1 h2)⟩)))
        (fun evs2 h2 =>
          hEnv y.g (evs_p1 ++ evs2)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inl (seqEnv_append_d3 hP1 (Or.inl h2))⟩)))
        (fun evs2 m i k kp reg dk recG whisperG h2 hpk hmsg_i hi hk hkp hreg hacc hex =>
          fitsEnv_after_d3 hpure.fits fun evs3 h3 =>
            hEnv y.g ((evs_p1 ++ evs2) ++ evs3)
              (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
                Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, whisperG,
                  hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
                  seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩)⟩)))
        (fun evs2 evs3 m i k kp reg dk recG G₁ whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl h3 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, G₁, whisperG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl,
                seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩))⟩)))
        (fun evs2 evs3 m i k kp reg dk recG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex h3 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
                seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩)))⟩)))
        (fun evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl htd h3 hok =>
          fitsEnv_after_d3 hpure.fits fun evs4 h4 =>
            hEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4)
              (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
                Or.inr (Or.inr (Or.inr (Or.inr ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                  hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl, htd, hok,
                  seqEnv_append_d3 (seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3) h4⟩)))⟩)))
        (fun evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl htd h3 hok h4 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inr (Or.inr ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl, htd, hok,
                seqEnv_append_d3 (seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3) h4⟩)))⟩)))
        hpure.files_eq hpure.filesOkPeer hd3False hScopeOver0 hpure.coins_lt htrusted
        hload_rel hcur0 hnot_match0
        hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-! ## 3. `LibsignalFrozen` / `withLsFrozen` Twins -/

/-- `LibsignalFrozen`-guarded pure invariants unpacked from
`withLsFrozen lsmpl (dpPollSpecStateBudget ...)` under `DecPkOkOverV4`. -/
structure DpPollEntryPureOverD3FrozenPlaced [LibsignalPlacement] {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 : State) : Prop where
  froz : LibsignalFrozen lsmpl s0.mem
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg
  fits : FitsEnv M lim y.st (DecPkEnv y.g)

/-- Unpack `(withLsFrozen lsmpl (dpPollSpecStateBudget ...)).pre` into
`DpPollEntryPureOverD3FrozenPlaced` and `dpPollEntrySpatialPlaced`. -/
theorem dpPollPre_unpack_over_d3_frozen_placed [LibsignalPlacement]
    {W : CliHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R) :
    DpPollEntryPureOverD3FrozenPlaced (W := W) (Scope := Scope) stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) := by
  obtain ⟨hfroz, hpre0⟩ := extract_withLsFrozen hpre
  have hpre_ro : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded.of_libsignalFrozen hfroz,
      hpre0⟩
  obtain ⟨hpure, hspatial⟩ :=
    dpPollPre_unpack_over_d3_placed (W := W) (Scope := Scope) hSemOk stk' y R s0 hpre_ro
  exact ⟨⟨hfroz, hpure.x0, hpure.x1, hpure.x2, hpure.stk_le_sp, hpure.files_eq,
    hpure.coins_lt, hpure.filesOkPeer, hpure.decPkOk, hpure.fits⟩, hspatial⟩

/-- Pointwise `withLsFrozen`-guarded D3 `validOver` poll contract on Block `518`
(`dpPollEntryPlaced = lsmpl.base 518`) at fixed `(mmpl, gh, W, X, B, S, Scope)` under `decPkOverDef`
and `DecPkOkOverV4`. -/
def CliDpPollOkOverV4StateFrozenPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CliGhostAllocHooks M A lim gh →
  RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
    (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) →
  EncodeInjOn scopeKit →
  (∀ r, Scope r → scopeIn r) →
  S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope →
  (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
    FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm) →
  ∀ stk' : Nat, (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk'))

set_option maxHeartbeats 1200000 in
/-- `withLsFrozen`-guarded block-`518` poll composition for `validOver` (`DecPkOkOverV4`),
combining `closure_untrusted_over_d3_full_placedBudget_ok`, `stageP1_ok_placed_inst`, and
`closure_pathCOver_d3_full_placedBudget_ok`. -/
theorem decPk_d3_validOver_poll_full_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hP2O : StageP2OverQpanCliD3FrozenPlacedBudgetStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      DecPkD3ValidOverPollEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hG hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_over_d3_frozen_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨⟨hd3False, _hd3Scope⟩, r0, s_old0, hload0, hcur0, hScopeOver0, hnot_match0⟩ :=
    hpure.decPkOk
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_over_d3_full_placedBudget_ok A lim hDropNz mmpl gh W X B S Scope
      hh hRead hDeser hinjK hsub hS stk' hneed' hstk63 y
      (fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inl hevs)))
      (fun evs hevs => hEnv y.g evs (Or.inl hevs))
      R s0 hpc hrun hsp hpure.froz hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hd3False htrusted hm_base
  | true =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hhSt :
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
          A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
      ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs,
       hh.utf8, hh.memrchr, hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed' hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3 A.repAlloc
      σ y.g.stores hsub hpure.filesOkPeer hd3False pid sid kid kbk
    have hm_stores : s0.mem ⊨
        memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
      Satisfies.mono (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
    have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
      have := dpPollNeed_eq_frame_add_subStack B; omega
    have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
      stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
    rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
        preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        stackAt_poll_entry_split s0.sp B stk' hneed' hstk63,
        stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
        clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
    rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
      b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
    rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
    simp only [Nat.reduceMul] at hm_flat
    dsimp only [cliPollStoresKitsAtPlaced, coroUnusedP1AtPlaced] at hm_flat
    let P_p1 : SepProp :=
      stageP1OkPreAt A lim y.st kit ikit StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer y.g.msg.identityKey s0 sp y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) y.g.stores
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
        v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2
    let Fr_inner : SepProp :=
      memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
      Satisfies.mono (by
        dsimp only [P_p1, Fr_inner, stageP1OkPreAt, kit, ikit, pkKit, spkKit, kpkKit,
          cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
          cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
          cliPreKeyStoreSpecPlaced, cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
          cliKyberPreKeyStoreSpecPlaced]
        sep_frame) hm_flat
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inr (Or.inl hevs)))
    have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
      hhSt hRead hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity
      (Nat.le_trans hp1_le hsub64) rfl rfl
      (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
        StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
      (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
        cliId_trustRel_eq_of_trusted htrusted h)
      hfits_p1
      s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
      v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2
      (CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded.of_libsignalFrozen
        hpure.froz)
      (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_false_d3 hwp ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hP1_raw, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, _hro1⟩
    have hfroz1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hpure.froz hsteps01.keepsFrozen
    have hP1 : CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs_p1 := hP1_raw
    have htr1 : s1.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := p1Ok_recombine_entails_stageP2_budget_d3_placed stk' hneed' hstk63 y
      (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    have hload_opt : loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
    cases opt with
    | none =>
      cases hload0.symm.trans hload_opt
    | some r =>
      have hr_eq0 : r = r0 := Option.some.inj (Except.ok.inj (hload_opt.symm.trans hload0))
      subst hr_eq0
      exact closure_pathCOver_d3_full_placedBudget_ok A lim DecPkEnv hP2O hP3O hP4O
        mmpl gh W X B S Scope hG hh hTry hinjK hsub hS stk' hneed' hstk63
        y evs_p1 r s_old0 s0 s1 coins v_a8 v_b8 v_d0 R
        (fitsEnv_after_d3 hpure.fits fun evs2 h2 =>
          hEnv y.g (evs_p1 ++ evs2)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inl (seqEnv_append_d3 hP1 h2)⟩)))
        (fun evs2 h2 =>
          hEnv y.g (evs_p1 ++ evs2)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inl (seqEnv_append_d3 hP1 (Or.inl h2))⟩)))
        (fun evs2 m i k kp reg dk recG whisperG h2 hpk hmsg_i hi hk hkp hreg hacc hex =>
          fitsEnv_after_d3 hpure.fits fun evs3 h3 =>
            hEnv y.g ((evs_p1 ++ evs2) ++ evs3)
              (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
                Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, whisperG,
                  hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
                  seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩)⟩)))
        (fun evs2 evs3 m i k kp reg dk recG G₁ whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl h3 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, G₁, whisperG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl,
                seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩))⟩)))
        (fun evs2 evs3 m i k kp reg dk recG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex h3 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
                seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩)))⟩)))
        (fun evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl htd h3 hok =>
          fitsEnv_after_d3 hpure.fits fun evs4 h4 =>
            hEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4)
              (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
                Or.inr (Or.inr (Or.inr (Or.inr ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                  hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl, htd, hok,
                  seqEnv_append_d3 (seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3) h4⟩)))⟩)))
        (fun evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl htd h3 hok h4 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inr (Or.inr ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl, htd, hok,
                seqEnv_append_d3 (seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3) h4⟩)))⟩)))
        hpure.files_eq hpure.filesOkPeer hd3False hScopeOver0 hpure.coins_lt htrusted
        hload_rel hcur0 hnot_match0
        hsteps01 htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

set_option maxHeartbeats 1200000 in
/-- Pointwise `(X, mmpl, gh, W)` `withLsFrozen`-guarded block-`518` poll composition for
`validOver` (`DecPkOkOverV4`). -/
theorem decPk_d3_validOver_poll_at_full_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hP2O : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      DecPkD3ValidOverPollEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope := by
  intro hG hh hRead hDeser hinjK hsub hS hSemOk stk' hneed hstk63
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_over_d3_frozen_placed (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre
  obtain ⟨⟨hd3False, _hd3Scope⟩, r0, s_old0, hload0, hcur0, hScopeOver0, hnot_match0⟩ :=
    hpure.decPkOk
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    exact closure_untrusted_over_d3_full_placedBudget_ok A lim hDropNz mmpl gh W X B S Scope
      hh hRead hDeser hinjK hsub hS stk' hneed' hstk63 y
      (fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inl hevs)))
      (fun evs hevs => hEnv y.g evs (Or.inl hevs))
      R s0 hpc hrun hsp hpure.froz hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hd3False htrusted hm_base
  | true =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hhSt :
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
          A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
      ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs,
       hh.utf8, hh.memrchr, hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed' hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d3 A.repAlloc
      σ y.g.stores hsub hpure.filesOkPeer hd3False pid sid kid kbk
    have hm_stores : s0.mem ⊨
        memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
      Satisfies.mono (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
    have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
      have := dpPollNeed_eq_frame_add_subStack B; omega
    have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
      stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
    rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
        preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        stackAt_poll_entry_split s0.sp B stk' hneed' hstk63,
        stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
        clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
    rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
      b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
    rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
    simp only [Nat.reduceMul] at hm_flat
    dsimp only [cliPollStoresKitsAtPlaced, coroUnusedP1AtPlaced] at hm_flat
    let P_p1 : SepProp :=
      stageP1OkPreAt A lim y.st kit ikit StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer y.g.msg.identityKey s0 sp y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) y.g.stores
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
        v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2
    let Fr_inner : SepProp :=
      memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
      Satisfies.mono (by
        dsimp only [P_p1, Fr_inner, stageP1OkPreAt, kit, ikit, pkKit, spkKit, kpkKit,
          cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
          cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
          cliPreKeyStoreSpecPlaced, cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
          cliKyberPreKeyStoreSpecPlaced]
        sep_frame) hm_flat
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inr (Or.inl hevs)))
    have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
      hhSt hRead hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity
      (Nat.le_trans hp1_le hsub64) rfl rfl
      (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
        StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
      (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
        cliId_trustRel_eq_of_trusted htrusted h)
      hfits_p1
      s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
      v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2
      (CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded.of_libsignalFrozen
        hpure.froz)
      (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_false_d3 hwp ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hP1_raw, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, _hro1⟩
    have hfroz1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hpure.froz hsteps01.keepsFrozen
    have hP1 : CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs_p1 := hP1_raw
    have htr1 : s1.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := p1Ok_recombine_entails_stageP2_budget_d3_placed stk' hneed' hstk63 y
      (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    have hload_opt : loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hpure.filesOkPeer hload_rel
    cases opt with
    | none =>
      cases hload0.symm.trans hload_opt
    | some r =>
      have hr_eq0 : r = r0 := Option.some.inj (Except.ok.inj (hload_opt.symm.trans hload0))
      subst hr_eq0
      exact closure_pathCOver_d3_at_full_placedBudget_ok A lim DecPkEnv hP2O hP3O hP4O
        B S Scope hG hh hTry hinjK hsub hS stk' hneed' hstk63
        y evs_p1 r s_old0 s0 s1 coins v_a8 v_b8 v_d0 R
        (fitsEnv_after_d3 hpure.fits fun evs2 h2 =>
          hEnv y.g (evs_p1 ++ evs2)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inl (seqEnv_append_d3 hP1 h2)⟩)))
        (fun evs2 h2 =>
          hEnv y.g (evs_p1 ++ evs2)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inl (seqEnv_append_d3 hP1 (Or.inl h2))⟩)))
        (fun evs2 m i k kp reg dk recG whisperG h2 hpk hmsg_i hi hk hkp hreg hacc hex =>
          fitsEnv_after_d3 hpure.fits fun evs3 h3 =>
            hEnv y.g ((evs_p1 ++ evs2) ++ evs3)
              (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
                Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, whisperG,
                  hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
                  seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩)⟩)))
        (fun evs2 evs3 m i k kp reg dk recG G₁ whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl h3 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG, G₁, whisperG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl,
                seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩))⟩)))
        (fun evs2 evs3 m i k kp reg dk recG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex h3 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inr (Or.inl ⟨m, i, k, kp, reg, dk, recG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex,
                seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3⟩)))⟩)))
        (fun evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl htd h3 hok =>
          fitsEnv_after_d3 hpure.fits fun evs4 h4 =>
            hEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4)
              (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
                Or.inr (Or.inr (Or.inr (Or.inr ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                  hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl, htd, hok,
                  seqEnv_append_d3 (seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3) h4⟩)))⟩)))
        (fun evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
            h2 hpk hmsg_i hi hk hkp hreg hacc hex hcl htd h3 hok h4 =>
          hEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4)
            (Or.inr (Or.inr ⟨r, s_old0, hload_rel, hcur0, hScopeOver0, hnot_match0,
              Or.inr (Or.inr (Or.inr (Or.inr ⟨m, i, k, kp, reg, dk, recG, G₁, G', pt, whisperG,
                hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hcl, htd, hok,
                seqEnv_append_d3 (seqEnv_append_d3 (seqEnv_append_d3 hP1 h2) h3) h4⟩)))⟩)))
        hpure.files_eq hpure.filesOkPeer hd3False hScopeOver0 hpure.coins_lt htrusted
        hload_rel hcur0 hnot_match0
        hsteps01 htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
