/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Stage P2, P3, and P4 Interfaces

Defines the budget-threaded `RunHooksPlaced` bundle, Stage P2 and Stage P4 allocation envelopes,
spatial entry/exit predicates over `A.atState lim st s_pool`, and stage interfaces bundled into
`ClosureStagesPlacedStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
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
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  StageP1OkPlacedStmt StageP1UntrustedPlacedStmt
  StageP3PrevEmptyVRegsPlacedStmt StageP3GenStepsVRegsPlacedStmt
  stageP4MatchedSharedPlaced stageP4MatchedPrePlaced stageP4MatchedExitAtPlaced
  StageP4MatchedBranchPlaced StageP4MatchedPlacedStmt
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced StageP4PathAPlacedStmt
  StageP2MatchedCliPlacedStmt
  StageP2PathAErrPlaced StageP2PathACliPlacedStmt ClosureStagesPlacedStmt
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents rustCliAllocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (formatInnerBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv PreKeyStoreBudgetEnv retagPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv retagKyberPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv StoreStepEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv retagIdentityStore)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced ReadFileRuleEnv
   readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

abbrev StageP1OkPlacedStmt [LibsignalPlacement] : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget.StageP1OkPlacedStmt

abbrev StageP1UntrustedPlacedStmt [LibsignalPlacement] : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget.StageP1UntrustedPlacedStmt

abbrev StageP3PrevEmptyVRegsPlacedStmt [LibsignalPlacement] : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3PrevEmptyVRegsPlacedStmt

abbrev StageP3GenStepsVRegsPlacedStmt [LibsignalPlacement] : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.StageP3GenStepsVRegsPlacedStmt

/-- Relocatable `[LibsignalPlacement]` budget-threaded hook facts for `signal_session::run` and
its poll callees. -/
structure RunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks) : Prop where
  alloc : AllocContractsXCliPlaced A lim ext
  allocFs : AllocContractsFsPlaced A lim ext
  panics : CliPanicHooksPlaced ext
  memcpyRO : HookSat ext LibsignalTripleRatchet.lsMemcpySym (withVmPreserved sessionMemcpyRegionROSpec)
  bcmp : HookSat ext "bcmp" (withVmPreserved cliBcmpSpec)
  fs : ∀ (prog : Program) (i : Nat), [IsLsBlockProg prog i ext] → TraceFsSound prog
  utf8 : ∀ stk : Nat, HookSat ext lsFromUtf8Sym (withVmPreserved (fromUtf8AsciiSpec stk))
  memrchr : ∀ stk : Nat, HookSat ext lsMemrchrSym (withVmPreserved (memrchrSpec stk))
  codecHooks : CodecHooksPlaced M A lim ext
  allocZeroed : HookSat ext lsRustAllocZeroedSymCli (rustCliAllocBudgetSpec M A lim true)
  stringClone : HookSat ext SignalSession.lsStringCloneSym (stringCloneBudgetSpec M A lim)
  formatInner : HookSat ext lsFormatInnerSym (formatInnerBudgetSpec M A lim)

/-! ## 1. Path B Stage P4 (`M4`) Envelopes, Spatial Entry/Exit & Three-Way Outcome (`StageP4MatchedBranchPlaced`) -/

/-- Allocation envelope on the `save_identity = Err` path of matched-session Stage P4:
`SaveStepEnv` (`save_identity` shim + poll + `Box` dealloc) followed by `FreeOnlyEvs`
(`drop_glue<SessionStructure>` + `pt` buffer dealloc). -/
def StageP4MatchedSaveErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (remoteIk : IdentityKey) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk) FreeOnlyEvs

/-- Allocation envelope on the `save_identity = Ok` (`store_session = Ok` or `Err`) path of
matched-session Stage P4: `SaveStepEnv` followed by `StoreStepEnv` followed by `FreeOnlyEvs`
(coroutine `SessionStructure` / `previous_sessions` / `pt` teardown deallocations). -/
def StageP4MatchedStoreStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (rem : AddrVal) (remoteIk : IdentityKey) (ss : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (StoreStepEnv kit kitEnv sst0 rem ⟨some ss⟩) FreeOnlyEvs)

/-- Full Stage-P4 matched-path allocation envelope covering both `saveErr` and `ok`/`storeErr`. -/
def StageP4MatchedEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (rem : AddrVal) (remoteIk : IdentityKey) (ss : Session (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  StageP4MatchedSaveErrEnv ikit ikitEnv ist0 rem remoteIk evs ∨
    StageP4MatchedStoreStepEnv kit kitEnv ikit ikitEnv sst0 ist0 rem remoteIk ss evs

theorem fitsEnv_saveErr_of_matched {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {rem : AddrVal} {remoteIk : IdentityKey} {ss : Session (List (BitVec 8))}
    (h : FitsEnv M lim st (StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 rem remoteIk ss)) :
    FitsEnv M lim st (StageP4MatchedSaveErrEnv ikit ikitEnv ist0 rem remoteIk) :=
  h.mono (fun _ he => Or.inl he)

theorem fitsEnv_storeStep_of_matched {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {rem : AddrVal} {remoteIk : IdentityKey} {ss : Session (List (BitVec 8))}
    (h : FitsEnv M lim st (StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 rem remoteIk ss)) :
    FitsEnv M lim st (StageP4MatchedStoreStepEnv kit kitEnv ikit ikitEnv sst0 ist0 rem remoteIk ss) :=
  h.mono (fun _ he => Or.inr he)

/-- Shared spatial resources across `P4.1` (`save_identity`) and `P4.4` (`store_session`) on
matched-session Path B (`opkIdIsSome = 2#32`, skipping `P4.2` and `P4.3`) under
`[LibsignalPlacement]`, indexing stack offsets at `s.sp` and evaluating `A.pool` at `s_pool`. -/
def stageP4MatchedSharedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) :
    SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0xb8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xc0#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
  ((coroPtr + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
  ((coroPtr + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2ac#64) 8 ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x340#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  FromRecordCallees.lsLogOff ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (stageP4MatchedCallStack kit ikit)

theorem stageP4MatchedSharedPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) :
    stageP4MatchedSharedPlaced A lim st kit ikit s0 s s_pool
      coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
      pt peer remoteIk =
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP4MatchedSharedPlaced
      (retagSessionStore (A' := A.atState lim st s_pool) kit)
      (retagIdentityStore (A' := A.atState lim st s_pool) ikit)
      s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
      pt peer remoteIk :=
  rfl

/-- Spatial precondition at `+0x34dc` for matched-session Path B Stage P4 (`M4`) under
`[LibsignalPlacement]`. -/
def stageP4MatchedPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (g : RecordGhost) (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MatchedSharedPlaced A lim st0 kit ikit s0 s s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk ∗
  prevSessionsEmptyAt A.repAlloc coroPtr g ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.repAlloc.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0 ∗
  kit.storeAt sessionStorePtr sst0

theorem stageP4MatchedPrePlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (g : RecordGhost) (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) :
    stageP4MatchedPrePlaced A lim st0 kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
      sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
      opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ssSt =
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP4MatchedPrePlaced
      (retagSessionStore (A' := A.atState lim st0 s) kit)
      (retagIdentityStore (A' := A.atState lim st0 s) ikit)
      s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
      sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
      opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ssSt :=
  rfl

/-- Spatial postcondition at `s0.readReg64.x30` for matched-session Path B Stage P4 (`M4`)
under `[LibsignalPlacement]`, indexing stack offsets at `s.sp` and evaluating `A.pool` at `sf`. -/
def stageP4MatchedExitAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 s sf : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (outSlot : SepProp) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey)
    (sstf : kit.StoreState) (istf : ikit.IdState) : SepProp :=
  stageP4MatchedSharedPlaced A lim stf kit ikit s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk ∗
  outSlot ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr istf ∗
  kit.storeAt sessionStorePtr sstf

theorem stageP4MatchedExitAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 s sf : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (outSlot : SepProp) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey)
    (sstf : kit.StoreState) (istf : ikit.IdState) :
    stageP4MatchedExitAtPlaced A lim stf kit ikit s0 s sf
      coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
      outSlot pt peer remoteIk sstf istf =
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP4MatchedExitAtPlaced
      (retagSessionStore (A' := A.atState lim stf sf) kit)
      (retagIdentityStore (A' := A.atState lim stf sf) ikit)
      s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
      outSlot pt peer remoteIk sstf istf :=
  rfl

/-- Budget-threaded three-way outcome classification of matched-session Path B Stage P4 under
`[LibsignalPlacement]`. -/
inductive StageP4MatchedBranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop where
  | ok (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4MatchedStoreStepEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()))
      (hpost : Pf ⊢ stageP4MatchedExitAtPlaced A lim (M.stepEvents evs st0) kit ikit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (vecResultAt A.repAlloc outPtr (.ok pt))
        pt peer remoteIk
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)))
  | saveErr (evs : List AllocEvent)
      (hevs : StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4MatchedExitAtPlaced A lim (M.stepEvents evs st0) kit ikit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (savePollPlacedOutAt outPtr (.error ()))
        pt peer remoteIk sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())))
  | storeErr (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4MatchedStoreStepEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()))
      (hpost : Pf ⊢ stageP4MatchedExitAtPlaced A lim (M.stepEvents evs st0) kit ikit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (storePollPlacedOutAt outPtr (.error ()))
        pt peer remoteIk
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)))

theorem StageP4MatchedBranchPlaced.exists_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ} {b : BitVec 64}
    {kit : SessionStoreSpec A.repAlloc b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64}
    {opkHi kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (hb : StageP4MatchedBranchPlaced A lim st0 kit kitEnv ikit ikitEnv encRecord s0 s
      coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
      pt peer remoteIk sst0 ist0 ss sf Pf) :
    ∃ evs, StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss evs := by
  cases hb with
  | ok _ evs hevs _ _ _ _ => exact ⟨evs, Or.inr hevs⟩
  | saveErr evs hevs _ _ _ => exact ⟨evs, Or.inl hevs⟩
  | storeErr _ evs hevs _ _ _ _ => exact ⟨evs, Or.inr hevs⟩

/-- Budget-threaded relocatable `[LibsignalPlacement]` Path B Stage P4
(`+0x34dc → s0.readReg64.x30`, `M4`) contract on `dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` for
`cliPollSessKitPlaced` and `cliPollIdKitPlaced` (`onPanic = fun _ _ => False`). -/
def StageP4MatchedPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 Slots.scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    ∀ (kitEnv : SessionStoreBudgetEnv kit) (ikitEnv : IdentityStoreBudgetEnv ikit),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
        (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv) →
      ∀ (st_b : M.σ) (s0 s : State)
        (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
         kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
        (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
        (remoteIk : IdentityKey) (sst0 : kit.StoreState) (ist0 : ikit.IdState)
        (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))),
        SessionExtraRel G ss → kit.RecOk ⟨some ss⟩ →
        kit.addrOk peer.val → ikit.addrOk peer.val →
        FitsEnv M lim st_b
          (StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss) →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
        FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
        StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
        s.pc = dpPollEntryPlaced + 0x34dc#64 → s.status = .Running →
        (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
        s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
        s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
        s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
        calleeSavedVRegs s = calleeSavedVRegs s0 →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
          (stageP4MatchedPrePlaced A lim st_b kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
            remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
            opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss.state)
          (fun sf Pf =>
            Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
            sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
            StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
            StageP4MatchedBranchPlaced A lim st_b kit kitEnv ikit ikitEnv E2E.Record.encodeRecord
              s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
              kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
              pt peer remoteIk sst0 ist0 ss sf Pf)
          (fun _ _ => False)

/-! ## 2. Path A 4-Kit Stage P4 Envelopes, Spatial Entry/Exit & Five-Way Outcome (`StageP4BranchPlaced`) -/

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
    (id : BitVec 32) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv pkKit.removeBoxSize)
    (SeqEnv (pkKitEnv.removePollEnv pst0 id)
      (· = rustDeallocEvents pkKit.removeBoxSize 8))

/-- Optional `remove_pre_key` step envelope over `opkId? : Option (BitVec 32)`. -/
def OptRemoveStepEnv {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b)
    (pkKitEnv : PreKeyStoreBudgetEnv pkKit) (pst0 : pkKit.PkState)
    (opkId? : Option (BitVec 32)) : List AllocEvent → Prop :=
  match opkId? with
  | none => (· = [])
  | some opkId => RemoveStepEnv pkKit pkKitEnv pst0 opkId

/-- Allocation envelope on the `save_identity = Err` arm of 4-kit Stage P4. -/
def StageP4PathASaveErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (remoteIk : IdentityKey) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk) FreeOnlyEvs

/-- Allocation envelope on the `mark_kyber_pre_key_used = Err` arm of 4-kit Stage P4. -/
def StageP4PathAMarkErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey) FreeOnlyEvs)

/-- Allocation envelope on the `remove_pre_key = Err` arm (`opkId? = some opkId`) of 4-kit Stage P4. -/
def StageP4PathARemoveErrEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (SeqEnv (RemoveStepEnv pkKit pkKitEnv pst0 opkId) FreeOnlyEvs))

/-- Allocation envelope on the `store_session` (`ok` or `storeErr`) arm of 4-kit Stage P4. -/
def StageP4PathAStoreStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (baseKey : PublicKey) (ss : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (SeqEnv (OptRemoveStepEnv pkKit pkKitEnv pst0 opkId?)
        (SeqEnv (StoreStepEnv kit kitEnv sst0 rem ⟨some ss⟩) FreeOnlyEvs)))

/-- Full 4-kit Stage-P4 allocation envelope covering all five branches (`saveErr`, `markErr`,
`removeErr`, `storeErr`, and `ok`). -/
def StageP4PathAEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (baseKey : PublicKey) (ss : Session (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  StageP4PathASaveErrEnv ikit ikitEnv ist0 rem remoteIk evs ∨
    StageP4PathAMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0 rem remoteIk
      kyberPreKeyId signedPreKeyId baseKey evs ∨
    (match opkId? with
     | none => False
     | some opkId =>
       StageP4PathARemoveErrEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
         ist0 pst0 kst0 rem remoteIk opkId kyberPreKeyId signedPreKeyId baseKey evs) ∨
    StageP4PathAStoreStepEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      sst0 ist0 pst0 kst0 rem remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss evs

/-- Shared spatial resources preserved across all of 4-kit Stage P4 (`+0x34dc → s0.readReg64.x30`)
under `[LibsignalPlacement]`, indexing stack offsets at `s.sp` and evaluating `A.pool` at `s_pool`. -/
def stageP4SharedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey) : SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0xb0#64) ↦₆₄ pkKit.pk_vt) ∗
  ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xd0#64) ↦₆₄ kpkKit.kpk_vt) ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x2e0#64) 36 ∗
  memRegion (s.sp + 0x310#64) 36 ∗
  memRegion (s.sp + 0x340#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  FromRecordCallees.lsLogOff ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (stageP4CallStack kit ikit pkKit kpkKit)

theorem stageP4SharedPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey) :
    stageP4SharedPlaced A lim st kit ikit pkKit kpkKit s0 s s_pool
      coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
      kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey =
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP4SharedPlaced
      (retagSessionStore (A' := A.atState lim st s_pool) kit)
      (retagIdentityStore (A' := A.atState lim st s_pool) ikit)
      (retagPreKeyStore (A' := A.atState lim st s_pool) pkKit)
      (retagKyberPreKeyStore (A' := A.atState lim st s_pool) kpkKit)
      s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
      kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey :=
  rfl

/-- Full 4-kit Stage P4 entry assertion at `+0x34dc` parameterized by an `opkSlot` assertion
at `coroPtr + 0x298..0x2a0` under `[LibsignalPlacement]`. -/
def stageP4RawPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4SharedPlaced A lim st0 kit ikit pkKit kpkKit s0 s s coroPtr msgPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
    ptCap ptPtr v_3d0 kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  opkSlot ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.repAlloc.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0 ∗
  kpkKit.storeAt kyberStorePtr kst0 ∗
  pkKit.storeAt preKeyStorePtr pst0 ∗
  kit.storeAt sessionStorePtr sst0

theorem stageP4RawPrePlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) :
    stageP4RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s
      coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
      opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
      sst0 ist0 pst0 kst0 G ssSt =
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP4RawPrePlaced
      (retagSessionStore (A' := A.atState lim st0 s) kit)
      (retagIdentityStore (A' := A.atState lim st0 s) ikit)
      (retagPreKeyStore (A' := A.atState lim st0 s) pkKit)
      (retagKyberPreKeyStore (A' := A.atState lim st0 s) kpkKit)
      s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
      opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
      sst0 ist0 pst0 kst0 G ssSt :=
  rfl

/-- Full 4-kit Stage P4 entry assertion at `+0x34dc` over `opkId? : Option (BitVec 32)`. -/
abbrev stageP4PrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
    ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?) kyberPreKeyId signedPreKeyId b_2c0 pt
    peer remoteIk baseKey sst0 ist0 pst0 kst0 G ssSt

/-- Exit spatial assertion common to all five Stage P4 outcomes under `[LibsignalPlacement]`,
indexing stack offsets at `s.sp` and evaluating `A.pool` at `sf`. -/
def stageP4ExitAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s sf : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot outSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey)
    (sstf : kit.StoreState) (istf : ikit.IdState)
    (pstf : pkKit.PkState) (kstf : kpkKit.KpkState) : SepProp :=
  stageP4SharedPlaced A lim stf kit ikit pkKit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
    ptCap ptPtr v_3d0 kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  opkSlot ∗
  outSlot ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr istf ∗
  kpkKit.storeAt kyberStorePtr kstf ∗
  pkKit.storeAt preKeyStorePtr pstf ∗
  kit.storeAt sessionStorePtr sstf

theorem stageP4ExitAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s sf : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot outSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey)
    (sstf : kit.StoreState) (istf : ikit.IdState)
    (pstf : pkKit.PkState) (kstf : kpkKit.KpkState) :
    stageP4ExitAtPlaced A lim stf kit ikit pkKit kpkKit s0 s sf
      coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
      opkSlot outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
      sstf istf pstf kstf =
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP4ExitAtPlaced
      (retagSessionStore (A' := A.atState lim stf sf) kit)
      (retagIdentityStore (A' := A.atState lim stf sf) ikit)
      (retagPreKeyStore (A' := A.atState lim stf sf) pkKit)
      (retagKyberPreKeyStore (A' := A.atState lim stf sf) kpkKit)
      s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
      opkSlot outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
      sstf istf pstf kstf :=
  rfl

/-- Budget-threaded five-way outcome branches of Stage P4 (`+0x34dc → s0.readReg64.x30`)
parameterized by an `opkSlot` assertion at `coroPtr + 0x298..0x2a0` under `[LibsignalPlacement]`. -/
inductive StageP4RawBranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp) (opkId? : Option (BitVec 32))
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop where
  | ok (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4PathAStoreStepEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 peer.val remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | saveErr (evs : List AllocEvent)
      (hevs : StageP4PathASaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)
  | markErr (c : IdentityChange) (e : kpkKit.MarkErr) (evs : List AllocEvent)
      (hevs : StageP4PathAMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0 peer.val remoteIk
        kyberPreKeyId signedPreKeyId baseKey evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot (speErrAt kpkKit.markErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))
  | removeErr (opkId : BitVec 32) (c : IdentityChange) (e : pkKit.RemoveErr) (evs : List AllocEvent)
      (hopk : opkId? = some opkId)
      (hevs : StageP4PathARemoveErrEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        ist0 pst0 kst0 peer.val remoteIk opkId kyberPreKeyId signedPreKeyId baseKey evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : pkKit.removeRel pst0 opkId (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        pkKit.removeEvs opkId (.error e))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot (speErrAt pkKit.removeErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (pkKit.removeUpdate pst0 opkId (.error e))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | storeErr (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4PathAStoreStepEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 peer.val remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()))
      (hpost : Pf ⊢ stageP4ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))

/-- Unified budget-threaded `StageP4BranchPlaced` over `coroOpkIdAtP4 coroPtr opkId?`. -/
abbrev StageP4BranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop :=
  StageP4RawBranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
    encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
    opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf

theorem StageP4RawBranchPlaced.exists_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ} {b : BitVec 64}
    {kit : SessionStoreSpec A.repAlloc b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {pkKit : PreKeyStoreSpec A.repAlloc b} {pkKitEnv : PreKeyStoreBudgetEnv pkKit}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64}
    {opkSlot : SepProp} {opkId? : Option (BitVec 32)}
    {kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey} {baseKey : PublicKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (hb : StageP4RawBranchPlaced A lim st0 kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
      preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkSlot opkId?
      kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf) :
    ∃ evs, StageP4PathAEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
      sst0 ist0 pst0 kst0 peer.val remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss evs := by
  cases hb with
  | ok _ evs hevs _ _ _ _ _ _ => exact ⟨evs, Or.inr (Or.inr (Or.inr hevs))⟩
  | saveErr evs hevs _ _ _ => exact ⟨evs, Or.inl hevs⟩
  | markErr _ _ evs hevs _ _ _ _ => exact ⟨evs, Or.inr (Or.inl hevs)⟩
  | removeErr opkId _ _ evs hopk hevs _ _ _ _ _ =>
    refine ⟨evs, Or.inr (Or.inr (Or.inl ?_))⟩
    rw [hopk]; exact hevs
  | storeErr _ evs hevs _ _ _ _ _ _ => exact ⟨evs, Or.inr (Or.inr (Or.inr hevs))⟩

/-- Budget-threaded relocatable `[LibsignalPlacement]` Path A 4-kit Stage P4
(`+0x34dc → s0.readReg64.x30`) contract on `dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` for the placed
CLI 4-kit bundle (`onPanic = fun _ _ => False`). -/
def StageP4PathAPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc F0 Slots.scopeKit peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc F0 peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk σ
    ∀ (kitEnv : SessionStoreBudgetEnv kit) (ikitEnv : IdentityStoreBudgetEnv ikit)
      (pkKitEnv : PreKeyStoreBudgetEnv pkKit) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
        (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv) →
      ∀ (st_b : M.σ) (s0 s : State)
        (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
         preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
        (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
        (b_2c0 : BitVec 8) (pt : List (BitVec 8))
        (remoteIk : IdentityKey) (baseKey : PublicKey)
        (sst0 : kit.StoreState) (ist0 : ikit.IdState)
        (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
        (G : SessionGhost) (ss : Session (List (BitVec 8))),
        prevStatesPtr ≠ 0#64 →
        SessionExtraRel G ss → kit.RecOk ⟨some ss⟩ →
        kit.addrOk peer.val → ikit.addrOk peer.val →
        kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
        (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
        FitsEnv M lim st_b
          (StageP4PathAEnv kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
            sst0 ist0 pst0 kst0 peer.val remoteIk opkId? kyberPreKeyId signedPreKeyId baseKey ss) →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
        FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
          (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s →
        StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
        s.pc = dpPollEntryPlaced + 0x34dc#64 → s.status = .Running →
        (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
        s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
        s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
        s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
        calleeSavedVRegs s = calleeSavedVRegs s0 →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
          (stageP4PrePlaced A lim st_b kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
            prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt
            peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss.state)
          (fun sf Pf =>
            Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s sf ∧
            sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
            StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
            StageP4BranchPlaced A lim st_b kit kitEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
              E2E.Record.encodeRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
              sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr
              v_3d0 opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
              sst0 ist0 pst0 kst0 ss sf Pf)
          (fun _ _ => False)

/-! ## 3. Path B Stage P2 Envelopes & Statement (`StageP2MatchedCliPlacedStmt`) -/

/-- Allocation envelope on the matched-identity (`sess.state.remoteIdentity = some y.g.msg.identityKey`)
branch of Path B Stage P2 (`+0x0868 → +0x1778`): `PublicKey::serialize` (`33` B, align `1`)
followed by deallocation of the temporary serialized base-key slice (`33` B, align `1`). -/
def StageP2MatchedMatchEnv : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 33 1) (· = rustDeallocEvents 33 1)

/-- Allocation envelope on the remote-identity mismatch (`sess.state.remoteIdentity ≠ some y.g.msg.identityKey`)
branch of Path B Stage P2 (`+0x0868 → s0.readReg64.x30`): `PublicKey::serialize` (`33` B, align `1`),
temporary slice deallocation (`33` B, align `1`), `strToOwnedLocal2` (`14`-byte `"bad ciphertext"`,
align `1`), and `SessionRecord` drop (`FreeOnlyEvs`). -/
def StageP2MatchedMismatchEnv : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 33 1)
    (SeqEnv (· = rustDeallocEvents 33 1)
      (SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs))

/-- Combined Path B Stage-P2 allocation envelope covering both `hmatch` and `hmismatch`. -/
def StageP2MatchedEnv (evs : List AllocEvent) : Prop :=
  StageP2MatchedMatchEnv evs ∨ StageP2MatchedMismatchEnv evs

theorem fitsEnv_match_of_stageP2Matched {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st StageP2MatchedEnv) :
    FitsEnv M lim st StageP2MatchedMatchEnv :=
  h.mono (fun _ he => Or.inl he)

theorem fitsEnv_mismatch_of_stageP2Matched {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st StageP2MatchedEnv) :
    FitsEnv M lim st StageP2MatchedMismatchEnv :=
  h.mono (fun _ he => Or.inr he)

/-- Budget-threaded relocatable `[LibsignalPlacement]` CPS Stage P2 contract for Path B
(`opt = some ⟨some sess⟩`) at `dpPollEntryPlaced + 0x0868#64`, eliminating Stage-P2 OOM panics and
threading `Qpan` exclusively from the `hmatch` Stage-P3 continuation. -/
def StageP2MatchedCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {st_b : M.σ}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv) →
    FitsEnv M lim st_b StageP2MatchedEnv →
    SessMatchesPm sess y.g.msg →
    StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    rootStack ≤ sp.toNat →
    s1.pc = dpPollEntryPlaced + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (hmismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
        StageP2MatchedMismatchEnv evs →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
        sf.sp = s0.sp → sf.trace = s1.trace →
        ClosureCalleeSaved s0 sf → calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          apiDecResultAt A.repAlloc y.out
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          coinsInstalledPlaced y.g.coinsP y.g.coins ∗
          LsTokenInit ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt sp rootStack) →
        Q sf Pf) →
    (hmatch : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ (evs : List AllocEvent) (s2 : State) (g : RecordGhost) (recG : SessionGhost)
        (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
        (preKeyMsgRem : SepProp)
        (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        StageP2MatchedMatchEnv evs →
        SessionExtraRel recG sess →
        (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ⊢
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
        s2.pc = dpPollEntryPlaced + 0x1778#64 →
        s2.status = .Running →
        s2.sp = sp →
        (s2.sp &&& 15#64 == 0#64) = true →
        s2.trace = s1.trace →
        s2.readReg64 .x19 = y.fut →
        s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = s0.sp - 0x60#64 →
        calleeSavedVRegs s2 = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
        SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
          (LsTokenInit ∗
           LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.genP3Pre_placed
             A lim (M.stepEvents evs st_b) s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
             whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
             recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
           stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 ∗
           stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
             (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
             (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
             (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
             (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
             (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
              ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
              memRegion (y.fut + 0x2a8#64) 4) ∗
           stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
           ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
           preKeyMsgRem)
          Q Qpan) →
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Scope A.repAlloc y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp rootStack)
      Q Qpan

/-! ## 4. Path A Stage P2 Statement (`StageP2PathACliPlacedStmt`) & Combined `ClosureStagesPlacedStmt` -/

/-- Combined Path A Stage-P2 allocation envelope over `P2PathAErrEnv` and `P2PathAOkEnv`. -/
def StageP2PathAEnv (P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  P2PathAErrEnv g evs ∨ P2PathAOkEnv g evs

/-- Budget-threaded outcome of the 6 Stage P2 error exits on Path A (`+0x0868 → s0.readReg64.x30`)
under `[LibsignalPlacement]`. -/
inductive StageP2PathAErrPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (P2PathAErrEnv : DecPkGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop where
  | reject (err : ApiError AddrVal Unit) (evs : List AllocEvent)
      (hevs : P2PathAErrEnv y.g evs)
      (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
      (htr : sf.trace = s1.trace)
      (hmodel : decPkDef X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
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

/-- Budget-threaded relocatable `[LibsignalPlacement]` CPS Stage P2 contract for Path A
(`opt = none`, `DecPkOk₀`) at `dpPollEntryPlaced + 0x0868#64`, eliminating Stage-P2 OOM panics and
threading `Qpan` exclusively from the `hok` Stage-P3 continuation. -/
def StageP2PathACliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {st_b : M.σ}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q Qpan : State → SepProp → Prop),
    RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv) →
    FitsEnv M lim st_b (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) →
    DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 →
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
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      StageP2PathAErrPlaced A lim st_b P2PathAErrEnv X W B S Scope y s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (evs : List AllocEvent) (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      P2PathAOkEnv y.g evs →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 s2 →
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
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2
        (LsTokenInit ∗
         LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.genP3Pre_placed
           A lim (M.stepEvents evs st_b) s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
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
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Scope A.repAlloc y.fut none ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores g1 ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B))
      Q Qpan

/-- Combined bundle of budget-threaded stage contracts under `[LibsignalPlacement]`. -/
structure ClosureStagesPlacedStmt [LibsignalPlacement] : Prop where
  stageP1Ok : StageP1OkPlacedStmt
  stageP1Untrusted : StageP1UntrustedPlacedStmt
  stageP2Matched : StageP2MatchedCliPlacedStmt
  stageP3PrevEmpty : StageP3PrevEmptyVRegsPlacedStmt
  stageP4Matched : StageP4MatchedPlacedStmt
  stageP2PathA : StageP2PathACliPlacedStmt
  stageP3Gen : StageP3GenStepsVRegsPlacedStmt
  stageP4PathA : StageP4PathAPlacedStmt

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
