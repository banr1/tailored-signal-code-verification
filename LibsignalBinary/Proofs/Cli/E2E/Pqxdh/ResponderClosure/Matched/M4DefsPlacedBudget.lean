/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StepsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StoreStepsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Matched-Session Stage P4: Bundles and Statement

Defines the matched-session Stage P4 (`opkIdIsSome = 2#32`) allocation envelopes
(`StageP4MatchedSaveErrEnv`, `StageP4MatchedStoreStepEnv`, `StageP4MatchedEnv`), budget-threaded
spatial bundles, three-way outcome `StageP4MatchedBranchPlaced`, and `StageP4MatchedPlacedStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey SessionState)
open CryptoGames.LibsignalSessionApi (IdentityChange Session SessionRecord)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost protocolAddressAt sessionStateAt vecResultAt
)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt IdentityStoreSpec IdentityVtablesPlacedOk LibsignalCodeRoLoaded
  SessionOnlyVtablesPlacedOk SessionStoreSpec
  savePollPlacedOutAt storePollPlacedOutAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (ClosureCalleeSavedP4)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (SessionExtraRel)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  prevSessionsEmptyAt stageP4MatchedCallStack
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv SaveStepEnv retagIdentityStore
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  SessionStoreBudgetEnv StoreStepEnv retagSessionStore
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)

/-! ## Matched-session Stage P4 allocation envelopes -/

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
    FitsEnv M lim st
      (StageP4MatchedStoreStepEnv kit kitEnv ikit ikitEnv sst0 ist0 rem remoteIk ss) :=
  h.mono (fun _ he => Or.inr he)

theorem fitsEnv_saveStep_of_matched {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {rem : AddrVal} {remoteIk : IdentityKey} {ss : Session (List (BitVec 8))}
    (h : FitsEnv M lim st (StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 rem remoteIk ss)) :
    FitsEnv M lim st (SaveStepEnv ikit ikitEnv ist0 rem remoteIk) :=
  (fitsEnv_saveErr_of_matched h).seq_left

/-! ## Budget-threaded spatial bundles and `atState` bridges -/

/-- Budget-threaded shared spatial resources across `P4.1` (`save_identity`) and `P4.4`
(`store_session`) on matched-session Stage P4 (`opkIdIsSome = 2#32`) under `[LibsignalPlacement]`. -/
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
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (stageP4MatchedCallStack kit ikit)

theorem stageP4MatchedSharedPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) :
    stageP4MatchedSharedPlaced A lim st kit ikit s0 s s coroPtr msgPtr remoteAddrPtr remoteIkPtr
      sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
      opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP4MatchedSharedPlaced
      (retagSessionStore (A' := A.atState lim st s) kit)
      (retagIdentityStore (A' := A.atState lim st s) ikit)
      s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
      sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
      opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk :=
  rfl

/-- Budget-threaded spatial precondition at `+0x34dc` for matched-session Stage P4 under
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
   else A.live ptPtr ptCap.toNat 1 ∗
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
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP4MatchedPrePlaced
      (retagSessionStore (A' := A.atState lim st0 s) kit)
      (retagIdentityStore (A' := A.atState lim st0 s) ikit)
      s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
      sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
      opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ssSt :=
  rfl

/-- Budget-threaded spatial postcondition at `s0.readReg64 .x30` for matched-session Stage P4
under `[LibsignalPlacement]`. -/
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

/-! ## Outcome classification and relocatable statement -/

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

/-- Every branch of `StageP4MatchedBranchPlaced` carries an event trace in `StageP4MatchedEnv`. -/
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

/-- Budget-threaded relocatable `[LibsignalPlacement]` Stage P4
(`(blkPl_518).base + 0x34dc → s0.readReg64 .x30`) statement for `opkIdIsSome = 2#32`
(`onPanic = fun _ _ => False`). -/
def StageP4MatchedPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  ∀ (ext : String → Option (State → State))
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit),
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord (Rust.withPanics ext) →
    SessionOnlyVtablesPlacedOk kit →
    IdentityStoreKitPlacedOkI A lim ikit ikitEnv (Rust.withPanics ext) →
    IdentityVtablesPlacedOk ikit →
    ∀ (st0 : M.σ) (s0 s : State)
      (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
      (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (peer : AddrGhost) (remoteIk : IdentityKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))),
      SessionExtraRel G ss →
      kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      FitsEnv M lim st0
        (StageP4MatchedEnv kit kitEnv ikit ikitEnv sst0 ist0 peer.val remoteIk ss) →
      pt.length ≤ ptCap.toNat →
      ptCap.toNat < 2 ^ 63 →
      ptPtr ≠ 0#64 →
      stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
      FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
        (lsProg_518 (Rust.withPanics ext)) s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = (blkPl_518).base + 0x34dc#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 →
      s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr →
      s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
        (stageP4MatchedPrePlaced A lim st0 kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk
          sst0 ist0 g G ss.state)
        (fun sf Pf =>
          Steps (lsProg_518 (Rust.withPanics ext)) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4MatchedBranchPlaced A lim st0 kit kitEnv ikit ikitEnv encRecord s0 s
            coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
            kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId
            pt peer remoteIk sst0 ist0 ss sf Pf)
        (fun _ _ => False)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
