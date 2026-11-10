/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1MarkPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1RemovePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1SaveIdPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P4 Over-Path Bundles, Envelopes, and `+0x3cc` Wrapper

Defines budget-threaded `[LibsignalPlacement]` 4-kit spatial bundles, allocation envelopes
(`StageP4Prev1StepEnv`, `StageP4Prev1ExitEnv`), and the five-way outcome classification
`StageP4Prev1BranchPlaced` over a 1-element `prevVecAt [enc]`, and proves the Substage P4.4 wrapper
at `+0x3cc`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  IdentityStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk
  PreKeyStoreKitPlacedOk SessionOnlyKitPlacedOkSE
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  stageP4SaveIdSharedPlaced stageP4SaveIdPrePlaced
  stageP4SaveIdOkPostPlaced stageP4SaveIdErrPostPlaced
  stageP4_saveIdentity_dispatch_vregs_kits_placed
  stageP4MarkKyberSharedPlaced stageP4MarkKyberPrePlaced
  stageP4MarkKyberOkPostPlaced stageP4MarkKyberErrPostPlaced
  KyberPreKeyMarkKitPlacedOk kyberPreKeyMarkKitPlacedOk_of_store
  stageP4RemovePreKeySharedPlaced stageP4RemovePreKeyPrePlaced
  stageP4RemovePreKeyOkPostPlaced stageP4RemovePreKeyErrPostPlaced
  PreKeyRemoveKitPlacedOk preKeyRemoveKitPlacedOk_of_store
  stageP4StoreSessionSharedPlaced stageP4StoreSessionPrePlaced
  stageP4StoreSessionOkPostPlaced stageP4StoreSessionErrPostPlaced
  stageP4_storeSession_dispatch_vregs_kits_placed
  stageP4SharedPlaced stageP4RawPrePlaced stageP4PrePlaced stageP4ExitAtPlaced
  StageP4RawBranchPlaced StageP4BranchPlaced
  stageP4At3ccPrePlaced stageP4_at_3cc_vregs_kits_placed
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (storeSessionVtablesPlacedAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  StorePrev1Ops prevVecAt
)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv SaveStepEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  PreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefusedPlacedBudget (
  StageP4KyberRefusedMarkErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProofPlacedBudget (
  MarkStepEnv StageP4MarkErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlacedBudget (
  StageP4RemoveBranchErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlacedBudget (
  RemoveStepEnv StageP4RemoveErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlacedBudget (
  StageP4MatchedSaveErrEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrPlacedBudget (
  dpClosureEntryP34Placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlacedBudget (
  SessionPrev1KitPlacedOkSE StageP4StorePrev1ExitEnv StorePrev1BudgetEnv StorePrev1StepEnv
  stageP4StoreSessionPrev1ErrPostPlaced stageP4StoreSessionPrev1OkPostPlaced
  stageP4StoreSessionPrev1PrePlaced stageP4StoreSessionPrev1SharedPlaced
  stageP4_storeSession_prev1_vregs_kits_p4_placed
)

/-! ## Placed 4-Kit Spatial Bundles -/

/-- Budget-threaded placed shared spatial resources preserved across Stage P4
(`+0x34dc → s0.readReg64 .x30`). -/
def stageP4Prev1SharedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s s_pool : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
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
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool lim st s_pool ∗
  stackAt s.sp (stageP4CallStack kit ikit pkKit kpkKit)

/-- Budget-threaded placed Stage P4 entry assertion at `+0x34dc` parameterized by `opkSlot`. -/
def stageP4Prev1RawPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4Prev1SharedPlaced A lim st0 kit ikit pkKit kpkKit s0 s s coroPtr msgPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ssSt ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  opkSlot ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0 ∗
  kpkKit.storeAt kyberStorePtr kst0 ∗
  pkKit.storeAt preKeyStorePtr pst0 ∗
  kit.storeAt sessionStorePtr sst0

/-- Budget-threaded placed Stage P4 entry assertion at `+0x34dc` over `opkId? : Option (BitVec 32)`. -/
abbrev stageP4Prev1PrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
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
    (G : SessionGhost) (ssSt : SessionState (List (BitVec 8))) : SepProp :=
  stageP4Prev1RawPrePlaced A lim st0 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
    remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
    prevCap prevPtr ptCap ptPtr v_3d0 (coroOpkIdAtP4 coroPtr opkId?)
    kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
    sst0 ist0 pst0 kst0 G ssSt

/-- Budget-threaded placed Stage P4 assertion at `+0x3cc` entering Substage P4.4 (`store_session`). -/
def stageP4At3ccPrev1PrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st3 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s s3 : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4Prev1SharedPlaced A lim st3 kit ikit pkKit kpkKit s0 s s3 coroPtr msgPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  opkSlot ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G ss.state ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist1 ∗
  kpkKit.storeAt kyberStorePtr kst1 ∗
  pkKit.storeAt preKeyStorePtr pst1 ∗
  kit.storeAt sessionStorePtr sst0

/-- Budget-threaded placed exit assertion common to all five Stage P4 outcomes at `s0.readReg64 .x30`. -/
def stageP4Prev1ExitAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ikit : IdentityStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b) (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (s0 s sf : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot outSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey)
    (sstf : kit.StoreState) (istf : ikit.IdState)
    (pstf : pkKit.PkState) (kstf : kpkKit.KpkState) : SepProp :=
  stageP4Prev1SharedPlaced A lim stf kit ikit pkKit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  opkSlot ∗
  outSlot ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr istf ∗
  kpkKit.storeAt kyberStorePtr kstf ∗
  pkKit.storeAt preKeyStorePtr pstf ∗
  kit.storeAt sessionStorePtr sstf

/-! ## Stage P4 Allocation Envelopes and `FitsEnv` Monotonicity -/

/-- Entry allocation envelope for Stage P4 when `opkId? = none`: `SaveStepEnv`, `MarkStepEnv`, and
`StorePrev1StepEnv`. -/
abbrev StageP4Prev1NoneStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (StorePrev1StepEnv kit opsEnv sst0 rem G ss enc))

/-- Entry allocation envelope for Stage P4 parameterized by `opkId? : Option (BitVec 32)`, inserting
`RemoveStepEnv` between `MarkStepEnv` and `StorePrev1StepEnv` when `opkId? = some opkId`. -/
def StageP4Prev1StepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (opkId? : Option (BitVec 32))
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    List AllocEvent → Prop :=
  match opkId? with
  | none =>
      StageP4Prev1NoneStepEnv kit opsEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc
  | some opkId =>
      SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
        (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
          (SeqEnv (RemoveStepEnv pkKit pkKitEnv pst0 opkId)
            (StorePrev1StepEnv kit opsEnv sst0 rem G ss enc)))

/-- Allocation envelope on the `ok` and `storeErr` exits of Stage P4. -/
def StageP4Prev1StoreBranchEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (opkId? : Option (BitVec 32))
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    List AllocEvent → Prop :=
  match opkId? with
  | none =>
      SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
        (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
          (StageP4StorePrev1ExitEnv kit opsEnv sst0 rem G ss enc))
  | some opkId =>
      SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
        (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
          (SeqEnv (RemoveStepEnv pkKit pkKitEnv pst0 opkId)
            (StageP4StorePrev1ExitEnv kit opsEnv sst0 rem G ss enc)))

/-- Combined exit allocation envelope of Stage P4 when `opkId? = none`. -/
def StageP4Prev1NoneExitEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (kst0 : kpkKit.KpkState)
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist0 rem remoteIk)
    (SeqEnv (MarkStepEnv kpkKit kpkKitEnv kst0 kyberPreKeyId signedPreKeyId baseKey)
      (StageP4StorePrev1ExitEnv kit opsEnv sst0 rem G ss enc)) evs ∨
  StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
    rem remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∨
  StageP4MatchedSaveErrEnv ikit ikitEnv ist0 rem remoteIk evs

/-- Combined exit allocation envelope of Stage P4 parameterized by `opkId? : Option (BitVec 32)`. -/
def StageP4Prev1ExitEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (pkKit : PreKeyStoreSpec A b) (pkKitEnv : PreKeyStoreBudgetEnv pkKit)
    (kpkKit : KyberPreKeyStoreSpec A b) (kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (opkId? : Option (BitVec 32))
    (rem : AddrVal) (remoteIk : IdentityKey)
    (kyberPreKeyId signedPreKeyId : BitVec 32) (baseKey : PublicKey)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  match opkId? with
  | none =>
      StageP4Prev1NoneExitEnv kit opsEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc evs
  | some opkId =>
      StageP4Prev1StoreBranchEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 (some opkId) rem remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc
        evs ∨
      StageP4RemoveBranchErrEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        ist0 pst0 kst0 rem remoteIk opkId kyberPreKeyId signedPreKeyId baseKey evs ∨
      StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        rem remoteIk kyberPreKeyId signedPreKeyId baseKey evs ∨
      StageP4MatchedSaveErrEnv ikit ikitEnv ist0 rem remoteIk evs

theorem fitsEnv_prev1NoneStep_of_noneExit {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {opsEnv : StorePrev1BudgetEnv kit}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {kpkKit : KyberPreKeyStoreSpec A b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState} {kst0 : kpkKit.KpkState}
    {rem : AddrVal} {remoteIk : IdentityKey}
    {kyberPreKeyId signedPreKeyId : BitVec 32} {baseKey : PublicKey}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : FitsEnv M lim st
      (StageP4Prev1NoneExitEnv kit opsEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc)) :
    FitsEnv M lim st
      (StageP4Prev1NoneStepEnv kit opsEnv ikit ikitEnv kpkKit kpkKitEnv
        sst0 ist0 kst0 rem remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc) :=
  h.mono fun
    | _, Or.inl hsave => Or.inl (Or.inl hsave)
    | _, Or.inr ⟨_, _, rfl, hsave, Or.inl hmark⟩ =>
        Or.inl (SeqEnv.append hsave (Or.inl hmark))
    | _, Or.inr ⟨_, _, rfl, hsave, Or.inr ⟨_, _, rfl, hmark, hstore⟩⟩ =>
        Or.inl (SeqEnv.append hsave (SeqEnv.append hmark (Or.inl hstore)))

theorem fitsEnv_prev1Step_of_exit {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {opsEnv : StorePrev1BudgetEnv kit}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {pkKit : PreKeyStoreSpec A b} {pkKitEnv : PreKeyStoreBudgetEnv pkKit}
    {kpkKit : KyberPreKeyStoreSpec A b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {opkId? : Option (BitVec 32)}
    {rem : AddrVal} {remoteIk : IdentityKey}
    {kyberPreKeyId signedPreKeyId : BitVec 32} {baseKey : PublicKey}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : FitsEnv M lim st
      (StageP4Prev1ExitEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? rem remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc)) :
    FitsEnv M lim st
      (StageP4Prev1StepEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? rem remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc) := by
  cases opkId? with
  | none =>
      exact fitsEnv_prev1NoneStep_of_noneExit h
  | some opkId =>
      exact h.mono fun
        | _, Or.inl hsave => Or.inl (Or.inl hsave)
        | _, Or.inr ⟨_, _, rfl, hsave, Or.inl hmark⟩ =>
            Or.inl (SeqEnv.append hsave (Or.inl hmark))
        | _, Or.inr ⟨_, _, rfl, hsave, Or.inr ⟨_, _, rfl, hmark, Or.inl hrem⟩⟩ =>
            Or.inl (SeqEnv.append hsave (SeqEnv.append hmark (Or.inl hrem)))
        | _, Or.inr ⟨_, _, rfl, hsave,
            Or.inr ⟨_, _, rfl, hmark, Or.inr ⟨_, _, rfl, hrem, hstore⟩⟩⟩ =>
            Or.inl (SeqEnv.append hsave (SeqEnv.append hmark (SeqEnv.append hrem (Or.inl hstore))))

/-! ## Placed Five-Way Outcome Classification -/

/-- Budget-threaded placed five-way outcome classification of Stage P4 (`+0x34dc → s0.readReg64 .x30`)
parameterized by `opkSlot`. -/
inductive StageP4Prev1RawBranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ops : StorePrev1Ops kit) (opsEnv : StorePrev1BudgetEnv kit)
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
      (hevs : StageP4Prev1StoreBranchEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc
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
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | saveErr (evs : List AllocEvent)
      (hevs : StageP4MatchedSaveErrEnv ikit ikitEnv ist0 peer.val remoteIk evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)
  | markErr (c : IdentityChange) (e : kpkKit.MarkErr) (evs : List AllocEvent)
      (hevs : StageP4KyberRefusedMarkErrEnv ikit ikitEnv kpkKit kpkKitEnv ist0 kst0
        peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (speErrAt kpkKit.markErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))
  | removeErr (opkId : BitVec 32) (c : IdentityChange) (e : pkKit.RemoveErr)
      (evs : List AllocEvent)
      (hopk : opkId? = some opkId)
      (hevs : StageP4RemoveBranchErrEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        ist0 pst0 kst0 peer.val remoteIk opkId kyberPreKeyId signedPreKeyId baseKey evs)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : pkKit.removeRel pst0 opkId (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        pkKit.removeEvs opkId (.error e))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (speErrAt pkKit.removeErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (pkKit.removeUpdate pst0 opkId (.error e))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | storeErr (c : IdentityChange) (evs : List AllocEvent)
      (hevs : StageP4Prev1StoreBranchEnv kit opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
        sst0 ist0 pst0 kst0 opkId? peer.val remoteIk kyberPreKeyId signedPreKeyId baseKey G ss enc
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
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st0) kit ikit pkKit kpkKit
        s0 s sf coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))

/-- Budget-threaded placed five-way Stage P4 outcome classification over `coroOpkIdAtP4 coroPtr opkId?`. -/
abbrev StageP4Prev1BranchPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) {b : BitVec 64}
    (kit : SessionStoreSpec A.repAlloc b) (ops : StorePrev1Ops kit) (opsEnv : StorePrev1BudgetEnv kit)
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
  StageP4Prev1RawBranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv kpkKit kpkKitEnv
    s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    (coroOpkIdAtP4 coroPtr opkId?) opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
    baseKey sst0 ist0 pst0 kst0 G ss sf Pf

theorem StageP4Prev1RawBranchPlaced.mono_opkSlot [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ} {b : BitVec 64}
    {kit : SessionStoreSpec A.repAlloc b} {ops : StorePrev1Ops kit}
    {opsEnv : StorePrev1BudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {pkKit : PreKeyStoreSpec A.repAlloc b} {pkKitEnv : PreKeyStoreBudgetEnv pkKit}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc b} {kpkKitEnv : KyberPreKeyStoreBudgetEnv kpkKit}
    {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64}
    {opkSlot1 opkSlot2 : SepProp} {opkId? : Option (BitVec 32)}
    {kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt enc : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey} {baseKey : PublicKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (hopk : opkSlot1 ⊢ opkSlot2)
    (h : StageP4Prev1RawBranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
      kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
      idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot1 opkId?
      kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf) :
    StageP4Prev1RawBranchPlaced A lim st0 kit ops opsEnv ikit ikitEnv pkKit pkKitEnv
      kpkKit kpkKitEnv s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr
      idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 opkSlot2 opkId?
      kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf := by
  have hexit : ∀ stf outSlot sstf istf pstf kstf,
      stageP4Prev1ExitAtPlaced A lim stf kit ikit pkKit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot1 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf ⊢
      stageP4Prev1ExitAtPlaced A lim stf kit ikit pkKit kpkKit s0 s sf coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot2 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf :=
    fun _ _ _ _ _ _ => by
      unfold stageP4Prev1ExitAtPlaced
      exact sepConj_mono_right (sepConj_mono_left hopk)
  rcases h with ⟨c, evs, hevs, hs, hm, hr, hst, htr, hp⟩
    | ⟨evs, hevs, hs, htr, hp⟩
    | ⟨c, e, evs, hevs, hs, hm, htr, hp⟩
    | ⟨opkId, c, e, evs, hopk_eq, hevs, hs, hm, hr, htr, hp⟩
    | ⟨c, evs, hevs, hs, hm, hr, hst, htr, hp⟩
  · exact .ok c evs hevs hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _ _))
  · exact .saveErr evs hevs hs htr (Entails.trans hp (hexit _ _ _ _ _ _))
  · exact .markErr c e evs hevs hs hm htr (Entails.trans hp (hexit _ _ _ _ _ _))
  · exact .removeErr opkId c e evs hopk_eq hevs hs hm hr htr (Entails.trans hp (hexit _ _ _ _ _ _))
  · exact .storeErr c evs hevs hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _ _))

/-! ## Budget-Threaded Placed Substage P4.4 Wrapper (`+0x3cc → s0.readReg64 .x30`) -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded placed Substage P4.4 (`store_session`, `+0x3cc → s0.readReg64 .x30`) wrapper on
the 4-kit `stageP4At3ccPrev1PrePlaced` frame under `StorePrev1StepEnv`. -/
theorem stageP4_at_3cc_prev1_vregs_kits_p4_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A.repAlloc 0#64)
    (ops : StorePrev1Ops kit)
    (opsEnv : StorePrev1BudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hkit : SessionPrev1KitPlacedOkSE A lim kit ops opsEnv ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    {Qfs : Prop} {Qp : State → SepProp → Prop}
    (st3 : M.σ) (s0 s s3 : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (hfits : FitsEnv M lim st3 (StorePrev1StepEnv kit opsEnv sst0 peer.val G ss enc))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs3 : FsAt kit.envOk Qfs (lsProg_518 ext) s3)
    (hcro3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem)
    (hpc3 : s3.pc = dpClosureEntryP34Placed + 0x3cc#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hOk : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4StorePrev1ExitEnv kit opsEnv sst0 peer.val G ss enc evs →
      Steps (lsProg_518 ext) s3 sf →
      ops.storeRelPrev1 sst0 peer.val G ss enc (.ok ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ ops.storeEvsPrev1 peer.val G ss enc (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ())) ist1 pst1 kst1) →
      Q sf Pf)
    (hErr : ∀ (evs : List AllocEvent) (sf : State) (Pf : SepProp),
      StageP4StorePrev1ExitEnv kit opsEnv sst0 peer.val G ss enc evs →
      Steps (lsProg_518 ext) s3 sf →
      ops.storeRelPrev1 sst0 peer.val G ss enc (.error ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ ops.storeEvsPrev1 peer.val G ss enc (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ())) ist1 pst1 kst1) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s3
      (stageP4At3ccPrev1PrePlaced A lim st3 kit ikit pkKit kpkKit s0 s s3 coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt enc peer
        remoteIk baseKey sst0 ist1 pst1 kst1 G ss)
      Q Qp := by
  have hsp_ss : storeSessionCallStack kit ≤ 2 ^ 64 :=
    Nat.le_trans (storeSessionStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4StoreSessionPrev1PrePlaced A lim st3 kit s0 s3 coroPtr outPtr remoteAddrPtr
      sessionStorePtr prevCap prevPtr ptCap ptPtr b_2c0 pt enc peer sst0 G ss)
    (by
      unfold stageP4At3ccPrev1PrePlaced stageP4Prev1SharedPlaced
        stageP4StoreSessionPrev1PrePlaced stageP4StoreSessionPrev1SharedPlaced
      rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_storeSession_prev1_vregs_kits_p4_placed ext kit ops opsEnv
    hdealloc hDropSS3 hkit hsVt st3 s0 s3 coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr
    prevCap prevPtr ptCap ptPtr b_2c0 pt enc peer sst0 G ss _ _
    hExtra hrec_ok haddr_ss hfits hpt_le hcap_lt hptr_nz hsp_ss
    hfs3 hcro3 hpc3 hrun3 hsp3_align
    hx19_3 (hsp3.symm ▸ hx24_3) (hsp3.symm ▸ hx25_3) hx26_3 hx27_3 hvregs3
    (fun evs sf Pf hevs4 hst4 hrel4 _ _ hspf htr4 hcsf hvregsf hcrof hPf => ?_)
    (fun evs sf Pf hevs4 hst4 hrel4 _ _ hspf htr4 hcsf hvregsf hcrof hPf => ?_)
  · refine ⟨storeSessionVtablesPlacedAt kit,
      stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (vecResultAt A.repAlloc outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ())) ist1 pst1 kst1,
      ?_, hOk evs sf _ hevs4 hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hvregsf hcrof
        (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionPrev1OkPostPlaced stageP4StoreSessionPrev1SharedPlaced
      stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    sep_ac_rfl
  · refine ⟨storeSessionVtablesPlacedAt kit,
      stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs st3) kit ikit pkKit kpkKit s0 s sf
        coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
        kyberStorePtr ptCap ptPtr v_3d0 opkSlot
        (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ())) ist1 pst1 kst1,
      ?_, hErr evs sf _ hevs4 hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hvregsf hcrof
        (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionPrev1ErrPostPlaced stageP4StoreSessionPrev1SharedPlaced
      stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    sep_ac_rfl

abbrev stageP4_at_3cc_prev1_vregs_kits_placed := @stageP4_at_3cc_prev1_vregs_kits_p4_placed

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
