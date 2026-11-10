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
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrustAux
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Stage P1 Interfaces

Defines Stage P1 allocation envelopes (`StageP1OkEnv`, `StageP1UntrustedEnv`) and budget-threaded
`[LibsignalPlacement]` Stage P1 interfaces (`StageP1OkPlacedStmt` and `StageP1UntrustedPlacedStmt`)
on `dpPollProgPlaced ext` at `dpPollEntryPlaced` (`lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust (trustCallStack)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (dpPollEntryPlaced dpPollProgPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv stringCloneBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (LoadStepEnv SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)

/-- Stage P1 trusted-path (`is_trusted_identity =.ok true`) allocation envelope:
`load_session` step followed by `is_trusted_identity` step. -/
def StageP1OkEnv {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    (peer : AddrVal) (remoteIdKey : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (LoadStepEnv kit kitEnv st peer)
    (TrustStepEnv ikit ikitEnv ist peer remoteIdKey .receiving)

/-- Stage P1 untrusted-path (`is_trusted_identity =.ok false`) allocation envelope:
`load_session` step, `is_trusted_identity` step, `String::clone` of `peer.name`, and record drop. -/
def StageP1UntrustedEnv {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    (peer : AddrGhost) (remoteIdKey : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (LoadStepEnv kit kitEnv st peer.val)
    (SeqEnv (TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving)
      (SeqEnv (StringCloneEnv peer.name) FreeOnlyEvs))

/-- Budget-threaded relocatable `[LibsignalPlacement]` counterpart of `StageP1OkPlacedStmt`. -/
def StageP1OkPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st : kit.StoreState} {ist : ikit.IdState} {st_b : M.σ}
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    AllocContractsXCliPlaced A lim ext →
    SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord ext →
    IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext →
    stageP1CallStack kit ikit ≤ 2 ^ 64 →
    extHookStack ≤ loadCallStack kit →
    extHookStack ≤ trustCallStack ikit →
    kit.addrOk peer.val →
    ikit.addrOk peer.val →
    (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
    (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok true) →
    FitsEnv M lim st_b (StageP1OkEnv kit kitEnv st ikit ikitEnv ist peer.val remoteIdKey) →
    ∀ (s0 : State)
      (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
       sessStorePtr idStorePtr
       preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
       kyberStorePtr kyberStoreVt rngPtr
       v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
      (b_390 b_4f2 : BitVec 8),
      StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem →
      FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
        (dpPollProgPlaced ext) s0 →
      s0.pc = dpPollEntryPlaced →
      s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.sp - 0xcd0#64 = sp →
      s0.readReg64 .x0 = outPtr →
      s0.readReg64 .x1 = coroPtr →
      s0.readReg64 .x2 = ctxPtr →
      SepWPp (dpPollProgPlaced ext)
        (dpPollEntryPlaced + 0x868#64) s0
        (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
           sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
           preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
           kyberStorePtr kyberStoreVt rngPtr ∗
         cells (coroPtr + 0x70#64) 14 ∗
         cells (coroPtr + 0xe0#64) 4 ∗
         memRegion (coroPtr + 0x100#64) 336 ∗
         ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
         cells (coroPtr + 0x2c8#64) 25 ∗
         ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
         ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
         cells (coroPtr + 0x428#64) 8 ∗
         cells (coroPtr + 0x490#64) 4 ∗
         ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         (sp ↦₆₄ v_sp0) ∗
         ((sp + 0x98#64) ↦₆₄ u_98) ∗
         ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
         ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
         ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (sp + 0xd8#64) 348 ∗
         memRegion (sp + 0x3e0#64) 368 ∗
         cells (s0.sp - 0x60#64) 12 ∗
         FromRecordCallees.lsLogOff ∗
         kit.storeAt sessStorePtr st ∗
         ikit.identityAt idStorePtr ist ∗
         protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
         ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
         A.pool lim st_b s0 ∗
         stackAt sp (stageP1CallStack kit ikit))
        (fun sf P_f =>
          (∃ opt : Option (SessionRecord (List (BitVec 8))), ∃ evs : List AllocEvent,
            StageP1OkEnv kit kitEnv st ikit ikitEnv ist peer.val remoteIdKey evs ∧
            kit.loadRel st peer.val (.ok opt) ∧
            ikit.trustRel ist peer.val remoteIdKey .receiving (.ok true) ∧
            sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
              ikit.trustEvs peer.val remoteIdKey .receiving (.ok true) ∧
            (P_f ⊢
              ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
                decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                  preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                  kyberStorePtr kyberStoreVt rngPtr ∗
                decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                  preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                  kyberStorePtr kyberStoreVt rngPtr ∗
                p1LoadedRecordAt Scope A.repAlloc coroPtr opt ∗
                ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
                processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                  spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
                processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                  spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
                ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
                cells (coroPtr + 0x398#64) 2 ∗
                ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
                (sp ↦₆₄ 0#64) ∗
                ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
                ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
                ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
                ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
                ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
                ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
                ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
                memRegion (sp + 0xd8#64) 348 ∗
                memRegion (sp + 0x3e0#64) 368 ∗
                decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
                FromRecordCallees.lsLogOff ∗
                kit.storeAt sessStorePtr st ∗
                ikit.identityAt idStorePtr
                  (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok true)) ∗
                protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
                ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
                A.pool lim (M.stepEvents evs st_b) sf ∗
                stackAt sp (stageP1CallStack kit ikit))) ∧
          sf.sp = sp ∧
          sf.readReg64 .x8 = kyberStorePtr ∧
          sf.readReg64 .x9 = msgPtr ∧
          sf.readReg64 .x10 = kyberStoreVt ∧
          sf.readReg64 .x11 = preKeyStorePtr ∧
          sf.readReg64 .x12 = remoteAddrPtr ∧
          sf.readReg64 .x13 = preKeyStoreVt ∧
          sf.readReg64 .x14 = localAddrPtr ∧
          sf.readReg64 .x15 = idStorePtr ∧
          sf.readReg64 .x16 = ikit.id_vt ∧
          sf.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
          sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
          sf.readReg64 .x22 = spkStorePtr ∧
          sf.readReg64 .x23 = coroPtr + 0xe0#64 ∧
          sf.readReg64 .x24 = spkStoreVt ∧
          sf.readReg64 .x25 = sp + 0x210#64 ∧
          sf.readReg64 .x28 = sp + 0xa90#64 ∧
          sf.readReg64 .x29 = s0.sp - 0x60#64 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
        (fun _ _ => False)

/-- Budget-threaded relocatable `[LibsignalPlacement]` counterpart of `StageP1UntrustedPlacedStmt`. -/
def StageP1UntrustedPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st : kit.StoreState} {ist : ikit.IdState} {st_b : M.σ}
    (peer : AddrGhost) (remoteIdKey : IdentityKey),
    AllocContractsXCliPlaced A lim ext →
    HookSat ext stringCloneHookName (stringCloneBudgetSpec M A lim) →
    SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord ext →
    IdentityStoreKitPlacedOkI A lim ikit ikitEnv ext →
    stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 →
    extHookStack ≤ loadCallStack kit →
    kit.addrOk peer.val →
    ikit.addrOk peer.val →
    (∀ ans, kit.loadRel st peer.val ans → ans.isOk = true) →
    (∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false) →
    FitsEnv M lim st_b (StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey) →
    ∀ (s0 : State)
      (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
       sessStorePtr idStorePtr
       preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
       kyberStorePtr kyberStoreVt rngPtr
       v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
      (b_390 : BitVec 8),
      StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem →
      FsAt (fun F => kit.envOk F ∧ ikit.envOk F) (kit.Quiet ∧ ikit.Quiet)
        (dpPollProgPlaced ext) s0 →
      s0.pc = dpPollEntryPlaced →
      s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true →
      s0.sp - 0xcd0#64 = sp →
      s0.readReg64 .x0 = outPtr →
      s0.readReg64 .x1 = coroPtr →
      s0.readReg64 .x2 = ctxPtr →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s0
        (decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
           sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
           preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
           kyberStorePtr kyberStoreVt rngPtr ∗
         cells (coroPtr + 0x70#64) 14 ∗
         cells (coroPtr + 0xe0#64) 4 ∗
         memRegion (coroPtr + 0x100#64) 336 ∗
         cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
         cells (coroPtr + 0x2c8#64) 25 ∗
         ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
         ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
         (sp ↦₆₄ v_sp0) ∗
         ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
         ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (sp + 0xd8#64) 348 ∗
         memRegion (sp + 0x370#64) 36 ∗
         memRegion (sp + 0x3e0#64) 368 ∗
         cells (sp + 0xa90#64) 6 ∗
         cells (s0.sp - 0x60#64) 12 ∗
         memRegion outPtr 48 ∗
         FromRecordCallees.lsLogOff ∗
         kit.storeAt sessStorePtr st ∗
         ikit.identityAt idStorePtr ist ∗
         protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
         ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
         A.pool lim st_b s0 ∗
         stackAt sp (stageP1UntrustedCallStack kit ikit))
        (fun sf P_f =>
          (∃ opt : Option (SessionRecord (List (BitVec 8))), ∃ evs : List AllocEvent,
            StageP1UntrustedEnv kit kitEnv st ikit ikitEnv ist peer remoteIdKey evs ∧
            kit.loadRel st peer.val (.ok opt) ∧
            ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
            sf.trace = s0.trace ++ kit.loadEvs encRecord peer.val (.ok opt) ++
              ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
            (P_f ⊢
              ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
                decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                  preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                  kyberStorePtr kyberStoreVt rngPtr ∗
                decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  sessStorePtr kit.ss_vt idStorePtr ikit.id_vt
                  preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
                  kyberStorePtr kyberStoreVt rngPtr ∗
                memRegion (coroPtr + 0xe0#64) 368 ∗
                cells (coroPtr + 0x250#64) 6 ∗
                ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
                processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
                  idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
                  spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
                ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
                cells (coroPtr + 0x398#64) 2 ∗
                (sp ↦₆₄ 0#64) ∗
                ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
                ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
                ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
                ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
                ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
                memRegion (sp + 0xd8#64) 348 ∗
                memRegion (sp + 0x370#64) 36 ∗
                memRegion (sp + 0x3e0#64) 368 ∗
                cells (sp + 0xa90#64) 6 ∗
                decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
                apiDecResultAt A.repAlloc outPtr (.error (.untrustedIdentity peer.val)) ∗
                FromRecordCallees.lsLogOff ∗
                kit.storeAt sessStorePtr st ∗
                ikit.identityAt idStorePtr
                  (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
                protocolAddressAt A.repAlloc peer remoteAddrPtr ∗
                ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
                A.pool lim (M.stepEvents evs st_b) sf ∗
                stackAt sp (stageP1UntrustedCallStack kit ikit))) ∧
          sf.sp = s0.sp ∧
          ClosureCalleeSaved s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
        (fun _ _ => False)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
