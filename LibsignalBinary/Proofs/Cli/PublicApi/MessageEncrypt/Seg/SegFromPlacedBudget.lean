/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable CLI `SegFrom` Proof (`segFrom_placed_okV_budget`)

Verifies `SegFromSpecVBudget` (`CurStateVBudget` at `+0x20c` → `OtrStateVBudget` at `+0x2c8` or
error tail at `+0x49c`) on `lsProg_464 Hk` (`blkPl_464`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom hiding curState_placed_mem_unpack fromRestFramePlaced okStepFramePlaced otrFrom_placed_err_tail_mem otrFrom_placed_err_unpack otrFrom_placed_ok_pack otrFrom_placed_ok_unpack otrFrom_placed_post_unpack otrFrom_placed_pre_frame
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.HKDF
open CryptoGames.HMAC
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace TempTwins

export LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget (PreKeyMsgNewEnv)
export LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins (
  LoadStepEnv StoreStepEnv FromCurEnv
  timeAddBudgetSpec sessionMemcpyRegionBudgetSpec
  kitLoadShimBudgetSpec kitStoreShimBudgetSpec
  kitLoadPollBudgetSpecS kitLoadPollBudgetSpecSE
  kitStorePollBudgetSpec kitStorePollBudgetSpecE
  SessionOnlyKitBudgetOkSE
  otrFromRawBudgetSpec otrApplyBudgetSpec kyberMapBudgetSpec
  preKeyMsgNewBudgetSpec dropSessionStructureLocal2BudgetSpec
)

def durationSinceBoundedBudgetSpec : Spec (BitVec 64 × BitVec 64) :=
  { durationSinceBoundedSpec with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ durationSinceBoundedSpec.post x s0 sf }

def CurStateVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromCurEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 Scope x) ∧
  CurStateVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r g sess R s0 s

def StoredStateVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (c : IdentityChange) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st FreeOnlyEvs ∧
  StoredStateVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' c R s0 s

structure EncCalleesFullBudget [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (H : LibsignalHooks) : Prop
    extends EncCalleesBudget Q C A lim ctl parse S sendEnv H where
  otrFrom : subroutine_ok (lsProg_464 H) (lsmpl.base 19)
    (StoreKit.withLsRoCl lsmpl (otrFromRawBudgetSpec M A lim))
  otrApply : subroutine_ok (lsProg_464 H) (lsmpl.base 20)
    (StoreKit.withLsRoCl lsmpl (otrApplyBudgetSpec M A lim))
  kyber : subroutine_ok (lsProg_464 H) (lsmpl.base 430)
    (StoreKit.withLsRoCl lsmpl (kyberMapBudgetSpec M A lim))
  psmNew : subroutine_ok (lsProg_464 H) (lsmpl.base 41)
    (StoreKit.withLsRoCl lsmpl (preKeyMsgNewBudgetSpec M A lim))
  dropSs : subroutine_ok (lsProg_464 H) (lsmpl.base 442)
    (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim))

structure EncEnvFullBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop
    extends EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H where
  kitOk : SessionOnlyKitBudgetOkSE A lim kit kitEnv Scope encRecord H
  calleesFull : EncCalleesFullBudget Q C A lim ctl parse S sendEnv H
  timeAddVm : HookSat H CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsTimeAddSym
    (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet timeAddBudgetSpec)
  durationSinceVm : HookSat H CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsDurationSinceSym
    (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
      durationSinceBoundedBudgetSpec)
  memcpyVm : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec
  tailWriteResult :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit)
      (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
      (bs : List (BitVec 8)) (Hp : SepProp),
      TailModel kit st0 ikit ist0 C S parse encRecord x answers res s0 s →
      ResStaged A.repAlloc x.ret res [w0, w1, w2, w3] bs Hp →
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
        (encEntryPlaced + 0x5f8#64)
        (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
          s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
        (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
          memRegion (sp + 0x578#64) 0x608 ∗ Hp) R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun _ => False)
  tailWriteErr :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp),
      TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
      SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
        (encEntryPlaced + 0x5b4#64) (tailRegs w0 w1 w2)
        (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ Hp) R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun _ => False)
  tailFreePrevSessions :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (prevCap prevPtr : BitVec 64),
      TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
      SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
        (encEntryPlaced + 0x564#64) (tailRegs w0 w1 w2)
        (fun sp => memRegion sp 0x58 ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ Hp) R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun _ => False)
  tailFromSessionStateErr :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (g : RecordGhost)
      (rec : SessionRecord (List (BitVec 8))),
      TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
      SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
        (encEntryPlaced + 0x49c#64)
        (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
          s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
        (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ Hp) R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun _ => False)
  tailPreKeyEncryptErr :
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
        (kyPtr : BitVec 64) (kp : Option KyberPayload),
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + 0xc38#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
              (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A.repAlloc (sp + 0x8a0#64) kyPtr kp ∗
                memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
                memRegion (sp + 0xb18#64) 0x68) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)

def SegLoadSpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
      EncFsCtxPlaced kit ikit H s0 s0 →
      s0.pc = encEntryPlaced → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨
        (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord).pre
          (x, st_init) s0 ∗ R) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s0
        (fun s => ∃ st' r g sess,
          CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r g sess R s0 s)

def SegFromSpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (g : RecordGhost) (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r g sess R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st' otr taken pqCap pqPtr,
          OtrStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken pqCap pqPtr R s0 s')

def SegPreKeySpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey.isSome →
      KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken pqCap pqPtr k R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st' m otr' pqCap' pqPtr',
          CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R s0 s')

def SegApplyStoreSpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
      (c : IdentityChange) (R : SepProp) (s0 s : State),
      kit.addrOk x.rem.val →
      EncFsCtxPlaced kit ikit H s0 s →
      ApplyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken k m otr' pqCap' pqPtr' c R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s
        (fun s' => ∃ st',
          StoredStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
            x st_init st' r sess otr taken k m otr' c R s0 s')

def SegFinishSpecVBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H →
    ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
      (s0 s : State),
      StoredStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord
        x st_init st r sess otr taken k m otr' c R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun _ => False)

end TempTwins

open TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom (curState_placed_mem_unpack fromRestFramePlaced okStepFramePlaced otrFrom_placed_err_tail_mem otrFrom_placed_err_unpack otrFrom_placed_ok_pack otrFrom_placed_ok_unpack otrFrom_placed_post_unpack otrFrom_placed_pre_frame)



attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem model_of_fromSessionState_error_placed
    {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {e : SignalProtocolError}
    (hcur : r.currentSession = some sess)
    (herr : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error e) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (.protocol e), [.loadSession x.rem.val]) ∧
    x.draws S (okAnswers r .newOrUnchanged) = 0 := by
  have hex : execOk OutgoingTripleRatchet.fromSessionState sess.state = .error e :=
    execOk_fromSessionState_of_error_shared_lb herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (fromSessionState_error_ne_invalidState_shared_lb herr).2
  have hmod : x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol okAnswers
    simp [hcur, hex, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ExceptT.run, StateT.run, bind, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      StateT.bind, StateT.map, Functor.map, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, pure, ExceptT.pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw]
  refine ⟨by rw [hmod, hprot], ?_⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession okAnswers
  simp only [hcur, hex]

/-! ## Budget-Threaded `SegFrom` Steppers & Main Proof (`segFrom_placed_okV_budget`) -/

theorem segFrom_placed_step_pre_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp u280 : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x20c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx21 : s.readReg64 .x21 = sp + 0x128#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (lsProg_464 Hk) (lsmpl.base 19) s ((sp + 0x280#64) ↦₆₄ u280)
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 0x58#64 ∧
        sm.readReg64 .x21 = sp + 0x580#64 ∧
        sm.readReg64 .x24 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = sp + 0x9d0#64 ∧
        sm.readReg64 .x27 = sp + 0xc0#64 ∧
        sm.readReg64 .x28 = sp + 0x4a0#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 Reg.lr = encEntryPlaced + 0x228#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))) := by
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    wp_done)

theorem segFrom_placed_step_err_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x49c#64) s ((sp + 0x580#64) ↦₆₄ errTag)
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ (sp + 0x580#64) ↦₆₄ errTag)) := by
  unfold encEntryPlaced at hs_pc ⊢
  unfold errTag
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    wp_done)

set_option maxHeartbeats 1600000 in
theorem segFrom_placed_step_ok_vm [LibsignalPlacement] {Hk : LibsignalHooks} {sp : BitVec 64}
    {pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
      BitVec 64}
    {u850 u858 u860 u950 u958 u960 : BitVec 64} {u469 : BitVec 8} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx27 : s.readReg64 .x27 = sp + 0xc0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hpq : pqCap + 1#64 ≠ 0#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x2c8#64) s
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24 ∗
        ((sp + 0x469#64) ↦₈ u469) ∗
        otrWords25 (sp + 0x580#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗ ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x950#64) ↦₆₄ u950) ∗ ((sp + 0x958#64) ↦₆₄ u958) ∗ ((sp + 0x960#64) ↦₆₄ u960))
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 0x58#64 ∧
        sm.readReg64 .x22 = sp + 0x8b8#64 ∧
        sm.readReg64 .x23 = sp + 0x58#64 ∧
        sm.readReg64 .x24 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = sp + 0x9d0#64 ∧
        sm.readReg64 .x27 = sp + 0xc0#64 ∧
        sm.readReg64 .x28 = sp + 0x4a0#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          otrWords25 (sp + 0x288#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗
          otrWords25 (sp + 0x580#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6) ∗
          ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6))) := by
  have hpq_beq : (pqCap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hpq
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true, otrWords25]
  by_vm_steps (
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    wp_done)

private theorem fromRestFramePlaced_atState [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st1 st2 : M.σ) (s1 s2 : State) :
    fromRestFramePlaced ss_vt id_vt (A.atState lim st1 s1) =
      fromRestFramePlaced ss_vt id_vt (A.atState lim st2 s2) := rfl

private theorem speStaged_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    SpeStaged (A.atState lim st s) = SpeStaged A.repAlloc := rfl

private theorem sessionRecordAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    sessionRecordAt (A.atState lim st s) = sessionRecordAt A.repAlloc := rfl

private theorem otrAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st1 st2 : M.σ) (s1 s2 : State) :
    otrAt (A.atState lim st1 s1) = otrAt (A.atState lim st2 s2) := rfl

private theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagSessionStore (A' := A') kit).storeFinal st0 ans cs = kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ ans cs

private theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs = ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ ans cs

private theorem encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8))))
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A') kit)
      ((retagSessionStore (A' := A') kit).storeFinal st0 ans cs)
      (retagIdentityStore (A' := A') ikit)
      ((retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs) x s0 =
    encStoreExtraPlaced kit (kit.storeFinal st0 ans cs)
      ikit (ikit.idFinal ist0 ans cs) x s0 := by
  have hs := storeFinal_retag (A' := A') kit st0 ans cs
  have hi := idFinal_retag (A' := A') ikit ist0 ans cs
  have hfn :
      ∀ (st : kit.StoreState) (ist : ikit.IdState),
        encStoreExtraPlaced (retagSessionStore (A' := A') kit) st
          (retagIdentityStore (A' := A') ikit) ist x s0 =
        encStoreExtraPlaced kit st ikit ist x s0 := fun _ _ => rfl
  exact (hfn _ _).trans (by rw [hs, hi])

private theorem encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) =
    (slotsP ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) := by
  have hext := encStoreExtraPlaced_final_retag (A' := A') kit st0 ikit ist0 answers
    (x.model C S uuidTryParse answers).2 x s0
  have hvt :
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

theorem segFrom_placed_okV [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegFromSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk := by
  intro env x st_init st r g sess R0 s0 s hcurState
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hcurState with ⟨hbud0, hcur, hsc, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx21, hx25, hx26, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hs_pc' : s.pc = encEntryPlaced + 0x20c#64 := hs_pc
  have hsc' : kit.ScopeAt Scope st0 x.rem.val r := hsc
  have htr' : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) := htr
  obtain ⟨G, u280, _, hpure, hm_unp⟩ :=
    curState_placed_mem_unpack (A.atState lim st s) ctl x r g sess sp R s0 hsp0 hcur hm
  refine SegExitBudget.of_sepWP (R0 := R0) hm_unp
    (segFrom_placed_step_pre_vm hs_pc' hrun hsp hal hx20 hx21 hx25 hx26 hx28) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x21, hs1_x24, hs1_x25, hs1_x26,
      hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hAs1 : A.atState lim st s = A.atState lim st s1 :=
    (A.atState_eq_of_vmPreserved lim st hvm01).symm
  rw [hAs1] at hm1
  have hm1_pre := otrFrom_placed_pre_frame (A.atState lim st s1) ctl x g G sess sp R Pm1 s0 s1
    hcrl1 hs1_sp hs1_x0 hs1_x8 hPm1 hm1
  refine SegExitBudget.call (R0 := R0) env.calleesFull.otrFrom
    (⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩, st)
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (otrFromRawBudgetSpec M A lim)).onExit
          (⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩, st) code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpan_post => by
      rw [show (StoreKit.withLsRoCl lsmpl (otrFromRawBudgetSpec M A lim)).onPanic
          (⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩, st) s1 sf = ⌜False⌝ from rfl,
          sepConj_assoc, satisfies_pure_sepConj] at hpan_post
      exact hpan_post.1.elim)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x20 : s2.readReg64 .x20 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x26 : s2.readReg64 .x26 = sp + 0x9d0#64 := by reg_chain
  have hs2_x27 : s2.readReg64 .x27 = sp + 0xc0#64 := by reg_chain
  have hs2_x28 : s2.readReg64 .x28 = sp + 0x4a0#64 := by reg_chain
  dsimp only [StoreKit.withLsRoCl, otrFromRawBudgetSpec] at hpost2
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost2
  obtain ⟨evs, hpost2⟩ := hpost2
  have hpost2_pull : s2.mem ⊨ ⌜FreeOnlyEvs evs⌝ ∗
      (((StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec
            (A.atState lim (M.stepEvents evs st) s2))).post
          ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ s1 s2 ∗
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          fromRestFramePlaced kit.ss_vt ikit.id_vt (A.atState lim (M.stepEvents evs st) s2)
            ctl x g sp s0)) ∗ R) := by
    rw [← fromRestFramePlaced_atState kit.ss_vt ikit.id_vt A lim st (M.stepEvents evs st) s1 s2]
    dsimp only [StoreKit.withLsRoCl]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost2
  rw [satisfies_pure_sepConj] at hpost2_pull
  rcases hpost2_pull with ⟨hevs, hpost2_rocl⟩
  set st2 := M.stepEvents evs st
  have hbud2 := hbud0.advance hevs
  obtain ⟨hcrl2, G', _, hs2_tr, hm2⟩ :=
    otrFrom_placed_post_unpack (A.atState lim st2 s2) ctl x g G sess
      ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
      sp R s0 s1 s2 rfl hsp0 hs1_sp hpure hpost2_rocl
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr')
  rcases hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 with p | otr
  · change s2.mem ⊨ otrResultAt (A.atState lim st2 s2) (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w0, w1, w2, w3, w4, w5, H, hst, hm2_err⟩ :=
      otrFrom_placed_err_unpack (A.atState lim st2 s2) ctl x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 p sp R s0 s2 hres hm2
    rw [speStaged_atState A lim st2 s2] at hst
    refine SegExitBudget.of_sepWP (R0 := R0) hm2_err
      (segFrom_placed_step_err_vm hs2_pc hs2_run hs2_sp' hs2_al) ?_
    intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hvm23, hs3_sp, hs3_tr, hs3_x19, hs3_x21, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
    have hs3_al : s3.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hAs23 : A.atState lim st2 s2 = A.atState lim st2 s3 :=
      (A.atState_eq_of_vmPreserved lim st2 hvm23).symm
    rw [hAs23] at hm3
    have ⟨hmod_res, hdraws0⟩ := model_of_fromSessionState_error_placed (C := C) (S := S)
      (x := x) hcur hres
    have hm3_tail := otrFrom_placed_err_tail_mem (A.atState lim st2 s3) ctl x
      { g with cur := some G' } sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 w0 w1 w2 w3 w4 w5 sp H R Pm3
      s0 s3 hPm3 hm3
    rw [sessionRecordAt_atState A lim st2 s3] at hm3_tail
    refine SegExitBudget.of_false (env.tailFromSessionStateErr x st_init st2 R0 s0 s3
      (okAnswers r .newOrUnchanged)
      (.protocol p) w0 w1 w2 w3 w4 w5 H { g with cur := some G' }
      (takenRecord sess (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2)
      ?_ hst ?_)
    · refine ⟨⟨by rw [hmod_res], by rw [hmod_res]; exact ⟨hsc'.2, trivial⟩, by rw [hmod_res]; trivial⟩, ?_⟩
      rw [hs3_tr, hs2_tr', hmod_res]
      dsimp only [okAnswers]
      rw [ikit.traceOfWith_load]
    · refine ⟨hbud2.narrow (fun _ => Or.inl),
        hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
        by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
        ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩, hstk, ?_⟩
      rw [encTail_mem_retag_eq (A' := A.atState lim st2 s3) kit st0 ikit ist0 C ctl S x
        (okAnswers r .newOrUnchanged) _ R0 s0]
      rw [hdraws0, hmod_res]
      exact hm3_tail
  · change s2.mem ⊨ otrResultAt (A.atState lim st2 s2) (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
      w19, w20, w21, w22, w23, w24,
      d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24,
      u850, u858, u860, u950, u958, u960, H, hpq, hpack, hm2_ok⟩ :=
      otrFrom_placed_ok_unpack (A.atState lim st2 s2) ctl x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr sp R s0 s2 hm2
    refine SegExitBudget.of_sepWP (R0 := R0) hm2_ok
      (segFrom_placed_step_ok_vm hs2_pc hs2_run hs2_sp' hs2_al hs2_x20 hs2_x24 hs2_x25 hs2_x26 hs2_x27
        hs2_x28 hpq) ?_
    intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hvm23, hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25,
        hs3_x26, hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
    have hs3_al : s3.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hAs23 : A.atState lim st2 s2 = A.atState lim st2 s3 :=
      (A.atState_eq_of_vmPreserved lim st2 hvm23).symm
    rw [hAs23] at hm3
    rw [otrAt_atState A lim st2 st2 s2 s3] at hpack
    have hm3_ok := otrFrom_placed_ok_pack (A.atState lim st2 s3) ctl x { g with cur := some G' } G.pq sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
      sp H R Pm3 s0 s3 hpack hPm3 hm3
    refine SegExitBudget.next
      ⟨st2, otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
        G.pq.cap, G.pq.ptr,
        hbud2.narrow (fun _ h =>
          Or.inr ⟨r, sess, otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
            hsc', hcur, execOk_fromSessionState_of_ok_shared_lb hres, h⟩),
        hcur, hsc', execOk_fromSessionState_of_ok_shared_lb hres, ?_⟩
    exact ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
      by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
      hs3_tr.trans hs2_tr',
      ⟨hs3_x0, hs3_x8, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25, hs3_x26, hs3_x27, hs3_x28⟩,
      hpt, hrest, hloc, hnow, hstk, hm3_ok⟩


end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
