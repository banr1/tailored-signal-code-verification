/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailSymPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Seam States for the `segPreKey` Tail (`+0x8b4` and `+0x8c8`)

Defines `PreKeyEncryptState'Budget` and `PreKeyEncryptRetStateBudget` on Block `464`
(`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlacedBudget

/-- Budget-threaded state at `+0x8b4` (`encEntryPlaced + 2228#64`), right after `bl kyberMap` returns. -/
def PreKeyEncryptState'Budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (items : PendingPreKey)
    (R0 : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromPreKeyEncEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items) ∧
  PreKeyEncryptState'Placed (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 ctl encRecord
    x r sess otr taken pqCap pqPtr k items R0 s0 s

/-- Budget-threaded state at `+0x8c8` (`encEntryPlaced + 2248#64`), right after `bl OTR::encrypt` returns. -/
def PreKeyEncryptRetStateBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (items : PendingPreKey)
    (R0 : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromPreKeyRetEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items) ∧
  PreKeyEncryptRetStatePlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 C ctl parse S encRecord
    x r sess otr taken pqCap pqPtr k items R0 s0 s

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget
