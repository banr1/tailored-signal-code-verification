/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.PeakBudget.CallSiteFacts
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget

/-!
# Envelope and `FitsEnv` Bridges for W4 `decrypt_prekey`

Connects the concrete budget-threaded store, stage, and call-site envelopes across W4
(`process_prekey` / `decrypt_prekey`) — prekey-store step envelopes (`SpkGet`, `KpkGet`, `KpkMark`,
`PkGet`, `PkRemove`), Stage P1 `.ok`/`.untrusted` bridges, `0`-prev and `prev1` serialization
`OutLarge ≤ Peak` bounds, and `DecPkCallSite` unpackers — to `W4OuterPeakSpec` and
`FitsEnv fineCostModel`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4OuterEnvBridges

open Arm64 ProofLib
open CryptoGames.LibsignalSession (IdentityKey PublicKey ShaCompress)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec
   SessionStoreSpec SignedPreKeyStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost PksmGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_smallMaxReq_eq fineDynIvsOfCum fineStepReserveOfCum)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeOutLarge recordSerializePeak
   serializePrev1OutLarge serializePrev1Peak
   serializeSomeOutLarge serializeSomePeak)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
  (stringClone_phaseCredit_aff stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (W4DecryptPrekeySlotEnv W4DecryptPrekeySlotParams W4SlotR3bEnv
   w4DecryptPrekeySlotDeltaCum w4DecryptPrekeySlotDeltaLive
   w4DecryptPrekeySlotDeltaPeak w4DecryptPrekeySlotMaxReq
   w4DecryptPrekeySlot_live_le_peak w4DecryptPrekeySlot_small_phaseCredit
   w4SlotR3bDeltaCum w4SlotR3bDeltaPeak w4SlotR3bMaxReq
   w4SlotR3b_live_le_peak w4SlotR3b_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (boxDeallocStep_to_w4BoxedStoreStep loadStepEnv_phaseCredit
   phaseCreditSpec_seq_freeOnly_exact trustStepEnv_phaseCredit
   w4BoxedStepCum w4BoxedStepLive w4BoxedStepMaxReq w4BoxedStepPeak
   w4BoxedStoreStep_phaseCredit w4BoxedStoreStep_small_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
  (fineCostModel_wireLowInterceptHyps)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (BoxAllocEnv BoxDeallocEnv PreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (LoadStepEnv SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
  (SignedPreKeyStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.CallSiteFacts (DecPkCallSite decPkCallSite_bounds)

/-! ## 1. `StoreKit` PreKey-Store Step Envelopes -/

/-- Boxed `get_signed_pre_key` step (`BoxAllocEnv → getPollEnv → BoxDeallocEnv`). -/
def SpkGetStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SignedPreKeyStoreSpec A b) (kitEnv : SignedPreKeyStoreBudgetEnv kit)
    (st0 : kit.SpkState) (id : BitVec 32) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.getBoxSize)
    (SeqEnv (kitEnv.getPollEnv st0 id) (BoxDeallocEnv kit.getBoxSize))

/-- Boxed `get_kyber_pre_key` step (`BoxAllocEnv → getPollEnv → BoxDeallocEnv`). -/
def KpkGetStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (st0 : kit.KpkState) (id : BitVec 32) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.getBoxSize)
    (SeqEnv (kitEnv.getPollEnv st0 id) (BoxDeallocEnv kit.getBoxSize))

/-- Boxed `mark_kyber_pre_key_used` step (`BoxAllocEnv → markPollEnv → BoxDeallocEnv`). -/
def KpkMarkStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (st0 : kit.KpkState) (id signedId : BitVec 32) (baseKey : PublicKey) :
    List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.markBoxSize)
    (SeqEnv (kitEnv.markPollEnv st0 id signedId baseKey) (BoxDeallocEnv kit.markBoxSize))

/-- Boxed `get_pre_key` step (`BoxAllocEnv → getPollEnv → BoxDeallocEnv`). -/
def PkGetStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : PreKeyStoreSpec A b) (kitEnv : PreKeyStoreBudgetEnv kit)
    (st0 : kit.PkState) (id : BitVec 32) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.getBoxSize)
    (SeqEnv (kitEnv.getPollEnv st0 id) (BoxDeallocEnv kit.getBoxSize))

/-- Boxed `remove_pre_key` step (`BoxAllocEnv → removePollEnv → BoxDeallocEnv`). -/
def PkRemoveStepEnv {A : RustAlloc} {b : BitVec 64}
    (kit : PreKeyStoreSpec A b) (kitEnv : PreKeyStoreBudgetEnv kit)
    (st0 : kit.PkState) (id : BitVec 32) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.removeBoxSize)
    (SeqEnv (kitEnv.removePollEnv st0 id) (BoxDeallocEnv kit.removeBoxSize))

theorem spkGetStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : SignedPreKeyStoreSpec A b) (kitEnv : SignedPreKeyStoreBudgetEnv kit)
    (st0 : kit.SpkState) (id : BitVec 32) {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.getPollEnv st0 id) c l p r) :
    PhaseCreditSpec M (SpkGetStepEnv kit kitEnv st0 id)
      (w4BoxedStepCum kit.getBoxSize c)
      (w4BoxedStepLive kit.getBoxSize l)
      (w4BoxedStepPeak kit.getBoxSize p)
      (w4BoxedStepMaxReq kit.getBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_phaseCredit hM kit.getBoxSize hpoll)

theorem spkGetStepEnv_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : SignedPreKeyStoreSpec A b) (kitEnv : SignedPreKeyStoreBudgetEnv kit)
    (st0 : kit.SpkState) (id : BitVec 32) {c l p r : Nat}
    (hsz : kit.getBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (kitEnv.getPollEnv st0 id) c l p r) :
    PhaseCreditSpec M (SpkGetStepEnv kit kitEnv st0 id)
      (w4BoxedStepCum kit.getBoxSize c) l p (w4BoxedStepMaxReq kit.getBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_small_phaseCredit hM kit.getBoxSize hsz hpoll)

theorem kpkGetStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (st0 : kit.KpkState) (id : BitVec 32) {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.getPollEnv st0 id) c l p r) :
    PhaseCreditSpec M (KpkGetStepEnv kit kitEnv st0 id)
      (w4BoxedStepCum kit.getBoxSize c)
      (w4BoxedStepLive kit.getBoxSize l)
      (w4BoxedStepPeak kit.getBoxSize p)
      (w4BoxedStepMaxReq kit.getBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_phaseCredit hM kit.getBoxSize hpoll)

theorem kpkGetStepEnv_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (st0 : kit.KpkState) (id : BitVec 32) {c l p r : Nat}
    (hsz : kit.getBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (kitEnv.getPollEnv st0 id) c l p r) :
    PhaseCreditSpec M (KpkGetStepEnv kit kitEnv st0 id)
      (w4BoxedStepCum kit.getBoxSize c) l p (w4BoxedStepMaxReq kit.getBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_small_phaseCredit hM kit.getBoxSize hsz hpoll)

theorem kpkMarkStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (st0 : kit.KpkState) (id signedId : BitVec 32) (baseKey : PublicKey)
    {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.markPollEnv st0 id signedId baseKey) c l p r) :
    PhaseCreditSpec M (KpkMarkStepEnv kit kitEnv st0 id signedId baseKey)
      (w4BoxedStepCum kit.markBoxSize c)
      (w4BoxedStepLive kit.markBoxSize l)
      (w4BoxedStepPeak kit.markBoxSize p)
      (w4BoxedStepMaxReq kit.markBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_phaseCredit hM kit.markBoxSize hpoll)

theorem kpkMarkStepEnv_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (st0 : kit.KpkState) (id signedId : BitVec 32) (baseKey : PublicKey)
    {c l p r : Nat}
    (hsz : kit.markBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (kitEnv.markPollEnv st0 id signedId baseKey) c l p r) :
    PhaseCreditSpec M (KpkMarkStepEnv kit kitEnv st0 id signedId baseKey)
      (w4BoxedStepCum kit.markBoxSize c) l p (w4BoxedStepMaxReq kit.markBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_small_phaseCredit hM kit.markBoxSize hsz hpoll)

theorem pkGetStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : PreKeyStoreSpec A b) (kitEnv : PreKeyStoreBudgetEnv kit)
    (st0 : kit.PkState) (id : BitVec 32) {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.getPollEnv st0 id) c l p r) :
    PhaseCreditSpec M (PkGetStepEnv kit kitEnv st0 id)
      (w4BoxedStepCum kit.getBoxSize c)
      (w4BoxedStepLive kit.getBoxSize l)
      (w4BoxedStepPeak kit.getBoxSize p)
      (w4BoxedStepMaxReq kit.getBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_phaseCredit hM kit.getBoxSize hpoll)

theorem pkGetStepEnv_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : PreKeyStoreSpec A b) (kitEnv : PreKeyStoreBudgetEnv kit)
    (st0 : kit.PkState) (id : BitVec 32) {c l p r : Nat}
    (hsz : kit.getBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (kitEnv.getPollEnv st0 id) c l p r) :
    PhaseCreditSpec M (PkGetStepEnv kit kitEnv st0 id)
      (w4BoxedStepCum kit.getBoxSize c) l p (w4BoxedStepMaxReq kit.getBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_small_phaseCredit hM kit.getBoxSize hsz hpoll)

theorem pkRemoveStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : PreKeyStoreSpec A b) (kitEnv : PreKeyStoreBudgetEnv kit)
    (st0 : kit.PkState) (id : BitVec 32) {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.removePollEnv st0 id) c l p r) :
    PhaseCreditSpec M (PkRemoveStepEnv kit kitEnv st0 id)
      (w4BoxedStepCum kit.removeBoxSize c)
      (w4BoxedStepLive kit.removeBoxSize l)
      (w4BoxedStepPeak kit.removeBoxSize p)
      (w4BoxedStepMaxReq kit.removeBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_phaseCredit hM kit.removeBoxSize hpoll)

theorem pkRemoveStepEnv_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : PreKeyStoreSpec A b) (kitEnv : PreKeyStoreBudgetEnv kit)
    (st0 : kit.PkState) (id : BitVec 32) {c l p r : Nat}
    (hsz : kit.removeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (kitEnv.removePollEnv st0 id) c l p r) :
    PhaseCreditSpec M (PkRemoveStepEnv kit kitEnv st0 id)
      (w4BoxedStepCum kit.removeBoxSize c) l p (w4BoxedStepMaxReq kit.removeBoxSize r) :=
  PhaseCreditSpec.of_imp (fun _ h => boxDeallocStep_to_w4BoxedStoreStep h)
    (w4BoxedStoreStep_small_phaseCredit hM kit.removeBoxSize hsz hpoll)

/-! ## 2. Kit-Level Stage P1 `.ok` and `.untrusted` Bridges -/

/-- Kit-level Stage P1 `.ok` (`LoadStepEnv → TrustStepEnv`) `PhaseCreditSpec`. -/
theorem stageP1OkKit_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b b' : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    (peer : AddrVal) (remoteIdKey : IdentityKey)
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hLoad : PhaseCreditSpec M (kitEnv.loadPollEnv st peer) c₁ l₁ p₁ r₁)
    (hTrust : PhaseCreditSpec M (ikitEnv.trustPollEnv ist peer remoteIdKey .receiving) c₂ l₂ p₂ r₂) :
    let cL := w4BoxedStepCum kit.loadBoxSize c₁
    let lL := w4BoxedStepLive kit.loadBoxSize l₁
    let pL := w4BoxedStepPeak kit.loadBoxSize p₁
    let rL := w4BoxedStepMaxReq kit.loadBoxSize r₁
    let cT := w4BoxedStepCum ikit.trustBoxSize c₂
    let lT := w4BoxedStepLive ikit.trustBoxSize l₂
    let pT := w4BoxedStepPeak ikit.trustBoxSize p₂
    let rT := w4BoxedStepMaxReq ikit.trustBoxSize r₂
    PhaseCreditSpec M
      (SeqEnv (LoadStepEnv kit kitEnv st peer)
        (TrustStepEnv ikit ikitEnv ist peer remoteIdKey .receiving))
      (cL + cT) (lL + lT) (max pL (lL + pT)) (max rL rT) := by
  dsimp only
  exact (loadStepEnv_phaseCredit hM kit kitEnv st peer hLoad).seq
    (trustStepEnv_phaseCredit hM ikit ikitEnv ist peer remoteIdKey .receiving hTrust)

/-- Regime-free kit-level Stage P1 `.untrusted` (`LoadStepEnv → TrustStepEnv → StringCloneEnv → FreeOnlyEvs`) `PhaseCreditSpec`.
-/
theorem stageP1UntrustedKit_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b b' : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    {maxPeerLen c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hLoad : PhaseCreditSpec M (kitEnv.loadPollEnv st peer.val) c₁ l₁ p₁ r₁)
    (hTrust : PhaseCreditSpec M
      (ikitEnv.trustPollEnv ist peer.val remoteIdKey .receiving) c₂ l₂ p₂ r₂)
    (hPeer : peer.name.bytes.length ≤ maxPeerLen) :
    let cL := w4BoxedStepCum kit.loadBoxSize c₁
    let lL := w4BoxedStepLive kit.loadBoxSize l₁
    let pL := w4BoxedStepPeak kit.loadBoxSize p₁
    let rL := w4BoxedStepMaxReq kit.loadBoxSize r₁
    let cT := w4BoxedStepCum ikit.trustBoxSize c₂
    let lT := w4BoxedStepLive ikit.trustBoxSize l₂
    let pT := w4BoxedStepPeak ikit.trustBoxSize p₂
    let rT := w4BoxedStepMaxReq ikit.trustBoxSize r₂
    PhaseCreditSpec M
      (SeqEnv (LoadStepEnv kit kitEnv st peer.val)
        (SeqEnv (TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving)
          (SeqEnv (StringCloneEnv peer.name) FreeOnlyEvs)))
      (cL + cT + (2 * maxPeerLen + 9539))
      (lL + lT + (maxPeerLen + 8195))
      (max pL (lL + max pT (lT + (maxPeerLen + 8195))))
      (max rL (max rT maxPeerLen)) := by
  dsimp only
  have hL := loadStepEnv_phaseCredit hM kit kitEnv st peer.val hLoad
  have hT := trustStepEnv_phaseCredit hM ikit ikitEnv ist peer.val remoteIdKey .receiving hTrust
  have hCl := phaseCreditSpec_seq_freeOnly_exact hM (stringClone_phaseCredit_aff hM hPeer)
  have hTC := hT.seq hCl
  exact (hL.seq hTC).mono (by omega) (by omega) (by omega) (by omega)

/-- Small-regime kit-level Stage P1 `.untrusted` `PhaseCreditSpec`. -/
theorem stageP1UntrustedKit_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b b' : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A b') (ikitEnv : IdentityStoreBudgetEnv ikit) (ist : ikit.IdState)
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    {maxPeerLen c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hLoad : PhaseCreditSpec M (kitEnv.loadPollEnv st peer.val) c₁ l₁ p₁ r₁)
    (hTrust : PhaseCreditSpec M
      (ikitEnv.trustPollEnv ist peer.val remoteIdKey .receiving) c₂ l₂ p₂ r₂)
    (hPeer : peer.name.bytes.length ≤ maxPeerLen)
    (hSmall : maxPeerLen ≤ HasFineReallocCredit.smallMaxReq M) :
    let cL := w4BoxedStepCum kit.loadBoxSize c₁
    let lL := w4BoxedStepLive kit.loadBoxSize l₁
    let pL := w4BoxedStepPeak kit.loadBoxSize p₁
    let rL := w4BoxedStepMaxReq kit.loadBoxSize r₁
    let cT := w4BoxedStepCum ikit.trustBoxSize c₂
    let lT := w4BoxedStepLive ikit.trustBoxSize l₂
    let pT := w4BoxedStepPeak ikit.trustBoxSize p₂
    let rT := w4BoxedStepMaxReq ikit.trustBoxSize r₂
    PhaseCreditSpec M
      (SeqEnv (LoadStepEnv kit kitEnv st peer.val)
        (SeqEnv (TrustStepEnv ikit ikitEnv ist peer.val remoteIdKey .receiving)
          (SeqEnv (StringCloneEnv peer.name) FreeOnlyEvs)))
      (cL + cT + (2 * maxPeerLen + 9539))
      (lL + lT)
      (max pL (lL + max pT lT))
      (max rL (max rT maxPeerLen)) := by
  dsimp only
  have hL := loadStepEnv_phaseCredit hM kit kitEnv st peer.val hLoad
  have hT := trustStepEnv_phaseCredit hM ikit ikitEnv ist peer.val remoteIdKey .receiving hTrust
  have hCl := phaseCreditSpec_seq_freeOnly_exact hM
    (stringClone_phaseCredit_small hM hPeer hSmall)
  have hTC := hT.seq hCl
  exact (hL.seq hTC).mono (by omega) (by omega) (by omega) (by omega)

/-! ## 3. `0`-Prev and `prev1` Session-Serialization `OutLarge ≤ Peak` Lemmas -/

theorem recordSerializeOutLarge_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    recordSerializeOutLarge M g r ≤ recordSerializePeak M g r := by
  unfold recordSerializeOutLarge recordSerializePeak
  cases g.cur <;> cases r.currentSession <;> simp [serializeSomeOutLarge, serializeSomePeak]

theorem serializePrev1OutLarge_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    serializePrev1OutLarge M G sess enc ≤ serializePrev1Peak M G sess enc := by
  unfold serializePrev1OutLarge serializePrev1Peak
  exact Nat.le_add_left _ _

/-! ## 4. `DecPkCallSite` Unpackers and `FitsEnv fineCostModel` Discharges -/

theorem decPkCallSite_peer_name_le_40 {img : Obj.Image} {S : RunSem} {g : RunCall}
    {x : DecPkGhost} (h : DecPkCallSite img S g x) (hpksm : S.pksmParse = pksmParse) :
    x.peer.name.bytes.length ≤ 40 :=
  (decPkCallSite_bounds h hpksm).1

theorem decPkCallSite_me_name_le_40 {img : Obj.Image} {S : RunSem} {g : RunCall}
    {x : DecPkGhost} (h : DecPkCallSite img S g x) (hpksm : S.pksmParse = pksmParse) :
    x.me.name.bytes.length ≤ 40 :=
  (decPkCallSite_bounds h hpksm).2.1

theorem decPkCallSite_wire_lengths_lt_2pow32 {img : Obj.Image} {S : RunSem} {g : RunCall}
    {x : DecPkGhost} (h : DecPkCallSite img S g x) (hpksm : S.pksmParse = pksmParse) :
    x.msg.serialized.length < 2 ^ 32 ∧
    x.msg.message.serialized.length < 2 ^ 32 ∧
    x.msg.message.ciphertext.length < 2 ^ 32 ∧
    x.msg.message.pqRatchet.length < 2 ^ 32 ∧
    ∀ ky, x.msg.kyberPayload = some ky → ky.ciphertext.length < 2 ^ 32 :=
  (decPkCallSite_bounds h hpksm).2.2

/-- Discharges `P.peer.name.bytes.length ≤ 40` in `w4DecryptPrekeySlot_small_phaseCredit` from `DecPkCallSite`.
-/
theorem w4DecryptPrekeySlot_at_decPkCallSite_phaseCredit {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (P : W4DecryptPrekeySlotParams α)
    {img : Obj.Image} {S : RunSem} {g : RunCall} {x : DecPkGhost}
    (hSite : DecPkCallSite img S g x) (hpksm : S.pksmParse = pksmParse)
    (hPeerEq : P.peer = x.peer)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_td l_td p_td r_td ikmCap : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hkpkMark : P.kpkMarkName.length ≤ 64)
    (hold : P.x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec M P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hl_le_p : ∀ y ∈ P.archivedTrials, l_dec y ≤ p_dec)
    (hDec : ∀ y ∈ P.archivedTrials, PhaseCreditSpec M (P.DecEnv y) c_dec (l_dec y) p_dec r_dec)
    (hTrial : ∀ y ∈ P.archivedTrials, PhaseCreditSpec M (P.TrialEnv y) c_tr 0 p_tr r_tr)
    (hDrop : ∀ y ∈ P.archivedTrials, DeallocCreditSpec M (P.DropEnv y) (l_dec y))
    (hPush : PhaseCreditSpec M P.VecPushEnv c_push 0 0 r_push)
    (hTd : PhaseCreditSpec M P.TryDecEnv c_td l_td p_td r_td) :
    let cap := max maxVal fileCap
    PhaseCreditSpec M (W4DecryptPrekeySlotEnv P)
      (w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum c_cur c_dec c_tr c_push c_td ikmCap)
      (w4DecryptPrekeySlotDeltaLive M P cap maxEntries deserLive l_td)
      (w4DecryptPrekeySlotDeltaPeak M P cap maxEntries deserLive deserPeak
        p_cur p_dec p_tr l_td p_td)
      (w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq r_cur r_dec r_tr r_push r_td ikmCap) := by
  have hpeer : P.peer.name.bytes.length ≤ 40 := by
    rw [hPeerEq]
    exact decPkCallSite_peer_name_le_40 hSite hpksm
  exact w4DecryptPrekeySlot_small_phaseCredit hM P
    hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess hdir
    hpeer hkeyName hregName hkpkMark hold hnew hSmall hspqrKey
    hfileCap hdeser hCurTrial hlen4 hl_le_p hDec hTrial hDrop hPush hTd

/-- `FitsEnv fineCostModel` discharge for `W4DecryptPrekeySlotEnv P` from `fineCostModel.init`. -/
theorem w4DecryptPrekeySlot_fitsEnv_fineCostModel {α : Type}
    {lim : BudgetLimits} (P : W4DecryptPrekeySlotParams α)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_td l_td p_td r_td ikmCap : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hkpkMark : P.kpkMarkName.length ≤ 64)
    (hold : P.x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap)
    (hIkmSmall : ikmCap ≤ 135167)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hl_le_p : ∀ y ∈ P.archivedTrials, l_dec y ≤ p_dec)
    (hDec : ∀ y ∈ P.archivedTrials,
      PhaseCreditSpec fineCostModel (P.DecEnv y) c_dec (l_dec y) p_dec r_dec)
    (hTrial : ∀ y ∈ P.archivedTrials,
      PhaseCreditSpec fineCostModel (P.TrialEnv y) c_tr 0 p_tr r_tr)
    (hDrop : ∀ y ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv y) (l_dec y))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hTd : PhaseCreditSpec fineCostModel P.TryDecEnv c_td l_td p_td r_td)
    (henf : lim.enforced = true)
    (hram :
      let cap := max maxVal fileCap
      let cumB := w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum
        c_cur c_dec c_tr c_push c_td ikmCap
      let peakB := w4DecryptPrekeySlotDeltaPeak fineCostModel P cap maxEntries
        deserLive deserPeak p_cur p_dec p_tr l_td p_td
      let maxReq := w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq
        r_cur r_dec r_tr r_push r_td ikmCap
      lim.staticBytes + (18686152 + cumB + peakB) +
        2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva :
      let cap := max maxVal fileCap
      let cumB := w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum
        c_cur c_dec c_tr c_push c_td ikmCap
      let peakB := w4DecryptPrekeySlotDeltaPeak fineCostModel P cap maxEntries
        deserLive deserPeak p_cur p_dec p_tr l_td p_td
      let maxReq := w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq
        r_cur r_dec r_tr r_push r_td ikmCap
      MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
        fineStepReserveOfCum maxReq 16 cumB +
        (lim.staticCount + fineDynIvsOfCum cumB + 16) *
          (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
        fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init (W4DecryptPrekeySlotEnv P) := by
  have hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    omega
  have hSpec := w4DecryptPrekeySlot_small_phaseCredit fineCostModel_modelHyps P
    hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess hdir
    hpeer hkeyName hregName hkpkMark hold hnew hSmall hspqrKey
    hfileCap hdeser hCurTrial hlen4 hl_le_p hDec hTrial hDrop hPush hTd
  have hlp := w4DecryptPrekeySlot_live_le_peak fineCostModel P
    (max maxVal fileCap) maxEntries deserLive deserPeak p_cur p_dec p_tr l_td p_td
  exact fitsEnv_fineCostModel_of_phaseCredit hSpec hlp henf hram hva

/-- `FitsEnv fineCostModel` discharge for outer `W4SlotR3bEnv x_pksm DecPkEnv`. -/
theorem w4SlotR3b_fitsEnv_fineCostModel
    {lim : BudgetLimits} (x_pksm : PksmGhost)
    {DecPkEnv : List AllocEvent → Prop} {decCum decLive decPeak decMaxReq : Nat}
    (hDec : PhaseCreditSpec fineCostModel DecPkEnv decCum decLive decPeak decMaxReq)
    (henf : lim.enforced = true)
    (hram :
      let cumB := w4SlotR3bDeltaCum x_pksm decCum
      let peakB := w4SlotR3bDeltaPeak x_pksm decLive decPeak
      let maxReq := w4SlotR3bMaxReq x_pksm decMaxReq
      lim.staticBytes + (18686152 + cumB + peakB) +
        2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva :
      let cumB := w4SlotR3bDeltaCum x_pksm decCum
      let peakB := w4SlotR3bDeltaPeak x_pksm decLive decPeak
      let maxReq := w4SlotR3bMaxReq x_pksm decMaxReq
      MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
        fineStepReserveOfCum maxReq 16 cumB +
        (lim.staticCount + fineDynIvsOfCum cumB + 16) *
          (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
        fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init (W4SlotR3bEnv x_pksm DecPkEnv) := by
  have hSpec :=
    w4SlotR3b_phaseCredit fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps x_pksm hDec
  have hlp := w4SlotR3b_live_le_peak x_pksm decLive decPeak
  exact fitsEnv_fineCostModel_of_phaseCredit hSpec hlp henf hram hva

end LibsignalBinary.Proofs.PeakBudget.W4OuterEnvBridges
