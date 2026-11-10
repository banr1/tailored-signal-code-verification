/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
public import LibsignalBinary.Proofs.PeakBudget.CallSiteFacts
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateAffinePeak
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers
public import LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget

/-!
# Envelope Bridges for W3 `process_prekey_bundle`

Connects the concrete budget-threaded envelopes across W3 (`process_prekey_bundle`, Stages 1–5) —
`DoReserveEnv`, `KemSerialize1569Env`, `StringCloneEnv`, `FmtWriteEnv`, `StoreKitBudget` step
envelopes, `SpqrInitParamEnv`, and `0`-prev `SessionRecord` serialization — to `W3InitiatePeakSpec`
and `FitsEnv fineCostModel`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto IdentityKey ReceiverChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentitySelfStoreSpec IdentityStoreSpec SessionStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost VecGhost)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_smallMaxReq_eq fineDynIvsOfCum fineStepReserveOfCum)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (StringCloneEnv stringCloneEvents stringCloneEvents_eq_of_env)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
  (DoReserveEnv KemSerialize1569Env doReserveEvents)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps dirDomainCaps_opened_own dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (FreeOnlyAlign16Evs ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (sessLoadPollDeltaLive sessLoadPollDeltaPeak
   sessStorePollDeltaLive sessStorePollDeltaPeak
   smallStorePollDeltaLive smallStorePollDeltaPeak)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (chainCloneLarge chainCloneMaxReq optLargeCost optLargeCost_of_le
   segCloneLarge segCloneMaxReq vecCloneLarge_of_le)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak
   serializeSomeOutLarge serializeSomePeak serializeSomeMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateAffinePeak
  (w3BoundedEvs_rustAlloc w3BoundedEvs_rustRealloc w3InitiateNativeAffLive)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers
  (phaseCreditSpec_kemSerialize1569_aff phaseCreditSpec_kemSerialize1569_small
   phaseCreditSpec_kyberPreKeyIdDisplay14_small)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
  (W3BoxedStoreStepEnv W3InitiateSlotEnv W3InitiateSlotParams
   w3BoxedStoreStep_phaseCredit
   w3BoxedStepCum w3BoxedStepLive w3BoxedStepMaxReq w3BoxedStepPeak
   w3InitiateSlotDeltaCum w3InitiateSlotDeltaLive w3InitiateSlotDeltaPeak w3InitiateSlotMaxReq
   w3InitiateSlotSmallDeltaLive w3InitiateSlotSmallDeltaPeak
   w3InitiateSlot_opened_phaseCredit w3InitiateSlot_small_phaseCredit
   w3SpqrInitCum w3SpqrInitLive w3SpqrInitPeak w3SpqrInit32_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (W3BoundedEvs phaseCreditSpec_w3BoundedEvs_aff phaseCreditSpec_w3BoundedEvs_small
   w3BoundedEvs_nil)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
  (IdentitySelfStoreBudgetEnv KpStepEnv RegIdStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (LoadStepEnv SessionStoreBudgetEnv StoreStepEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.CallSiteFacts (InitCallSite initCallSite_bounds)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (senderChainAsProtoGhost)

/-! ## 1. Stage 1, Stage 3, and Stage 5 Callee Envelope Bridges -/

theorem w3BoundedEvs_doReserveEvents (x : DoReserveCall) {maxCap : Nat}
    (hcap : reserveCap x.cap.toNat x.bs.length x.additional ≤ maxCap) :
    W3BoundedEvs 1 maxCap (doReserveEvents x) := by
  unfold doReserveEvents
  dsimp only
  split_ifs
  · exact w3BoundedEvs_rustAlloc (by decide) hcap
  · exact w3BoundedEvs_rustRealloc (by decide) hcap

theorem w3BoundedEvs_doReserveEnv {x : DoReserveCall} {maxCap : Nat}
    (hcap : reserveCap x.cap.toNat x.bs.length x.additional ≤ maxCap)
    {evs : List AllocEvent} (hevs : DoReserveEnv x evs) :
    W3BoundedEvs 1 maxCap evs :=
  hevs ▸ w3BoundedEvs_doReserveEvents x hcap

theorem doReserveEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : DoReserveCall} {maxCap : Nat}
    (hcap : reserveCap x.cap.toNat x.bs.length x.additional ≤ maxCap) :
    PhaseCreditSpec M (DoReserveEnv x)
      (2 * maxCap + 9539) (maxCap + 8195) (maxCap + 8195) maxCap :=
  ((phaseCreditSpec_w3BoundedEvs_aff hM 1 maxCap).of_imp
    (fun _ h => w3BoundedEvs_doReserveEnv hcap h)).mono
    (Nat.le_of_eq (Nat.one_mul _))
    (Nat.le_of_eq (Nat.one_mul _))
    (Nat.le_of_eq (Nat.one_mul _))
    (Nat.le_refl _)

theorem doReserveEnv_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : DoReserveCall} {maxCap : Nat}
    (hcap : reserveCap x.cap.toNat x.bs.length x.additional ≤ maxCap)
    (hsmall : maxCap ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (DoReserveEnv x) (2 * maxCap + 9539) 0 0 maxCap :=
  ((phaseCreditSpec_w3BoundedEvs_small hM 1 maxCap hsmall).of_imp
    (fun _ h => w3BoundedEvs_doReserveEnv hcap h)).mono
    (Nat.le_of_eq (Nat.one_mul _)) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)

theorem doReserveEnv_secrets192_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : DoReserveCall}
    (hcap : reserveCap x.cap.toNat x.bs.length x.additional ≤ 192) :
    PhaseCreditSpec M (DoReserveEnv x) (2 * 192 + 9539) (192 + 8195) (192 + 8195) 192 :=
  doReserveEnv_phaseCredit hM hcap

theorem doReserveEnv_secrets192_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : DoReserveCall}
    (hcap : reserveCap x.cap.toNat x.bs.length x.additional ≤ 192)
    (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (DoReserveEnv x) (2 * 192 + 9539) 0 0 192 :=
  doReserveEnv_small_phaseCredit hM hcap hsmall

theorem w3BoundedEvs_kemSerialize1569Env {evs : List AllocEvent}
    (hevs : KemSerialize1569Env evs) :
    W3BoundedEvs 1 1569 evs :=
  hevs ▸ w3BoundedEvs_rustAlloc (req := 1569) (al := 1) (maxReq := 1569)
    (by decide) (Nat.le_refl 1569)

theorem kemSerialize1569Env_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M KemSerialize1569Env
      (2 * 1569 + 9539) (1569 + 8195) (1569 + 8195) 1569 :=
  (phaseCreditSpec_kemSerialize1569_aff hM).of_imp (fun _ h => h)

theorem kemSerialize1569Env_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle : 1569 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M KemSerialize1569Env (2 * 1569 + 9539) 0 0 1569 :=
  (phaseCreditSpec_kemSerialize1569_small hM hle).of_imp (fun _ h => h)

theorem w3BoundedEvs_stringCloneEvents (g : VecGhost) {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen) :
    W3BoundedEvs 1 maxLen (stringCloneEvents g) := by
  unfold stringCloneEvents
  split_ifs
  · exact w3BoundedEvs_nil 1 maxLen
  · exact w3BoundedEvs_rustAlloc (by decide) hlen

theorem w3BoundedEvs_stringCloneEnv {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen)
    {evs : List AllocEvent} (hevs : StringCloneEnv g evs) :
    W3BoundedEvs 1 maxLen evs :=
  stringCloneEvents_eq_of_env hevs ▸ w3BoundedEvs_stringCloneEvents g hlen

theorem stringCloneEvents_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen) :
    PhaseCreditSpec M (· = stringCloneEvents g)
      (2 * maxLen + 9539) (maxLen + 8195) (maxLen + 8195) maxLen :=
  ((phaseCreditSpec_w3BoundedEvs_aff hM 1 maxLen).of_imp
    (fun _ h => h ▸ w3BoundedEvs_stringCloneEvents g hlen)).mono
    (Nat.le_of_eq (Nat.one_mul _))
    (Nat.le_of_eq (Nat.one_mul _))
    (Nat.le_of_eq (Nat.one_mul _))
    (Nat.le_refl _)

theorem stringCloneEvents_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen)
    (hsmall : maxLen ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = stringCloneEvents g) (2 * maxLen + 9539) 0 0 maxLen :=
  ((phaseCreditSpec_w3BoundedEvs_small hM 1 maxLen hsmall).of_imp
    (fun _ h => h ▸ w3BoundedEvs_stringCloneEvents g hlen)).mono
    (Nat.le_of_eq (Nat.one_mul _)) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)

theorem stringCloneEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen) :
    PhaseCreditSpec M (StringCloneEnv g)
      (2 * maxLen + 9539) (maxLen + 8195) (maxLen + 8195) maxLen :=
  (stringCloneEvents_phaseCredit hM hlen).of_imp (fun _ => stringCloneEvents_eq_of_env)

theorem stringCloneEnv_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen)
    (hsmall : maxLen ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (StringCloneEnv g) (2 * maxLen + 9539) 0 0 maxLen :=
  (stringCloneEvents_small_phaseCredit hM hlen hsmall).of_imp (fun _ => stringCloneEvents_eq_of_env)

theorem fmtWriteEnv_phaseCredit (M : AllocCostModel) [HasFineReallocCredit M] :
    PhaseCreditSpec M FmtWriteEnv 0 0 0 0 :=
  PhaseCreditSpec.of_eq_nil (fun _ h => h)

theorem formatInnerEnv_phaseCredit (M : AllocCostModel) [HasFineReallocCredit M] :
    PhaseCreditSpec M FormatInnerEnv 0 0 0 0 :=
  PhaseCreditSpec.of_eq_nil (fun _ h => h)

theorem alloc14_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (· = rustAllocEvents 14 1)
      (2 * 14 + 9539) (14 + 8195) (14 + 8195) 14 :=
  PhaseCreditSpec.rustAlloc_aff hM (by decide)

theorem alloc14_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle : 14 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents 14 1) (2 * 14 + 9539) 0 0 14 :=
  phaseCreditSpec_kyberPreKeyIdDisplay14_small hM hle

/-! ## 2. `StoreKit` Step-Envelope Bridges -/

theorem freeOnlyEvs_rustDealloc8 (sz : Nat) : FreeOnlyEvs (rustDeallocEvents sz 8) :=
  (FreeOnlyAlign16Evs.rustDealloc (by decide) sz).toFreeOnlyEvs

/-- Exact-deallocation async store steps imply `W3BoxedStoreStepEnv boxSz E_poll`. -/
theorem w3BoxedStoreStepEnv_of_exactDealloc {boxSz : Nat} {E_poll : List AllocEvent → Prop}
    {evs : List AllocEvent}
    (h : SeqEnv (BoxAllocEnv boxSz) (SeqEnv E_poll (· = rustDeallocEvents boxSz 8)) evs) :
    W3BoxedStoreStepEnv boxSz E_poll evs := by
  rcases h with h1 | ⟨e₁, e₂, rfl, h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨e₁, e₂, rfl, h1, ?_⟩
    rcases h2 with hp | ⟨ep, ed, rfl, hp, hd⟩
    · exact Or.inl hp
    · exact Or.inr ⟨ep, ed, rfl, hp, hd ▸ freeOnlyEvs_rustDealloc8 boxSz⟩

theorem trustStepEnv_to_w3Boxed {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey) (d : Direction)
    {evs : List AllocEvent} (h : TrustStepEnv ikit ikitEnv ist0 rem key d evs) :
    W3BoxedStoreStepEnv ikit.trustBoxSize (ikitEnv.trustPollEnv ist0 rem key d) evs :=
  w3BoxedStoreStepEnv_of_exactDealloc h

theorem trustStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey) (d : Direction)
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 rem key d) c_p l_p p_p r_p) :
    PhaseCreditSpec M (TrustStepEnv ikit ikitEnv ist0 rem key d)
      (w3BoxedStepCum ikit.trustBoxSize c_p)
      (w3BoxedStepLive ikit.trustBoxSize l_p)
      (w3BoxedStepPeak ikit.trustBoxSize p_p)
      (w3BoxedStepMaxReq ikit.trustBoxSize r_p) :=
  (w3BoxedStoreStep_phaseCredit hM ikit.trustBoxSize hpoll).of_imp
    (fun _ => trustStepEnv_to_w3Boxed ikit ikitEnv ist0 rem key d)

theorem saveStepEnv_to_w3Boxed {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey)
    {evs : List AllocEvent} (h : SaveStepEnv ikit ikitEnv ist0 rem key evs) :
    W3BoxedStoreStepEnv ikit.saveBoxSize (ikitEnv.savePollEnv ist0 rem key) evs :=
  w3BoxedStoreStepEnv_of_exactDealloc h

theorem saveStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey)
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (ikitEnv.savePollEnv ist0 rem key) c_p l_p p_p r_p) :
    PhaseCreditSpec M (SaveStepEnv ikit ikitEnv ist0 rem key)
      (w3BoxedStepCum ikit.saveBoxSize c_p)
      (w3BoxedStepLive ikit.saveBoxSize l_p)
      (w3BoxedStepPeak ikit.saveBoxSize p_p)
      (w3BoxedStepMaxReq ikit.saveBoxSize r_p) :=
  (w3BoxedStoreStep_phaseCredit hM ikit.saveBoxSize hpoll).of_imp
    (fun _ => saveStepEnv_to_w3Boxed ikit ikitEnv ist0 rem key)

theorem kpStepEnv_to_w3Boxed {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit) (ist0 : ikit.IdState)
    {evs : List AllocEvent} (h : KpStepEnv skit senv ist0 evs) :
    W3BoxedStoreStepEnv skit.kpBoxSize (senv.kpPollEnv ist0) evs :=
  w3BoxedStoreStepEnv_of_exactDealloc h

theorem kpStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit) (ist0 : ikit.IdState)
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (senv.kpPollEnv ist0) c_p l_p p_p r_p) :
    PhaseCreditSpec M (KpStepEnv skit senv ist0)
      (w3BoxedStepCum skit.kpBoxSize c_p)
      (w3BoxedStepLive skit.kpBoxSize l_p)
      (w3BoxedStepPeak skit.kpBoxSize p_p)
      (w3BoxedStepMaxReq skit.kpBoxSize r_p) :=
  (w3BoxedStoreStep_phaseCredit hM skit.kpBoxSize hpoll).of_imp
    (fun _ => kpStepEnv_to_w3Boxed skit senv ist0)

theorem regIdStepEnv_to_w3Boxed {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit) (ist0 : ikit.IdState)
    {evs : List AllocEvent} (h : RegIdStepEnv skit senv ist0 evs) :
    W3BoxedStoreStepEnv skit.regIdBoxSize (senv.regIdPollEnv ist0) evs :=
  w3BoxedStoreStepEnv_of_exactDealloc h

theorem regIdStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit) (ist0 : ikit.IdState)
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (senv.regIdPollEnv ist0) c_p l_p p_p r_p) :
    PhaseCreditSpec M (RegIdStepEnv skit senv ist0)
      (w3BoxedStepCum skit.regIdBoxSize c_p)
      (w3BoxedStepLive skit.regIdBoxSize l_p)
      (w3BoxedStepPeak skit.regIdBoxSize p_p)
      (w3BoxedStepMaxReq skit.regIdBoxSize r_p) :=
  (w3BoxedStoreStep_phaseCredit hM skit.regIdBoxSize hpoll).of_imp
    (fun _ => regIdStepEnv_to_w3Boxed skit senv ist0)

theorem loadStepEnv_to_w3Boxed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal)
    {evs : List AllocEvent} (h : LoadStepEnv kit kitEnv st0 rem evs) :
    W3BoxedStoreStepEnv kit.loadBoxSize (kitEnv.loadPollEnv st0 rem) evs :=
  w3BoxedStoreStepEnv_of_exactDealloc h

theorem loadStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal)
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.loadPollEnv st0 rem) c_p l_p p_p r_p) :
    PhaseCreditSpec M (LoadStepEnv kit kitEnv st0 rem)
      (w3BoxedStepCum kit.loadBoxSize c_p)
      (w3BoxedStepLive kit.loadBoxSize l_p)
      (w3BoxedStepPeak kit.loadBoxSize p_p)
      (w3BoxedStepMaxReq kit.loadBoxSize r_p) :=
  (w3BoxedStoreStep_phaseCredit hM kit.loadBoxSize hpoll).of_imp
    (fun _ => loadStepEnv_to_w3Boxed kit kitEnv st0 rem)

theorem storeStepEnv_to_w3Boxed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal) (rec : SessionRecord (List (BitVec 8)))
    {evs : List AllocEvent} (h : StoreStepEnv kit kitEnv st0 rem rec evs) :
    W3BoxedStoreStepEnv kit.storeBoxSize (kitEnv.storePollEnv st0 rem rec) evs :=
  w3BoxedStoreStepEnv_of_exactDealloc h

theorem storeStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal) (rec : SessionRecord (List (BitVec 8)))
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.storePollEnv st0 rem rec) c_p l_p p_p r_p) :
    PhaseCreditSpec M (StoreStepEnv kit kitEnv st0 rem rec)
      (w3BoxedStepCum kit.storeBoxSize c_p)
      (w3BoxedStepLive kit.storeBoxSize l_p)
      (w3BoxedStepPeak kit.storeBoxSize p_p)
      (w3BoxedStepMaxReq kit.storeBoxSize r_p) :=
  (w3BoxedStoreStep_phaseCredit hM kit.storeBoxSize hpoll).of_imp
    (fun _ => storeStepEnv_to_w3Boxed kit kitEnv st0 rem rec)

/-! ## 3. `SpqrInitParamEnv` and Stage 5 Session-Serialization Bridges -/

/-- `Params`-indexed wrapper around `InitialStateEnv` (`SpqrInitParamEnv F x.p = InitialStateEnv F x`).
-/
def SpqrInitParamEnv (F : ShaCompress) (p : Params) (evs : List AllocEvent) : Prop :=
  InitialStateEnv F { pA := 0#64, ret := 0#64, akPtr := 0#64, p := p } evs

theorem spqrInitParamEnv_eq (F : ShaCompress) (x : InitialStateGhost) :
    SpqrInitParamEnv F x.p = InitialStateEnv F x :=
  rfl

theorem spqrInitParamEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (p : Params)
    (hkey : p.authKey.length ≤ 32) :
    PhaseCreditSpec M (SpqrInitParamEnv F p)
      (w3SpqrInitCum 32) (w3SpqrInitLive 32) (w3SpqrInitPeak 32) 4224 :=
  w3SpqrInit32_phaseCredit hM F { pA := 0#64, ret := 0#64, akPtr := 0#64, p := p } hkey

theorem serializeSomeOutLarge_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    serializeSomeOutLarge M G sess ≤ serializeSomePeak M G sess :=
  Nat.le_add_left _ _

theorem recordSerializeOutLarge_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    recordSerializeOutLarge M g r ≤ recordSerializePeak M g r := by
  unfold recordSerializeOutLarge recordSerializePeak
  cases g.cur <;> cases r.currentSession <;> simp [serializeSomeOutLarge_le_peak]

private theorem sum_map_eq_zero_of_forall_zero {α : Type} {f : α → Nat} {xs : List α}
    (h : ∀ x ∈ xs, f x = 0) :
    (xs.map f).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.map_cons, List.sum_cons, h x List.mem_cons_self, Nat.zero_add]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem le_of_mem_foldr_max {α : Type} (f : α → Nat) {xs : List α} {bound : Nat}
    (hb : (xs.map f).foldr max 0 ≤ bound) :
    ∀ x ∈ xs, f x ≤ bound := by
  induction xs with
  | nil => intro _ h; nomatch h
  | cons x tl ih =>
    simp only [List.map_cons, List.foldr_cons, Nat.max_le] at hb
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact hb.1
    · exact ih hb.2 y hmem

theorem chainCloneLarge_eq_zero_of_maxReq_le (M : AllocCostModel) [HasFineReallocCredit M]
    {gc : ChainGhost × ReceiverChain}
    (hmax : chainCloneMaxReq gc ≤ HasFineReallocCredit.smallMaxReq M) :
    chainCloneLarge M gc = 0 := by
  simp only [chainCloneMaxReq, Nat.max_le] at hmax
  obtain ⟨⟨⟨hsrk, hpriv⟩, h32⟩, h104, hseeds⟩ := hmax
  unfold chainCloneLarge
  rw [vecCloneLarge_of_le M hsrk, vecCloneLarge_of_le M hpriv]
  have hsum0 : (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum = 0 :=
    sum_map_eq_zero_of_forall_zero (fun mkg hm =>
      optLargeCost_of_le M (le_of_mem_foldr_max (fun m => m.seed.length) hseeds mkg hm))
  cases gc.2.chainKey <;> split_ifs <;>
    simp only [optLargeCost_of_le M h32, optLargeCost_of_le M h104, hsum0, Nat.add_zero]

theorem segCloneLarge_eq_zero_of_maxReq_le (M : AllocCostModel) [HasFineReallocCredit M]
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hmax : segCloneMaxReq G st ≤ HasFineReallocCredit.smallMaxReq M) :
    segCloneLarge M G st = 0 := by
  unfold segCloneMaxReq at hmax
  dsimp only at hmax
  simp only [Nat.max_le] at hmax
  obtain ⟨⟨⟨⟨⟨hlIk, hrIk⟩, h32⟩, hsnd⟩, h104, hrc⟩, ⟨hpend, hkyb⟩, halice, hpq⟩ := hmax
  unfold segCloneLarge
  rw [vecCloneLarge_of_le M hlIk, vecCloneLarge_of_le M hrIk, optLargeCost_of_le M h32,
    vecCloneLarge_of_le M hpend, vecCloneLarge_of_le M hkyb,
    vecCloneLarge_of_le M halice, vecCloneLarge_of_le M hpq]
  have hsum0 : ((G.chains.zip st.receiverChains).map (chainCloneLarge M)).sum = 0 :=
    sum_map_eq_zero_of_forall_zero (fun gc hmem =>
      chainCloneLarge_eq_zero_of_maxReq_le M
        (le_of_mem_foldr_max chainCloneMaxReq hrc gc hmem))
  cases hGs : G.sender <;> cases hSc : st.senderChain <;> split_ifs <;>
    simp only [hGs, hSc, optLargeCost_of_le M h104, hsum0, Nat.zero_add, Nat.add_zero] at hsnd ⊢
  all_goals exact chainCloneLarge_eq_zero_of_maxReq_le M hsnd

/-- When the encoded `0`-prev session fits within `maxEnc ≤ smallMaxReq M`, `serializeSomeOutLarge M G sess = 0`.
-/
theorem serializeSomeOutLarge_eq_zero_of_enc_le (M : AllocCostModel) [HasFineReallocCredit M]
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {maxEnc : Nat}
    (henc : (lenField 1 (encSessionMem G sess)).length ≤ maxEnc)
    (hsmall : maxEnc ≤ HasFineReallocCredit.smallMaxReq M) :
    serializeSomeOutLarge M G sess = 0 :=
  optLargeCost_of_le M (Nat.le_trans henc hsmall)

theorem recordSerializeOutLarge_eq_zero_of_enc_le (M : AllocCostModel) [HasFineReallocCredit M]
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))} {maxEnc : Nat}
    (henc : ∀ G sess, g.cur = some G → r.currentSession = some sess →
      (lenField 1 (encSessionMem G sess)).length ≤ maxEnc)
    (hsmall : maxEnc ≤ HasFineReallocCredit.smallMaxReq M) :
    recordSerializeOutLarge M g r = 0 := by
  unfold recordSerializeOutLarge
  cases hg : g.cur with
  | none => rfl
  | some G =>
    cases hr : r.currentSession with
    | none => rfl
    | some sess =>
      exact serializeSomeOutLarge_eq_zero_of_enc_le M (henc G sess hg hr) hsmall

theorem serializeSomePeak_eq_zero_of_maxReq_le (M : AllocCostModel) [HasFineReallocCredit M]
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hmax : serializeSomeMaxReq G sess ≤ HasFineReallocCredit.smallMaxReq M) :
    serializeSomePeak M G sess = 0 := by
  simp only [serializeSomeMaxReq, Nat.max_le] at hmax
  unfold serializeSomePeak
  dsimp only
  rw [segCloneLarge_eq_zero_of_maxReq_le M hmax.1, optLargeCost_of_le M hmax.2]

/-- When `recordSerializeMaxReq g r ≤ smallMaxReq M`, both `recordSerializePeak M g r` and `recordSerializeOutLarge M g r` are `0`.
-/
theorem recordSerializePeak_eq_zero_of_maxReq_le (M : AllocCostModel) [HasFineReallocCredit M]
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hmax : recordSerializeMaxReq g r ≤ HasFineReallocCredit.smallMaxReq M) :
    recordSerializePeak M g r = 0 ∧ recordSerializeOutLarge M g r = 0 := by
  unfold recordSerializeMaxReq at hmax
  unfold recordSerializePeak recordSerializeOutLarge
  cases hg : g.cur with
  | none => exact ⟨rfl, rfl⟩
  | some G =>
    cases hr : r.currentSession with
    | none => exact ⟨rfl, rfl⟩
    | some sess =>
      rw [hg, hr] at hmax
      have hp := serializeSomePeak_eq_zero_of_maxReq_le M hmax
      have ho : serializeSomeOutLarge M G sess = 0 :=
        Nat.eq_zero_of_le_zero (hp ▸ serializeSomeOutLarge_le_peak M G sess)
      exact ⟨hp, ho⟩

/-! ## 4. `InitCallSite` and `fineCostModel` `FitsEnv` Instantiation -/

/-- Constructs `W3InitiateSlotParams` at `StoresGhost.opened` for a W3 `InitGhost` call. -/
def mkW3InitiateSlotParams
    (rd : ReadRule) (x : InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_spqr : InitialStateGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8))) :
    W3InitiateSlotParams where
  rd := rd
  DeserEnv := fun _ => (· = [])
  files := x.F
  ownDir := StoresGhost.opened.identity.own
  peersDir := StoresGhost.opened.identity.peers
  sessDir := StoresGhost.opened.sessions
  peer := x.peer
  ownKeyName := ownKeyName
  ownRegName := ownRegName
  F := F
  x_spqr := x_spqr
  g_rec := g_rec
  r_rec := r_rec

theorem peer_name_length_le_of_initCallSite {img : Obj.Image} {S : RunSem}
    {g : RunCall} {x : InitGhost} (hsite : InitCallSite img S g x) :
    x.peer.name.bytes.length ≤ 40 := by
  have h := (initCallSite_bounds hsite).1
  rwa [show x.peer.val.name = x.peer.name.bytes from rfl] at h

/-- Regime-free `PhaseCreditSpec M` at an `InitCallSite` (`StoresGhost.opened`). -/
theorem w3InitiateSlot_at_initCallSite_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {img : Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (hsite : InitCallSite img S g x)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {fileCap : Nat}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ fileCap) :
    let P := mkW3InitiateSlotParams rd x ownKeyName ownRegName F x_spqr g_rec r_rec
    PhaseCreditSpec M (W3InitiateSlotEnv P)
      (w3InitiateSlotDeltaCum fileCap 0 0 (recordSerializeCum g_rec r_rec))
      (w3InitiateSlotDeltaLive fileCap 0 0 (recordSerializeOutLarge M g_rec r_rec))
      (w3InitiateSlotDeltaPeak fileCap 0 0 0 (recordSerializePeak M g_rec r_rec))
      (w3InitiateSlotMaxReq fileCap 0 0 (recordSerializeMaxReq g_rec r_rec)) :=
  w3InitiateSlot_opened_phaseCredit hM
    (mkW3InitiateSlotParams rd x ownKeyName ownRegName F x_spqr g_rec r_rec)
    rfl rfl rfl (fun _ => rfl)
    (peer_name_length_le_of_initCallSite hsite)
    hkeyName hregName hspqrKey hfileCap

/-- Small-regime (`1569 ≤ smallMaxReq M`) `PhaseCreditSpec M` at an `InitCallSite` (`StoresGhost.opened`).
-/
theorem w3InitiateSlot_at_initCallSite_small_phaseCredit
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {img : Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (hsite : InitCallSite img S g x)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {fileCap : Nat}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ fileCap) :
    let P := mkW3InitiateSlotParams rd x ownKeyName ownRegName F x_spqr g_rec r_rec
    PhaseCreditSpec M (W3InitiateSlotEnv P)
      (w3InitiateSlotDeltaCum fileCap 0 0 (recordSerializeCum g_rec r_rec))
      (w3InitiateSlotSmallDeltaLive fileCap 0 0 (recordSerializeOutLarge M g_rec r_rec))
      (w3InitiateSlotSmallDeltaPeak fileCap 0 0 0 (recordSerializePeak M g_rec r_rec))
      (w3InitiateSlotMaxReq fileCap 0 0 (recordSerializeMaxReq g_rec r_rec)) := by
  intro P
  have hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseCreditSpec M (P.DeserEnv bs) 0 0 0 0 :=
    fun _ _ => PhaseCreditSpec.nil M
  have h := w3InitiateSlot_small_phaseCredit hM hsmall P
    dirDomainCaps_opened_own dirDomainCaps_opened_peers dirDomainCaps_opened_sess
    (by decide) (peer_name_length_le_of_initCallSite hsite)
    hkeyName hregName hspqrKey hfileCap hdeser
  exact Nat.zero_max fileCap ▸ h

private theorem boxedStepLive_le_peak_of_le (boxSz : Nat) {l p : Nat} (h : l ≤ p) :
    w3BoxedStepLive boxSz l ≤ w3BoxedStepPeak boxSz p :=
  Nat.add_le_add_left h _

private theorem sessStoreBoxedLive_le_peak {serLive serPeak : Nat} (maxEntries : Nat)
    (h : serLive ≤ serPeak) :
    w3BoxedStepLive 32 (sessStorePollDeltaLive serLive maxEntries) ≤
      w3BoxedStepPeak 32 (sessStorePollDeltaPeak serPeak maxEntries) :=
  boxedStepLive_le_peak_of_le 32
    (Nat.add_le_add_right (Nat.add_le_add_left h 32768) _)

theorem w3InitiateSlot_small_live_le_peak
    {fileCap maxEntries deserLive deserPeak serLive serPeak : Nat}
    (hser : serLive ≤ serPeak) :
    w3InitiateSlotSmallDeltaLive fileCap maxEntries deserLive serLive ≤
      w3InitiateSlotSmallDeltaPeak fileCap maxEntries deserLive deserPeak serPeak := by
  unfold w3InitiateSlotSmallDeltaLive w3InitiateSlotSmallDeltaPeak
  dsimp only
  have hss := sessStoreBoxedLive_le_peak maxEntries hser
  have hi :
      w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries) +
        w3BoxedStepLive 32 (sessStorePollDeltaLive serLive maxEntries) ≤
      max (w3BoxedStepPeak 32 (smallStorePollDeltaPeak fileCap maxEntries))
        (w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries) +
          w3BoxedStepPeak 32 (sessStorePollDeltaPeak serPeak maxEntries)) :=
    Nat.le_trans (Nat.add_le_add_left hss _) (Nat.le_max_right _ _)
  have hr :
      w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries) +
        (w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries) +
          w3BoxedStepLive 32 (sessStorePollDeltaLive serLive maxEntries)) ≤
      max (w3BoxedStepPeak 16 (smallStorePollDeltaPeak fileCap maxEntries))
        (w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries) +
          max (w3BoxedStepPeak 32 (smallStorePollDeltaPeak fileCap maxEntries))
            (w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries) +
              w3BoxedStepPeak 32 (sessStorePollDeltaPeak serPeak maxEntries))) :=
    Nat.le_trans (Nat.add_le_add_left hi _) (Nat.le_max_right _ _)
  refine Nat.le_trans ?_ (Nat.le_max_right _ _)
  rw [Nat.add_assoc _ (w3BoxedStepLive 16 _) (w3BoxedStepLive 32 _),
      Nat.add_assoc _ (w3BoxedStepLive 16 _ + _) (w3BoxedStepLive 32 _),
      Nat.add_assoc (w3BoxedStepLive 16 _) (w3BoxedStepLive 32 _) _]
  exact Nat.add_le_add_left hr _

private theorem aff_live_le_peak_abstract
    (a33 a1569 a1568 l3 a41613 a684
     l_t p_t l_sl p_sl l_k p_k l_q p_q l_r p_r l_i p_i l_ss p_ss : Nat)
    (hss : l_ss ≤ p_ss) :
    (a33 + a1569 + a1568 + l3 + a33 + a41613 + a684) +
      l_t + l_sl + l_k + l_q + l_r + l_i + l_ss ≤
    max p_t (l_t + (a33 + a1569 + p_sl)) +
      (l_t + (a33 + a1569 + l_sl)) +
      max p_k (l_k + a1568) +
      (l_k + a1568) +
      l3 + l3 +
      (a33 + max p_q (l_q + a41613)) +
      (a33 + l_q + a41613) +
      (a684 + max p_r (l_r + max p_i (l_i + p_ss))) := by
  omega

theorem w3InitiateSlot_live_le_peak
    {fileCap maxEntries deserLive deserPeak serLive serPeak : Nat}
    (hser : serLive ≤ serPeak) :
    w3InitiateSlotDeltaLive fileCap maxEntries deserLive serLive ≤
      w3InitiateSlotDeltaPeak fileCap maxEntries deserLive deserPeak serPeak := by
  unfold w3InitiateSlotDeltaLive w3InitiateSlotDeltaPeak w3InitiateNativeAffLive
  dsimp only
  exact aff_live_le_peak_abstract
    (33 + 8195) (1569 + 8195) (1568 + 8195) (8 * (1569 + 8195))
    (13 * (416 + 8195)) (4 * (68 + 8195))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (sessStoreBoxedLive_le_peak maxEntries hser)

/-- `FitsEnv fineCostModel` discharge for `W3InitiateSlotEnv P` from `fineCostModel.init`. -/
theorem w3InitiateSlot_small_fitsEnv_fineCostModel
    {lim : BudgetLimits} (P : W3InitiateSlotParams)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (henf : lim.enforced = true)
    (hram :
      let cap := max maxVal fileCap
      let cumB := w3InitiateSlotDeltaCum cap maxEntries deserCum
        (recordSerializeCum P.g_rec P.r_rec)
      let peakB := w3InitiateSlotSmallDeltaPeak cap maxEntries deserLive deserPeak
        (recordSerializePeak fineCostModel P.g_rec P.r_rec)
      let maxReq := w3InitiateSlotMaxReq cap maxEntries deserMaxReq
        (recordSerializeMaxReq P.g_rec P.r_rec)
      lim.staticBytes + (18686152 + cumB + peakB) +
        2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva :
      let cap := max maxVal fileCap
      let cumB := w3InitiateSlotDeltaCum cap maxEntries deserCum
        (recordSerializeCum P.g_rec P.r_rec)
      let peakB := w3InitiateSlotSmallDeltaPeak cap maxEntries deserLive deserPeak
        (recordSerializePeak fineCostModel P.g_rec P.r_rec)
      let maxReq := w3InitiateSlotMaxReq cap maxEntries deserMaxReq
        (recordSerializeMaxReq P.g_rec P.r_rec)
      MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
        fineStepReserveOfCum maxReq 16 cumB +
        (lim.staticCount + fineDynIvsOfCum cumB + 16) *
          (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
        fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init (W3InitiateSlotEnv P) := by
  have hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hSpec := w3InitiateSlot_small_phaseCredit fineCostModel_modelHyps hsmall P
    hdcOwn hdcPeers hdcSess hdir hpeer hkeyName hregName hspqrKey hfileCap hdeser
  have hlp := w3InitiateSlot_small_live_le_peak
    (fileCap := max maxVal fileCap) (maxEntries := maxEntries)
    (deserLive := deserLive) (deserPeak := deserPeak)
    (recordSerializeOutLarge_le_peak fineCostModel P.g_rec P.r_rec)
  exact fitsEnv_fineCostModel_of_phaseCredit hSpec hlp henf hram hva

end LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges
