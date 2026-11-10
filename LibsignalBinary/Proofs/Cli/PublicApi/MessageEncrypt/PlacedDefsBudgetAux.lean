/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CalleeProofs.KyberMapPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CalleeProofs.CmDropPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.DropsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.ComposeBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Auxiliary Definitions for CLI `MessageEncrypt`

Defines store-kit budget projections, `withStoresEncPlacedSpecV`, seam and tail states
(`*StateVPlaced`, `EncTailVPlaced`), and hook/callee bundles (`PublicApiEncHooksPlaced`,
`EncCalleesPlaced`) for `session_message_encrypt_with_stores` (`blkPl_464`, `lsProg_464 H`)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto IdentityKey OutgoingTripleRatchet SessionState)
open CryptoGames.LibsignalSessionApi
  (CiphertextMessage IdentityChange Session SessionRecord StoreAnswers)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement libsignalSessionLib
   lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
   lsRustReallocSym lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.CliRatchet.EncPlaced (lsProg_464)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
  (durationSinceBoundedSpec lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym
   lsStringCloneSym lsTimeAddSym)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (WithStoresEncGhost nowAt withStoresEncStackV)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost apiEncResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (SessionStoreSpec extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
   ls_subroutine_ok_rocl_of_cl ls_subroutine_ok_rocl_of_plain withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet
  (OtrEncryptGhost SpqrModel noAllocShimSpec sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchetRepr
  (UuidParser protocolAddressAt uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (hookSat_of_withVmPreserved timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (FromApplyEnv FromCmEnv FromKeyEnv FromOtrEnv FromSaveEnv OtrEncryptEnv SeamBudget
   SpqrSendBudgetEnv WithStoresEncEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
  (FromCurEnv)

/-! ## 1. Store-Kit Budget Projections -/

abbrev toTempTwinsKitEnv {A : RustAlloc} {b : BitVec 64} {kit : SessionStoreSpec A b}
    (kitEnv : SessionStoreBudgetEnv kit) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit where
  loadPollEnv := kitEnv.loadPollEnv
  storePollEnv := kitEnv.storePollEnv

abbrev toTempTwinsIkitEnv {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (ikitEnv : IdentityStoreBudgetEnv ikit) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit where
  trustPollEnv := ikitEnv.trustPollEnv
  savePollEnv := ikitEnv.savePollEnv

theorem toTempTwinsKitOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (h : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.SessionOnlyKitBudgetOkSE
      A lim kit (toTempTwinsKitEnv kitEnv) Scope encRecord H where
  loadShim := h.loadShim
  loadPoll := h.loadPoll
  loadFutDrop := h.loadFutDrop
  storeShim := h.storeShim
  storePoll := h.storePoll
  storeFutDrop := h.storeFutDrop

theorem toTempTwinsIkitOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {H : LibsignalHooks}
    (h : IdentityStoreKitPlacedOkI A lim ikit ikitEnv H) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreKitBudgetOkI
      A lim ikit (toTempTwinsIkitEnv ikitEnv) H where
  trustShim := h.trustShim
  trustPoll := h.trustPoll
  trustFutDrop := h.trustFutDrop
  saveShim := h.saveShim
  savePoll := h.savePoll
  saveFutDrop := h.saveFutDrop

/-! ## 2. Budget-Threaded Relocatable `_with_stores` Contract (`withStoresEncPlacedSpecV`) -/

/-- Relocatable budget-threaded `session_message_encrypt_with_stores` (`blkPl_464`, `lsProg_464 H`)
    contract parameterized by `SessionStoreSpec` and `IdentityStoreSpec` with their budget environments. -/
def withStoresEncPlacedSpecV [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (WithStoresEncGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st_init) s =>
        ⌜FitsEnv M lim st_init
            (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
              ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv uuidParse x) ∧
          s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s.readReg64 .x4 = x.ssA ∧ s.readReg64 .x5 = kit.ss_vt ∧
          s.readReg64 .x6 = x.idA ∧ s.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗ cliTapeAt ctl x.cur x.rest ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        stackAt s.sp (withStoresEncStackV kit ikit) ∗
        A.pool lim st_init s
      post := fun (x, st_init) s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit, ∃∗ evs : List AllocEvent,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            kit.callsRel st0 answers (x.model C S uuidParse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S uuidParse answers).2 ∧
            sf.trace = s0.trace ++
              ikit.traceOfWith kit encRecord answers (x.model C S uuidParse answers).2 ∧
            WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
              ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv uuidParse x evs⌝ ∗
          kit.storeAt x.ssA (kit.storeFinal st0 answers (x.model C S uuidParse answers).2) ∗
          ikit.identityAt x.idA (ikit.idFinal ist0 answers (x.model C S uuidParse answers).2) ∗
          apiEncResultAt A.repAlloc x.ret (x.model C S uuidParse answers).1 ∗
          nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          stackAt s0.sp (withStoresEncStackV kit ikit) ∗
          A.pool lim (M.stepEvents evs st_init) sf
      onPanic := fun (x, _) s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
            kit.loadRel st0 x.rem.val answers.loadSession ∧
            s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
            ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers)⌝ ∗
          anyHeap }

theorem withStoresEncPlacedSpecV_eq_tempTwins [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidParse S sendEnv encRecord =
      LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.withStoresEncBudgetSpecV
        A lim kit (toTempTwinsKitEnv kitEnv) st0 ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope
        C ctl uuidParse S sendEnv encRecord := by
  rfl

theorem withStoresEncPlacedSpecV_pre_addrOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S
        sendEnv encRecord).pre (x, st_init) s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  have ⟨_, hp⟩ := extract_withLsCodeRoLoaded hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## 3. Budget-Threaded Seam States & Tail State (`lsProg_464 H`) -/

/-- Budget-threaded **Cur** (`+0x20c`) seam state under `[LibsignalPlacement]`. -/
def CurStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim
    (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x)
    st_init st
    (FromCurEnv C S sendEnv parse kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope x) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r g sess R s0 s

/-- Budget-threaded **Otr** (`+0x2c8`) seam state under `[LibsignalPlacement]`. -/
def OtrStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim
    (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x)
    st_init st
    (FromOtrEnv C S sendEnv parse kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 x sess otr taken) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r sess otr taken pqCap pqPtr R s0 s

/-- Budget-threaded **Key** (`+0x344`) seam state under `[LibsignalPlacement]`. -/
def KeyStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim
    (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x)
    st_init st
    (FromKeyEnv C S sendEnv parse kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 x sess otr taken k) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r sess otr taken pqCap pqPtr k R s0 s

/-- Budget-threaded **Cm** (`+0xa70`) seam state under `[LibsignalPlacement]`. -/
def CmStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim
    (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x)
    st_init st
    (FromCmEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 x sess otr' taken k) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' R s0 s

/-- Budget-threaded **Save** (`+0xbd4`) seam state under `[LibsignalPlacement]`. -/
def SaveStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim
    (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x)
    st_init st
    (FromSaveEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv)
      (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x sess otr' taken k) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SaveStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' R s0 s

/-- Budget-threaded **Apply** (`+0xd9c`) seam state under `[LibsignalPlacement]`. -/
def ApplyStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    (pqCap' pqPtr' : BitVec 64) (c : IdentityChange) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget lim
    (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x)
    st_init st
    (FromApplyEnv kit (toTempTwinsKitEnv kitEnv) st0 x sess otr' taken) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.ApplyStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s

/-- Budget-threaded **Stored** (`+0xe88`) seam state under `[LibsignalPlacement]`. -/
def StoredStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
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
  SeamBudget lim
    (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x)
    st_init st FreeOnlyEvs ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.StoredStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' c R s0 s

/-- Budget-threaded error/result tail entry state under `[LibsignalPlacement]`. -/
def EncTailVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (pc : BitVec 64) (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  SeamBudget lim
    (WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x)
    st_init st FreeOnlyEvs ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 C ctl parse S
    x answers pc regs slots R s0 s

/-! ## 4. External Hooks & Callees on `lsProg_464 H` -/

/-- `VmPreserved`-strengthened bounded `std::time::SystemTime::duration_since` contract (`0` allocations). -/
def durationSinceBoundedBudgetSpec : Spec (BitVec 64 × BitVec 64) :=
  withVmPreserved durationSinceBoundedSpec

/-- Budget-threaded external hook contracts and panic stubs on `H : LibsignalHooks` used by
    `session_message_encrypt_with_stores` (`blkPl_464`) and its eight proved placed callees. -/
structure PublicApiEncHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec
  alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)
  memcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec
  stringClone : HookSat H lsStringCloneSym (stringCloneBudgetSpec M A lim)
  timeAdd : HookSat H lsTimeAddSym
    (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet timeAddBudgetSpec)
  durationSince : HookSat H lsDurationSinceSym
    (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
      durationSinceBoundedBudgetSpec)
  handleError : H lsHandleErrorSym = some Rust.panicked
  handleAllocError : H lsHandleAllocErrorSym = some Rust.panicked
  expectFailed : H lsExpectFailedSym = some Rust.panicked

theorem PublicApiEncHooksPlaced.toTempTwins [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : PublicApiEncHooksPlaced A lim H) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PublicApiEncHooksBudget
      A lim H where
  shim := hookSat_of_withVmPreserved h.shim
  shimBudget := h.shim
  alloc := h.alloc
  dealloc := h.dealloc
  realloc := h.realloc
  memcpy := hookSat_of_withVmPreserved h.memcpy
  memcpyBudget := h.memcpy
  stringClone := h.stringClone
  timeAdd := hookSat_of_withVmPreserved h.timeAdd
  durationSince := hookSat_of_withVmPreserved h.durationSince
  handleError := h.handleError
  handleAllocError := h.handleAllocError
  expectFailed := h.expectFailed

/-- Budget-threaded relocatable `OTR::encrypt::<Coins>` raw spec (`onOom = ⌜False⌝`,
    `allocFailedIn` eliminated from `onPanic` under `FitsEnv`). -/
def otrEncryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidParse x)⌝ ∗
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec C
        (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜OtrEncryptEnv C S sendEnv uuidParse x evs⌝ ∗
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec C
        (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- Budget-threaded relocatable `OTR::encrypt::<Coins>` spec restricted to OTRs whose SPQR state
    satisfies `Q`. -/
def otrEncryptPlacedSpecQ [LibsignalPlacement] {M : AllocCostModel} (Q : List (BitVec 8) → Prop)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  { otrEncryptPlacedSpec C A lim ctl parse S sendEnv with
    pre := fun (x, st) s =>
      ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv parse x)⌝ ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ Q C
          (A.atState lim st s) ctl parse S).pre x s }

/-- Budget-threaded relocatable `OTR::encrypt::<Coins>` spec restricted to `(pqrState, rest)`
    satisfying `Q`, with `F` framed. -/
def otrEncryptPlacedSpecQF [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  { otrEncryptPlacedSpec C A lim ctl parse S sendEnv with
    pre := fun (x, st) s =>
      ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv parse x)⌝ ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQF Q F C
          (A.atState lim st s) ctl parse S).pre x s
    post := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent,
        ⌜OtrEncryptEnv C S sendEnv parse x evs⌝ ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQF Q F C
          (A.atState lim (M.stepEvents evs st) sf) ctl parse S).post x s0 sf }

/-- Bundle of all 9 budget-threaded in-library callees invoked by Block `464` (`lsProg_464 H`)
    under `[LibsignalPlacement]`. -/
structure EncCalleesPlaced [LibsignalPlacement] {M : AllocCostModel} (Q : List (BitVec 8) → Prop)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (H : LibsignalHooks) : Prop where
  otrFrom : subroutine_ok (lsProg_464 H) (lsmpl.base 19)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.otrFromRawPlacedSpec
        M A lim))
  otrApply : subroutine_ok (lsProg_464 H) (lsmpl.base 20)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget.otrApplyPlacedSpec
        M A lim))
  remoteIk : subroutine_ok (lsProg_464 H) (lsmpl.base 29)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget.remoteIdentityKeyPlacedSpec
        A.repAlloc))
  otrEnc : subroutine_ok (lsProg_464 H)
    (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (withLsRoCl lsmpl (otrEncryptPlacedSpecQ Q C A lim ctl parse S sendEnv))
  unack : subroutine_ok (lsProg_464 H) (lsmpl.base 36)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget.unackItemsPlacedSpec
        A.repAlloc))
  kyber : subroutine_ok (lsProg_464 H) (lsmpl.base 430)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.kyberMapSpec M A lim))
  psmNew : subroutine_ok (lsProg_464 H) (lsmpl.base 41)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.preKeyMsgNewSpec M A lim))
  cmDrop : subroutine_ok (lsProg_464 H) (lsmpl.base 438)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.cmDropSpec M A lim))
  dropSs : subroutine_ok (lsProg_464 H) (lsmpl.base 442)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
        M A lim))

private theorem hookSat_noAllocShimVm_of_sessionShimBudget
    {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec) :
    HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec) := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun u R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ sessionShimBudgetSpec.pre u s0 ∗ R := by
    simpa [sessionShimBudgetSpec, sessionShimSpec, withVmPreserved, noAllocShimSpec] using hpre
  rcases hok u R s0 hrun hpre' hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hoom, hpost⟩ | ⟨hflt, hpc, hpost⟩ | ⟨htrp, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa [sessionShimBudgetSpec, sessionShimSpec, withVmPreserved, noAllocShimSpec] using hpost
  · exact Or.inr (Or.inl ⟨hoom, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hflt, hpc, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨htrp, hpost⟩))

private theorem subroutine_ok_withLsCodeRoLoaded_of_otrFromPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.otrFromPlacedSpec
        M A lim)) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.otrFromRawPlacedSpec
          M A lim)) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only
        [LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.otrFromPlacedSpec,
         CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.withLsRoLoaded,
         withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hfr.2, ?_⟩
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

private theorem subroutine_ok_dropSs_tempTwins [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsRoCl lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim))) :
    subroutine_ok prog entry
      (withLsRoCl lsmpl
        (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.dropSessionStructureLocal2BudgetSpec
          M A lim)) :=
  subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => by
      dsimp only [withLsRoCl,
        LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec,
        LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.dropSessionStructureLocal2BudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Spec,
        RustCliAllocBudget.atState] at hp ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.2.1, hp.1⟩, hp.2.2⟩)
    (fun ⟨x, st⟩ _ s0 sf hq => by
      dsimp only [withLsRoCl,
        LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec,
        LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.dropSessionStructureLocal2BudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Spec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      refine ⟨hq.1, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq
      rw [sepExists_sepConj_left, satisfies_sepExists]
      obtain ⟨evs, hevs⟩ := hq.2
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hevs
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hevs.1.2, hevs.1.1, hevs.2⟩)

/-- Discharge all 8 proved budget-threaded in-library callees of `EncCalleesPlaced` from
    `PublicApiEncHooksPlaced A lim H`, leaving only `otrEnc` as an assumption. -/
theorem EncCalleesPlaced.of_otrEnc [LibsignalPlacement] {M : AllocCostModel}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {H : LibsignalHooks}
    (hhooks : PublicApiEncHooksPlaced A lim H)
    (hotrEnc : subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (withLsRoCl lsmpl (otrEncryptPlacedSpecQ Q C A lim ctl parse S sendEnv))) :
    EncCalleesPlaced Q C A lim ctl parse S sendEnv H where
  otrFrom :=
    ls_subroutine_ok_rocl_of_block (callerProg := lsProg_464 H)
      (subroutine_ok_withLsCodeRoLoaded_of_otrFromPlaced
        (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.FromBudget.otrFrom_placed_ok
          hhooks.dealloc
          (((CryptoVerification.LibsignalTripleRatchet.Getters.instIsLsBlockProg_29 H).eq_blockProgram.trans
              (CryptoVerification.instIsLsBlockProg_29 H).eq_blockProgram.symm) ▸
            LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.remote_identity_key_placed_ok
              A.repAlloc H)
          (((CryptoVerification.LibsignalTripleRatchet.Getters.instIsLsBlockProg_5 H).eq_blockProgram.trans
              (CryptoVerification.instIsLsBlockProg_5 H).eq_blockProgram.symm) ▸
            LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget.drop_spe_placed_ok
              hhooks.dealloc)))
  otrApply :=
    ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_464 H)
      (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget.otrApply_placed_ok
        (hookSat_noAllocShimVm_of_sessionShimBudget hhooks.shim)
        hhooks.alloc hhooks.dealloc)
  remoteIk :=
    ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_464 H)
      (LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.remote_identity_key_placed_ok
        A.repAlloc H)
  otrEnc := hotrEnc
  unack :=
    ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_464 H)
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget.unackItems_ls_placed_ok
        hhooks.timeAdd)
  kyber :=
    ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_464 H)
      (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CalleeProofs.KyberMapPlacedBudget.kyberMap_placed_ok
        hhooks.shim hhooks.alloc hhooks.memcpy)
  psmNew :=
    ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_464 H)
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.ComposeBudget.preKeyMsgNew_placed_ok_sessionHooks
        hhooks.shim hhooks.alloc hhooks.dealloc hhooks.realloc hhooks.memcpy)
  cmDrop :=
    ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_464 H)
      (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CalleeProofs.CmDropPlacedBudget.cmDrop_placed_ok
        hhooks.dealloc)
  dropSs :=
    ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_464 H)
      (LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.DropsPlacedBudget.drop_session_structure_local2_placed_ok
        hhooks.dealloc)

theorem EncCalleesPlaced.toTempTwins [LibsignalPlacement] {M : AllocCostModel}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {H : LibsignalHooks}
    (c : EncCalleesPlaced Q C A lim ctl parse S sendEnv H) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.EncCalleesBudget
      Q C A lim ctl parse S sendEnv H where
  remoteIk := c.remoteIk
  otrEnc := c.otrEnc
  unack := c.unack

theorem EncCalleesPlaced.toTempTwinsFull [LibsignalPlacement] {M : AllocCostModel}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {H : LibsignalHooks}
    (c : EncCalleesPlaced Q C A lim ctl parse S sendEnv H) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins.EncCalleesFullBudget
      Q C A lim ctl parse S sendEnv H where
  toEncCalleesBudget := c.toTempTwins
  otrFrom := c.otrFrom
  otrApply := c.otrApply
  kyber := c.kyber
  psmNew := c.psmNew
  dropSs := subroutine_ok_dropSs_tempTwins c.dropSs

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
